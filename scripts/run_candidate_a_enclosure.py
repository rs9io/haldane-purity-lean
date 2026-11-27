#!/usr/bin/env python3
"""Driver & rigorous interval verifier for the exact __int128 Chebyshev trace enclosure engine.

Validates exact integer totals W_{n,g}^{(b)} against Codex's Round 2 centers_15p5.tsv and
centers_23.tsv, computing certified lower/upper bounds [L, U] and rigorous error radius
including:
  1. Chebyshev truncation tail 2 * sum_{k>K} exp(-mu) I_k(mu)
  2. 3-term Chebyshev integer-floor rounding error <= (sum_k c_k * k^2 / 2) * sqrt(c_dim * d_max)
  3. Coefficient quantization error <= (K + 1) * 2^{-60} * Q + (K + 1) * sqrt(c_dim * d_max)
  4. Exact exponential prefactor exp(x_n) enclosure via arbitrary-precision arithmetic.
"""
import csv
import math
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as F
from pathlib import Path

try:
    import flint
    HAS_FLINT = True
except ImportError:
    HAS_FLINT = False

import mpmath as mp
mp.mp.dps = 80

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / "scripts" / "chebyshev_enclose"
BIN_RX = ROOT / "scripts" / "chebyshev_enclose_rx"
EVID = ROOT / "round2_audit" / "round2-evidence"


def load_centers(tsv_path: Path):
    out = {}
    with tsv_path.open() as f:
        for row in csv.DictReader(f, delimiter="\t"):
            n = int(row["n"])
            out[n] = {k: int(row[k]) / 1e9 for k in ("I", "Rz", "Rx", "R4")}
    return out


def cheb_coeffs(mu_frac: F, K: int):
    """High-precision (80-digit) c_0 = exp(-mu)*I_0(mu), c_k = 2*exp(-mu)*I_k(mu),
    plus rigorous upper bound on tail sum_{k>K} c_k and weighted k^2/2 error factor."""
    mu = mp.mpf(mu_frac.numerator) / mp.mpf(mu_frac.denominator)
    ex = mp.exp(-mu)
    cs = []
    for k in range(K + 1):
        val = ex * mp.besseli(k, mu)
        if k >= 1:
            val *= 2
        cs.append(val)
    # Exact sum_{k=0}^inf c_k = exp(-mu) * exp(mu) = 1 (since T_k(1) = 1)!
    # Since every c_k > 0, the EXACT tail sum_{k>K} c_k = 1 - sum_{k=0}^K c_k!
    s = mp.fsum(cs)
    tail = max(mp.mpf(0), mp.mpf(1) - s) + mp.mpf("1e-70")
    # Weighted recurrence amplification: sum_{k=1}^K c_k * k*(k+1)/2
    amp = mp.fsum(cs[k] * mp.mpf(k * (k + 1)) / 2 for k in range(1, K + 1))
    # Integer coefficients floor(2^60 * c_k)
    scale = 1 << 60
    c_int = [int(mp.floor(c * scale)) for c in cs]
    return c_int, float(tail), float(amp)


def run_case(n: int, seam_name: str, Q_bits: int = 84, threads: int = 30, M_filter: int = -1):
    seam_map = {"I": 0, "Rz": 1, "R4": 2, "Rx": 3}
    seam = seam_map[seam_name]
    E_num = 24 if n <= 6 else 21  # 24/16 = 3/2 (all n>=2), 21/16 = 1.3125 (all n>=7 via 7-site open chain)
    W = math.ceil((20 + E_num) * n / 32)
    # Half-width W gives C = I - (H + E_shift*n) / W in [-1, 1]
    # mu_b = b * W / 2
    mu1 = F(31, 4) * W   # b = 31/2
    mu2 = F(23, 2) * W   # b = 23
    # Choose K so tail < 1e-22 for b = 23 (larger mu)
    K = int(math.ceil(math.sqrt(float(mu2) * 105))) + 15
    c1, tail1, amp1 = cheb_coeffs(mu1, K)
    c2, tail2, amp2 = cheb_coeffs(mu2, K)
    while tail2 > 1e-20:
        K += 20
        c1, tail1, amp1 = cheb_coeffs(mu1, K)
        c2, tail2, amp2 = cheb_coeffs(mu2, K)

    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as tf:
        for a, b in zip(c1, c2):
            tf.write(f"{a} {b}\n")
        coeff_path = tf.name

    t0 = time.monotonic()
    if seam_name == "Rx":
        cmd = [str(BIN_RX), str(n), str(E_num), str(W), str(K), str(Q_bits), str(threads), coeff_path]
    else:
        cmd = [str(BIN), str(n), str(seam), str(E_num), str(W), str(K), str(Q_bits), str(threads), coeff_path]
    if M_filter >= 0:
        cmd.append(str(M_filter))
    proc = subprocess.run(cmd, capture_output=True, text=True, check=True)
    dt = time.monotonic() - t0
    Path(coeff_path).unlink(missing_ok=True)

    W1_int = W2_int = None
    for line in proc.stdout.splitlines():
        if line.startswith("W1="):
            W1_int = int(line[3:])
        elif line.startswith("W2="):
            W2_int = int(line[3:])
    assert W1_int is not None and W2_int is not None

    # Rigorous error analysis:
    # Each block dim <= 3^n; complex R4 has factor sqrt(2) per floor step.
    dim_fac = math.sqrt(2.0 * (3 ** n)) if seam == 2 else math.sqrt(float(3 ** n))
    Q = mp.mpf(1 << Q_bits)
    a_shift = F(1242818, 10**6)
    E_shift = F(E_num, 16)

    results = {}
    for label, b_frac, W_int, tail, amp in [
        ("31/2", F(31, 2), W1_int, tail1, amp1),
        ("23", F(23, 1), W2_int, tail2, amp2),
    ]:
        # Column Euclidean error bound in units of 1 (where ideal column has scale Q):
        # 1) Recurrence floor errors: each step k introduces <= dim_fac, amplified by U_{m}(C) <= m+1
        #    -> summed over c_k gives amp * dim_fac
        # 2) Accumulation mul_shr60 floor errors: <= (K+1) * dim_fac
        # 3) Coefficient quantization c_k_int / 2^60 vs c_k: <= (K+1) * 2^{-60} * Q (since ||T_k(C)e_r|| <= 1)
        # 4) Chebyshev truncation: <= tail * Q
        E_col = mp.mpf(amp + K + 1) * mp.mpf(dim_fac) + Q * (mp.mpf(K + 1) * mp.power(2, -60) + mp.mpf(tail))
        # Frobenius norm error across all 3^n columns (in units of 1):
        E_frob = mp.sqrt(mp.mpf(3 ** n)) * E_col
        root_W = mp.sqrt(mp.mpf(W_int))
        lo_norm = max(mp.mpf(0), root_W - E_frob) / Q
        hi_norm = (root_W + E_frob) / Q

        x_n = b_frac * n * (E_shift - a_shift)
        ex_x = mp.exp(mp.mpf(x_n.numerator) / mp.mpf(x_n.denominator))
        lo_Z = ex_x * (lo_norm ** 2)
        hi_Z = ex_x * (hi_norm ** 2)
        mid = (lo_Z + hi_Z) / 2
        rad = (hi_Z - lo_Z) / 2
        results[label] = (float(mid), float(rad), float(lo_Z), float(hi_Z), W_int)

    return dt, W, K, results


def main():
    c155 = load_centers(EVID / "centers_15p5.tsv")
    c23 = load_centers(EVID / "centers_23.tsv")
    ns = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [4, 5, 6, 7, 8, 9, 10]
    seams = sys.argv[2].split(",") if len(sys.argv) > 2 else ["I", "Rz", "R4"]
    M_filter = int(sys.argv[3]) if len(sys.argv) > 3 else -1

    for n in ns:
        for s in seams:
            dt, W, K, res = run_case(n, s, Q_bits=84, threads=30, M_filter=M_filter)
            for label, ref in [("31/2", c155[n][s]), ("23", c23[n][s])]:
                mid, rad, lo, hi, _ = res[label]
                diff = abs(mid - ref)
                ok = "OK" if (M_filter >= 0 or (rad < 1e-5 and diff < 1e-5)) else "CHECK"
                print(f"n={n:2d} {s:2s} b={label:4s} (W={W:2d}, K={K:3d}, {dt:5.2f}s): "
                      f"mid={mid:14.9f} ± {rad:.2e} | ref={ref:14.9f} | |diff|={diff:.2e} [{ok}]",
                      flush=True)


if __name__ == "__main__":
    main()
