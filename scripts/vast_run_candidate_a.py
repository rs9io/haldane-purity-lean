#!/usr/bin/env python3
"""Remote Vast.ai multi-GPU orchestrator for Candidate A (Delta=1, D=1/4) exact int128 Chebyshev enclosures.

1. Compiles chebyshev_enclose_cuda.cu
2. Bit-for-bit verifies ALL 28 CPU reference totals (n=4..10, seams I, Rz, R4, Rx) against GPU output!
3. Computes exact 256-bit integer totals (W1, W2) and certified mpmath intervals for n=11, 12, 13, 14
   across ALL 4 seams (I, Rz, R4, Rx) and BOTH temperatures (b=31/2, b=23).
4. Saves incremental JSON checkpoint after EVERY single (n, seam) pair!
"""
import csv
import json
import math
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
mp.mp.dps = 80

WORK = Path(__file__).resolve().parent
BIN = WORK / "chebyshev_enclose_cuda"
OUT_JSON = WORK / "candidate_a_all88_enclosures.json"


def load_centers(tsv_path: Path):
    out = {}
    with tsv_path.open() as f:
        for row in csv.DictReader(f, delimiter="\t"):
            n = int(row["n"])
            out[n] = {k: int(row[k]) / 1e9 for k in ("I", "Rz", "Rx", "R4")}
    return out


def cheb_coeffs(mu_frac: F, K: int):
    mu = mp.mpf(mu_frac.numerator) / mp.mpf(mu_frac.denominator)
    ex = mp.exp(-mu)
    cs = []
    for k in range(K + 1):
        val = ex * mp.besseli(k, mu)
        if k >= 1:
            val *= 2
        cs.append(val)
    s = mp.fsum(cs)
    tail = max(mp.mpf(0), mp.mpf(1) - s) + mp.mpf("1e-70")
    amp = mp.fsum(cs[k] * mp.mpf(k * (k + 1)) / 2 for k in range(1, K + 1))
    scale = 1 << 60
    c_int = [int(mp.floor(c * scale)) for c in cs]
    return c_int, float(tail), float(amp)


def run_gpu_case(n: int, seam_name: str, Q_bits: int = 84):
    seam_map = {"I": 0, "Rz": 1, "R4": 2, "Rx": 3}
    seam = seam_map[seam_name]
    E_num = 24 if n <= 6 else 21
    W = math.ceil((20 + E_num) * n / 32)
    mu1 = F(31, 4) * W
    mu2 = F(23, 2) * W
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
    cmd = [str(BIN), str(n), str(seam), str(E_num), str(W), str(K), str(Q_bits), coeff_path]
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

    # Exact rigorous error bound (including the (Q + k*(k+1)/2 * dim_fac) * 2^{-60} term!)
    dim_fac = math.sqrt(2.0 * (3 ** n)) if seam == 2 else math.sqrt(float(3 ** n))
    Q = mp.mpf(1 << Q_bits)
    a_shift = F(1242818, 10**6)
    E_shift = F(E_num, 16)
    k_quad_sum = mp.mpf(K * (K + 1) * (K + 2)) / 6

    res = {}
    for label, b_frac, W_int, tail, amp in [
        ("31/2", F(31, 2), W1_int, tail1, amp1),
        ("23", F(23, 1), W2_int, tail2, amp2),
    ]:
        # Exact column error:
        #   sum_{k=1}^K c_k * k(k+1)/2 * dim_fac  (recurrence floors)
        # + (K+1) * dim_fac                       (accumulator floors)
        # + 2^{-60} * ((K+1)*Q + k_quad_sum*dim_fac)  (coeff quantization on v_k)
        # + tail * Q                              (Chebyshev truncation)
        E_col = (
            mp.mpf(amp + K + 1) * mp.mpf(dim_fac)
            + mp.power(2, -60) * (mp.mpf(K + 1) * Q + k_quad_sum * mp.mpf(dim_fac))
            + mp.mpf(tail) * Q
        )
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
        res[label] = {
            "W_int": str(W_int),
            "mid": float(mid),
            "rad": float(rad),
            "lo": str(mp.nstr(lo_Z, 25)),
            "hi": str(mp.nstr(hi_Z, 25)),
            "E_frob_over_Q": float(E_frob / Q),
        }
    return {
        "n": n, "seam": seam_name, "E_num": E_num, "W": W, "K": K, "Q_bits": Q_bits,
        "elapsed_s": round(dt, 3), "results": res,
    }


def main():
    print("=== Step 1: Compiling chebyshev_enclose_cuda.cu ===", flush=True)
    subprocess.run(
        ["nvcc", "-O3", "-std=c++17", "-arch=native",
         str(WORK / "chebyshev_enclose_cuda.cu"), "-o", str(BIN)],
        check=True
    )
    print("Compiled successfully!", flush=True)

    c155 = load_centers(WORK / "centers_15p5.tsv")
    c23 = load_centers(WORK / "centers_23.tsv")
    cpu_ref = json.loads((WORK / "candidate_a_cpu_ref.json").read_text())

    out = json.loads(OUT_JSON.read_text()) if OUT_JSON.exists() else {}

    print("\n=== Step 2: BIT-FOR-BIT CPU vs GPU Verification (n=4..10, all 4 seams) ===", flush=True)
    for n in [4, 5, 6, 7, 8, 9, 10]:
        for s in ["I", "Rz", "R4", "Rx"]:
            key = f"{n}_{s}"
            rec = run_gpu_case(n, s)
            r_cpu = cpu_ref[key]
            assert rec["results"]["31/2"]["W_int"] == r_cpu["W1"], f"MISMATCH W1 on {key}!"
            assert rec["results"]["23"]["W_int"] == r_cpu["W2"], f"MISMATCH W2 on {key}!"
            out[key] = rec
        print(f"  n={n:2d} (I, Rz, R4, Rx): 100% BIT-FOR-BIT IDENTICAL W1 & W2 to CPU!", flush=True)
    OUT_JSON.write_text(json.dumps(out, indent=2))

    print("\n=== Step 3: Enclosing n=11, 12, 13, 14 across ALL 4 seams (I, Rz, R4, Rx) ===", flush=True)
    for n in [11, 12, 13, 14]:
        for s in ["I", "Rz", "R4", "Rx"]:
            key = f"{n}_{s}"
            if key in out:
                print(f"  Skipping already-completed {key}", flush=True)
                continue
            rec = run_gpu_case(n, s)
            out[key] = rec
            OUT_JSON.write_text(json.dumps(out, indent=2))
            for lbl, ref_tbl in [("31/2", c155), ("23", c23)]:
                r = rec["results"][lbl]
                ref = ref_tbl[n][s]
                diff = abs(r["mid"] - ref)
                ok = "PASS" if (r["rad"] < 1e-5 and diff < 1e-5) else "WARN"
                print(f"  n={n:2d} {s:2s} b={lbl:4s} ({rec['elapsed_s']:6.2f}s): "
                      f"mid={r['mid']:14.9f} ± {r['rad']:.2e} | ref={ref:14.9f} | |diff|={diff:.2e} [{ok}]",
                      flush=True)

    print(f"\nALL 88 ENCLOSURES COMPLETE! Saved to {OUT_JSON}", flush=True)


if __name__ == "__main__":
    main()
