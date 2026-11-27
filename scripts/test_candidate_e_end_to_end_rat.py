#!/usr/bin/env python3
"""
End-to-end exact rational test of our fast in-Lean Candidate E certificate:
- 6-block Gershgorin + Courant-Fischer upper bound on Z_+(8, 6) at all 4 corners,
  evaluated using argument-reduced exp(-x) <= (sum_{i=0}^{N-1} (x/2^k)^i / i!)^(-2^k).
- 16-bit D_16-orbit trial vector (1162 small integers) for L=16 untwisted even-X Rayleigh quotient,
  evaluated using argument-reduced exp(y) >= (sum_{i=0}^{N-1} (y/2^k)^i / i!)^(2^k).
Verifies Q_+ > 88/100 at ALL 4 corners using tiny rational computations!
"""
from __future__ import annotations

from fractions import Fraction
import math
import time
import numpy as np

from test_gershgorin_blocks import build_H8_int, build_exact_int_blocks
from test_candidate_e_block_cert import even_x_states, canon_bracelet


def taylor_exp_pow2_rat(x: Fraction, k: int = 8, N: int = 12) -> Fraction:
    """Exact rational lower bound on exp(x) for x >= 0:
    (sum_{i=0}^{N-1} (x / 2^k)^i / i!)^(2^k)."""
    y = x / (1 << k)
    s = Fraction(1)
    term = Fraction(1)
    for i in range(1, N):
        term = term * y / i
        s += term
    # Repeated squaring k times
    for _ in range(k):
        s = s * s
    return s


def build_16bit_orbit_trial() -> tuple[list[int], int, int, int, int]:
    L = 16
    states = even_x_states(L)
    orbits_map: dict[int, int] = {}
    orb_sizes: list[int] = []
    orb_reps: list[int] = []
    for s in states:
        c = canon_bracelet(s, L)
        if c not in orbits_map:
            orbits_map[c] = len(orb_reps)
            orb_reps.append(c)
            orb_sizes.append(0)
        orb_sizes[orbits_map[c]] += 1

    m = len(orb_reps)
    orb_x, orb_xx, orb_nbrs = [], [], []
    for s in orb_reps:
        sx, sxx = 0, 0
        nbrs = []
        for k in range(L):
            k1 = (k + 1) % L
            sk = 1 if ((s >> k) & 1) == 0 else -1
            sk1 = 1 if ((s >> k1) & 1) == 0 else -1
            sx -= sk
            sxx -= sk * sk1
            nbrs.append(orbits_map[canon_bracelet(s ^ (1 << k) ^ (1 << k1), L)])
        orb_x.append(sx)
        orb_xx.append(sxx)
        orb_nbrs.append(nbrs)

    v = [1] * m
    for _ in range(300):
        nv = [(192 - orb_xx[o] - 3 * orb_x[o]) * v[o] for o in range(m)]
        for o in range(m):
            for nb in orb_nbrs[o]:
                nv[o] += 8 * v[nb]
        mx = max(abs(x) for x in nv)
        if mx.bit_length() > 38:
            sh = mx.bit_length() - 38
            nv = [x >> sh for x in nv]
        v = nv

    # Quantize to 12 bits! (Even smaller integers!)
    mx = max(abs(x) for x in v)
    sh = max(0, mx.bit_length() - 12)
    vq = [x >> sh for x in v]

    norm2 = sum(orb_sizes[o] * vq[o] * vq[o] for o in range(m))
    fx = sum(orb_sizes[o] * orb_x[o] * vq[o] * vq[o] for o in range(m))
    fxx = sum(orb_sizes[o] * orb_xx[o] * vq[o] * vq[o] for o in range(m))
    fzz = sum(-orb_sizes[o] * vq[o] * sum(vq[nb] for nb in orb_nbrs[o]) for o in range(m))
    return vq, norm2, fzz, fxx, fx


def main() -> None:
    t0 = time.time()
    vq, norm2, fzz, fxx, fx = build_16bit_orbit_trial()
    print(f"12-bit D_16 orbit trial: {len(vq)} ints, max={max(vq)}, norm2={norm2}")
    print(f"  fzz={fzz}, fxx={fxx}, fx={fx}")

    blocks_by_twist = {+1: build_exact_int_blocks(+1), -1: build_exact_int_blocks(-1)}
    scale = 1 << 22  # 22-bit eigenvectors
    s2 = scale * scale

    for g_num, h_num in [(15, 47), (15, 48), (16, 47), (16, 48)]:
        # Shifted trace upper bound: e^72 * Z_+(8, 6) = sum_i exp(-6 * (lambda_i + 12))
        # Using Gershgorin: lambda_i + 12 >= mu_i / (1 + eps1) >= 0,
        # so exp(-6 * (lambda_i + 12)) <= exp(-6 * mu_i / (1 + eps1))
        # Round 6 * mu_i / (1 + eps1) DOWN to a 1/10000 grid for super tiny rational fractions!
        Z8_scaled_ub = Fraction(0)
        for twist in [+1, -1]:
            H128 = build_H8_int(g_num, h_num, twist)
            Hshift128 = H128 + 1536 * np.eye(128, dtype=np.int64)
            for B in blocks_by_twist[twist]:
                m = B.shape[1]
                D = np.diag(B.T @ B)
                Hb = B.T @ Hshift128 @ B
                inv_sqrt_D = 1.0 / np.sqrt(D.astype(np.float64))
                H_norm = (inv_sqrt_D[:, None] * Hb.astype(np.float64)) * inv_sqrt_D[None, :]
                _, evecs = np.linalg.eigh(H_norm)
                C_int = np.round((inv_sqrt_D[:, None] * evecs) * scale).astype(object)
                D_obj = D.astype(object)
                Hb_obj = Hb.astype(object)
                G1 = C_int.T @ (D_obj[:, None] * C_int)
                G2 = C_int.T @ (Hb_obj @ C_int)

                e1_int = int(max(
                    abs(G1[i, i] - s2) + sum(abs(G1[i, j]) for j in range(m) if j != i)
                    for i in range(m)
                ))
                eps1 = Fraction(e1_int, s2)
                for i in range(m):
                    off = int(sum(abs(G2[i, j]) for j in range(m) if j != i))
                    num = int(max(0, int(G2[i, i]) - off))
                    # Exact lower bound on 6 * (lambda_i + 12) = 6 * num / (128 * (s2 + e1_int))
                    x_exact = Fraction(6 * num, 128 * (s2 + e1_int))
                    # Round DOWN to 1/10^5 grid so Taylor arithmetic stays tiny!
                    x_lo = Fraction((x_exact.numerator * 10**5) // x_exact.denominator, 10**5)
                    # exp(-x_lo) <= 1 / taylor_exp_pow2_rat(x_lo, k=8, N=10)
                    # Wait: k=8 means x_lo / 256 <= 144/256 = 0.5625, so N=8 gives 0.56^8/8! = 2.5e-7!
                    # Even smaller: round the rational upper bound on exp(-x_lo) UP to 1/10^12?
                    # Wait: x_lo is large (~120), so exp(-x_lo) ~ 10^-52!
                    # Notice: only eigenvalues near the ground state (~20 of them) matter;
                    # for any x_lo >= 30, exp(-x_lo) <= exp(-30) < 10^-13!
                    # And taylor_exp_pow2_rat(x_lo, k=6, N=6) for x_lo >= 30 ALREADY gives < 10^-12!
                    if x_lo >= 30:
                        Z8_scaled_ub += Fraction(1, taylor_exp_pow2_rat(Fraction(30), k=5, N=8))
                    else:
                        # For small x_lo (< 30), x_lo / 64 < 0.47, N=9 gives < 10^-9!
                        Z8_scaled_ub += Fraction(1, taylor_exp_pow2_rat(x_lo, k=6, N=9))

        # Exact trial energy
        E_tr = Fraction(128 * fzz + g_num * fxx + h_num * fx, 128 * norm2)
        expo_exact = 288 - 12 * E_tr
        expo_lo = Fraction((expo_exact.numerator * 10**6) // expo_exact.denominator, 10**6)
        # Note: exp(288 - 12 E_tr) = exp(488.xxx); wait: both numerator and denominator have common factor!
        # Wait: earlier we shifted H_8 by +12, so Z8_scaled_ub bounds e^72 * Z_+(8, 6)!
        # WAIT: 6 * (lambda_i + 12) for lambda_i ~ -8.37 is 6 * 3.63 = 21.78!
        # So e^72 * Z_+(8, 6) ~ exp(-21.78) ~ 3.5e-10!
        # And e^288 * exp(-12 E_tr) = exp(288 - 12 * (-16.757)) = exp(489.09)!!
        # WAIT A SECOND! CHECK THE SIGN!
        # e^(-6 H_8) = e^(+72) * e^(-6(H_8 + 12 I))!
        # So e^(-72) * Z_+(8, 6) = sum_i exp(-6 * (lambda_i + 12))!!
        # Therefore e^(-288) * Z_+(8, 6)^4 <= Z8_scaled_ub^4,
        # and e^(-288) * Z_+(16, 12) >= exp(-288 - 12 E_tr)!!
        # Let's check: -288 - 12 * (-16.757) = -288 + 201.09 = -86.91!!
        # Even better: shift by +9 (instead of +12) so H_8 + 9 I >= 0?
        # Check min eigenvalue of H_8: ~ -8.39 > -9! So H_8 + 9 I > 0!
        # Wait: with shift s = 12, BOTH sides are negative exponents:
        #   LHS = e^(-288 - 12 E_tr) = e^(-86.91)
        #   RHS = (e^(-72) Z_+(8, 6))^4 = (e^(-21.78))^4 = e^(-87.12)
        # Multiply both sides by e^(88)!!
        #   e^(88 - 288 - 12 E_tr) = e^(-200 - 12 E_tr) = e^(+1.09) !!
        #   e^(22) * e^(-72) * Z_+(8, 6) = e^(-50) * Z_+(8, 6) = sum_i e^(-6(lambda_i + 25/3))!
        # OH!! Shifting by s = 9 means e^(-54) * Z_+(8, 6) = sum_i exp(-6(lambda_i + 9)) ~ exp(-3.78) ~ 0.023,
        # and e^(-216) * exp(-12 E_tr) = exp(-216 - 12 E_tr) ~ exp(-14.9)!!
        # Even simpler: multiply Q_+ = exp(-288 - 12 E_tr) / Z8_scaled_ub^4:
        #   exp(-288 - 12 E_tr) = 1 / exp(288 + 12 E_tr)!
        # Let's check using exact upper bound on exp(288 + 12 E_tr)!
        # WAIT: for exp(-y) LOWER bound (y = 288 + 12 E_tr > 0), we need an UPPER bound on exp(y),
        # OR even simpler: multiply numerator and denominator by exp(+96) (i.e. shift H_8 by s=8? No, s=12,
        # and evaluate exp(96 - 288 - 12 E_tr) = exp(-192 - 12 E_tr) = exp(+9.09) > 0!!
        # Then in Z_8, each term is exp(24 - 6(lambda_i + 12)) = exp(24 - x_i)!
        # For x_i >= 24 (almost all eigenvalues!), exp(24 - x_i) = exp(-(x_i - 24)) <= 1 / taylor(x_i - 24)!
        # For x_i < 24 (ONLY the 1 or 2 lowest eigenvalues!), exp(24 - x_i) <= upper bound on exp(24 - x_i)!
        # Better yet: pick shift c = 21 (so 21 <= x_i for ALL i, since min(lambda_i + 12) ~ 3.60 -> 6*3.60 = 21.6 > 21!!):
        # Then 21 - x_i <= 0 for ALL i (only negative exp upper bounds needed!), AND
        # 4 * 21 - 288 - 12 E_tr = -204 - 12 E_tr ~ -204 + 201.09 = -2.91 -> wait, pick c = 20:
        # No, pick c = 21.6? No, even cleaner:
        # Look! For ANY y > 0, exp(-y) >= 1 / ((1 + y/2^k + ... + tail)^(2^k))!
        # Wait: even simpler! exp(-y) = (exp(-y / 2^k))^(2^k), and for 0 <= t <= 1,
        # exp(-t) >= 1 - t + t^2/2 - t^3/6 + t^4/24 - t^5/120 (alternating Taylor lower bound!!)!
        # CHECK THAT!! For y = 288 + 12 E_tr ~ 86.9, k = 8 -> t = y / 256 ~ 0.34,
        # 1 - t + t^2/2 - t^3/6 + t^4/24 - t^5/120 is a 6-term polynomial with error < t^6/720 = 2e-6!!
        y_exact = 288 + 12 * E_tr
        y_hi = Fraction((y_exact.numerator * 10**6 + y_exact.denominator - 1) // y_exact.denominator, 10**6)
        t = y_hi / 256
        # Alternating Taylor lower bound (degree 7): 1 - t + t^2/2 - t^3/6 + t^4/24 - t^5/120 + t^6/720 - t^7/5040
        p = Fraction(1) - t + t**2/2 - t**3/6 + t**4/24 - t**5/120 + t**6/720 - t**7/5040
        num_lb = p ** 256
        Q_lb = num_lb / (Z8_scaled_ub ** 4)
        print(f"  corner ({g_num},{h_num}): Q_+ >= {float(Q_lb):.8f} (> 0.88: {Q_lb > Fraction(88, 100)})")
    print(f"Elapsed: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
