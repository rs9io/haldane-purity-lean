#!/usr/bin/env python3
"""
Exact integer & rational witness generator/verifier for Candidate E:
  H = -sum_i Z_i Z_{i+1} - g sum_i X_i X_{i+1} - h sum_i X_i
on the coupling rectangle (g, h) in [15/128, 16/128] x [47/128, 48/128].

Reproduces Codex Round 1's exact rational bounds on Q_+(8, 6) at all 4 corners,
checks the 3 rounded coupled updates to (L_0, beta_0) = (64, 48), and inspects
D_8 / D_16 symmetry orbit dimensions for fast in-Lean verification.
"""
from __future__ import annotations

from fractions import Fraction
import math
import time
import numpy as np


def even_x_states(L: int) -> list[int]:
    """Basis states |b_0 ... b_{L-1}> in the product-X basis with even popcount
    (i.e. prod_i X_i = +1, where X_i = 1 - 2*b_i)."""
    return [s for s in range(1 << L) if s.bit_count() % 2 == 0]


def build_H8_int(g_num: int, h_num: int, twist: int) -> list[list[int]]:
    """Build exact integer matrix 128 * H_8^(twist) on the 128-dim even-X sector.
    twist = +1 (periodic) or -1 (antiperiodic closing ZZ bond)."""
    L = 8
    states = even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    assert n == 128
    M = [[0] * n for _ in range(n)]
    for i, s in enumerate(states):
        # Diagonal: -g sum_k sigma_k sigma_{k+1} - h sum_k sigma_k
        diag = 0
        for k in range(L):
            sk = 1 if ((s >> k) & 1) == 0 else -1
            sk1 = 1 if ((s >> ((k + 1) % L)) & 1) == 0 else -1
            diag += -g_num * (sk * sk1) - h_num * sk
        M[i][i] = diag
        # Off-diagonal: -Z_k Z_{k+1} (with closing bond multiplied by twist)
        for k in range(L):
            k1 = (k + 1) % L
            s2 = s ^ (1 << k) ^ (1 << k1)
            j = idx[s2]
            coeff = -128 if k < L - 1 else -128 * twist
            M[i][j] += coeff
    return M


def trace_exp_B_exact_upper(H128: list[list[int]], deg: int = 320) -> tuple[Fraction, Fraction]:
    """Compute exact rational trace of sum_{k=0}^{deg} ((6/128) B)^k / k!
    where B = 1536 I - 128 H_8^(t), plus exact positive remainder bound.
    Returns (poly_trace, tail_bound) for e^(72) * Tr(e^(-6 H_8^(t)))."""
    n = len(H128)
    # B = 1536 I - H128
    B = [[-H128[i][j] + (1536 if i == j else 0) for j in range(n)] for i in range(n)]
    # Check symmetry & store sparse rows for fast exact integer matmul
    rows = [[(j, val) for j, val in enumerate(B[i]) if val != 0] for i in range(n)]

    # Compute Tr(B^k) for k = 0..deg by tracking e_m^T B^k e_m or full matrix powers?
    # Note: we only need Tr(B^k)! Even faster: since B is symmetric, compute B^k column by column
    # or just maintain V_k = B^k (128x128 sparse-dense matmul takes ~128*128*9 = 1.5e5 integer ops/step).
    # Wait: even better, compute for k = 0..deg using dense list of rows with sparse B!
    cur = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    traces = [n]
    for k in range(1, deg + 1):
        # nxt[i][j] = sum_l B[i][l] * cur[l][j]
        nxt = [[0] * n for _ in range(n)]
        tr = 0
        for i in range(n):
            ri = rows[i]
            ni = nxt[i]
            for l, b_il in ri:
                cl = cur[l]
                for j in range(n):
                    ni[j] += b_il * cl[j]
            tr += ni[i]
        cur = nxt
        traces.append(tr)

    # Evaluate sum_{k=0}^{deg} traces[k] * (6/128)^k / k! as exact Fraction
    # Using common scale or Horner: sum_{k=0}^{deg} traces[k] * (3/64)^k / k!
    # Wait: compute exact rational via reversed Horner:
    # S = sum_{k=0}^deg traces[k] * (3^k) / (64^k * k!)
    # Better: accumulate numerator / denominator cleanly
    fact = 1
    p3 = 1
    p64 = 1
    total = Fraction(0)
    for k in range(deg + 1):
        if k > 0:
            fact *= k
            p3 *= 3
            p64 *= 64
        total += Fraction(traces[k] * p3, p64 * fact)

    # Remainder bound for one 128-dim block:
    # 0 <= (6/128) B <= 144 I, so each eigenvalue contributes <= 144^(deg+1)/(deg+1)! / (1 - 144/(deg+2))
    fact_next = fact * (deg + 1)
    tail_block = Fraction(128 * (144 ** (deg + 1)), fact_next) / (1 - Fraction(144, deg + 2))
    return total, tail_block


def generate_trial_16() -> tuple[list[int], int, int, int, int]:
    """Regenerate Codex's 16-site integer trial vector in even-X sector at (g, h) = (1/8, 3/8),
    and compute its exact integer Rayleigh forms:
      norm2 = <v, v>
      f_zz  = <v, (-sum Z_i Z_{i+1}) v>
      f_xx  = <v, (-sum X_i X_{i+1}) v>
      f_x   = <v, (-sum X_i) v>
    so E_tr(g, h) = (f_zz + g * f_xx + h * f_x) / norm2."""
    L = 16
    states = even_x_states(L)
    n = len(states)
    assert n == 32768
    idx = np.full(1 << L, -1, dtype=np.int32)
    for i, s in enumerate(states):
        idx[s] = i

    # Precompute diagonal arrays (integer sums of sigma_k and sigma_k sigma_{k+1})
    s_arr = np.array(states, dtype=np.int32)
    sum_x = np.zeros(n, dtype=np.int64)
    sum_xx = np.zeros(n, dtype=np.int64)
    neighbors = np.zeros((L, n), dtype=np.int32)
    for k in range(L):
        k1 = (k + 1) % L
        bk = (s_arr >> k) & 1
        bk1 = (s_arr >> k1) & 1
        sk = 1 - 2 * bk
        sk1 = 1 - 2 * bk1
        sum_x += sk
        sum_xx += sk * sk1
        neighbors[k] = idx[s_arr ^ (1 << k) ^ (1 << k1)]

    # Operator M = 192 I - 8 H_{16}^(+) at g=1/8, h=3/8:
    # 8 H = -8 sum ZZ - 1 sum XX - 3 sum X
    # M = (192 + sum_xx + 3 * sum_x) diag + 8 * sum_{k=0}^{15} flip(k, k+1)
    diag_M = (192 + sum_xx + 3 * sum_x).tolist()
    nbr_lists = [neighbors[k].tolist() for k in range(L)]

    v = [1] * n
    for step in range(300):
        nv = [diag_M[i] * v[i] for i in range(n)]
        for k in range(L):
            nk = nbr_lists[k]
            for i in range(n):
                nv[i] += 8 * v[nk[i]]
        mx = max(abs(x) for x in nv)
        bits = mx.bit_length()
        if bits > 38:
            shift = bits - 38
            nv = [x >> shift for x in nv]
        v = nv

    norm2 = sum(x * x for x in v)
    f_x = sum(-int(sum_x[i]) * v[i] * v[i] for i in range(n))
    f_xx = sum(-int(sum_xx[i]) * v[i] * v[i] for i in range(n))
    f_zz = 0
    for k in range(L):
        nk = nbr_lists[k]
        f_zz += sum(-v[i] * v[nk[i]] for i in range(n))
    return v, norm2, f_zz, f_xx, f_x


def ceil_grid7(x: Fraction) -> Fraction:
    scale = 10 ** 7
    y = x * scale
    c = y.numerator // y.denominator + (1 if y.numerator % y.denominator != 0 else 0)
    return Fraction(c, scale)


def fQ(u: Fraction) -> Fraction:
    return u * u / (2 * (1 - u) * (1 - u))


def count_orbits(L: int) -> int:
    """Count D_L bracelet orbits on even-popcount length-L bitstrings."""
    states = even_x_states(L)
    seen = set()
    orbits = 0
    mask = (1 << L) - 1
    for s in states:
        if s in seen:
            continue
        orbits += 1
        # Generate dihedral orbit
        cur = s
        for _ in range(L):
            seen.add(cur)
            # Reverse bits
            rev = 0
            for b in range(L):
                if (cur >> b) & 1:
                    rev |= 1 << (L - 1 - b)
            seen.add(rev)
            cur = ((cur << 1) | (cur >> (L - 1))) & mask
    return orbits


def main() -> None:
    t0 = time.time()
    print(f"D_8 even-X orbits (L=8):  {count_orbits(8)}")
    print(f"D_16 even-X orbits (L=16): {count_orbits(16)}")

    print("\n1. Generating 16-site integer trial vector (300 power steps)...")
    v, norm2, f_zz, f_xx, f_x = generate_trial_16()
    print(f"   norm2 = {norm2}")
    print(f"   Codex = 20136008109374295350016434 (match={norm2 == 20136008109374295350016434})")
    print(f"   f_zz  = {f_zz}")
    print(f"   f_xx  = {f_xx}")
    print(f"   f_x   = {f_x}")

    # Check if trial vector is constant on D_16 orbits!
    L = 16
    states = even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    mask = (1 << L) - 1
    orbit_inv = True
    for i, s in enumerate(states):
        rot = ((s << 1) | (s >> (L - 1))) & mask
        if v[i] != v[idx[rot]]:
            orbit_inv = False
            break
    print(f"   Trial vector is translation-invariant: {orbit_inv}")

    print("\n2. Computing exact rational Q_+ lower bounds at all 4 rectangle corners...")
    corners = [(15, 47), (15, 48), (16, 47), (16, 48)]
    for g_num, h_num in corners:
        H_p = build_H8_int(g_num, h_num, +1)
        H_m = build_H8_int(g_num, h_num, -1)
        tr_p, tail_p = trace_exp_B_exact_upper(H_p, deg=320)
        tr_m, tail_m = trace_exp_B_exact_upper(H_m, deg=320)
        Z8_scaled_U = tr_p + tail_p + tr_m + tail_m  # upper bound on e^72 * Z_+(8, 6)

        # Exact trial energy E_tr(g, h) = (f_zz + (g_num/128)*f_xx + (h_num/128)*f_x) / norm2
        E_tr = Fraction(128 * f_zz + g_num * f_xx + h_num * f_x, 128 * norm2)
        # Exponent for e^288 * e^(-12 E_tr) = e^(288 - 12 E_tr)
        # Note Z_+(16, 12) >= e^(-12 E_tr), and e^288 Z_+(8,6)^4 = (e^72 Z_+(8,6))^4 <= Z8_scaled_U^4
        # Round exponent down slightly to a clean rational for fast Taylor lower bound:
        expo_exact = 288 - 12 * E_tr
        # Rational lower bound on expo_exact with denom 10^9
        expo_lo = Fraction((expo_exact.numerator * 10**9) // expo_exact.denominator, 10**9)
        assert expo_lo <= expo_exact and expo_lo > 0

        # Degree-800 Taylor lower bound on exp(expo_lo)
        term = Fraction(1)
        num_lb = Fraction(1)
        for k in range(1, 801):
            term = term * expo_lo / k
            num_lb += term

        Q_lb = num_lb / (Z8_scaled_U ** 4)
        print(f"   (128g={g_num}, 128h={h_num}): E_tr={float(E_tr):.10f}, Q_+ >= {float(Q_lb):.8f} (> 0.88: {Q_lb > Fraction(88, 100)})")

    print("\n3. Checking 3 rounded coupled updates from (p0=62/1000, q0=12/100)...")
    p, q = Fraction(62, 1000), Fraction(12, 100)
    for r in range(1, 4):
        p = ceil_grid7(fQ(1 - (1 - p) ** 2 * (1 - q)))
        q = ceil_grid7(fQ(1 - (1 - q) ** 2 * (1 - p)))
        print(f"   Round {r}: p={p} ({float(p):.7f}), q={q} ({float(q):.7f})")
    print(f"   Both < 1/100: {p < Fraction(1, 100) and q < Fraction(1, 100)}")
    print(f"   Total elapsed: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
