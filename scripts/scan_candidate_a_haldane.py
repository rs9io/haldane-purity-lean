#!/usr/bin/env python3
"""
Exploratory exact-diagonalization + axial D2-sector moment-inference scanner
for Candidate A: Spin-1 XXZ + single-ion anisotropy
    H_L(Delta, D) = sum_{i=0}^{L-1} [ S^x_i S^x_{i+1} + S^y_i S^y_{i+1}
                                      + Delta * S^z_i S^z_{i+1} + D * (S^z_i)^2 ].

1. Sanity check against OpenAI's Table (lem:thermal-inputs, b = 49/4, a = 700741/500000)
   at isotropic (Delta=1, D=0) for L = 4..8, verifying Z_n(b, 1), Z_n(b, Rz), Z_n(b, Rx).
2. Axial D2-sector decomposition (valid for ALL Delta, D, no C3 needed!):
     J_n   = (Z_n(1) + Z_n(Rz) + 2 Z_n(Rx)) / 4     (D2-trivial)
     Nz_n  = (Z_n(1) + Z_n(Rz) - 2 Z_n(Rx)) / 4     (Rz=+1, Rx=-1)
     Nxy_n = (Z_n(1) - Z_n(Rz)) / 4                 (Rz=-1, multiplicity 2 by Rz(pi/2))
   Checks finite-size spectra + dominant-weight isolation at (Delta=1, D=1/4) and nearby points.
   NOTE: Unenclosed FP64 exploratory diagnostic only — NOT a rigorous proof certificate.
"""

import math
import time
import numpy as np
from scipy.linalg import eigvalsh


def build_d2_blocks_spectrum(L, Delta, D, twist="none"):
    """
    Exact full spectrum of H_L(Delta, D) with spatial twist in {"none", "Rz", "Rx"}
    using the real Cartesian basis {|x>, |y>, |z>} where:
      (Sz)^2 = diag(1, 1, 0)
      Rx(pi) = diag(+1, -1, -1),  Ry(pi) = diag(-1, +1, -1),  Rz(pi) = diag(-1, -1, +1)
      Sx: |y> <-> |z> (off-diag +/- i -> Sx_i Sx_j is REAL!)
      Sy: |z> <-> |x> (off-diag +/- i -> Sy_i Sy_j is REAL!)
      Sz: |x> <-> |y> (off-diag +/- i -> Sz_i Sz_j is REAL!)
    Specifically, in {|x>, |y>, |z>} (indices 0, 1, 2):
      (Sx)_{1,2} = -i, (Sx)_{2,1} = +i  =>  (Sx ⊗ Sx) maps |1,1> <-> -|2,2>, |1,2> <-> +|2,1>
      (Sy)_{2,0} = -i, (Sy)_{0,2} = +i  =>  (Sy ⊗ Sy) maps |2,2> <-> -|0,0>, |2,0> <-> +|0,2>
      (Sz)_{0,1} = -i, (Sz)_{1,0} = +i  =>  (Sz ⊗ Sz) maps |0,0> <-> -|1,1>, |0,1> <-> +|1,0>
    Wait: verify Sx, Sy, Sz satisfy [Sx, Sy] = i Sz and Sx^2+Sy^2+Sz^2 = 2 I:
      (S_a)_{bc} = -i * eps_{abc}  =>  (S_a ⊗ S_a)_{(b1,b2),(c1,c2)} = -eps_{a b1 c1} * eps_{a b2 c2} (REAL!).
    Twist signs on closing bond (L-1, 0):
      "none": (tx, ty, tz) = (+1, +1, +1)
      "Rz":   (tx, ty, tz) = (-1, -1, +1)
      "Rx":   (tx, ty, tz) = (+1, -1, -1)
    """
    dim = 3 ** L
    states = np.arange(dim, dtype=np.int32)
    digits = np.empty((dim, L), dtype=np.int8)
    tmp = states.copy()
    for i in range(L - 1, -1, -1):
        digits[:, i] = tmp % 3
        tmp //= 3

    # D2 parities: count of 0s (mod 2) and count of 1s (mod 2)
    # Every S_a ⊗ S_a flips two sites among the two states != a, preserving parities of #0, #1, #2!
    p0 = np.sum(digits == 0, axis=1) & 1
    p1 = np.sum(digits == 1, axis=1) & 1
    sector = 2 * p0 + p1  # 0, 1, 2, 3

    # Diagonal: D * sum_i (Sz_i)^2 = D * sum_i (digits != 2)
    diag_e = D * np.sum(digits != 2, axis=1).astype(np.float64)
    powers = (3 ** np.arange(L - 1, -1, -1, dtype=np.int32))

    # Coupling signs on each bond (i, (i+1)%L)
    if twist == "none":
        tw_signs = (1.0, 1.0, 1.0)
    elif twist == "Rz":
        tw_signs = (-1.0, -1.0, 1.0)
    elif twist == "Rx":
        tw_signs = (1.0, -1.0, -1.0)
    else:
        raise ValueError(twist)

    # For each axis a in {0(x), 1(y), 2(z)}, the two active states are (u, v) = ((a+1)%3, (a+2)%3)
    # eps_{a u v} = +1, eps_{a v u} = -1
    # -eps_{a b1 c1} * eps_{a b2 c2}:
    #   (u,u) <-> (v,v) gets -1
    #   (u,v) <-> (v,u) gets +1
    axis_pairs = [(1, 2, 1.0), (2, 0, 1.0), (0, 1, Delta)]

    all_evals = []
    for sec in range(4):
        idx = np.flatnonzero(sector == sec)
        n = len(idx)
        if n == 0:
            continue
        loc = np.full(dim, -1, dtype=np.int32)
        loc[idx] = np.arange(n, dtype=np.int32)
        H = np.zeros((n, n), dtype=np.float64)
        np.fill_diagonal(H, diag_e[idx])
        d_sub = digits[idx]

        for i in range(L):
            j = (i + 1) % L
            di = d_sub[:, i]
            dj = d_sub[:, j]
            is_closing = (i == L - 1)
            for a, (u, v, J_a) in enumerate(axis_pairs):
                coeff = J_a * (tw_signs[a] if is_closing else 1.0)
                if coeff == 0.0:
                    continue
                # (u, u) -> (v, v) with weight -coeff
                m1 = (di == u) & (dj == u)
                r1 = np.flatnonzero(m1)
                if len(r1):
                    ns = idx[r1] + (v - u) * powers[i] + (v - u) * powers[j]
                    c1 = loc[ns]
                    H[r1, c1] += -coeff
                    H[c1, r1] += -coeff
                # (u, v) -> (v, u) with weight +coeff
                m2 = (di == u) & (dj == v)
                r2 = np.flatnonzero(m2)
                if len(r2):
                    ns = idx[r2] + (v - u) * powers[i] + (u - v) * powers[j]
                    c2 = loc[ns]
                    H[r2, c2] += coeff
                    H[c2, r2] += coeff
        all_evals.append(eigvalsh(H))
    return np.concatenate(all_evals)


def shifted_Z(evals, L, b, a):
    """Compute Z_L(b) = sum_k exp(-b * (E_k + a * L))."""
    x = -b * (evals + a * L)
    m = np.max(x)
    return math.exp(m) * float(np.sum(np.exp(x - m)))


def main():
    t0 = time.time()
    print("=== 1. Sanity check vs OpenAI lem:thermal-inputs (Delta=1, D=0, b=49/4, a=700741/500000) ===")
    b_s1 = 49.0 / 4.0
    a_s1 = 700741.0 / 500000.0
    openai_ref = {
        4: (124.885379, 0.065757),
        5: (0.002925, 2.960742),
        6: (12.870614, 0.286599),
        7: (0.054069, 1.920414),
        8: (4.639283, 0.510140),
    }
    print(f"{'L':>2} | {'Z(1) calc':>12} {'Z(1) ref':>12} | {'Z(Rz) calc':>12} {'Z(Rx) calc':>12} {'Z(P) ref':>12}")
    for L in range(4, 9):
        ev1 = build_d2_blocks_spectrum(L, 1.0, 0.0, "none")
        evz = build_d2_blocks_spectrum(L, 1.0, 0.0, "Rz")
        evx = build_d2_blocks_spectrum(L, 1.0, 0.0, "Rx")
        z1 = shifted_Z(ev1, L, b_s1, a_s1)
        zz = shifted_Z(evz, L, b_s1, a_s1)
        zx = shifted_Z(evx, L, b_s1, a_s1)
        r1, rp = openai_ref[L]
        print(f"{L:2d} | {z1:12.6f} {r1:12.6f} | {zz:12.6f} {zx:12.6f} {rp:12.6f}")

    print("\n=== 2. Candidate A Haldane scan: Spin-1 XXZ + D*(Sz)^2 at (Delta=1, D=1/4) ===")
    Delta, D = 1.0, 0.25
    # Estimate ground-state energy density e0 from L=8
    ev8 = build_d2_blocks_spectrum(8, Delta, D, "none")
    ev8_s = np.sort(ev8)
    print(f"L=8 lowest 6 eigenvalues at (Delta={Delta}, D={D}): {np.round(ev8_s[:6], 6)}")
    print(f"L=8 gap E1 - E0 = {ev8_s[1] - ev8_s[0]:.6f}, e0(8) = {ev8_s[0]/8:.8f}")
    # Pick shift a near -e0_inf (estimate from L=6, 8)
    ev6 = build_d2_blocks_spectrum(6, Delta, D, "none")
    e0_6 = np.min(ev6) / 6.0
    e0_8 = ev8_s[0] / 8.0
    print(f"e0(6) = {e0_6:.8f}, e0(8) = {e0_8:.8f}")
    a_est = -e0_8 + 0.002  # slightly above -e0_inf so e0_inf + a < 0? Wait: we want E0(L) < -a*L => a < -e0_inf!
    a_est = -e0_8 - 0.003  # conservative shift so -e0_inf > a_est
    b_test = 10.0
    print(f"\nAxial D2 sector moments at (Delta=1, D=1/4), b={b_test}, a={a_est:.6f}:")
    print(f"{'L':>2} | {'Z(1)':>11} {'Z(Rz)':>11} {'Z(Rx)':>11} | {'J_L':>11} {'Nz_L':>11} {'Nxy_L':>11}")
    for L in range(4, 9):
        ev1 = build_d2_blocks_spectrum(L, Delta, D, "none")
        evz = build_d2_blocks_spectrum(L, Delta, D, "Rz")
        evx = build_d2_blocks_spectrum(L, Delta, D, "Rx")
        z1 = shifted_Z(ev1, L, b_test, a_est)
        zz = shifted_Z(evz, L, b_test, a_est)
        zx = shifted_Z(evx, L, b_test, a_est)
        J = (z1 + zz + 2 * zx) / 4.0
        Nz = (z1 + zz - 2 * zx) / 4.0
        Nxy = (z1 - zz) / 4.0
        print(f"{L:2d} | {z1:11.6f} {zz:11.6f} {zx:11.6f} | {J:11.6f} {Nz:11.6f} {Nxy:11.6f}")
    print(f"\nElapsed: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
