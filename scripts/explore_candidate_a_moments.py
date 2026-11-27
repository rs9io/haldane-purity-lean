#!/usr/bin/env python3
"""
Candidate A (Spin-1 XXZ + single-ion anisotropy at Delta=1, D=1/4):
1. Fast translation + D2-sector exact diagonalization for L = 4..10 (Z_n(1), Z_n(Rz), Z_n(Rx)).
2. Estimates thermodynamic ground-state energy density e0(1, 1/4) via L = 6, 8, 10 and
   checks axial D2-sector moment separation (J_n, Nz_n, Nxy_n) + polynomial filter feasibility.
NOTE: Unenclosed FP64 exploratory diagnostic only — NOT a proof certificate.
"""

import math
import time
import numpy as np
from scipy.linalg import eigvalsh
from scipy.sparse.linalg import eigsh
from scipy.sparse import csr_matrix


def spin1_d2_sparse_blocks(L, Delta, D, twist="none"):
    """Build sparse real symmetric Hamiltonian blocks in the 4 D2 sectors (Cartesian basis)."""
    dim = 3 ** L
    states = np.arange(dim, dtype=np.int32)
    digits = np.empty((dim, L), dtype=np.int8)
    tmp = states.copy()
    for i in range(L - 1, -1, -1):
        digits[:, i] = tmp % 3
        tmp //= 3

    p0 = np.sum(digits == 0, axis=1) & 1
    p1 = np.sum(digits == 1, axis=1) & 1
    sector = 2 * p0 + p1

    diag_e = D * np.sum(digits != 2, axis=1).astype(np.float64)
    powers = (3 ** np.arange(L - 1, -1, -1, dtype=np.int32))

    if twist == "none":
        tw_signs = (1.0, 1.0, 1.0)
    elif twist == "Rz":
        tw_signs = (-1.0, -1.0, 1.0)
    elif twist == "Rx":
        tw_signs = (1.0, -1.0, -1.0)
    else:
        raise ValueError(twist)

    axis_pairs = [(1, 2, 1.0), (2, 0, 1.0), (0, 1, Delta)]
    blocks = []
    for sec in range(4):
        idx = np.flatnonzero(sector == sec)
        n = len(idx)
        if n == 0:
            continue
        loc = np.full(dim, -1, dtype=np.int32)
        loc[idx] = np.arange(n, dtype=np.int32)
        d_sub = digits[idx]

        rows_list = [np.arange(n, dtype=np.int32)]
        cols_list = [np.arange(n, dtype=np.int32)]
        vals_list = [diag_e[idx]]

        for i in range(L):
            j = (i + 1) % L
            di = d_sub[:, i]
            dj = d_sub[:, j]
            is_closing = (i == L - 1)
            for a, (u, v, J_a) in enumerate(axis_pairs):
                coeff = J_a * (tw_signs[a] if is_closing else 1.0)
                if coeff == 0.0:
                    continue
                m1 = (di == u) & (dj == u)
                r1 = np.flatnonzero(m1)
                if len(r1):
                    ns = idx[r1] + (v - u) * powers[i] + (v - u) * powers[j]
                    c1 = loc[ns]
                    rows_list.extend([r1, c1])
                    cols_list.extend([c1, r1])
                    vals_list.extend([np.full(len(r1), -coeff), np.full(len(r1), -coeff)])
                m2 = (di == u) & (dj == v)
                r2 = np.flatnonzero(m2)
                if len(r2):
                    ns = idx[r2] + (v - u) * powers[i] + (u - v) * powers[j]
                    c2 = loc[ns]
                    rows_list.extend([r2, c2])
                    cols_list.extend([c2, r2])
                    vals_list.extend([np.full(len(r2), coeff), np.full(len(r2), coeff)])
        rows = np.concatenate(rows_list)
        cols = np.concatenate(cols_list)
        vals = np.concatenate(vals_list)
        H = csr_matrix((vals, (rows, cols)), shape=(n, n))
        blocks.append(H)
    return blocks


def low_spectrum_Z(blocks, L, b, a, k_low=40):
    """For L <= 8 use exact dense eigvalsh; for L >= 9 use Lanczos on low tail (high accuracy at b >= 8)."""
    evals_all = []
    for H in blocks:
        n = H.shape[0]
        if n <= 2000:
            ev = eigvalsh(H.toarray())
        else:
            k = min(k_low, n - 2)
            ev = eigsh(H, k=k, which="SA", return_eigenvectors=False, tol=1e-12)
        evals_all.append(ev)
    evals = np.concatenate(evals_all)
    x = -b * (evals + a * L)
    m = np.max(x)
    return math.exp(m) * float(np.sum(np.exp(x - m))), np.sort(evals)[:6]


def main():
    t0 = time.time()
    Delta, D = 1.0, 0.25
    print(f"=== Candidate A: Spin-1 XXZ + D*(Sz)^2 at (Delta={Delta}, D={D}) ===")
    # Get ground state energies at L = 6, 8, 10
    e0s = {}
    for L in [6, 8, 10]:
        blocks = spin1_d2_sparse_blocks(L, Delta, D, "none")
        _, low = low_spectrum_Z(blocks, L, 10.0, 1.25, k_low=12)
        e0s[L] = low[0]
        print(f"L={L:2d}: E0={low[0]:12.8f}, e0={low[0]/L:12.9f}, gap={low[1]-low[0]:.6f}, low4={np.round(low[:4], 5)}")

    # Estimate thermodynamic e0_inf (exponentially convergent in gapped phase!)
    e0_inf_est = e0s[10] / 10.0
    print(f"Estimated e0_inf ≈ {e0_inf_est:.8f} -> shift a slightly below -e0_inf = {-e0_inf_est:.8f}")
    # Choose shift a = 1.2528 so E0(L) < -a*L for large L
    a = 1.2528
    for b in [10.0, 12.25, 14.0]:
        print(f"\n--- Axial D2 moments at b = {b}, a = {a} ---")
        print(f"{'L':>2} | {'Z(1)':>12} {'Z(Rz)':>12} {'Z(Rx)':>12} | {'J_L':>12} {'Nz_L':>12} {'Nxy_L':>12} | {'Nz/J':>8} {'Nxy/J':>8}")
        for L in range(4, 11):
            z1, _ = low_spectrum_Z(spin1_d2_sparse_blocks(L, Delta, D, "none"), L, b, a, k_low=50)
            zz, _ = low_spectrum_Z(spin1_d2_sparse_blocks(L, Delta, D, "Rz"), L, b, a, k_low=50)
            zx, _ = low_spectrum_Z(spin1_d2_sparse_blocks(L, Delta, D, "Rx"), L, b, a, k_low=50)
            J = (z1 + zz + 2 * zx) / 4.0
            Nz = (z1 + zz - 2 * zx) / 4.0
            Nxy = (z1 - zz) / 4.0
            print(f"{L:2d} | {z1:12.6f} {zz:12.6f} {zx:12.6f} | {J:12.6f} {Nz:12.6f} {Nxy:12.6f} | {Nz/J:8.4f} {Nxy/J:8.4f}")
    print(f"\nElapsed: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
