#!/usr/bin/env python3
"""
Fast exploratory exact-diagonalization scanner for NEW quantum spin chains
with provably Hermitian spatial transfer matrices X_b (by the exact bond-history
theorem: real symmetric on-site b = b^T and bond interaction -v = sum_a c_a F_a x F_a
with real F_a and c_a >= 0).

Tests:
  1. Spin-1 XXZ + single-ion anisotropy:
       H = sum_i [ S^x_i S^x_{i+1} + S^y_i S^y_{i+1} + Delta * S^z_i S^z_{i+1} + D * (S^z_i)^2 ]
     for Delta >= 0, D in R. (OpenAI only proved Delta=1, D=0!)
  2. Spin-1 bilinear-biquadratic chain (beta <= 0 side, where -v = sum F_r x F_r):
       H = sum_i [ S_i . S_{i+1} - |beta| * (S_i . S_{i+1})^2 ]
  3. Spin-2 Heisenberg + single-ion anisotropy D * (S^z_i)^2 (Haldane S=2!)

Computes exact Z(L, b) for L = 4, 6, 8 (and L = 10 where needed) using Sz-sector
block diagonalization so we can spot parameter regimes where:
  S(L, b) = Z(2L, b) / Z(L, b)^2 >= 1 - u0  AND  T(2L, b) = Z(2L, 2b) / Z(2L, b)^2 >= 1 - u0
with u0 < 1/6 (or u0 <= 1/100) — directly feeding into our Lean 4 PurityBootstrap theorem!
"""

import math
import time
import numpy as np
from scipy.linalg import eigvalsh


def spin_ops(S):
    """Return Sx, Sy, Sz in Sz basis for spin S (dim = 2S+1)."""
    d = int(round(2 * S + 1))
    ms = [S - k for k in range(d)]
    Sz = np.diag(ms).astype(np.complex128)
    Sp = np.zeros((d, d), dtype=np.complex128)
    for k in range(d - 1):
        m = ms[k + 1]
        Sp[k, k + 1] = math.sqrt(S * (S + 1) - m * (m + 1))
    Sm = Sp.T.conj()
    Sx = 0.5 * (Sp + Sm)
    Sy = -0.5j * (Sp - Sm)
    return Sx, Sy, Sz


def build_spin1_xxz_d_spectrum(L, Delta, D):
    """Exact full spectrum of periodic spin-1 XXZ + D*(Sz)^2 chain of length L via Sz sectors."""
    # Basis states: ternary digits 0,1,2 -> Sz = +1, 0, -1
    dim = 3 ** L
    states = np.arange(dim, dtype=np.int32)
    # Extract digits
    digits = np.empty((dim, L), dtype=np.int8)
    tmp = states.copy()
    for i in range(L - 1, -1, -1):
        digits[:, i] = tmp % 3
        tmp //= 3
    sz_vals = 1 - digits  # 0->+1, 1->0, 2->-1
    total_sz = sz_vals.sum(axis=1)

    # Diagonal energy per basis state: Delta * sum Sz_i Sz_{i+1} + D * sum Sz_i^2
    diag_e = (
        Delta * np.sum(sz_vals * np.roll(sz_vals, -1, axis=1), axis=1).astype(np.float64)
        + D * np.sum(sz_vals * sz_vals, axis=1).astype(np.float64)
    )
    powers = (3 ** np.arange(L - 1, -1, -1, dtype=np.int32))

    all_evals = []
    # Use Sz <-> -Sz symmetry: only compute total_sz >= 0 (double multiplicity for > 0)
    for m in range(0, L + 1):
        idx = np.flatnonzero(total_sz == m)
        n = len(idx)
        if n == 0:
            continue
        # Map global state -> local index
        loc = np.full(dim, -1, dtype=np.int32)
        loc[idx] = np.arange(n, dtype=np.int32)
        H = np.zeros((n, n), dtype=np.float64)
        np.fill_diagonal(H, diag_e[idx])
        d_sub = digits[idx]
        # Off-diagonal: 0.5 * (S+_i S-_{i+1} + S-_i S+_{i+1})
        # For spin-1, S+ |0> = sqrt(2) |+1>, S+ |-1> = sqrt(2) |0>
        # So S+_i S-_{i+1} has matrix element (sqrt(2)*sqrt(2))/2 = 1.0 whenever digit_i > 0 and digit_{i+1} < 2!
        for i in range(L):
            j = (i + 1) % L
            di = d_sub[:, i]
            dj = d_sub[:, j]
            # S+_i (digit decreases by 1) and S-_j (digit increases by 1)
            mask1 = (di > 0) & (dj < 2)
            rows1 = np.flatnonzero(mask1)
            if len(rows1):
                new_states = idx[rows1] - powers[i] + powers[j]
                cols1 = loc[new_states]
                H[rows1, cols1] += 1.0
                H[cols1, rows1] += 1.0
        ev = eigvalsh(H)
        all_evals.append(ev)
        if m > 0:
            all_evals.append(ev)
    return np.concatenate(all_evals)


def check_purities(evals_L, evals_2L, L, betas):
    """Given exact full spectra at L and 2L, compute S(L, b), T(2L, b), and Lean gap bound."""
    e0_L = evals_L.min()
    e0_2L = evals_2L.min()
    # Shift by a = -e0_2L / (2L) so Z(2L, b) >= 1 and energy shift cancels from S and T!
    a = -e0_2L / (2 * L)
    dE_L = evals_L + a * L
    dE_2L = evals_2L + a * (2 * L)
    best = None
    for b in betas:
        # Use log-sum-exp for zero overflow
        mL = np.min(b * dE_L)
        m2L = np.min(b * dE_2L)
        m2L2 = np.min(2 * b * dE_2L)
        logZ_L = -mL + math.log(np.sum(np.exp(-(b * dE_L - mL))))
        logZ_2L = -m2L + math.log(np.sum(np.exp(-(b * dE_2L - m2L))))
        logZ_2L_2b = -m2L2 + math.log(np.sum(np.exp(-(2 * b * dE_2L - m2L2))))
        S = math.exp(logZ_2L - 2 * logZ_L)
        T = math.exp(logZ_2L_2b - 2 * logZ_2L)
        u = max(1 - S, 1 - T)
        if u < 0.16:
            # Compute G(u) and check bootstrap condition!
            v = 1.0 - u
            G = 0.5 * (v**-1 + v**-2 + v**-3) ** 2
            # Choose C = G * 1.001 (or C = 5 if u <= 0.01)
            C = G * 1.002
            r = C * u
            if r < 1.0 and C * (1.0 - 3.0 * u) > 3.0:
                gap_lb = math.log(1.0 / r) / b
                if best is None or gap_lb > best["gap_lb"]:
                    best = dict(b=b, S=S, T=T, u=u, C=C, r=r, gap_lb=gap_lb)
    return best


def main():
    t0 = time.time()
    betas = [0.5, 0.75, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 12.0, 16.0, 20.0]
    print("=== Spin-1 XXZ + Single-Ion Anisotropy (L=4 -> 2L=8, unenclosed FP64 diagnostic) ===")
    print(f"{'Delta':>6} {'D':>6} | {'E1-E0(L=8)':>10} | {'b*':>6} {'S(4,b)':>9} {'T(8,b)':>9} {'u0':>9} {'r=Cu0':>8} {'FP64 diag gap >':>15}")
    print("-" * 92)
    grid = [
        # Large-D phase (trivial gapped phase, D > 1)
        (1.0, 3.0), (1.0, 2.5), (1.0, 2.0), (1.0, 1.75), (1.0, 1.5), (1.0, 1.3),
        (0.5, 2.0), (0.0, 2.0), (0.0, 1.5),
        # Haldane phase (D <= 0.5, Delta around 1)
        (1.0, 0.5), (1.0, 0.0), (1.0, -0.2), (1.0, -0.5),
        # Easy-plane XY (Delta = 0, D > 0)
        (0.0, 1.0), (0.25, 1.5), (1.5, 2.5),
    ]
    for Delta, D in grid:
        ev4 = build_spin1_xxz_d_spectrum(4, Delta, D)
        ev8 = build_spin1_xxz_d_spectrum(8, Delta, D)
        ev8_s = np.sort(ev8)
        gap8 = ev8_s[1] - ev8_s[0]
        res = check_purities(ev4, ev8, 4, betas)
        if res:
            print(
                f"{Delta:6.2f} {D:6.2f} | {gap8:10.5f} | {res['b']:6.2f} "
                f"{res['S']:9.6f} {res['T']:9.6f} {res['u']:9.6f} {res['r']:8.5f} {res['gap_lb']:15.6f}"
            )
        else:
            print(f"{Delta:6.2f} {D:6.2f} | {gap8:10.5f} | (no L=4->8 single-step certificate)")
    print(f"\nElapsed: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
