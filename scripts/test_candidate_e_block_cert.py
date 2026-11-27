#!/usr/bin/env python3
"""
Test fast in-Lean-kernel certificate design for Candidate E:
1. Compact D_16 orbit-compressed trial vector (1162 small integers, e.g. 12-16 bit)
   for L=16 untwisted even-X Rayleigh quotient.
2. Exact integer block-diagonalization + Frobenius eigenvalue enclosure
   (Q^T Q = I + E1, Q^T H Q = D + E2) for the two 128-dim L=8 blocks at all 4 corners.
"""
from __future__ import annotations

from fractions import Fraction
import math
import numpy as np


def even_x_states(L: int) -> list[int]:
    return [s for s in range(1 << L) if s.bit_count() % 2 == 0]


def canon_bracelet(s: int, L: int) -> int:
    mask = (1 << L) - 1
    best = s
    cur = s
    for _ in range(L):
        if cur < best:
            best = cur
        rev = 0
        for b in range(L):
            if (cur >> b) & 1:
                rev |= 1 << (L - 1 - b)
        if rev < best:
            best = rev
        cur = ((cur << 1) | (cur >> (L - 1))) & mask
    return best


def test_compact_trial() -> None:
    L = 16
    states = even_x_states(L)
    n = len(states)
    idx = np.full(1 << L, -1, dtype=np.int32)
    for i, s in enumerate(states):
        idx[s] = i

    # Build D_16 orbits
    orbits_map: dict[int, int] = {}
    state_to_orb = np.zeros(n, dtype=np.int32)
    orb_sizes: list[int] = []
    orb_reps: list[int] = []
    for i, s in enumerate(states):
        c = canon_bracelet(s, L)
        if c not in orbits_map:
            orbits_map[c] = len(orb_reps)
            orb_reps.append(c)
            orb_sizes.append(0)
        oid = orbits_map[c]
        state_to_orb[i] = oid
        orb_sizes[oid] += 1

    m = len(orb_reps)
    print(f"L=16 D_16 orbits: {m}, sum(sizes)={sum(orb_sizes)}")

    # Compute orbit-level quadratic forms:
    # For each orbit rep s, diag_x(s) = -sum sigma_k, diag_xx(s) = -sum sigma_k sigma_{k+1},
    # and neighbors(s) = list of 16 neighbor orbit ids.
    orb_x = []
    orb_xx = []
    orb_nbrs = []
    for s in orb_reps:
        sx = 0
        sxx = 0
        nbrs = []
        for k in range(L):
            k1 = (k + 1) % L
            sk = 1 if ((s >> k) & 1) == 0 else -1
            sk1 = 1 if ((s >> k1) & 1) == 0 else -1
            sx -= sk
            sxx -= sk * sk1
            s2 = s ^ (1 << k) ^ (1 << k1)
            nbrs.append(orbits_map[canon_bracelet(s2, L)])
        orb_x.append(sx)
        orb_xx.append(sxx)
        orb_nbrs.append(nbrs)

    # Power iterate directly on the 1162-dim orbit vector!
    v = [1] * m
    for _ in range(300):
        nv = [(192 - orb_xx[o] - 3 * orb_x[o]) * v[o] for o in range(m)]
        for o in range(m):
            for nb in orb_nbrs[o]:
                nv[o] += 8 * v[nb]
        mx = max(abs(x) for x in nv)
        bits = mx.bit_length()
        if bits > 38:
            shift = bits - 38
            nv = [x >> shift for x in nv]
        v = nv

    # Test quantizing v down to small bit widths (8, 10, 12, 16 bits)!
    for target_bits in [8, 10, 12, 16, 38]:
        mx = max(abs(x) for x in v)
        shift = max(0, mx.bit_length() - target_bits)
        vq = [x >> shift for x in v]
        norm2 = sum(orb_sizes[o] * vq[o] * vq[o] for o in range(m))
        fx = sum(orb_sizes[o] * orb_x[o] * vq[o] * vq[o] for o in range(m))
        fxx = sum(orb_sizes[o] * orb_xx[o] * vq[o] * vq[o] for o in range(m))
        fzz = sum(-orb_sizes[o] * vq[o] * sum(vq[nb] for nb in orb_nbrs[o]) for o in range(m))
        e_corner = (128 * fzz + 16 * fxx + 48 * fx) / (128 * norm2)
        nz = sum(1 for x in vq if x != 0)
        print(f"  bits={target_bits:2d}: nonzero={nz:4d}/{m}, norm2_bits={norm2.bit_length():3d}, E(16/128,48/128)={e_corner:.10f}")


def build_H8(g: float, h: float, twist: int) -> np.ndarray:
    L = 8
    states = even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    H = np.zeros((n, n), dtype=np.float64)
    for i, s in enumerate(states):
        diag = 0.0
        for k in range(L):
            sk = 1.0 if ((s >> k) & 1) == 0 else -1.0
            sk1 = 1.0 if ((s >> ((k + 1) % L)) & 1) == 0 else -1.0
            diag += -g * sk * sk1 - h * sk
        H[i, i] = diag
        for k in range(L):
            k1 = (k + 1) % L
            s2 = s ^ (1 << k) ^ (1 << k1)
            j = idx[s2]
            H[i, j] += -1.0 if k < L - 1 else -float(twist)
    return H


def test_block_enclosure() -> None:
    """Test exact integer involutive symmetry decomposition on L=8 for t=+1 and t=-1:
    - For t=+1: T^4 (shift by 4), R (bit reverse), T^2 (shift by 2 on T^4=+1).
    - For t=-1: T'^4 where T' = X_0 T (so T'^4 = X_0 X_1 X_2 X_3 T^4, (T'^4)^2 = prod X_i = +1 on even-X!),
      and R' = X_0? Wait: check reflection symmetry of H_8^{(-)}!
      Under bit reversal i -> 7-i, closing bond (7,0) maps to (0,7) = SAME closing bond!
      So plain bit reversal R commutes with BOTH H_8^{(+)} AND H_8^{(-)}!!"""
    L = 8
    states = even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)

    def rot(s: int, k: int) -> int:
        return ((s << k) | (s >> (L - k))) & ((1 << L) - 1)

    def rev(s: int) -> int:
        r = 0
        for b in range(L):
            if (s >> b) & 1:
                r |= 1 << (L - 1 - b)
        return r

    # Build involutive symmetry matrices for t=+1 and t=-1
    for twist in [+1, -1]:
        H = build_H8(16 / 128, 48 / 128, twist)
        # Reflection R: |s> -> |rev(s)>
        R = np.zeros((n, n))
        for i, s in enumerate(states):
            R[idx[rev(s)], i] = 1.0
        # Half-ring translation:
        # For t=+1: S4 |s> = |rot(s, 4)>
        # For t=-1: S4 |s> = (prod_{k=0}^3 sigma_k) |rot(s, 4)>
        # Check: does S4 commute with H^{(-)}?
        # Under rot by 4, bond (7,0) goes to (3,4), and bond (3,4) goes to (7,0).
        # Conjugating by X_0 X_1 X_2 X_3 flips signs of ZZ bonds crossing {0,1,2,3} vs {4,5,6,7},
        # which are EXACTLY bonds (3,4) and (7,0)!!
        # So (X_0 X_1 X_2 X_3) T^4 flips BOTH (3,4) and (7,0) -> preserves H^{(-)}!
        S4 = np.zeros((n, n))
        for i, s in enumerate(states):
            sign = 1.0
            if twist == -1:
                # prod_{k=0}^3 sigma_k = (-1)^{popcount(s & 0xF)}
                if (s & 0xF).bit_count() % 2 == 1:
                    sign = -1.0
            S4[idx[rot(s, 4)], i] = sign

        # Also check R and S4 commutation:
        # For t=-1, R maps {0,1,2,3} to {4,5,6,7}, and on even-X sector prod_{0..3} = prod_{4..7}!
        # So R and S4 COMMUTE identically for BOTH twists!
        print(f"\ntwist={twist:+d}:")
        print(f"  ||[H, R]||  = {np.linalg.norm(H @ R - R @ H):.2e}")
        print(f"  ||[H, S4]|| = {np.linalg.norm(H @ S4 - S4 @ H):.2e}")
        print(f"  ||[R, S4]|| = {np.linalg.norm(R @ S4 - S4 @ R):.2e}")
        print(f"  ||S4^2 - I||= {np.linalg.norm(S4 @ S4 - np.eye(n)):.2e}")

        # Joint eigenspaces of (R, S4) -> 4 blocks!
        # Even better: check quarter-ring translation S2 on S4=+1!
        # For t=+1: S2 |s> = |rot(s, 2)> commutes with H, S4, and on S4=+1 satisfies S2^2 = +I!
        # Does S2 commute with R? R S2 R = S2^{-1} = S2 on S4=+1!! YES!!
        # What about t=-1? S2 |s> = (prod_{k=0}^1 sigma_k) |rot(s, 2)> -> S2^2 = S4!
        # And on S4=+1, S2^2 = +I, and R S2 R = S2^{-1} = S2!!
        S2 = np.zeros((n, n))
        for i, s in enumerate(states):
            sign = 1.0
            if twist == -1:
                if (s & 0x3).bit_count() % 2 == 1:
                    sign = -1.0
            S2[idx[rot(s, 2)], i] = sign
        print(f"  ||[H, S2]|| = {np.linalg.norm(H @ S2 - S2 @ H):.2e}")
        print(f"  ||S2^2 - S4||={np.linalg.norm(S2 @ S2 - S4):.2e}")

        # Check block sizes for (S4, R) and (S4=+1, S2, R) and (S4=+1, S2=+1, S1, R)!
        # Compute projector dimensions:
        I = np.eye(n)
        for s4_val in [+1, -1]:
            P4 = 0.5 * (I + s4_val * S4)
            for r_val in [+1, -1]:
                PR = 0.5 * (I + r_val * R)
                P = P4 @ PR
                dim = int(round(np.trace(P)))
                if s4_val == 1:
                    # Also split by S2! (S2 commutes with P4 and PR on S4=+1)
                    comm_r = np.linalg.norm(P4 @ (S2 @ R - R @ S2) @ P4)
                    d_plus = int(round(np.trace(P @ (0.5 * (I + S2)))))
                    d_minus = int(round(np.trace(P @ (0.5 * (I - S2)))))
                    print(f"  block (S4={s4_val:+d}, R={r_val:+d}): dim={dim} -> S2 split ({d_plus}, {d_minus}), ||[S2,R]|_{{S4=+1}}||={comm_r:.1e}")
                else:
                    print(f"  block (S4={s4_val:+d}, R={r_val:+d}): dim={dim}")

        # Test Frobenius eigenvalue enclosure precision directly on the 4 (S4, R) blocks
        # using 12-bit quantized eigenvectors Q!
        w_exact = np.linalg.eigvalsh(H)
        Z_exact = float(np.sum(np.exp(-6.0 * w_exact)))
        # Test 16-bit integer Q on full 128x128 vs blocks
        evals, evecs = np.linalg.eigh(H)
        for bits in [10, 12, 16]:
            scale = 1 << bits
            Q = np.round(evecs * scale) / scale
            e1 = np.linalg.norm(np.eye(n) - Q.T @ Q, 'fro')
            # Shift H + 12 I
            Hshift = H + 12.0 * np.eye(n)
            mu = np.round((evals + 12.0) * 10**6) / 10**6
            e2 = np.linalg.norm(Q.T @ Hshift @ Q - np.diag(mu), 'fro')
            # Courant-Fischer lower bound: lambda_k + 12 >= (mu_k - e2) / (1 + e1)
            lb = np.maximum(0.0, (mu - e2) / (1.0 + e1)) - 12.0
            Z_ub = float(np.sum(np.exp(-6.0 * lb)))
            print(f"  full 128x128 bits={bits:2d}: e1={e1:.2e}, e2={e2:.2e}, Z_exact={Z_exact:.6e}, Z_ub={Z_ub:.6e}, rel_err={(Z_ub/Z_exact - 1):.2e}")


if __name__ == "__main__":
    test_compact_trial()
    test_block_enclosure()
