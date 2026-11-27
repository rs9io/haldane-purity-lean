#!/usr/bin/env python3
"""
Test the exact integer (S4, R, S2) block-diagonalization + Gershgorin Courant-Fischer
eigenvalue enclosure for H_8^(+1) and H_8^(-1) at all 4 corners of Candidate E.
"""
from __future__ import annotations

from fractions import Fraction
import math
import numpy as np


def even_x_states(L: int) -> list[int]:
    return [s for s in range(1 << L) if s.bit_count() % 2 == 0]


def rot(s: int, k: int, L: int = 8) -> int:
    return ((s << k) | (s >> (L - k))) & ((1 << L) - 1)


def rev(s: int, L: int = 8) -> int:
    r = 0
    for b in range(L):
        if (s >> b) & 1:
            r |= 1 << (L - 1 - b)
    return r


def build_H8_int(g_num: int, h_num: int, twist: int) -> np.ndarray:
    """Exact integer matrix 128 * H_8^(twist) on the 128-dim even-X basis."""
    L = 8
    states = even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=np.int64)
    for i, s in enumerate(states):
        diag = 0
        for k in range(L):
            sk = 1 if ((s >> k) & 1) == 0 else -1
            sk1 = 1 if ((s >> ((k + 1) % L)) & 1) == 0 else -1
            diag += -g_num * (sk * sk1) - h_num * sk
        M[i, i] = diag
        for k in range(L):
            k1 = (k + 1) % L
            s2 = s ^ (1 << k) ^ (1 << k1)
            j = idx[s2]
            M[i, j] += -128 if k < L - 1 else -128 * twist
    return M


def build_exact_int_blocks(twist: int) -> list[np.ndarray]:
    """Construct exact integer orthogonal basis matrices B_b (entries in {-1, 0, +1})
    for the 6 symmetry subspaces of H_8^(twist) (using R, S4, and S2 on S4=+1)."""
    L = 8
    states = even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)

    R = np.zeros((n, n), dtype=np.int64)
    S4 = np.zeros((n, n), dtype=np.int64)
    S2 = np.zeros((n, n), dtype=np.int64)
    for i, s in enumerate(states):
        R[idx[rev(s)], i] = 1
        s4_sign = -1 if (twist == -1 and (s & 0xF).bit_count() % 2 == 1) else 1
        S4[idx[rot(s, 4)], i] = s4_sign
        # Note: rot(s, 2) moves bit k -> bit (k+2)%8, so closing bond (7,0) moves to (1,2).
        # Wait: let's check which two bits need X for rot(s, 2):
        # X_0 X_1 flips ZZ bonds (7,0) and (1,2)!
        # Let's check whether X_0 X_1 acts BEFORE or AFTER rot(s, 2):
        # (X_0 X_1) T^2 |s> = (prod_{k=0,1} sigma_k(rot(s,2))) |rot(s,2)> = (prod_{k=6,7} sigma_k(s)) |rot(s,2)>!
        s2_sign = -1 if (twist == -1 and ((s >> 6) & 0x3).bit_count() % 2 == 1) else 1
        S2[idx[rot(s, 2)], i] = s2_sign

    H_test = build_H8_int(16, 48, twist)
    assert np.array_equal(H_test @ R, R @ H_test), "R must commute with H"
    assert np.array_equal(H_test @ S4, S4 @ H_test), "S4 must commute with H"
    assert np.array_equal(H_test @ S2, S2 @ H_test), "S2 must commute with H"
    assert np.array_equal(S2 @ S2, S4), "S2^2 must equal S4"
    assert np.array_equal(R @ S4, S4 @ R), "R and S4 must commute"

    # Build clean integer {-1, 0, +1} orthogonal basis for each of the 6 blocks:
    # (S4=+1, R=+1, S2=+1), (S4=+1, R=+1, S2=-1),
    # (S4=+1, R=-1, S2=+1), (S4=+1, R=-1, S2=-1),
    # (S4=-1, R=+1), (S4=-1, R=-1).
    I = np.eye(n, dtype=np.int64)
    specs = [
        (I + S4) @ (I + R) @ (I + S2),
        (I + S4) @ (I + R) @ (I - S2),
        (I + S4) @ (I - R) @ (I + S2),
        (I + S4) @ (I - R) @ (I - S2),
        (I - S4) @ (I + R),
        (I - S4) @ (I - R),
    ]
    blocks = []
    for P in specs:
        # Extract linearly independent columns of P (every nonzero column is an orbit vector!)
        cols = []
        seen_support = set()
        for j in range(n):
            col = P[:, j]
            if not np.any(col):
                continue
            g = int(np.gcd.reduce(np.abs(col)))
            col = col // g
            # Canonicalize sign by first nonzero entry > 0
            first_nz = int(np.flatnonzero(col)[0])
            if col[first_nz] < 0:
                col = -col
            key = tuple(col.tolist())
            if key not in seen_support:
                seen_support.add(key)
                cols.append(col)
        B = np.column_stack(cols)
        # Verify B^T B is strictly diagonal!
        G = B.T @ B
        assert np.array_equal(G, np.diag(np.diag(G))), f"Non-orthogonal columns! G={G}"
        blocks.append(B)

    assert sum(B.shape[1] for B in blocks) == n
    # Verify inter-block orthogonality and H-orthogonality
    for a in range(len(blocks)):
        for b in range(a + 1, len(blocks)):
            assert np.all(blocks[a].T @ blocks[b] == 0)
            assert np.all(blocks[a].T @ H_test @ blocks[b] == 0)
    return blocks


def test_gershgorin_all_corners() -> None:
    blocks_by_twist = {+1: build_exact_int_blocks(+1), -1: build_exact_int_blocks(-1)}
    for twist in [+1, -1]:
        dims = [B.shape[1] for B in blocks_by_twist[twist]]
        print(f"twist={twist:+d}: 6 exact {{-1,0,+1}} block dims = {dims}, sum(m^3) = {sum(m**3 for m in dims):,}")

    # Test Gershgorin Courant-Fischer upper bound on Z_+(8, 6) at all 4 corners!
    for bits in [16, 20, 24]:
        scale = 1 << bits
        print(f"\n=== Gershgorin enclosure with {bits}-bit integer eigenvectors (scale=2^{bits}) ===")
        for g_num, h_num in [(15, 47), (15, 48), (16, 47), (16, 48)]:
            Z_exact_tot = 0.0
            Z_ub_tot = 0.0
            max_e1 = 0.0
            max_e2 = 0.0
            for twist in [+1, -1]:
                H128 = build_H8_int(g_num, h_num, twist)
                Hshift128 = H128 + 1536 * np.eye(128, dtype=np.int64)  # 128*(H + 12 I)
                for B in blocks_by_twist[twist]:
                    m = B.shape[1]
                    D = np.diag(B.T @ B)  # integer diagonal norms (1, 2, 4, or 8)
                    Hb = B.T @ Hshift128 @ B  # integer m x m
                    # Orthonormalized float version just to compute approximate eigenvectors C
                    inv_sqrt_D = 1.0 / np.sqrt(D.astype(np.float64))
                    H_norm = (inv_sqrt_D[:, None] * Hb.astype(np.float64)) * inv_sqrt_D[None, :]
                    evals, evecs = np.linalg.eigh(H_norm)
                    Z_exact_tot += float(np.sum(np.exp(-6.0 * (evals / 128.0 - 12.0))))
                    # Generalized eigenvectors C_float = diag(1/sqrt(D)) * evecs
                    C_float = inv_sqrt_D[:, None] * evecs
                    C_int = np.round(C_float * scale).astype(object)  # exact Python big ints!

                    # Exact integer matrix products:
                    # G1 = C^T D C (approximates scale^2 * I)
                    # G2 = C^T Hb C (approximates scale^2 * diag(128*(lambda+12)))
                    D_obj = D.astype(object)
                    Hb_obj = Hb.astype(object)
                    G1 = C_int.T @ (D_obj[:, None] * C_int)
                    G2 = C_int.T @ (Hb_obj @ C_int)

                    s2 = scale * scale
                    # Gershgorin row-sum bound on |G1 - s2 I| / s2 -> eps1
                    e1_int = 0
                    for i in range(m):
                        row_err = abs(G1[i, i] - s2) + sum(abs(G1[i, j]) for j in range(m) if j != i)
                        if row_err > e1_int:
                            e1_int = row_err
                    eps1 = e1_int / s2
                    max_e1 = max(max_e1, eps1)

                    # Row-wise Gershgorin lower bound on G2:
                    # For every row i, mu_lb_i = (G2[i,i] - sum_{j!=i} |G2[i,j]|) / (s2 * (1 + eps1))
                    # (Wait: for Courant-Fischer with row-wise Gershgorin:
                    #  w^T G2 w >= sum_i (G2[i,i] - sum_{j!=i} |G2[i,j]|) w_i^2!
                    #  Sorting those row lower bounds gives an immediate lower bound for EVERY lambda_k!)
                    mu_lbs = []
                    e2_max = 0.0
                    for i in range(m):
                        off = sum(abs(G2[i, j]) for j in range(m) if j != i)
                        e2_max = max(e2_max, off / (s2 * 128.0))
                        lb_shifted = max(0.0, (G2[i, i] - off) / (s2 * 128.0 * (1.0 + eps1)))
                        mu_lbs.append(lb_shifted - 12.0)
                    max_e2 = max(max_e2, e2_max)
                    Z_ub_tot += float(np.sum(np.exp(-6.0 * np.array(mu_lbs))))
            rel = Z_ub_tot / Z_exact_tot - 1.0
            print(f"  corner ({g_num},{h_num}): max_e1={max_e1:.2e}, max_e2={max_e2:.2e}, Z_ub/Z_exact - 1 = {rel:.2e}")


if __name__ == "__main__":
    test_gershgorin_all_corners()
