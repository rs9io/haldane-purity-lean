#!/usr/bin/env python3
"""Rigorous proof that the 7-site open spin-1 chain H_open(6 bonds, Delta=1, D=1/4)
satisfies A = 56 * (H_open + (63/8) * I) > I > 0 (hence H_n(g) + (21/16) * n * I >= (n/336) * I > 0
for EVERY ring n >= 7 and EVERY seam twist g in {I, Rz, Rx, R4} by overlapping-window unitary
equivalence).

Method: decompose A = 56 * (H_open + (63/8) * I) (exact integer symmetric matrix, dim 3^7 = 2187)
into exact S^z blocks M = 0..7 (by M <-> -M spin-negation symmetry, max block dim = 393).
Propose a floating-point Cholesky factor of A - 2*I, round L_i64 = round(S * L_fp) with S = 2^20,
and verify in EXACT overflow-guarded int64 arithmetic that the residual
  R = S^2 * (A - 2 * I) - L_i64 @ L_i64^T
satisfies ||R||_inf < S^2. By Gershgorin's circle theorem, S^2 * I + R is strictly positive definite,
so S^2 * (A - I) = L_i64 @ L_i64^T + (S^2 * I + R) > 0, i.e., A > I > 0.

Uses explicit runtime checks (never bare `assert`), so `python3 -O` cannot bypass any check.
"""
import numpy as np


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def build_open7_blocks() -> None:
    L = 7
    m_bonds = 6
    dim = 3**L
    pw = [3**j for j in range(L)]

    # Exact integer matrix A = 56 * (H_open + (63/8) * I):
    #   bond weight = 1              -> 56
    #   site weight = D * 6/7 = 3/14 -> 56 * (3/14) = 12
    #   shift       = 63/8           -> 56 * (63/8) = 441
    blocks: dict[int, list[tuple[int, list[int]]]] = {}
    for code in range(dim):
        x = code
        sz = []
        for _ in range(L):
            sz.append((x % 3) - 1)
            x //= 3
        M = sum(sz)
        if M >= 0:
            blocks.setdefault(M, []).append((code, sz))

    S = 1 << 20
    S2 = S * S
    checked_dim = 0

    for M in sorted(blocks.keys()):
        items = blocks[M]
        n = len(items)
        checked_dim += n if M == 0 else 2 * n
        idx_map = {code: i for i, (code, _) in enumerate(items)}
        A = np.zeros((n, n), dtype=np.int64)
        for i, (code, sz) in enumerate(items):
            zz = sum(sz[j] * sz[j + 1] for j in range(m_bonds))
            sz2 = sum(s * s for s in sz)
            A[i, i] = 441 + 56 * zz + 12 * sz2
            for j in range(m_bonds):
                if sz[j] < 1 and sz[j + 1] > -1:
                    dst = idx_map[code + pw[j] - pw[j + 1]]
                    A[i, dst] += 56
                if sz[j] > -1 and sz[j + 1] < 1:
                    dst = idx_map[code - pw[j] + pw[j + 1]]
                    A[i, dst] += 56
        require(bool(np.array_equal(A, A.T)), f"Block M={M} not symmetric")

        # Factor A - 2*I so that S^2 * (A - I) = L_i64 @ L_i64^T + (S^2 * I + R) > 0 whenever ||R||_inf < S^2.
        eye_i64 = np.eye(n, dtype=np.int64)
        A_minus_2I = A - 2 * eye_i64
        L_fp = np.linalg.cholesky(A_minus_2I.astype(np.float64))
        L_i64 = np.rint(L_fp * S).astype(np.int64)

        max_L = int(np.max(np.abs(L_i64)))
        require(n * max_L * max_L < (1 << 62), f"int64 matmul overflow risk in M={M}")
        max_A2 = int(np.max(np.abs(A_minus_2I)))
        require(S2 * max_A2 < (1 << 62), f"int64 scaling overflow risk in M={M}")

        LLT = L_i64 @ L_i64.T
        R = S2 * A_minus_2I - LLT
        require(bool(np.array_equal(R, R.T)), f"Residual R not symmetric in M={M}")

        max_R = int(np.max(np.abs(R)))
        require(n * max_R < (1 << 62), f"int64 row-sum overflow risk in M={M}")
        max_row_l1 = int(np.max(np.sum(np.abs(R), axis=1)))
        require(max_row_l1 < S2, f"Gershgorin certification failed in M={M}: ||R||_inf={max_row_l1} >= S^2={S2}")

        print(
            f"  M={M} (dim={n:3d}): max|L|={max_L:9d}, ||R||_inf={max_row_l1:12d} < S^2={S2} "
            f"(ratio={max_row_l1 / S2:.2e}) -> A > I CERTIFIED"
        )

    require(checked_dim == dim, f"Dimension accounting mismatch: {checked_dim} != {dim}")
    print("\nCERTIFIED: 56 * (H_open7 + (63/8) * I) > I > 0 across all M = -7..7 (dim 2187)!")
    print("Therefore H_n(g) + (21/16)*n*I >= (n/336)*I > 0 for EVERY n >= 7 and EVERY seam g in {I, Rz, Rx, R4}!")


if __name__ == "__main__":
    build_open7_blocks()
