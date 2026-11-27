#!/usr/bin/env python3
"""Check exact overlapping open-chain lower bounds E_shift for Candidate A (Delta=1, D=1/4),
plus exact Chebyshev/Fox-Glynn parameters and orbit counts for n = 4..14, seams I, Rz, Rx, R4."""
import math
import numpy as np
from scipy.linalg import eigvalsh
from scipy.sparse.linalg import eigsh
from scipy.sparse import csr_matrix
from scipy.special import ive  # exponentially scaled modified Bessel I_k(x) * exp(-x)

def open_chain_min_per_bond(m_bonds: int, D: float = 0.25) -> float:
    """Exact minimum eigenvalue of open (m_bonds+1)-site chain with uniform bond weight 1
    and site (S^z)^2 weight D * m_bonds / (m_bonds + 1), divided by m_bonds!
    Notice: summing over all n cyclic shifts on a ring of length n >= m_bonds + 1:
    - Each of the n bonds appears exactly m_bonds times -> total bond weight m_bonds
    - Each of the n sites appears exactly m_bonds + 1 times -> total site weight (m_bonds+1)*(D*m_bonds/(m_bonds+1)) = m_bonds * D
    Therefore H_ring(g) = (1 / m_bonds) * sum_{j=0}^{n-1} U_j H_open(m_bonds) U_j^* for EVERY seam twist g!
    """
    L = m_bonds + 1
    dim = 3 ** L
    # S^z basis: 0 -> +1, 1 -> 0, 2 -> -1
    ar = np.arange(dim, dtype=np.int32)
    pw = 3 ** np.arange(L, dtype=np.int32)
    digits = np.array([(ar // p) % 3 for p in pw], dtype=np.int8)  # (L, dim)
    sz = 1 - digits  # +1, 0, -1
    site_w = D * m_bonds / L
    diag = site_w * (sz * sz).sum(axis=0).astype(np.float64)
    rows = [ar]
    cols = [ar]
    data = [diag]
    for j in range(m_bonds):
        s1 = sz[j]
        s2 = sz[j + 1]
        diag += (s1 * s2).astype(np.float64)
        # S^+_j S^-_{j+1} / 2 + h.c.: raises s1 by 1 (digit - 1), lowers s2 by 1 (digit + 1), coeff 1.0
        for delta in (-1, 1):
            # s1 -> s1 + delta (digit1 -> digit1 - delta), s2 -> s2 - delta (digit2 -> digit2 + delta)
            d1 = digits[j]
            d2 = digits[j + 1]
            mask = np.flatnonzero((d1 - delta >= 0) & (d1 - delta <= 2) & (d2 + delta >= 0) & (d2 + delta <= 2)).astype(np.int32)
            dst = ar[mask] - delta * pw[j] + delta * pw[j + 1]
            rows.append(mask)
            cols.append(dst)
            data.append(np.ones(len(mask), dtype=np.float64))
    data[0] = diag
    H = csr_matrix((np.concatenate(data), (np.concatenate(rows), np.concatenate(cols))), shape=(dim, dim))
    if dim <= 800:
        e0 = float(eigvalsh(H.toarray())[0])
    else:
        e0 = float(eigsh(H, k=1, which="SA", tol=1e-13, return_eigenvectors=False)[0])
    return e0 / m_bonds

def main():
    a = 1.242818
    print("=== Exact overlapping open-chain lower bounds (valid for ALL seams I, Rz, Rx, R4) ===")
    for k in [1, 2, 3, 4, 5, 6, 7, 8]:
        eb = open_chain_min_per_bond(k, D=0.25)
        eshift = math.ceil(-eb * 16) / 16  # clean dyadic rational upper bound on -eb
        x14_155 = 15.5 * 14 * (eshift - a)
        x14_23 = 23.0 * 14 * (eshift - a)
        print(f"  k={k} ({k+1} sites, dim={3**(k+1):5d}): min/bond={eb:.8f} -> E_shift={eshift:.4f} | "
              f"exp(x14/2)@15.5 = {math.exp(x14_155/2):.2e}, @23 = {math.exp(x14_23/2):.2e}")

    # Check Chebyshev degree K for n=14 with E_shift = 1.3125 (21/16) or 1.375 (11/8)
    print("\n=== Chebyshev degree & int64/fp64 error budget at n=14 ===")
    for eshift in [1.5, 1.375, 1.3125]:
        emax = 1.25  # max per bond: S.S <= 1, (Sz)^2 <= 1 -> 1 + 0.25 = 1.25
        width_14 = 14 * (emax + eshift)
        W = width_14 / 2.0  # half-width for C in [-1, 1]
        for b in [15.5, 23.0]:
            mu = 0.5 * b * W
            # Find K where 2 * sum_{k>K} ive(k, mu) < 1e-18
            # Wait: F = exp(-(b/2)*(H + E_shift*n)) = exp(-(b/2)*W*(I - C)) = exp(-mu) * exp(mu * C)
            # where C = I - (H + E_shift*n) / W has spec in [-1, 1]!
            # So exp(-mu) * exp(mu * C) = ive(0, mu) + 2 * sum_{k>=1} ive(k, mu) T_k(C)!
            ks = np.arange(0, 300)
            cs = ive(ks, mu)
            cs[1:] *= 2.0
            tail = np.cumsum(cs[::-1])[::-1]
            K_15 = int(np.searchsorted(-tail, -1e-15))
            K_20 = int(np.searchsorted(-tail, -1e-20))
            ex2 = math.exp(0.5 * b * 14 * (eshift - a))
            # Column error with Q = 2^52 (int64) and d0 = 571231:
            # Chebyshev Clenshaw or 3-term: error grows at most O(K^2 * sqrt(d0)) (or O(K * sqrt(d0)) with exact scaling!)
            print(f"  E_shift={eshift:.4f}, b={b:4.1f}: W={W:.3f}, mu={mu:.2f}, K(1e-15)={K_15}, K(1e-20)={K_20}, "
                  f"exp(x14/2)={ex2:.2e}")

if __name__ == "__main__":
    main()
