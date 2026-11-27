#!/usr/bin/env python3
"""
Fast periodic uniform MPS variational energy + axial D2 polynomial-filter feasibility test
for Candidate A: Spin-1 XXZ + single-ion anisotropy at (Delta=1, D=1/4).

Uses translation-invariant real MPS A[s] (s in {0(x), 1(y), 2(z)}, D x D real matrices)
with exact periodic transfer-matrix contraction E = sum_s A[s] ⊗ A[s] (D^2 x D^2) to find
the thermodynamic ground-state energy density e0_inf(1, 1/4) and finite-ring energy E_MPS(72).
"""

import math
import time
import numpy as np
from scipy.optimize import minimize


def build_spin1_cartesian_bond(Delta, D_aniso):
    """Return 9x9 real symmetric two-site bond operator h = S_1.S_2(Delta) + (D/2)(Sz_1^2 + Sz_2^2)."""
    # In {|x>, |y>, |z>} (0, 1, 2): (S_a)_{bc} = -i * eps_{abc}
    # (S_a ⊗ S_a)_{(b1,b2),(c1,c2)} = -eps_{a b1 c1} * eps_{a b2 c2}
    eps = np.zeros((3, 3, 3), dtype=np.float64)
    for (a, b, c), s in [((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1),
                         ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1)]:
        eps[a, b, c] = s
    h = np.zeros((3, 3, 3, 3), dtype=np.float64)
    weights = [1.0, 1.0, Delta]
    for a in range(3):
        # h[b1, b2, c1, c2] += -weights[a] * eps[a, b1, c1] * eps[a, b2, c2]
        h += -weights[a] * np.einsum("ij,kl->ikjl", eps[a], eps[a])
    # Single-ion D * (Sz^2) split half-and-half across bonds
    sz2 = np.diag([1.0, 1.0, 0.0])
    eye3 = np.eye(3)
    h += 0.5 * D_aniso * (np.einsum("ij,kl->ikjl", sz2, eye3) + np.einsum("ij,kl->ikjl", eye3, sz2))
    return h


def mps_energy_density_inf(params, chi, h_bond):
    """Exact infinite-chain uniform MPS energy density via dominant eigenvector of transfer matrix."""
    A = params.reshape(3, chi, chi)
    # Transfer matrix E[(a,b),(c,d)] = sum_s A[s,a,c] * A[s,b,d]
    E = np.einsum("sac,sbd->abcd", A, A).reshape(chi * chi, chi * chi)
    # Power iteration / eigen for dominant right & left eigenvectors (fast for small chi)
    evals, R = np.linalg.eig(E)
    idx = np.argmax(np.abs(evals))
    lam = evals[idx].real
    if lam <= 0:
        return 10.0
    r = R[:, idx].real
    evalsL, L = np.linalg.eig(E.T)
    idxL = np.argmax(np.abs(evalsL))
    l = L[:, idxL].real
    norm = float(np.dot(l, r))
    if abs(norm) < 1e-14:
        return 10.0
    # Two-site operator transfer matrix H_E[(a,b),(e,f)] = sum_{s1,s2,t1,t2} h[s1,s2,t1,t2] (A[s1]A[s2])[a,e] (A[t1]A[t2])[b,f]
    AA = np.einsum("sac,tce->stae", A, A)  # (3, 3, chi, chi)
    hAA = np.einsum("stuv,uvae->stae", h_bond, AA)
    HE = np.einsum("stae,stbf->abef", AA, hAA).reshape(chi * chi, chi * chi)
    num = float(l @ (HE @ r))
    return num / (norm * lam * lam)


def mps_energy_periodic_L(A, L, h_bond):
    """Exact periodic ring energy E(L) / L for uniform MPS A (3, chi, chi) of length L."""
    chi = A.shape[1]
    E = np.einsum("sac,sbd->abcd", A, A).reshape(chi * chi, chi * chi)
    AA = np.einsum("sac,tce->stae", A, A)
    hAA = np.einsum("stuv,uvae->stae", h_bond, AA)
    HE = np.einsum("stae,stbf->abef", AA, hAA).reshape(chi * chi, chi * chi)
    E_Lm2 = np.linalg.matrix_power(E, L - 2)
    E_L = E_Lm2 @ E @ E
    norm = np.trace(E_L)
    ebond = np.trace(HE @ E_Lm2)
    return ebond / norm


def main():
    t0 = time.time()
    Delta, D_aniso = 1.0, 0.25
    h_bond = build_spin1_cartesian_bond(Delta, D_aniso)
    # Also sanity-check isotropic (1, 0) where e0_inf = -1.401484039
    for label, (dl, da) in [("Isotropic (1, 0)", (1.0, 0.0)), ("Candidate A (1, 1/4)", (1.0, 0.25))]:
        hb = build_spin1_cartesian_bond(dl, da)
        rng = np.random.default_rng(42)
        print(f"\n=== {label} ===")
        for chi in [4, 6, 8]:
            # Start from AKLT-like / random real matrices
            x0 = rng.normal(scale=0.5, size=3 * chi * chi)
            res = minimize(mps_energy_density_inf, x0, args=(chi, hb), method="BFGS",
                           options={"maxiter": 400, "gtol": 1e-7})
            A = res.x.reshape(3, chi, chi)
            e72 = mps_energy_periodic_L(A, 72, hb)
            e120 = mps_energy_periodic_L(A, 120, hb)
            print(f"  chi={chi}: e0_inf={res.fun:.9f}, e(72)={e72:.9f}, e(120)={e120:.9f} (nit={res.nit})")
    print(f"\nElapsed: {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
