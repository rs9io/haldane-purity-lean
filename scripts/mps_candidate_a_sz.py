#!/usr/bin/env python3
"""Uniform 1-site real periodic MPS in the S^z basis {|+1>, |0>, |-1>}.

In the S^z basis, both H(Delta, D) AND the AKLT/Haldane MPS matrices are 100% real
even for a 1-site unit cell! Tests isotropic (1, 0) (exact e0_inf = -1.401484039)
and Candidate A (1, 1/4) at chi = 2, 4, 6, 8, 12, 16.
"""
import time
import numpy as np
from scipy.optimize import minimize

# Spin-1 operators in S^z basis {|+1>, |0>, |-1>}
Sz = np.diag([1.0, 0.0, -1.0])
Sp = np.array([[0.0, np.sqrt(2.0), 0.0],
               [0.0, 0.0, np.sqrt(2.0)],
               [0.0, 0.0, 0.0]])
Sm = Sp.T
Sz2 = np.diag([1.0, 0.0, 1.0])
I3 = np.eye(3)

def h_bond(Delta: float, D: float) -> np.ndarray:
    h = 0.5 * (np.kron(Sp, Sm) + np.kron(Sm, Sp)) + Delta * np.kron(Sz, Sz)
    h += 0.5 * D * (np.kron(Sz2, I3) + np.kron(I3, Sz2))
    return h.reshape(3, 3, 3, 3)  # (s1', s2', s1, s2)

def mps_energy_inf(A: np.ndarray, h4: np.ndarray) -> float:
    """Infinite-chain energy density e_inf = Tr(H_E * vR vL^T) / (vL^T E^2 vR) via leading eigenpair."""
    # E_{(a,a'),(b,b')} = sum_s A[s, a, b] A[s, a', b']
    chi = A.shape[1]
    E = np.einsum("sab,scd->acbd", A, A).reshape(chi * chi, chi * chi)
    # Power iteration / eig for leading right and left eigenvectors
    vals, vecs = np.linalg.eig(E)
    idx = np.argmax(np.real(vals))
    lam = np.real(vals[idx])
    if lam <= 1e-15:
        return 1e6
    # Symmetrize or use finite L=120 exact periodic trace!
    return lam

def mps_periodic_energy(A: np.ndarray, h4: np.ndarray, L: int) -> float:
    """Exact periodic ring energy density <psi|H_L|psi> / (L <psi|psi>) for 1-site real MPS."""
    chi = A.shape[1]
    E = np.einsum("sab,scd->acbd", A, A).reshape(chi * chi, chi * chi)
    AA = np.einsum("sab,tbc->stac", A, A)
    H_AA = np.einsum("pqst,stac->pqac", h4, AA)
    H2 = np.einsum("pqac,pqbd->abcd", H_AA, AA).reshape(chi * chi, chi * chi)
    # Normalize by spectral radius (max |eigval|) so E^L stays O(1) for all L!
    rho = float(np.max(np.abs(np.linalg.eigvals(E))))
    if rho < 1e-30:
        return 1e6
    En = E / rho
    H2n = H2 / (rho * rho)
    E_Lm2 = np.linalg.matrix_power(En, L - 2)
    E_L = E_Lm2 @ En @ En
    den = float(np.trace(E_L))
    if abs(den) < 1e-30:
        return 1e6
    num = float(np.trace(H2n @ E_Lm2))
    return num / den

def mps_periodic_energy_and_grad(x: np.ndarray, chi: int, h4: np.ndarray, L: int):
    """Exact energy and analytic gradient w.r.t. real A[3, chi, chi] on periodic ring L."""
    A = x.reshape(3, chi, chi)
    # Use small complex-step or finite-diff? No, analytic gradient via matrix_power adjoint is fast,
    # or simple finite-L eigendecomposition of E when E is diagonalizable.
    # Actually at chi <= 12 (params <= 432), let's use exact PyTorch/autograd if available, else
    # analytic adjoint of binary exponentiation!
    pass

def optimize_mps(Delta: float, D: float, chi: int, L_opt: int = 64, seed: int = 0, maxiter: int = 400):
    h4 = h_bond(Delta, D)
    rng = np.random.default_rng(seed)
    # Initialize with AKLT block in top-left 2x2 + small perturbation
    A0 = 0.05 * rng.standard_normal((3, chi, chi))
    A0[0, 0, 1] += np.sqrt(2.0)   # S^z = +1
    A0[1, 0, 0] += -1.0           # S^z = 0
    A0[1, 1, 1] += 1.0
    A0[2, 1, 0] += -np.sqrt(2.0)  # S^z = -1

    # Check if torch is installed for fast exact gradients!
    try:
        import torch
        torch.set_num_threads(4)
        h4_t = torch.tensor(h4, dtype=torch.float64)
        def fg(x_np):
            A_t = torch.tensor(x_np.reshape(3, chi, chi), dtype=torch.float64, requires_grad=True)
            E = torch.einsum("sab,scd->acbd", A_t, A_t).reshape(chi * chi, chi * chi)
            AA = torch.einsum("sab,tbc->stac", A_t, A_t)
            H_AA = torch.einsum("pqst,stac->pqac", h4_t, AA)
            H2 = torch.einsum("pqac,pqbd->abcd", H_AA, AA).reshape(chi * chi, chi * chi)
            with torch.no_grad():
                rho = float(torch.max(torch.abs(torch.linalg.eigvals(E))).item())
            s = max(rho, 1e-12)
            En = E / s
            H2n = H2 / (s * s)
            E_Lm2 = torch.linalg.matrix_power(En, L_opt - 2)
            E_L = E_Lm2 @ En @ En
            e = torch.trace(H2n @ E_Lm2) / torch.trace(E_L)
            e.backward()
            return float(e.item()), A_t.grad.detach().numpy().ravel()
        res = minimize(fg, A0.ravel(), method="L-BFGS-B", jac=True, options={"maxiter": maxiter, "ftol": 1e-14, "gtol": 1e-9})
    except ImportError:
        res = minimize(lambda x: mps_periodic_energy(x.reshape(3, chi, chi), h4, L_opt),
                       A0.ravel(), method="L-BFGS-B", options={"maxiter": maxiter})
    A = res.x.reshape(3, chi, chi)
    return A, mps_periodic_energy(A, h4, 72), mps_periodic_energy(A, h4, 120), mps_periodic_energy(A, h4, 240), res.nit

def main():
    t0 = time.time()
    for label, Delta, D in [("Isotropic (1, 0)", 1.0, 0.0), ("Candidate A (1, 1/4)", 1.0, 0.25)]:
        print(f"\n=== {label} ===")
        for chi in [2, 4, 6, 8, 12]:
            A, e72, e120, e240, nit = optimize_mps(Delta, D, chi, L_opt=64, seed=42, maxiter=300)
            print(f"  chi={chi:2d}: e(72)={e72:.10f}, e(120)={e120:.10f}, e(240)={e240:.10f} (nit={nit})", flush=True)
    print(f"\nElapsed: {time.time() - t0:.2f}s")

if __name__ == "__main__":
    main()
