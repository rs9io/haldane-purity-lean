# `haldane-purity-lean`: A Lean 4 Formalization of the Finite-Temperature Purity Bootstrap and the Anisotropic Spin-1 Haldane Gap

**Author:** Dale Richards-Smith ([RS9 Systems](https://rs9.com.au), `lab@rs9.com.au`)  
**Interactive Companion:** [rs9.com.au/haldane-gap](https://rs9.com.au/haldane-gap)  
**Lean / Mathlib Version:** Lean `v4.36.0` + Mathlib `v4.36.0`  
**Verification Standard:** Zero `sorry`, zero `admit`, zero `native_decide`, zero project axiom declarations — all **29** project modules and all **1,781** project theorem constants (`1,468` under `PurityBootstrap.*`) verified fail-closed against strictly standard axioms `[propext, Classical.choice, Quot.sound]`.

---

## Overview

This repository formalizes the **finite-temperature purity bootstrap** (introduced in OpenAI's September 24, 2026 periodic spin-1 Haldane gap preprint and extended to symmetry twists and higher dimensions in Grover `arXiv:2611.07400`) inside Lean 4's pure kernel.

| Model / Role | Lean Declaration | Scope | External Inputs | Proven Spectral Bound |
|---|---|---|---|---|
| **Anisotropic Spin-1 ($D = 1/4$, main result)** | `candidate_a_physical_spin1_charpoly_gap_896` | Concrete $3^L \times 3^L$ `H_spin1`, all finite even $L \ge 896$ | 88 finite `Z_spin1` boxes ($n \le 14$) + 1 trial $\psi$ ($L = 112$) | Simple ground energy; $\gamma_L > \log(20)/368 \approx 0.00814058$ |
| **Anisotropic Spin-1 Interval (main corollary)** | `candidate_a_physical_spin1_interval_charpoly_gap_1792` | All $D \in [0.249999, 0.250001]$, all finite even $L \ge 1792$ | Same 88 $D = 1/4$ boxes + 1 trial (zero new traces) | Simple ground energy; $\gamma_L > \log(20)/736 \approx 0.00407029$ |
| **Isotropic Spin-1 ($D = 0$, Source 1 bridge)** | `source1_physical_spin1_charpoly_gap_2304` | Concrete $3^L \times 3^L$ `H_spin1`, all finite even $L \ge 2304$ | 18 finite `Z_spin1` boxes ($n \le 12$) + 1 trial $\psi$ ($L = 72$) | Simple ground energy; $\gamma_L > \log(20)/784$ |
| **1D Interacting Ising (zero-oracle benchmark)** | `candidate_e_unconditional_full_hamiltonian_theorem` | All $(g, h) \in [\frac{15}{128}, \frac{16}{128}] \times [\frac{47}{128}, \frac{48}{128}]$, finite even $\ell \ge 64$ | **None** (self-contained in Lean 4) | $0 \le E_1 - E_0 \le \frac{1}{20}e^{-\frac{\log 20}{128}\ell}$, $E_i - E_1 > \frac{\log 8}{48}$ ($i \ge 2$) |
| **2D TFIM Torus (zero-oracle 2D benchmark)** | `ising_2d_unconditional_rectangle_charpoly_gap` | All $\|J_x\|, \|J_y\| \le 1/192$, finite even $L \times L$ ($L \ge 2$) | **None** (self-contained, data-free closure) | Simple ground energy; $\gamma_L > \log(2)/5 \approx 0.138629$ |

A tight-radius corollary (`candidate_a_physical_spin1_interval_charpoly_gap_896`) also preserves $L \ge 896$ and $\gamma_L > \log(20)/368$ across $D \in [0.2499999, 0.2500001]$.

---

## 1. Main Physics Result — Anisotropic Spin-1 Haldane Gap at $(\Delta, D) = (1, 1/4)$ & Continuous Interval

**Lean declarations:**
- `PurityBootstrap.Spin1PhysicalGap.candidate_a_physical_spin1_gap_896` & `candidate_a_physical_spin1_charpoly_gap_896`
- `PurityBootstrap.Spin1Interval.candidate_a_physical_spin1_interval_gap_1792` & `candidate_a_physical_spin1_interval_charpoly_gap_1792`
- `PurityBootstrap.Spin1Interval.candidate_a_physical_spin1_interval_gap_896` & `candidate_a_physical_spin1_interval_charpoly_gap_896`

Breaking $SO(3) \to O(2)$ removes the isotropic representation-theory shortcut. Given **only** the 88 concrete physical thermal trace enclosures on `Z_spin1 n _ (1/4) (1242818/10^6) g b` ($n = 4\ldots 14$, $g \in \{I, R_z(\pi), R_x(\pi), R_z(\pi/2)\}$, $b \in \{31/2, 23\}$) and a single nonzero $L = 112$ real variational vector $\psi$ with shifted Rayleigh energy $\langle \psi, (H_{112} + 112 a I) \psi \rangle \le 0$:

- **Machine-checked in Lean 4 (`Spin1Hamiltonian.lean`, `Spin1Compactness.lean`, `Spin1Transfer.lean`, `Spin1PhysicalGap.lean`, `Spin1Interval.lean`, `CandidateA/Data.lean`, `CandidateA/Certificate.lean`):**
  - Concrete $3^n \times 3^n$ physical spin-1 Hamiltonian `H_spin1` in the real Cartesian basis, explicit unitary equivalence `U_cart_to_sz` to the textbook $S^z$ weight basis, finite-$M$ no-collision $O(2)/SO(3)$-equivariant real symmetric transfer matrix `K_mat`, exact cycle contraction $\operatorname{Tr}(K_M^n U_g) = \operatorname{Tr}(T_{\mathrm{slice}}^M)$, first-order Trotter convergence $\operatorname{Tr}(K_M^n U_g) \to Z_{\mathrm{spin1}}$ for all $n \ge 3$ (even & odd), uniform Hilbert–Schmidt $\ell^2$ sequential compactness (`l2_seq_compact_moments`), and exact real $D_4 + R_z(\pi/4)$ sector projections (`spin1_D4_sector_moments`).
  - All 16 degree-14 nonnegative polynomial filters (`decide +kernel`), capped-mass residual bounds, exact $46/31$ temperature-transfer temporal purity lemma ($31/2 \to 23$), four upward-rounded coupled bootstrap rounds $(56, 23) \to (896, 368)$, operator-monotone trace comparison (`matZ_anti_of_le`) and coupling transport (`spin1_S_transport`, `spin1_T_transport`) for $D \in [0.249999, 0.250001]$ ($5$ scalar rounds to $L \ge 1792$), Rayleigh–Ritz criterion, and characteristic-polynomial root multiplicity extraction (`charpoly_roots_eq_eigenvalues`).
- **Externally certified finite inputs (zero floating-point trust in the thermal verifiers):**
  - **7-site overlapping open-chain lower bound (`scripts/certify_open7_shift.py`):** Floating-point Cholesky proposal rounded and certified via exact overflow-guarded `int64` residuals certifying $H_n(g) + \frac{21}{16}nI \succeq \frac{n}{336}I \succ 0$ for every $n \ge 7$ and every seam $g \in \{I, R_z, R_x, R_4\}$.
  - **All 88 raw thermal trace enclosures (`scripts/verify_candidate_a_all88.py`):** Produced by pure 128-bit integer Chebyshev contraction (`scripts/chebyshev_enclose.cpp`, `scripts/chebyshev_enclose_rx.cpp`, `scripts/chebyshev_enclose_cuda.cu`; zero floating point, zero truncated states; bit-for-bit CPU/GPU matched through $n = 11$, 64/88 replayed on CPU, full-matrix ED cross-checks at $n = 4\ldots 6$ and Arb matrix-exponential checks at $n = 4$). The stdlib-only exact rational verifier certifies all 88 intervals inside Lean's centers with worst-case endpoint distance **$1.245 \times 10^{-6} < 10^{-5}$** (87.55% safety margin).
  - **$L = 112$ variational trial witness (`scripts/check_trial.py`, `data/trial32_dyadic14.npz`):** 160-bit Arb verification enclosing the periodic $\chi = 32$ two-site integer MPS Rayleigh quotient per site in $[-1.242820131121, -1.242820131120] < -1.242818$.

---

## 2. Isotropic Spin-1 Haldane Gap ($D = 0$, OpenAI Source 1 Bridge)

**Lean declarations:** `PurityBootstrap.Spin1PhysicalGap.source1_physical_spin1_gap_2304` & `source1_physical_spin1_charpoly_gap_2304`

Applies the same concrete transfer limit and $D_2 \rtimes C_3$ projection bridge (`spin1_D2_sector_moments`) inside Lean 4 to deduce OpenAI's Source 1 isotropic spin-1 Haldane gap ($\gamma_L > \log(20)/784$, simple ground energy, every finite even $L \ge 2304$) directly on `H_spin1 L _ 0 rotI` from only the 18 finite physical thermal trace enclosures ($n = 4\ldots 12$, $b = 49/4$, seams $\{I, R_x\}$) and one $L = 72$ variational Rayleigh vector.

---

## 3. Zero-Oracle Formal-Verification Benchmarks (1D Interacting Ising & 2D TFIM Torus)

To validate our reusable 1D symmetry-twist and 2D Lie–Trotter purity-bootstrap libraries end-to-end with **zero external numerical inputs**, we prove two self-contained theorems in perturbative regimes where existence of a spectral gap is classically known:

- **1D Interacting Transverse-Field Ising Ring (`PurityBootstrap/IsingTrotter.lean`, `CandidateE/*`):** `candidate_e_unconditional_full_hamiltonian_theorem` proves an exponentially narrow parity doublet ($0 \le E_1 - E_0 \le \frac{1}{20}e^{-(\log 20)\ell/128}$) and uniform gap ($E_i - E_1 > \frac{\log 8}{48}$) across the closed two-parameter coupling rectangle $(g, h) \in [\frac{15}{128}, \frac{16}{128}] \times [\frac{47}{128}, \frac{48}{128}]$ for all finite even $\ell \ge 64$, using exact 3-way Lie–Trotter transfer contraction, kernel-checked block-Gershgorin corner enclosures, exact integer $\chi = 2$ MPS trial, and log-convexity.
- **2D Transverse-Field Ising Square Torus (`PurityBootstrap/HigherDim.lean`, `Ising2DTrotter.lean`, `Ising2DSeed.lean`, `Ising2DGap.lean`):** `ising_2d_unconditional_rectangle_charpoly_gap` proves a simple ground energy and uniform gap $\gamma_L > \log(2)/5 \approx 0.138629$ for the concrete $2^{L^2} \times 2^{L^2}$ 2D TFIM torus across $|J_x|, |J_y| \le 1/192$ for all finite even $L \ge 2$, with a completely data-free import closure.

---

## Reproducing All Checks

```bash
# 1. Build all 29 Lean 4 modules (zero errors, zero sorry, zero native_decide)
lake build

# 2. Run the fail-closed audit across all 29 modules, 0 project axioms, and all 1,781 theorems
lake env lean scripts/check_axioms.lean

# 3. Verify Candidate A 7-site open-chain lower bound (exact int64 residual certificate; -O safe)
python3 -O scripts/certify_open7_shift.py

# 4. Pure-integer/rational verification of all 88 Candidate A raw thermal enclosures (-O safe, stdlib only)
python3 -O scripts/verify_candidate_a_all88.py

# 5. (Optional, requires python-flint) Verify the L=112 chi=32 periodic MPS trial Rayleigh quotient in 160-bit Arb
python3 -O scripts/check_trial.py
```

---

## Related Work & Attribution

- **OpenAI (Sep 24, 2026):** *The periodic spin-one Haldane gap* — introduced the finite-temperature purity bootstrap, polynomial-filter/capped-mass moment initialization, and exact integer thermal column evaluation.
- **T. Grover (`arXiv:2611.07400`):** Generalized the purity bootstrap to symmetry-twisted sectors and higher spatial dimensions.
- **S. Lu (`arXiv:2611.11049`):** Independently formalized a finite-Gram/Trotter unconditional Lean 4 theorem for a longitudinal-field Ising chain and reported improved isotropic spin-1 gap bounds ($\gamma_L > 0.0729$ for even $L \ge 36$) plus $D = 4$ single-ion anisotropy.
- **M. F. Lapa & M. Levin (`arXiv:2107.11396`):** Earlier analytic stability proof of ground-state degeneracy and exponentially narrow splitting under weak symmetric perturbations.
- **H. Tasaki (`arXiv:2610.34330`):** Proves uniqueness of the translation-invariant infinite-chain ground state together with a spectral gap and continuity for sufficiently small $|D|$.
