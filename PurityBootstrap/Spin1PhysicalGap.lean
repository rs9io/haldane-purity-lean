import PurityBootstrap.Spin1Transfer
import PurityBootstrap.CandidateA.Certificate
import PurityBootstrap.MomentInit
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Physical Spin-1 Haldane Gap Theorems (Zero Abstract Transfer Hypotheses!)

Eliminates ALL abstract `SpectralSystem1D`, `spatialEig`, `lam155/lam23`, `lamJ/lamN`, and
signed-sector-moment hypotheses from both:
1. **Candidate A (`Δ = 1, D = 1/4`, `a = 1.242818`)** —
   `candidate_a_physical_spin1_gap_896` & `candidate_a_physical_spin1_charpoly_gap_896`:
   takes ONLY the 88 concrete physical thermal trace inequalities on
   `Z_spin1 n _ (1/4) (1242818/10^6) g b` (`n ∈ [4..14]`, `g ∈ {rotI, rotZ, rotX, rotF}`,
   `b ∈ {31/2, 23}`) and a single `L = 112` variational trial vector `ψ` with
   Rayleigh energy `≤ -112 * 1.242818`, and proves that for every even ring `L ≥ 896` the
   concrete `3^L × 3^L` physical Hamiltonian matrix `H_spin1 L _ (1/4) rotI` has a unique
   ground state and uniform spectral gap `γ_L > log(20) / 368 ≈ 0.00814058`.
2. **OpenAI Source 1 (`Δ = 1, D = 0`, `a = 700741/500000`)** —
   `source1_physical_spin1_gap_2304` & `source1_physical_spin1_charpoly_gap_2304`:
   takes ONLY the 18 concrete physical thermal trace inequalities on
   `Z_spin1 n _ 0 (700741/500000) g (49/4)` (`n ∈ [4..12]`, `g ∈ {rotI, rotX}`) and a
   single `L = 72` variational trial vector `ψ` with Rayleigh energy `≤ -72 * (700741/500000)`,
   and proves that for every even ring `L ≥ 2304` the concrete `3^L × 3^L` isotropic spin-1
   Heisenberg ring `H_spin1 L _ 0 rotI` has a unique ground state and uniform spectral gap
   `γ_L > log(20) / 784`.
-/

namespace PurityBootstrap.Spin1PhysicalGap

open scoped BigOperators Matrix
open Matrix PurityBootstrap PurityBootstrap.Spin1Hamiltonian PurityBootstrap.Spin1Transfer
open PurityBootstrap.CandidateA PurityBootstrap.MomentInit

/-! ## 1. Concrete `SpectralSystem1D` Instance for the Physical Spin-1 Ring `H_spin1` -/

private noncomputable def spin1SpatialEig (D a : ℝ) (b : ℝ) : ℕ → ℝ :=
  if hb : 0 < b then Classical.choose (spin1_spatial_eigs D a hb) else fun _ => 0

private lemma spin1SpatialEig_spec (D a : ℝ) {b : ℝ} (hb : 0 < b) :
    Summable (fun i => |spin1SpatialEig D a b i| ^ (4 : ℕ)) ∧
    ∀ n : ℕ, ∀ hn : 4 ≤ n, Z_spin1 n (by omega) D a rotI b = ∑' i, (spin1SpatialEig D a b i) ^ n := by
  have hspec := Classical.choose_spec (spin1_spatial_eigs D a hb)
  have hfun : spin1SpatialEig D a b = Classical.choose (spin1_spatial_eigs D a hb) := by
    simp only [spin1SpatialEig, hb, ↓reduceDIte]
  simpa only [hfun] using hspec

/-- Concrete `SpectralSystem1D` for the physical `3^L × 3^L` spin-1 Hamiltonian `H_spin1 L _ D rotI`
with energy shift `a` (proved unconditionally via the finite-`M` transfer limit `Spin1Transfer`). -/
noncomputable def spin1SpectralSystem (D a : ℝ) : SpectralSystem1D where
  spatialEig := spin1SpatialEig D a
  spatial_summable := fun b hb => (spin1SpatialEig_spec D a hb).1
  d := fun L => Fintype.card (Spin1Cfg L)
  d_pos := fun L _ _ => by simp
  E := fun L k =>
    if hL : 3 ≤ L then
      (H_spin1_isHermitian L hL D rotI).eigenvalues ((Fintype.equivFin (Spin1Cfg L)).symm k)
    else 0
  a := a
  Z_eq := fun L b hLeven hL4 hb => by
    have hL3 : 3 ≤ L := by omega
    have hpow : ∀ x : ℝ, |x| ^ L = x ^ L := fun x => by
      rcases hLeven with ⟨m, rfl⟩
      rw [show m + m = 2 * m by omega, pow_mul, pow_mul, sq_abs]
    simp_rw [hpow]
    rw [← (spin1SpatialEig_spec D a hb).2 L hL4, Z_spin1_eq_sum_exp]
    simp only [hL3, ↓reduceDIte]
    exact (Fintype.sum_equiv (Fintype.equivFin (Spin1Cfg L)).symm _ _ fun _ => rfl).symm

lemma spin1SpectralSystem_Z_eq (D a : ℝ) {L : ℕ} (hLeven : Even L) (hL4 : 4 ≤ L)
    {b : ℝ} (hb : 0 < b) :
    (spin1SpectralSystem D a).Z L b = Z_spin1 L (by omega) D a rotI b := by
  unfold SpectralSystem1D.Z
  change ∑' i, |spin1SpatialEig D a b i| ^ L = Z_spin1 L (by omega) D a rotI b
  have hpow : ∀ x : ℝ, |x| ^ L = x ^ L := fun x => by
    rcases hLeven with ⟨m, rfl⟩
    rw [show m + m = 2 * m by omega, pow_mul, pow_mul, sq_abs]
  simp_rw [hpow]
  exact ((spin1SpatialEig_spec D a hb).2 L hL4).symm

/-- Characteristic-polynomial roots multiset identity for any real symmetric matrix `H`:
`H.charpoly.roots = Finset.univ.val.map hH.eigenvalues` (exact multiplicity). -/
lemma charpoly_roots_eq_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHermitian) :
    H.charpoly.roots = Finset.univ.val.map hH.eigenvalues := by
  let U : Matrix ι ι ℝ := hH.eigenvectorUnitary.1
  have hU_left : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hU_right : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hspec : H = U * Matrix.diagonal hH.eigenvalues * Uᵀ := by
    have h := hH.spectral_theorem
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_assoc] using h
  have hcp : H.charpoly = (Matrix.diagonal hH.eigenvalues).charpoly := by
    conv_lhs => rw [hspec]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_left, Matrix.one_mul]
  rw [hcp, Matrix.charpoly_diagonal]
  have hprod_roots : (∏ i : ι, (Polynomial.X - Polynomial.C (hH.eigenvalues i))).roots =
      Finset.univ.val.map hH.eigenvalues := by
    rw [Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C]
      induction (Finset.univ : Finset ι).val using Multiset.induction_on with
      | empty => simp
      | cons a s _ => simp
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
  exact hprod_roots

/-! ## 2. Candidate A (`Δ = 1, D = 1/4`): Physical Spin-1 Haldane Gap (`L ≥ 896`) -/

/-- Candidate A energy shift `a = 1.242818 = 1242818 / 10^6`. -/
noncomputable def caShift : ℝ := (1242818 : ℝ) / 1000000

/-- **Candidate A Physical Spin-1 Uniform Haldane Gap Theorem (`Δ = 1, D = 1/4`, `L ≥ 896`)**:
ZERO abstract `SpectralSystem1D` or signed-sector-moment hypotheses!
Given ONLY:
1. the 88 concrete physical thermal trace enclosures on `Z_spin1 n _ (1/4) caShift g b`
   (`4 ≤ n ≤ 14`, `g ∈ {rotI, rotZ, rotX, rotF}`, `b ∈ {31/2, 23}`), and
2. a single nonzero `L = 112` variational trial vector `ψ : Spin1Cfg 112 → ℝ` with
   Rayleigh energy `≤ -112 * caShift`,
proves that for **every even ring `L ≥ 896`**, the concrete `3^L × 3^L` physical Hamiltonian
matrix `H_spin1 L _ (1/4) rotI` has a unique ground eigenvalue `k₀ : Spin1Cfg L` and uniform
spectral gap `Real.log 20 / 368 < E_k - E_{k₀}` for all `k ≠ k₀`. -/
theorem candidate_a_physical_spin1_gap_896
    -- 88 concrete physical thermal trace enclosures (`n = 4..14`, `b ∈ {31/2, 23}`, 4 seams)
    (h155_I : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotI (31 / 2) - ((caRawQuad caTable155 n).1 : ℝ)| ≤ (caEps : ℝ))
    (h155_Z : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotZ (31 / 2) - ((caRawQuad caTable155 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (h155_X : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotX (31 / 2) - ((caRawQuad caTable155 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (h155_F : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotF (31 / 2) - ((caRawQuad caTable155 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    (h23_I : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotI 23 - ((caRawQuad caTable23 n).1 : ℝ)| ≤ (caEps : ℝ))
    (h23_Z : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotZ 23 - ((caRawQuad caTable23 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (h23_X : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotX 23 - ((caRawQuad caTable23 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (h23_F : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotF 23 - ((caRawQuad caTable23 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    -- Single L = 112 variational trial vector (`⟨ψ, (H_112 + 112 * caShift * I) ψ⟩ ≤ 0`)
    {n_trial : ℕ} (hn_trial : n_trial = 112)
    (ψ : Spin1Cfg n_trial → ℝ) (hψ_nz : 0 < dotProduct ψ ψ)
    (hψ_le : dotProduct ψ ((H_spin1 n_trial (by omega) (1 / 4) rotI).mulVec ψ) +
      (caShift * (n_trial : ℝ)) * dotProduct ψ ψ ≤ 0)
    {L : ℕ} (hL_even : Even L) (hL_ge : 896 ≤ L) :
    ∃ k₀ : Spin1Cfg L,
      (∀ k : Spin1Cfg L,
        (H_spin1_isHermitian L (by omega) (1 / 4) rotI).eigenvalues k₀ ≤
          (H_spin1_isHermitian L (by omega) (1 / 4) rotI).eigenvalues k) ∧
      (∀ k : Spin1Cfg L, k ≠ k₀ →
        Real.log 20 / 368 <
          (H_spin1_isHermitian L (by omega) (1 / 4) rotI).eigenvalues k -
            (H_spin1_isHermitian L (by omega) (1 / 4) rotI).eigenvalues k₀) := by
  let sys := spin1SpectralSystem (1 / 4) caShift
  rcases spin1_D4_sector_moments (1 / 4) caShift (b := 31 / 2) (by norm_num) with
    ⟨lam155, hsumm155, h155I_eq, h155Z_eq, h155X_eq, h155F_eq⟩
  rcases spin1_D4_sector_moments (1 / 4) caShift (b := 23) (by norm_num) with
    ⟨lam23, hsumm23, h23I_eq, h23Z_eq, h23X_eq, h23F_eq⟩
  rcases exists_eig_le_of_rayleigh (by omega) (1 / 4) caShift rotI ψ hψ_nz hψ_le with ⟨kt, hkt⟩
  have htrial : ∃ k : Fin (sys.d 112), sys.E 112 k + sys.a * (112 : ℝ) ≤ 0 := by
    have h112_cast : (112 : ℝ) = (n_trial : ℝ) := by rw [hn_trial]; norm_num
    rw [h112_cast, ← hn_trial]
    refine ⟨Fintype.equivFin (Spin1Cfg n_trial) kt, ?_⟩
    simpa [sys, spin1SpectralSystem, show 3 ≤ n_trial by omega] using hkt
  have hgap := candidate_a_uniform_gap_896 sys lam155 lam23 hsumm155 hsumm23
    (fun n hn h4 => by rw [spin1SpectralSystem_Z_eq _ _ hn h4 (by norm_num)]; exact h155I_eq n h4)
    (fun n hn h4 => by rw [spin1SpectralSystem_Z_eq _ _ hn h4 (by norm_num)]; exact h23I_eq n h4)
    (fun n h4 h14 => by rw [← h155I_eq n h4]; exact h155_I n h4 h14)
    (fun n h4 h14 => by rw [← h155Z_eq n h4]; exact h155_Z n h4 h14)
    (fun n h4 h14 => by rw [← h155X_eq n h4]; exact h155_X n h4 h14)
    (fun n h4 h14 => by rw [← h155F_eq n h4]; exact h155_F n h4 h14)
    (fun n h4 h14 => by rw [← h23I_eq n h4]; exact h23_I n h4 h14)
    (fun n h4 h14 => by rw [← h23Z_eq n h4]; exact h23_Z n h4 h14)
    (fun n h4 h14 => by rw [← h23X_eq n h4]; exact h23_X n h4 h14)
    (fun n h4 h14 => by rw [← h23F_eq n h4]; exact h23_F n h4 h14)
    htrial hL_even hL_ge
  rcases hgap with ⟨k₀, hmin, hsep⟩
  let e := Fintype.equivFin (Spin1Cfg L)
  refine ⟨e.symm k₀, fun k => ?_, fun k hne => ?_⟩
  · have h := hmin (e k)
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using h
  · have hne' : e k ≠ k₀ := fun heq => hne (by simpa [e] using congrArg e.symm heq)
    have h := hsep (e k) hne'
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using h

/-- **Characteristic-polynomial roots formulation of Candidate A (`Δ = 1, D = 1/4`, `L ≥ 896`)**:
states the unique ground state and uniform spectral gap `> log(20) / 368` directly on the
multiset `(H_spin1 L _ (1/4) rotI).charpoly.roots` with exact multiplicity! -/
theorem candidate_a_physical_spin1_charpoly_gap_896
    (h155_I : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotI (31 / 2) - ((caRawQuad caTable155 n).1 : ℝ)| ≤ (caEps : ℝ))
    (h155_Z : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotZ (31 / 2) - ((caRawQuad caTable155 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (h155_X : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotX (31 / 2) - ((caRawQuad caTable155 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (h155_F : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotF (31 / 2) - ((caRawQuad caTable155 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    (h23_I : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotI 23 - ((caRawQuad caTable23 n).1 : ℝ)| ≤ (caEps : ℝ))
    (h23_Z : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotZ 23 - ((caRawQuad caTable23 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (h23_X : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotX 23 - ((caRawQuad caTable23 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (h23_F : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 14 →
      |Z_spin1 n (by omega) (1 / 4) caShift rotF 23 - ((caRawQuad caTable23 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    {n_trial : ℕ} (hn_trial : n_trial = 112)
    (ψ : Spin1Cfg n_trial → ℝ) (hψ_nz : 0 < dotProduct ψ ψ)
    (hψ_le : dotProduct ψ ((H_spin1 n_trial (by omega) (1 / 4) rotI).mulVec ψ) +
      (caShift * (n_trial : ℝ)) * dotProduct ψ ψ ≤ 0)
    {L : ℕ} (hL_even : Even L) (hL_ge : 896 ≤ L) :
    ∃ (E₀ : ℝ) (rest : Multiset ℝ),
      (H_spin1 L (by omega) (1 / 4) rotI).charpoly.roots = E₀ ::ₘ rest ∧
      rest.card + 1 = 3 ^ L ∧
      ∀ E ∈ rest, Real.log 20 / 368 < E - E₀ := by
  rcases candidate_a_physical_spin1_gap_896 h155_I h155_Z h155_X h155_F
      h23_I h23_Z h23_X h23_F hn_trial ψ hψ_nz hψ_le hL_even hL_ge with ⟨k₀, _, hsep⟩
  let hH := H_spin1_isHermitian L (by omega) (1 / 4) rotI
  refine ⟨hH.eigenvalues k₀, (Finset.univ.erase k₀).val.map hH.eigenvalues, ?_, ?_, ?_⟩
  · rw [charpoly_roots_eq_eigenvalues _ hH]
    have hcons : (Finset.univ : Finset (Spin1Cfg L)).val = k₀ ::ₘ (Finset.univ.erase k₀).val := by
      have := Finset.insert_erase (Finset.mem_univ k₀)
      conv_lhs => rw [← this]
      exact Finset.insert_val_of_notMem (Finset.notMem_erase k₀ _)
    rw [hcons, Multiset.map_cons]
  · simp [Nat.sub_add_cancel (show 1 ≤ 3 ^ L from Nat.one_le_pow L 3 (by omega))]
  · intro E hE
    rw [Multiset.mem_map] at hE
    rcases hE with ⟨k, hk, rfl⟩
    have hne : k ≠ k₀ := (Finset.mem_erase.mp hk).1
    exact hsep k hne

/-! ## 3. OpenAI Source 1 (`Δ = 1, D = 0`): Physical Isotropic Spin-1 Haldane Gap (`L ≥ 2304`) -/

/-- OpenAI Source 1 energy shift `a = 700741 / 500000`. -/
noncomputable def s1Shift : ℝ := (700741 : ℝ) / 500000

/-- **OpenAI Source 1 Physical Spin-1 Uniform Haldane Gap Theorem (`Δ = 1, D = 0`, `L ≥ 2304`)**:
ZERO abstract `SpectralSystem1D` or signed-sector-moment hypotheses!
Given ONLY:
1. the 18 concrete physical thermal trace enclosures on `Z_spin1 n _ 0 s1Shift g (49/4)`
   (`4 ≤ n ≤ 12`, `g ∈ {rotI, rotX}`), and
2. a single nonzero `L = 72` variational trial vector `ψ : Spin1Cfg 72 → ℝ` with
   Rayleigh energy `≤ -72 * s1Shift`,
proves that for **every even ring `L ≥ 2304`**, the concrete `3^L × 3^L` isotropic spin-1
Heisenberg ring `H_spin1 L _ 0 rotI` has a unique ground eigenvalue `k₀ : Spin1Cfg L` and
uniform spectral gap `Real.log 20 / 784 < E_k - E_{k₀}` for all `k ≠ k₀`. -/
theorem source1_physical_spin1_gap_2304
    (hraw_Z : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 12 →
      |Z_spin1 n (by omega) 0 s1Shift rotI (49 / 4) - (s1RawZ n : ℝ)| ≤ (ExactCertificates.s1Eps : ℝ))
    (hraw_P : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 12 →
      |Z_spin1 n (by omega) 0 s1Shift rotX (49 / 4) - (s1RawP n : ℝ)| ≤ (ExactCertificates.s1Eps : ℝ))
    {n_trial : ℕ} (hn_trial : n_trial = 72)
    (ψ : Spin1Cfg n_trial → ℝ) (hψ_nz : 0 < dotProduct ψ ψ)
    (hψ_le : dotProduct ψ ((H_spin1 n_trial (by omega) 0 rotI).mulVec ψ) +
      (s1Shift * (n_trial : ℝ)) * dotProduct ψ ψ ≤ 0)
    {L : ℕ} (hL_even : Even L) (hL_ge : 2304 ≤ L) :
    ∃ k₀ : Spin1Cfg L,
      (∀ k : Spin1Cfg L,
        (H_spin1_isHermitian L (by omega) 0 rotI).eigenvalues k₀ ≤
          (H_spin1_isHermitian L (by omega) 0 rotI).eigenvalues k) ∧
      (∀ k : Spin1Cfg L, k ≠ k₀ →
        Real.log 20 / 784 <
          (H_spin1_isHermitian L (by omega) 0 rotI).eigenvalues k -
            (H_spin1_isHermitian L (by omega) 0 rotI).eigenvalues k₀) := by
  let sys := spin1SpectralSystem 0 s1Shift
  rcases spin1_D2_sector_moments s1Shift (b := 49 / 4) (by norm_num) with
    ⟨lamJ, lamN, hsummJ, hsummN, hI_eq, hX_eq⟩
  rcases exists_eig_le_of_rayleigh (by omega) 0 s1Shift rotI ψ hψ_nz hψ_le with ⟨kt, hkt⟩
  have hZ72_ge1 : 1 ≤ sys.Z 72 (49 / 2 : ℝ) := by
    rw [← hn_trial, spin1SpectralSystem_Z_eq 0 s1Shift ⟨36, by omega⟩ (by omega) (by norm_num),
      Z_spin1_eq_sum_exp]
    have h1 : (1 : ℝ) ≤ Real.exp (-(49 / 2 : ℝ) *
        ((H_spin1_isHermitian n_trial (by omega) 0 rotI).eigenvalues kt + s1Shift * (n_trial : ℝ))) :=
      Real.one_le_exp (by nlinarith)
    exact h1.trans (Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ kt))
  have hgap := source1_gap_from_raw_thermal_table sys lamJ lamN hsummJ hsummN
    (fun n hn h4 => by rw [spin1SpectralSystem_Z_eq _ _ hn h4 (by norm_num)]; exact hI_eq n h4)
    (fun n h4 h12 => by rw [← hI_eq n h4]; exact hraw_Z n h4 h12)
    (fun n h4 h12 => by rw [← hX_eq n h4]; exact hraw_P n h4 h12)
    hZ72_ge1 hL_even hL_ge
  rcases hgap with ⟨k₀, hmin, hsep⟩
  let e := Fintype.equivFin (Spin1Cfg L)
  refine ⟨e.symm k₀, fun k => ?_, fun k hne => ?_⟩
  · have h := hmin (e k)
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using h
  · have hne' : e k ≠ k₀ := fun heq => hne (by simpa [e] using congrArg e.symm heq)
    have h := hsep (e k) hne'
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using h

/-- **Characteristic-polynomial roots formulation of OpenAI Source 1 (`Δ = 1, D = 0`, `L ≥ 2304`)**. -/
theorem source1_physical_spin1_charpoly_gap_2304
    (hraw_Z : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 12 →
      |Z_spin1 n (by omega) 0 s1Shift rotI (49 / 4) - (s1RawZ n : ℝ)| ≤ (ExactCertificates.s1Eps : ℝ))
    (hraw_P : ∀ n : ℕ, ∀ hn : 4 ≤ n, n ≤ 12 →
      |Z_spin1 n (by omega) 0 s1Shift rotX (49 / 4) - (s1RawP n : ℝ)| ≤ (ExactCertificates.s1Eps : ℝ))
    {n_trial : ℕ} (hn_trial : n_trial = 72)
    (ψ : Spin1Cfg n_trial → ℝ) (hψ_nz : 0 < dotProduct ψ ψ)
    (hψ_le : dotProduct ψ ((H_spin1 n_trial (by omega) 0 rotI).mulVec ψ) +
      (s1Shift * (n_trial : ℝ)) * dotProduct ψ ψ ≤ 0)
    {L : ℕ} (hL_even : Even L) (hL_ge : 2304 ≤ L) :
    ∃ (E₀ : ℝ) (rest : Multiset ℝ),
      (H_spin1 L (by omega) 0 rotI).charpoly.roots = E₀ ::ₘ rest ∧
      rest.card + 1 = 3 ^ L ∧
      ∀ E ∈ rest, Real.log 20 / 784 < E - E₀ := by
  rcases source1_physical_spin1_gap_2304 hraw_Z hraw_P hn_trial ψ hψ_nz hψ_le hL_even hL_ge with ⟨k₀, _, hsep⟩
  let hH := H_spin1_isHermitian L (by omega) 0 rotI
  refine ⟨hH.eigenvalues k₀, (Finset.univ.erase k₀).val.map hH.eigenvalues, ?_, ?_, ?_⟩
  · rw [charpoly_roots_eq_eigenvalues _ hH]
    have hcons : (Finset.univ : Finset (Spin1Cfg L)).val = k₀ ::ₘ (Finset.univ.erase k₀).val := by
      have := Finset.insert_erase (Finset.mem_univ k₀)
      conv_lhs => rw [← this]
      exact Finset.insert_val_of_notMem (Finset.notMem_erase k₀ _)
    rw [hcons, Multiset.map_cons]
  · simp [Nat.sub_add_cancel (show 1 ≤ 3 ^ L from Nat.one_le_pow L 3 (by omega))]
  · intro E hE
    rw [Multiset.mem_map] at hE
    rcases hE with ⟨k, hk, rfl⟩
    have hne : k ≠ k₀ := (Finset.mem_erase.mp hk).1
    exact hsep k hne

end PurityBootstrap.Spin1PhysicalGap
