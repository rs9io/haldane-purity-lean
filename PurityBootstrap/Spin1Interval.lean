import PurityBootstrap.Spin1PhysicalGap
import Mathlib.Tactic

/-!
# Continuous Single-Ion Anisotropy Interval Theorems for the Physical Spin-1 Haldane Chain

Eliminates point-isolation at `D = 1/4` by transporting the physical seed purities `S(56, 23)` and
`T(112, 23)` across an entire continuous interval of anisotropy couplings `D` around `D_* = 1/4`,
using ONLY the exact same 88 archived Candidate A trace enclosures at `D_* = 1/4` and the single
`L = 112` variational trial witness at `D_* = 1/4` (zero new thermal traces or GPU runs!).

### Proof Mechanism
1. **Operator-monotone thermal trace bound (`matZ_anti_of_le`)**: for any real symmetric matrices
   `A ⪯ B` (`∀ u, ⟨u, A u⟩ ≤ ⟨u, B u⟩`) and `b ≥ 0`, `matZ B hB b ≤ matZ A hA b` (proved in 15 lines
   from eigenbasis Jensen `exp_quad_le_sum_sq_exp` and basis completeness `sum_orthonormal_overlap_sq`).
2. **One-sided `Z_spin1` coupling transport**: since `H_spin1(D) - H_spin1(D_*) = (D - D_*) V_n`
   with `V_n = ∑_j (S_j^z)^2` diagonal and `0 ≤ V_n ≤ n I`:
   - for `D_* ≤ D ≤ D_* + h`: `exp(-b n h) Z(n, D_*, b) ≤ Z(n, D, b) ≤ Z(n, D_*, b)`;
   - for `D_* - h ≤ D ≤ D_*`: `Z(n, D_*, b) ≤ Z(n, D, b) ≤ exp(+b n h) Z(n, D_*, b)`.
3. **Uniform purity transport (`spin1_S_transport`, `spin1_T_transport`)**: in BOTH signs of `D - D_*`,
   uniform per-site energy shifts cancel and
     `S(n, b; D) ≥ exp(-2 n b h) S(n, b; D_*)`,
     `T(m, b; D) ≥ exp(-2 m b h) T(m, b; D_*)`.
4. **Restarting the `D`-parametric bootstrap on `spin1SpectralSystem D caShift`**:
   - **`D ∈ [249999/10^6, 250001/10^6]` (`|D - 1/4| ≤ 10⁻⁶`)**: 5 exact upward-rounded scalar
     doubling rounds `(56, 23) → (1792, 736)` reach `(0.0016762, 0.0001751) < 1/100`, proving a
     unique ground state (simple root of `charpoly`) and uniform spectral gap
     `γ_L > log(20) / 736 ≈ 0.00407029` for **every even ring `L ≥ 1792`** and **every `D` in the
     continuous interval `[0.249999, 0.250001]`**.
   - **`D ∈ [2499999/10^7, 2500001/10^7]` (`|D - 1/4| ≤ 10⁻⁷`)**: 4 exact scalar rounds preserve
     the original Candidate A threshold **`L ≥ 896`** and gap **`γ_L > log(20) / 368 ≈ 0.00814058`**.
-/

namespace PurityBootstrap.Spin1Interval

open scoped BigOperators Matrix
open Matrix PurityBootstrap PurityBootstrap.MatrixTools PurityBootstrap.LieTrotter
open PurityBootstrap.ExactCertificates PurityBootstrap.CandidateA
open PurityBootstrap.Spin1Hamiltonian PurityBootstrap.Spin1Transfer PurityBootstrap.Spin1PhysicalGap

/-! ## 1. Operator-Monotone Antitone Bound for `matZ` and Coupling Transport for `Z_spin1` -/

/-- **Operator-monotone antitone bound for `matZ`**:
if real symmetric matrices `A, B` satisfy `u ⬝ᵥ A *ᵥ u ≤ u ⬝ᵥ B *ᵥ u` for all `u` and `0 ≤ b`,
then `matZ B hB b ≤ matZ A hA b`. -/
theorem matZ_anti_of_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b)
    (hle : ∀ u : n → ℝ, dotProduct u (A.mulVec u) ≤ dotProduct u (B.mulVec u)) :
    matZ B hB b ≤ matZ A hA b := by
  let u : n → (n → ℝ) := fun k => (hB.eigenvectorBasis k).ofLp
  have hu_unit : ∀ k, dotProduct (u k) (u k) = 1 := fun k => by
    have h := hB.eigenvectorBasis.orthonormal.1 k
    have hsq : ‖hB.eigenvectorBasis k‖ ^ 2 = 1 := by rw [h, one_pow]
    rw [EuclideanSpace.norm_sq_eq] at hsq
    simpa [u, dotProduct, Real.norm_eq_abs, sq_abs, sq] using hsq
  unfold matZ
  calc ∑ k : n, Real.exp (-b * hB.eigenvalues k)
      ≤ ∑ k : n, Real.exp (-b * dotProduct (u k) (A.mulVec (u k))) := by
          refine Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr ?_
          have heig : dotProduct (u k) (B.mulVec (u k)) = hB.eigenvalues k := by
            rw [hB.mulVec_eigenvectorBasis k, dotProduct_smul, smul_eq_mul, hu_unit k, mul_one]
          have hAB := hle (u k)
          rw [heig] at hAB
          nlinarith
    _ ≤ ∑ k : n, ∑ j : n, (dotProduct (hA.eigenvectorBasis j).ofLp (u k)) ^ 2 *
          Real.exp (-b * hA.eigenvalues j) :=
          Finset.sum_le_sum fun k _ => exp_quad_le_sum_sq_exp A hA b (u k) (hu_unit k)
    _ = ∑ j : n, Real.exp (-b * hA.eigenvalues j) :=
          sum_orthonormal_overlap_sq hA.eigenvectorBasis hB.eigenvectorBasis
            (fun j => Real.exp (-b * hA.eigenvalues j))

/-- `Z_spin1` equals `matZ` of the energy-shifted concrete Hamiltonian `H_spin1_shifted`. -/
lemma Z_spin1_eq_matZ_shifted (n : ℕ) (hn : 3 ≤ n) (D a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ) :
    Z_spin1 n hn D a g b =
      matZ (H_spin1_shifted n hn D a g) (H_spin1_shifted_isHermitian n hn D a g) b := by
  unfold Z_spin1
  exact trace_exp_eq_matZ (H_spin1_shifted n hn D a g) (H_spin1_shifted_isHermitian n hn D a g) b

/-- Shifting the per-site energy offset `a ↦ a + c` multiplies `Z_spin1` by `exp(-b * c * n)`. -/
lemma Z_spin1_shift_add (n : ℕ) (hn : 3 ≤ n) (D a c : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ) :
    Z_spin1 n hn D (a + c) g b = Real.exp (-b * (c * (n : ℝ))) * Z_spin1 n hn D a g b := by
  rw [Z_spin1_eq_sum_exp, Z_spin1_eq_sum_exp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private lemma V_mat_diag_eq (D a : ℝ) (i : Fin 3) :
    V_mat D a i i = D * SzSq_mat i i + a := by
  fin_cases i <;> simp [V_mat, SzSq_mat]

private lemma SzSq_mat_diag_bounds (i : Fin 3) :
    0 ≤ SzSq_mat i i ∧ SzSq_mat i i ≤ 1 := by
  fin_cases i <;> simp [SzSq_mat]

private lemma H_spin1_shifted_quad_diff (n : ℕ) (hn : 3 ≤ n) (D₁ D₂ a₁ a₂ : ℝ)
    (g : Matrix (Fin 3) (Fin 3) ℝ) (u : Spin1Cfg n → ℝ) :
    dotProduct u ((H_spin1_shifted n hn D₂ a₂ g).mulVec u) -
      dotProduct u ((H_spin1_shifted n hn D₁ a₁ g).mulVec u) =
    ∑ σ : Spin1Cfg n,
      ((D₂ - D₁) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + (a₂ - a₁) * (n : ℝ)) * (u σ) ^ 2 := by
  rw [H_spin1_shifted_eq_bonds_add_onsite, H_spin1_shifted_eq_bonds_add_onsite,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    H_onsite_eq_diagonal, H_onsite_eq_diagonal]
  have hsub :
      (dotProduct u ((H_bonds n hn g).mulVec u) +
        dotProduct u ((Matrix.diagonal fun σ => ∑ j : Fin n, V_mat D₂ a₂ (σ j) (σ j)).mulVec u)) -
      (dotProduct u ((H_bonds n hn g).mulVec u) +
        dotProduct u ((Matrix.diagonal fun σ => ∑ j : Fin n, V_mat D₁ a₁ (σ j) (σ j)).mulVec u)) =
      dotProduct u ((Matrix.diagonal fun σ => ∑ j : Fin n, V_mat D₂ a₂ (σ j) (σ j)).mulVec u) -
      dotProduct u ((Matrix.diagonal fun σ => ∑ j : Fin n, V_mat D₁ a₁ (σ j) (σ j)).mulVec u) := by
    ring
  rw [hsub]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hsum : (∑ j : Fin n, V_mat D₂ a₂ (σ j) (σ j)) - (∑ j : Fin n, V_mat D₁ a₁ (σ j) (σ j)) =
      (D₂ - D₁) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + (a₂ - a₁) * (n : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    have hpt : ∀ j : Fin n, V_mat D₂ a₂ (σ j) (σ j) - V_mat D₁ a₁ (σ j) (σ j) =
        (D₂ - D₁) * SzSq_mat (σ j) (σ j) + (a₂ - a₁) := fun j => by
      rw [V_mat_diag_eq, V_mat_diag_eq]; ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  calc u σ * ((∑ j : Fin n, V_mat D₂ a₂ (σ j) (σ j)) * u σ) -
        u σ * ((∑ j : Fin n, V_mat D₁ a₁ (σ j) (σ j)) * u σ)
      = ((∑ j : Fin n, V_mat D₂ a₂ (σ j) (σ j)) - (∑ j : Fin n, V_mat D₁ a₁ (σ j) (σ j))) *
          (u σ) ^ 2 := by ring
    _ = ((D₂ - D₁) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + (a₂ - a₁) * (n : ℝ)) * (u σ) ^ 2 := by
          rw [hsum]

/-- One-sided thermal partition-function bounds for `D₀ ≤ D ≤ D₀ + h`:
`exp(-b h n) * Z_spin1(D₀) ≤ Z_spin1(D) ≤ Z_spin1(D₀)`. -/
lemma Z_spin1_D_bounds_of_ge {n : ℕ} (hn : 3 ≤ n) {D₀ D h : ℝ} (hlo : D₀ ≤ D) (hhi : D - D₀ ≤ h)
    (a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (-b * (h * (n : ℝ))) * Z_spin1 n hn D₀ a g b ≤ Z_spin1 n hn D a g b ∧
    Z_spin1 n hn D a g b ≤ Z_spin1 n hn D₀ a g b := by
  have hV_bounds : ∀ σ : Spin1Cfg n,
      0 ≤ ∑ j : Fin n, SzSq_mat (σ j) (σ j) ∧ ∑ j : Fin n, SzSq_mat (σ j) (σ j) ≤ (n : ℝ) := fun σ => by
    constructor
    · exact Finset.sum_nonneg fun j _ => (SzSq_mat_diag_bounds (σ j)).1
    · calc ∑ j : Fin n, SzSq_mat (σ j) (σ j)
          ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => (SzSq_mat_diag_bounds (σ j)).2
        _ = (n : ℝ) := by simp
  have h1 : ∀ u : Spin1Cfg n → ℝ,
      dotProduct u ((H_spin1_shifted n hn D₀ a g).mulVec u) ≤
        dotProduct u ((H_spin1_shifted n hn D a g).mulVec u) := fun u => by
    have hdiff := H_spin1_shifted_quad_diff n hn D₀ D a a g u
    have hnn : 0 ≤ ∑ σ : Spin1Cfg n,
        ((D - D₀) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + (a - a) * (n : ℝ)) * (u σ) ^ 2 := by
      refine Finset.sum_nonneg fun σ _ => mul_nonneg ?_ (sq_nonneg _)
      have h0 := (hV_bounds σ).1
      nlinarith
    linarith
  have h2 : ∀ u : Spin1Cfg n → ℝ,
      dotProduct u ((H_spin1_shifted n hn D a g).mulVec u) ≤
        dotProduct u ((H_spin1_shifted n hn D₀ (a + h) g).mulVec u) := fun u => by
    have hdiff := H_spin1_shifted_quad_diff n hn D D₀ a (a + h) g u
    have hnn : 0 ≤ ∑ σ : Spin1Cfg n,
        ((D₀ - D) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + ((a + h) - a) * (n : ℝ)) * (u σ) ^ 2 := by
      refine Finset.sum_nonneg fun σ _ => mul_nonneg ?_ (sq_nonneg _)
      have hV := hV_bounds σ
      nlinarith
    linarith
  constructor
  · rw [← Z_spin1_shift_add n hn D₀ a h g b, Z_spin1_eq_matZ_shifted, Z_spin1_eq_matZ_shifted]
    exact matZ_anti_of_le _ _ (H_spin1_shifted_isHermitian n hn D a g)
      (H_spin1_shifted_isHermitian n hn D₀ (a + h) g) hb h2
  · rw [Z_spin1_eq_matZ_shifted, Z_spin1_eq_matZ_shifted]
    exact matZ_anti_of_le _ _ (H_spin1_shifted_isHermitian n hn D₀ a g)
      (H_spin1_shifted_isHermitian n hn D a g) hb h1

/-- One-sided thermal partition-function bounds for `D₀ - h ≤ D ≤ D₀`:
`Z_spin1(D₀) ≤ Z_spin1(D) ≤ exp(+b h n) * Z_spin1(D₀)`. -/
lemma Z_spin1_D_bounds_of_le {n : ℕ} (hn : 3 ≤ n) {D₀ D h : ℝ} (hlo : D ≤ D₀) (hhi : D₀ - D ≤ h)
    (a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) {b : ℝ} (hb : 0 ≤ b) :
    Z_spin1 n hn D₀ a g b ≤ Z_spin1 n hn D a g b ∧
    Z_spin1 n hn D a g b ≤ Real.exp (b * (h * (n : ℝ))) * Z_spin1 n hn D₀ a g b := by
  have hV_bounds : ∀ σ : Spin1Cfg n,
      0 ≤ ∑ j : Fin n, SzSq_mat (σ j) (σ j) ∧ ∑ j : Fin n, SzSq_mat (σ j) (σ j) ≤ (n : ℝ) := fun σ => by
    constructor
    · exact Finset.sum_nonneg fun j _ => (SzSq_mat_diag_bounds (σ j)).1
    · calc ∑ j : Fin n, SzSq_mat (σ j) (σ j)
          ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => (SzSq_mat_diag_bounds (σ j)).2
        _ = (n : ℝ) := by simp
  have h1 : ∀ u : Spin1Cfg n → ℝ,
      dotProduct u ((H_spin1_shifted n hn D a g).mulVec u) ≤
        dotProduct u ((H_spin1_shifted n hn D₀ a g).mulVec u) := fun u => by
    have hdiff := H_spin1_shifted_quad_diff n hn D D₀ a a g u
    have hnn : 0 ≤ ∑ σ : Spin1Cfg n,
        ((D₀ - D) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + (a - a) * (n : ℝ)) * (u σ) ^ 2 := by
      refine Finset.sum_nonneg fun σ _ => mul_nonneg ?_ (sq_nonneg _)
      have h0 := (hV_bounds σ).1
      nlinarith
    linarith
  have h2 : ∀ u : Spin1Cfg n → ℝ,
      dotProduct u ((H_spin1_shifted n hn D₀ (a - h) g).mulVec u) ≤
        dotProduct u ((H_spin1_shifted n hn D a g).mulVec u) := fun u => by
    have hdiff := H_spin1_shifted_quad_diff n hn D₀ D (a - h) a g u
    have hnn : 0 ≤ ∑ σ : Spin1Cfg n,
        ((D - D₀) * (∑ j : Fin n, SzSq_mat (σ j) (σ j)) + (a - (a - h)) * (n : ℝ)) * (u σ) ^ 2 := by
      refine Finset.sum_nonneg fun σ _ => mul_nonneg ?_ (sq_nonneg _)
      have hV := hV_bounds σ
      nlinarith
    linarith
  constructor
  · rw [Z_spin1_eq_matZ_shifted, Z_spin1_eq_matZ_shifted]
    exact matZ_anti_of_le _ _ (H_spin1_shifted_isHermitian n hn D a g)
      (H_spin1_shifted_isHermitian n hn D₀ a g) hb h1
  · have hshift : Z_spin1 n hn D₀ (a - h) g b = Real.exp (b * (h * (n : ℝ))) * Z_spin1 n hn D₀ a g b := by
      have hsub : a - h = a + (-h) := by ring
      rw [hsub, Z_spin1_shift_add]
      congr 2; ring
    rw [← hshift, Z_spin1_eq_matZ_shifted, Z_spin1_eq_matZ_shifted]
    exact matZ_anti_of_le _ _ (H_spin1_shifted_isHermitian n hn D₀ (a - h) g)
      (H_spin1_shifted_isHermitian n hn D a g) hb h2

/-- **Spatial purity transport across coupling `D` (`|D - D₀| ≤ h`)**:
`Real.exp (-2 * n * b * h) * S(n, b; D₀) ≤ S(n, b; D)`. -/
theorem spin1_S_transport {D₀ D h a b : ℝ} (hD : |D - D₀| ≤ h) (hb : 0 < b)
    {n : ℕ} (hn_even : Even n) (hn4 : 4 ≤ n) :
    Real.exp (-2 * (n : ℝ) * b * h) * (spin1SpectralSystem D₀ a).toPuritySystem1D.S n b ≤
      (spin1SpectralSystem D a).toPuritySystem1D.S n b := by
  have hn2_even : Even (2 * n) := ⟨n, by omega⟩
  have hS_D : (spin1SpectralSystem D a).toPuritySystem1D.S n b =
      Z_spin1 (2 * n) (by omega) D a rotI b / (Z_spin1 n (by omega) D a rotI b) ^ 2 := by
    change (spin1SpectralSystem D a).Z (2 * n) b / ((spin1SpectralSystem D a).Z n b) ^ 2 = _
    rw [spin1SpectralSystem_Z_eq D a hn2_even (by omega) hb,
      spin1SpectralSystem_Z_eq D a hn_even hn4 hb]
  have hS_D0 : (spin1SpectralSystem D₀ a).toPuritySystem1D.S n b =
      Z_spin1 (2 * n) (by omega) D₀ a rotI b / (Z_spin1 n (by omega) D₀ a rotI b) ^ 2 := by
    change (spin1SpectralSystem D₀ a).Z (2 * n) b / ((spin1SpectralSystem D₀ a).Z n b) ^ 2 = _
    rw [spin1SpectralSystem_Z_eq D₀ a hn2_even (by omega) hb,
      spin1SpectralSystem_Z_eq D₀ a hn_even hn4 hb]
  rw [hS_D, hS_D0]
  have hZ_pos : ∀ (m : ℕ) (hm : 3 ≤ m) (D' : ℝ), 0 < Z_spin1 m hm D' a rotI b := fun m hm D' => by
    rw [Z_spin1_eq_matZ_shifted]; exact matZ_pos _ _ _
  have hZ0_n : 0 < Z_spin1 n (by omega) D₀ a rotI b := hZ_pos n (by omega) D₀
  have hZD_n : 0 < Z_spin1 n (by omega) D a rotI b := hZ_pos n (by omega) D
  have hZ0_2n : 0 < Z_spin1 (2 * n) (by omega) D₀ a rotI b := hZ_pos (2 * n) (by omega) D₀
  rcases le_total D₀ D with hge | hle
  · have hhi : D - D₀ ≤ h := (abs_le.mp hD).2
    have hnum := (Z_spin1_D_bounds_of_ge (n := 2 * n) (by omega) hge hhi a rotI hb.le).1
    have hden := (Z_spin1_D_bounds_of_ge (n := n) (by omega) hge hhi a rotI hb.le).2
    have hexp_eq : -b * (h * ((2 * n : ℕ) : ℝ)) = -2 * (n : ℝ) * b * h := by push_cast; ring
    rw [hexp_eq] at hnum
    have hden2 : (Z_spin1 n (by omega) D a rotI b) ^ 2 ≤
        (Z_spin1 n (by omega) D₀ a rotI b) ^ 2 :=
      pow_le_pow_left₀ hZD_n.le hden 2
    calc Real.exp (-2 * (n : ℝ) * b * h) *
          (Z_spin1 (2 * n) (by omega) D₀ a rotI b / (Z_spin1 n (by omega) D₀ a rotI b) ^ 2)
        = (Real.exp (-2 * (n : ℝ) * b * h) * Z_spin1 (2 * n) (by omega) D₀ a rotI b) /
            (Z_spin1 n (by omega) D₀ a rotI b) ^ 2 := by ring
      _ ≤ Z_spin1 (2 * n) (by omega) D a rotI b / (Z_spin1 n (by omega) D₀ a rotI b) ^ 2 :=
            div_le_div_of_nonneg_right hnum (pow_nonneg hZ0_n.le 2)
      _ ≤ Z_spin1 (2 * n) (by omega) D a rotI b / (Z_spin1 n (by omega) D a rotI b) ^ 2 :=
            div_le_div_of_nonneg_left (hZ_pos (2 * n) (by omega) D).le (pow_pos hZD_n 2) hden2
  · have hhi : D₀ - D ≤ h := by linarith [(abs_le.mp hD).1]
    have hnum := (Z_spin1_D_bounds_of_le (n := 2 * n) (by omega) hle hhi a rotI hb.le).1
    have hden := (Z_spin1_D_bounds_of_le (n := n) (by omega) hle hhi a rotI hb.le).2
    have hden2 : (Z_spin1 n (by omega) D a rotI b) ^ 2 ≤
        Real.exp (2 * (n : ℝ) * b * h) * (Z_spin1 n (by omega) D₀ a rotI b) ^ 2 := by
      have hsq := pow_le_pow_left₀ hZD_n.le hden 2
      rw [mul_pow, ← Real.exp_nat_mul] at hsq
      have hexp_eq : (2 : ℕ) * (b * (h * (n : ℝ))) = 2 * (n : ℝ) * b * h := by push_cast; ring
      rwa [hexp_eq] at hsq
    have hprod_pos : 0 < Real.exp (2 * (n : ℝ) * b * h) * (Z_spin1 n (by omega) D₀ a rotI b) ^ 2 :=
      mul_pos (Real.exp_pos _) (pow_pos hZ0_n 2)
    calc Real.exp (-2 * (n : ℝ) * b * h) *
          (Z_spin1 (2 * n) (by omega) D₀ a rotI b / (Z_spin1 n (by omega) D₀ a rotI b) ^ 2)
        = Z_spin1 (2 * n) (by omega) D₀ a rotI b /
            (Real.exp (2 * (n : ℝ) * b * h) * (Z_spin1 n (by omega) D₀ a rotI b) ^ 2) := by
              rw [show (-2 * (n : ℝ) * b * h) = -(2 * (n : ℝ) * b * h) by ring, Real.exp_neg]
              field_simp [(Real.exp_pos _).ne', hZ0_n.ne']
      _ ≤ Z_spin1 (2 * n) (by omega) D a rotI b /
            (Real.exp (2 * (n : ℝ) * b * h) * (Z_spin1 n (by omega) D₀ a rotI b) ^ 2) :=
            div_le_div_of_nonneg_right hnum hprod_pos.le
      _ ≤ Z_spin1 (2 * n) (by omega) D a rotI b / (Z_spin1 n (by omega) D a rotI b) ^ 2 :=
            div_le_div_of_nonneg_left (hZ_pos (2 * n) (by omega) D).le (pow_pos hZD_n 2) hden2

/-- **Temporal purity transport across coupling `D` (`|D - D₀| ≤ h`)**:
`Real.exp (-2 * m * b * h) * T(m, b; D₀) ≤ T(m, b; D)`. -/
theorem spin1_T_transport {D₀ D h a b : ℝ} (hD : |D - D₀| ≤ h) (hb : 0 < b)
    {m : ℕ} (hm_even : Even m) (hm4 : 4 ≤ m) :
    Real.exp (-2 * (m : ℝ) * b * h) * (spin1SpectralSystem D₀ a).toPuritySystem1D.T m b ≤
      (spin1SpectralSystem D a).toPuritySystem1D.T m b := by
  have hb2 : 0 < 2 * b := by linarith
  have hT_D : (spin1SpectralSystem D a).toPuritySystem1D.T m b =
      Z_spin1 m (by omega) D a rotI (2 * b) / (Z_spin1 m (by omega) D a rotI b) ^ 2 := by
    change (spin1SpectralSystem D a).Z m (2 * b) / ((spin1SpectralSystem D a).Z m b) ^ 2 = _
    rw [spin1SpectralSystem_Z_eq D a hm_even hm4 hb2,
      spin1SpectralSystem_Z_eq D a hm_even hm4 hb]
  have hT_D0 : (spin1SpectralSystem D₀ a).toPuritySystem1D.T m b =
      Z_spin1 m (by omega) D₀ a rotI (2 * b) / (Z_spin1 m (by omega) D₀ a rotI b) ^ 2 := by
    change (spin1SpectralSystem D₀ a).Z m (2 * b) / ((spin1SpectralSystem D₀ a).Z m b) ^ 2 = _
    rw [spin1SpectralSystem_Z_eq D₀ a hm_even hm4 hb2,
      spin1SpectralSystem_Z_eq D₀ a hm_even hm4 hb]
  rw [hT_D, hT_D0]
  have hZ_pos : ∀ (D' b' : ℝ), 0 < Z_spin1 m (by omega) D' a rotI b' := fun D' b' => by
    rw [Z_spin1_eq_matZ_shifted]; exact matZ_pos _ _ _
  have hZ0_b : 0 < Z_spin1 m (by omega) D₀ a rotI b := hZ_pos D₀ b
  have hZD_b : 0 < Z_spin1 m (by omega) D a rotI b := hZ_pos D b
  rcases le_total D₀ D with hge | hle
  · have hhi : D - D₀ ≤ h := (abs_le.mp hD).2
    have hnum := (Z_spin1_D_bounds_of_ge (n := m) (by omega) hge hhi a rotI hb2.le).1
    have hden := (Z_spin1_D_bounds_of_ge (n := m) (by omega) hge hhi a rotI hb.le).2
    have hexp_eq : -(2 * b) * (h * (m : ℝ)) = -2 * (m : ℝ) * b * h := by ring
    rw [hexp_eq] at hnum
    have hden2 : (Z_spin1 m (by omega) D a rotI b) ^ 2 ≤
        (Z_spin1 m (by omega) D₀ a rotI b) ^ 2 :=
      pow_le_pow_left₀ hZD_b.le hden 2
    calc Real.exp (-2 * (m : ℝ) * b * h) *
          (Z_spin1 m (by omega) D₀ a rotI (2 * b) / (Z_spin1 m (by omega) D₀ a rotI b) ^ 2)
        = (Real.exp (-2 * (m : ℝ) * b * h) * Z_spin1 m (by omega) D₀ a rotI (2 * b)) /
            (Z_spin1 m (by omega) D₀ a rotI b) ^ 2 := by ring
      _ ≤ Z_spin1 m (by omega) D a rotI (2 * b) / (Z_spin1 m (by omega) D₀ a rotI b) ^ 2 :=
            div_le_div_of_nonneg_right hnum (pow_nonneg hZ0_b.le 2)
      _ ≤ Z_spin1 m (by omega) D a rotI (2 * b) / (Z_spin1 m (by omega) D a rotI b) ^ 2 :=
            div_le_div_of_nonneg_left (hZ_pos D (2 * b)).le (pow_pos hZD_b 2) hden2
  · have hhi : D₀ - D ≤ h := by linarith [(abs_le.mp hD).1]
    have hnum := (Z_spin1_D_bounds_of_le (n := m) (by omega) hle hhi a rotI hb2.le).1
    have hden := (Z_spin1_D_bounds_of_le (n := m) (by omega) hle hhi a rotI hb.le).2
    have hden2 : (Z_spin1 m (by omega) D a rotI b) ^ 2 ≤
        Real.exp (2 * (m : ℝ) * b * h) * (Z_spin1 m (by omega) D₀ a rotI b) ^ 2 := by
      have hsq := pow_le_pow_left₀ hZD_b.le hden 2
      rw [mul_pow, ← Real.exp_nat_mul] at hsq
      have hexp_eq : (2 : ℕ) * (b * (h * (m : ℝ))) = 2 * (m : ℝ) * b * h := by push_cast; ring
      rwa [hexp_eq] at hsq
    have hprod_pos : 0 < Real.exp (2 * (m : ℝ) * b * h) * (Z_spin1 m (by omega) D₀ a rotI b) ^ 2 :=
      mul_pos (Real.exp_pos _) (pow_pos hZ0_b 2)
    calc Real.exp (-2 * (m : ℝ) * b * h) *
          (Z_spin1 m (by omega) D₀ a rotI (2 * b) / (Z_spin1 m (by omega) D₀ a rotI b) ^ 2)
        = Z_spin1 m (by omega) D₀ a rotI (2 * b) /
            (Real.exp (2 * (m : ℝ) * b * h) * (Z_spin1 m (by omega) D₀ a rotI b) ^ 2) := by
              rw [show (-2 * (m : ℝ) * b * h) = -(2 * (m : ℝ) * b * h) by ring, Real.exp_neg]
              field_simp [(Real.exp_pos _).ne', hZ0_b.ne']
      _ ≤ Z_spin1 m (by omega) D a rotI (2 * b) /
            (Real.exp (2 * (m : ℝ) * b * h) * (Z_spin1 m (by omega) D₀ a rotI b) ^ 2) :=
            div_le_div_of_nonneg_right hnum hprod_pos.le
      _ ≤ Z_spin1 m (by omega) D a rotI (2 * b) / (Z_spin1 m (by omega) D a rotI b) ^ 2 :=
            div_le_div_of_nonneg_left (hZ_pos D (2 * b)).le (pow_pos hZD_b 2) hden2

/-! ## 2. Exact Rational Bootstrap Rounds for Radius `10⁻⁶` (`L ≥ 1792`) and `10⁻⁷` (`L ≥ 896`) -/

/-- Exact rational upper bounds on the 5-round bootstrap defects for `|D - 1/4| ≤ 10⁻⁶`. -/
def int6P0 : ℚ := 1237932 / 10000000
def int6Q0 : ℚ := 1248536 / 10000000
def int6P1 : ℚ := 1192445 / 10000000
def int6Q1 : ℚ := 1163843 / 10000000
def int6P2 : ℚ := 1052952 / 10000000
def int6Q2 : ℚ :=  930991 / 10000000
def int6P3 : ℚ :=  712400 / 10000000
def int6Q3 : ℚ :=  477752 / 10000000
def int6P4 : ℚ :=  236437 / 10000000
def int6Q4 : ℚ :=   83941 / 10000000
def int6P5 : ℚ :=   16762 / 10000000
def int6Q5 : ℚ :=    1751 / 10000000

/-- Exact rational certificate for initial defect transport (`h = 10⁻⁶`) and all 5 coupled
bootstrap rounds `(56, 23) → (1792, 736)` reaching `(0.0016762, 0.0001751) < 1/100`. -/
theorem int6_five_rounded_updates_exact :
    1 - (1 - 2 * 56 * 23 * (1 / 1000000 : ℚ)) * (1 - caP0) ≤ int6P0 ∧
    1 - (1 - 4 * 56 * 23 * (1 / 1000000 : ℚ)) * (1 - caQ0) ≤ int6Q0 ∧
    ceilGrid7 (fQ (1 - (1 - int6P0) ^ 2 * (1 - int6Q0))) = int6P1 ∧
    ceilGrid7 (fQ (1 - (1 - int6Q0) ^ 2 * (1 - int6P1))) = int6Q1 ∧
    ceilGrid7 (fQ (1 - (1 - int6P1) ^ 2 * (1 - int6Q1))) = int6P2 ∧
    ceilGrid7 (fQ (1 - (1 - int6Q1) ^ 2 * (1 - int6P2))) = int6Q2 ∧
    ceilGrid7 (fQ (1 - (1 - int6P2) ^ 2 * (1 - int6Q2))) = int6P3 ∧
    ceilGrid7 (fQ (1 - (1 - int6Q2) ^ 2 * (1 - int6P3))) = int6Q3 ∧
    ceilGrid7 (fQ (1 - (1 - int6P3) ^ 2 * (1 - int6Q3))) = int6P4 ∧
    ceilGrid7 (fQ (1 - (1 - int6Q3) ^ 2 * (1 - int6P4))) = int6Q4 ∧
    ceilGrid7 (fQ (1 - (1 - int6P4) ^ 2 * (1 - int6Q4))) = int6P5 ∧
    ceilGrid7 (fQ (1 - (1 - int6Q4) ^ 2 * (1 - int6P5))) = int6Q5 ∧
    int6P5 < 1 / 100 ∧ int6Q5 < 1 / 100 := by
  decide +kernel

/-- Exact rational upper bounds on the 4-round bootstrap defects for `|D - 1/4| ≤ 10⁻⁷`. -/
def int7P0 : ℚ := 1217565 / 10000000
def int7Q0 : ℚ := 1207747 / 10000000
def int7P1 : ℚ := 1126157 / 10000000
def int7Q1 : ℚ := 1047750 / 10000000
def int7P2 : ℚ :=  875916 / 10000000
def int7Q2 : ℚ :=  675501 / 10000000
def int7P3 : ℚ :=  415405 / 10000000
def int7Q3 : ℚ :=  199967 / 10000000
def int7P4 : ℚ :=   61353 / 10000000
def int7Q4 : ℚ :=   11355 / 10000000

/-- Exact rational certificate for initial defect transport (`h = 10⁻⁷`) and all 4 coupled
bootstrap rounds `(56, 23) → (896, 368)` reaching `(0.0061353, 0.0011355) < 1/100`. -/
theorem int7_four_rounded_updates_exact :
    1 - (1 - 2 * 56 * 23 * (1 / 10000000 : ℚ)) * (1 - caP0) ≤ int7P0 ∧
    1 - (1 - 4 * 56 * 23 * (1 / 10000000 : ℚ)) * (1 - caQ0) ≤ int7Q0 ∧
    ceilGrid7 (fQ (1 - (1 - int7P0) ^ 2 * (1 - int7Q0))) = int7P1 ∧
    ceilGrid7 (fQ (1 - (1 - int7Q0) ^ 2 * (1 - int7P1))) = int7Q1 ∧
    ceilGrid7 (fQ (1 - (1 - int7P1) ^ 2 * (1 - int7Q1))) = int7P2 ∧
    ceilGrid7 (fQ (1 - (1 - int7Q1) ^ 2 * (1 - int7P2))) = int7Q2 ∧
    ceilGrid7 (fQ (1 - (1 - int7P2) ^ 2 * (1 - int7Q2))) = int7P3 ∧
    ceilGrid7 (fQ (1 - (1 - int7Q2) ^ 2 * (1 - int7P3))) = int7Q3 ∧
    ceilGrid7 (fQ (1 - (1 - int7P3) ^ 2 * (1 - int7Q3))) = int7P4 ∧
    ceilGrid7 (fQ (1 - (1 - int7Q3) ^ 2 * (1 - int7P4))) = int7Q4 ∧
    int7P4 < 1 / 100 ∧ int7Q4 < 1 / 100 := by
  decide +kernel

private lemma rounded_step_grid7 (sys : PuritySystem1D)
    {n : ℕ} {b : ℝ} {p q p' q' : ℚ}
    (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (hp'1 : p' < 1)
    (hp'eq : ceilGrid7 (fQ (1 - (1 - p) ^ 2 * (1 - q))) = p')
    (hq'eq : ceilGrid7 (fQ (1 - (1 - q) ^ 2 * (1 - p'))) = q')
    (hS : 1 - sys.S n b ≤ (p : ℝ)) (hT : 1 - sys.T (2 * n) b ≤ (q : ℝ)) :
    1 - sys.S (2 * n) (2 * b) ≤ (p' : ℝ) ∧ 1 - sys.T (4 * n) (2 * b) ≤ (q' : ℝ) := by
  have hp'_le : fQ (1 - (1 - p) ^ 2 * (1 - q)) ≤ p' := hp'eq ▸ le_ceilGrid7 _
  have hq'_le : fQ (1 - (1 - q) ^ 2 * (1 - p')) ≤ q' := hq'eq ▸ le_ceilGrid7 _
  have hp'_R : purityUpdate (1 - (1 - (p : ℝ)) ^ 2 * (1 - (q : ℝ))) ≤ (p' : ℝ) := by
    have hcast : ((fQ (1 - (1 - p) ^ 2 * (1 - q)) : ℚ) : ℝ) ≤ (p' : ℝ) := by exact_mod_cast hp'_le
    rw [fQ_cast] at hcast; push_cast at hcast; exact hcast
  have hq'_R : purityUpdate (1 - (1 - (q : ℝ)) ^ 2 * (1 - (p' : ℝ))) ≤ (q' : ℝ) := by
    have hcast : ((fQ (1 - (1 - q) ^ 2 * (1 - p')) : ℚ) : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'_le
    rw [fQ_cast] at hcast; push_cast at hcast; exact hcast
  exact sys.rounded_coupled_update hn h4 hb
    (by exact_mod_cast hp0) (by exact_mod_cast hp1)
    (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    (by exact_mod_cast hp'1) hS hT hp'_R hq'_R

/-- Five exact upward-rounded doubling rounds `(56, 23) → (1792, 736)` for radius `10⁻⁶`. -/
theorem int6_five_rounds_to_1792_exact (sys : PuritySystem1D)
    (hS0 : 1 - sys.S 56 (23 : ℝ) ≤ (int6P0 : ℝ))
    (hT0 : 1 - sys.T 112 (23 : ℝ) ≤ (int6Q0 : ℝ)) :
    1 - sys.S 1792 (736 : ℝ) ≤ (int6P5 : ℝ) ∧
    1 - sys.T 3584 (736 : ℝ) ≤ (int6Q5 : ℝ) := by
  have hex := int6_five_rounded_updates_exact
  have r1 := rounded_step_grid7 sys (n := 56) (b := 23) ⟨28, by omega⟩ (by omega) (by norm_num)
    (by unfold int6P0; norm_num) (by unfold int6P0; norm_num)
    (by unfold int6Q0; norm_num) (by unfold int6Q0; norm_num)
    (by unfold int6P1; norm_num) hex.2.2.1 hex.2.2.2.1 hS0 hT0
  have r2 := rounded_step_grid7 sys (n := 112) (b := 46) ⟨56, by omega⟩ (by omega) (by norm_num)
    (by unfold int6P1; norm_num) (by unfold int6P1; norm_num)
    (by unfold int6Q1; norm_num) (by unfold int6Q1; norm_num)
    (by unfold int6P2; norm_num) hex.2.2.2.2.1 hex.2.2.2.2.2.1
    (by convert r1.1 using 2 <;> norm_num) (by convert r1.2 using 2 <;> norm_num)
  have r3 := rounded_step_grid7 sys (n := 224) (b := 92) ⟨112, by omega⟩ (by omega) (by norm_num)
    (by unfold int6P2; norm_num) (by unfold int6P2; norm_num)
    (by unfold int6Q2; norm_num) (by unfold int6Q2; norm_num)
    (by unfold int6P3; norm_num) hex.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.1
    (by convert r2.1 using 2 <;> norm_num) (by convert r2.2 using 2 <;> norm_num)
  have r4 := rounded_step_grid7 sys (n := 448) (b := 184) ⟨224, by omega⟩ (by omega) (by norm_num)
    (by unfold int6P3; norm_num) (by unfold int6P3; norm_num)
    (by unfold int6Q3; norm_num) (by unfold int6Q3; norm_num)
    (by unfold int6P4; norm_num) hex.2.2.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.2.2.1
    (by convert r3.1 using 2 <;> norm_num) (by convert r3.2 using 2 <;> norm_num)
  have r5 := rounded_step_grid7 sys (n := 896) (b := 368) ⟨448, by omega⟩ (by omega) (by norm_num)
    (by unfold int6P4; norm_num) (by unfold int6P4; norm_num)
    (by unfold int6Q4; norm_num) (by unfold int6Q4; norm_num)
    (by unfold int6P5; norm_num) hex.2.2.2.2.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.2.2.2.2.1
    (by convert r4.1 using 2 <;> norm_num) (by convert r4.2 using 2 <;> norm_num)
  exact ⟨by convert r5.1 using 2 <;> norm_num, by convert r5.2 using 2 <;> norm_num⟩

/-- Four exact upward-rounded doubling rounds `(56, 23) → (896, 368)` for radius `10⁻⁷`. -/
theorem int7_four_rounds_to_896_exact (sys : PuritySystem1D)
    (hS0 : 1 - sys.S 56 (23 : ℝ) ≤ (int7P0 : ℝ))
    (hT0 : 1 - sys.T 112 (23 : ℝ) ≤ (int7Q0 : ℝ)) :
    1 - sys.S 896 (368 : ℝ) ≤ (int7P4 : ℝ) ∧
    1 - sys.T 1792 (368 : ℝ) ≤ (int7Q4 : ℝ) := by
  have hex := int7_four_rounded_updates_exact
  have r1 := rounded_step_grid7 sys (n := 56) (b := 23) ⟨28, by omega⟩ (by omega) (by norm_num)
    (by unfold int7P0; norm_num) (by unfold int7P0; norm_num)
    (by unfold int7Q0; norm_num) (by unfold int7Q0; norm_num)
    (by unfold int7P1; norm_num) hex.2.2.1 hex.2.2.2.1 hS0 hT0
  have r2 := rounded_step_grid7 sys (n := 112) (b := 46) ⟨56, by omega⟩ (by omega) (by norm_num)
    (by unfold int7P1; norm_num) (by unfold int7P1; norm_num)
    (by unfold int7Q1; norm_num) (by unfold int7Q1; norm_num)
    (by unfold int7P2; norm_num) hex.2.2.2.2.1 hex.2.2.2.2.2.1
    (by convert r1.1 using 2 <;> norm_num) (by convert r1.2 using 2 <;> norm_num)
  have r3 := rounded_step_grid7 sys (n := 224) (b := 92) ⟨112, by omega⟩ (by omega) (by norm_num)
    (by unfold int7P2; norm_num) (by unfold int7P2; norm_num)
    (by unfold int7Q2; norm_num) (by unfold int7Q2; norm_num)
    (by unfold int7P3; norm_num) hex.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.1
    (by convert r2.1 using 2 <;> norm_num) (by convert r2.2 using 2 <;> norm_num)
  have r4 := rounded_step_grid7 sys (n := 448) (b := 184) ⟨224, by omega⟩ (by omega) (by norm_num)
    (by unfold int7P3; norm_num) (by unfold int7P3; norm_num)
    (by unfold int7Q3; norm_num) (by unfold int7Q3; norm_num)
    (by unfold int7P4; norm_num) hex.2.2.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.2.2.1
    (by convert r3.1 using 2 <;> norm_num) (by convert r3.2 using 2 <;> norm_num)
  exact ⟨by convert r4.1 using 2 <;> norm_num, by convert r4.2 using 2 <;> norm_num⟩

/-! ## 3. Shared Seed Extraction at `D_* = 1/4` -/

private lemma candidate_a_center_seed56
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
      (caShift * (n_trial : ℝ)) * dotProduct ψ ψ ≤ 0) :
    1 - (spin1SpectralSystem (1 / 4) caShift).toPuritySystem1D.S 56 (23 : ℝ) ≤ (caP0 : ℝ) ∧
    1 - (spin1SpectralSystem (1 / 4) caShift).toPuritySystem1D.T 112 (23 : ℝ) ≤ (caQ0 : ℝ) := by
  let sys0 := spin1SpectralSystem (1 / 4) caShift
  rcases spin1_D4_sector_moments (1 / 4) caShift (b := 31 / 2) (by norm_num) with
    ⟨lam155, hsumm155, h155I_eq, h155Z_eq, h155X_eq, h155F_eq⟩
  rcases spin1_D4_sector_moments (1 / 4) caShift (b := 23) (by norm_num) with
    ⟨lam23, hsumm23, h23I_eq, h23Z_eq, h23X_eq, h23F_eq⟩
  rcases exists_eig_le_of_rayleigh (by omega) (1 / 4) caShift rotI ψ hψ_nz hψ_le with ⟨kt, hkt⟩
  have htrial : ∃ k : Fin (sys0.d 112), sys0.E 112 k + sys0.a * (112 : ℝ) ≤ 0 := by
    have h112_cast : (112 : ℝ) = (n_trial : ℝ) := by rw [hn_trial]; norm_num
    rw [h112_cast, ← hn_trial]
    refine ⟨Fintype.equivFin (Spin1Cfg n_trial) kt, ?_⟩
    simpa [sys0, spin1SpectralSystem, show 3 ≤ n_trial by omega] using hkt
  exact (candidate_a_seed896_from_raw_table sys0 lam155 lam23 hsumm155 hsumm23
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
    htrial).1

/-! ## 4. Main Continuous-Interval Uniform Haldane Gap Theorems -/

/-- **Continuous-Interval Physical Spin-1 Haldane Gap Theorem (`D ∈ [0.249999, 0.250001]`, `L ≥ 1792`)**:
from ONLY the archived Candidate A finite inputs at the center `D_* = 1/4` (88 thermal trace
enclosures for `n = 4..14` and a single `L = 112` variational trial vector), proves that for
**every continuous anisotropy coupling `D ∈ [249999/10^6, 250001/10^6]`** and **every even ring
`L ≥ 1792`**, the concrete `3^L × 3^L` physical Hamiltonian matrix `H_spin1 L _ D rotI` has a
unique ground eigenvalue `k₀ : Spin1Cfg L` and uniform spectral gap
`Real.log 20 / 736 < E_k - E_{k₀}` (`≈ 0.00407029`) for all `k ≠ k₀`. -/
theorem candidate_a_physical_spin1_interval_gap_1792
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
    {D : ℝ} (hD_lo : (249999 : ℝ) / 1000000 ≤ D) (hD_hi : D ≤ (250001 : ℝ) / 1000000)
    {L : ℕ} (hL_even : Even L) (hL_ge : 1792 ≤ L) :
    ∃ k₀ : Spin1Cfg L,
      (∀ k : Spin1Cfg L,
        (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k₀ ≤
          (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k) ∧
      (∀ k : Spin1Cfg L, k ≠ k₀ →
        Real.log 20 / 736 <
          (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k -
            (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k₀) := by
  have hD_abs : |D - (1 / 4 : ℝ)| ≤ (1 / 1000000 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcenter := candidate_a_center_seed56 h155_I h155_Z h155_X h155_F
    h23_I h23_Z h23_X h23_F hn_trial ψ hψ_nz hψ_le
  have hex := int6_five_rounded_updates_exact
  let sys := spin1SpectralSystem D caShift
  have hS56 : 1 - sys.toPuritySystem1D.S 56 (23 : ℝ) ≤ (int6P0 : ℝ) := by
    have htr := spin1_S_transport (D₀ := 1 / 4) (D := D) (h := 1 / 1000000) (a := caShift)
      (b := 23) hD_abs (by norm_num) (n := 56) ⟨28, by omega⟩ (by omega)
    have hexp : 1 - 2 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ) ≤
        Real.exp (-2 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ)) := by
      have := Real.add_one_le_exp (-2 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ))
      linarith
    have h1 : (1 - 2 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ)) * (1 - (caP0 : ℝ)) ≤
        sys.toPuritySystem1D.S 56 (23 : ℝ) := by
      have hnonneg1 : 0 ≤ 1 - 2 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ) := by norm_num
      have hnonneg2 : 0 ≤ 1 - (caP0 : ℝ) := by unfold caP0; norm_num
      have hS0_ge : 1 - (caP0 : ℝ) ≤ (spin1SpectralSystem (1 / 4) caShift).toPuritySystem1D.S 56 (23 : ℝ) := by
        linarith [hcenter.1]
      exact (mul_le_mul hexp hS0_ge hnonneg2 (Real.exp_pos _).le).trans htr
    have hrat : 1 - (1 - 2 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ)) * (1 - (caP0 : ℝ)) ≤ (int6P0 : ℝ) := by
      have h := hex.1
      have hR : ((1 - (1 - 2 * 56 * 23 * (1 / 1000000 : ℚ)) * (1 - caP0) : ℚ) : ℝ) ≤ (int6P0 : ℝ) := by
        exact_mod_cast h
      push_cast at hR; exact hR
    linarith
  have hT112 : 1 - sys.toPuritySystem1D.T 112 (23 : ℝ) ≤ (int6Q0 : ℝ) := by
    have htr := spin1_T_transport (D₀ := 1 / 4) (D := D) (h := 1 / 1000000) (a := caShift)
      (b := 23) hD_abs (by norm_num) (m := 112) ⟨56, by omega⟩ (by omega)
    have hexp : 1 - 4 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ) ≤
        Real.exp (-2 * (112 : ℝ) * 23 * (1 / 1000000 : ℝ)) := by
      have := Real.add_one_le_exp (-2 * (112 : ℝ) * 23 * (1 / 1000000 : ℝ))
      linarith
    have h1 : (1 - 4 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ)) * (1 - (caQ0 : ℝ)) ≤
        sys.toPuritySystem1D.T 112 (23 : ℝ) := by
      have hnonneg2 : 0 ≤ 1 - (caQ0 : ℝ) := by unfold caQ0; norm_num
      have hT0_ge : 1 - (caQ0 : ℝ) ≤ (spin1SpectralSystem (1 / 4) caShift).toPuritySystem1D.T 112 (23 : ℝ) := by
        linarith [hcenter.2]
      exact (mul_le_mul hexp hT0_ge hnonneg2 (Real.exp_pos _).le).trans htr
    have hrat : 1 - (1 - 4 * (56 : ℝ) * 23 * (1 / 1000000 : ℝ)) * (1 - (caQ0 : ℝ)) ≤ (int6Q0 : ℝ) := by
      have h := hex.2.1
      have hR : ((1 - (1 - 4 * 56 * 23 * (1 / 1000000 : ℚ)) * (1 - caQ0) : ℚ) : ℝ) ≤ (int6Q0 : ℝ) := by
        exact_mod_cast h
      push_cast at hR; exact hR
    linarith
  have h5 := int6_five_rounds_to_1792_exact sys.toPuritySystem1D hS56 hT112
  have hp5 : (int6P5 : ℝ) < (1 / 100 : ℝ) := by unfold int6P5; norm_num
  have hq5 : (int6Q5 : ℝ) < (1 / 100 : ℝ) := by unfold int6Q5; norm_num
  have hS1792 : 1 - sys.toPuritySystem1D.S 1792 (736 : ℝ) ≤ (1 / 100 : ℝ) := by linarith [h5.1]
  have hT3584 : 1 - sys.toPuritySystem1D.T 3584 (736 : ℝ) ≤ (1 / 100 : ℝ) := by linarith [h5.2]
  have hG5 : bootstrapCoeff (1 / 100 : ℝ) ≤ 5 := by unfold bootstrapCoeff; norm_num
  have hd_pos : 0 < sys.d L := sys.d_pos L hL_even (by omega)
  have hne : (Finset.univ : Finset (Fin (sys.d L))).Nonempty := ⟨⟨0, hd_pos⟩, Finset.mem_univ _⟩
  rcases Finset.exists_min_image Finset.univ (sys.E L) hne with ⟨k₀, _, hk₀_min⟩
  have hres := uniform_gap_from_purities sys.toPuritySystem1D sys.interp
    (n₀ := 1792) (b₀ := 736) (u₀ := 1 / 100) (C := 5)
    ⟨896, by omega⟩ (by omega) (by norm_num)
    (by norm_num) (by norm_num) hG5 (by norm_num) (by norm_num)
    hS1792 (by convert hT3584 using 2) hL_even hL_ge
    (fun k => sys.E L k + sys.a * (L : ℝ)) k₀
    (fun k => by linarith [hk₀_min k (Finset.mem_univ k)])
    (fun b hb => sys.Z_eq L b hL_even (by omega) hb)
  have h20 : (1 : ℝ) / (5 * (1 / 100 : ℝ)) = 20 := by norm_num
  let e := Fintype.equivFin (Spin1Cfg L)
  refine ⟨e.symm k₀, fun k => ?_, fun k hne => ?_⟩
  · have h := hk₀_min (e k) (Finset.mem_univ _)
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using h
  · have hne' : e k ≠ k₀ := fun heq => hne (by simpa [e] using congrArg e.symm heq)
    have h := hres.2 (e k) hne'
    rw [h20] at h
    have hsub : Real.log 20 / 736 < sys.E L (e k) - sys.E L k₀ := by linarith
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using hsub

/-- **Characteristic-polynomial roots formulation (`D ∈ [0.249999, 0.250001]`, `L ≥ 1792`)**:
states the simple ground root and uniform spectral gap `> log(20) / 736` directly on the
multiset `(H_spin1 L _ D rotI).charpoly.roots` with exact multiplicity. -/
theorem candidate_a_physical_spin1_interval_charpoly_gap_1792
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
    {D : ℝ} (hD_lo : (249999 : ℝ) / 1000000 ≤ D) (hD_hi : D ≤ (250001 : ℝ) / 1000000)
    {L : ℕ} (hL_even : Even L) (hL_ge : 1792 ≤ L) :
    ∃ (E₀ : ℝ) (rest : Multiset ℝ),
      (H_spin1 L (by omega) D rotI).charpoly.roots = E₀ ::ₘ rest ∧
      rest.card + 1 = 3 ^ L ∧
      ∀ E ∈ rest, Real.log 20 / 736 < E - E₀ := by
  rcases candidate_a_physical_spin1_interval_gap_1792 h155_I h155_Z h155_X h155_F
      h23_I h23_Z h23_X h23_F hn_trial ψ hψ_nz hψ_le hD_lo hD_hi hL_even hL_ge with ⟨k₀, _, hsep⟩
  let hH := H_spin1_isHermitian L (by omega) D rotI
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

/-- **Tight-Radius Continuous-Interval Corollary (`D ∈ [0.2499999, 0.2500001]`, `L ≥ 896`)**:
preserves the exact original Candidate A length threshold `L ≥ 896` and uniform gap
`Real.log 20 / 368 ≈ 0.00814058` in 4 exact scalar rounds across the continuous interval
`[2499999/10^7, 2500001/10^7]`. -/
theorem candidate_a_physical_spin1_interval_gap_896
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
    {D : ℝ} (hD_lo : (2499999 : ℝ) / 10000000 ≤ D) (hD_hi : D ≤ (2500001 : ℝ) / 10000000)
    {L : ℕ} (hL_even : Even L) (hL_ge : 896 ≤ L) :
    ∃ k₀ : Spin1Cfg L,
      (∀ k : Spin1Cfg L,
        (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k₀ ≤
          (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k) ∧
      (∀ k : Spin1Cfg L, k ≠ k₀ →
        Real.log 20 / 368 <
          (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k -
            (H_spin1_isHermitian L (by omega) D rotI).eigenvalues k₀) := by
  have hD_abs : |D - (1 / 4 : ℝ)| ≤ (1 / 10000000 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcenter := candidate_a_center_seed56 h155_I h155_Z h155_X h155_F
    h23_I h23_Z h23_X h23_F hn_trial ψ hψ_nz hψ_le
  have hex := int7_four_rounded_updates_exact
  let sys := spin1SpectralSystem D caShift
  have hS56 : 1 - sys.toPuritySystem1D.S 56 (23 : ℝ) ≤ (int7P0 : ℝ) := by
    have htr := spin1_S_transport (D₀ := 1 / 4) (D := D) (h := 1 / 10000000) (a := caShift)
      (b := 23) hD_abs (by norm_num) (n := 56) ⟨28, by omega⟩ (by omega)
    have hexp : 1 - 2 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ) ≤
        Real.exp (-2 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ)) := by
      have := Real.add_one_le_exp (-2 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ))
      linarith
    have h1 : (1 - 2 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ)) * (1 - (caP0 : ℝ)) ≤
        sys.toPuritySystem1D.S 56 (23 : ℝ) := by
      have hnonneg2 : 0 ≤ 1 - (caP0 : ℝ) := by unfold caP0; norm_num
      have hS0_ge : 1 - (caP0 : ℝ) ≤ (spin1SpectralSystem (1 / 4) caShift).toPuritySystem1D.S 56 (23 : ℝ) := by
        linarith [hcenter.1]
      exact (mul_le_mul hexp hS0_ge hnonneg2 (Real.exp_pos _).le).trans htr
    have hrat : 1 - (1 - 2 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ)) * (1 - (caP0 : ℝ)) ≤ (int7P0 : ℝ) := by
      have h := hex.1
      have hR : ((1 - (1 - 2 * 56 * 23 * (1 / 10000000 : ℚ)) * (1 - caP0) : ℚ) : ℝ) ≤ (int7P0 : ℝ) := by
        exact_mod_cast h
      push_cast at hR; exact hR
    linarith
  have hT112 : 1 - sys.toPuritySystem1D.T 112 (23 : ℝ) ≤ (int7Q0 : ℝ) := by
    have htr := spin1_T_transport (D₀ := 1 / 4) (D := D) (h := 1 / 10000000) (a := caShift)
      (b := 23) hD_abs (by norm_num) (m := 112) ⟨56, by omega⟩ (by omega)
    have hexp : 1 - 4 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ) ≤
        Real.exp (-2 * (112 : ℝ) * 23 * (1 / 10000000 : ℝ)) := by
      have := Real.add_one_le_exp (-2 * (112 : ℝ) * 23 * (1 / 10000000 : ℝ))
      linarith
    have h1 : (1 - 4 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ)) * (1 - (caQ0 : ℝ)) ≤
        sys.toPuritySystem1D.T 112 (23 : ℝ) := by
      have hnonneg2 : 0 ≤ 1 - (caQ0 : ℝ) := by unfold caQ0; norm_num
      have hT0_ge : 1 - (caQ0 : ℝ) ≤ (spin1SpectralSystem (1 / 4) caShift).toPuritySystem1D.T 112 (23 : ℝ) := by
        linarith [hcenter.2]
      exact (mul_le_mul hexp hT0_ge hnonneg2 (Real.exp_pos _).le).trans htr
    have hrat : 1 - (1 - 4 * (56 : ℝ) * 23 * (1 / 10000000 : ℝ)) * (1 - (caQ0 : ℝ)) ≤ (int7Q0 : ℝ) := by
      have h := hex.2.1
      have hR : ((1 - (1 - 4 * 56 * 23 * (1 / 10000000 : ℚ)) * (1 - caQ0) : ℚ) : ℝ) ≤ (int7Q0 : ℝ) := by
        exact_mod_cast h
      push_cast at hR; exact hR
    linarith
  have h4 := int7_four_rounds_to_896_exact sys.toPuritySystem1D hS56 hT112
  have hp4 : (int7P4 : ℝ) < (1 / 100 : ℝ) := by unfold int7P4; norm_num
  have hq4 : (int7Q4 : ℝ) < (1 / 100 : ℝ) := by unfold int7Q4; norm_num
  have hS896 : 1 - sys.toPuritySystem1D.S 896 (368 : ℝ) ≤ (1 / 100 : ℝ) := by linarith [h4.1]
  have hT1792 : 1 - sys.toPuritySystem1D.T 1792 (368 : ℝ) ≤ (1 / 100 : ℝ) := by linarith [h4.2]
  have hG5 : bootstrapCoeff (1 / 100 : ℝ) ≤ 5 := by unfold bootstrapCoeff; norm_num
  have hd_pos : 0 < sys.d L := sys.d_pos L hL_even (by omega)
  have hne : (Finset.univ : Finset (Fin (sys.d L))).Nonempty := ⟨⟨0, hd_pos⟩, Finset.mem_univ _⟩
  rcases Finset.exists_min_image Finset.univ (sys.E L) hne with ⟨k₀, _, hk₀_min⟩
  have hres := uniform_gap_from_purities sys.toPuritySystem1D sys.interp
    (n₀ := 896) (b₀ := 368) (u₀ := 1 / 100) (C := 5)
    ⟨448, by omega⟩ (by omega) (by norm_num)
    (by norm_num) (by norm_num) hG5 (by norm_num) (by norm_num)
    hS896 (by convert hT1792 using 2) hL_even hL_ge
    (fun k => sys.E L k + sys.a * (L : ℝ)) k₀
    (fun k => by linarith [hk₀_min k (Finset.mem_univ k)])
    (fun b hb => sys.Z_eq L b hL_even (by omega) hb)
  have h20 : (1 : ℝ) / (5 * (1 / 100 : ℝ)) = 20 := by norm_num
  let e := Fintype.equivFin (Spin1Cfg L)
  refine ⟨e.symm k₀, fun k => ?_, fun k hne => ?_⟩
  · have h := hk₀_min (e k) (Finset.mem_univ _)
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using h
  · have hne' : e k ≠ k₀ := fun heq => hne (by simpa [e] using congrArg e.symm heq)
    have h := hres.2 (e k) hne'
    rw [h20] at h
    have hsub : Real.log 20 / 368 < sys.E L (e k) - sys.E L k₀ := by linarith
    simpa [sys, spin1SpectralSystem, e, show 3 ≤ L by omega] using hsub

/-- **Characteristic-polynomial roots formulation (`D ∈ [0.2499999, 0.2500001]`, `L ≥ 896`)**. -/
theorem candidate_a_physical_spin1_interval_charpoly_gap_896
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
    {D : ℝ} (hD_lo : (2499999 : ℝ) / 10000000 ≤ D) (hD_hi : D ≤ (2500001 : ℝ) / 10000000)
    {L : ℕ} (hL_even : Even L) (hL_ge : 896 ≤ L) :
    ∃ (E₀ : ℝ) (rest : Multiset ℝ),
      (H_spin1 L (by omega) D rotI).charpoly.roots = E₀ ::ₘ rest ∧
      rest.card + 1 = 3 ^ L ∧
      ∀ E ∈ rest, Real.log 20 / 368 < E - E₀ := by
  rcases candidate_a_physical_spin1_interval_gap_896 h155_I h155_Z h155_X h155_F
      h23_I h23_Z h23_X h23_F hn_trial ψ hψ_nz hψ_le hD_lo hD_hi hL_even hL_ge with ⟨k₀, _, hsep⟩
  let hH := H_spin1_isHermitian L (by omega) D rotI
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

end PurityBootstrap.Spin1Interval
