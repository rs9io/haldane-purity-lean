import PurityBootstrap.Basic
import PurityBootstrap.OneD
import PurityBootstrap.SymmetryTwists
import PurityBootstrap.MatrixTools
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Finite-Dimensional Lie–Trotter Formula & Trotter-Limit Ising Multiplet Theorem

Eliminates infinite-dimensional compact-operator transfer hypotheses completely:
1. **Finite-dimensional 3-term Lie–Trotter (`tendsto_trotter3`)**:
   for any real matrices `A, B, C : Matrix n n ℝ`,
   `(exp ((1/M) • A) * exp ((1/M) • B) * exp ((1/M) • C)) ^ M → exp (A + B + C)` as `M → ∞`.
2. **Spectral trace identity (`trace_exp_eq_matZ`)**:
   for any real symmetric matrix `H`, `Matrix.trace (NormedSpace.exp ((-b) • H)) = matZ H hH b`.
3. **Involutive exponential (`exp_involutive`)**:
   if `M * M = 1`, then `NormedSpace.exp (a • M) = Real.cosh a • 1 + Real.sinh a • M`.
4. **Closed spatial inequalities from finite-dimensional PSD transfer pairs (`psd_pair_spatial_ineqs`)**:
   for any `V₀, V₁`, the Gram matrices `A₀ = V₀ * V₀ᵀ`, `A₁ = V₁ * V₁ᵀ` are real symmetric PSD,
   so `Z_+(2m) = Tr(A₀^m) + Tr(A₁^m)` and `Z_-(2m) = Tr(A₀^m) - Tr(A₁^m)` satisfy all 6 closed
   spatial inequalities of the purity bootstrap and symmetry-twist theorem.
5. **Trotter-limit Ising multiplet theorem (`TrotterIsingSystem.ising_multiplet_sorted`)**:
   passes all 6 closed spatial inequalities through `M → ∞` via `le_of_tendsto_of_tendsto`,
   delivering the full sorted doublet-splitting + multiplet-gap theorem with ZERO infinite-dim
   transfer operators.
-/

namespace PurityBootstrap.LieTrotter

open scoped BigOperators Matrix
open Filter Matrix NormedSpace PurityBootstrap PurityBootstrap.SymmetryTwists PurityBootstrap.MatrixTools

/-! ## Finite-Dimensional Matrix Exponential Bounds & 3-Term Lie–Trotter -/

section MatrixExp

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator

private lemma matrix_norm_one_le : ‖(1 : Matrix n n ℝ)‖ ≤ 1 := by
  by_cases hne : Nonempty n
  · rw [Matrix.linfty_opNorm_def]
    have hsup : Finset.univ.sup (fun i : n => ∑ j : n, ‖(1 : Matrix n n ℝ) i j‖₊) ≤ (1 : NNReal) := by
      refine Finset.sup_le fun i _ => ?_
      have h1 : ∑ j : n, ‖(1 : Matrix n n ℝ) i j‖₊ = (1 : NNReal) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Matrix.one_apply, Ne.symm hji]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      exact h1.le
    exact_mod_cast hsup
  · haveI : IsEmpty n := not_nonempty_iff.mp hne
    rw [Matrix.linfty_opNorm_def]
    simp

private lemma matrix_norm_pow_le (x : Matrix n n ℝ) : ∀ k : ℕ, ‖x ^ k‖ ≤ ‖x‖ ^ k
  | 0 => by simpa using (matrix_norm_one_le (n := n))
  | k + 1 => by
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (matrix_norm_pow_le x k) (norm_nonneg x))

private lemma real_exp_hasSum (a : ℝ) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * a ^ k) (Real.exp a) := by
  have h := Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) a
  refine h.congr_fun fun k => ?_
  rw [div_eq_inv_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Operator-norm bound `‖exp x‖ ≤ Real.exp ‖x‖` for finite real matrices. -/
lemma norm_exp_le_real_exp_norm (x : Matrix n n ℝ) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hhas : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • x ^ k) (NormedSpace.exp x) := by
    have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) x
    simpa [NormedSpace.expSeries_apply_eq] using h
  have hsum_norm : Summable (fun k : ℕ => ‖((k.factorial : ℝ)⁻¹) • x ^ k‖) :=
    hhas.summable.norm
  have hreal_has := real_exp_hasSum ‖x‖
  have hle : ‖NormedSpace.exp x‖ ≤ ∑' k : ℕ, ‖((k.factorial : ℝ)⁻¹) • x ^ k‖ := by
    rw [← hhas.tsum_eq]
    exact norm_tsum_le_tsum_norm hsum_norm
  refine hle.trans ?_
  rw [← hreal_has.tsum_eq]
  refine hsum_norm.tsum_le_tsum (fun k => ?_) hreal_has.summable
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (matrix_norm_pow_le x k) (by positivity)

set_option backward.isDefEq.respectTransparency false in
/-- Second-order Taylor remainder bound: `‖exp x - 1 - x‖ ≤ ‖x‖^2 * Real.exp ‖x‖`. -/
lemma norm_exp_sub_one_sub_le (x : Matrix n n ℝ) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have hhas : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • x ^ k) (NormedSpace.exp x) := by
    have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) x
    simpa [NormedSpace.expSeries_apply_eq] using h
  have hshift : HasSum (fun k : ℕ => (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2))
      (NormedSpace.exp x - 1 - x) := by
    have h1 := (hasSum_nat_add_iff' 2).mpr hhas
    have hfin : ∑ i ∈ Finset.range 2, ((i.factorial : ℝ)⁻¹) • x ^ i = 1 + x := by
      simp [Finset.sum_range_succ]
    rw [hfin] at h1
    simpa [sub_sub] using h1
  have hsum_norm : Summable (fun k : ℕ => ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖) :=
    hshift.summable.norm
  have hreal_has := (real_exp_hasSum ‖x‖).mul_left (‖x‖ ^ 2)
  have hle : ‖NormedSpace.exp x - 1 - x‖ ≤
      ∑' k : ℕ, ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ := by
    rw [← hshift.tsum_eq]
    exact norm_tsum_le_tsum_norm hsum_norm
  refine hle.trans ?_
  rw [← hreal_has.tsum_eq]
  refine hsum_norm.tsum_le_tsum (fun k => ?_) hreal_has.summable
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hfact : (k.factorial : ℝ) ≤ ((k + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : k ≤ k + 2)
  have hinv : (((k + 2).factorial : ℝ)⁻¹) ≤ (k.factorial : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) hfact
  have hpow : ‖x ^ (k + 2)‖ ≤ ‖x‖ ^ 2 * ‖x‖ ^ k := by
    calc ‖x ^ (k + 2)‖ ≤ ‖x‖ ^ (k + 2) := matrix_norm_pow_le x (k + 2)
      _ = ‖x‖ ^ 2 * ‖x‖ ^ k := by rw [pow_add, mul_comm]
  calc (((k + 2).factorial : ℝ)⁻¹) * ‖x ^ (k + 2)‖
      ≤ (k.factorial : ℝ)⁻¹ * (‖x‖ ^ 2 * ‖x‖ ^ k) :=
        mul_le_mul hinv hpow (norm_nonneg _) (by positivity)
    _ = ‖x‖ ^ 2 * ((k.factorial : ℝ)⁻¹ * ‖x‖ ^ k) := by ring

/-- `exp (m • x) = (exp x) ^ m` for any natural `m` and real matrix `x`. -/
lemma exp_nsmul_eq_pow (x : Matrix n n ℝ) (m : ℕ) :
    NormedSpace.exp ((m : ℝ) • x) = (NormedSpace.exp x) ^ m := by
  have h : ((m : ℝ) • x) = m • x := by rw [Nat.cast_smul_eq_nsmul]
  rw [h, Matrix.exp_nsmul]

/-- Telescoping bound on `X^m - Y^m` in any normed ring. -/
private lemma norm_pow_sub_pow_le {X Y : Matrix n n ℝ} {R : ℝ}
    (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R) (hR : 1 ≤ R) :
    ∀ m : ℕ, ‖X ^ m - Y ^ m‖ ≤ (m : ℝ) * R ^ m * ‖X - Y‖
  | 0 => by simp
  | m + 1 => by
    have hsplit : X ^ (m + 1) - Y ^ (m + 1) =
        X ^ m * (X - Y) + (X ^ m - Y ^ m) * Y := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul]; abel
    rw [hsplit]
    have h1 : ‖X ^ m * (X - Y)‖ ≤ R ^ m * ‖X - Y‖ := by
      calc ‖X ^ m * (X - Y)‖ ≤ ‖X ^ m‖ * ‖X - Y‖ := norm_mul_le _ _
        _ ≤ ‖X‖ ^ m * ‖X - Y‖ := mul_le_mul_of_nonneg_right (matrix_norm_pow_le X m) (norm_nonneg _)
        _ ≤ R ^ m * ‖X - Y‖ := mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hX m) (norm_nonneg _)
    have h2 : ‖(X ^ m - Y ^ m) * Y‖ ≤ (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by
      calc ‖(X ^ m - Y ^ m) * Y‖ ≤ ‖X ^ m - Y ^ m‖ * ‖Y‖ := norm_mul_le _ _
        _ ≤ ((m : ℝ) * R ^ m * ‖X - Y‖) * R :=
            mul_le_mul (norm_pow_sub_pow_le hX hY hR m) hY (norm_nonneg _) (by positivity)
        _ = (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by rw [pow_succ]; ring
    have hRm : R ^ m ≤ R ^ (m + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg (by linarith : 0 ≤ R) m]
    calc ‖X ^ m * (X - Y) + (X ^ m - Y ^ m) * Y‖
        ≤ ‖X ^ m * (X - Y)‖ + ‖(X ^ m - Y ^ m) * Y‖ := norm_add_le _ _
      _ ≤ R ^ m * ‖X - Y‖ + (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := add_le_add h1 h2
      _ ≤ R ^ (m + 1) * ‖X - Y‖ + (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by
          nlinarith [norm_nonneg (X - Y)]
      _ = ((m + 1 : ℕ) : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by push_cast; ring

set_option backward.isDefEq.respectTransparency false in
/-- **3-Term Finite-Dimensional Lie–Trotter Product Formula**:
for any three real matrices `A, B, C : Matrix n n ℝ`,
`(exp ((1/M) • A) * exp ((1/M) • B) * exp ((1/M) • C)) ^ M → exp (A + B + C)` as `M → ∞`. -/
theorem tendsto_trotter3 (A B C : Matrix n n ℝ) :
    Tendsto
      (fun M : ℕ =>
        (NormedSpace.exp (((M : ℝ)⁻¹) • A) *
         NormedSpace.exp (((M : ℝ)⁻¹) • B) *
         NormedSpace.exp (((M : ℝ)⁻¹) • C)) ^ M)
      atTop (nhds (NormedSpace.exp (A + B + C))) := by
  set S : ℝ := ‖A‖ + ‖B‖ + ‖C‖ + 1
  have hS_pos : 0 < S := by dsimp [S]; linarith [norm_nonneg A, norm_nonneg B, norm_nonneg C]
  have hA_le : ‖A‖ ≤ S := by dsimp [S]; linarith [norm_nonneg B, norm_nonneg C]
  have hB_le : ‖B‖ ≤ S := by dsimp [S]; linarith [norm_nonneg A, norm_nonneg C]
  have hC_le : ‖C‖ ≤ S := by dsimp [S]; linarith [norm_nonneg A, norm_nonneg B]
  have hABC_le : ‖A + B + C‖ ≤ S := by
    have h1 := norm_add_le (A + B) C
    have h2 := norm_add_le A B
    dsimp [S]; linarith
  -- Global Lipschitz constant K for ‖X_M - Y_M‖ ≤ K / M^2 when M ≥ 1
  set K : ℝ := 16 * S ^ 2 * Real.exp (3 * S)
  have hbound : ∀ M : ℕ, 1 ≤ M →
      ‖(NormedSpace.exp (((M : ℝ)⁻¹) • A) *
        NormedSpace.exp (((M : ℝ)⁻¹) • B) *
        NormedSpace.exp (((M : ℝ)⁻¹) • C)) ^ M -
        NormedSpace.exp (A + B + C)‖ ≤
      (K * Real.exp S) / (M : ℝ) := by
    intro M hM
    set t : ℝ := (M : ℝ)⁻¹
    have ht_pos : 0 < t := by dsimp [t]; positivity
    have ht_le1 : t ≤ 1 := by
      dsimp [t]
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      exact inv_le_one_of_one_le₀ hM1
    set EA := NormedSpace.exp (t • A)
    set EB := NormedSpace.exp (t • B)
    set EC := NormedSpace.exp (t • C)
    set X := EA * EB * EC
    set Y := NormedSpace.exp (t • (A + B + C))
    have hYM : Y ^ M = NormedSpace.exp (A + B + C) := by
      dsimp [Y]
      rw [← exp_nsmul_eq_pow, smul_smul]
      have hMt : (M : ℝ) * t = 1 := mul_inv_cancel₀ (by positivity)
      rw [hMt, one_smul]
    rw [← hYM]
    have hEA_n : ‖EA‖ ≤ Real.exp (t * S) := by
      refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left hA_le ht_pos.le
    have hEB_n : ‖EB‖ ≤ Real.exp (t * S) := by
      refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left hB_le ht_pos.le
    have hEC_n : ‖EC‖ ≤ Real.exp (t * S) := by
      refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left hC_le ht_pos.le
    have hX_n : ‖X‖ ≤ Real.exp (t * S) := by
      -- Tighter bound using ‖A‖ + ‖B‖ + ‖C‖ ≤ S
      have h1 : ‖EA‖ ≤ Real.exp (t * ‖A‖) := by
        refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      have h2 : ‖EB‖ ≤ Real.exp (t * ‖B‖) := by
        refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      have h3 : ‖EC‖ ≤ Real.exp (t * ‖C‖) := by
        refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      calc ‖EA * EB * EC‖ ≤ ‖EA * EB‖ * ‖EC‖ := norm_mul_le _ _
        _ ≤ ‖EA‖ * ‖EB‖ * ‖EC‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ Real.exp (t * ‖A‖) * Real.exp (t * ‖B‖) * Real.exp (t * ‖C‖) := by
            exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le)
              h3 (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        _ = Real.exp (t * (‖A‖ + ‖B‖ + ‖C‖)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (t * S) := Real.exp_le_exp.mpr (by dsimp [S]; nlinarith)
    have hY_n : ‖Y‖ ≤ Real.exp (t * S) := by
      refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left hABC_le ht_pos.le
    -- Second-order Taylor errors rA, rB, rC, rY
    set rA := EA - 1 - t • A
    set rB := EB - 1 - t • B
    set rC := EC - 1 - t • C
    set rY := Y - 1 - t • (A + B + C)
    have hrem : ∀ (P : Matrix n n ℝ), ‖P‖ ≤ S →
        ‖NormedSpace.exp (t • P) - 1 - t • P‖ ≤ t ^ 2 * S ^ 2 * Real.exp S := fun P hP => by
      have h1 := norm_exp_sub_one_sub_le (t • P)
      have hn : ‖t • P‖ ≤ t * S := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact mul_le_mul_of_nonneg_left hP ht_pos.le
      have he : Real.exp ‖t • P‖ ≤ Real.exp S :=
        Real.exp_le_exp.mpr (hn.trans (by nlinarith))
      have hsq : ‖t • P‖ ^ 2 ≤ (t * S) ^ 2 := by nlinarith [norm_nonneg (t • P)]
      calc ‖NormedSpace.exp (t • P) - 1 - t • P‖
          ≤ ‖t • P‖ ^ 2 * Real.exp ‖t • P‖ := h1
        _ ≤ (t * S) ^ 2 * Real.exp S :=
            mul_le_mul hsq he (Real.exp_pos _).le (sq_nonneg _)
        _ = t ^ 2 * S ^ 2 * Real.exp S := by ring
    have hrA : ‖rA‖ ≤ t ^ 2 * S ^ 2 * Real.exp S := hrem A hA_le
    have hrB : ‖rB‖ ≤ t ^ 2 * S ^ 2 * Real.exp S := hrem B hB_le
    have hrC : ‖rC‖ ≤ t ^ 2 * S ^ 2 * Real.exp S := hrem C hC_le
    have hrY : ‖rY‖ ≤ t ^ 2 * S ^ 2 * Real.exp S := hrem (A + B + C) hABC_le
    -- Expand X - (1 + t•(A+B+C)) = rA*EB*EC + (t•A)*(EB - 1)*EC + (t•A)*(EC - 1) + rB*EC + (t•B)*(EC - 1) + rC
    have hEA_eq : EA = 1 + t • A + rA := by dsimp [rA]; abel
    have hEB_eq : EB = 1 + t • B + rB := by dsimp [rB]; abel
    have hEC_eq : EC = 1 + t • C + rC := by dsimp [rC]; abel
    have hY_eq : Y = 1 + t • (A + B + C) + rY := by dsimp [rY]; abel
    have hdiff_id : X - Y =
        rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
        rB * EC + (t • B) * (EC - 1) + rC - rY := by
      dsimp [X]
      calc EA * EB * EC - Y
          = (1 + t • A + rA) * EB * EC - (1 + t • (A + B + C) + rY) := by rw [← hEA_eq, ← hY_eq]
        _ = rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
            (EB * EC - 1 - t • B - t • C) - rY := by
            simp only [add_mul, mul_add, one_mul, mul_one, mul_sub, sub_mul, smul_add]
            abel
        _ = rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
            rB * EC + (t • B) * (EC - 1) + rC - rY := by
            have hBC : EB * EC - 1 - t • B - t • C = rB * EC + (t • B) * (EC - 1) + rC := by
              calc EB * EC - 1 - t • B - t • C
                  = (1 + t • B + rB) * EC - 1 - t • B - t • C := by rw [← hEB_eq]
                _ = rB * EC + (t • B) * (EC - 1) + (EC - 1 - t • C) := by
                    simp only [add_mul, one_mul, mul_sub, mul_one]; abel
                _ = rB * EC + (t • B) * (EC - 1) + rC := by rfl
            rw [hBC]; abel
    -- First-order bound `‖exp(t•P) - 1‖ ≤ t * S * Real.exp S` directly from power series
    have hsub1_clean : ∀ (P : Matrix n n ℝ), ‖P‖ ≤ S →
        ‖NormedSpace.exp (t • P) - 1‖ ≤ t * S * Real.exp S := fun P hP => by
      have hhas : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (t • P) ^ k) (NormedSpace.exp (t • P)) := by
        have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (t • P)
        simpa [NormedSpace.expSeries_apply_eq] using h
      have hshift : HasSum (fun k : ℕ => (((k + 1).factorial : ℝ)⁻¹) • (t • P) ^ (k + 1))
          (NormedSpace.exp (t • P) - 1) := by
        have h1 := (hasSum_nat_add_iff' 1).mpr hhas
        simpa using h1
      have hsum_norm := hshift.summable.norm
      have hn : ‖t • P‖ ≤ t * S := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact mul_le_mul_of_nonneg_left hP ht_pos.le
      have hreal_has := (real_exp_hasSum S).mul_left (t * S)
      have hle : ‖NormedSpace.exp (t • P) - 1‖ ≤
          ∑' k : ℕ, ‖(((k + 1).factorial : ℝ)⁻¹) • (t • P) ^ (k + 1)‖ := by
        rw [← hshift.tsum_eq]; exact norm_tsum_le_tsum_norm hsum_norm
      refine hle.trans ?_
      rw [← hreal_has.tsum_eq]
      refine hsum_norm.tsum_le_tsum (fun k => ?_) hreal_has.summable
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hfact : (k.factorial : ℝ) ≤ ((k + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega : k ≤ k + 1)
      have hinv : (((k + 1).factorial : ℝ)⁻¹) ≤ (k.factorial : ℝ)⁻¹ := inv_anti₀ (by positivity) hfact
      have hpow : ‖(t • P) ^ (k + 1)‖ ≤ (t * S) * S ^ k := by
        calc ‖(t • P) ^ (k + 1)‖ ≤ ‖t • P‖ ^ (k + 1) := matrix_norm_pow_le _ _
          _ = ‖t • P‖ * ‖t • P‖ ^ k := by rw [pow_succ']
          _ ≤ (t * S) * S ^ k := mul_le_mul hn
                (pow_le_pow_left₀ (norm_nonneg _) (hn.trans (by nlinarith)) k)
                (pow_nonneg (norm_nonneg _) k) (by positivity)
      calc (((k + 1).factorial : ℝ)⁻¹) * ‖(t • P) ^ (k + 1)‖
          ≤ (k.factorial : ℝ)⁻¹ * ((t * S) * S ^ k) :=
            mul_le_mul hinv hpow (norm_nonneg _) (by positivity)
        _ = t * S * ((k.factorial : ℝ)⁻¹ * S ^ k) := by ring
    have hEB1 := hsub1_clean B hB_le
    have hEC1 := hsub1_clean C hC_le
    have heS : Real.exp (t * S) ≤ Real.exp S := Real.exp_le_exp.mpr (by nlinarith)
    have hEB_e : ‖EB‖ ≤ Real.exp S := hEB_n.trans heS
    have hEC_e : ‖EC‖ ≤ Real.exp S := hEC_n.trans heS
    have htA : ‖t • A‖ ≤ t * S := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]; exact mul_le_mul_of_nonneg_left hA_le ht_pos.le
    have htB : ‖t • B‖ ≤ t * S := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]; exact mul_le_mul_of_nonneg_left hB_le ht_pos.le
    have hE3_ge1 : Real.exp S ≤ Real.exp (3 * S) := Real.exp_le_exp.mpr (by linarith)
    have hE2_le : Real.exp S * Real.exp S ≤ Real.exp (3 * S) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hE3_eq : Real.exp S * Real.exp S * Real.exp S = Real.exp (3 * S) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hXY : ‖X - Y‖ ≤ K * t ^ 2 := by
      rw [hdiff_id]
      have t1 : ‖rA * EB * EC‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := by
        calc ‖rA * EB * EC‖ ≤ ‖rA‖ * ‖EB‖ * ‖EC‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (t ^ 2 * S ^ 2 * Real.exp S) * Real.exp S * Real.exp S :=
              mul_le_mul (mul_le_mul hrA hEB_e (norm_nonneg _) (by positivity)) hEC_e (norm_nonneg _) (by positivity)
          _ = t ^ 2 * S ^ 2 * Real.exp (3 * S) := by rw [← hE3_eq]; ring
      have t2 : ‖(t • A) * (EB - 1) * EC‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := by
        calc ‖(t • A) * (EB - 1) * EC‖ ≤ ‖t • A‖ * ‖EB - 1‖ * ‖EC‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (t * S) * (t * S * Real.exp S) * Real.exp S :=
              mul_le_mul (mul_le_mul htA hEB1 (norm_nonneg _) (by positivity)) hEC_e (norm_nonneg _) (by positivity)
          _ = t ^ 2 * S ^ 2 * (Real.exp S * Real.exp S) := by ring
          _ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := mul_le_mul_of_nonneg_left hE2_le (by positivity)
      have t3 : ‖(t • A) * (EC - 1)‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := by
        calc ‖(t • A) * (EC - 1)‖ ≤ ‖t • A‖ * ‖EC - 1‖ := norm_mul_le _ _
          _ ≤ (t * S) * (t * S * Real.exp S) := mul_le_mul htA hEC1 (norm_nonneg _) (by positivity)
          _ = t ^ 2 * S ^ 2 * Real.exp S := by ring
          _ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := mul_le_mul_of_nonneg_left hE3_ge1 (by positivity)
      have t4 : ‖rB * EC‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := by
        calc ‖rB * EC‖ ≤ ‖rB‖ * ‖EC‖ := norm_mul_le _ _
          _ ≤ (t ^ 2 * S ^ 2 * Real.exp S) * Real.exp S := mul_le_mul hrB hEC_e (norm_nonneg _) (by positivity)
          _ = t ^ 2 * S ^ 2 * (Real.exp S * Real.exp S) := by ring
          _ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := mul_le_mul_of_nonneg_left hE2_le (by positivity)
      have t5 : ‖(t • B) * (EC - 1)‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := by
        calc ‖(t • B) * (EC - 1)‖ ≤ ‖t • B‖ * ‖EC - 1‖ := norm_mul_le _ _
          _ ≤ (t * S) * (t * S * Real.exp S) := mul_le_mul htB hEC1 (norm_nonneg _) (by positivity)
          _ = t ^ 2 * S ^ 2 * Real.exp S := by ring
          _ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := mul_le_mul_of_nonneg_left hE3_ge1 (by positivity)
      have t6 : ‖rC‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) :=
        hrC.trans (mul_le_mul_of_nonneg_left hE3_ge1 (by positivity))
      have t7 : ‖rY‖ ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) :=
        hrY.trans (mul_le_mul_of_nonneg_left hE3_ge1 (by positivity))
      have htri : ‖rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
          rB * EC + (t • B) * (EC - 1) + rC - rY‖ ≤
          ‖rA * EB * EC‖ + ‖(t • A) * (EB - 1) * EC‖ + ‖(t • A) * (EC - 1)‖ +
          ‖rB * EC‖ + ‖(t • B) * (EC - 1)‖ + ‖rC‖ + ‖rY‖ := by
        have h1 := norm_sub_le (rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
          rB * EC + (t • B) * (EC - 1) + rC) rY
        have h2 := norm_add_le (rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
          rB * EC + (t • B) * (EC - 1)) rC
        have h3 := norm_add_le (rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1) +
          rB * EC) ((t • B) * (EC - 1))
        have h4 := norm_add_le (rA * EB * EC + (t • A) * (EB - 1) * EC + (t • A) * (EC - 1)) (rB * EC)
        have h5 := norm_add_le (rA * EB * EC + (t • A) * (EB - 1) * EC) ((t • A) * (EC - 1))
        have h6 := norm_add_le (rA * EB * EC) ((t • A) * (EB - 1) * EC)
        linarith
      have h7sum : 7 * (t ^ 2 * S ^ 2 * Real.exp (3 * S)) ≤ K * t ^ 2 := by
        have hnn : 0 ≤ t ^ 2 * S ^ 2 * Real.exp (3 * S) := by positivity
        have heq : K * t ^ 2 = 16 * (t ^ 2 * S ^ 2 * Real.exp (3 * S)) := by dsimp [K]; ring
        linarith only [hnn, heq]
      linarith only [htri, t1, t2, t3, t4, t5, t6, t7, h7sum]
    have hR1 : (1 : ℝ) ≤ Real.exp (t * S) := Real.one_le_exp (by positivity)
    have htele := norm_pow_sub_pow_le hX_n hY_n hR1 M
    have hRM : (Real.exp (t * S)) ^ M = Real.exp S := by
      rw [← Real.exp_nat_mul]
      congr 1; dsimp [t]; field_simp [(by positivity : (M : ℝ) ≠ 0)]
    rw [hRM] at htele
    calc ‖X ^ M - Y ^ M‖ ≤ (M : ℝ) * Real.exp S * ‖X - Y‖ := htele
      _ ≤ (M : ℝ) * Real.exp S * (K * t ^ 2) :=
          mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = (K * Real.exp S) / (M : ℝ) := by
          dsimp [t]; field_simp [(by positivity : (M : ℝ) ≠ 0)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((K * Real.exp S) / ε)
  refine ⟨max 1 N, fun M hM => ?_⟩
  rw [dist_eq_norm]
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMN : N ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlt : (K * Real.exp S) / (M : ℝ) < ε := by
    rw [div_lt_iff₀ hMpos]
    have h1 : (K * Real.exp S) / ε < (M : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hMN)
    have h2 := (div_lt_iff₀ hε).mp h1
    linarith
  exact lt_of_le_of_lt (hbound M hM1) hlt

set_option backward.isDefEq.respectTransparency false in
/-- **Involutive Matrix Exponential**: if `M * M = 1`, then
`exp (a • M) = Real.cosh a • 1 + Real.sinh a • M`. -/
theorem exp_involutive {M : Matrix n n ℝ} (hM : M * M = 1) (a : ℝ) :
    NormedSpace.exp (a • M) = Real.cosh a • (1 : Matrix n n ℝ) + Real.sinh a • M := by
  have hpow : ∀ k : ℕ, M ^ k = if Even k then (1 : Matrix n n ℝ) else M := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      by_cases hk : Even k
      · have hodd : ¬ Even (k + 1) := by rcases hk with ⟨r, rfl⟩; intro ⟨s, hs⟩; omega
        simp [hk, hodd]
      · have hev : Even (k + 1) := by
          rcases Nat.even_or_odd k with h | ⟨r, rfl⟩
          · exact absurd h hk
          · exact ⟨r + 1, by omega⟩
        simp [hk, hev, hM]
  have hhas : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹ * a ^ k) • M ^ k) (NormedSpace.exp (a • M)) := by
    have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (a • M)
    simpa [NormedSpace.expSeries_apply_eq, smul_pow, smul_smul] using h
  have hp := real_exp_hasSum a
  have hm := real_exp_hasSum (-a)
  have heven_full : HasSum (fun k : ℕ => if Even k then (k.factorial : ℝ)⁻¹ * a ^ k else 0) (Real.cosh a) := by
    rw [Real.cosh_eq]
    have havg := (hp.add hm).div_const 2
    refine havg.congr_fun fun k => ?_
    by_cases hk : Even k
    · simp [hk, hk.neg_pow]
    · have hodd : Odd k := Nat.not_even_iff_odd.mp hk
      simp [hk, hodd.neg_pow]
  have hodd_full : HasSum (fun k : ℕ => if Even k then (0 : ℝ) else (k.factorial : ℝ)⁻¹ * a ^ k) (Real.sinh a) := by
    rw [Real.sinh_eq]
    have havg := (hp.sub hm).div_const 2
    refine havg.congr_fun fun k => ?_
    by_cases hk : Even k
    · simp [hk, hk.neg_pow]
    · have hodd : Odd k := Nat.not_even_iff_odd.mp hk
      simp [hk, hodd.neg_pow]
  have h1 : HasSum (fun k : ℕ => (if Even k then (k.factorial : ℝ)⁻¹ * a ^ k else 0) • (1 : Matrix n n ℝ))
      (Real.cosh a • (1 : Matrix n n ℝ)) := heven_full.smul_const (1 : Matrix n n ℝ)
  have h2 : HasSum (fun k : ℕ => (if Even k then (0 : ℝ) else (k.factorial : ℝ)⁻¹ * a ^ k) • M)
      (Real.sinh a • M) := hodd_full.smul_const M
  have hsum := h1.add h2
  have hterm : ∀ k : ℕ,
      (if Even k then (k.factorial : ℝ)⁻¹ * a ^ k else 0) • (1 : Matrix n n ℝ) +
      (if Even k then (0 : ℝ) else (k.factorial : ℝ)⁻¹ * a ^ k) • M =
      ((k.factorial : ℝ)⁻¹ * a ^ k) • M ^ k := fun k => by
    rw [hpow k]; split_ifs <;> simp
  simp_rw [hterm] at hsum
  exact hhas.unique hsum

set_option backward.isDefEq.respectTransparency false in
/-- **Spectral Trace Identity**: `Matrix.trace (exp ((-b) • H)) = matZ H hH b`. -/
theorem trace_exp_eq_matZ (H : Matrix n n ℝ) (hH : H.IsHermitian) (b : ℝ) :
    Matrix.trace (NormedSpace.exp ((-b) • H)) = matZ H hH b := by
  have hspec := hH.spectral_theorem
  let U : (Matrix n n ℝ)ˣ := Unitary.toUnits hH.eigenvectorUnitary
  have hH_eq : H = (U : Matrix n n ℝ) * Matrix.diagonal hH.eigenvalues * ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hspec
  have hscale : (-b) • H =
      (U : Matrix n n ℝ) * Matrix.diagonal (fun k => -b * hH.eigenvalues k) *
      ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    have hsd : (-b) • Matrix.diagonal hH.eigenvalues =
        Matrix.diagonal (fun k => -b * hH.eigenvalues k) := by
      ext i j; by_cases h : i = j <;> simp [h]
    conv_lhs => rw [hH_eq]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hsd]
  rw [hscale, Matrix.exp_units_conj, Matrix.exp_diagonal, Matrix.trace_mul_cycle]
  have hUinv : ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := by
    exact_mod_cast U.inv_mul
  rw [hUinv, Matrix.one_mul, Matrix.trace_diagonal]
  unfold matZ
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpi : ∀ (f : n → ℝ), NormedSpace.exp f k = Real.exp (f k) := fun f => by
    rw [Real.exp_eq_exp_ℝ]
    have heval := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) f).map
      (Pi.evalAddMonoidHom (fun _ : n => ℝ) k) (continuous_apply k)
    have hcomp : ((Pi.evalAddMonoidHom (fun _ : n => ℝ) k) ∘
        fun m => NormedSpace.expSeries ℝ (n → ℝ) m fun _ => f) =
        fun m => NormedSpace.expSeries ℝ ℝ m fun _ => f k := by
      funext m
      change (NormedSpace.expSeries ℝ (n → ℝ) m fun _ => f) k =
        NormedSpace.expSeries ℝ ℝ m fun _ => f k
      rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq]
      simp
    rw [hcomp] at heval
    exact (heval.unique (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (f k)))
  exact hpi (fun j => -b * hH.eigenvalues j)

end MatrixExp

/-! ## Closed Spatial Inequalities from Finite-Dimensional PSD Transfer Pairs -/

section PSDPair

/-- Every eigenvalue of a real Gram matrix `V * Vᵀ` is nonnegative! -/
lemma gram_isHermitian {n : Type*} [Fintype n] [DecidableEq n] (V : Matrix n n ℝ) :
    (V * Vᵀ).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul]

lemma gram_eigenvalues_nonneg {n : Type*} [Fintype n] [DecidableEq n] (V : Matrix n n ℝ) (k : n) :
    0 ≤ (gram_isHermitian V).eigenvalues k := by
  let hA := gram_isHermitian V
  let u : n → ℝ := (hA.eigenvectorBasis k).ofLp
  have hu_unit : dotProduct u u = 1 := by
    have h1 := hA.eigenvectorBasis.orthonormal.1 k
    have hsq : ‖hA.eigenvectorBasis k‖ ^ 2 = 1 := by rw [h1, one_pow]
    rw [EuclideanSpace.norm_sq_eq] at hsq
    simpa [u, dotProduct, Real.norm_eq_abs, sq] using hsq
  have heig : hA.eigenvalues k = dotProduct u ((V * Vᵀ).mulVec u) := by
    rw [hA.mulVec_eigenvectorBasis k, dotProduct_smul, smul_eq_mul, hu_unit, mul_one]
  rw [heig, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hvec : u ᵥ* V = Vᵀ.mulVec u := by
    ext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvec]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- Trace of `m`-th power of a real symmetric matrix equals sum of `m`-th powers of its eigenvalues. -/
lemma trace_pow_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (m : ℕ) :
    Matrix.trace (A ^ m) = ∑ k : n, (hA.eigenvalues k) ^ m := by
  have hspec := hA.spectral_theorem
  let U : (Matrix n n ℝ)ˣ := Unitary.toUnits hA.eigenvectorUnitary
  have hA_eq : A = (U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues * ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hspec
  have hpow : ∀ r : ℕ, A ^ r =
      (U : Matrix n n ℝ) * Matrix.diagonal (fun k => (hA.eigenvalues k) ^ r) *
      ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    intro r
    induction r with
    | zero =>
      simp only [pow_zero, Matrix.diagonal_one, Matrix.mul_one]
      exact (show (U : Matrix n n ℝ) * ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) = 1 from by
        exact_mod_cast U.mul_inv).symm
    | succ r ih =>
      have hUinv : ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := by
        exact_mod_cast U.inv_mul
      calc A ^ (r + 1) = A ^ r * A := pow_succ A r
        _ = ((U : Matrix n n ℝ) * Matrix.diagonal (fun k => hA.eigenvalues k ^ r) *
              ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ)) *
            ((U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues *
              ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ)) := congrArg₂ (· * ·) ih hA_eq
        _ = (U : Matrix n n ℝ) * Matrix.diagonal (fun k => hA.eigenvalues k ^ r) *
              (((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) * (U : Matrix n n ℝ)) *
              Matrix.diagonal hA.eigenvalues * ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
            simp only [Matrix.mul_assoc]
        _ = (U : Matrix n n ℝ) * (Matrix.diagonal (fun k => hA.eigenvalues k ^ r) *
              Matrix.diagonal hA.eigenvalues) * ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
            rw [hUinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by
            have hdiag : Matrix.diagonal (fun k => hA.eigenvalues k ^ r) *
                Matrix.diagonal hA.eigenvalues =
                Matrix.diagonal (fun k => hA.eigenvalues k ^ (r + 1)) := by
              rw [Matrix.diagonal_mul_diagonal]; rfl
            rw [hdiag]
  rw [hpow m, Matrix.trace_mul_cycle]
  have hUinv : ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := by
    exact_mod_cast U.inv_mul
  rw [hUinv, Matrix.one_mul, Matrix.trace_diagonal]

/-- All 6 closed spatial inequalities for any finite-dimensional PSD pair `A₀ = V₀ V₀ᵀ`,
`A₁ = V₁ V₁ᵀ` with `Zp(m) = Tr(A₀^m) + Tr(A₁^m)` and `Zm(m) = Tr(A₀^m) - Tr(A₁^m)`. -/
theorem psd_pair_spatial_ineqs {n : Type*} [Fintype n] [DecidableEq n]
    (V₀ V₁ : Matrix n n ℝ) :
    let A₀ := V₀ * V₀ᵀ
    let A₁ := V₁ * V₁ᵀ
    let Zp : ℕ → ℝ := fun m => Matrix.trace (A₀ ^ m) + Matrix.trace (A₁ ^ m)
    let Zm : ℕ → ℝ := fun m => Matrix.trace (A₀ ^ m) - Matrix.trace (A₁ ^ m)
    (∀ m, 0 ≤ Zp m) ∧
    (∀ m, Zm m ≤ Zp m) ∧
    (∀ m, Zp (2 * m) ≤ Zp m ^ 2) ∧
    (∀ m, 2 * Zp (2 * m) ≤ Zp m ^ 2 + Zm m ^ 2) ∧
    (∀ m, 0 < Zp m → 0 < Zp (2 * m) →
      1 - Zp (4 * m) / Zp (2 * m) ^ 2 ≤ purityUpdate (1 - Zp (2 * m) / Zp m ^ 2)) ∧
    (∀ m₁ m₂, 1 ≤ m₁ → m₁ ≤ m₂ → 0 < Zp m₁ → 0 < Zp m₂ →
      Zp (2 * m₁) / Zp m₁ ^ 2 ≤ Zp (2 * m₂) / Zp m₂ ^ 2) ∧
    (∀ m₁ m₂, 1 ≤ m₁ → m₁ ≤ m₂ → 0 < Zp m₁ →
      Zp m₂ ≤ Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) := by
  intro A₀ A₁ Zp Zm
  let hA₀ := gram_isHermitian V₀
  let hA₁ := gram_isHermitian V₁
  let lam : n ⊕ n → ℝ := Sum.elim hA₀.eigenvalues hA₁.eigenvalues
  have hlam_nn : ∀ x : n ⊕ n, 0 ≤ lam x := fun x => by
    cases x with
    | inl k => exact gram_eigenvalues_nonneg V₀ k
    | inr k => exact gram_eigenvalues_nonneg V₁ k
  have hZp_eq : ∀ m : ℕ, Zp m = ∑ x : n ⊕ n, lam x ^ m := fun m => by
    dsimp [Zp, lam]
    rw [trace_pow_eq_sum_eigenvalues A₀ hA₀ m, trace_pow_eq_sum_eigenvalues A₁ hA₁ m,
      Fintype.sum_sum_type]
    rfl
  have htr0_nn : ∀ m : ℕ, 0 ≤ Matrix.trace (A₀ ^ m) := fun m => by
    rw [trace_pow_eq_sum_eigenvalues A₀ hA₀ m]
    exact Finset.sum_nonneg fun k _ => pow_nonneg (gram_eigenvalues_nonneg V₀ k) m
  have htr1_nn : ∀ m : ℕ, 0 ≤ Matrix.trace (A₁ ^ m) := fun m => by
    rw [trace_pow_eq_sum_eigenvalues A₁ hA₁ m]
    exact Finset.sum_nonneg fun k _ => pow_nonneg (gram_eigenvalues_nonneg V₁ k) m
  have hsq_le : ∀ (f : n → ℝ), (∀ k, 0 ≤ f k) → ∀ m : ℕ,
      ∑ k : n, f k ^ (2 * m) ≤ (∑ k : n, f k ^ m) ^ 2 := fun f hf m => by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun k => f k ^ m)
      (fun k _ => pow_nonneg (hf k) m)
    simpa [← pow_mul, mul_comm] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; rw [hZp_eq m]; exact Finset.sum_nonneg fun x _ => pow_nonneg (hlam_nn x) m
  · intro m; dsimp [Zp, Zm]; linarith [htr1_nn m]
  · intro m
    rw [hZp_eq (2 * m), hZp_eq m]
    have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun x : n ⊕ n => lam x ^ m)
      (fun x _ => pow_nonneg (hlam_nn x) m)
    simpa [← pow_mul, mul_comm] using h
  · intro m
    dsimp [Zp, Zm]
    have h0 : Matrix.trace (A₀ ^ (2 * m)) ≤ Matrix.trace (A₀ ^ m) ^ 2 := by
      rw [trace_pow_eq_sum_eigenvalues A₀ hA₀, trace_pow_eq_sum_eigenvalues A₀ hA₀]
      exact hsq_le hA₀.eigenvalues (gram_eigenvalues_nonneg V₀) m
    have h1 : Matrix.trace (A₁ ^ (2 * m)) ≤ Matrix.trace (A₁ ^ m) ^ 2 := by
      rw [trace_pow_eq_sum_eigenvalues A₁ hA₁, trace_pow_eq_sum_eigenvalues A₁ hA₁]
      exact hsq_le hA₁.eigenvalues (gram_eigenvalues_nonneg V₁) m
    nlinarith
  · intro m hZm hZ2m
    let p : n ⊕ n → ℝ := fun x => lam x ^ m / Zp m
    have hp_nn : ∀ x ∈ (Finset.univ : Finset (n ⊕ n)), 0 ≤ p x := fun x _ =>
      div_nonneg (pow_nonneg (hlam_nn x) m) hZm.le
    have hp_sum : ∑ x : n ⊕ n, p x = 1 := by
      dsimp [p]; rw [← Finset.sum_div, ← hZp_eq m, div_self hZm.ne']
    have hP2 : ∑ x : n ⊕ n, p x ^ 2 = Zp (2 * m) / Zp m ^ 2 := by
      dsimp [p]; simp_rw [div_pow, ← Finset.sum_div, ← pow_mul, mul_comm m 2, ← hZp_eq (2 * m)]
    have hP4 : ∑ x : n ⊕ n, p x ^ 4 = Zp (4 * m) / Zp m ^ 4 := by
      dsimp [p]; simp_rw [div_pow, ← Finset.sum_div, ← pow_mul, mul_comm m 4, ← hZp_eq (4 * m)]
    have hbd := (finset_purity_square_bound Finset.univ p hp_nn hp_sum).2.2
    have hrat : (∑ x : n ⊕ n, p x ^ 4) / (∑ x : n ⊕ n, p x ^ 2) ^ 2 = Zp (4 * m) / Zp (2 * m) ^ 2 := by
      rw [hP2, hP4]; field_simp [hZm.ne', hZ2m.ne']
    rwa [hrat, hP2] at hbd
  · intro m₁ m₂ hm1 hm12 hZ1 hZ2
    let p : n ⊕ n → ℝ := fun x => lam x ^ m₁ / Zp m₁
    have hp_nn : ∀ x ∈ (Finset.univ : Finset (n ⊕ n)), 0 ≤ p x := fun x _ =>
      div_nonneg (pow_nonneg (hlam_nn x) m₁) hZ1.le
    have hr : (1 : ℝ) ≤ (m₂ : ℝ) / (m₁ : ℝ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (m₁ : ℝ))]
      have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm12
      linarith
    have hmono := finset_purity_rpow_mono Finset.univ p hp_nn hr
    have hpow_r : ∀ x : n ⊕ n, p x ^ ((m₂ : ℝ) / (m₁ : ℝ)) =
        lam x ^ m₂ / Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ)) := fun x => by
      dsimp [p]
      rw [Real.div_rpow (pow_nonneg (hlam_nn x) m₁) hZ1.le, ← Real.rpow_natCast (lam x) m₁,
        ← Real.rpow_mul (hlam_nn x)]
      have hm1_ne : (m₁ : ℝ) ≠ 0 := by positivity
      rw [show (m₁ : ℝ) * ((m₂ : ℝ) / (m₁ : ℝ)) = (m₂ : ℝ) by field_simp [hm1_ne],
        Real.rpow_natCast]
    have hS1 : ∑ x : n ⊕ n, p x = 1 := by
      dsimp [p]; rw [← Finset.sum_div, ← hZp_eq m₁, div_self hZ1.ne']
    have hP2 : ∑ x : n ⊕ n, p x ^ 2 = Zp (2 * m₁) / Zp m₁ ^ 2 := by
      dsimp [p]; simp_rw [div_pow, ← Finset.sum_div, ← pow_mul, mul_comm m₁ 2, ← hZp_eq (2 * m₁)]
    have hSr : ∑ x : n ⊕ n, p x ^ ((m₂ : ℝ) / (m₁ : ℝ)) =
        Zp m₂ / Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ)) := by
      simp_rw [hpow_r, ← Finset.sum_div, ← hZp_eq m₂]
    have hSr2 : ∑ x : n ⊕ n, (p x ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 =
        Zp (2 * m₂) / (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 := by
      simp_rw [hpow_r, div_pow, ← Finset.sum_div, ← pow_mul, mul_comm m₂ 2, ← hZp_eq (2 * m₂)]
    rw [hS1, one_pow, one_mul, hP2, hSr, hSr2] at hmono
    have hden_pos : 0 < (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 :=
      pow_pos (Real.rpow_pos_of_pos hZ1 _) 2
    rw [le_div_iff₀ (pow_pos hZ2 2)]
    have hclear : (Zp m₂ ^ 2 / (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2) * (Zp (2 * m₁) / Zp m₁ ^ 2) ≤
        Zp (2 * m₂) / (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 := by
      simpa [div_pow] using hmono
    have hmul := mul_le_mul_of_nonneg_right hclear hden_pos.le
    have hL : (Zp m₂ ^ 2 / (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2) * (Zp (2 * m₁) / Zp m₁ ^ 2) *
        (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 = Zp (2 * m₁) / Zp m₁ ^ 2 * Zp m₂ ^ 2 := by
      field_simp [hden_pos.ne']
    have hR : Zp (2 * m₂) / (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 *
        (Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ))) ^ 2 = Zp (2 * m₂) := div_mul_cancel₀ _ hden_pos.ne'
    linarith
  · intro m₁ m₂ hm1 hm12 hZ1
    have hr : (1 : ℝ) ≤ (m₂ : ℝ) / (m₁ : ℝ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (m₁ : ℝ))]
      have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm12
      linarith
    have hle1 : ∀ x : n ⊕ n, lam x ^ m₁ / Zp m₁ ≤ 1 := fun x => by
      rw [div_le_one hZ1, hZp_eq m₁]
      exact Finset.single_le_sum (fun y _ => pow_nonneg (hlam_nn y) m₁) (Finset.mem_univ x)
    have hsum_le : ∑ x : n ⊕ n, (lam x ^ m₁ / Zp m₁) ^ ((m₂ : ℝ) / (m₁ : ℝ)) ≤ 1 := by
      calc ∑ x : n ⊕ n, (lam x ^ m₁ / Zp m₁) ^ ((m₂ : ℝ) / (m₁ : ℝ))
          ≤ ∑ x : n ⊕ n, (lam x ^ m₁ / Zp m₁) :=
            Finset.sum_le_sum fun x _ => Real.rpow_le_self_of_le_one
              (div_nonneg (pow_nonneg (hlam_nn x) m₁) hZ1.le) (hle1 x) hr
        _ = 1 := by rw [← Finset.sum_div, ← hZp_eq m₁, div_self hZ1.ne']
    have hrew : ∑ x : n ⊕ n, (lam x ^ m₁ / Zp m₁) ^ ((m₂ : ℝ) / (m₁ : ℝ)) =
        Zp m₂ / Zp m₁ ^ ((m₂ : ℝ) / (m₁ : ℝ)) := by
      rw [hZp_eq m₂, Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Real.div_rpow (pow_nonneg (hlam_nn x) m₁) hZ1.le, ← Real.rpow_natCast (lam x) m₁,
        ← Real.rpow_mul (hlam_nn x)]
      have hm1_ne : (m₁ : ℝ) ≠ 0 := by positivity
      rw [show (m₁ : ℝ) * ((m₂ : ℝ) / (m₁ : ℝ)) = (m₂ : ℝ) by field_simp [hm1_ne],
        Real.rpow_natCast]
    rw [hrew, div_le_one (Real.rpow_pos_of_pos hZ1 _)] at hsum_le
    exact hsum_le

end PSDPair

/-! ## Trotter-Limit Ising Multiplet System & Sorted-Spectrum Theorem -/

/-- Ising symmetry-twist system whose spatial transfer properties are certified by a sequence
of finite-dimensional PSD transfer pairs `(V₀^{(M)}, V₁^{(M)})` converging in trace to
`(Z_+(L, b), Z_-(L, b))` as `M → ∞`. Zero infinite-dimensional operators needed! -/
structure TrotterIsingSystem where
  d_pu : ℕ → ℕ
  d_pt : ℕ → ℕ
  d_mu : ℕ → ℕ
  d_mt : ℕ → ℕ
  d_pu_pos : ∀ L, Even L → 4 ≤ L → 0 < d_pu L
  d_mu_pos : ∀ L, Even L → 4 ≤ L → 0 < d_mu L
  E_pu : ∀ L, Fin (d_pu L) → ℝ
  E_pt : ∀ L, Fin (d_pt L) → ℝ
  E_mu : ∀ L, Fin (d_mu L) → ℝ
  E_mt : ∀ L, Fin (d_mt L) → ℝ
  seam_order_p : ∀ L, Even L → 4 ≤ L →
    ∀ kt : Fin (d_pt L), ∃ ku : Fin (d_pu L), E_pu L ku ≤ E_pt L kt
  seam_order_m : ∀ L, Even L → 4 ≤ L →
    ∀ kt : Fin (d_mt L), ∃ ku : Fin (d_mu L), E_mu L ku ≤ E_mt L kt
  /-- Finite-dimensional PSD Trotter transfer matrices at inverse temperature `b > 0`
  and Trotter depth `M` (`dim M`), converging to `(Z_+(2m, b), Z_-(2m, b))` as `M → ∞`. -/
  trotDim : ℕ → ℕ
  V0 : ℝ → ∀ M : ℕ, Matrix (Fin (trotDim M)) (Fin (trotDim M)) ℝ
  V1 : ℝ → ∀ M : ℕ, Matrix (Fin (trotDim M)) (Fin (trotDim M)) ℝ
  trot_tendsto_Zplus : ∀ m : ℕ, 2 ≤ m → ∀ b : ℝ, 0 < b →
    Tendsto (fun M : ℕ =>
      Matrix.trace ((V0 b M * (V0 b M)ᵀ) ^ m) + Matrix.trace ((V1 b M * (V1 b M)ᵀ) ^ m))
      atTop (nhds (
        (∑ k : Fin (d_pu (2 * m)), Real.exp (-b * E_pu (2 * m) k)) +
        (∑ k : Fin (d_pt (2 * m)), Real.exp (-b * E_pt (2 * m) k))))
  trot_tendsto_Zminus : ∀ m : ℕ, 2 ≤ m → ∀ b : ℝ, 0 < b →
    Tendsto (fun M : ℕ =>
      Matrix.trace ((V0 b M * (V0 b M)ᵀ) ^ m) - Matrix.trace ((V1 b M * (V1 b M)ᵀ) ^ m))
      atTop (nhds (
        (∑ k : Fin (d_mu (2 * m)), Real.exp (-b * E_mu (2 * m) k)) +
        (∑ k : Fin (d_mt (2 * m)), Real.exp (-b * E_mt (2 * m) k))))

namespace TrotterIsingSystem

noncomputable def Zplus (sys : TrotterIsingSystem) (L : ℕ) (b : ℝ) : ℝ :=
  (∑ k : Fin (sys.d_pu L), Real.exp (-b * sys.E_pu L k)) +
  (∑ k : Fin (sys.d_pt L), Real.exp (-b * sys.E_pt L k))

noncomputable def Zminus (sys : TrotterIsingSystem) (L : ℕ) (b : ℝ) : ℝ :=
  (∑ k : Fin (sys.d_mu L), Real.exp (-b * sys.E_mu L k)) +
  (∑ k : Fin (sys.d_mt L), Real.exp (-b * sys.E_mt L k))

noncomputable def Splus (sys : TrotterIsingSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Zplus (2 * L) b / (sys.Zplus L b) ^ 2

noncomputable def Tplus (sys : TrotterIsingSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Zplus L (2 * b) / (sys.Zplus L b) ^ 2

noncomputable def Tminus (sys : TrotterIsingSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Zminus L (2 * b) / (sys.Zminus L b) ^ 2

lemma Zplus_pos (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ} (hL : Even L) (h4 : 4 ≤ L) :
    0 < sys.Zplus L b := by
  unfold Zplus
  have h1 : 0 < ∑ k : Fin (sys.d_pu L), Real.exp (-b * sys.E_pu L k) := by
    haveI : Nonempty (Fin (sys.d_pu L)) := ⟨⟨0, sys.d_pu_pos L hL h4⟩⟩
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  have h2 : 0 ≤ ∑ k : Fin (sys.d_pt L), Real.exp (-b * sys.E_pt L k) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  linarith

lemma Zminus_pos (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ} (hL : Even L) (h4 : 4 ≤ L) :
    0 < sys.Zminus L b := by
  unfold Zminus
  have h1 : 0 < ∑ k : Fin (sys.d_mu L), Real.exp (-b * sys.E_mu L k) := by
    haveI : Nonempty (Fin (sys.d_mu L)) := ⟨⟨0, sys.d_mu_pos L hL h4⟩⟩
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  have h2 : 0 ≤ ∑ k : Fin (sys.d_mt L), Real.exp (-b * sys.E_mt L k) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  linarith

private lemma trot_Zp_tendsto (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) :
    Tendsto (fun M => Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (L / 2)) +
      Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (L / 2)))
      atTop (nhds (sys.Zplus L b)) := by
  rcases hL with ⟨k, rfl⟩
  have hk : k + k = 2 * k := by omega
  have hd : (2 * k) / 2 = k := by omega
  rw [hk, hd]
  exact sys.trot_tendsto_Zplus k (by omega) b hb

private lemma trot_Zm_tendsto (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) :
    Tendsto (fun M => Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (L / 2)) -
      Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (L / 2)))
      atTop (nhds (sys.Zminus L b)) := by
  rcases hL with ⟨k, rfl⟩
  have hk : k + k = 2 * k := by omega
  have hd : (2 * k) / 2 = k := by omega
  rw [hk, hd]
  exact sys.trot_tendsto_Zminus k (by omega) b hb

lemma Zminus_le_Zplus (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) :
    sys.Zminus L b ≤ sys.Zplus L b :=
  le_of_tendsto_of_tendsto (sys.trot_Zm_tendsto hL h4 hb) (sys.trot_Zp_tendsto hL h4 hb)
    (Eventually.of_forall fun M => (psd_pair_spatial_ineqs (sys.V0 b M) (sys.V1 b M)).2.1 (L / 2))

lemma Splus_le_one (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) :
    sys.Splus L b ≤ 1 := by
  unfold Splus
  rw [div_le_one (pow_pos (sys.Zplus_pos hL h4) 2)]
  have h2L : Even (2 * L) := even_two_mul L
  have hdiv : (2 * L) / 2 = 2 * (L / 2) := by rcases hL with ⟨k, rfl⟩; omega
  have htL := sys.trot_Zp_tendsto hL h4 hb
  have ht2L := sys.trot_Zp_tendsto h2L (by omega) hb
  rw [hdiv] at ht2L
  exact le_of_tendsto_of_tendsto ht2L (htL.pow 2)
    (Eventually.of_forall fun M => (psd_pair_spatial_ineqs (sys.V0 b M) (sys.V1 b M)).2.2.1 (L / 2))

lemma two_mul_Zplus_double_le (sys : TrotterIsingSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) :
    2 * sys.Zplus (2 * L) b ≤ sys.Zplus L b ^ 2 + sys.Zminus L b ^ 2 := by
  have h2L : Even (2 * L) := even_two_mul L
  have hdiv : (2 * L) / 2 = 2 * (L / 2) := by rcases hL with ⟨k, rfl⟩; omega
  have htL := sys.trot_Zp_tendsto hL h4 hb
  have htLm := sys.trot_Zm_tendsto hL h4 hb
  have ht2L := sys.trot_Zp_tendsto h2L (by omega) hb
  rw [hdiv] at ht2L
  exact le_of_tendsto_of_tendsto (ht2L.const_mul 2) ((htL.pow 2).add (htLm.pow 2))
    (Eventually.of_forall fun M => (psd_pair_spatial_ineqs (sys.V0 b M) (sys.V1 b M)).2.2.2.1 (L / 2))

lemma Zplus_rpow_upper (sys : TrotterIsingSystem) {n L : ℕ} {b : ℝ}
    (hn : Even n) (hL : Even L) (h4 : 4 ≤ n) (hnL : n ≤ L) (hb : 0 < b) :
    sys.Zplus L b ≤ sys.Zplus n b ^ ((L : ℝ) / (n : ℝ)) := by
  have hdiv_ratio : ((L / 2 : ℕ) : ℝ) / ((n / 2 : ℕ) : ℝ) = (L : ℝ) / (n : ℝ) := by
    rcases hn with ⟨kn, rfl⟩; rcases hL with ⟨kL, rfl⟩
    have hkn2 : (kn + kn) / 2 = kn := by omega
    have hkL2 : (kL + kL) / 2 = kL := by omega
    simp only [hkn2, hkL2, Nat.cast_add]
    have hkn : (kn : ℝ) ≠ 0 := by exact_mod_cast (by omega : kn ≠ 0)
    field_simp [hkn]
  have ht_n := sys.trot_Zp_tendsto hn h4 hb
  have ht_L := sys.trot_Zp_tendsto hL (le_trans h4 hnL) hb
  have hpos_ev : ∀ᶠ M in atTop,
      0 < Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (n / 2)) +
          Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (n / 2)) :=
    ht_n.eventually (lt_mem_nhds (sys.Zplus_pos hn h4))
  have hrpow_tend : Tendsto (fun M =>
      (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (n / 2)) +
       Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (n / 2))) ^ ((L : ℝ) / (n : ℝ)))
      atTop (nhds (sys.Zplus n b ^ ((L : ℝ) / (n : ℝ)))) :=
    ht_n.rpow_const (Or.inl (sys.Zplus_pos hn h4).ne')
  refine le_of_tendsto_of_tendsto ht_L hrpow_tend ?_
  filter_upwards [hpos_ev] with M hMpos
  have hbd := (psd_pair_spatial_ineqs (sys.V0 b M) (sys.V1 b M)).2.2.2.2.2.2
    (n / 2) (L / 2) (by omega) (by omega) hMpos
  rwa [hdiv_ratio] at hbd

lemma Splus_mono_even (sys : TrotterIsingSystem) {n L : ℕ} {b : ℝ}
    (hn : Even n) (hL : Even L) (h4 : 4 ≤ n) (hnL : n ≤ L) (hb : 0 < b) :
    sys.Splus n b ≤ sys.Splus L b := by
  have ht_n := sys.trot_Zp_tendsto hn h4 hb
  have ht_2n := sys.trot_Zp_tendsto (even_two_mul n) (by omega) hb
  have ht_L := sys.trot_Zp_tendsto hL (le_trans h4 hnL) hb
  have ht_2L := sys.trot_Zp_tendsto (even_two_mul L) (by omega) hb
  have hdn : (2 * n) / 2 = 2 * (n / 2) := by rcases hn with ⟨k, rfl⟩; omega
  have hdL : (2 * L) / 2 = 2 * (L / 2) := by rcases hL with ⟨k, rfl⟩; omega
  rw [hdn] at ht_2n; rw [hdL] at ht_2L
  have hpos_n := ht_n.eventually (lt_mem_nhds (sys.Zplus_pos hn h4))
  have hpos_L := ht_L.eventually (lt_mem_nhds (sys.Zplus_pos hL (le_trans h4 hnL)))
  have hSn : Tendsto (fun M =>
      (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (2 * (n / 2))) +
       Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (2 * (n / 2)))) /
      (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (n / 2)) +
       Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (n / 2))) ^ 2)
      atTop (nhds (sys.Splus n b)) :=
    ht_2n.div (ht_n.pow 2) (pow_pos (sys.Zplus_pos hn h4) 2).ne'
  have hSL : Tendsto (fun M =>
      (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (2 * (L / 2))) +
       Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (2 * (L / 2)))) /
      (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (L / 2)) +
       Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (L / 2))) ^ 2)
      atTop (nhds (sys.Splus L b)) :=
    ht_2L.div (ht_L.pow 2) (pow_pos (sys.Zplus_pos hL (le_trans h4 hnL)) 2).ne'
  refine le_of_tendsto_of_tendsto hSn hSL ?_
  filter_upwards [hpos_n, hpos_L] with M hMn hML
  exact (psd_pair_spatial_ineqs (sys.V0 b M) (sys.V1 b M)).2.2.2.2.2.1
    (n / 2) (L / 2) (by omega) (by omega) hMn hML

lemma Splus_square (sys : TrotterIsingSystem) {n : ℕ} {b : ℝ}
    (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b) :
    1 - sys.Splus (2 * n) b ≤ purityUpdate (1 - sys.Splus n b) := by
  have ht_n := sys.trot_Zp_tendsto hn h4 hb
  have ht_2n := sys.trot_Zp_tendsto (even_two_mul n) (by omega) hb
  have ht_4n := sys.trot_Zp_tendsto (even_two_mul (2 * n)) (by omega) hb
  have hd2 : (2 * n) / 2 = 2 * (n / 2) := by rcases hn with ⟨k, rfl⟩; omega
  have hd4 : (2 * (2 * n)) / 2 = 4 * (n / 2) := by rcases hn with ⟨k, rfl⟩; omega
  rw [hd2] at ht_2n; rw [hd4] at ht_4n
  have hZ_n := sys.Zplus_pos hn h4 (b := b)
  have hZ_2n := sys.Zplus_pos (even_two_mul n) (by omega) (b := b)
  have hSn_pos : 0 < sys.Splus n b := div_pos hZ_2n (pow_pos hZ_n 2)
  have hS1_tend : Tendsto (fun M =>
      1 - (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (2 * (n / 2))) +
           Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (2 * (n / 2)))) /
          (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (n / 2)) +
           Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (n / 2))) ^ 2)
      atTop (nhds (1 - sys.Splus n b)) :=
    tendsto_const_nhds.sub (ht_2n.div (ht_n.pow 2) (pow_pos hZ_n 2).ne')
  have hS2_tend : Tendsto (fun M =>
      1 - (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (4 * (n / 2))) +
           Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (4 * (n / 2)))) /
          (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (2 * (n / 2))) +
           Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (2 * (n / 2)))) ^ 2)
      atTop (nhds (1 - sys.Splus (2 * n) b)) :=
    tendsto_const_nhds.sub (ht_4n.div (ht_2n.pow 2) (pow_pos hZ_2n 2).ne')
  have hU_tend : Tendsto (fun M =>
      purityUpdate (1 - (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (2 * (n / 2))) +
                         Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (2 * (n / 2)))) /
                        (Matrix.trace ((sys.V0 b M * (sys.V0 b M)ᵀ) ^ (n / 2)) +
                         Matrix.trace ((sys.V1 b M * (sys.V1 b M)ᵀ) ^ (n / 2))) ^ 2))
      atTop (nhds (purityUpdate (1 - sys.Splus n b))) := by
    unfold purityUpdate
    have hden_ne : 2 * (1 - (1 - sys.Splus n b)) ^ 2 ≠ 0 := by
      have : 1 - (1 - sys.Splus n b) = sys.Splus n b := by ring
      rw [this]; positivity
    exact (hS1_tend.pow 2).div (((tendsto_const_nhds.sub hS1_tend).pow 2).const_mul 2) hden_ne
  have hpos_n := ht_n.eventually (lt_mem_nhds hZ_n)
  have hpos_2n := ht_2n.eventually (lt_mem_nhds hZ_2n)
  refine le_of_tendsto_of_tendsto hS2_tend hU_tend ?_
  filter_upwards [hpos_n, hpos_2n] with M hMn hM2n
  exact (psd_pair_spatial_ineqs (sys.V0 b M) (sys.V1 b M)).2.2.2.2.1 (n / 2) hMn hM2n

/-- Construct `PuritySystem1D` for `Zplus` directly from the Trotter limit + finite Gibbs sums! -/
noncomputable def toPuritySystem1D (sys : TrotterIsingSystem) : PuritySystem1D where
  Z := sys.Zplus
  Z_pos := fun n b hn h4 _ => sys.Zplus_pos hn h4
  S_le_one := fun n b hn h4 hb => sys.Splus_le_one hn h4 hb
  T_le_one := fun n b hn h4 _ => by
    have hZ := sys.Zplus_pos hn h4 (b := b)
    rw [div_le_one (pow_pos hZ 2)]
    let w : Fin (sys.d_pu n) ⊕ Fin (sys.d_pt n) → ℝ :=
      Sum.elim (fun k => Real.exp (-b * sys.E_pu n k)) (fun k => Real.exp (-b * sys.E_pt n k))
    have hw_nn : ∀ x, 0 ≤ w x := fun x => by cases x <;> exact (Real.exp_pos _).le
    have h1 : sys.Zplus n b = ∑ x, w x := by unfold Zplus; rw [Fintype.sum_sum_type]; rfl
    have h2 : sys.Zplus n (2 * b) = ∑ x, w x ^ 2 := by
      unfold Zplus; rw [Fintype.sum_sum_type]
      congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;>
        (dsimp [w]; rw [← Real.exp_nat_mul]; congr 1; ring)
    rw [h1, h2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun x _ => hw_nn x)
  S_square := fun n b hn h4 hb => by
    have h := sys.Splus_square hn h4 hb
    unfold Splus at h
    rwa [show 2 * (2 * n) = 4 * n by omega] at h
  T_square := fun n b hn h4 _ => by
    have hZ := sys.Zplus_pos hn h4 (b := b)
    have hZ2 := sys.Zplus_pos hn h4 (b := 2 * b)
    let w : Fin (sys.d_pu n) ⊕ Fin (sys.d_pt n) → ℝ :=
      Sum.elim (fun k => Real.exp (-b * sys.E_pu n k)) (fun k => Real.exp (-b * sys.E_pt n k))
    let p : Fin (sys.d_pu n) ⊕ Fin (sys.d_pt n) → ℝ := fun x => w x / sys.Zplus n b
    have hp_nn : ∀ x ∈ Finset.univ, 0 ≤ p x := fun x _ =>
      div_nonneg (by cases x <;> exact (Real.exp_pos _).le) hZ.le
    have h1 : sys.Zplus n b = ∑ x, w x := by unfold Zplus; rw [Fintype.sum_sum_type]; rfl
    have h2 : sys.Zplus n (2 * b) = ∑ x, w x ^ 2 := by
      unfold Zplus; rw [Fintype.sum_sum_type]
      congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;>
        (dsimp [w]; rw [← Real.exp_nat_mul]; congr 1; ring)
    have h4eq : sys.Zplus n (4 * b) = ∑ x, w x ^ 4 := by
      unfold Zplus; rw [Fintype.sum_sum_type]
      congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;>
        (dsimp [w]; rw [← Real.exp_nat_mul]; congr 1; ring)
    have hp_sum : ∑ x, p x = 1 := by dsimp [p]; rw [← Finset.sum_div, ← h1, div_self hZ.ne']
    have hP2 : ∑ x, p x ^ 2 = sys.Zplus n (2 * b) / sys.Zplus n b ^ 2 := by
      dsimp [p]; simp_rw [div_pow, ← Finset.sum_div, ← h2]
    have hP4 : ∑ x, p x ^ 4 = sys.Zplus n (4 * b) / sys.Zplus n b ^ 4 := by
      dsimp [p]; simp_rw [div_pow, ← Finset.sum_div, ← h4eq]
    have hbd := (finset_purity_square_bound Finset.univ p hp_nn hp_sum).2.2
    have hrat : (∑ x, p x ^ 4) / (∑ x, p x ^ 2) ^ 2 = sys.Zplus n (4 * b) / sys.Zplus n (2 * b) ^ 2 := by
      rw [hP2, hP4]; field_simp [hZ.ne', hZ2.ne']
    rwa [hrat, hP2] at hbd

set_option maxHeartbeats 800000 in
/-- **Trotter-Limit Ising Multiplet Theorem (Sorted Spectrum with Exact Length & Parity Labels)**:
from `1 - Splus L₀ b₀ ≤ 1/100` and `1 - Tplus (2 L₀) b₀ ≤ 1/100` alone, proves for **every**
even `ℓ ≥ L₀` that sorting `E_pu ℓ ++ E_mu ℓ` yields:
- `sorted.length = sys.d_pu ℓ + sys.d_mu ℓ` (with `2 ≤ sorted.length`),
- `sorted[0]` is the unique ground energy of the `+1` parity sector (`E_pu`) and
  `sorted[1]` is the unique ground energy of the `-1` parity sector (`E_mu`),
- `0 ≤ W_ℓ ≤ (12 / (5 * b₀)) * exp (-(log 20) * ℓ / (2 * L₀))`,
- `Γ_ℓ > log 8 / b₀` for every higher level `i ≥ 2`. -/
theorem ising_multiplet_sorted_labeled (sys : TrotterIsingSystem)
    {L₀ : ℕ} {b₀ : ℝ} (hL₀ : Even L₀) (h4 : 4 ≤ L₀) (hb₀ : 0 < b₀)
    (hS0 : 1 - sys.Splus L₀ b₀ ≤ 1 / 100)
    (hT0 : 1 - sys.Tplus (2 * L₀) b₀ ≤ 1 / 100)
    {ℓ : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : L₀ ≤ ℓ) :
    let raw := List.ofFn (sys.E_pu ℓ) ++ List.ofFn (sys.E_mu ℓ)
    let sorted := raw.mergeSort (· ≤ ·)
    sorted.length = sys.d_pu ℓ + sys.d_mu ℓ ∧
    2 ≤ sorted.length ∧
    (∀ h0, ∃ k₀ : Fin (sys.d_pu ℓ), sorted[0]'h0 = sys.E_pu ℓ k₀ ∧
      ∀ k : Fin (sys.d_pu ℓ), sys.E_pu ℓ k₀ ≤ sys.E_pu ℓ k) ∧
    (∀ h1, ∃ k₁ : Fin (sys.d_mu ℓ), sorted[1]'h1 = sys.E_mu ℓ k₁ ∧
      ∀ k : Fin (sys.d_mu ℓ), sys.E_mu ℓ k₁ ≤ sys.E_mu ℓ k) ∧
    (∀ h0 h1, (0 : ℝ) ≤ sorted[1]'h1 - sorted[0]'h0 ∧
      sorted[1]'h1 - sorted[0]'h0 ≤
        (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ)))) ∧
    (∀ i (hi : i < sorted.length) (h1 : 1 < sorted.length), 2 ≤ i →
      Real.log 8 / b₀ < sorted[i]'hi - sorted[1]'h1) := by
  -- 1. Build a virtual `IsingTwistSystem`? No — prove the exact same 6 steps directly!
  let psys := sys.toPuritySystem1D
  have hG5 : bootstrapCoeff (1 / 100 : ℝ) ≤ 5 := by unfold bootstrapCoeff; norm_num
  have hdyad := psys.dyadic_purities hL₀ h4 hb₀ (by norm_num) (by norm_num) hG5 (by norm_num)
    hS0 hT0
  -- 2. Locate the dyadic bracket `n_j ≤ ℓ ≤ 2 n_j`
  have hL₀_pos : 0 < L₀ := by omega
  have hex : ∃ j : ℕ, 2 ^ j * L₀ ≤ ℓ ∧ ℓ ≤ 2 * (2 ^ j * L₀) := by
    have hpow_gt : ∃ k : ℕ, ℓ < 2 ^ k * L₀ := ⟨ℓ + 1, by
      have : ℓ + 1 < 2 ^ (ℓ + 1) := Nat.lt_two_pow_self
      nlinarith⟩
    let k := Nat.find hpow_gt
    have hk_gt : ℓ < 2 ^ k * L₀ := Nat.find_spec hpow_gt
    have hk_pos : 0 < k := by
      by_contra h0; push_neg at h0
      have hk0 : k = 0 := Nat.le_zero.mp h0
      rw [hk0, pow_zero, one_mul] at hk_gt; omega
    refine ⟨k - 1, ?_, ?_⟩
    · have hmin := Nat.find_min hpow_gt (Nat.sub_lt hk_pos Nat.one_pos)
      exact not_lt.mp hmin
    · have hmul : 2 * (2 ^ (k - 1) * L₀) = 2 ^ k * L₀ := by
        have : 2 * 2 ^ (k - 1) = 2 ^ k := by
          conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
        rw [← mul_assoc, this]
      omega
  rcases hex with ⟨j, hnj_le, hℓ_le⟩
  set nj := 2 ^ j * L₀
  set bj := (2 : ℝ) ^ j * b₀
  set uj := dyadicDefect 5 (5 * (1 / 100 : ℝ)) j
  have hnj_even : Even nj := by rcases hL₀ with ⟨k, rfl⟩; exact ⟨2 ^ j * k, by dsimp [nj]; ring⟩
  have hnj4 : 4 ≤ nj := by have : 1 ≤ 2 ^ j := Nat.one_le_two_pow; dsimp [nj]; nlinarith
  have hbj_pos : 0 < bj := by dsimp [bj]; positivity
  have hℓ4 : 4 ≤ ℓ := le_trans hnj4 hnj_le
  have huj_eq : uj = (1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j) := by
    dsimp [uj, dyadicDefect]; norm_num
  have huj_pos : 0 < uj := by rw [huj_eq]; positivity
  have huj_le : uj ≤ 1 / 100 := by
    rw [huj_eq]
    have hpow : (1 / 20 : ℝ) ^ (2 ^ j) ≤ (1 / 20 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) Nat.one_le_two_pow
    linarith
  have hS_nj : 1 - sys.Splus nj bj ≤ uj := (hdyad j).1
  have hT_2nj : 1 - sys.Tplus (2 * nj) bj ≤ uj := (hdyad j).2
  -- 3. Interpolate `Tplus ℓ bj ≥ 1 - 3 uj` and `Splus ℓ bj ≥ 1 - uj`
  have hS_ℓ : 1 - uj ≤ sys.Splus ℓ bj := by
    have hmono := sys.Splus_mono_even hnj_even hℓ_even hnj4 hnj_le hbj_pos
    linarith
  have hT_ℓ : 1 - 3 * uj ≤ sys.Tplus ℓ bj := by
    have hUpper : sys.Zplus ℓ bj ≤ sys.Zplus nj bj ^ ((ℓ : ℝ) / (nj : ℝ)) :=
      sys.Zplus_rpow_upper hnj_even hℓ_even hnj4 hnj_le hbj_pos
    have hLower : sys.Zplus (2 * nj) (2 * bj) ^ ((ℓ : ℝ) / (2 * (nj : ℝ))) ≤ sys.Zplus ℓ (2 * bj) := by
      have h2 := sys.Zplus_rpow_upper (b := 2 * bj) hℓ_even (even_two_mul nj) hℓ4 hℓ_le (by linarith)
      have hr_pos : 0 < (ℓ : ℝ) / (2 * (nj : ℝ)) := by
        have : 0 < ℓ := by omega
        have : 0 < nj := by omega
        positivity
      have hp := Real.rpow_le_rpow (sys.Zplus_pos (even_two_mul nj) (by omega)).le h2 hr_pos.le
      rw [← Real.rpow_mul (sys.Zplus_pos hℓ_even hℓ4).le] at hp
      have hcancel : ((2 * nj : ℕ) : ℝ) / (ℓ : ℝ) * ((ℓ : ℝ) / (2 * (nj : ℝ))) = 1 := by
        have h1 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
        have h2' : (nj : ℝ) ≠ 0 := by exact_mod_cast (by omega : nj ≠ 0)
        push_cast; field_simp [h1, h2']
      rwa [hcancel, Real.rpow_one] at hp
    have hinterp := purity_interpolation (by omega : 0 < nj)
      (sys.Zplus_pos hnj_even hnj4 (b := bj))
      (sys.Zplus_pos (even_two_mul nj) (by omega) (b := bj))
      (sys.Zplus_pos (even_two_mul nj) (by omega) (b := 2 * bj))
      (sys.Zplus_pos hℓ_even hℓ4 (b := bj)) hUpper hLower
    have hcube : (1 - uj) ^ 3 ≤ sys.Tplus (2 * nj) bj * sys.Splus nj bj ^ 2 := by
      have h1 : 1 - uj ≤ sys.Tplus (2 * nj) bj := by linarith
      have h2 : 1 - uj ≤ sys.Splus nj bj := by linarith
      have h1mu : 0 ≤ 1 - uj := by linarith
      have hsq : (1 - uj) ^ 2 ≤ sys.Splus nj bj ^ 2 := by nlinarith
      calc (1 - uj) ^ 3 = (1 - uj) * (1 - uj) ^ 2 := by ring
        _ ≤ sys.Tplus (2 * nj) bj * sys.Splus nj bj ^ 2 :=
            mul_le_mul h1 hsq (sq_nonneg _) (by linarith)
    have hexp_le1 : (ℓ : ℝ) / (2 * (nj : ℝ)) ≤ 1 := by
      have hnj_Rpos : (0 : ℝ) < (nj : ℝ) := by exact_mod_cast (by omega : 0 < nj)
      rw [div_le_one (by positivity)]
      have : (ℓ : ℝ) ≤ (2 * nj : ℕ) := by exact_mod_cast hℓ_le
      push_cast at this; linarith
    have hpow_ge : (1 - uj) ^ 3 ≤
        (sys.Tplus (2 * nj) bj * sys.Splus nj bj ^ 2) ^ ((ℓ : ℝ) / (2 * (nj : ℝ))) := by
      have h1mu_pos : 0 < (1 - uj) ^ 3 := pow_pos (by linarith) 3
      have h1 : (1 - uj) ^ 3 ≤ 1 := by
        have : 0 ≤ 1 - uj := by linarith
        nlinarith [sq_nonneg (1 - uj)]
      have h2 : ((1 - uj) ^ 3) ^ ((ℓ : ℝ) / (2 * (nj : ℝ))) ≤
          (sys.Tplus (2 * nj) bj * sys.Splus nj bj ^ 2) ^ ((ℓ : ℝ) / (2 * (nj : ℝ))) :=
        Real.rpow_le_rpow h1mu_pos.le hcube (by positivity)
      have h3 : (1 - uj) ^ 3 ≤ ((1 - uj) ^ 3) ^ ((ℓ : ℝ) / (2 * (nj : ℝ))) := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge h1mu_pos h1 hexp_le1
      exact h3.trans h2
    have hbern := one_sub_three_mul_le_cube huj_pos.le (by linarith)
    exact hbern.trans (hpow_ge.trans hinterp)
  -- 4. Sector ratio `Zminus / Zplus ≥ 1 - 2 δ` whenever `Splus ℓ b ≥ 1 - δ` (`0 ≤ δ ≤ 1/2`)
  have hrat_at : ∀ (b δ : ℝ), 0 < b → 0 ≤ δ → δ ≤ 1 / 2 → 1 - δ ≤ sys.Splus ℓ b →
      1 - 2 * δ ≤ sys.Zminus ℓ b / sys.Zplus ℓ b := by
    intro b δ hb hδ0 hδh hS
    have hZp := sys.Zplus_pos hℓ_even hℓ4 (b := b)
    have hZm := sys.Zminus_pos hℓ_even hℓ4 (b := b)
    have hZm_le := sys.Zminus_le_Zplus hℓ_even hℓ4 hb
    have h2Z := sys.two_mul_Zplus_double_le hℓ_even hℓ4 hb
    have hS_le : sys.Splus ℓ b ≤ (1 + (sys.Zminus ℓ b / sys.Zplus ℓ b) ^ 2) / 2 := by
      unfold Splus
      have hrew : (1 + (sys.Zminus ℓ b / sys.Zplus ℓ b) ^ 2) / 2 =
          (sys.Zplus ℓ b ^ 2 + sys.Zminus ℓ b ^ 2) / (2 * sys.Zplus ℓ b ^ 2) := by
        field_simp [hZp.ne']
      rw [hrew, div_le_div_iff₀ (pow_pos hZp 2) (by positivity)]
      nlinarith [pow_pos hZp 2]
    have hr_nn : 0 ≤ sys.Zminus ℓ b / sys.Zplus ℓ b := div_nonneg hZm.le hZp.le
    have hr_le1 : sys.Zminus ℓ b / sys.Zplus ℓ b ≤ 1 := (div_le_one hZp).mpr hZm_le
    nlinarith
  have hrat_bj : 1 - 2 * uj ≤ sys.Zminus ℓ bj / sys.Zplus ℓ bj :=
    hrat_at bj uj hbj_pos huj_pos.le (by linarith) hS_ℓ
  have hS_ℓ_2b : 1 - 3 * uj ≤ sys.Splus ℓ (2 * bj) := by
    have h1 : psys.S nj (2 * bj) = psys.S nj bj ^ 2 * psys.T (2 * nj) bj / psys.T nj bj ^ 2 :=
      psys.space_time_cancel hnj_even hnj4 hbj_pos
    have hT_le1 : psys.T nj bj ≤ 1 := psys.T_le_one nj bj hnj_even hnj4 hbj_pos
    have hT_pos : 0 < psys.T nj bj := psys.T_pos hnj_even hnj4 hbj_pos
    have hT2_le1 : psys.T nj bj ^ 2 ≤ 1 := by nlinarith
    have hnum_ge : (1 - uj) ^ 3 ≤ psys.S nj bj ^ 2 * psys.T (2 * nj) bj := by
      have ha : 1 - uj ≤ psys.S nj bj := by change 1 - uj ≤ sys.Splus nj bj; linarith
      have hb' : 1 - uj ≤ psys.T (2 * nj) bj := by change 1 - uj ≤ sys.Tplus (2 * nj) bj; linarith
      have hsq : (1 - uj) ^ 2 ≤ psys.S nj bj ^ 2 := by nlinarith
      calc (1 - uj) ^ 3 = (1 - uj) ^ 2 * (1 - uj) := by ring
        _ ≤ psys.S nj bj ^ 2 * psys.T (2 * nj) bj :=
            mul_le_mul hsq hb' (by linarith) (sq_nonneg _)
    have hSnj_2b : 1 - 3 * uj ≤ sys.Splus nj (2 * bj) := by
      have hdiv : psys.S nj bj ^ 2 * psys.T (2 * nj) bj ≤ psys.S nj (2 * bj) := by
        rw [h1, le_div_iff₀ (pow_pos hT_pos 2)]
        have hnn : 0 ≤ psys.S nj bj ^ 2 * psys.T (2 * nj) bj :=
          mul_nonneg (sq_nonneg _) (psys.T_pos (even_two_mul nj) (by omega) hbj_pos).le
        nlinarith
      exact (one_sub_three_mul_le_cube huj_pos.le (by linarith)).trans (hnum_ge.trans hdiv)
    exact hSnj_2b.trans (sys.Splus_mono_even hnj_even hℓ_even hnj4 hnj_le (by linarith))
  have hrat_2bj : 1 - 6 * uj ≤ sys.Zminus ℓ (2 * bj) / sys.Zplus ℓ (2 * bj) := by
    have := hrat_at (2 * bj) (3 * uj) (by linarith) (by linarith) (by linarith) hS_ℓ_2b
    linarith
  have hTm_ge : 1 - 9 * uj ≤ sys.Tminus ℓ bj := by
    have hZp_b := sys.Zplus_pos hℓ_even hℓ4 (b := bj)
    have hZm_b := sys.Zminus_pos hℓ_even hℓ4 (b := bj)
    have hZp_2b := sys.Zplus_pos hℓ_even hℓ4 (b := 2 * bj)
    have hZm_le := sys.Zminus_le_Zplus hℓ_even hℓ4 hbj_pos
    have hT_id : sys.Tminus ℓ bj =
        sys.Tplus ℓ bj * (sys.Zminus ℓ (2 * bj) / sys.Zplus ℓ (2 * bj)) /
          (sys.Zminus ℓ bj / sys.Zplus ℓ bj) ^ 2 := by
      unfold Tminus Tplus; field_simp [hZp_b.ne', hZm_b.ne', hZp_2b.ne']
    have hden_le1 : (sys.Zminus ℓ bj / sys.Zplus ℓ bj) ^ 2 ≤ 1 := by
      have hle1 : sys.Zminus ℓ bj / sys.Zplus ℓ bj ≤ 1 := (div_le_one hZp_b).mpr hZm_le
      have hpos : 0 ≤ sys.Zminus ℓ bj / sys.Zplus ℓ bj := div_nonneg hZm_b.le hZp_b.le
      nlinarith
    have hden_pos : 0 < (sys.Zminus ℓ bj / sys.Zplus ℓ bj) ^ 2 := pow_pos (div_pos hZm_b hZp_b) 2
    have hprod : (1 - 3 * uj) * (1 - 6 * uj) ≤
        sys.Tplus ℓ bj * (sys.Zminus ℓ (2 * bj) / sys.Zplus ℓ (2 * bj)) :=
      mul_le_mul hT_ℓ hrat_2bj (by linarith) (by linarith)
    have hdiv : sys.Tplus ℓ bj * (sys.Zminus ℓ (2 * bj) / sys.Zplus ℓ (2 * bj)) ≤ sys.Tminus ℓ bj := by
      rw [hT_id, le_div_iff₀ hden_pos]
      have hnn : 0 ≤ sys.Tplus ℓ bj * (sys.Zminus ℓ (2 * bj) / sys.Zplus ℓ (2 * bj)) :=
        mul_nonneg (div_nonneg (sys.Zplus_pos hℓ_even hℓ4).le (pow_nonneg hZp_b.le 2))
          (div_nonneg (sys.Zminus_pos hℓ_even hℓ4).le hZp_2b.le)
      nlinarith
    have h9 : 1 - 9 * uj ≤ (1 - 3 * uj) * (1 - 6 * uj) := by nlinarith [sq_nonneg uj]
    linarith
  -- 5. Ground states `k₀` (even-X untwisted) and `k₁` (odd-X untwisted) + ordering `E₀ ≤ E₁`
  haveI : Nonempty (Fin (sys.d_pu ℓ)) := ⟨⟨0, sys.d_pu_pos ℓ hℓ_even hℓ4⟩⟩
  haveI : Nonempty (Fin (sys.d_mu ℓ)) := ⟨⟨0, sys.d_mu_pos ℓ hℓ_even hℓ4⟩⟩
  rcases Finset.exists_min_image Finset.univ (sys.E_pu ℓ) Finset.univ_nonempty with ⟨k₀, _, hk₀⟩
  rcases Finset.exists_min_image Finset.univ (sys.E_mu ℓ) Finset.univ_nonempty with ⟨k₁, _, hk₁⟩
  let Ep : Fin (sys.d_pu ℓ + sys.d_pt ℓ) → ℝ := Fin.addCases (sys.E_pu ℓ) (sys.E_pt ℓ)
  let Em : Fin (sys.d_mu ℓ + sys.d_mt ℓ) → ℝ := Fin.addCases (sys.E_mu ℓ) (sys.E_mt ℓ)
  let k₀_comb : Fin (sys.d_pu ℓ + sys.d_pt ℓ) := Fin.castAdd (sys.d_pt ℓ) k₀
  let k₁_comb : Fin (sys.d_mu ℓ + sys.d_mt ℓ) := Fin.castAdd (sys.d_mt ℓ) k₁
  have hEp_min : ∀ k, Ep k₀_comb ≤ Ep k := fun k => by
    refine Fin.addCases (fun i => ?_) (fun t => ?_) k
    · simpa [Ep, k₀_comb] using hk₀ i (Finset.mem_univ i)
    · rcases sys.seam_order_p ℓ hℓ_even hℓ4 t with ⟨u, hu⟩
      have h1 := hk₀ u (Finset.mem_univ u)
      simpa [Ep, k₀_comb] using le_trans h1 hu
  have hEm_min : ∀ k, Em k₁_comb ≤ Em k := fun k => by
    refine Fin.addCases (fun i => ?_) (fun t => ?_) k
    · simpa [Em, k₁_comb] using hk₁ i (Finset.mem_univ i)
    · rcases sys.seam_order_m ℓ hℓ_even hℓ4 t with ⟨u, hu⟩
      have h1 := hk₁ u (Finset.mem_univ u)
      simpa [Em, k₁_comb] using le_trans h1 hu
  have hZp_sum : ∀ b : ℝ, sys.Zplus ℓ b = ∑ k : Fin (sys.d_pu ℓ + sys.d_pt ℓ), Real.exp (-b * Ep k) := fun b => by
    unfold Zplus; rw [Fin.sum_univ_add]; simp [Ep]
  have hZm_sum : ∀ b : ℝ, sys.Zminus ℓ b = ∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-b * Em k) := fun b => by
    unfold Zminus; rw [Fin.sum_univ_add]; simp [Em]
  have hE0_le_E1 : sys.E_pu ℓ k₀ ≤ sys.E_mu ℓ k₁ := by
    have h := gibbs_min_le_of_Z_le Ep Em k₀_comb k₁_comb hEp_min fun b hb => by
      rw [← hZp_sum b, ← hZm_sum b]; exact sys.Zminus_le_Zplus hℓ_even hℓ4 hb
    simpa [Ep, Em, k₀_comb, k₁_comb] using h
  -- 6. Exponential doublet splitting `E₁ - E₀ ≤ 12 u_j / b_j ≤ (12 / (5 b₀)) exp(-log 20 * ℓ / (2 L₀))`
  have hLower_m : sys.Tminus ℓ bj * sys.Zminus ℓ bj ≤ Real.exp (-bj * sys.E_mu ℓ k₁) := by
    have h1 := gibbs_purity_mul_Z_le_ground Em k₁_comb hbj_pos hEm_min
    have h2 : ∑ k, Real.exp (-2 * bj * Em k) = sys.Zminus ℓ (2 * bj) := by
      rw [hZm_sum (2 * bj)]
      refine Finset.sum_congr rfl fun k _ => by congr 1; ring
    rw [h2, ← hZm_sum bj] at h1
    simpa [Tminus, Em, k₁_comb] using h1
  have hUpper_p : Real.exp (-bj * sys.E_pu ℓ k₀) ≤ sys.Zplus ℓ bj := by
    rw [hZp_sum bj]
    simpa [Ep, k₀_comb] using
      Finset.single_le_sum (f := fun k => Real.exp (-bj * Ep k))
        (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k₀_comb)
  have hsplit_12 : sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤ 12 * uj / bj := by
    rw [huj_eq] at hTm_ge hrat_bj ⊢
    exact ising_splitting_12uj hb₀ (sys.Zplus_pos hℓ_even hℓ4) (sys.Zminus_pos hℓ_even hℓ4)
      hTm_ge hrat_bj hLower_m hUpper_p
  have hsplit_012 : sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤ (12 / 100 : ℝ) / b₀ := by
    have hbj_ge : b₀ ≤ bj := by
      dsimp [bj]; have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num); nlinarith
    calc sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤ 12 * uj / bj := hsplit_12
      _ ≤ 12 * (1 / 100) / b₀ :=
          div_le_div₀ (by norm_num) (by linarith) hb₀ hbj_ge
      _ = (12 / 100 : ℝ) / b₀ := by ring
  have hsplit_exp : sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤
      (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) := by
    have hbj_ge : b₀ ≤ bj := by
      dsimp [bj]; have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num); nlinarith
    have h1 : 12 * uj / bj ≤ (12 / (5 * b₀)) * (1 / 20 : ℝ) ^ (2 ^ j) := by
      rw [huj_eq]
      calc 12 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) / bj
          ≤ 12 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) / b₀ :=
            div_le_div_of_nonneg_left (by positivity) hb₀ hbj_ge
        _ = (12 / (5 * b₀)) * (1 / 20 : ℝ) ^ (2 ^ j) := by ring
    have h2 : (1 / 20 : ℝ) ^ (2 ^ j) ≤ Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) := by
      have heq : (1 / 20 : ℝ) ^ (2 ^ j) = Real.exp (-((2 ^ j : ℕ) : ℝ) * Real.log 20) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 20 : ℝ) ^ (2 ^ j)),
          Real.log_pow, one_div, Real.log_inv]
        congr 1; ring
      rw [heq]; apply Real.exp_le_exp.mpr
      have hℓ_bound : (ℓ : ℝ) / (2 * (L₀ : ℝ)) ≤ ((2 ^ j : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        have : (ℓ : ℝ) ≤ ((2 * (2 ^ j * L₀) : ℕ) : ℝ) := by exact_mod_cast hℓ_le
        push_cast at this ⊢; linarith
      have hlog20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
      have hmul := mul_le_mul_of_nonneg_left hℓ_bound hlog20.le
      have hneg : -(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ)) =
          -(Real.log 20 * ((ℓ : ℝ) / (2 * (L₀ : ℝ)))) := by ring
      have hcomm : -((2 ^ j : ℕ) : ℝ) * Real.log 20 = -(Real.log 20 * ((2 ^ j : ℕ) : ℝ)) := by ring
      rw [hneg, hcomm]
      linarith only [hmul]
    exact hsplit_12.trans (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
  -- 7. Within-sector excited-state gaps (`> log 20 / b₀` in even-X, `> log 10 / b₀` in odd-X)
  have hgap_p : ∀ k : Fin (sys.d_pu ℓ), k ≠ k₀ →
      Real.log 20 / b₀ < sys.E_pu ℓ k - sys.E_pu ℓ k₀ := by
    have hTp_gibbs : 1 - 3 * uj ≤ (∑ k, Real.exp (-2 * bj * Ep k)) / (∑ k, Real.exp (-bj * Ep k)) ^ 2 := by
      have h2 : ∑ k, Real.exp (-2 * bj * Ep k) = sys.Zplus ℓ (2 * bj) := by
        rw [hZp_sum (2 * bj)]; refine Finset.sum_congr rfl fun k _ => by congr 1; ring
      rw [h2, ← hZp_sum bj]; exact hT_ℓ
    have hgibbs_p := gibbs_purity_implies_unique_ground_and_gap Ep k₀_comb bj hbj_pos hEp_min
      (by positivity) (by linarith) hTp_gibbs
    intro k hne
    have hne_comb : Fin.castAdd (sys.d_pt ℓ) k ≠ k₀_comb := fun h => hne (Fin.castAdd_injective _ _ h)
    have hexp_le := hgibbs_p.2 (Fin.castAdd (sys.d_pt ℓ) k) hne_comb
    have hratio_lt : 3 * uj / (1 - 3 * uj) < (1 / 20 : ℝ) ^ (2 ^ j) := by
      have h1m : 0 < 1 - 3 * uj := by linarith only [huj_le]
      have h4u : 3 * uj / (1 - 3 * uj) < 5 * uj := by rw [div_lt_iff₀ h1m]; nlinarith only [huj_pos, huj_le]
      have h5eq : 5 * uj = (1 / 20 : ℝ) ^ (2 ^ j) := by rw [huj_eq]; ring
      linarith only [h4u, h5eq]
    have hlog_lt : -bj * (sys.E_pu ℓ k - sys.E_pu ℓ k₀) < (2 ^ j : ℕ) * Real.log (1 / 20) := by
      have hlt := Real.log_lt_log (Real.exp_pos _) (lt_of_le_of_lt hexp_le hratio_lt)
      rw [Real.log_exp, Real.log_pow] at hlt
      simpa [Ep, k₀_comb] using hlt
    rw [one_div, Real.log_inv] at hlog_lt
    rw [div_lt_iff₀ hb₀]
    have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    rw [Nat.cast_pow, Nat.cast_ofNat] at hlog_lt
    dsimp [bj] at hlog_lt; nlinarith only [hlog_lt, h2j_pos]
  have hgap_m : ∀ k : Fin (sys.d_mu ℓ), k ≠ k₁ →
      Real.log 10 / b₀ < sys.E_mu ℓ k - sys.E_mu ℓ k₁ := by
    have hTm_gibbs : 1 - 9 * uj ≤ (∑ k, Real.exp (-2 * bj * Em k)) / (∑ k, Real.exp (-bj * Em k)) ^ 2 := by
      have h2 : ∑ k, Real.exp (-2 * bj * Em k) = sys.Zminus ℓ (2 * bj) := by
        rw [hZm_sum (2 * bj)]; refine Finset.sum_congr rfl fun k _ => by congr 1; ring
      rw [h2, ← hZm_sum bj]; exact hTm_ge
    have hgibbs_m := gibbs_purity_implies_unique_ground_and_gap Em k₁_comb bj hbj_pos hEm_min
      (by positivity) (by linarith) hTm_gibbs
    intro k hne
    have hne_comb : Fin.castAdd (sys.d_mt ℓ) k ≠ k₁_comb := fun h => hne (Fin.castAdd_injective _ _ h)
    have hexp_le := hgibbs_m.2 (Fin.castAdd (sys.d_mt ℓ) k) hne_comb
    have hratio_lt : 9 * uj / (1 - 9 * uj) < (1 / 10 : ℝ) ^ (2 ^ j) := by
      have h1m : 0 < 1 - 9 * uj := by linarith only [huj_le]
      have h10u : 9 * uj / (1 - 9 * uj) < 10 * uj := by rw [div_lt_iff₀ h1m]; nlinarith only [huj_pos, huj_le]
      have h10u_le : 10 * uj ≤ (1 / 10 : ℝ) ^ (2 ^ j) := by
        rw [huj_eq]
        have hsplit : (1 / 20 : ℝ) ^ (2 ^ j) = (1 / 2 : ℝ) ^ (2 ^ j) * (1 / 10 : ℝ) ^ (2 ^ j) := by
          rw [← mul_pow]; norm_num
        rw [hsplit]
        have hhalf : (1 / 2 : ℝ) ^ (2 ^ j) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) Nat.one_le_two_pow
        have hpos10 : 0 ≤ (1 / 10 : ℝ) ^ (2 ^ j) := by positivity
        nlinarith only [hhalf, hpos10]
      linarith only [h10u, h10u_le]
    have hlog_lt : -bj * (sys.E_mu ℓ k - sys.E_mu ℓ k₁) < (2 ^ j : ℕ) * Real.log (1 / 10) := by
      have hlt := Real.log_lt_log (Real.exp_pos _) (lt_of_le_of_lt hexp_le hratio_lt)
      rw [Real.log_exp, Real.log_pow] at hlt
      simpa [Em, k₁_comb] using hlt
    rw [one_div, Real.log_inv] at hlog_lt
    rw [div_lt_iff₀ hb₀]
    have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    rw [Nat.cast_pow, Nat.cast_ofNat] at hlog_lt
    dsimp [bj] at hlog_lt; nlinarith only [hlog_lt, h2j_pos]
  -- 8. Multiplet gap `> log 8 / b₀` above `E₁` for every other untwisted level, then sort!
  have hlog8_lt_10 : Real.log 8 < Real.log 10 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog10_lt_20 : Real.log 10 < Real.log 20 := Real.log_lt_log (by norm_num) (by norm_num)
  have h12_lt := twelve_hundredths_lt_log_ten_sub_log_eight
  have hmgap_p : ∀ k : Fin (sys.d_pu ℓ), k ≠ k₀ → Real.log 8 / b₀ < sys.E_pu ℓ k - sys.E_mu ℓ k₁ := fun k hne => by
    have h1 : (Real.log 10 - 12 / 100) / b₀ < (Real.log 20 - 12 / 100) / b₀ :=
      div_lt_div_of_pos_right (by linarith only [hlog10_lt_20]) hb₀
    have h2 : Real.log 8 / b₀ < (Real.log 10 - 12 / 100) / b₀ :=
      div_lt_div_of_pos_right (by linarith only [h12_lt]) hb₀
    have hsub : Real.log 20 / b₀ - (12 / 100 : ℝ) / b₀ = (Real.log 20 - 12 / 100) / b₀ := by ring
    linarith only [hgap_p k hne, hsplit_012, h1, h2, hsub]
  have hmgap_m : ∀ k : Fin (sys.d_mu ℓ), k ≠ k₁ → Real.log 8 / b₀ < sys.E_mu ℓ k - sys.E_mu ℓ k₁ := fun k hne =>
    lt_trans (div_lt_div_of_pos_right hlog8_lt_10 hb₀) (hgap_m k hne)
  -- Sort `raw = ofFn (E_pu ℓ) ++ ofFn (E_mu ℓ)` (exact same filter argument as `SymmetryTwists`)
  intro raw sorted
  have hperm : sorted.Perm raw := List.mergeSort_perm raw (· ≤ ·)
  have hlen : sorted.length = sys.d_pu ℓ + sys.d_mu ℓ := by rw [hperm.length_eq]; simp [raw]
  have hlen2 : 2 ≤ sorted.length := by
    have := sys.d_pu_pos ℓ hℓ_even hℓ4; have := sys.d_mu_pos ℓ hℓ_even hℓ4; omega
  have hsorted : sorted.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) raw
  set E₀ := sys.E_pu ℓ k₀
  set E₁ := sys.E_mu ℓ k₁
  have hlog8_pos : 0 < Real.log 8 / b₀ := div_pos (Real.log_pos (by norm_num)) hb₀
  have hfilt_single : ∀ {m : ℕ} (f : Fin m → ℝ) (kstar : Fin m),
      f kstar ≤ E₁ →
      (∀ k, k ≠ kstar → E₁ + Real.log 8 / b₀ < f k) →
      (List.ofFn f).filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [f kstar] := by
    intro m f kstar hle hgt
    rw [List.ofFn_eq_map, List.filter_map]
    have hfilt : (List.finRange m).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) = [kstar] := by
      have hnodup := (List.nodup_finRange m).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀))
      have hmem : ∀ k, k ∈ (List.finRange m).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) ↔
          k = kstar := fun k => by
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact ⟨fun hk => by by_contra hne; linarith [hgt k hne], fun hk => by subst hk; linarith⟩
      cases hL : (List.finRange m).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) with
      | nil => have := (hmem kstar).mpr rfl; rw [hL] at this; exact absurd this List.not_mem_nil
      | cons a tl =>
        have ha : a = kstar := (hmem a).mp (by rw [hL]; simp)
        subst ha
        cases tl with
        | nil => rfl
        | cons b tl' =>
          have hb : b = a := (hmem b).mp (by rw [hL]; simp)
          subst hb; rw [hL] at hnodup
          exact absurd List.mem_cons_self (List.nodup_cons.mp hnodup).1
    change List.map f (List.filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) (List.finRange m)) = [f kstar]
    rw [hfilt]; rfl
  have hfilt_sorted_perm : (sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).Perm [E₀, E₁] := by
    refine (hperm.filter _).trans ?_
    dsimp [raw]
    rw [List.filter_append,
      hfilt_single (sys.E_pu ℓ) k₀ (by linarith) (fun k hne => by linarith [hmgap_p k hne]),
      hfilt_single (sys.E_mu ℓ) k₁ le_rfl (fun k hne => by linarith [hmgap_m k hne])]
    exact List.Perm.refl [E₀, E₁]
  rcases List.exists_cons_of_length_pos (by omega : 0 < sorted.length) with ⟨a, t1, ht1⟩
  have ht1_len : 1 ≤ t1.length := by rw [ht1] at hlen2; simp at hlen2; omega
  rcases List.exists_cons_of_length_pos (by omega : 0 < t1.length) with ⟨b, rest, hrest⟩
  have hsorted_eq : sorted = a :: b :: rest := by rw [ht1, hrest]
  have hpw : (a :: b :: rest).Pairwise (· ≤ ·) := hsorted_eq ▸ hsorted
  have hab : a ≤ b := (List.pairwise_cons.mp hpw).1 b List.mem_cons_self
  have hbrest : ∀ x ∈ rest, b ≤ x := (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1
  have hfilt_len : (sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).length = 2 := by
    rw [hfilt_sorted_perm.length_eq]; rfl
  have hb_le : b ≤ E₁ + Real.log 8 / b₀ := by
    by_contra hgt; push_neg at hgt
    have hfilt_rest : rest.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx; simp [not_le.mpr (lt_of_lt_of_le hgt (hbrest x hx))]
    have hlen_le1 : (sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).length ≤ 1 := by
      rw [hsorted_eq]; simp [List.filter_cons, not_le.mpr hgt, hfilt_rest]; split_ifs <;> simp
    omega
  have ha_le : a ≤ E₁ + Real.log 8 / b₀ := le_trans hab hb_le
  have hrest_gt : ∀ x ∈ rest, E₁ + Real.log 8 / b₀ < x := fun x hx => by
    by_contra hle; push_neg at hle
    have hpos : 0 < (rest.filter (fun y => decide (y ≤ E₁ + Real.log 8 / b₀))).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨hx, decide_eq_true hle⟩)
    have hge3 : 3 ≤ (sorted.filter (fun y => decide (y ≤ E₁ + Real.log 8 / b₀))).length := by
      rw [hsorted_eq]; simp [List.filter_cons, ha_le, hb_le]; omega
    omega
  have hfilt_rest : rest.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; simp [not_le.mpr (hrest_gt x hx)]
  have hfilt_eq : sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [a, b] := by
    rw [hsorted_eq]; simp [List.filter_cons, ha_le, hb_le, hfilt_rest]
  rw [hfilt_eq] at hfilt_sorted_perm
  have hab_eq : a = E₀ ∧ b = E₁ := by
    rcases (by simpa using List.perm_pair.mp hfilt_sorted_perm : (a = E₀ ∧ b = E₁) ∨ (a = E₁ ∧ b = E₀)) with
      h | ⟨rfl, rfl⟩
    · exact h
    · exact ⟨le_antisymm hab (by linarith), le_antisymm (by linarith) hab⟩
  have htake2 : sorted.take 2 = [E₀, E₁] := by rw [hsorted_eq, hab_eq.1, hab_eq.2]; rfl
  have hs0 : ∀ h0 : 0 < sorted.length, sorted[0]'h0 = E₀ := fun h0 => by
    have h := congrArg (fun l => l[0]?) htake2; simp [List.getElem?_take_of_lt, h0] at h; exact h
  have hs1 : ∀ h1 : 1 < sorted.length, sorted[1]'h1 = E₁ := fun h1 => by
    have h := congrArg (fun l => l[1]?) htake2; simp [List.getElem?_take_of_lt, h1] at h; exact h
  refine ⟨hlen, hlen2, ?_, ?_, ?_, ?_⟩
  · intro h0; exact ⟨k₀, hs0 h0, fun k => hk₀ k (Finset.mem_univ k)⟩
  · intro h1; exact ⟨k₁, hs1 h1, fun k => hk₁ k (Finset.mem_univ k)⟩
  · intro h0 h1; rw [hs0 h0, hs1 h1]; exact ⟨sub_nonneg.mpr hE0_le_E1, hsplit_exp⟩
  · intro i hi h1 hi2
    rw [hs1 h1]
    have hmem : sorted[i]'hi ∈ rest := by
      cases i with
      | zero => omega
      | succ i' =>
        cases i' with
        | zero => omega
        | succ r =>
          have hr : r < rest.length := by rw [hsorted_eq] at hi; simp at hi; omega
          have hget : sorted[r + 2]'hi = rest[r]'hr := by simp [hsorted_eq]
          rw [hget]; exact List.getElem_mem hr
    linarith [hrest_gt _ hmem]

/-- Projection of `ising_multiplet_sorted_labeled` onto the compact sorted-spectrum statement. -/
theorem ising_multiplet_sorted (sys : TrotterIsingSystem)
    {L₀ : ℕ} {b₀ : ℝ} (hL₀ : Even L₀) (h4 : 4 ≤ L₀) (hb₀ : 0 < b₀)
    (hS0 : 1 - sys.Splus L₀ b₀ ≤ 1 / 100)
    (hT0 : 1 - sys.Tplus (2 * L₀) b₀ ≤ 1 / 100)
    {ℓ : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : L₀ ≤ ℓ) :
    let raw := List.ofFn (sys.E_pu ℓ) ++ List.ofFn (sys.E_mu ℓ)
    let sorted := raw.mergeSort (· ≤ ·)
    2 ≤ sorted.length ∧
    (∀ h0 h1, (0 : ℝ) ≤ sorted[1]'h1 - sorted[0]'h0 ∧
      sorted[1]'h1 - sorted[0]'h0 ≤
        (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ)))) ∧
    (∀ i (hi : i < sorted.length) (h1 : 1 < sorted.length), 2 ≤ i →
      Real.log 8 / b₀ < sorted[i]'hi - sorted[1]'h1) := by
  have h := sys.ising_multiplet_sorted_labeled hL₀ h4 hb₀ hS0 hT0 hℓ_even hℓ_ge
  exact ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end TrotterIsingSystem

end PurityBootstrap.LieTrotter
