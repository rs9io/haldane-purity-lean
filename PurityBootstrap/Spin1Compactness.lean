import PurityBootstrap.LieTrotter
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# General Matrix-Power Limit, Symmetric Projection Algebra, and `ℓ²` Compactness Lemma

Provides three reusable finite-to-infinite tools with zero infinite-dimensional operator theory:
1. **`tendsto_trace_pow_of_first_order`**: if
   `‖X M - (1 + (1 / M) • A)‖ ≤ C / M^2` eventually (in `Matrix.Norms.Operator`), then
   `trace (X M ^ M) → trace (NormedSpace.exp A)` (via the local matrix-power norm estimate
   `‖X M ^ M - NormedSpace.exp A‖ → 0`).
2. **Real symmetric projection algebra (`proj_mul_isHermitian`, `proj_mul_pow`,
   `trace_proj_conj_eq`, `trace_proj_sq_le`, `trace_pow_eq_sum_eigenvalues`)**:
   avoids subspace basis restrictions completely by working on `P * K * P` directly.
3. **`l2_seq_compact_moments`**: given a uniform `ℓ²` bound `∑ i, (f M s i)^2 ≤ C` across
   `s : Fin k`, sorting by decreasing `|·|`, padding with `0`, and applying Tychonoff sequential
   compactness (`isCompact_univ_pi` + `IsCompact.isSeqCompact`) extracts a limit
   `lam : Fin k → ℕ → ℝ` whose `n`-th signed moments (`n ≥ 3`) are the limits of
   `∑ i, (f (φ j) s i)^n` along a strictly increasing subsequence `φ`.
-/

namespace PurityBootstrap.Spin1Compactness

open scoped BigOperators Matrix
open Filter Matrix NormedSpace Topology PurityBootstrap.LieTrotter

/-! ## 1. First-Order Matrix Power Convergence `X_M ^ M → exp A` -/

section PowerLimit

open scoped Matrix.Norms.Operator

private lemma matrix_norm_one_le' {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℝ)‖ ≤ 1 := by
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
    rw [Matrix.linfty_opNorm_def]; simp

private lemma matrix_norm_pow_le' {n : Type*} [Fintype n] [DecidableEq n]
    (x : Matrix n n ℝ) : ∀ k : ℕ, ‖x ^ k‖ ≤ ‖x‖ ^ k
  | 0 => by simpa using (matrix_norm_one_le' (n := n))
  | k + 1 => by
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (matrix_norm_pow_le' x k) (norm_nonneg x))

private lemma norm_pow_sub_pow_le' {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℝ} {R : ℝ} (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R) (hR : 1 ≤ R) :
    ∀ m : ℕ, ‖X ^ m - Y ^ m‖ ≤ (m : ℝ) * R ^ m * ‖X - Y‖
  | 0 => by simp
  | m + 1 => by
    have hsplit : X ^ (m + 1) - Y ^ (m + 1) =
        X ^ m * (X - Y) + (X ^ m - Y ^ m) * Y := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul]; abel
    rw [hsplit]
    have h1 : ‖X ^ m * (X - Y)‖ ≤ R ^ m * ‖X - Y‖ :=
      (norm_mul_le _ _).trans <|
        mul_le_mul_of_nonneg_right
          ((matrix_norm_pow_le' X m).trans (pow_le_pow_left₀ (norm_nonneg _) hX m)) (norm_nonneg _)
    have h2 : ‖(X ^ m - Y ^ m) * Y‖ ≤ (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by
      calc ‖(X ^ m - Y ^ m) * Y‖ ≤ ‖X ^ m - Y ^ m‖ * ‖Y‖ := norm_mul_le _ _
        _ ≤ ((m : ℝ) * R ^ m * ‖X - Y‖) * R :=
            mul_le_mul (norm_pow_sub_pow_le' hX hY hR m) hY (norm_nonneg _) (by positivity)
        _ = (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by rw [pow_succ]; ring
    have hRm : R ^ m ≤ R ^ (m + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg (by linarith : 0 ≤ R) m]
    calc ‖X ^ m * (X - Y) + (X ^ m - Y ^ m) * Y‖
        ≤ ‖X ^ m * (X - Y)‖ + ‖(X ^ m - Y ^ m) * Y‖ := norm_add_le _ _
      _ ≤ R ^ m * ‖X - Y‖ + (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := add_le_add h1 h2
      _ ≤ R ^ (m + 1) * ‖X - Y‖ + (m : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by
          nlinarith [norm_nonneg (X - Y)]
      _ = ((m + 1 : ℕ) : ℝ) * R ^ (m + 1) * ‖X - Y‖ := by push_cast; ring

/-- Entrywise absolute value is bounded by the `ℓ∞` operator norm. -/
lemma abs_entry_le_linfty_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) : |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ k : n, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)
  have h2 : ∑ k : n, ‖A i k‖₊ ≤ Finset.univ.sup (fun r : n => ∑ k : n, ‖A r k‖₊) :=
    Finset.le_sup (f := fun r : n => ∑ k : n, ‖A r k‖₊) (Finset.mem_univ i)
  have h3 : (‖A i j‖₊ : ℝ) ≤ (Finset.univ.sup (fun r : n => ∑ k : n, ‖A r k‖₊) : NNReal) := by
    exact_mod_cast h1.trans h2
  simpa [Real.norm_eq_abs] using h3

/-- Trace magnitude is bounded by `(card n) * ‖A‖` in the `ℓ∞` operator norm. -/
lemma abs_trace_le_card_mul_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : |Matrix.trace A| ≤ (Fintype.card n : ℝ) * ‖A‖ := by
  calc |Matrix.trace A| = |∑ i : n, A i i| := rfl
    _ ≤ ∑ i : n, |A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, ‖A‖ := Finset.sum_le_sum fun i _ => abs_entry_le_linfty_opNorm A i i
    _ = (Fintype.card n : ℝ) * ‖A‖ := by simp

/-- If `‖X M - (1 + (1 / M) • A)‖ ≤ C / M^2` for all `M ≥ M₀` (`M₀ ≥ 1`), then
`‖X M ^ M - NormedSpace.exp A‖ → 0` and `Matrix.trace (X M ^ M) → Matrix.trace (NormedSpace.exp A)`. -/
theorem tendsto_trace_pow_of_first_order {n : Type*} [Fintype n] [DecidableEq n]
    (X : ℕ → Matrix n n ℝ) (A : Matrix n n ℝ) {C : ℝ} (hC : 0 ≤ C) {M₀ : ℕ} (hM₀ : 1 ≤ M₀)
    (happrox : ∀ M : ℕ, M₀ ≤ M → ‖X M - (1 + ((M : ℝ)⁻¹) • A)‖ ≤ C / (M : ℝ) ^ 2) :
    Tendsto (fun M : ℕ => Matrix.trace (X M ^ M)) atTop (nhds (Matrix.trace (NormedSpace.exp A))) := by
  let S : ℝ := ‖A‖ + C + 1
  have hS_pos : 0 < S := by positivity
  let K : ℝ := C + S ^ 2 * Real.exp S
  have hK_nn : 0 ≤ K := by positivity
  have hbound : ∀ M : ℕ, M₀ ≤ M →
      ‖X M ^ M - NormedSpace.exp A‖ ≤ K * Real.exp S / (M : ℝ) := by
    intro M hM
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans hM₀ hM))
    have hMge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans hM₀ hM)
    let t : ℝ := (M : ℝ)⁻¹
    have ht_pos : 0 < t := inv_pos.mpr hMpos
    have ht_le1 : t ≤ 1 := inv_le_one_of_one_le₀ hMge1
    let Y : Matrix n n ℝ := NormedSpace.exp (t • A)
    have hYM : Y ^ M = NormedSpace.exp A := by
      rw [← exp_nsmul_eq_pow, smul_smul, mul_inv_cancel₀ hMpos.ne', one_smul]
    have hY_norm : ‖Y‖ ≤ Real.exp (t * S) := by
      have h1 := norm_exp_le_real_exp_norm (t • A)
      have h2 : ‖t • A‖ ≤ t * S := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact mul_le_mul_of_nonneg_left (by dsimp [S]; linarith [norm_nonneg A]) ht_pos.le
      exact h1.trans (Real.exp_le_exp.mpr h2)
    have hX_norm : ‖X M‖ ≤ Real.exp (t * S) := by
      have htri : ‖X M‖ ≤ ‖(1 : Matrix n n ℝ)‖ + ‖t • A‖ + ‖X M - (1 + t • A)‖ := by
        have hdecomp : X M = (1 + t • A) + (X M - (1 + t • A)) := by abel
        calc ‖X M‖ = ‖(1 + t • A) + (X M - (1 + t • A))‖ := by rw [← hdecomp]
          _ ≤ ‖1 + t • A‖ + ‖X M - (1 + t • A)‖ := norm_add_le _ _
          _ ≤ (‖(1 : Matrix n n ℝ)‖ + ‖t • A‖) + ‖X M - (1 + t • A)‖ := by
                linarith [norm_add_le (1 : Matrix n n ℝ) (t • A)]
      have h1 : ‖(1 : Matrix n n ℝ)‖ ≤ 1 := matrix_norm_one_le'
      have h2 : ‖t • A‖ = t * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      have h3 : ‖X M - (1 + t • A)‖ ≤ t * C := by
        have ha := happrox M hM
        have hdiv : C / (M : ℝ) ^ 2 = t * (t * C) := by dsimp [t]; field_simp
        have htc : t * (t * C) ≤ 1 * (t * C) := mul_le_mul_of_nonneg_right ht_le1 (by positivity)
        linarith
      have hlin : 1 + t * S ≤ Real.exp (t * S) := by linarith [Real.add_one_le_exp (t * S)]
      have : 1 + t * ‖A‖ + t * C ≤ 1 + t * S := by dsimp [S]; nlinarith [ht_pos]
      linarith
    have hXY : ‖X M - Y‖ ≤ K * t ^ 2 := by
      have hdecomp : X M - Y = (X M - (1 + t • A)) - (Y - 1 - t • A) := by abel
      rw [hdecomp]
      have h1 : ‖X M - (1 + t • A)‖ ≤ C * t ^ 2 := by
        have ha := happrox M hM
        rwa [show C / (M : ℝ) ^ 2 = C * t ^ 2 by dsimp [t]; rw [div_eq_mul_inv, inv_pow]] at ha
      have h2 : ‖Y - 1 - t • A‖ ≤ t ^ 2 * S ^ 2 * Real.exp S := by
        have hr := norm_exp_sub_one_sub_le (t • A)
        have hta : ‖t • A‖ ≤ t * S := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
          exact mul_le_mul_of_nonneg_left (by dsimp [S]; linarith [norm_nonneg A]) ht_pos.le
        have hsq : ‖t • A‖ ^ 2 ≤ (t * S) ^ 2 := by nlinarith [norm_nonneg (t • A)]
        have hexp : Real.exp ‖t • A‖ ≤ Real.exp S := Real.exp_le_exp.mpr (hta.trans (by nlinarith))
        calc ‖Y - 1 - t • A‖ ≤ ‖t • A‖ ^ 2 * Real.exp ‖t • A‖ := hr
          _ ≤ (t * S) ^ 2 * Real.exp S := mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _)
          _ = t ^ 2 * S ^ 2 * Real.exp S := by ring
      calc ‖(X M - (1 + t • A)) - (Y - 1 - t • A)‖
          ≤ ‖X M - (1 + t • A)‖ + ‖Y - 1 - t • A‖ := norm_sub_le _ _
        _ ≤ C * t ^ 2 + t ^ 2 * S ^ 2 * Real.exp S := add_le_add h1 h2
        _ = K * t ^ 2 := by dsimp [K]; ring
    have hRge1 : 1 ≤ Real.exp (t * S) := Real.one_le_exp (by positivity)
    have hpow := norm_pow_sub_pow_le' hX_norm hY_norm hRge1 M
    rw [hYM] at hpow
    have hRM : (Real.exp (t * S)) ^ M = Real.exp S := by
      rw [← Real.exp_nat_mul]
      congr 1; dsimp [t]; field_simp [hMpos.ne']
    rw [hRM] at hpow
    calc ‖X M ^ M - NormedSpace.exp A‖
        ≤ (M : ℝ) * Real.exp S * ‖X M - Y‖ := hpow
      _ ≤ (M : ℝ) * Real.exp S * (K * t ^ 2) :=
          mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = K * Real.exp S / (M : ℝ) := by dsimp [t]; field_simp [hMpos.ne']
  rw [Metric.tendsto_atTop]
  intro ε hε
  let D : ℝ := (Fintype.card n : ℝ) * K * Real.exp S
  obtain ⟨N, hN⟩ := exists_nat_gt (D / ε)
  refine ⟨max M₀ (max N 1), fun M hM => ?_⟩
  have hM0 : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hMN : N ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM)
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  rw [Real.dist_eq, ← Matrix.trace_sub]
  have htr : |Matrix.trace (X M ^ M - NormedSpace.exp A)| ≤ D / (M : ℝ) := by
    calc |Matrix.trace (X M ^ M - NormedSpace.exp A)|
        ≤ (Fintype.card n : ℝ) * ‖X M ^ M - NormedSpace.exp A‖ := abs_trace_le_card_mul_opNorm _
      _ ≤ (Fintype.card n : ℝ) * (K * Real.exp S / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (hbound M hM0) (Nat.cast_nonneg _)
      _ = D / (M : ℝ) := by dsimp [D]; ring
  refine htr.trans_lt ?_
  rw [div_lt_iff₀ hMpos]
  have hNlt : D / ε < (M : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hMN)
  have h1 := (div_lt_iff₀ hε).mp hNlt
  linarith

end PowerLimit

/-! ## 2. Real Symmetric Projection Algebra -/

section Projections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma isHermitian_of_transpose_eq {A : Matrix ι ι ℝ} (hA : Aᵀ = A) : A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA

lemma proj_mul_isHermitian {K P : Matrix ι ι ℝ} (hK : Kᵀ = K) (hP : Pᵀ = P) :
    (P * K * P).IsHermitian := by
  apply isHermitian_of_transpose_eq
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hP, hK, Matrix.mul_assoc]

lemma proj_mul_pow {K P : Matrix ι ι ℝ} (hP2 : P * P = P) (hcomm : P * K = K * P) :
    ∀ n : ℕ, 1 ≤ n → (P * K * P) ^ n = P * K ^ n
  | 0, h => by omega
  | 1, _ => by
      rw [pow_one, pow_one, Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hP2]
  | n + 2, _ => by
      have hKnP : K ^ (n + 1) * P = P * K ^ (n + 1) :=
        (Commute.pow_left hcomm.symm (n + 1)).eq
      rw [pow_succ, proj_mul_pow hP2 hcomm (n + 1) (by omega), pow_succ]
      calc P * K ^ (n + 1) * (P * K * P)
          = P * (K ^ (n + 1) * P) * K * P := by simp [Matrix.mul_assoc]
        _ = P * (P * K ^ (n + 1)) * K * P := by rw [hKnP]
        _ = (P * P) * K ^ (n + 1) * K * P := by simp [Matrix.mul_assoc]
        _ = P * K ^ (n + 1) * (K * P) := by rw [hP2]; simp [Matrix.mul_assoc]
        _ = P * K ^ (n + 1) * (P * K) := by rw [← hcomm]
        _ = P * (K ^ (n + 1) * P) * K := by simp [Matrix.mul_assoc]
        _ = P * (P * K ^ (n + 1)) * K := by rw [hKnP]
        _ = (P * P) * K ^ (n + 1) * K := by simp [Matrix.mul_assoc]
        _ = P * (K ^ (n + 1) * K) := by rw [hP2, Matrix.mul_assoc]

/-- Trace of `A^n` equals the sum of `n`-th powers of eigenvalues for any real symmetric matrix `A`. -/
theorem trace_pow_eq_sum_eigenvalues (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (n : ℕ) :
    Matrix.trace (A ^ n) = ∑ i : ι, (hA.eigenvalues i) ^ n := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary.1
  have hU_left : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hU_right : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
    have h := hA.spectral_theorem
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_assoc] using h
  have hpow : ∀ k : ℕ, A ^ k = U * Matrix.diagonal (fun i => (hA.eigenvalues i) ^ k) * Uᵀ := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Matrix.diagonal_one, Matrix.mul_one, hU_right]
    | succ k ih =>
      rw [pow_succ, ih]
      conv_lhs => arg 2; rw [hspec]
      calc U * Matrix.diagonal (fun i => (hA.eigenvalues i) ^ k) * Uᵀ *
              (U * Matrix.diagonal hA.eigenvalues * Uᵀ)
          = U * Matrix.diagonal (fun i => (hA.eigenvalues i) ^ k) * (Uᵀ * U) *
              Matrix.diagonal hA.eigenvalues * Uᵀ := by simp [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i => (hA.eigenvalues i) ^ k) *
              Matrix.diagonal hA.eigenvalues) * Uᵀ := by
              rw [hU_left, Matrix.mul_one]; simp [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i => (hA.eigenvalues i) ^ (k + 1)) * Uᵀ := by
              rw [Matrix.diagonal_mul_diagonal]
              have hfun : (fun i => hA.eigenvalues i ^ k * hA.eigenvalues i) =
                  (fun i => hA.eigenvalues i ^ (k + 1)) := funext fun i => (pow_succ _ _).symm
              rw [hfun]
  rw [hpow n, Matrix.trace_mul_cycle, hU_left, Matrix.one_mul, Matrix.trace_diagonal]

lemma trace_proj_conj_eq {K P₁ P₂ R : Matrix ι ι ℝ}
    (hR_left : Rᵀ * R = 1) (hRK : R * K = K * R) (hRP : R * P₁ * Rᵀ = P₂) (n : ℕ) :
    Matrix.trace (P₂ * K ^ n) = Matrix.trace (P₁ * K ^ n) := by
  have hRKn : R * K ^ n = K ^ n * R := (Commute.pow_right hRK n).eq
  calc Matrix.trace (P₂ * K ^ n)
      = Matrix.trace ((R * P₁) * Rᵀ * K ^ n) := by rw [← hRP]
    _ = Matrix.trace (K ^ n * (R * P₁) * Rᵀ) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Rᵀ * K ^ n * (R * P₁)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Rᵀ * (K ^ n * R) * P₁) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace (Rᵀ * (R * K ^ n) * P₁) := by rw [← hRKn]
    _ = Matrix.trace ((Rᵀ * R) * K ^ n * P₁) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace (K ^ n * P₁) := by rw [hR_left, Matrix.one_mul]
    _ = Matrix.trace (P₁ * K ^ n) := Matrix.trace_mul_comm _ _

lemma trace_sq_eq_sum_entries_sq {K : Matrix ι ι ℝ} (hK : Kᵀ = K) :
    Matrix.trace (K ^ 2) = ∑ x : ι, ∑ y : ι, (K x y) ^ 2 := by
  rw [pow_two, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hxy : K y x = K x y := by
    have := congrFun (congrFun hK x) y
    simpa [Matrix.transpose_apply] using this
  rw [hxy, sq]

lemma trace_proj_sq_le {K P : Matrix ι ι ℝ} (hK : Kᵀ = K) (hP : Pᵀ = P)
    (hP2 : P * P = P) (hcomm : P * K = K * P) :
    Matrix.trace ((P * K * P) ^ 2) ≤ Matrix.trace (K ^ 2) := by
  let Q : Matrix ι ι ℝ := 1 - P
  have hQT : Qᵀ = Q := by dsimp [Q]; rw [Matrix.transpose_sub, Matrix.transpose_one, hP]
  have hQ2 : Q * Q = Q := by
    dsimp [Q]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]
    abel
  have hQcomm : Q * K = K * Q := by
    dsimp [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm]
  have hsum : Matrix.trace ((P * K * P) ^ 2) + Matrix.trace ((Q * K * Q) ^ 2) =
      Matrix.trace (K ^ 2) := by
    rw [proj_mul_pow hP2 hcomm 2 (by omega), proj_mul_pow hQ2 hQcomm 2 (by omega),
      ← Matrix.trace_add, ← Matrix.add_mul]
    have hPQ : P + Q = 1 := by dsimp [Q]; abel
    rw [hPQ, Matrix.one_mul]
  have hQ_nn : 0 ≤ Matrix.trace ((Q * K * Q) ^ 2) := by
    rw [trace_pow_eq_sum_eigenvalues (Q * K * Q) (proj_mul_isHermitian hK hQT) 2]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

end Projections

/-! ## 3. Uniform `ℓ²` Sequential Compactness & Signed Moment-Limit Lemma -/

section L2Compactness

private noncomputable def absGeDec (a b : ℝ) : Bool :=
  @decide (|b| ≤ |a|) (Classical.propDecidable _)

private noncomputable def sortedAbsList {ι : Type*} [Fintype ι] (f : ι → ℝ) : List ℝ :=
  (Finset.univ.toList.map f).mergeSort absGeDec

/-- Sort a finite real family `f : ι → ℝ` by decreasing absolute value and pad with `0` to `ℕ → ℝ`. -/
noncomputable def sortedPad {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℕ → ℝ :=
  fun k => (sortedAbsList f).getD k 0

private lemma sortedAbsList_perm {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (sortedAbsList f).Perm (Finset.univ.toList.map f) :=
  List.mergeSort_perm _ _

private lemma sortedAbsList_length {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (sortedAbsList f).length = Fintype.card ι := by
  rw [(sortedAbsList_perm f).length_eq, List.length_map, Finset.length_toList, Finset.card_univ]

private lemma sortedAbsList_pairwise {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (sortedAbsList f).Pairwise (fun a b => |b| ≤ |a|) := by
  have hp : (sortedAbsList f).Pairwise (fun a b => absGeDec a b = true) :=
    List.pairwise_mergeSort
      (le := absGeDec)
      (trans := fun a b c hab hbc => by
        simp only [absGeDec, decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hbc hab)
      (total := fun a b => by
        simp only [absGeDec, Bool.or_eq_true, decide_eq_true_eq]
        exact le_total |b| |a|)
      _
  exact hp.imp fun h => by simpa [absGeDec] using h

private lemma sortedPad_eq_zero_of_ge {ι : Type*} [Fintype ι] (f : ι → ℝ) {k : ℕ}
    (hk : Fintype.card ι ≤ k) : sortedPad f k = 0 := by
  unfold sortedPad
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sortedAbsList_length]; exact hk)]
  rfl

private lemma sortedPad_antitone_abs {ι : Type*} [Fintype ι] (f : ι → ℝ) {i j : ℕ} (hij : i ≤ j) :
    |sortedPad f j| ≤ |sortedPad f i| := by
  unfold sortedPad
  set L := sortedAbsList f
  have hpair : L.Pairwise (fun a b => |b| ≤ |a|) := sortedAbsList_pairwise f
  by_cases hj : j < L.length
  · have hi : i < L.length := lt_of_le_of_lt hij hj
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp only [Option.getD_some]
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact List.pairwise_iff_getElem.mp hpair i j hi hj hlt
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hj)]
    simp [abs_nonneg]

private lemma list_sum_range_getD_pow (L : List ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range L.length, (L.getD k 0) ^ n) = (L.map (fun x => x ^ n)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, add_comm]

private lemma sortedPad_sum_pow {ι : Type*} [Fintype ι] (f : ι → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (Fintype.card ι), (sortedPad f k) ^ n) = ∑ i : ι, (f i) ^ n := by
  unfold sortedPad
  rw [← sortedAbsList_length f, list_sum_range_getD_pow]
  have hp : ((sortedAbsList f).map (fun x => x ^ n)).Perm ((Finset.univ.toList.map f).map (fun x => x ^ n)) :=
    (sortedAbsList_perm f).map _
  rw [hp.sum_eq, List.map_map]
  change (Finset.univ.toList.map (fun i => (f i) ^ n)).sum = ∑ i : ι, (f i) ^ n
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

private lemma sortedPad_abs_le_sqrt {ι : Type*} [Fintype ι] (f : ι → ℝ) {C : ℝ}
    (hC : ∑ i : ι, (f i) ^ 2 ≤ C) (k : ℕ) :
    |sortedPad f k| ≤ Real.sqrt (C / ((k : ℝ) + 1)) := by
  have hsum_range : ∑ j ∈ Finset.range (k + 1), (sortedPad f j) ^ 2 ≤ C := by
    have hfin : ∑ j ∈ Finset.range (max (k + 1) (Fintype.card ι)), (sortedPad f j) ^ 2 =
        ∑ i : ι, (f i) ^ 2 := by
      rw [← sortedPad_sum_pow f 2]
      refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_).symm
      intro j _ hj
      rw [Finset.mem_range, not_lt] at hj
      rw [sortedPad_eq_zero_of_ge f hj]; norm_num
    have hle : ∑ j ∈ Finset.range (k + 1), (sortedPad f j) ^ 2 ≤
        ∑ j ∈ Finset.range (max (k + 1) (Fintype.card ι)), (sortedPad f j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
        (fun _ _ _ => sq_nonneg _)
    linarith
  have hterm : ((k : ℝ) + 1) * |sortedPad f k| ^ 2 ≤ C := by
    have h1 : ∀ j ∈ Finset.range (k + 1), |sortedPad f k| ^ 2 ≤ (sortedPad f j) ^ 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← sq_abs (sortedPad f j)]
      exact pow_le_pow_left₀ (abs_nonneg _) (sortedPad_antitone_abs f (Nat.lt_succ_iff.mp hj)) 2
    have h2 := Finset.sum_le_sum h1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h2
    linarith
  have hsq : |sortedPad f k| ^ 2 ≤ C / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    linarith
  calc |sortedPad f k| = Real.sqrt (|sortedPad f k| ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ Real.sqrt (C / ((k : ℝ) + 1)) := Real.sqrt_le_sqrt hsq

private lemma tendsto_finset_sum' {α : Type*} (s : Finset α) (u : α → ℕ → ℝ) (l : α → ℝ)
    (h : ∀ a ∈ s, Tendsto (u a) atTop (nhds (l a))) :
    Tendsto (fun j => ∑ a ∈ s, u a j) atTop (nhds (∑ a ∈ s, l a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- **Uniform `ℓ²` Sequential Compactness & Signed Moment-Limit Theorem**:
given finite real families `f M s : ι M → ℝ` (`s : Fin k`) with uniform `ℓ²` bound
`∑ i, (f M s i)^2 ≤ C`, there exist a strictly increasing subsequence `φ : ℕ → ℕ` and
limiting sequences `lam : Fin k → ℕ → ℝ` such that for every `s : Fin k` and every `n ≥ 3`:
1. `Summable (fun i => |lam s i| ^ n)`, and
2. `Tendsto (fun j => ∑ i, (f (φ j) s i) ^ n) atTop (nhds (∑' i, (lam s i) ^ n))`. -/
theorem l2_seq_compact_moments {k : ℕ} {ι : ℕ → Type*} [∀ M, Fintype (ι M)]
    (f : ∀ M, Fin k → ι M → ℝ) {C : ℝ} (hC_nn : 0 ≤ C)
    (hl2 : ∀ M (s : Fin k), ∑ i : ι M, (f M s i) ^ 2 ≤ C) :
    ∃ (φ : ℕ → ℕ) (lam : Fin k → ℕ → ℝ),
      StrictMono φ ∧
      (∀ s n, 3 ≤ n → Summable (fun i => |lam s i| ^ n)) ∧
      (∀ s n, 3 ≤ n →
        Tendsto (fun j => ∑ i : ι (φ j), (f (φ j) s i) ^ n) atTop (nhds (∑' i, (lam s i) ^ n))) := by
  let seq : ℕ → Fin k → ℕ → ℝ := fun M s => sortedPad (f M s)
  let B : ℕ → ℝ := fun i => Real.sqrt (C / ((i : ℝ) + 1))
  let Box : Set (Fin k → ℕ → ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun i => Set.Icc (-B i) (B i)
  have hBox_compact : IsCompact Box :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun i => isCompact_Icc
  have hmem : ∀ M : ℕ, seq M ∈ Box := fun M s _ i _ => by
    exact abs_le.mp (sortedPad_abs_le_sqrt (f M s) (hl2 M s) i)
  rcases hBox_compact.isSeqCompact hmem with ⟨lam, hlam_mem, φ, hφ_mono, hφ_tendsto⟩
  -- Coordinatewise convergence `seq (φ j) s i → lam s i`
  have hcoord : ∀ s i, Tendsto (fun j => seq (φ j) s i) atTop (nhds (lam s i)) := fun s i =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hφ_tendsto s) i
  -- Uniform finite-partial-sum `ℓ²` bound for `lam`
  have hlam_l2_fin : ∀ (s : Fin k) (N : ℕ), ∑ i ∈ Finset.range N, (lam s i) ^ 2 ≤ C := fun s N => by
    have hlim : Tendsto (fun j => ∑ i ∈ Finset.range N, (seq (φ j) s i) ^ 2) atTop
        (nhds (∑ i ∈ Finset.range N, (lam s i) ^ 2)) :=
      tendsto_finset_sum' (Finset.range N) (fun i j => (seq (φ j) s i) ^ 2)
        (fun i => (lam s i) ^ 2) fun i _ => (hcoord s i).pow 2
    refine le_of_tendsto hlim (Eventually.of_forall fun j => ?_)
    have h1 : ∑ i ∈ Finset.range N, (seq (φ j) s i) ^ 2 ≤
        ∑ i ∈ Finset.range (max N (Fintype.card (ι (φ j)))), (seq (φ j) s i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
        (fun _ _ _ => sq_nonneg _)
    have h2 : ∑ i ∈ Finset.range (max N (Fintype.card (ι (φ j)))), (seq (φ j) s i) ^ 2 =
        ∑ i : ι (φ j), (f (φ j) s i) ^ 2 := by
      dsimp [seq]
      rw [← sortedPad_sum_pow (f (φ j) s) 2]
      refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_).symm
      intro m _ hm
      rw [Finset.mem_range, not_lt] at hm
      rw [sortedPad_eq_zero_of_ge _ hm]; norm_num
    linarith [hl2 (φ j) s]
  -- Coordinate bound `|lam s i| ≤ B i`
  have hlam_abs : ∀ s i, |lam s i| ≤ B i := fun s i => abs_le.mpr (hlam_mem s trivial i trivial)
  -- Summability of `|lam s i|^2` and `|lam s i|^n` for `n ≥ 3`
  have hlam_summ2 : ∀ s, Summable (fun i => (lam s i) ^ 2) := fun s =>
    summable_of_sum_range_le (fun _ => sq_nonneg _) (hlam_l2_fin s)
  have hlam_summ_n : ∀ s n, 3 ≤ n → Summable (fun i => |lam s i| ^ n) := fun s n hn => by
    refine Summable.of_nonneg_of_le (fun _ => pow_nonneg (abs_nonneg _) n) (fun i => ?_)
      ((hlam_summ2 s).mul_left (B 0 ^ (n - 2)))
    have hBi_le : B i ≤ B 0 := Real.sqrt_le_sqrt <|
      div_le_div_of_nonneg_left hC_nn (by positivity)
        (by simp only [Nat.cast_zero]; linarith [Nat.cast_nonneg (α := ℝ) i])
    have hpow_split : |lam s i| ^ n = |lam s i| ^ (n - 2) * (lam s i) ^ 2 := by
      rw [← sq_abs (lam s i), ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hpow_split]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) ((hlam_abs s i).trans hBi_le) (n - 2)) (sq_nonneg _)
  -- Uniform tail bound for `seq M s` for `n ≥ 3`
  have htail_seq : ∀ M s n N, 3 ≤ n →
      |(∑ i : ι M, (f M s i) ^ n) - (∑ i ∈ Finset.range N, (seq M s i) ^ n)| ≤
        B N ^ (n - 2) * C := fun M s n N hn => by
    let R := max N (Fintype.card (ι M))
    have hfull : ∑ i : ι M, (f M s i) ^ n = ∑ i ∈ Finset.range R, (seq M s i) ^ n := by
      dsimp [seq]
      rw [← sortedPad_sum_pow (f M s) n]
      refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_
      intro m _ hm
      rw [Finset.mem_range, not_lt] at hm
      rw [sortedPad_eq_zero_of_ge _ hm, zero_pow (by omega)]
    rw [hfull]
    have hdiff : (∑ i ∈ Finset.range R, (seq M s i) ^ n) - (∑ i ∈ Finset.range N, (seq M s i) ^ n) =
        ∑ i ∈ Finset.Ico N R, (seq M s i) ^ n := by
      rw [← Finset.sum_range_add_sum_Ico _ (le_max_left N _)]; ring
    rw [hdiff]
    calc |∑ i ∈ Finset.Ico N R, (seq M s i) ^ n|
        ≤ ∑ i ∈ Finset.Ico N R, |(seq M s i) ^ n| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Ico N R, |seq M s i| ^ (n - 2) * (seq M s i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [abs_pow, ← sq_abs (seq M s i), ← pow_add, Nat.sub_add_cancel (by omega)]
      _ ≤ ∑ i ∈ Finset.Ico N R, B N ^ (n - 2) * (seq M s i) ^ 2 := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hNi : N ≤ i := (Finset.mem_Ico.mp hi).1
            have habs : |seq M s i| ≤ B N :=
              (sortedPad_antitone_abs (f M s) hNi).trans (sortedPad_abs_le_sqrt (f M s) (hl2 M s) N)
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) habs (n - 2)) (sq_nonneg _)
      _ = B N ^ (n - 2) * ∑ i ∈ Finset.Ico N R, (seq M s i) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ B N ^ (n - 2) * C := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
            have hsub : ∑ i ∈ Finset.Ico N R, (seq M s i) ^ 2 ≤
                ∑ i ∈ Finset.range R, (seq M s i) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
                (fun _ _ _ => sq_nonneg _)
            have hR2 : ∑ i ∈ Finset.range R, (seq M s i) ^ 2 = ∑ i : ι M, (f M s i) ^ 2 := by
              dsimp [seq]
              rw [← sortedPad_sum_pow (f M s) 2]
              refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_).symm
              intro m _ hm
              rw [Finset.mem_range, not_lt] at hm
              rw [sortedPad_eq_zero_of_ge _ hm]; norm_num
            linarith [hl2 M s]
  -- Same tail bound for `lam s`
  have htail_lam : ∀ s n N, 3 ≤ n →
      |(∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| ≤
        B N ^ (n - 2) * C := fun s n N hn => by
    have hs_abs : Summable (fun i => |lam s i| ^ n) := hlam_summ_n s n hn
    have hs_pow : Summable (fun i => (lam s i) ^ n) :=
      Summable.of_abs (by simpa only [abs_pow] using hs_abs)
    have hsplit : (∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n) =
        ∑' i : ℕ, (lam s (i + N)) ^ n := by
      rw [← hs_pow.sum_add_tsum_nat_add N]; ring
    rw [hsplit]
    have hs_shift_abs : Summable (fun i => |(lam s (i + N)) ^ n|) := by
      simpa only [abs_pow] using (summable_nat_add_iff N).mpr hs_abs
    have hs_shift_norm : Summable (fun i => ‖(lam s (i + N)) ^ n‖) := by
      simpa only [Real.norm_eq_abs] using hs_shift_abs
    have hs_l2_shift : Summable (fun i => (lam s (i + N)) ^ 2) :=
      (summable_nat_add_iff N).mpr (hlam_summ2 s)
    have hnorm_le : |∑' i, (lam s (i + N)) ^ n| ≤ ∑' i, |(lam s (i + N)) ^ n| := by
      have h := norm_tsum_le_tsum_norm hs_shift_norm
      simpa only [Real.norm_eq_abs] using h
    have htsum_le : ∑' i, |(lam s (i + N)) ^ n| ≤ ∑' i, B N ^ (n - 2) * (lam s (i + N)) ^ 2 := by
      refine hs_shift_abs.tsum_le_tsum (fun i => ?_) (hs_l2_shift.mul_left _)
      rw [abs_pow, show |lam s (i + N)| ^ n = |lam s (i + N)| ^ (n - 2) * (lam s (i + N)) ^ 2 by
        rw [← sq_abs (lam s (i + N)), ← pow_add, Nat.sub_add_cancel (by omega)]]
      have hBN : B (i + N) ≤ B N := Real.sqrt_le_sqrt <|
        div_le_div_of_nonneg_left hC_nn (by positivity) (by push_cast; linarith)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) ((hlam_abs s (i + N)).trans hBN) (n - 2)) (sq_nonneg _)
    have htsum_mul : ∑' i, B N ^ (n - 2) * (lam s (i + N)) ^ 2 =
        B N ^ (n - 2) * ∑' i, (lam s (i + N)) ^ 2 := tsum_mul_left
    have hl2_le : ∑' i, (lam s (i + N)) ^ 2 ≤ C := by
      have h1 := (hlam_summ2 s).sum_add_tsum_nat_add N
      have hnn : 0 ≤ ∑ i ∈ Finset.range N, (lam s i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : ∑' i, (lam s i) ^ 2 ≤ C :=
        (hlam_summ2 s).tsum_le_of_sum_range_le (hlam_l2_fin s)
      linarith
    calc |∑' i, (lam s (i + N)) ^ n|
        ≤ ∑' i, |(lam s (i + N)) ^ n| := hnorm_le
      _ ≤ ∑' i, B N ^ (n - 2) * (lam s (i + N)) ^ 2 := htsum_le
      _ = B N ^ (n - 2) * ∑' i, (lam s (i + N)) ^ 2 := htsum_mul
      _ ≤ B N ^ (n - 2) * C := mul_le_mul_of_nonneg_left hl2_le (pow_nonneg (Real.sqrt_nonneg _) _)
  -- Assemble `ε/3` moment convergence for every `s : Fin k` and `n ≥ 3`
  refine ⟨φ, lam, hφ_mono, hlam_summ_n, fun s n hn => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB_tendsto : Tendsto (fun N : ℕ => B N ^ (n - 2) * C) atTop (nhds 0) := by
    have hdiv : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hsqrt : Tendsto B atTop (nhds 0) := by
      simpa [B, Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hdiv
    have hpow : Tendsto (fun N : ℕ => B N ^ (n - 2)) atTop (nhds 0) := by
      simpa [zero_pow (show n - 2 ≠ 0 by omega)] using hsqrt.pow (n - 2)
    simpa using hpow.mul_const C
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hB_tendsto (ε / 3) (by linarith)
  have htail_lt : B N ^ (n - 2) * C < ε / 3 := by
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    exact h
  have hfin_lim : Tendsto (fun j => ∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) atTop
      (nhds (∑ i ∈ Finset.range N, (lam s i) ^ n)) :=
    tendsto_finset_sum' (Finset.range N) (fun i j => (seq (φ j) s i) ^ n)
      (fun i => (lam s i) ^ n) fun i _ => (hcoord s i).pow n
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hfin_lim (ε / 3) (by linarith)
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq]
  have hmid : |(∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| < ε / 3 := by
    simpa [Real.dist_eq] using hJ j hj
  have h1 := htail_seq (φ j) s n N hn
  have h2 := htail_lam s n N hn
  have hsplit : (∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑' i, (lam s i) ^ n) =
      ((∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n)) +
      ((∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)) -
      ((∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)) := by ring
  rw [hsplit]
  have htri : |((∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n)) +
        ((∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)) -
        ((∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n))| ≤
      |(∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n)| +
      |(∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| +
      |(∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| := by
    calc |((∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n)) +
          ((∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)) -
          ((∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n))|
        ≤ |((∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n)) +
           ((∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n))| +
          |(∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| := abs_sub _ _
      _ ≤ |(∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n)| +
          |(∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| +
          |(∑' i, (lam s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n)| := by
            linarith [abs_add_le
              ((∑ i : ι (φ j), (f (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n))
              ((∑ i ∈ Finset.range N, (seq (φ j) s i) ^ n) - (∑ i ∈ Finset.range N, (lam s i) ^ n))]
  linarith

end L2Compactness

end PurityBootstrap.Spin1Compactness
