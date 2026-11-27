import PurityBootstrap.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# 1D Purity-Bootstrap Uniform Spectral Gap Theorem

Formalizes OpenAI's Proposition `prop:bootstrap` (*The periodic spin-one Haldane gap*,
Section 4, `bootstrap.tex`):
1. Dyadic doubling induction: `S(2^j n₀, 2^j b₀) ≥ 1 - u_j`, `T(2^{j+1} n₀, 2^j b₀) ≥ 1 - u_j`
   with `u_j = C⁻¹ r^{2^j}`.
2. `ℓ^p`-norm interpolation for all intermediate even lengths `n_j ≤ L ≤ 2 n_j`:
   `T(L, b_j) ≥ (T(2 n_j, b_j) * S(n_j, b_j)^2)^{L / (2 n_j)} ≥ (1 - u_j)^3 ≥ 1 - 3 u_j > 1/2`.
3. Unique ground state and uniform spectral gap `γ_L > log(1/r) / b₀` for every even `L ≥ n₀`.
-/

namespace PurityBootstrap

open scoped BigOperators
open Filter Real

/-- Dyadic purity defect sequence `u_j = C⁻¹ * r^(2^j)`. -/
noncomputable def dyadicDefect (C r : ℝ) (j : ℕ) : ℝ :=
  C⁻¹ * r ^ (2 ^ j)

lemma dyadicDefect_zero {C u₀ : ℝ} (hC : C ≠ 0) :
    dyadicDefect C (C * u₀) 0 = u₀ := by
  unfold dyadicDefect
  simp only [pow_zero, pow_one]
  field_simp [hC]

lemma dyadicDefect_succ {C r : ℝ} (hC : C ≠ 0) (j : ℕ) :
    dyadicDefect C r (j + 1) = C * (dyadicDefect C r j) ^ 2 := by
  unfold dyadicDefect
  have hexp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
  rw [hexp, pow_add]
  field_simp [hC]

lemma dyadicDefect_pos {C r : ℝ} (hC : 0 < C) (hr : 0 < r) (j : ℕ) :
    0 < dyadicDefect C r j := by
  unfold dyadicDefect
  positivity

lemma dyadicDefect_le_u0 {C u₀ : ℝ} (hC : 0 < C) (hu0 : 0 < u₀) (hr : C * u₀ < 1) :
    ∀ j, dyadicDefect C (C * u₀) j ≤ u₀ := by
  intro j
  induction j with
  | zero => rw [dyadicDefect_zero hC.ne']
  | succ j ih =>
    rw [dyadicDefect_succ hC.ne']
    have hpos : 0 < dyadicDefect C (C * u₀) j := dyadicDefect_pos hC (mul_pos hC hu0) j
    have hCu : C * dyadicDefect C (C * u₀) j ≤ C * u₀ := mul_le_mul_of_nonneg_left ih hC.le
    calc C * dyadicDefect C (C * u₀) j ^ 2
        = (C * dyadicDefect C (C * u₀) j) * dyadicDefect C (C * u₀) j := by ring
      _ ≤ 1 * u₀ := by nlinarith
      _ = u₀ := one_mul u₀

/-- Dyadic doubling induction (`eq:dyadic-purities`):
if `S(n₀, b₀) ≥ 1 - u₀` and `T(2n₀, b₀) ≥ 1 - u₀`, then for all `j : ℕ`,
both defects at `(2^j n₀, 2^j b₀)` are at most `u_j = C⁻¹ * (C u₀)^(2^j)`. -/
theorem PuritySystem1D.dyadic_purities (sys : PuritySystem1D)
    {n₀ : ℕ} {b₀ u₀ C : ℝ}
    (hn₀ : Even n₀) (h4 : 4 ≤ n₀) (hb₀ : 0 < b₀)
    (hu0_pos : 0 < u₀) (hu0_lt : u₀ < 1 / 6)
    (hGC : bootstrapCoeff u₀ ≤ C) (hr_lt : C * u₀ < 1)
    (hS0 : 1 - sys.S n₀ b₀ ≤ u₀) (hT0 : 1 - sys.T (2 * n₀) b₀ ≤ u₀) :
    ∀ j : ℕ,
      1 - sys.S (2 ^ j * n₀) (2 ^ j * b₀) ≤ dyadicDefect C (C * u₀) j ∧
      1 - sys.T (2 * (2 ^ j * n₀)) (2 ^ j * b₀) ≤ dyadicDefect C (C * u₀) j := by
  have hC_pos : 0 < C := by
    have hG_pos : 0 < bootstrapCoeff u₀ := by
      unfold bootstrapCoeff
      have h1 : 0 < 1 - u₀ := by linarith
      positivity
    linarith
  have hr_pos : 0 < C * u₀ := mul_pos hC_pos hu0_pos
  intro j
  induction j with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_one]
    rw [dyadicDefect_zero hC_pos.ne']
    exact ⟨hS0, hT0⟩
  | succ j ih =>
    rcases ih with ⟨ihS, ihT⟩
    set n := 2 ^ j * n₀
    set b := (2 : ℝ) ^ j * b₀
    set u := dyadicDefect C (C * u₀) j
    set u' := dyadicDefect C (C * u₀) (j + 1)
    have hn_even : Even n := by
      rcases hn₀ with ⟨k, hk⟩
      exact ⟨2 ^ j * k, by dsimp [n]; rw [hk]; ring⟩
    have hn4 : 4 ≤ n := by
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      dsimp [n]; nlinarith
    have hb_pos : 0 < b := by dsimp [b]; positivity
    have hu_pos : 0 < u := dyadicDefect_pos hC_pos hr_pos j
    have hu_le : u ≤ u₀ := dyadicDefect_le_u0 hC_pos hu0_pos hr_lt j
    have hu_lt1 : u < 1 := by linarith
    have hu'_eq : u' = C * u ^ 2 := dyadicDefect_succ hC_pos.ne' j
    have hu'_le_u : u' ≤ u := by
      rw [hu'_eq]
      have : C * u ≤ C * u₀ := mul_le_mul_of_nonneg_left hu_le hC_pos.le
      nlinarith
    have hu'_lt1 : u' < 1 := by linarith
    have hGu_le_C : bootstrapCoeff u ≤ C :=
      (bootstrapCoeff_mono hu_le (by linarith)).trans hGC
    have hstep1 : purityUpdate (1 - (1 - u) ^ 2 * (1 - u)) ≤ u' := by
      have hcube : (1 - u) ^ 2 * (1 - u) = (1 - u) ^ 3 := by ring
      rw [hcube, purityUpdate_one_sub_cube (by linarith), hu'_eq]
      exact mul_le_mul_of_nonneg_right hGu_le_C (sq_nonneg u)
    have hstep2 : purityUpdate (1 - (1 - u) ^ 2 * (1 - u')) ≤ u' := by
      have hmono : purityUpdate (1 - (1 - u) ^ 2 * (1 - u')) ≤
          purityUpdate (1 - (1 - u) ^ 2 * (1 - u)) := by
        refine purityUpdate_mono ?_ ?_ ?_
        · have h1mu : 0 ≤ 1 - u := by linarith
          have h1mu' : 0 ≤ 1 - u' := by linarith
          have : (1 - u) ^ 2 * (1 - u') ≤ 1 := by
            have h1 : (1 - u) ^ 2 ≤ 1 := by nlinarith
            have h2 : 1 - u' ≤ 1 := by linarith [dyadicDefect_pos hC_pos hr_pos (j + 1)]
            nlinarith
          linarith
        · have h1mu2 : 0 ≤ (1 - u) ^ 2 := sq_nonneg (1 - u)
          nlinarith
        · have h1mu : 0 < 1 - u := by linarith
          nlinarith [pow_pos h1mu 2]
      exact hmono.trans hstep1
    have hupd := sys.rounded_coupled_update hn_even hn4 hb_pos
      hu_pos.le hu_lt1 hu_pos.le hu_lt1 hu'_lt1 ihS ihT hstep1 hstep2
    have h2n : 2 ^ (j + 1) * n₀ = 2 * n := by dsimp [n]; ring
    have h4n : 2 * (2 ^ (j + 1) * n₀) = 4 * n := by dsimp [n]; ring
    have h2b : (2 : ℝ) ^ (j + 1) * b₀ = 2 * b := by dsimp [b]; ring
    rw [h4n, h2n, h2b]
    exact hupd

/-- `ℓ^p`-norm monotonicity for countable nonnegative series:
if `a_i ≥ 0`, `∑' i, a_i ^ p = S > 0` (summable), and `0 < p ≤ q`, then
`∑' i, a_i ^ q ≤ S ^ (q / p)`. -/
theorem tsum_rpow_le_rpow_div {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hsum : Summable (fun i => a i ^ p)) (hpos : 0 < ∑' i, a i ^ p) :
    Summable (fun i => a i ^ q) ∧
    ∑' i, a i ^ q ≤ (∑' i, a i ^ p) ^ (q / p) := by
  set S := ∑' i, a i ^ p
  have hr : 1 ≤ q / p := (one_le_div hp).mpr hpq
  have hterm : ∀ i, a i ^ q ≤ S ^ (q / p - 1) * a i ^ p := by
    intro i
    have hleS : a i ^ p ≤ S := hsum.le_tsum i (fun j _ => Real.rpow_nonneg (ha j) p)
    have hnorm_le1 : a i ^ p / S ≤ 1 := (div_le_one hpos).mpr hleS
    have hnorm_nn : 0 ≤ a i ^ p / S := div_nonneg (Real.rpow_nonneg (ha i) p) hpos.le
    have hrpow_le : (a i ^ p / S) ^ (q / p) ≤ a i ^ p / S :=
      Real.rpow_le_self_of_le_one hnorm_nn hnorm_le1 hr
    have hdiv_rpow : (a i ^ p / S) ^ (q / p) = a i ^ q / S ^ (q / p) := by
      rw [Real.div_rpow (Real.rpow_nonneg (ha i) p) hpos.le,
        ← Real.rpow_mul (ha i), mul_div_cancel₀ _ hp.ne']
    rw [hdiv_rpow] at hrpow_le
    have hSqp_pos : 0 < S ^ (q / p) := Real.rpow_pos_of_pos hpos _
    have hmul : a i ^ q ≤ (a i ^ p / S) * S ^ (q / p) := (div_le_iff₀ hSqp_pos).mp hrpow_le
    have hpow_sub : S ^ (q / p) / S = S ^ (q / p - 1) := by
      rw [Real.rpow_sub hpos, Real.rpow_one]
    calc a i ^ q ≤ (a i ^ p / S) * S ^ (q / p) := hmul
      _ = (S ^ (q / p) / S) * a i ^ p := by ring
      _ = S ^ (q / p - 1) * a i ^ p := by rw [hpow_sub]
  have hsum_q : Summable (fun i => a i ^ q) :=
    Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (ha i) q) hterm (hsum.mul_left _)
  refine ⟨hsum_q, ?_⟩
  calc ∑' i, a i ^ q
      ≤ ∑' i, S ^ (q / p - 1) * a i ^ p := hsum_q.tsum_le_tsum hterm (hsum.mul_left _)
    _ = S ^ (q / p - 1) * S := by rw [tsum_mul_left]
    _ = S ^ (q / p) := by
        rw [Real.rpow_sub hpos, Real.rpow_one, div_mul_cancel₀ _ hpos.ne']

/-- Purity interpolation for intermediate even lengths `n ≤ L ≤ 2n`
(OpenAI Eq. `eq:purity-interpolation`):
if `Z L b ≤ Z n b ^ (L / n)` and `Z (2n) (2b) ^ (L / (2n)) ≤ Z L (2b)`, then
`T(L, b) ≥ (T(2n, b) * S(n, b)^2) ^ (L / (2n))`. -/
theorem purity_interpolation {Z_nb Z_2nb Z_2n2b Z_Lb Z_L2b : ℝ}
    {n L : ℕ} (hn : 0 < n)
    (hZnb : 0 < Z_nb) (hZ2nb : 0 < Z_2nb) (hZ2n2b : 0 < Z_2n2b) (hZLb : 0 < Z_Lb)
    (hUpper : Z_Lb ≤ Z_nb ^ ((L : ℝ) / (n : ℝ)))
    (hLower : Z_2n2b ^ ((L : ℝ) / (2 * (n : ℝ))) ≤ Z_L2b) :
    ((Z_2n2b / Z_2nb ^ 2) * (Z_2nb / Z_nb ^ 2) ^ 2) ^ ((L : ℝ) / (2 * (n : ℝ))) ≤
      Z_L2b / Z_Lb ^ 2 := by
  have hident : (Z_2n2b / Z_2nb ^ 2) * (Z_2nb / Z_nb ^ 2) ^ 2 = Z_2n2b / Z_nb ^ 4 := by
    field_simp [hZ2nb.ne', hZnb.ne']
  rw [hident]
  have hden : Z_Lb ^ 2 ≤ (Z_nb ^ 4) ^ ((L : ℝ) / (2 * (n : ℝ))) := by
    have hsq : Z_Lb ^ 2 ≤ (Z_nb ^ ((L : ℝ) / (n : ℝ))) ^ 2 := by nlinarith
    have hpow : (Z_nb ^ ((L : ℝ) / (n : ℝ))) ^ 2 = (Z_nb ^ 4) ^ ((L : ℝ) / (2 * (n : ℝ))) := by
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [← Real.rpow_natCast (Z_nb ^ ((L : ℝ) / (n : ℝ))) 2, ← Real.rpow_mul hZnb.le,
        ← Real.rpow_natCast Z_nb 4, ← Real.rpow_mul hZnb.le]
      congr 1
      push_cast
      field_simp [hn0]
      ring
    linarith
  rw [Real.div_rpow hZ2n2b.le (pow_nonneg hZnb.le 4)]
  have hden_pos : 0 < (Z_nb ^ 4) ^ ((L : ℝ) / (2 * (n : ℝ))) :=
    Real.rpow_pos_of_pos (pow_pos hZnb 4) _
  rw [div_le_div_iff₀ hden_pos (pow_pos hZLb 2)]
  have h1 : 0 ≤ Z_2n2b ^ ((L : ℝ) / (2 * (n : ℝ))) := Real.rpow_nonneg hZ2n2b.le _
  exact mul_le_mul hLower hden (pow_nonneg hZLb.le 2) (le_trans h1 hLower)

/-- Bernoulli's inequality for cubes: `1 - 3 u ≤ (1 - u)^3` for `u ≥ 0` and `u ≤ 1/3`
(in fact for all `0 ≤ u ≤ 1`!). -/
lemma one_sub_three_mul_le_cube {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - 3 * u ≤ (1 - u) ^ 3 := by
  have : (1 - u) ^ 3 - (1 - 3 * u) = u ^ 2 * (3 - u) := by ring
  nlinarith [sq_nonneg u]

/-- From a physical Gibbs purity `T > 1 - δ` (`δ < 1/2`), deduce:
1. Ground-state weight `w₀ ≥ T > 1/2` (hence the ground state is **unique**!).
2. For any distinct excited energy `E₁ > E₀`, `exp (-b * (E₁ - E₀)) ≤ δ / (1 - δ)`. -/
theorem gibbs_purity_implies_unique_ground_and_gap {d : ℕ}
    (E : Fin d → ℝ) (k₀ : Fin d) (b : ℝ) (hb : 0 < b)
    (hmin : ∀ k, E k₀ ≤ E k)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hT : 1 - δ ≤ (∑ k : Fin d, Real.exp (-2 * b * E k)) /
        (∑ k : Fin d, Real.exp (-b * E k)) ^ 2) :
    (∀ k : Fin d, E k = E k₀ → k = k₀) ∧
    (∀ k : Fin d, k ≠ k₀ → Real.exp (-b * (E k - E k₀)) ≤ δ / (1 - δ)) := by
  set Z := ∑ k : Fin d, Real.exp (-b * E k)
  have hZ_pos : 0 < Z := by
    have hk₀ : 0 < Real.exp (-b * E k₀) := Real.exp_pos _
    have hle : Real.exp (-b * E k₀) ≤ Z :=
      Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k₀)
    linarith
  let w : Fin d → ℝ := fun k => Real.exp (-b * E k) / Z
  have hw_pos : ∀ k, 0 < w k := fun k => div_pos (Real.exp_pos _) hZ_pos
  have hw_sum : ∑ k : Fin d, w k = 1 := by
    dsimp [w]
    rw [← Finset.sum_div, div_self hZ_pos.ne']
  have hw_max : ∀ k, w k ≤ w k₀ := fun k => by
    dsimp [w]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hmin k])) hZ_pos.le
  have hT_eq : (∑ k : Fin d, Real.exp (-2 * b * E k)) / Z ^ 2 = ∑ k : Fin d, w k ^ 2 := by
    dsimp [w]
    simp_rw [div_pow, ← Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hT_eq] at hT
  have hw0_ge : 1 - δ ≤ w k₀ := by
    calc 1 - δ ≤ ∑ k : Fin d, w k ^ 2 := hT
      _ ≤ ∑ k : Fin d, w k₀ * w k := Finset.sum_le_sum fun k _ => by
            have := hw_max k; have := (hw_pos k).le; nlinarith
      _ = w k₀ * ∑ k : Fin d, w k := by rw [← Finset.mul_sum]
      _ = w k₀ := by rw [hw_sum, mul_one]
  -- 1. Uniqueness of ground state
  have huniq : ∀ k : Fin d, E k = E k₀ → k = k₀ := by
    intro k hEk
    by_contra hne
    have hwk : w k = w k₀ := by dsimp [w]; rw [hEk]
    have hpair : w k₀ + w k ≤ ∑ j : Fin d, w j := by
      have hsub : ({k₀, k} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := w) (fun j _ _ => (hw_pos j).le)
      rwa [Finset.sum_pair (Ne.symm hne)] at this
    rw [hw_sum, hwk] at hpair
    linarith
  -- 2. Exponential gap ratio bound
  have hgap : ∀ k : Fin d, k ≠ k₀ → Real.exp (-b * (E k - E k₀)) ≤ δ / (1 - δ) := by
    intro k hne
    have hratio : Real.exp (-b * (E k - E k₀)) = w k / w k₀ := by
      dsimp [w]
      rw [div_div_div_cancel_right₀ hZ_pos.ne', ← Real.exp_sub]
      congr 1; ring
    rw [hratio]
    have hpair : w k₀ + w k ≤ 1 := by
      have hsub : ({k₀, k} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := w) (fun j _ _ => (hw_pos j).le)
      rwa [Finset.sum_pair (Ne.symm hne), hw_sum] at this
    have hwk_le : w k ≤ δ := by linarith
    have h1mδ : 0 < 1 - δ := by linarith
    have hw0_pos : 0 < w k₀ := by linarith
    rw [div_le_div_iff₀ hw0_pos h1mδ]
    nlinarith
  exact ⟨huniq, hgap⟩

/-- Clean dyadic interval covering via `Nat.log 2 (L / n₀)` — works for ALL `L ≥ n₀ > 0`! -/
theorem exists_dyadic_interval_exact {n₀ L : ℕ} (hn₀ : 0 < n₀) (hL : n₀ ≤ L) :
    ∃ j : ℕ, 2 ^ j * n₀ ≤ L ∧ L < 2 * (2 ^ j * n₀) := by
  let q := L / n₀
  have hq : 0 < q := Nat.div_pos hL hn₀
  let j := Nat.log 2 q
  refine ⟨j, ?_, ?_⟩
  · have h1 : 2 ^ j ≤ q := Nat.pow_log_le_self 2 hq.ne'
    calc 2 ^ j * n₀ ≤ q * n₀ := Nat.mul_le_mul_right n₀ h1
      _ ≤ L := Nat.div_mul_le_self L n₀
  · have h2 : q < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have h3 : q + 1 ≤ 2 ^ (j + 1) := h2
    have h4 : L < (q + 1) * n₀ := by
      have := Nat.lt_mul_div_succ L hn₀
      simpa [q, Nat.mul_comm] using this
    calc L < (q + 1) * n₀ := h4
      _ ≤ 2 ^ (j + 1) * n₀ := Nat.mul_le_mul_right n₀ h3
      _ = 2 * (2 ^ j * n₀) := by ring

/-- Master 1D Uniform Spectral Gap Theorem (OpenAI Proposition `prop:bootstrap`):
for any 1D partition function system with Hermitian spatial transfer moments and
finite-dimensional physical spectra satisfying the initial purity bounds
`S(n₀, b₀) ≥ 1 - u₀` and `T(2n₀, b₀) ≥ 1 - u₀`, every even length `L ≥ n₀` has:
1. A **unique** physical ground state;
2. A **uniform** spectral gap `E_k(L) - E_0(L) > log(1 / r) / b₀` for all `k ≠ k₀`! -/
theorem uniform_gap_from_purities
    (sys : PuritySystem1D)
    (hInterp : ∀ (n L : ℕ) (b : ℝ), Even n → 4 ≤ n → Even L → n ≤ L → L ≤ 2 * n → 0 < b →
      sys.Z L b ≤ sys.Z n b ^ ((L : ℝ) / (n : ℝ)) ∧
      sys.Z (2 * n) (2 * b) ^ ((L : ℝ) / (2 * (n : ℝ))) ≤ sys.Z L (2 * b))
    {n₀ : ℕ} {b₀ u₀ C : ℝ}
    (hn₀ : Even n₀) (h4 : 4 ≤ n₀) (hb₀ : 0 < b₀)
    (hu0_pos : 0 < u₀) (hu0_lt : u₀ < 1 / 6)
    (hGC : bootstrapCoeff u₀ ≤ C) (hr_lt : C * u₀ < 1)
    (hC_margin : 3 < C * (1 - 3 * u₀))
    (hS0 : 1 - sys.S n₀ b₀ ≤ u₀) (hT0 : 1 - sys.T (2 * n₀) b₀ ≤ u₀)
    {L d : ℕ} (hL_even : Even L) (hL_ge : n₀ ≤ L)
    (E : Fin d → ℝ) (k₀ : Fin d) (hmin : ∀ k, E k₀ ≤ E k)
    (hGibbs : ∀ b, 0 < b → sys.Z L b = ∑ k : Fin d, Real.exp (-b * E k)) :
    (∀ k : Fin d, E k = E k₀ → k = k₀) ∧
    (∀ k : Fin d, k ≠ k₀ → Real.log (1 / (C * u₀)) / b₀ < E k - E k₀) := by
  have hC_pos : 0 < C := by
    have hG_pos : 0 < bootstrapCoeff u₀ := by
      unfold bootstrapCoeff
      have : 0 < 1 - u₀ := by linarith
      positivity
    linarith
  have hr_pos : 0 < C * u₀ := mul_pos hC_pos hu0_pos
  rcases exists_dyadic_interval_exact (by omega : 0 < n₀) hL_ge with ⟨j, hj_lo, hj_hi⟩
  set nj := 2 ^ j * n₀
  set bj := (2 : ℝ) ^ j * b₀
  set uj := dyadicDefect C (C * u₀) j
  have hnj_even : Even nj := by
    rcases hn₀ with ⟨m, hm⟩
    exact ⟨2 ^ j * m, by dsimp [nj]; rw [hm]; ring⟩
  have hnj4 : 4 ≤ nj := by
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    dsimp [nj]; nlinarith
  have hbj_pos : 0 < bj := by dsimp [bj]; positivity
  have hdyad := sys.dyadic_purities hn₀ h4 hb₀ hu0_pos hu0_lt hGC hr_lt hS0 hT0 j
  have huj_pos : 0 < uj := dyadicDefect_pos hC_pos hr_pos j
  have huj_le : uj ≤ u₀ := dyadicDefect_le_u0 hC_pos hu0_pos hr_lt j
  have h3uj_lt : 3 * uj < 1 / 2 := by linarith
  -- Interpolate T(L, b_j) ≥ (1 - u_j)^3 ≥ 1 - 3 u_j
  rcases hInterp nj L bj hnj_even hnj4 hL_even hj_lo hj_hi.le hbj_pos with ⟨hUp, hLo⟩
  have h2nj : Even (2 * nj) := even_two_mul nj
  have hTint := purity_interpolation (by omega : 0 < nj)
    (sys.Z_pos nj bj hnj_even hnj4 hbj_pos)
    (sys.Z_pos (2 * nj) bj h2nj (by omega) hbj_pos)
    (sys.Z_pos (2 * nj) (2 * bj) h2nj (by omega) (by linarith))
    (sys.Z_pos L bj hL_even (by omega) hbj_pos)
    hUp hLo
  have hprod_ge : (1 - uj) ^ 3 ≤
      (sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
      (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2 := by
    have hSj : 1 - uj ≤ sys.S nj bj := by linarith [hdyad.1]
    have hTj : 1 - uj ≤ sys.T (2 * nj) bj := by linarith [hdyad.2]
    have h1m : 0 ≤ 1 - uj := by linarith
    have hsq : (1 - uj) ^ 2 ≤ sys.S nj bj ^ 2 := by nlinarith
    have := mul_le_mul hTj hsq (sq_nonneg _) (by linarith)
    have hcube : (1 - uj) * (1 - uj) ^ 2 = (1 - uj) ^ 3 := by ring
    simpa [PuritySystem1D.S, PuritySystem1D.T, hcube] using this
  have hprod_le1 :
      (sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
      (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2 ≤ 1 := by
    have hS1 : sys.S nj bj ≤ 1 := sys.S_le_one nj bj hnj_even hnj4 hbj_pos
    have hT1 : sys.T (2 * nj) bj ≤ 1 := sys.T_le_one (2 * nj) bj h2nj (by omega) hbj_pos
    have hS0' : 0 ≤ sys.S nj bj := (sys.S_pos hnj_even hnj4 hbj_pos).le
    have hT0' : 0 ≤ sys.T (2 * nj) bj := (sys.T_pos h2nj (by omega) hbj_pos).le
    have hsq : sys.S nj bj ^ 2 ≤ 1 := by nlinarith
    simpa [PuritySystem1D.S, PuritySystem1D.T] using
      mul_le_mul hT1 hsq (sq_nonneg _) zero_le_one
  have hexp_le1 : (L : ℝ) / (2 * (nj : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : L ≤ 2 * nj := hj_hi.le
    exact_mod_cast this
  have hprod_pos : 0 < (sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
      (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2 :=
    lt_of_lt_of_le (pow_pos (by linarith : 0 < 1 - uj) 3) hprod_ge
  have hTL_ge : 1 - 3 * uj ≤ sys.Z L (2 * bj) / sys.Z L bj ^ 2 := by
    have hpow_ge : (sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
        (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2 ≤
        ((sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
        (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2) ^ ((L : ℝ) / (2 * (nj : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_ge hprod_pos hprod_le1 hexp_le1 |> fun h => by
        simpa [Real.rpow_one] using h
    calc 1 - 3 * uj
        ≤ (1 - uj) ^ 3 := one_sub_three_mul_le_cube huj_pos.le (by linarith)
      _ ≤ (sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
            (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2 := hprod_ge
      _ ≤ ((sys.Z (2 * nj) (2 * bj) / sys.Z (2 * nj) bj ^ 2) *
            (sys.Z (2 * nj) bj / sys.Z nj bj ^ 2) ^ 2) ^ ((L : ℝ) / (2 * (nj : ℝ))) := hpow_ge
      _ ≤ sys.Z L (2 * bj) / sys.Z L bj ^ 2 := hTint
  -- Rewrite Z(L, bj) and Z(L, 2*bj) via Gibbs trace
  have hGibbs_bj := hGibbs bj hbj_pos
  have hGibbs_2bj : sys.Z L (2 * bj) = ∑ k : Fin d, Real.exp (-2 * bj * E k) := by
    rw [hGibbs (2 * bj) (by linarith)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring
  rw [hGibbs_bj, hGibbs_2bj] at hTL_ge
  rcases gibbs_purity_implies_unique_ground_and_gap E k₀ bj hbj_pos hmin
    (by linarith : 0 ≤ 3 * uj) h3uj_lt hTL_ge with ⟨huniq, hgap⟩
  refine ⟨huniq, fun k hne => ?_⟩
  have hratio_lt : 3 * uj / (1 - 3 * uj) < (C * u₀) ^ (2 ^ j) := by
    have h1m_pos : 0 < 1 - 3 * uj := by linarith
    have h1m_ge : 1 - 3 * u₀ ≤ 1 - 3 * uj := by linarith
    rw [div_lt_iff₀ h1m_pos]
    have hrpow_pos : 0 < (C * u₀) ^ (2 ^ j) := pow_pos hr_pos _
    have h3uj_eq : 3 * uj = (3 / C) * (C * u₀) ^ (2 ^ j) := by
      dsimp [uj, dyadicDefect]; ring
    have h3C : 3 / C < 1 - 3 * u₀ := (div_lt_iff₀ hC_pos).mpr (by linarith)
    have hlt := mul_lt_mul_of_pos_right (lt_of_lt_of_le h3C h1m_ge) hrpow_pos
    linarith
  have hexp_lt : Real.exp (-bj * (E k - E k₀)) < (C * u₀) ^ (2 ^ j) :=
    lt_of_le_of_lt (hgap k hne) hratio_lt
  have hlog_lt : -bj * (E k - E k₀) < (2 ^ j : ℕ) * Real.log (C * u₀) := by
    have := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp, Real.log_pow] at this
  have hlog_inv : Real.log (1 / (C * u₀)) = -Real.log (C * u₀) := by
    rw [one_div, Real.log_inv]
  rw [hlog_inv, div_lt_iff₀ hb₀]
  have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hbj_eq : bj = (2 : ℝ) ^ j * b₀ := rfl
  rw [hbj_eq, Nat.cast_pow, Nat.cast_ofNat] at hlog_lt
  nlinarith

/-! ## Concrete 1D Spectral Constructor (`SpectralSystem1D`)

Derives `PuritySystem1D`, both halves of `hInterp`, monotonicity of spatial purity in even length,
and the shifted-energy uniform spectral gap directly from a spatial transfer spectrum
`spatialEig b : ℕ → ℝ` and a finite nonempty physical spectrum `E L : Fin (d L) → ℝ`. -/

/-- Concrete 1D spectral family sharing a common shifted partition function
`Z L b = ∑' i, |spatialEig b i|^L = ∑ k : Fin (d L), exp (-b * (E L k + a * L))`. -/
structure SpectralSystem1D where
  spatialEig : ℝ → ℕ → ℝ
  spatial_summable : ∀ b, 0 < b → Summable (fun i => |spatialEig b i| ^ (4 : ℕ))
  d : ℕ → ℕ
  d_pos : ∀ L, Even L → 4 ≤ L → 0 < d L
  E : ∀ L, Fin (d L) → ℝ
  a : ℝ
  Z_eq : ∀ L b, Even L → 4 ≤ L → 0 < b →
    ∑' i, |spatialEig b i| ^ L = ∑ k : Fin (d L), Real.exp (-b * (E L k + a * (L : ℝ)))

namespace SpectralSystem1D

/-- Partition function `Z L b = ∑' i, |spatialEig b i|^L`. -/
noncomputable def Z (sys : SpectralSystem1D) (L : ℕ) (b : ℝ) : ℝ :=
  ∑' i, |sys.spatialEig b i| ^ L

lemma Z_pos (sys : SpectralSystem1D) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) : 0 < sys.Z L b := by
  unfold Z
  rw [sys.Z_eq L b hL h4 hb]
  let k0 : Fin (sys.d L) := ⟨0, sys.d_pos L hL h4⟩
  have hpos : 0 < Real.exp (-b * (sys.E L k0 + sys.a * (L : ℝ))) := Real.exp_pos _
  have hle : Real.exp (-b * (sys.E L k0 + sys.a * (L : ℝ))) ≤
      ∑ k : Fin (sys.d L), Real.exp (-b * (sys.E L k + sys.a * (L : ℝ))) :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k0)
  linarith

lemma spatial_summable_of_ge (sys : SpectralSystem1D) {L : ℕ} {b : ℝ}
    (h4 : 4 ≤ L) (hb : 0 < b) : Summable (fun i => |sys.spatialEig b i| ^ L) := by
  have hsum4 : Summable (fun i => |sys.spatialEig b i| ^ (4 : ℝ)) := by
    simpa [Real.rpow_natCast] using sys.spatial_summable b hb
  have hpos4 : 0 < ∑' i, |sys.spatialEig b i| ^ (4 : ℝ) := by
    simpa [Z, Real.rpow_natCast] using sys.Z_pos ⟨2, rfl⟩ le_rfl hb
  have h := (tsum_rpow_le_rpow_div (fun i => |sys.spatialEig b i|) (fun _ => abs_nonneg _)
    (p := (4 : ℝ)) (q := (L : ℝ)) (by norm_num) (by exact_mod_cast h4) hsum4 hpos4).1
  simpa [Real.rpow_natCast] using h

lemma Z_rpow_le (sys : SpectralSystem1D) {n L : ℕ} {b : ℝ}
    (hn : Even n) (hn4 : 4 ≤ n) (hnL : n ≤ L) (hb : 0 < b) :
    sys.Z L b ≤ sys.Z n b ^ ((L : ℝ) / (n : ℝ)) := by
  have hsum_n : Summable (fun i => |sys.spatialEig b i| ^ (n : ℝ)) := by
    simpa [Real.rpow_natCast] using sys.spatial_summable_of_ge hn4 hb
  have hpos_n : 0 < ∑' i, |sys.spatialEig b i| ^ (n : ℝ) := by
    simpa [Z, Real.rpow_natCast] using sys.Z_pos hn hn4 hb
  have h := (tsum_rpow_le_rpow_div (fun i => |sys.spatialEig b i|) (fun _ => abs_nonneg _)
    (p := (n : ℝ)) (q := (L : ℝ)) (by positivity) (by exact_mod_cast hnL) hsum_n hpos_n).2
  simpa [Z, Real.rpow_natCast] using h

/-- Automatic `hInterp` proof for any `SpectralSystem1D`. -/
theorem interp (sys : SpectralSystem1D) :
    ∀ (n L : ℕ) (b : ℝ), Even n → 4 ≤ n → Even L → n ≤ L → L ≤ 2 * n → 0 < b →
      sys.Z L b ≤ sys.Z n b ^ ((L : ℝ) / (n : ℝ)) ∧
      sys.Z (2 * n) (2 * b) ^ ((L : ℝ) / (2 * (n : ℝ))) ≤ sys.Z L (2 * b) := by
  intro n L b hn hn4 hL hnL hL2n hb
  refine ⟨sys.Z_rpow_le hn hn4 hnL hb, ?_⟩
  have h2b : 0 < 2 * b := by linarith
  have hL4 : 4 ≤ L := le_trans hn4 hnL
  have hUp := sys.Z_rpow_le hL hL4 hL2n h2b
  have hZ2n_nn : 0 ≤ sys.Z (2 * n) (2 * b) := (sys.Z_pos (even_two_mul n) (by omega) h2b).le
  have hZL_pos : 0 < sys.Z L (2 * b) := sys.Z_pos hL hL4 h2b
  have hexp_nn : 0 ≤ (L : ℝ) / (2 * (n : ℝ)) := by positivity
  have hpow := Real.rpow_le_rpow hZ2n_nn hUp hexp_nn
  have hcancel :
      (sys.Z L (2 * b) ^ (((2 * n : ℕ) : ℝ) / (L : ℝ))) ^ ((L : ℝ) / (2 * (n : ℝ))) =
        sys.Z L (2 * b) := by
    rw [← Real.rpow_mul hZL_pos.le]
    have hL0 : (L : ℝ) ≠ 0 := by positivity
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have h1 : (((2 * n : ℕ) : ℝ) / (L : ℝ)) * ((L : ℝ) / (2 * (n : ℝ))) = 1 := by
      push_cast; field_simp [hL0, hn0]
    rw [h1, Real.rpow_one]
  rwa [hcancel] at hpow

/-- Automatic construction of `PuritySystem1D` from `SpectralSystem1D`. -/
noncomputable def toPuritySystem1D (sys : SpectralSystem1D) : PuritySystem1D where
  Z := sys.Z
  Z_pos := fun n b hn h4 hb => sys.Z_pos hn h4 hb
  S_le_one := fun n b hn h4 hb => by
    have hZpos : 0 < sys.Z n b := sys.Z_pos hn h4 hb
    let w : ℕ → ℝ := fun i => |sys.spatialEig b i| ^ n / sys.Z n b
    have hw_nn : ∀ i, 0 ≤ w i := fun i => div_nonneg (pow_nonneg (abs_nonneg _) n) hZpos.le
    have hsum_n : Summable (fun i => |sys.spatialEig b i| ^ n) := sys.spatial_summable_of_ge h4 hb
    have hHasSum : HasSum w 1 := by
      have h : HasSum w (sys.Z n b / sys.Z n b) := hsum_n.hasSum.div_const (sys.Z n b)
      rwa [div_self hZpos.ne'] at h
    have hsq := (tsum_purity_square_bound w hw_nn hHasSum).2.2.2.1
    have htsum2 : ∑' i, w i ^ 2 = sys.Z (2 * n) b / (sys.Z n b) ^ 2 := by
      have heq : (fun i => w i ^ 2) = fun i => |sys.spatialEig b i| ^ (2 * n) / (sys.Z n b) ^ 2 := by
        funext i; dsimp [w]; rw [div_pow, ← pow_mul, mul_comm]
      rw [heq, tsum_div_const]; rfl
    rwa [htsum2] at hsq
  T_le_one := fun n b hn h4 hb => by
    have hZpos : 0 < sys.Z n b := sys.Z_pos hn h4 hb
    let w : Fin (sys.d n) → ℝ := fun k => Real.exp (-b * (sys.E n k + sys.a * (n : ℝ))) / sys.Z n b
    have hw_nn : ∀ k ∈ (Finset.univ : Finset (Fin (sys.d n))), 0 ≤ w k :=
      fun k _ => div_nonneg (Real.exp_pos _).le hZpos.le
    have hsum : ∑ k : Fin (sys.d n), w k = 1 := by
      dsimp [w]; rw [← Finset.sum_div, ← sys.Z_eq n b hn h4 hb]; exact div_self hZpos.ne'
    have hsq := (finset_purity_square_bound Finset.univ w hw_nn hsum).2.1
    have hsum2 : ∑ k : Fin (sys.d n), w k ^ 2 = sys.Z n (2 * b) / (sys.Z n b) ^ 2 := by
      dsimp [w]; simp_rw [div_pow, ← Finset.sum_div]
      rw [show sys.Z n (2 * b) = ∑ k : Fin (sys.d n), Real.exp (-(2 * b) * (sys.E n k + sys.a * (n : ℝ))) from
        sys.Z_eq n (2 * b) hn h4 (by linarith)]
      congr 1; refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rwa [hsum2] at hsq
  S_square := fun n b hn h4 hb => by
    have hZpos : 0 < sys.Z n b := sys.Z_pos hn h4 hb
    let w : ℕ → ℝ := fun i => |sys.spatialEig b i| ^ n / sys.Z n b
    have hw_nn : ∀ i, 0 ≤ w i := fun i => div_nonneg (pow_nonneg (abs_nonneg _) n) hZpos.le
    have hsum_n : Summable (fun i => |sys.spatialEig b i| ^ n) := sys.spatial_summable_of_ge h4 hb
    have hHasSum : HasSum w 1 := by
      have h : HasSum w (sys.Z n b / sys.Z n b) := hsum_n.hasSum.div_const (sys.Z n b)
      rwa [div_self hZpos.ne'] at h
    have hsq := (tsum_purity_square_bound w hw_nn hHasSum).2.2.2.2
    have htsum2 : ∑' i, w i ^ 2 = sys.Z (2 * n) b / (sys.Z n b) ^ 2 := by
      have heq : (fun i => w i ^ 2) = fun i => |sys.spatialEig b i| ^ (2 * n) / (sys.Z n b) ^ 2 := by
        funext i; dsimp [w]; rw [div_pow, ← pow_mul, mul_comm]
      rw [heq, tsum_div_const]; rfl
    have htsum4 : ∑' i, w i ^ 4 = sys.Z (4 * n) b / (sys.Z n b) ^ 4 := by
      have heq : (fun i => w i ^ 4) = fun i => |sys.spatialEig b i| ^ (4 * n) / (sys.Z n b) ^ 4 := by
        funext i; dsimp [w]; rw [div_pow, ← pow_mul, mul_comm]
      rw [heq, tsum_div_const]; rfl
    rw [htsum2, htsum4] at hsq
    have hratio : (sys.Z (4 * n) b / (sys.Z n b) ^ 4) / (sys.Z (2 * n) b / (sys.Z n b) ^ 2) ^ 2 =
        sys.Z (4 * n) b / (sys.Z (2 * n) b) ^ 2 := by
      have h2n_ne : sys.Z (2 * n) b ≠ 0 := (sys.Z_pos (even_two_mul n) (by omega) hb).ne'
      field_simp [hZpos.ne', h2n_ne]
    rwa [hratio] at hsq
  T_square := fun n b hn h4 hb => by
    have hZpos : 0 < sys.Z n b := sys.Z_pos hn h4 hb
    let w : Fin (sys.d n) → ℝ := fun k => Real.exp (-b * (sys.E n k + sys.a * (n : ℝ))) / sys.Z n b
    have hw_nn : ∀ k ∈ (Finset.univ : Finset (Fin (sys.d n))), 0 ≤ w k :=
      fun k _ => div_nonneg (Real.exp_pos _).le hZpos.le
    have hsum : ∑ k : Fin (sys.d n), w k = 1 := by
      dsimp [w]; rw [← Finset.sum_div, ← sys.Z_eq n b hn h4 hb]; exact div_self hZpos.ne'
    have hsq := (finset_purity_square_bound Finset.univ w hw_nn hsum).2.2
    have hsum2 : ∑ k : Fin (sys.d n), w k ^ 2 = sys.Z n (2 * b) / (sys.Z n b) ^ 2 := by
      dsimp [w]; simp_rw [div_pow, ← Finset.sum_div]
      rw [show sys.Z n (2 * b) = ∑ k : Fin (sys.d n), Real.exp (-(2 * b) * (sys.E n k + sys.a * (n : ℝ))) from
        sys.Z_eq n (2 * b) hn h4 (by linarith)]
      congr 1; refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsum4 : ∑ k : Fin (sys.d n), w k ^ 4 = sys.Z n (4 * b) / (sys.Z n b) ^ 4 := by
      dsimp [w]; simp_rw [div_pow, ← Finset.sum_div]
      rw [show sys.Z n (4 * b) = ∑ k : Fin (sys.d n), Real.exp (-(4 * b) * (sys.E n k + sys.a * (n : ℝ))) from
        sys.Z_eq n (4 * b) hn h4 (by linarith)]
      congr 1; refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hsum2, hsum4] at hsq
    have hratio : (sys.Z n (4 * b) / (sys.Z n b) ^ 4) / (sys.Z n (2 * b) / (sys.Z n b) ^ 2) ^ 2 =
        sys.Z n (4 * b) / (sys.Z n (2 * b)) ^ 2 := by
      have h2b_ne : sys.Z n (2 * b) ≠ 0 := (sys.Z_pos hn h4 (by linarith)).ne'
      field_simp [hZpos.ne', h2b_ne]
    rwa [hratio] at hsq

/-- Spatial purity is nondecreasing in even length at fixed temperature:
if `4 ≤ n ≤ L` (both even) and `b > 0`, then `S(n, b) ≤ S(L, b)`. -/
theorem spatial_purity_mono_even (sys : SpectralSystem1D) {n L : ℕ} {b : ℝ}
    (hn : Even n) (hn4 : 4 ≤ n) (hL : Even L) (hnL : n ≤ L) (hb : 0 < b) :
    sys.toPuritySystem1D.S n b ≤ sys.toPuritySystem1D.S L b := by
  have hZpos : 0 < sys.Z n b := sys.Z_pos hn hn4 hb
  let p : ℕ → ℝ := fun i => |sys.spatialEig b i| ^ n / sys.Z n b
  have hp_nn : ∀ i, 0 ≤ p i := fun i => div_nonneg (pow_nonneg (abs_nonneg _) n) hZpos.le
  have hsum_n : Summable (fun i => |sys.spatialEig b i| ^ n) := sys.spatial_summable_of_ge hn4 hb
  have hHasSum : HasSum p 1 := by
    have h : HasSum p (sys.Z n b / sys.Z n b) := hsum_n.hasSum.div_const (sys.Z n b)
    rwa [div_self hZpos.ne'] at h
  set r : ℝ := (L : ℝ) / (n : ℝ)
  have hr : 1 ≤ r := (one_le_div (by positivity : (0 : ℝ) < n)).mpr (by exact_mod_cast hnL)
  have hmono := (tsum_purity_rpow_mono p hp_nn hHasSum hr).2.2.2.2
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have htsum2 : ∑' i, p i ^ 2 = sys.Z (2 * n) b / (sys.Z n b) ^ 2 := by
    have heq : (fun i => p i ^ 2) = fun i => |sys.spatialEig b i| ^ (2 * n) / (sys.Z n b) ^ 2 := by
      funext i; dsimp [p]; rw [div_pow, ← pow_mul, mul_comm]
    rw [heq, tsum_div_const]; rfl
  have hp_r : ∀ i, p i ^ r = |sys.spatialEig b i| ^ L / (sys.Z n b) ^ r := fun i => by
    dsimp [p]
    rw [Real.div_rpow (pow_nonneg (abs_nonneg _) n) hZpos.le,
      ← Real.rpow_natCast (|sys.spatialEig b i|) n, ← Real.rpow_mul (abs_nonneg _)]
    have hmul : (n : ℝ) * r = (L : ℝ) := mul_div_cancel₀ _ hn0
    rw [hmul, Real.rpow_natCast]
  have htsum_r : ∑' i, p i ^ r = sys.Z L b / (sys.Z n b) ^ r := by
    simp_rw [hp_r]; rw [tsum_div_const]; rfl
  have htsum_r2 : ∑' i, (p i ^ r) ^ 2 = sys.Z (2 * L) b / ((sys.Z n b) ^ r) ^ 2 := by
    have heq : (fun i => (p i ^ r) ^ 2) =
        fun i => |sys.spatialEig b i| ^ (2 * L) / ((sys.Z n b) ^ r) ^ 2 := by
      funext i; rw [hp_r i, div_pow, ← pow_mul, mul_comm]
    rw [heq, tsum_div_const]; rfl
  rw [htsum2, htsum_r, htsum_r2] at hmono
  have hZr_ne : (sys.Z n b) ^ r ≠ 0 := (Real.rpow_pos_of_pos hZpos r).ne'
  have hZL_ne : sys.Z L b ≠ 0 := (sys.Z_pos hL (le_trans hn4 hnL) hb).ne'
  have hcancel :
      (sys.Z (2 * L) b / ((sys.Z n b) ^ r) ^ 2) / (sys.Z L b / (sys.Z n b) ^ r) ^ 2 =
        sys.Z (2 * L) b / (sys.Z L b) ^ 2 := by
    field_simp [hZr_ne, hZL_ne]
  rw [hcancel] at hmono
  exact hmono

/-- Uniform spectral gap for a `SpectralSystem1D` with automatic shift cancellation
and non-vacuous excited-state witness when `2 ≤ sys.d L`. -/
theorem uniform_gap (sys : SpectralSystem1D)
    {n₀ : ℕ} {b₀ u₀ C : ℝ}
    (hn₀ : Even n₀) (h4 : 4 ≤ n₀) (hb₀ : 0 < b₀)
    (hu0_pos : 0 < u₀) (hu0_lt : u₀ < 1 / 6)
    (hGC : bootstrapCoeff u₀ ≤ C) (hr_lt : C * u₀ < 1)
    (hC_margin : 3 < C * (1 - 3 * u₀))
    (hS0 : 1 - sys.toPuritySystem1D.S n₀ b₀ ≤ u₀)
    (hT0 : 1 - sys.toPuritySystem1D.T (2 * n₀) b₀ ≤ u₀)
    {L : ℕ} (hL_even : Even L) (hL_ge : n₀ ≤ L)
    (k₀ : Fin (sys.d L)) (hmin : ∀ k, sys.E L k₀ ≤ sys.E L k) :
    (∀ k : Fin (sys.d L), sys.E L k = sys.E L k₀ → k = k₀) ∧
    (∀ k : Fin (sys.d L), k ≠ k₀ → Real.log (1 / (C * u₀)) / b₀ < sys.E L k - sys.E L k₀) ∧
    (2 ≤ sys.d L → ∃ k₁ : Fin (sys.d L), k₁ ≠ k₀ ∧
      Real.log (1 / (C * u₀)) / b₀ < sys.E L k₁ - sys.E L k₀) := by
  let E' : Fin (sys.d L) → ℝ := fun k => sys.E L k + sys.a * (L : ℝ)
  have hmin' : ∀ k, E' k₀ ≤ E' k := fun k => by dsimp [E']; linarith [hmin k]
  have hGibbs : ∀ b, 0 < b → sys.toPuritySystem1D.Z L b = ∑ k : Fin (sys.d L), Real.exp (-b * E' k) :=
    fun b hb => sys.Z_eq L b hL_even (le_trans h4 hL_ge) hb
  have hres := uniform_gap_from_purities sys.toPuritySystem1D sys.interp
    hn₀ h4 hb₀ hu0_pos hu0_lt hGC hr_lt hC_margin hS0 hT0 hL_even hL_ge E' k₀ hmin' hGibbs
  have huniq : ∀ k : Fin (sys.d L), sys.E L k = sys.E L k₀ → k = k₀ := fun k hk =>
    hres.1 k (by dsimp [E']; linarith)
  have hgap : ∀ k : Fin (sys.d L), k ≠ k₀ → Real.log (1 / (C * u₀)) / b₀ < sys.E L k - sys.E L k₀ :=
    fun k hne => by
      have h := hres.2 k hne
      dsimp [E'] at h
      linarith
  refine ⟨huniq, hgap, fun hd2 => ?_⟩
  by_cases h0 : k₀.val = 0
  · have hne1 : (⟨1, by omega⟩ : Fin (sys.d L)) ≠ k₀ := fun heq => by
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    exact ⟨⟨1, by omega⟩, hne1, hgap ⟨1, by omega⟩ hne1⟩
  · have hne0 : (⟨0, by omega⟩ : Fin (sys.d L)) ≠ k₀ := fun heq => by
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    exact ⟨⟨0, by omega⟩, hne0, hgap ⟨0, by omega⟩ hne0⟩

end SpectralSystem1D

end PurityBootstrap
