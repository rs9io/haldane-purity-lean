import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Core Purity-Bootstrap Inequalities

Formalizes the elementary probability-squaring inequality, coupled space-time
purity updates, and exact bootstrap factorization from:
- OpenAI (Sep 2026), *The periodic spin-one Haldane gap*, Section 4 (`bootstrap.tex`)
- T. Grover (Nov 2026), *Extensions of the Haldane gap proof*, arXiv:2611.07400
-/

namespace PurityBootstrap

open scoped BigOperators
open Filter

/-- The quadratic purity-defect update map `f(u) = u^2 / (2 (1 - u)^2)`. -/
noncomputable def purityUpdate (u : ℝ) : ℝ :=
  u ^ 2 / (2 * (1 - u) ^ 2)

/-- The bootstrap envelope coefficient
`G(u) = ((1-u)⁻¹ + (1-u)⁻² + (1-u)⁻³)^2 / 2`. -/
noncomputable def bootstrapCoeff (u : ℝ) : ℝ :=
  ((1 - u)⁻¹ + (1 - u)⁻¹ ^ 2 + (1 - u)⁻¹ ^ 3) ^ 2 / 2

lemma purityUpdate_nonneg (u : ℝ) : 0 ≤ purityUpdate u := by
  unfold purityUpdate
  positivity

lemma purityUpdate_mono {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) :
    purityUpdate u ≤ purityUpdate v := by
  unfold purityUpdate
  have hu1 : 0 < 1 - u := by linarith
  have hv1' : 0 < 1 - v := by linarith
  have h1 : u / (1 - u) ≤ v / (1 - v) := by
    rw [div_le_div_iff₀ hu1 hv1']
    nlinarith
  have h0 : 0 ≤ u / (1 - u) := div_nonneg hu0 hu1.le
  have hsq : (u / (1 - u)) ^ 2 ≤ (v / (1 - v)) ^ 2 := by nlinarith
  have hrewrite : ∀ x : ℝ, x ^ 2 / (2 * (1 - x) ^ 2) = (x / (1 - x)) ^ 2 / 2 := by
    intro x
    rw [div_pow, div_div, mul_comm]
  rw [hrewrite u, hrewrite v]
  linarith

lemma bootstrapCoeff_nonneg (u : ℝ) : 0 ≤ bootstrapCoeff u := by
  unfold bootstrapCoeff
  positivity

lemma bootstrapCoeff_mono {u v : ℝ} (huv : u ≤ v) (hv1 : v < 1) :
    bootstrapCoeff u ≤ bootstrapCoeff v := by
  unfold bootstrapCoeff
  have hu1 : 0 < 1 - u := by linarith
  have hv1' : 0 < 1 - v := by linarith
  have hinv : (1 - u)⁻¹ ≤ (1 - v)⁻¹ := by
    exact inv_anti₀ hv1' (by linarith)
  have hinv_pos : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr hu1.le
  have hinv2 : (1 - u)⁻¹ ^ 2 ≤ (1 - v)⁻¹ ^ 2 := by nlinarith
  have hinv3 : (1 - u)⁻¹ ^ 3 ≤ (1 - v)⁻¹ ^ 3 := by nlinarith
  have hsum_pos : 0 ≤ (1 - u)⁻¹ + (1 - u)⁻¹ ^ 2 + (1 - u)⁻¹ ^ 3 := by positivity
  have hsum :
      (1 - u)⁻¹ + (1 - u)⁻¹ ^ 2 + (1 - u)⁻¹ ^ 3 ≤
        (1 - v)⁻¹ + (1 - v)⁻¹ ^ 2 + (1 - v)⁻¹ ^ 3 := by linarith
  nlinarith

/-- Exact algebraic factorization (OpenAI Eq. `eq:bootstrap-factorization`):
`f(1 - (1 - u)^3) = G(u) * u^2` for all `u ≠ 1`. -/
theorem purityUpdate_one_sub_cube {u : ℝ} (hu : u ≠ 1) :
    purityUpdate (1 - (1 - u) ^ 3) = bootstrapCoeff u * u ^ 2 := by
  have h1 : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  unfold purityUpdate bootstrapCoeff
  field_simp [h1]
  ring

/-- Key finite combinatorial inequality: for any nonnegative weights `w` on a finite set `s`,
`2 * ((∑ w_i^2)^2 - ∑ w_i^4) ≤ ((∑ w_i)^2 - ∑ w_i^2)^2`.
Requires no linear order on the index type `ι`. -/
theorem finset_two_mul_offdiag_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    2 * ((∑ i ∈ s, w i ^ 2) ^ 2 - ∑ i ∈ s, w i ^ 4) ≤
      ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2) ^ 2 := by
  let T : ι × ι → ℝ := fun p => if p.1 = p.2 then 0 else w p.1 * w p.2
  have hT_nonneg : ∀ p ∈ s ×ˢ s, 0 ≤ T p := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    dsimp [T]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw p.1 hp1) (hw p.2 hp2)
  have hsum_T : ∑ p ∈ s ×ˢ s, T p = (∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2 := by
    rw [Finset.sum_product, sq, Finset.sum_mul_sum]
    have h1 : ∀ i ∈ s, ∑ j ∈ s, T (i, j) = (∑ j ∈ s, w i * w j) - w i ^ 2 := by
      intro i hi
      dsimp [T]
      have := Finset.sum_ite_eq s i (fun j => w i * w j)
      have hsplit :
          ∑ j ∈ s, (if i = j then (0 : ℝ) else w i * w j) +
            ∑ j ∈ s, (if i = j then w i * w j else 0) =
          ∑ j ∈ s, w i * w j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [this, if_pos hi, ← sq] at hsplit
      linarith
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  have hsum_T2 : ∑ p ∈ s ×ˢ s, (T p) ^ 2 = (∑ i ∈ s, w i ^ 2) ^ 2 - ∑ i ∈ s, w i ^ 4 := by
    rw [Finset.sum_product, sq, Finset.sum_mul_sum]
    have h1 : ∀ i ∈ s, ∑ j ∈ s, (T (i, j)) ^ 2 = (∑ j ∈ s, w i ^ 2 * w j ^ 2) - w i ^ 4 := by
      intro i hi
      have hsqT : ∀ j, (T (i, j)) ^ 2 = if i = j then 0 else w i ^ 2 * w j ^ 2 := by
        intro j
        dsimp [T]
        split_ifs <;> ring
      simp_rw [hsqT]
      have := Finset.sum_ite_eq s i (fun j => w i ^ 2 * w j ^ 2)
      have hsplit :
          ∑ j ∈ s, (if i = j then (0 : ℝ) else w i ^ 2 * w j ^ 2) +
            ∑ j ∈ s, (if i = j then w i ^ 2 * w j ^ 2 else 0) =
          ∑ j ∈ s, w i ^ 2 * w j ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [this, if_pos hi] at hsplit
      have h4 : w i ^ 2 * w i ^ 2 = w i ^ 4 := by ring
      rw [h4] at hsplit
      linarith
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  rw [← hsum_T, ← hsum_T2, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  by_cases hdiag : p.1 = p.2
  · have hTp0 : T p = 0 := by simp [T, hdiag]
    simp only [hTp0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_mul, Finset.sum_const_zero, le_refl]
  · let p' : ι × ι := (p.2, p.1)
    have hp' : p' ∈ s ×ˢ s := by
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      exact Finset.mem_product.mpr ⟨hp2, hp1⟩
    have hne : p ≠ p' := by
      intro h
      exact hdiag (congrArg Prod.fst h)
    have hTp' : T p' = T p := by
      dsimp [T, p']
      have hdiag' : p.2 ≠ p.1 := Ne.symm hdiag
      rw [ite_eq_right_iff.mpr (fun h => (hdiag' h).elim),
        ite_eq_right_iff.mpr (fun h => (hdiag h).elim), mul_comm]
    have hsub : ({p, p'} : Finset (ι × ι)) ⊆ s ×ˢ s := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun q => T p * T q) (fun q hq _ => mul_nonneg (hT_nonneg p hp) (hT_nonneg q hq))
    rw [Finset.sum_pair hne, hTp'] at hle
    linarith

/-- Finite probability-squaring lemma (`lem:purity`, finite version):
if `w ≥ 0` on `s` with `∑ w_i = 1`, then `P = ∑ w_i^2 ∈ (0, 1]` and
`1 - (∑ w_i^4) / P^2 ≤ f(1 - P)`. -/
theorem finset_purity_square_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) :
    0 < ∑ i ∈ s, w i ^ 2 ∧
    ∑ i ∈ s, w i ^ 2 ≤ 1 ∧
    1 - (∑ i ∈ s, w i ^ 4) / (∑ i ∈ s, w i ^ 2) ^ 2 ≤
      purityUpdate (1 - ∑ i ∈ s, w i ^ 2) := by
  set P := ∑ i ∈ s, w i ^ 2
  set Q := ∑ i ∈ s, w i ^ 4
  have hw_le_one : ∀ i ∈ s, w i ≤ 1 := fun i hi => by
    have h := Finset.single_le_sum hw hi
    linarith
  have hP_le : P ≤ 1 := by
    calc P = ∑ i ∈ s, w i ^ 2 := rfl
      _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum fun i hi => by
            have := hw i hi; have := hw_le_one i hi; nlinarith
      _ = 1 := hsum
  have hP_pos : 0 < P := by
    by_contra hle
    push_neg at hle
    have hP_nonneg : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
    have hP0 : P = 0 := le_antisymm hle hP_nonneg
    have hall0 : ∀ i ∈ s, w i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).mp hP0
    have hw0 : ∑ i ∈ s, w i = 0 := Finset.sum_eq_zero fun i hi => sq_eq_zero_iff.mp (hall0 i hi)
    linarith
  refine ⟨hP_pos, hP_le, ?_⟩
  have hmain := finset_two_mul_offdiag_sq_le s w hw
  rw [hsum, one_pow] at hmain
  unfold purityUpdate
  have h1sub : 1 - (1 - P) = P := by ring
  rw [h1sub]
  have hP2_pos : 0 < P ^ 2 := pow_pos hP_pos 2
  have h2P2_pos : 0 < 2 * P ^ 2 := by positivity
  rw [show 1 - Q / P ^ 2 = (P ^ 2 - Q) / P ^ 2 by field_simp [hP_pos.ne']]
  rw [div_le_div_iff₀ hP2_pos h2P2_pos]
  nlinarith

/-- Countable (`tsum`) probability-squaring lemma (`lem:purity`, full countable version):
for any summable nonnegative family `w : ι → ℝ` with `∑' i, w i = 1`,
`P = ∑' i, w i ^ 2 ∈ (0, 1]`, `w i ^ 4` is summable, and
`1 - (∑' i, w i ^ 4) / P^2 ≤ purityUpdate (1 - P)`. -/
theorem tsum_purity_square_bound {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : HasSum w 1) :
    Summable (fun i => w i ^ 2) ∧
    Summable (fun i => w i ^ 4) ∧
    0 < ∑' i, w i ^ 2 ∧
    ∑' i, w i ^ 2 ≤ 1 ∧
    1 - (∑' i, w i ^ 4) / (∑' i, w i ^ 2) ^ 2 ≤
      purityUpdate (1 - ∑' i, w i ^ 2) := by
  have hw_le_one : ∀ i, w i ≤ 1 := fun i => by
    have h := hsum.summable.le_tsum i (fun j _ => hw j)
    rw [hsum.tsum_eq] at h
    exact h
  have hsum2 : Summable (fun i => w i ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg (w i)) (fun i => ?_) hsum.summable
    have := hw i; have := hw_le_one i; nlinarith
  have hsum4 : Summable (fun i => w i ^ 4) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsum2
    have h2 : w i ^ 2 ≤ 1 := by have := hw i; have := hw_le_one i; nlinarith
    have h2n : 0 ≤ w i ^ 2 := sq_nonneg (w i)
    nlinarith
  set P := ∑' i, w i ^ 2
  set Q := ∑' i, w i ^ 4
  have hP_le : P ≤ 1 := by
    calc P ≤ ∑' i, w i := hsum2.tsum_le_tsum (fun i => by
            have := hw i; have := hw_le_one i; nlinarith) hsum.summable
      _ = 1 := hsum.tsum_eq
  have hP_pos : 0 < P := by
    by_contra hle
    push_neg at hle
    have hP_nonneg : 0 ≤ P := tsum_nonneg fun i => sq_nonneg (w i)
    have hP0 : P = 0 := le_antisymm hle hP_nonneg
    have hall0 : ∀ i, w i = 0 := fun i => by
      have hi : w i ^ 2 ≤ P := hsum2.le_tsum i (fun j _ => sq_nonneg (w j))
      have : w i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg (w i))
      exact sq_eq_zero_iff.mp this
    have : ∑' i, w i = 0 := by simp [hall0]
    rw [hsum.tsum_eq] at this
    linarith
  refine ⟨hsum2, hsum4, hP_pos, hP_le, ?_⟩
  have hlim : 2 * (P ^ 2 - Q) ≤ (1 - P) ^ 2 := by
    have hL : Tendsto (fun s : Finset ι => 2 * ((∑ i ∈ s, w i ^ 2) ^ 2 - ∑ i ∈ s, w i ^ 4))
        atTop (nhds (2 * (P ^ 2 - Q))) :=
      (((hsum2.hasSum.pow 2).sub hsum4.hasSum).const_mul 2)
    have hR : Tendsto (fun s : Finset ι => ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2) ^ 2)
        atTop (nhds ((1 ^ 2 - P) ^ 2)) :=
      ((hsum.pow 2).sub hsum2.hasSum).pow 2
    have hle_ev : ∀ s : Finset ι,
        2 * ((∑ i ∈ s, w i ^ 2) ^ 2 - ∑ i ∈ s, w i ^ 4) ≤
          ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, w i ^ 2) ^ 2 :=
      fun s => finset_two_mul_offdiag_sq_le s w (fun i _ => hw i)
    have := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hle_ev)
    simpa [one_pow] using this
  unfold purityUpdate
  have h1sub : 1 - (1 - P) = P := by ring
  rw [h1sub]
  have hP2_pos : 0 < P ^ 2 := pow_pos hP_pos 2
  have h2P2_pos : 0 < 2 * P ^ 2 := by positivity
  rw [show 1 - Q / P ^ 2 = (P ^ 2 - Q) / P ^ 2 by field_simp [hP_pos.ne']]
  rw [div_le_div_iff₀ hP2_pos h2P2_pos]
  nlinarith

/-- Finite purity monotonicity under power-raising (`r ≥ 1`):
for any nonnegative weights `p` on a finite set `s`,
`(∑ p_i^r)^2 * (∑ p_i^2) ≤ (∑ p_i)^2 * (∑ (p_i^r)^2)`.
Equivalently, raising nonnegative weights to a power `r ≥ 1` and renormalizing can only
increase their purity (used by Grover in `arXiv:2611.07400` App. `app:ising-bounds`). -/
theorem finset_purity_rpow_mono {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, p i ^ r) ^ 2 * (∑ i ∈ s, p i ^ 2) ≤
      (∑ i ∈ s, p i) ^ 2 * (∑ i ∈ s, (p i ^ r) ^ 2) := by
  set S1 := ∑ i ∈ s, p i
  set Sr := ∑ i ∈ s, p i ^ r
  have hS1_nn : 0 ≤ S1 := Finset.sum_nonneg hp
  have hSr_nn : 0 ≤ Sr := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hp i hi) r
  have hmul_r : ∀ i ∈ s, p i * p i ^ (r - 1) = p i ^ r := fun i hi => by
    rcases eq_or_lt_of_le (hp i hi) with h0 | hpos
    · rw [← h0, zero_mul, Real.zero_rpow (by linarith)]
    · rw [← Real.rpow_one_add' (hp i hi) (by linarith : (1 : ℝ) + (r - 1) ≠ 0)]
      ring_nf
  have hdouble_nn :
      0 ≤ ∑ i ∈ s, ∑ j ∈ s,
        p i * p j * (p i ^ (r - 1) - p j ^ (r - 1)) *
          (S1 * (p i ^ r - p j ^ r) + Sr * (p i - p j)) := by
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    have hpipj : 0 ≤ p i * p j := mul_nonneg (hp i hi) (hp j hj)
    rcases le_total (p i) (p j) with hle | hle
    · have h1 : p i ^ (r - 1) ≤ p j ^ (r - 1) :=
        Real.rpow_le_rpow (hp i hi) hle (by linarith)
      have h2 : p i ^ r ≤ p j ^ r :=
        Real.rpow_le_rpow (hp i hi) hle (by linarith)
      have hfac1 : p i ^ (r - 1) - p j ^ (r - 1) ≤ 0 := by linarith
      have hfac2 : S1 * (p i ^ r - p j ^ r) + Sr * (p i - p j) ≤ 0 := by
        have ha : S1 * (p i ^ r - p j ^ r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hS1_nn (by linarith)
        have hb : Sr * (p i - p j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hSr_nn (by linarith)
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hpipj hfac1) hfac2
    · have h1 : p j ^ (r - 1) ≤ p i ^ (r - 1) :=
        Real.rpow_le_rpow (hp j hj) hle (by linarith)
      have h2 : p j ^ r ≤ p i ^ r :=
        Real.rpow_le_rpow (hp j hj) hle (by linarith)
      have hfac1 : 0 ≤ p i ^ (r - 1) - p j ^ (r - 1) := by linarith
      have hfac2 : 0 ≤ S1 * (p i ^ r - p j ^ r) + Sr * (p i - p j) := by
        have ha : 0 ≤ S1 * (p i ^ r - p j ^ r) := mul_nonneg hS1_nn (by linarith)
        have hb : 0 ≤ Sr * (p i - p j) := mul_nonneg hSr_nn (by linarith)
        linarith
      exact mul_nonneg (mul_nonneg hpipj hfac1) hfac2
  have hident :
      (∑ i ∈ s, ∑ j ∈ s,
        p i * p j * (p i ^ (r - 1) - p j ^ (r - 1)) *
          (S1 * (p i ^ r - p j ^ r) + Sr * (p i - p j))) =
      2 * (S1 ^ 2 * (∑ i ∈ s, (p i ^ r) ^ 2) - Sr ^ 2 * (∑ i ∈ s, p i ^ 2)) := by
    have hterm : ∀ i ∈ s, ∀ j ∈ s,
        p i * p j * (p i ^ (r - 1) - p j ^ (r - 1)) *
          (S1 * (p i ^ r - p j ^ r) + Sr * (p i - p j)) =
        S1 * ((p i ^ r) ^ 2 * p j + p i * (p j ^ r) ^ 2)
        - S1 * (p i ^ r * (p j ^ r * p j) + (p i ^ r * p i) * p j ^ r)
        + Sr * ((p i ^ r * p i) * p j + p i * (p j ^ r * p j))
        - Sr * (p i ^ r * p j ^ 2 + p i ^ 2 * p j ^ r) := fun i hi j hj => by
      have h1 : p i * p j * (p i ^ (r - 1) - p j ^ (r - 1)) =
          p i ^ r * p j - p i * p j ^ r := by
        calc p i * p j * (p i ^ (r - 1) - p j ^ (r - 1))
            = (p i * p i ^ (r - 1)) * p j - p i * (p j * p j ^ (r - 1)) := by ring
          _ = p i ^ r * p j - p i * p j ^ r := by rw [hmul_r i hi, hmul_r j hj]
      rw [h1]
      ring
    calc ∑ i ∈ s, ∑ j ∈ s,
            p i * p j * (p i ^ (r - 1) - p j ^ (r - 1)) *
              (S1 * (p i ^ r - p j ^ r) + Sr * (p i - p j))
        = ∑ i ∈ s, ∑ j ∈ s,
            (S1 * ((p i ^ r) ^ 2 * p j + p i * (p j ^ r) ^ 2)
             - S1 * (p i ^ r * (p j ^ r * p j) + (p i ^ r * p i) * p j ^ r)
             + Sr * ((p i ^ r * p i) * p j + p i * (p j ^ r * p j))
             - Sr * (p i ^ r * p j ^ 2 + p i ^ 2 * p j ^ r)) := by
          refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hterm i hi j hj
      _ = S1 * (∑ i ∈ s, ∑ j ∈ s, ((p i ^ r) ^ 2 * p j + p i * (p j ^ r) ^ 2))
          - S1 * (∑ i ∈ s, ∑ j ∈ s, (p i ^ r * (p j ^ r * p j) + (p i ^ r * p i) * p j ^ r))
          + Sr * (∑ i ∈ s, ∑ j ∈ s, ((p i ^ r * p i) * p j + p i * (p j ^ r * p j)))
          - Sr * (∑ i ∈ s, ∑ j ∈ s, (p i ^ r * p j ^ 2 + p i ^ 2 * p j ^ r)) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = S1 * (2 * (∑ i ∈ s, (p i ^ r) ^ 2) * S1)
          - S1 * (2 * Sr * (∑ i ∈ s, p i ^ r * p i))
          + Sr * (2 * (∑ i ∈ s, p i ^ r * p i) * S1)
          - Sr * (2 * Sr * (∑ i ∈ s, p i ^ 2)) := by
          have hpair : ∀ (f g : ι → ℝ),
              ∑ i ∈ s, ∑ j ∈ s, (f i * g j + g i * f j) =
                2 * (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := fun f g => by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
            ring
          rw [hpair (fun i => (p i ^ r) ^ 2) p,
              hpair (fun i => p i ^ r) (fun i => p i ^ r * p i),
              hpair (fun i => p i ^ r * p i) p,
              hpair (fun i => p i ^ r) (fun i => p i ^ 2)]
      _ = 2 * (S1 ^ 2 * (∑ i ∈ s, (p i ^ r) ^ 2) - Sr ^ 2 * (∑ i ∈ s, p i ^ 2)) := by ring
  linarith

/-- Countable (`tsum`) purity monotonicity under power-raising (`r ≥ 1`):
for any nonnegative summable probability distribution `∑' i, p i = 1`, raising each weight
to power `r ≥ 1` and renormalizing can only increase its purity:
`∑' i, p_i^2 ≤ (∑' i, (p_i^r)^2) / (∑' i, p_i^r)^2`. -/
theorem tsum_purity_rpow_mono {ι : Type*} (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : HasSum p 1) {r : ℝ} (hr : 1 ≤ r) :
    Summable (fun i => p i ^ 2) ∧
    Summable (fun i => p i ^ r) ∧
    Summable (fun i => (p i ^ r) ^ 2) ∧
    0 < ∑' i, p i ^ r ∧
    ∑' i, p i ^ 2 ≤ (∑' i, (p i ^ r) ^ 2) / (∑' i, p i ^ r) ^ 2 := by
  have hp_le1 : ∀ i, p i ≤ 1 := fun i => by
    have h := hsum.summable.le_tsum i (fun j _ => hp j)
    rwa [hsum.tsum_eq] at h
  have hsum2 : Summable (fun i => p i ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg (p i))
      (fun i => by have := hp i; have := hp_le1 i; nlinarith) hsum.summable
  have hsum_r : Summable (fun i => p i ^ r) :=
    Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (hp i) r)
      (fun i => Real.rpow_le_self_of_le_one (hp i) (hp_le1 i) hr) hsum.summable
  have hsum_r2 : Summable (fun i => (p i ^ r) ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => by
        have hnn : 0 ≤ p i ^ r := Real.rpow_nonneg (hp i) r
        have hle : p i ^ r ≤ 1 := Real.rpow_le_one (hp i) (hp_le1 i) (by linarith)
        nlinarith) hsum_r
  have hSr_pos : 0 < ∑' i, p i ^ r := by
    by_contra hle
    push_neg at hle
    have hSr_nn : 0 ≤ ∑' i, p i ^ r := tsum_nonneg fun i => Real.rpow_nonneg (hp i) r
    have hSr0 : ∑' i, p i ^ r = 0 := le_antisymm hle hSr_nn
    have hall0 : ∀ i, p i = 0 := fun i => by
      have hi : p i ^ r ≤ ∑' j, p j ^ r := hsum_r.le_tsum i (fun j _ => Real.rpow_nonneg (hp j) r)
      have h0 : p i ^ r = 0 := le_antisymm (by linarith) (Real.rpow_nonneg (hp i) r)
      by_contra hne
      have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hne)
      exact (Real.rpow_pos_of_pos hpos r).ne' h0
    have : ∑' i, p i = 0 := by simp [hall0]
    rw [hsum.tsum_eq] at this
    linarith
  refine ⟨hsum2, hsum_r, hsum_r2, hSr_pos, ?_⟩
  have hlim : (∑' i, p i ^ r) ^ 2 * (∑' i, p i ^ 2) ≤ 1 ^ 2 * (∑' i, (p i ^ r) ^ 2) := by
    have hL : Tendsto (fun s : Finset ι => (∑ i ∈ s, p i ^ r) ^ 2 * (∑ i ∈ s, p i ^ 2))
        atTop (nhds ((∑' i, p i ^ r) ^ 2 * (∑' i, p i ^ 2))) :=
      (hsum_r.hasSum.pow 2).mul hsum2.hasSum
    have hR : Tendsto (fun s : Finset ι => (∑ i ∈ s, p i) ^ 2 * (∑ i ∈ s, (p i ^ r) ^ 2))
        atTop (nhds (1 ^ 2 * (∑' i, (p i ^ r) ^ 2))) :=
      (hsum.pow 2).mul hsum_r2.hasSum
    exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall fun s =>
      finset_purity_rpow_mono s p (fun i _ => hp i) hr)
  rw [one_pow, one_mul] at hlim
  rw [le_div_iff₀ (pow_pos hSr_pos 2)]
  linarith

/-- Abstract 1D space-time partition function system carrying spatial and temporal purities. -/
structure PuritySystem1D where
  Z : ℕ → ℝ → ℝ
  Z_pos : ∀ n b, Even n → 4 ≤ n → 0 < b → 0 < Z n b
  S_le_one : ∀ n b, Even n → 4 ≤ n → 0 < b → Z (2 * n) b / (Z n b) ^ 2 ≤ 1
  T_le_one : ∀ n b, Even n → 4 ≤ n → 0 < b → Z n (2 * b) / (Z n b) ^ 2 ≤ 1
  S_square : ∀ n b, Even n → 4 ≤ n → 0 < b →
    1 - Z (4 * n) b / (Z (2 * n) b) ^ 2 ≤ purityUpdate (1 - Z (2 * n) b / (Z n b) ^ 2)
  T_square : ∀ n b, Even n → 4 ≤ n → 0 < b →
    1 - Z n (4 * b) / (Z n (2 * b)) ^ 2 ≤ purityUpdate (1 - Z n (2 * b) / (Z n b) ^ 2)

namespace PuritySystem1D

/-- Spatial purity `S(n, b) = Z(2n, b) / Z(n, b)^2`. -/
noncomputable def S (sys : PuritySystem1D) (n : ℕ) (b : ℝ) : ℝ :=
  sys.Z (2 * n) b / (sys.Z n b) ^ 2

/-- Temporal (physical) purity `T(n, b) = Z(n, 2b) / Z(n, b)^2`. -/
noncomputable def T (sys : PuritySystem1D) (n : ℕ) (b : ℝ) : ℝ :=
  sys.Z n (2 * b) / (sys.Z n b) ^ 2

lemma S_pos (sys : PuritySystem1D) {n : ℕ} {b : ℝ} (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b) :
    0 < sys.S n b := by
  unfold S
  have h2n : Even (2 * n) := even_two_mul n
  exact div_pos (sys.Z_pos (2 * n) b h2n (by omega) hb) (pow_pos (sys.Z_pos n b hn h4 hb) 2)

lemma T_pos (sys : PuritySystem1D) {n : ℕ} {b : ℝ} (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b) :
    0 < sys.T n b := by
  unfold T
  exact div_pos (sys.Z_pos n (2 * b) hn h4 (by linarith)) (pow_pos (sys.Z_pos n b hn h4 hb) 2)

/-- Exact space-time cancellation identity (OpenAI Eq. `eq:space-time-cancel`):
`S(n, 2b) = S(n, b)^2 * T(2n, b) / T(n, b)^2`. -/
lemma space_time_cancel (sys : PuritySystem1D) {n : ℕ} {b : ℝ}
    (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b) :
    sys.S n (2 * b) = sys.S n b ^ 2 * sys.T (2 * n) b / sys.T n b ^ 2 := by
  unfold S T
  have h1 : sys.Z n b ≠ 0 := (sys.Z_pos n b hn h4 hb).ne'
  have h2 : sys.Z (2 * n) b ≠ 0 := (sys.Z_pos (2 * n) b (even_two_mul n) (by omega) hb).ne'
  have h3 : sys.Z n (2 * b) ≠ 0 := (sys.Z_pos n (2 * b) hn h4 (by linarith)).ne'
  field_simp [h1, h2, h3]

/-- Exact time-space cancellation identity (OpenAI Eq. `eq:time-space-cancel`):
`T(4n, b) = T(2n, b)^2 * S(2n, 2b) / S(2n, b)^2`. -/
lemma time_space_cancel (sys : PuritySystem1D) {n : ℕ} {b : ℝ}
    (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b) :
    sys.T (4 * n) b = sys.T (2 * n) b ^ 2 * sys.S (2 * n) (2 * b) / sys.S (2 * n) b ^ 2 := by
  unfold S T
  have h2n : Even (2 * n) := even_two_mul n
  have h4n : Even (4 * n) := ⟨2 * n, by omega⟩
  have h1 : sys.Z (2 * n) b ≠ 0 := (sys.Z_pos (2 * n) b h2n (by omega) hb).ne'
  have h2 : sys.Z (4 * n) b ≠ 0 := (sys.Z_pos (4 * n) b h4n (by omega) hb).ne'
  have h3 : sys.Z (2 * n) (2 * b) ≠ 0 := (sys.Z_pos (2 * n) (2 * b) h2n (by omega) (by linarith)).ne'
  have hmul : 2 * (2 * n) = 4 * n := by omega
  rw [hmul]
  field_simp [h1, h2, h3]

/-- Coupled rounded update (`lem:rounded-update`):
propagates `(1 - S(n, b) ≤ p, 1 - T(2n, b) ≤ q)` to
`(1 - S(2n, 2b) ≤ p_+, 1 - T(4n, 2b) ≤ q_+)`. -/
theorem rounded_coupled_update (sys : PuritySystem1D) {n : ℕ} {b p q p' q' : ℝ}
    (hn : Even n) (h4 : 4 ≤ n) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hp'1 : p' < 1)
    (hS : 1 - sys.S n b ≤ p) (hT : 1 - sys.T (2 * n) b ≤ q)
    (hp'_ge : purityUpdate (1 - (1 - p) ^ 2 * (1 - q)) ≤ p')
    (hq'_ge : purityUpdate (1 - (1 - q) ^ 2 * (1 - p')) ≤ q') :
    1 - sys.S (2 * n) (2 * b) ≤ p' ∧ 1 - sys.T (4 * n) (2 * b) ≤ q' := by
  have h2n : Even (2 * n) := even_two_mul n
  have h4n : Even (4 * n) := ⟨2 * n, by omega⟩
  have h2b : 0 < 2 * b := by linarith
  -- Step 1: lower bound S(n, 2b) ≥ (1 - p)^2 * (1 - q)
  have hS_n_2b : (1 - p) ^ 2 * (1 - q) ≤ sys.S n (2 * b) := by
    rw [sys.space_time_cancel hn h4 hb]
    have hTnb_pos : 0 < sys.T n b := sys.T_pos hn h4 hb
    have hTnb_le : sys.T n b ≤ 1 := sys.T_le_one n b hn h4 hb
    have hTnb_sq_pos : 0 < sys.T n b ^ 2 := pow_pos hTnb_pos 2
    have hTnb_sq_le : sys.T n b ^ 2 ≤ 1 := by nlinarith
    have hSnb : 1 - p ≤ sys.S n b := by linarith
    have hT2nb : 1 - q ≤ sys.T (2 * n) b := by linarith
    have hnum : (1 - p) ^ 2 * (1 - q) ≤ sys.S n b ^ 2 * sys.T (2 * n) b := by
      have h1mp : 0 ≤ 1 - p := by linarith
      have h1mq : 0 ≤ 1 - q := by linarith
      have hsq : (1 - p) ^ 2 ≤ sys.S n b ^ 2 := by nlinarith
      exact mul_le_mul hsq hT2nb h1mq (sq_nonneg _)
    calc (1 - p) ^ 2 * (1 - q)
        ≤ sys.S n b ^ 2 * sys.T (2 * n) b := hnum
      _ ≤ sys.S n b ^ 2 * sys.T (2 * n) b / sys.T n b ^ 2 := by
          rw [le_div_iff₀ hTnb_sq_pos]
          have hnn : 0 ≤ sys.S n b ^ 2 * sys.T (2 * n) b :=
            mul_nonneg (sq_nonneg _) (sys.T_pos h2n (by omega) hb).le
          nlinarith
  have hS_2n_2b : 1 - sys.S (2 * n) (2 * b) ≤ p' := by
    have hsq := sys.S_square n (2 * b) hn h4 h2b
    have hdef : sys.S (2 * n) (2 * b) = sys.Z (4 * n) (2 * b) / (sys.Z (2 * n) (2 * b)) ^ 2 := by
      unfold S; congr 2; omega
    rw [hdef]
    have hdef0 : sys.S n (2 * b) = sys.Z (2 * n) (2 * b) / (sys.Z n (2 * b)) ^ 2 := rfl
    rw [← hdef0] at hsq
    have hmono : purityUpdate (1 - sys.S n (2 * b)) ≤
        purityUpdate (1 - (1 - p) ^ 2 * (1 - q)) := by
      refine purityUpdate_mono ?_ (by linarith) ?_
      · linarith [sys.S_le_one n (2 * b) hn h4 h2b]
      · have h1mp : 0 < 1 - p := by linarith
        have h1mq : 0 < 1 - q := by linarith
        nlinarith [pow_pos h1mp 2]
    linarith
  -- Step 2: lower bound T(4n, b) ≥ (1 - q)^2 * (1 - p')
  have hT_4n_b : (1 - q) ^ 2 * (1 - p') ≤ sys.T (4 * n) b := by
    rw [sys.time_space_cancel hn h4 hb]
    have hS2nb_pos : 0 < sys.S (2 * n) b := sys.S_pos h2n (by omega) hb
    have hS2nb_le : sys.S (2 * n) b ≤ 1 := sys.S_le_one (2 * n) b h2n (by omega) hb
    have hS2nb_sq_pos : 0 < sys.S (2 * n) b ^ 2 := pow_pos hS2nb_pos 2
    have hS2nb_sq_le : sys.S (2 * n) b ^ 2 ≤ 1 := by nlinarith
    have hT2nb : 1 - q ≤ sys.T (2 * n) b := by linarith
    have hS2n2b : 1 - p' ≤ sys.S (2 * n) (2 * b) := by linarith
    have hnum : (1 - q) ^ 2 * (1 - p') ≤ sys.T (2 * n) b ^ 2 * sys.S (2 * n) (2 * b) := by
      have h1mq : 0 ≤ 1 - q := by linarith
      have h1mp' : 0 ≤ 1 - p' := by linarith
      have hsq : (1 - q) ^ 2 ≤ sys.T (2 * n) b ^ 2 := by nlinarith
      exact mul_le_mul hsq hS2n2b h1mp' (sq_nonneg _)
    calc (1 - q) ^ 2 * (1 - p')
        ≤ sys.T (2 * n) b ^ 2 * sys.S (2 * n) (2 * b) := hnum
      _ ≤ sys.T (2 * n) b ^ 2 * sys.S (2 * n) (2 * b) / sys.S (2 * n) b ^ 2 := by
          rw [le_div_iff₀ hS2nb_sq_pos]
          have hnn : 0 ≤ sys.T (2 * n) b ^ 2 * sys.S (2 * n) (2 * b) :=
            mul_nonneg (sq_nonneg _) (sys.S_pos h2n (by omega) h2b).le
          nlinarith
  have hT_4n_2b : 1 - sys.T (4 * n) (2 * b) ≤ q' := by
    have hsq := sys.T_square (4 * n) b h4n (by omega) hb
    have hdef : sys.T (4 * n) (2 * b) = sys.Z (4 * n) (4 * b) / (sys.Z (4 * n) (2 * b)) ^ 2 := by
      unfold T; congr 1; ring_nf
    rw [hdef]
    have hdef0 : sys.T (4 * n) b = sys.Z (4 * n) (2 * b) / (sys.Z (4 * n) b) ^ 2 := rfl
    rw [← hdef0] at hsq
    have hmono : purityUpdate (1 - sys.T (4 * n) b) ≤
        purityUpdate (1 - (1 - q) ^ 2 * (1 - p')) := by
      refine purityUpdate_mono ?_ (by linarith) ?_
      · linarith [sys.T_le_one (4 * n) b h4n (by omega) hb]
      · have h1mq : 0 < 1 - q := by linarith
        have h1mp' : 0 < 1 - p' := by linarith
        nlinarith [pow_pos h1mq 2]
    linarith
  exact ⟨hS_2n_2b, hT_4n_2b⟩

end PuritySystem1D

end PurityBootstrap
