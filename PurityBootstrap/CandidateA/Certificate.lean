import Mathlib.Tactic
import PurityBootstrap.OneD
import PurityBootstrap.ExactCertificates
import PurityBootstrap.MomentInit
import PurityBootstrap.CandidateA.Data

/-!
# Candidate A (`Δ = 1, D = 1/4` Spin-1 Haldane Chain): Machine-Checked Spectral Gap Certificate

Proves inside Lean 4's pure kernel (`decide +kernel`, zero `sorry`, zero `native_decide`,
strictly standard axioms `[propext, Classical.choice, Quot.sound]`):
1. All 16 one-sided degree-14 nonnegative polynomial filters (`x^4 q(x)^2`, `deg q ≤ 5`)
   across the 4 dihedral `D₄` symmetry sectors at `b = 31/2` and `b = 23` (`n = 4..14`).
2. Dominant-eigenvalue extraction and capped-mass residual bounds (`r = 4, 8`) yielding:
   - `1 - S(56, 23) ≤ 1215302 / 10^7`,
   - `Z_112(31/2) ≤ 14505687 / 12500000 < 1.160455`.
3. Temperature-transfer temporal purity bound (`31/2 → 23` at `L = 112`) from the trial
   inequality `E_0(112) + 112 a ≤ 0`:
   `1 - T(112, 23) ≤ 1203214 / 10^7`.
4. Four upward-rounded coupled bootstrap rounds `(56, 23) → (896, 368)` reaching
   `(53546/10^7, 9312/10^7) < (1/100, 1/100)`.
5. **Conditional Uniform Haldane Gap (`candidate_a_uniform_gap_896`)**:
   unique ground state and uniform spectral gap `γ_L > log(20) / 368 ≈ 0.00814`
   for **every even ring length `L ≥ 896`**.
-/

namespace PurityBootstrap.CandidateA

open PurityBootstrap
open PurityBootstrap.ExactCertificates
open PurityBootstrap.MomentInit

/-! ## Section 1: Degree-14 Polynomial Filters & Integer-Cleared One-Sided Ray Certificates -/

/-- Degree-14 polynomial `x^4 * (∑_{i=0}^5 q_i x^i)^2` as a length-15 list of integer coefficients. -/
def filterPoly14 (q : List ℤ) : List ℤ :=
  (List.range 15).map fun d =>
    (List.range q.length).foldl (fun acc i =>
      (List.range q.length).foldl (fun acc2 j =>
        if i + j + 4 = d then acc2 + q.getD i 0 * q.getD j 0 else acc2) acc) 0

/-- Upper bound `B = ∑_{d=4}^{14} (f_d c_d + |f_d| ε)` for a degree-14 filter on sector `sec`. -/
def filter14Upper (tbl : List (ℤ × ℤ × ℤ × ℤ)) (sec : Fin 4) (coeffs : List ℤ) : ℚ :=
  ((List.range 15).map fun d =>
    let c : ℤ := coeffs.getD d 0
    (c : ℚ) * caMoment tbl sec d + (|c| : ℚ) * caSectorEps sec).sum

/-- Integer-cleared Taylor coefficient of `q_den^14 * F(sign * (p / q_den + y))` at `(q_den * y)^j`:
`∑_{d=j}^{14} coeffs[d] * sign^d * C(d, j) * p^(d - j) * q_den^(14 - d)`. -/
def shiftedFilter14Int (coeffs : List ℤ) (sign p q_den : ℤ) (j : ℕ) : ℤ :=
  ((List.range 15).map fun d =>
    if j ≤ d then
      coeffs.getD d 0 * (sign ^ d) * (Nat.choose d j : ℤ) * (p ^ (d - j)) * (q_den ^ (14 - d))
    else 0).sum

/-- Fast pure-integer ray check for a single `(sign, cap, q)` witness on sector `sec`. -/
def checkRay14 (tbl : List (ℤ × ℤ × ℤ × ℤ)) (sec : Fin 4) (ray : ℤ × ℚ × List ℤ) : Bool :=
  let (sign, cap, q) := ray
  let coeffs := filterPoly14 q
  let B := filter14Upper tbl sec coeffs
  let p : ℤ := cap.num
  let qd : ℤ := (cap.den : ℤ)
  let c0 : ℤ := shiftedFilter14Int coeffs sign p qd 0
  decide (0 < cap) &&
  decide (sign = 1 ∨ sign = -1) &&
  decide (q.length ≤ 6) &&
  decide (B.num * qd ^ 14 < c0 * (B.den : ℤ)) &&
  (List.range 14).all (fun j => decide (0 ≤ shiftedFilter14Int coeffs sign p qd (j + 1)))

lemma filterPoly14_eval_eq (q : List ℤ) (hq : q.length ≤ 6) (x : ℝ) :
    ∑ d : Fin 15, ((filterPoly14 q).getD d.val 0 : ℝ) * x ^ d.val =
      x ^ 4 * (∑ i ∈ Finset.range q.length, (q.getD i 0 : ℝ) * x ^ i) ^ 2 := by
  have hget : ∀ d : Fin 15, ((filterPoly14 q).getD d.val 0 : ℝ) =
      ∑ i ∈ Finset.range q.length, ∑ j ∈ Finset.range q.length,
        if i + j + 4 = d.val then (q.getD i 0 : ℝ) * (q.getD j 0 : ℝ) else 0 := by
    intro d
    unfold filterPoly14
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range d.isLt,
      Option.map_some, Option.getD_some]
    have hfold : ∀ (n : ℕ) (g : ℕ → ℤ) (init : ℤ),
        (List.range n).foldl (fun acc k => acc + g k) init = init + ∑ k ∈ Finset.range n, g k := by
      intro n g
      induction n with
      | zero => intro init; simp
      | succ n ih =>
        intro init
        rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
        simp [add_assoc]
    have hinner : ∀ (i : ℕ) (init : ℤ),
        (List.range q.length).foldl
          (fun acc2 j => if i + j + 4 = d.val then acc2 + q.getD i 0 * q.getD j 0 else acc2) init =
        init + ∑ j ∈ Finset.range q.length,
          if i + j + 4 = d.val then q.getD i 0 * q.getD j 0 else 0 := fun i init => by
      have heq : (fun acc2 j => if i + j + 4 = d.val then acc2 + q.getD i 0 * q.getD j 0 else acc2) =
          (fun acc2 j => acc2 + if i + j + 4 = d.val then q.getD i 0 * q.getD j 0 else 0) := by
        funext acc2 j; split_ifs <;> ring
      rw [heq, hfold]
    have houter :
        (List.range q.length).foldl (fun acc i =>
          (List.range q.length).foldl
            (fun acc2 j => if i + j + 4 = d.val then acc2 + q.getD i 0 * q.getD j 0 else acc2) acc) 0 =
        ∑ i ∈ Finset.range q.length, ∑ j ∈ Finset.range q.length,
          if i + j + 4 = d.val then q.getD i 0 * q.getD j 0 else 0 := by
      have heq : (fun acc i =>
          (List.range q.length).foldl
            (fun acc2 j => if i + j + 4 = d.val then acc2 + q.getD i 0 * q.getD j 0 else acc2) acc) =
          (fun acc i => acc + ∑ j ∈ Finset.range q.length,
            if i + j + 4 = d.val then q.getD i 0 * q.getD j 0 else 0) := by
        funext acc i; exact hinner i acc
      rw [heq, hfold, zero_add]
    rw [houter]; push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  simp_rw [hget, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i; rw [Finset.sum_comm]
  rw [sq, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' : i < q.length := Finset.mem_range.mp hi
  have hj' : j < q.length := Finset.mem_range.mp hj
  have hlt15 : i + j + 4 < 15 := by omega
  let d0 : Fin 15 := ⟨i + j + 4, hlt15⟩
  rw [Finset.sum_eq_single d0]
  · simp [d0]; rw [pow_add, pow_add]; ring
  · intro d _ hne
    have hval : i + j + 4 ≠ d.val := fun h => hne (Fin.ext h.symm)
    simp [hval]
  · intro h; exact absurd (Finset.mem_univ d0) h

lemma filterPoly14_zero_low (q : List ℤ) (d : Fin 15) (hd : d.val < 4) :
    (filterPoly14 q).getD d.val 0 = 0 := by
  unfold filterPoly14
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range d.isLt,
    Option.map_some, Option.getD_some]
  have hfold0 : ∀ (l : List ℕ) (f : ℤ → ℕ → ℤ), (∀ x ∈ l, f 0 x = 0) → l.foldl f 0 = 0 := by
    intro l; induction l with
    | nil => intros; rfl
    | cons x xs ih =>
      intro f hf; simp only [List.foldl_cons, hf x (by simp)]
      exact ih f fun y hy => hf y (by simp [hy])
  refine hfold0 _ _ fun i _ => hfold0 _ _ fun j _ => ?_
  have hne : ¬ (i + j + 4 = d.val) := by omega
  simp [hne]

lemma shiftedFilter14Int_eval_eq (coeffs : List ℤ) (sign : ℤ) (cap : ℚ) (y : ℝ) :
    ((cap.den : ℝ) ^ 14) *
      ∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) * ((cap : ℝ) + y)) ^ d.val =
    ∑ j : Fin 15, (shiftedFilter14Int coeffs sign cap.num (cap.den : ℤ) j.val : ℝ) *
      ((cap.den : ℝ) * y) ^ j.val := by
  have hlist : ∀ (n : ℕ) (g : ℕ → ℤ),
      (((List.range n).map g).sum : ℝ) = ∑ d ∈ Finset.range n, (g d : ℝ) := fun n g => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        Int.cast_add, ih, Finset.sum_range_succ]
  have hq_ne : (cap.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr cap.den_nz
  have hcap_eq : (cap.den : ℝ) * ((cap : ℝ) + y) = (cap.num : ℝ) + (cap.den : ℝ) * y := by
    rw [mul_add, Rat.cast_def]
    field_simp [hq_ne]
  have hS : ∀ j : Fin 15,
      (shiftedFilter14Int coeffs sign cap.num (cap.den : ℤ) j.val : ℝ) =
      ∑ d : Fin 15,
        if j.val ≤ d.val then
          (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) ^ d.val) * (Nat.choose d.val j.val : ℝ) *
          ((cap.num : ℝ) ^ (d.val - j.val)) * ((cap.den : ℝ) ^ (14 - d.val))
        else 0 := fun j => by
    unfold shiftedFilter14Int
    rw [hlist, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> push_cast <;> rfl
  simp_rw [hS, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hpow14 : (cap.den : ℝ) ^ 14 = (cap.den : ℝ) ^ (14 - d.val) * (cap.den : ℝ) ^ d.val := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : d.val ≤ 14)]
  have hLHS :
      (cap.den : ℝ) ^ 14 * ((coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) * ((cap : ℝ) + y)) ^ d.val) =
      (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) ^ d.val) * ((cap.den : ℝ) ^ (14 - d.val)) *
      ((cap.num : ℝ) + (cap.den : ℝ) * y) ^ d.val := by
    rw [hpow14, mul_pow, ← hcap_eq, mul_pow]
    ring
  rw [hLHS, add_comm (cap.num : ℝ), add_pow, Finset.mul_sum]
  have hrange : ∑ j : Fin 15,
      (if j.val ≤ d.val then
        (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) ^ d.val) * (Nat.choose d.val j.val : ℝ) *
        ((cap.num : ℝ) ^ (d.val - j.val)) * ((cap.den : ℝ) ^ (14 - d.val))
      else 0) * ((cap.den : ℝ) * y) ^ j.val =
      ∑ j ∈ Finset.range (d.val + 1),
        (coeffs.getD d.val 0 : ℝ) * (sign : ℝ) ^ d.val * (cap.den : ℝ) ^ (14 - d.val) *
        (((cap.den : ℝ) * y) ^ j * (cap.num : ℝ) ^ (d.val - j) * (Nat.choose d.val j : ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      (if j ≤ d.val then
        (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) ^ d.val) * (Nat.choose d.val j : ℝ) *
        ((cap.num : ℝ) ^ (d.val - j)) * ((cap.den : ℝ) ^ (14 - d.val))
      else 0) * ((cap.den : ℝ) * y) ^ j)]
    have hsub : Finset.range (d.val + 1) ⊆ Finset.range 15 := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjle : j ≤ d.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [if_pos hjle]; ring
    · intro j _ hnot
      have hjgt : ¬ (j ≤ d.val) := fun hle => hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [hjgt]
  exact hrange.symm

/-- One-sided polynomial filter exclusion on `ι → ℝ`: if `F(x) ≥ 0` everywhere, moments match
`c_d` within `ε`, and `F(x) > B` for every `x` with `cap ≤ sign * x`, then `sign * lam i < cap`. -/
theorem polynomial_filter14_ray_tsum {ι : Type*} (lam : ι → ℝ)
    (tbl : List (ℤ × ℤ × ℤ × ℤ)) (sec : Fin 4) (ray : ℤ × ℚ × List ℤ)
    (hcheck : checkRay14 tbl sec ray = true)
    (hsumm : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam i| ^ n))
    (hmom : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |(∑' i, lam i ^ n) - (caMoment tbl sec n : ℝ)| ≤ (caSectorEps sec : ℝ)) :
    ∀ i : ι, (ray.1 : ℝ) * lam i < (ray.2.1 : ℝ) := by
  rcases ray with ⟨sign, cap, q⟩
  dsimp [checkRay14] at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hcap_pos, hsign_pm⟩, hq_len⟩, hB_lt⟩, hall⟩
  set coeffs := filterPoly14 q
  set B := filter14Upper tbl sec coeffs
  have hB_eq : (B : ℝ) =
      (∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * (caMoment tbl sec d.val : ℝ)) +
      (caSectorEps sec : ℝ) * (∑ d : Fin 15, |(coeffs.getD d.val 0 : ℝ)|) := by
    dsimp [B, filter14Upper]
    have hlist : ∀ (n : ℕ) (g : ℕ → ℚ),
        (((List.range n).map g).sum : ℝ) = ∑ d ∈ Finset.range n, (g d : ℝ) := fun n g => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          Rat.cast_add, ih, Finset.sum_range_succ]
    rw [hlist, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast; ring
  have hF_nn : ∀ x : ℝ, 0 ≤ ∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * x ^ d.val := fun x => by
    rw [filterPoly14_eval_eq q hq_len x]; positivity
  have hF_gt : ∀ x : ℝ, (cap : ℝ) ≤ (sign : ℝ) * x →
      (B : ℝ) < ∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * x ^ d.val := fun x hx => by
    set y : ℝ := (sign : ℝ) * x - (cap : ℝ)
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hx_eq : x = (sign : ℝ) * ((cap : ℝ) + y) := by
      rcases hsign_pm with rfl | rfl <;> (dsimp [y]; push_cast; ring)
    have hq_pos : (0 : ℝ) < (cap.den : ℝ) := Nat.cast_pos.mpr cap.pos
    have hq14_pos : (0 : ℝ) < (cap.den : ℝ) ^ 14 := pow_pos hq_pos 14
    rw [hx_eq]
    suffices hmul : (cap.den : ℝ) ^ 14 * (B : ℝ) <
        (cap.den : ℝ) ^ 14 * ∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) * ((cap : ℝ) + y)) ^ d.val by
      exact lt_of_mul_lt_mul_left hmul hq14_pos.le
    rw [shiftedFilter14Int_eval_eq, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
    have h0_lt : (cap.den : ℝ) ^ 14 * (B : ℝ) <
        (shiftedFilter14Int coeffs sign cap.num (cap.den : ℤ) 0 : ℝ) := by
      have hBden_pos : (0 : ℝ) < (B.den : ℝ) := Nat.cast_pos.mpr B.pos
      have hR : ((B.num : ℝ) * ((cap.den : ℝ) ^ 14)) <
          (shiftedFilter14Int coeffs sign cap.num (cap.den : ℤ) 0 : ℝ) * (B.den : ℝ) := by
        exact_mod_cast hB_lt
      rw [Rat.cast_def]
      have : (cap.den : ℝ) ^ 14 * ((B.num : ℝ) / (B.den : ℝ)) =
          ((B.num : ℝ) * (cap.den : ℝ) ^ 14) / (B.den : ℝ) := by ring
      rw [this, div_lt_iff₀ hBden_pos]
      exact hR
    have htail_nn : 0 ≤ ∑ j : Fin 14,
        (shiftedFilter14Int coeffs sign cap.num (cap.den : ℤ) (j.val + 1) : ℝ) *
          ((cap.den : ℝ) * y) ^ (j.val + 1) := by
      refine Finset.sum_nonneg fun j _ => ?_
      have hj_mem : j.val ∈ List.range 14 := List.mem_range.mpr j.isLt
      have hj_ok : (0 : ℤ) ≤ shiftedFilter14Int coeffs sign cap.num (cap.den : ℤ) (j.val + 1) :=
        of_decide_eq_true (List.all_eq_true.mp hall j.val hj_mem)
      exact mul_nonneg (by exact_mod_cast hj_ok) (pow_nonneg (mul_nonneg hq_pos.le hy) _)
    linarith
  -- Sum F(lam i) over all `i` and compare with `B`
  have hterm_summ : ∀ d : Fin 15, Summable (fun i => (coeffs.getD d.val 0 : ℝ) * lam i ^ d.val) := fun d => by
    by_cases h0 : (coeffs.getD d.val 0 : ℝ) = 0
    · simp_rw [h0, zero_mul]; exact summable_zero
    · have hd4 : 4 ≤ d.val := by
        by_contra hlt; push Not at hlt
        apply h0
        dsimp only [coeffs]
        rw [filterPoly14_zero_low q d hlt]; norm_num
      have habs : Summable (fun i => |lam i ^ d.val|) := by
        simpa [abs_pow] using hsumm d.val hd4
      exact (Summable.of_abs habs).mul_left _
  have hF_summ : Summable (fun i => ∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * lam i ^ d.val) :=
    summable_sum fun d _ => hterm_summ d
  have htsum_le : ∑' i, (∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * lam i ^ d.val) ≤ (B : ℝ) := by
    rw [hB_eq, Summable.tsum_finsetSum fun d _ => hterm_summ d]
    simp_rw [tsum_mul_left]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases h0 : (coeffs.getD d.val 0 : ℝ) = 0
    · rw [h0]; simp
    · have hd4 : 4 ≤ d.val := by
        by_contra hlt; push Not at hlt
        apply h0
        dsimp only [coeffs]
        rw [filterPoly14_zero_low q d hlt]; norm_num
      have herr := hmom d.val hd4 (by omega)
      have h1 : (coeffs.getD d.val 0 : ℝ) * ((∑' i, lam i ^ d.val) - (caMoment tbl sec d.val : ℝ)) ≤
          |(coeffs.getD d.val 0 : ℝ)| * (caSectorEps sec : ℝ) := by
        calc _ ≤ |(coeffs.getD d.val 0 : ℝ) * ((∑' i, lam i ^ d.val) - (caMoment tbl sec d.val : ℝ))| := le_abs_self _
          _ = |(coeffs.getD d.val 0 : ℝ)| * |(∑' i, lam i ^ d.val) - (caMoment tbl sec d.val : ℝ)| := abs_mul _ _
          _ ≤ |(coeffs.getD d.val 0 : ℝ)| * (caSectorEps sec : ℝ) := mul_le_mul_of_nonneg_left herr (abs_nonneg _)
      linarith
  intro i
  by_contra hge; push Not at hge
  have hsingle : (∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * lam i ^ d.val) ≤
      ∑' k, (∑ d : Fin 15, (coeffs.getD d.val 0 : ℝ) * lam k ^ d.val) :=
    hF_summ.le_tsum i (fun k _ => hF_nn (lam k))
  have hgt := hF_gt (lam i) hge
  linarith

/-! ## Section 2: Pure-Kernel Exact Rational Verification (`decide +kernel`) -/

/-- All 8 one-sided degree-14 polynomial filter rays at `b = 31/2` pass! -/
theorem ca_rays155_exact :
    checkRay14 caTable155 0 (caRays155.getD 0 (1, 1, [])) = true ∧
    checkRay14 caTable155 0 (caRays155.getD 1 (-1, 1, [])) = true ∧
    checkRay14 caTable155 1 (caRays155.getD 2 (1, 1, [])) = true ∧
    checkRay14 caTable155 1 (caRays155.getD 3 (-1, 1, [])) = true ∧
    checkRay14 caTable155 2 (caRays155.getD 4 (1, 1, [])) = true ∧
    checkRay14 caTable155 2 (caRays155.getD 5 (-1, 1, [])) = true ∧
    checkRay14 caTable155 3 (caRays155.getD 6 (1, 1, [])) = true ∧
    checkRay14 caTable155 3 (caRays155.getD 7 (-1, 1, [])) = true := by
  decide +kernel

/-- All 8 one-sided degree-14 polynomial filter rays at `b = 23` pass! -/
theorem ca_rays23_exact :
    checkRay14 caTable23 0 (caRays23.getD 0 (1, 1, [])) = true ∧
    checkRay14 caTable23 0 (caRays23.getD 1 (-1, 1, [])) = true ∧
    checkRay14 caTable23 1 (caRays23.getD 2 (1, 1, [])) = true ∧
    checkRay14 caTable23 1 (caRays23.getD 3 (-1, 1, [])) = true ∧
    checkRay14 caTable23 2 (caRays23.getD 4 (1, 1, [])) = true ∧
    checkRay14 caTable23 2 (caRays23.getD 5 (-1, 1, [])) = true ∧
    checkRay14 caTable23 3 (caRays23.getD 6 (1, 1, [])) = true ∧
    checkRay14 caTable23 3 (caRays23.getD 7 (-1, 1, [])) = true := by
  decide +kernel

/-- Clean 9-digit rational intermediate bounds for 14th powers (keeps kernel verification sub-second!). -/
def caLo155_14_lo : ℚ := 124998573 / 125000000
def caLo155_14_hi : ℚ := 199997717 / 200000000
def caCap155_14_0 : ℚ := 127345699 / 125000000
def caCap155_14_1 : ℚ := 34805843 / 1000000000
def caCap155_14_2 : ℚ := 38202173 / 1000000000
def caCap155_14_3 : ℚ := 71655143 / 250000000
def caU112_ceil   : ℚ := 14505687 / 12500000

def caLo23_14_lo  : ℚ := 499888677 / 500000000
def caLo23_14_hi  : ℚ := 199955471 / 200000000
def caCap23_14_0  : ℚ := 513312993 / 500000000
def caCap23_14_1  : ℚ := 8975789 / 125000000
def caCap23_14_2  : ℚ := 43896319 / 500000000
def caCap23_14_3  : ℚ := 414832829 / 1000000000

def caMass (tbl : List (ℤ × ℤ × ℤ × ℤ)) (sec : Fin 4) : ℚ :=
  caMoment tbl sec 14 + caSectorEps sec

/-- Exact rational verification of all 14th-power intermediate enclosures at `b = 31/2` and `b = 23`. -/
theorem ca_pows14_exact :
    caLo155_14_lo ≤ caLo155 ^ 14 ∧ caLo155 ^ 14 ≤ caLo155_14_hi ∧
    (max (caRays155.getD 0 (1, 1, [])).2.1 (caRays155.getD 1 (-1, 1, [])).2.1) ^ 14 ≤ caCap155_14_0 ∧
    (max (caRays155.getD 2 (1, 1, [])).2.1 (caRays155.getD 3 (-1, 1, [])).2.1) ^ 14 ≤ caCap155_14_1 ∧
    (max (caRays155.getD 4 (1, 1, [])).2.1 (caRays155.getD 5 (-1, 1, [])).2.1) ^ 14 ≤ caCap155_14_2 ∧
    (max (caRays155.getD 6 (1, 1, [])).2.1 (caRays155.getD 7 (-1, 1, [])).2.1) ^ 14 ≤ caCap155_14_3 ∧
    caLo23_14_lo ≤ caLo23 ^ 14 ∧ caLo23 ^ 14 ≤ caLo23_14_hi ∧
    (max (caRays23.getD 0 (1, 1, [])).2.1 (caRays23.getD 1 (-1, 1, [])).2.1) ^ 14 ≤ caCap23_14_0 ∧
    (max (caRays23.getD 2 (1, 1, [])).2.1 (caRays23.getD 3 (-1, 1, [])).2.1) ^ 14 ≤ caCap23_14_1 ∧
    (max (caRays23.getD 4 (1, 1, [])).2.1 (caRays23.getD 5 (-1, 1, [])).2.1) ^ 14 ≤ caCap23_14_2 ∧
    (max (caRays23.getD 6 (1, 1, [])).2.1 (caRays23.getD 7 (-1, 1, [])).2.1) ^ 14 ≤ caCap23_14_3 := by
  decide +kernel

/-- Exact rational verification of dominance, `U_112(31/2) ≤ caU112_ceil`,
`(caU112_ceil - 1)^46 ≤ caRelTail^31`, `p_0 ≤ caP0`, and `q_0 ≤ caQ0`. -/
theorem ca_initial_bounds_exact :
    let m155_0 := caMass caTable155 0
    let m155_1 := caMass caTable155 1
    let m155_2 := caMass caTable155 2
    let m155_3 := caMass caTable155 3
    let o155_8 := 2 * cappedMassQ m155_1 caCap155_14_1 8 +
                  cappedMassQ m155_2 caCap155_14_2 8 +
                  2 * cappedMassQ m155_3 caCap155_14_3 8
    let resid155 := m155_0 - caLo155_14_lo
    let tail155_112 := resid155 ^ 8 + o155_8
    let m23_0 := caMass caTable23 0
    let m23_1 := caMass caTable23 1
    let m23_2 := caMass caTable23 2
    let m23_3 := caMass caTable23 3
    let o23_4 := 2 * cappedMassQ m23_1 caCap23_14_1 4 +
                 cappedMassQ m23_2 caCap23_14_2 4 +
                 2 * cappedMassQ m23_3 caCap23_14_3 4
    let o23_8 := 2 * cappedMassQ m23_1 caCap23_14_1 8 +
                 cappedMassQ m23_2 caCap23_14_2 8 +
                 2 * cappedMassQ m23_3 caCap23_14_3 8
    let resid23 := m23_0 - caLo23_14_lo
    let tail23_56 := resid23 ^ 4 + o23_4
    -- 1. Dominance at b = 31/2 and b = 23
    cappedMassQ m155_0 caLo155_14_hi 8 + o155_8 < 1 ∧
    caLo155_14_lo ≤ m155_0 ∧
    cappedMassQ m23_0 caLo23_14_hi 8 + o23_8 < 1 ∧
    caLo23_14_lo ≤ m23_0 ∧
    -- 2. U_112(31/2) bound and 46/31 power transfer to caRelTail
    caCap155_14_0 ^ 8 + tail155_112 ≤ caU112_ceil ∧
    (1 : ℚ) < caU112_ceil ∧
    (caU112_ceil - 1) ^ 46 ≤ caRelTail ^ 31 ∧
    -- 3. Initial spatial defect p_0 ≤ caP0 and temporal defect q_0 ≤ caQ0
    1 - (1 + tail23_56 / caLo23_14_lo ^ 4)⁻¹ ^ 2 ≤ caP0 ∧
    1 - (1 + caRelTail)⁻¹ ^ 2 ≤ caQ0 ∧
    0 ≤ tail23_56 ∧
    0 ≤ m155_1 ∧ 0 ≤ m155_2 ∧ 0 ≤ m155_3 ∧
    0 ≤ m23_1 ∧ 0 ≤ m23_2 ∧ 0 ≤ m23_3 := by
  decide +kernel

/-- All four upward-rounded coupled purity-bootstrap rounds `(56, 23) → (896, 368)` in exact `ℚ`. -/
theorem ca_four_rounded_updates_exact :
    ceilGrid7 (fQ (1 - (1 - caP0) ^ 2 * (1 - caQ0))) = caP1 ∧
    ceilGrid7 (fQ (1 - (1 - caQ0) ^ 2 * (1 - caP1))) = caQ1 ∧
    ceilGrid7 (fQ (1 - (1 - caP1) ^ 2 * (1 - caQ1))) = caP2 ∧
    ceilGrid7 (fQ (1 - (1 - caQ1) ^ 2 * (1 - caP2))) = caQ2 ∧
    ceilGrid7 (fQ (1 - (1 - caP2) ^ 2 * (1 - caQ2))) = caP3 ∧
    ceilGrid7 (fQ (1 - (1 - caQ2) ^ 2 * (1 - caP3))) = caQ3 ∧
    ceilGrid7 (fQ (1 - (1 - caP3) ^ 2 * (1 - caQ3))) = caP4 ∧
    ceilGrid7 (fQ (1 - (1 - caQ3) ^ 2 * (1 - caP4))) = caQ4 ∧
    caP4 < 1 / 100 ∧ caQ4 < 1 / 100 := by
  decide +kernel

/-! ## Section 3: Four-Round Bootstrap & Temperature-Transfer Lemmas -/

/-- Exact four-round propagation `(56, 23) → (896, 368)` inside `PuritySystem1D`,
returning the stronger exact ceilings `(caP4 = 53546/10^7, caQ4 = 9312/10^7)`. -/
theorem ca_four_rounds_to_896_exact (sys : PuritySystem1D)
    (hS0 : 1 - sys.S 56 (23 : ℝ) ≤ (caP0 : ℝ))
    (hT0 : 1 - sys.T 112 (23 : ℝ) ≤ (caQ0 : ℝ)) :
    1 - sys.S 896 (368 : ℝ) ≤ (caP4 : ℝ) ∧
    1 - sys.T 1792 (368 : ℝ) ≤ (caQ4 : ℝ) := by
  have hex := ca_four_rounded_updates_exact
  have step : ∀ {n : ℕ} {b : ℝ} {p q p' q' : ℚ},
      Even n → 4 ≤ n → 0 < b →
      0 ≤ p → p < 1 → 0 ≤ q → q < 1 → p' < 1 →
      ceilGrid7 (fQ (1 - (1 - p) ^ 2 * (1 - q))) = p' →
      ceilGrid7 (fQ (1 - (1 - q) ^ 2 * (1 - p'))) = q' →
      1 - sys.S n b ≤ (p : ℝ) → 1 - sys.T (2 * n) b ≤ (q : ℝ) →
      1 - sys.S (2 * n) (2 * b) ≤ (p' : ℝ) ∧ 1 - sys.T (4 * n) (2 * b) ≤ (q' : ℝ) := by
    intro n b p q p' q' hn h4 hb hp0 hp1 hq0 hq1 hp'1 hp'eq hq'eq hS hT
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
  have r1 := step (n := 56) (b := 23) ⟨28, by omega⟩ (by omega) (by norm_num)
    (by unfold caP0; norm_num) (by unfold caP0; norm_num)
    (by unfold caQ0; norm_num) (by unfold caQ0; norm_num)
    (by unfold caP1; norm_num) hex.1 hex.2.1 hS0 hT0
  have r2 := step (n := 112) (b := 46) ⟨56, by omega⟩ (by omega) (by norm_num)
    (by unfold caP1; norm_num) (by unfold caP1; norm_num)
    (by unfold caQ1; norm_num) (by unfold caQ1; norm_num)
    (by unfold caP2; norm_num) hex.2.2.1 hex.2.2.2.1
    (by convert r1.1 using 2 <;> norm_num) (by convert r1.2 using 2 <;> norm_num)
  have r3 := step (n := 224) (b := 92) ⟨112, by omega⟩ (by omega) (by norm_num)
    (by unfold caP2; norm_num) (by unfold caP2; norm_num)
    (by unfold caQ2; norm_num) (by unfold caQ2; norm_num)
    (by unfold caP3; norm_num) hex.2.2.2.2.1 hex.2.2.2.2.2.1
    (by convert r2.1 using 2 <;> norm_num) (by convert r2.2 using 2 <;> norm_num)
  have r4 := step (n := 448) (b := 184) ⟨224, by omega⟩ (by omega) (by norm_num)
    (by unfold caP3; norm_num) (by unfold caP3; norm_num)
    (by unfold caQ3; norm_num) (by unfold caQ3; norm_num)
    (by unfold caP4; norm_num) hex.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.1
    (by convert r3.1 using 2 <;> norm_num) (by convert r3.2 using 2 <;> norm_num)
  constructor
  · convert r4.1 using 2 <;> norm_num
  · convert r4.2 using 2 <;> norm_num

/-- Finite `ℓ^r` monotonicity (`r ≥ 1`): `∑_{k ∈ s} u_k^r ≤ (∑_{k ∈ s} u_k)^r` for `u_k ≥ 0`. -/
private lemma finset_rpow_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ k ∈ s, 0 ≤ u k) {r : ℝ} (hr : 1 ≤ r) :
    ∑ k ∈ s, u k ^ r ≤ (∑ k ∈ s, u k) ^ r := by
  set S := ∑ k ∈ s, u k
  have hS_nn : 0 ≤ S := Finset.sum_nonneg hu
  by_cases hS0 : S = 0
  · have hall0 : ∀ k ∈ s, u k = 0 := (Finset.sum_eq_zero_iff_of_nonneg hu).mp hS0
    have hr_pos : 0 < r := by linarith
    rw [hS0, Real.zero_rpow hr_pos.ne']
    exact (Finset.sum_eq_zero fun k hk => by rw [hall0 k hk, Real.zero_rpow hr_pos.ne']).le
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
    have hterm : ∀ k ∈ s, (u k / S) ^ r ≤ u k / S := fun k hk => by
      have hnn : 0 ≤ u k / S := div_nonneg (hu k hk) hS_pos.le
      have hle1 : u k / S ≤ 1 := (div_le_one hS_pos).mpr (Finset.single_le_sum hu hk)
      by_cases hx0 : u k / S = 0
      · rw [hx0, Real.zero_rpow (by linarith)]
      · have hx_pos : 0 < u k / S := lt_of_le_of_ne hnn (Ne.symm hx0)
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx_pos hle1 hr
    have hsum_le : ∑ k ∈ s, (u k / S) ^ r ≤ 1 := by
      calc ∑ k ∈ s, (u k / S) ^ r
          ≤ ∑ k ∈ s, u k / S := Finset.sum_le_sum hterm
        _ = (∑ k ∈ s, u k) / S := (Finset.sum_div s u S).symm
        _ = 1 := div_self hS_pos.ne'
    have hSr_pos : 0 < S ^ r := Real.rpow_pos_of_pos hS_pos r
    have hmul : (∑ k ∈ s, (u k / S) ^ r) * S ^ r ≤ 1 * S ^ r :=
      mul_le_mul_of_nonneg_right hsum_le hSr_pos.le
    rw [one_mul, Finset.sum_mul] at hmul
    have hrew : ∀ k ∈ s, (u k / S) ^ r * S ^ r = u k ^ r := fun k hk => by
      rw [Real.div_rpow (hu k hk) hS_pos.le, div_mul_cancel₀ _ hSr_pos.ne']
    rwa [Finset.sum_congr rfl hrew] at hmul

/-- **Temperature-Transfer Temporal Purity Bound (`31/2 → 23` at `L = 112`)**:
if `Z_112(31/2) ≤ U` (`1 < U`), `(U - 1)^46 ≤ R^31` (`0 ≤ R`), and there exists a shifted
ground level `E_{k₀} ≤ 0`, then `T(112, 23) = Z_112(46) / Z_112(23)^2 ≥ (1 + R)⁻¹^2`! -/
theorem temp_transfer_112 {d : ℕ} (E : Fin d → ℝ) (k₀ : Fin d)
    (hmin : ∀ k : Fin d, E k₀ ≤ E k) (hE0_le : E k₀ ≤ 0)
    {U R : ℝ} (hU1 : 1 < U) (hR0 : 0 ≤ R)
    (hZ155_le : ∑ k : Fin d, Real.exp (-(31 / 2 : ℝ) * E k) ≤ U)
    (hpow : (U - 1) ^ 46 ≤ R ^ 31) :
    (1 + R)⁻¹ ^ 2 ≤
      (∑ k : Fin d, Real.exp (-46 * E k)) / (∑ k : Fin d, Real.exp (-23 * E k)) ^ 2 := by
  let s' : Finset (Fin d) := Finset.univ.erase k₀
  have hw0_ge1 : (1 : ℝ) ≤ Real.exp (-(31 / 2 : ℝ) * E k₀) :=
    Real.one_le_exp (by nlinarith)
  have hw0_pos : 0 < Real.exp (-(31 / 2 : ℝ) * E k₀) := Real.exp_pos _
  -- Relative Boltzmann weights at b = 31/2: u k = exp(-(31/2) * (E k - E k₀))
  let u : Fin d → ℝ := fun k => Real.exp (-(31 / 2 : ℝ) * (E k - E k₀))
  have hu_nn : ∀ k ∈ s', 0 ≤ u k := fun k _ => (Real.exp_pos _).le
  have hsum_u_le : ∑ k ∈ s', u k ≤ U - 1 := by
    have hsplit : ∑ k : Fin d, Real.exp (-(31 / 2 : ℝ) * E k) =
        Real.exp (-(31 / 2 : ℝ) * E k₀) * (1 + ∑ k ∈ s', u k) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀), mul_add, mul_one, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [u]; rw [← Real.exp_add]; congr 1; ring
    rw [hsplit] at hZ155_le
    have hnn : 0 ≤ ∑ k ∈ s', u k := Finset.sum_nonneg hu_nn
    have h1 : 1 + ∑ k ∈ s', u k ≤ U := by nlinarith
    linarith
  -- Raise to r = 46/31 ≥ 1
  have hr : (1 : ℝ) ≤ 46 / 31 := by norm_num
  have hsum_ur : ∑ k ∈ s', u k ^ (46 / 31 : ℝ) ≤ R := by
    have h1 : ∑ k ∈ s', u k ^ (46 / 31 : ℝ) ≤ (∑ k ∈ s', u k) ^ (46 / 31 : ℝ) :=
      finset_rpow_sum_le s' u hu_nn hr
    have h2 : (∑ k ∈ s', u k) ^ (46 / 31 : ℝ) ≤ (U - 1) ^ (46 / 31 : ℝ) :=
      Real.rpow_le_rpow (Finset.sum_nonneg hu_nn) hsum_u_le (by positivity)
    have h3 : (U - 1) ^ (46 / 31 : ℝ) ≤ R := by
      have hU_pos : 0 < U - 1 := by linarith
      have hpow31 : ((U - 1) ^ (46 / 31 : ℝ)) ^ (31 : ℕ) ≤ R ^ (31 : ℕ) := by
        rw [← Real.rpow_natCast ((U - 1) ^ (46 / 31 : ℝ)) 31, ← Real.rpow_mul hU_pos.le]
        have h46 : (46 / 31 : ℝ) * (31 : ℕ) = (46 : ℕ) := by norm_num
        rw [h46, Real.rpow_natCast]; exact hpow
      by_contra hgt; push Not at hgt
      have hlt := pow_lt_pow_left₀ hgt hR0 (by norm_num : 31 ≠ 0)
      linarith
    exact h1.trans (h2.trans h3)
  -- Express Z(23) and Z(46) via `exp(-23 * E k₀)`
  have hZ23_eq : ∑ k : Fin d, Real.exp (-23 * E k) =
      Real.exp (-23 * E k₀) * (1 + ∑ k ∈ s', u k ^ (46 / 31 : ℝ)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀), mul_add, mul_one, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [u]; rw [← Real.exp_mul, ← Real.exp_add]; congr 1; ring
  have hZ23_pos : 0 < ∑ k : Fin d, Real.exp (-23 * E k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨k₀, Finset.mem_univ k₀⟩
  have hZ46_ge : (Real.exp (-23 * E k₀)) ^ 2 ≤ ∑ k : Fin d, Real.exp (-46 * E k) := by
    have hsq : (Real.exp (-23 * E k₀)) ^ 2 = Real.exp (-46 * E k₀) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hsq]
    exact Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k₀)
  have hZ23_le : ∑ k : Fin d, Real.exp (-23 * E k) ≤ Real.exp (-23 * E k₀) * (1 + R) := by
    rw [hZ23_eq]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hden_pos : 0 < (Real.exp (-23 * E k₀) * (1 + R)) ^ 2 :=
    pow_pos (mul_pos (Real.exp_pos _) (by linarith)) 2
  have h1 : (Real.exp (-23 * E k₀)) ^ 2 / (Real.exp (-23 * E k₀) * (1 + R)) ^ 2 ≤
      (∑ k : Fin d, Real.exp (-46 * E k)) / (∑ k : Fin d, Real.exp (-23 * E k)) ^ 2 := by
    calc (Real.exp (-23 * E k₀)) ^ 2 / (Real.exp (-23 * E k₀) * (1 + R)) ^ 2
        ≤ (Real.exp (-23 * E k₀)) ^ 2 / (∑ k : Fin d, Real.exp (-23 * E k)) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hZ23_pos 2)
            (pow_le_pow_left₀ hZ23_pos.le hZ23_le 2)
      _ ≤ (∑ k : Fin d, Real.exp (-46 * E k)) / (∑ k : Fin d, Real.exp (-23 * E k)) ^ 2 :=
          div_le_div_of_nonneg_right hZ46_ge (sq_nonneg _)
  have hcancel : (Real.exp (-23 * E k₀)) ^ 2 / (Real.exp (-23 * E k₀) * (1 + R)) ^ 2 = (1 + R)⁻¹ ^ 2 := by
    have he : Real.exp (-23 * E k₀) ≠ 0 := (Real.exp_pos _).ne'
    have hr1 : (1 + R) ≠ 0 := by linarith
    rw [mul_pow, inv_pow, ← one_div]
    field_simp [he, hr1]
  rwa [hcancel] at h1

/-! ## Section 4: Master Candidate A (`Δ = 1, D = 1/4`) Seed & Uniform Gap Theorems -/

/-- Helper: extract both `|lam_s i| < cap_s` and `Z_{14r} - |lam_0 i₀|^{14r} ≤ tail` at a given
table `tbl` (`b = 31/2` or `b = 23`), using the verified degree-14 filters and `D₄` projections. -/
private lemma ca_sector_caps_and_moments
    {ι : Fin 4 → Type*} (lam : ∀ s : Fin 4, ι s → ℝ)
    (tbl : List (ℤ × ℤ × ℤ × ℤ))
    (hsumm : ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam s i| ^ n))
    (hraw_I : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n) + 2 * (∑' i, lam 3 i ^ n)) -
        ((caRawQuad tbl n).1 : ℝ)| ≤ (caEps : ℝ))
    (hraw_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n) - 2 * (∑' i, lam 3 i ^ n)) -
        ((caRawQuad tbl n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw_X : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam 0 i ^ n) - (∑' i, lam 2 i ^ n)) -
        ((caRawQuad tbl n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw_F : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam 0 i ^ n) - 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n)) -
        ((caRawQuad tbl n).2.2.2 : ℝ)| ≤ (caEps : ℝ)) :
    ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |(∑' i, lam s i ^ n) - (caMoment tbl s n : ℝ)| ≤ (caSectorEps s : ℝ) := by
  intro s n h4 h14
  have hI := abs_le.mp (hraw_I n h4 h14)
  have hZ := abs_le.mp (hraw_Z n h4 h14)
  have hX := abs_le.mp (hraw_X n h4 h14)
  have hF := abs_le.mp (hraw_F n h4 h14)
  fin_cases s
  · dsimp [caMoment, caSectorEps]; push_cast; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · dsimp [caMoment, caSectorEps]; push_cast; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · dsimp [caMoment, caSectorEps]; push_cast; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · dsimp [caMoment, caSectorEps]; push_cast; exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Helper: combine positive-ray and negative-ray checks on a sector into `|lam i| < max cap_+ cap_-`. -/
private lemma ca_sector_abs_lt {ι : Type*} (lam : ι → ℝ)
    (tbl : List (ℤ × ℤ × ℤ × ℤ)) (sec : Fin 4)
    (rayP rayN : ℤ × ℚ × List ℤ)
    (hsignP : rayP.1 = 1) (hsignN : rayN.1 = -1)
    (hchkP : checkRay14 tbl sec rayP = true)
    (hchkN : checkRay14 tbl sec rayN = true)
    (hsumm : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam i| ^ n))
    (hmom : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |(∑' i, lam i ^ n) - (caMoment tbl sec n : ℝ)| ≤ (caSectorEps sec : ℝ)) :
    ∀ i : ι, |lam i| < ((max rayP.2.1 rayN.2.1 : ℚ) : ℝ) := by
  intro i
  have hP := polynomial_filter14_ray_tsum lam tbl sec rayP hchkP hsumm hmom i
  have hN := polynomial_filter14_ray_tsum lam tbl sec rayN hchkN hsumm hmom i
  rw [hsignP] at hP; rw [hsignN] at hN
  push_cast at hP hN ⊢
  rw [abs_lt]
  constructor
  · have hle : (rayN.2.1 : ℝ) ≤ max (rayP.2.1 : ℝ) (rayN.2.1 : ℝ) := le_max_right _ _
    linarith
  · have hle : (rayP.2.1 : ℝ) ≤ max (rayP.2.1 : ℝ) (rayN.2.1 : ℝ) := le_max_left _ _
    linarith

/-- Helper: given 4-sector moments at temperature `b`, caps `c14_s` on `|lam s i|^14`,
lower threshold `lo14_lo ≤ lo^14 ≤ lo14_hi`, and `1 ≤ Z_112(b)`, extract a dominant
eigenvalue `i₀` in sector 0 and bound `Z_{14r}(b) - |lam 0 i₀|^{14r}` for `r = 4, 8`. -/
private lemma ca_extract_dominant_and_tail
    {ι : Fin 4 → Type*} (lam : ∀ s : Fin 4, ι s → ℝ)
    (Z : ℕ → ℝ) (tbl : List (ℤ × ℤ × ℤ × ℤ))
    (lo lo14_lo lo14_hi c14_1 c14_2 c14_3 : ℚ)
    (hsumm : ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam s i| ^ n))
    (hZ_even : ∀ n : ℕ, Even n → 4 ≤ n →
      Z n = (∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) +
            (∑' i, lam 2 i ^ n) + 2 * (∑' i, lam 3 i ^ n))
    (hmom14 : ∀ s : Fin 4, |(∑' i, lam s i ^ 14) - (caMoment tbl s 14 : ℝ)| ≤ (caSectorEps s : ℝ))
    (hcap1 : ∀ i, |lam 1 i| ^ 14 ≤ (c14_1 : ℝ))
    (hcap2 : ∀ i, |lam 2 i| ^ 14 ≤ (c14_2 : ℝ))
    (hcap3 : ∀ i, |lam 3 i| ^ 14 ≤ (c14_3 : ℝ))
    (hc1_pos : (0 : ℚ) < c14_1) (hc2_pos : (0 : ℚ) < c14_2) (hc3_pos : (0 : ℚ) < c14_3)
    (hlo_pos : (0 : ℚ) < lo) (hlo_hi_pos : (0 : ℚ) < lo14_hi)
    (hlo_lo_le : lo14_lo ≤ lo ^ 14) (hlo_le_hi : lo ^ 14 ≤ lo14_hi)
    (hm0_ge : lo14_lo ≤ caMass tbl 0)
    (hm1_nn : 0 ≤ caMass tbl 1) (hm2_nn : 0 ≤ caMass tbl 2) (hm3_nn : 0 ≤ caMass tbl 3)
    (hdom_lt1 : cappedMassQ (caMass tbl 0) lo14_hi 8 +
      (2 * cappedMassQ (caMass tbl 1) c14_1 8 +
       cappedMassQ (caMass tbl 2) c14_2 8 +
       2 * cappedMassQ (caMass tbl 3) c14_3 8) < 1)
    (hZ112_ge1 : 1 ≤ Z 112) :
    ∃ i₀ : ι 0, (lo : ℝ) < |lam 0 i₀| ∧
      (∀ r : ℕ, 1 ≤ r →
        Z (14 * r) - |lam 0 i₀| ^ (14 * r) ≤
          ((caMass tbl 0 - lo14_lo) ^ r +
            (2 * cappedMassQ (caMass tbl 1) c14_1 r +
             cappedMassQ (caMass tbl 2) c14_2 r +
             2 * cappedMassQ (caMass tbl 3) c14_3 r) : ℚ)) := by
  have hpow14 : ∀ x : ℝ, x ^ 14 = |x| ^ 14 := fun x => by
    rw [show (14 : ℕ) = 2 * 7 by rfl, pow_mul, pow_mul, sq_abs]
  have hmass_le : ∀ s : Fin 4, ∑' i, |lam s i| ^ 14 ≤ (caMass tbl s : ℝ) := fun s => by
    have h := (abs_le.mp (hmom14 s)).2
    unfold caMass; push_cast
    simpa [hpow14] using (by linarith : ∑' i, lam s i ^ 14 ≤ (caMoment tbl s 14 : ℝ) + (caSectorEps s : ℝ))
  have hother : ∀ r : ℕ, 1 ≤ r →
      2 * (∑' i, lam 1 i ^ (14 * r)) + (∑' i, lam 2 i ^ (14 * r)) + 2 * (∑' i, lam 3 i ^ (14 * r)) ≤
      ((2 * cappedMassQ (caMass tbl 1) c14_1 r +
        cappedMassQ (caMass tbl 2) c14_2 r +
        2 * cappedMassQ (caMass tbl 3) c14_3 r : ℚ) : ℝ) := fun r hr => by
    have hbnd : ∀ (s : Fin 4) (c14 : ℚ), (0 : ℚ) < c14 → 0 ≤ caMass tbl s →
        (∀ i, |lam s i| ^ 14 ≤ (c14 : ℝ)) →
        ∑' i, lam s i ^ (14 * r) ≤ (cappedMassQ (caMass tbl s) c14 r : ℝ) := fun s c14 hc hm hcap => by
      have hcm := capped_mass_tsum (fun i => |lam s i| ^ 14)
        (by exact_mod_cast hc) (by exact_mod_cast hm)
        (fun i => pow_nonneg (abs_nonneg _) 14) hcap (hsumm s 14 (by omega)) (hmass_le s) hr
      have hrew : ∀ i, lam s i ^ (14 * r) = (|lam s i| ^ 14) ^ r := fun i => by rw [pow_mul, hpow14]
      simp_rw [hrew]; rw [cappedMassQ_cast]; exact hcm.2
    have h1 := hbnd 1 c14_1 hc1_pos hm1_nn hcap1
    have h2 := hbnd 2 c14_2 hc2_pos hm2_nn hcap2
    have h3 := hbnd 3 c14_3 hc3_pos hm3_nn hcap3
    push_cast; linarith
  -- Existence of dominant `i₀ : ι 0` with `lo < |lam 0 i₀|`
  have hex_dom : ∃ i₀ : ι 0, (lo : ℝ) < |lam 0 i₀| := by
    by_contra hno; push Not at hno
    have hcap0 : ∀ i, |lam 0 i| ^ 14 ≤ (lo14_hi : ℝ) := fun i => by
      have h1 : |lam 0 i| ^ 14 ≤ (lo : ℝ) ^ 14 := pow_le_pow_left₀ (abs_nonneg _) (hno i) 14
      have h2 : (lo : ℝ) ^ 14 ≤ (lo14_hi : ℝ) := by exact_mod_cast hlo_le_hi
      exact h1.trans h2
    have hm0_nn : (0 : ℚ) ≤ caMass tbl 0 := by
      have hR : (0 : ℝ) ≤ (caMass tbl 0 : ℝ) :=
        le_trans (tsum_nonneg fun i => pow_nonneg (abs_nonneg _) 14) (hmass_le 0)
      exact_mod_cast hR
    have hcm0 := capped_mass_tsum (fun i => |lam 0 i| ^ 14)
      (by exact_mod_cast hlo_hi_pos) (by exact_mod_cast hm0_nn)
      (fun i => pow_nonneg (abs_nonneg _) 14) hcap0 (hsumm 0 14 (by omega)) (hmass_le 0) (r := 8) (by omega)
    have hS0 : ∑' i, lam 0 i ^ 112 ≤ (cappedMassQ (caMass tbl 0) lo14_hi 8 : ℝ) := by
      have hrew : ∀ i, lam 0 i ^ 112 = (|lam 0 i| ^ 14) ^ 8 := fun i => by
        rw [show (112 : ℕ) = 14 * 8 by rfl, pow_mul, hpow14]
      simp_rw [hrew]; rw [cappedMassQ_cast]; exact hcm0.2
    have hO8 := hother 8 (by omega)
    have hZ112_eq := hZ_even 112 ⟨56, by omega⟩ (by omega)
    have hlt1 : ((cappedMassQ (caMass tbl 0) lo14_hi 8 +
        (2 * cappedMassQ (caMass tbl 1) c14_1 8 +
         cappedMassQ (caMass tbl 2) c14_2 8 +
         2 * cappedMassQ (caMass tbl 3) c14_3 8) : ℚ) : ℝ) < 1 := by exact_mod_cast hdom_lt1
    push_cast at hlt1 hO8
    linarith
  rcases hex_dom with ⟨i₀, hi₀⟩
  refine ⟨i₀, hi₀, fun r hr => ?_⟩
  classical
  let tRem : ι 0 → ℝ := fun i => if i = i₀ then 0 else |lam 0 i| ^ 14
  have htRem_nn : ∀ i, 0 ≤ tRem i := fun i => by dsimp [tRem]; split_ifs <;> positivity
  have htRem_s : Summable tRem :=
    Summable.of_nonneg_of_le htRem_nn (fun i => by dsimp [tRem]; split_ifs <;> [positivity; exact le_rfl])
      (hsumm 0 14 (by omega))
  have htRem_sum : ∑' i, tRem i ≤ ((caMass tbl 0 - lo14_lo : ℚ) : ℝ) := by
    have hadd : (∑' i, tRem i) + |lam 0 i₀| ^ 14 = ∑' i, |lam 0 i| ^ 14 := by
      have hpt : ∀ i, tRem i + (if i = i₀ then |lam 0 i₀| ^ 14 else 0) = |lam 0 i| ^ 14 := fun i => by
        dsimp [tRem]; by_cases h : i = i₀ <;> simp [h]
      have h1s : Summable (fun i : ι 0 => if i = i₀ then |lam 0 i₀| ^ 14 else 0) :=
        (hasSum_ite_eq i₀ (|lam 0 i₀| ^ 14)).summable
      have hsum_add := htRem_s.tsum_add h1s
      simp_rw [hpt] at hsum_add; rw [tsum_ite_eq] at hsum_add; exact hsum_add.symm
    have hi₀_14 : (lo14_lo : ℝ) ≤ |lam 0 i₀| ^ 14 :=
      le_trans (by exact_mod_cast hlo_lo_le) (pow_le_pow_left₀ (by exact_mod_cast hlo_pos.le) hi₀.le 14)
    have h0 := hmass_le 0
    push_cast; linarith
  have hdiff_nn : 0 ≤ ((caMass tbl 0 - lo14_lo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ caMass tbl 0 - lo14_lo := sub_nonneg.mpr hm0_ge
    exact_mod_cast this
  have huncap := uncapped_mass_tsum tRem hdiff_nn htRem_nn htRem_s htRem_sum hr
  have hJ_split : (∑' i, lam 0 i ^ (14 * r)) - |lam 0 i₀| ^ (14 * r) = ∑' i, tRem i ^ r := by
    have hpt : ∀ i, tRem i ^ r + (if i = i₀ then |lam 0 i₀| ^ (14 * r) else 0) = lam 0 i ^ (14 * r) := fun i => by
      dsimp [tRem]
      by_cases h : i = i₀
      · subst h; rw [if_pos rfl, if_pos rfl, zero_pow (by omega : r ≠ 0), zero_add, pow_mul, ← hpow14 (lam 0 i), ← pow_mul]
      · rw [if_neg h, if_neg h, add_zero, ← hpow14 (lam 0 i), ← pow_mul]
    have h1s : Summable (fun i : ι 0 => if i = i₀ then |lam 0 i₀| ^ (14 * r) else 0) :=
      (hasSum_ite_eq i₀ (|lam 0 i₀| ^ (14 * r))).summable
    have hsum_add := huncap.1.tsum_add h1s
    simp_rw [hpt] at hsum_add; rw [tsum_ite_eq] at hsum_add; linarith
  have hZ_eq := hZ_even (14 * r) ⟨7 * r, by omega⟩ (by omega)
  have hO := hother r hr
  push_cast at huncap hO ⊢
  linarith [huncap.2]

set_option maxHeartbeats 800000 in
/-- **Candidate A (`Δ = 1, D = 1/4`) Seed `(896, 368)` from Raw 4-Seam Thermal Tables**:
from any `SpectralSystem1D` satisfying the `D₄` 4-seam spatial decomposition at `b = 31/2` and `b = 23`,
all 88 raw trace intervals (radius `10⁻⁵`), and the `L = 112` trial energy witness `E_0(112) + 112 a ≤ 0`,
derives inside Lean 4's pure kernel:
- `1 - S(56, 23) ≤ caP0 = 1215302 / 10^7` and `1 - T(112, 23) ≤ caQ0 = 1203214 / 10^7`,
- `1 - S(896, 368) ≤ caP4 = 53546 / 10^7` and `1 - T(1792, 368) ≤ caQ4 = 9312 / 10^7`. -/
theorem candidate_a_seed896_from_raw_table (sys : SpectralSystem1D)
    {ι155 ι23 : Fin 4 → Type*}
    (lam155 : ∀ s : Fin 4, ι155 s → ℝ)
    (lam23  : ∀ s : Fin 4, ι23 s → ℝ)
    (hsumm155 : ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam155 s i| ^ n))
    (hsumm23  : ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam23 s i| ^ n))
    (hZ155_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (31 / 2 : ℝ) = (∑' i, lam155 0 i ^ n) + 2 * (∑' i, lam155 1 i ^ n) +
                              (∑' i, lam155 2 i ^ n) + 2 * (∑' i, lam155 3 i ^ n))
    (hZ23_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (23 : ℝ) = (∑' i, lam23 0 i ^ n) + 2 * (∑' i, lam23 1 i ^ n) +
                          (∑' i, lam23 2 i ^ n) + 2 * (∑' i, lam23 3 i ^ n))
    -- 44 raw shifted trace enclosures at b = 31/2 (n = 4..14, seams I, Rz, Rx, R4, radius 10⁻⁵)
    (hraw155_I : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) + 2 * (∑' i, lam155 1 i ^ n) + (∑' i, lam155 2 i ^ n) + 2 * (∑' i, lam155 3 i ^ n)) -
        ((caRawQuad caTable155 n).1 : ℝ)| ≤ (caEps : ℝ))
    (hraw155_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) + 2 * (∑' i, lam155 1 i ^ n) + (∑' i, lam155 2 i ^ n) - 2 * (∑' i, lam155 3 i ^ n)) -
        ((caRawQuad caTable155 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw155_X : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) - (∑' i, lam155 2 i ^ n)) -
        ((caRawQuad caTable155 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw155_F : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) - 2 * (∑' i, lam155 1 i ^ n) + (∑' i, lam155 2 i ^ n)) -
        ((caRawQuad caTable155 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    -- 44 raw shifted trace enclosures at b = 23 (n = 4..14, seams I, Rz, Rx, R4, radius 10⁻⁵)
    (hraw23_I : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) + 2 * (∑' i, lam23 1 i ^ n) + (∑' i, lam23 2 i ^ n) + 2 * (∑' i, lam23 3 i ^ n)) -
        ((caRawQuad caTable23 n).1 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) + 2 * (∑' i, lam23 1 i ^ n) + (∑' i, lam23 2 i ^ n) - 2 * (∑' i, lam23 3 i ^ n)) -
        ((caRawQuad caTable23 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_X : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) - (∑' i, lam23 2 i ^ n)) -
        ((caRawQuad caTable23 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_F : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) - 2 * (∑' i, lam23 1 i ^ n) + (∑' i, lam23 2 i ^ n)) -
        ((caRawQuad caTable23 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    -- Single L = 112 variational trial bound (`E_0(112) + 112 a ≤ 0`)
    (htrial112 : ∃ k : Fin (sys.d 112), sys.E 112 k + sys.a * (112 : ℝ) ≤ 0) :
    (1 - sys.toPuritySystem1D.S 56 (23 : ℝ) ≤ (caP0 : ℝ) ∧
     1 - sys.toPuritySystem1D.T 112 (23 : ℝ) ≤ (caQ0 : ℝ)) ∧
    (1 - sys.toPuritySystem1D.S 896 (368 : ℝ) ≤ (caP4 : ℝ) ∧
     1 - sys.toPuritySystem1D.T 1792 (368 : ℝ) ≤ (caQ4 : ℝ)) := by
  have hpows := ca_pows14_exact
  have hinit := ca_initial_bounds_exact
  have hr155 := ca_rays155_exact
  have hr23 := ca_rays23_exact
  -- 1. Trial energy implies `1 ≤ Z_112(b)` for all `b > 0`
  rcases htrial112 with ⟨kt, hkt⟩
  have hZ112_ge1 : ∀ b : ℝ, 0 < b → 1 ≤ sys.Z 112 b := fun b hb => by
    have hZeq : sys.Z 112 b = ∑ k : Fin (sys.d 112), Real.exp (-b * (sys.E 112 k + sys.a * (112 : ℝ))) :=
      sys.Z_eq 112 b ⟨56, by omega⟩ (by omega) hb
    rw [hZeq]
    have h1 : (1 : ℝ) ≤ Real.exp (-b * (sys.E 112 kt + sys.a * (112 : ℝ))) :=
      Real.one_le_exp (by nlinarith)
    exact h1.trans (Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ kt))
  -- 2. Projected sector moments at b = 31/2 and b = 23
  have hmom155 := ca_sector_caps_and_moments lam155 caTable155 hsumm155 hraw155_I hraw155_Z hraw155_X hraw155_F
  have hmom23  := ca_sector_caps_and_moments lam23 caTable23 hsumm23 hraw23_I hraw23_Z hraw23_X hraw23_F
  -- 3. 14th-power caps from the 16 verified degree-14 rays
  have hcap155_0 : ∀ i, |lam155 0 i| ^ 14 ≤ (caCap155_14_0 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam155 0) caTable155 0 _ _ rfl rfl hr155.1 hr155.2.1 (hsumm155 0) (hmom155 0) i).le 14).trans (by exact_mod_cast hpows.2.2.1)
  have hcap155_1 : ∀ i, |lam155 1 i| ^ 14 ≤ (caCap155_14_1 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam155 1) caTable155 1 _ _ rfl rfl hr155.2.2.1 hr155.2.2.2.1 (hsumm155 1) (hmom155 1) i).le 14).trans (by exact_mod_cast hpows.2.2.2.1)
  have hcap155_2 : ∀ i, |lam155 2 i| ^ 14 ≤ (caCap155_14_2 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam155 2) caTable155 2 _ _ rfl rfl hr155.2.2.2.2.1 hr155.2.2.2.2.2.1 (hsumm155 2) (hmom155 2) i).le 14).trans (by exact_mod_cast hpows.2.2.2.2.1)
  have hcap155_3 : ∀ i, |lam155 3 i| ^ 14 ≤ (caCap155_14_3 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam155 3) caTable155 3 _ _ rfl rfl hr155.2.2.2.2.2.2.1 hr155.2.2.2.2.2.2.2 (hsumm155 3) (hmom155 3) i).le 14).trans (by exact_mod_cast hpows.2.2.2.2.2.1)
  have hcap23_1 : ∀ i, |lam23 1 i| ^ 14 ≤ (caCap23_14_1 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam23 1) caTable23 1 _ _ rfl rfl hr23.2.2.1 hr23.2.2.2.1 (hsumm23 1) (hmom23 1) i).le 14).trans (by exact_mod_cast hpows.2.2.2.2.2.2.2.2.2.1)
  have hcap23_2 : ∀ i, |lam23 2 i| ^ 14 ≤ (caCap23_14_2 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam23 2) caTable23 2 _ _ rfl rfl hr23.2.2.2.2.1 hr23.2.2.2.2.2.1 (hsumm23 2) (hmom23 2) i).le 14).trans (by exact_mod_cast hpows.2.2.2.2.2.2.2.2.2.2.1)
  have hcap23_3 : ∀ i, |lam23 3 i| ^ 14 ≤ (caCap23_14_3 : ℝ) := fun i =>
    (pow_le_pow_left₀ (abs_nonneg _) (ca_sector_abs_lt (lam23 3) caTable23 3 _ _ rfl rfl hr23.2.2.2.2.2.2.1 hr23.2.2.2.2.2.2.2 (hsumm23 3) (hmom23 3) i).le 14).trans (by exact_mod_cast hpows.2.2.2.2.2.2.2.2.2.2.2)
  -- 4. Dominant eigenvalue & upper bound `Z_112(31/2) ≤ caU112_ceil`
  have hdom155 := ca_extract_dominant_and_tail lam155 (fun n => sys.Z n (31 / 2 : ℝ)) caTable155
    caLo155 caLo155_14_lo caLo155_14_hi caCap155_14_1 caCap155_14_2 caCap155_14_3
    hsumm155 hZ155_even (fun s => hmom155 s 14 (by omega) (by omega))
    hcap155_1 hcap155_2 hcap155_3
    (by unfold caCap155_14_1; norm_num) (by unfold caCap155_14_2; norm_num) (by unfold caCap155_14_3; norm_num)
    (by unfold caLo155; norm_num) (by unfold caLo155_14_hi; norm_num)
    hpows.1 hpows.2.1 hinit.2.1
    hinit.2.2.2.2.2.2.2.2.2.2.1 hinit.2.2.2.2.2.2.2.2.2.2.2.1 hinit.2.2.2.2.2.2.2.2.2.2.2.2.1
    hinit.1 (hZ112_ge1 (31 / 2) (by norm_num))
  rcases hdom155 with ⟨i₀_155, _, htail155⟩
  have hZ112_le_U : sys.Z 112 (31 / 2 : ℝ) ≤ (caU112_ceil : ℝ) := by
    have ht8 : sys.Z 112 (31 / 2 : ℝ) - |lam155 0 i₀_155| ^ 112 ≤
        (((caMass caTable155 0 - caLo155_14_lo) ^ 8 +
          (2 * cappedMassQ (caMass caTable155 1) caCap155_14_1 8 +
           cappedMassQ (caMass caTable155 2) caCap155_14_2 8 +
           2 * cappedMassQ (caMass caTable155 3) caCap155_14_3 8) : ℚ) : ℝ) := by
      simpa only [show 14 * 8 = 112 from rfl] using htail155 8 (by omega)
    have hc8 : |lam155 0 i₀_155| ^ 112 ≤ (caCap155_14_0 : ℝ) ^ 8 := by
      rw [show (112 : ℕ) = 14 * 8 by rfl, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg (abs_nonneg _) 14) (hcap155_0 i₀_155) 8
    have hU_rat : ((caCap155_14_0 ^ 8 + ((caMass caTable155 0 - caLo155_14_lo) ^ 8 +
          (2 * cappedMassQ (caMass caTable155 1) caCap155_14_1 8 +
           cappedMassQ (caMass caTable155 2) caCap155_14_2 8 +
           2 * cappedMassQ (caMass caTable155 3) caCap155_14_3 8)) : ℚ) : ℝ) ≤ (caU112_ceil : ℝ) := by
      exact_mod_cast hinit.2.2.2.2.1
    push_cast at ht8 hU_rat
    linarith
  -- 5. Temporal purity `1 - T(112, 23) ≤ caQ0` via `temp_transfer_112`
  have hT112 : 1 - sys.toPuritySystem1D.T 112 (23 : ℝ) ≤ (caQ0 : ℝ) := by
    let E112 : Fin (sys.d 112) → ℝ := fun k => sys.E 112 k + sys.a * (112 : ℝ)
    have hd112 : 0 < sys.d 112 := sys.d_pos 112 ⟨56, by omega⟩ (by omega)
    have hne112 : (Finset.univ : Finset (Fin (sys.d 112))).Nonempty := ⟨⟨0, hd112⟩, Finset.mem_univ _⟩
    rcases Finset.exists_min_image Finset.univ E112 hne112 with ⟨k₀, _, hk₀_min⟩
    have hE0_le : E112 k₀ ≤ 0 := le_trans (hk₀_min kt (Finset.mem_univ kt)) hkt
    have hZ155_sum : ∑ k : Fin (sys.d 112), Real.exp (-(31 / 2 : ℝ) * E112 k) ≤ (caU112_ceil : ℝ) := by
      have hZeq : sys.Z 112 (31 / 2 : ℝ) = ∑ k : Fin (sys.d 112), Real.exp (-(31 / 2 : ℝ) * E112 k) :=
        sys.Z_eq 112 (31 / 2) ⟨56, by omega⟩ (by omega) (by norm_num)
      linarith
    have htr := temp_transfer_112 E112 k₀ (fun k => hk₀_min k (Finset.mem_univ k)) hE0_le
      (U := (caU112_ceil : ℝ)) (R := (caRelTail : ℝ))
      (by exact_mod_cast hinit.2.2.2.2.2.1) (by unfold caRelTail; norm_num)
      hZ155_sum (by exact_mod_cast hinit.2.2.2.2.2.2.1)
    have hTeq : sys.toPuritySystem1D.T 112 (23 : ℝ) =
        (∑ k : Fin (sys.d 112), Real.exp (-46 * E112 k)) /
        (∑ k : Fin (sys.d 112), Real.exp (-23 * E112 k)) ^ 2 := by
      unfold PuritySystem1D.T
      have h2b : 2 * (23 : ℝ) = 46 := by norm_num
      change sys.Z 112 (2 * (23 : ℝ)) / (sys.Z 112 (23 : ℝ)) ^ 2 = _
      have hZ46 : sys.Z 112 46 = ∑ k : Fin (sys.d 112), Real.exp (-46 * E112 k) :=
        sys.Z_eq 112 46 ⟨56, by omega⟩ (by omega) (by norm_num)
      have hZ23 : sys.Z 112 23 = ∑ k : Fin (sys.d 112), Real.exp (-23 * E112 k) :=
        sys.Z_eq 112 23 ⟨56, by omega⟩ (by omega) (by norm_num)
      rw [h2b, hZ46, hZ23]
    have hq_rat : (1 : ℝ) - (1 + (caRelTail : ℝ))⁻¹ ^ 2 ≤ (caQ0 : ℝ) := by
      have hq : ((1 - (1 + caRelTail)⁻¹ ^ 2 : ℚ) : ℝ) ≤ (caQ0 : ℝ) := by
        exact_mod_cast hinit.2.2.2.2.2.2.2.2.1
      push_cast at hq; exact hq
    rw [hTeq]; linarith
  -- 6. Dominant eigenvalue at b = 23 & spatial purity `1 - S(56, 23) ≤ caP0`
  have hS56 : 1 - sys.toPuritySystem1D.S 56 (23 : ℝ) ≤ (caP0 : ℝ) := by
    have hdom23 := ca_extract_dominant_and_tail lam23 (fun n => sys.Z n (23 : ℝ)) caTable23
      caLo23 caLo23_14_lo caLo23_14_hi caCap23_14_1 caCap23_14_2 caCap23_14_3
      hsumm23 hZ23_even (fun s => hmom23 s 14 (by omega) (by omega))
      hcap23_1 hcap23_2 hcap23_3
      (by unfold caCap23_14_1; norm_num) (by unfold caCap23_14_2; norm_num) (by unfold caCap23_14_3; norm_num)
      (by unfold caLo23; norm_num) (by unfold caLo23_14_hi; norm_num)
      hpows.2.2.2.2.2.2.1 hpows.2.2.2.2.2.2.2.1 hinit.2.2.2.1
      hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      hinit.2.2.1 (hZ112_ge1 23 (by norm_num))
    rcases hdom23 with ⟨i₀, hi₀, htail23⟩
    have hpow14 : ∀ x : ℝ, x ^ 14 = |x| ^ 14 := fun x => by
      rw [show (14 : ℕ) = 2 * 7 by rfl, pow_mul, pow_mul, sq_abs]
    set tail56Q : ℚ := (caMass caTable23 0 - caLo23_14_lo) ^ 4 +
      (2 * cappedMassQ (caMass caTable23 1) caCap23_14_1 4 +
       cappedMassQ (caMass caTable23 2) caCap23_14_2 4 +
       2 * cappedMassQ (caMass caTable23 3) caCap23_14_3 4)
    have hres56 : sys.Z 56 (23 : ℝ) - |lam23 0 i₀| ^ 56 ≤ (tail56Q : ℝ) := by
      simpa only [show 14 * 4 = 56 from rfl] using htail23 4 (by omega)
    have hZ56_pos : 0 < sys.Z 56 (23 : ℝ) := sys.Z_pos ⟨28, by omega⟩ (by omega) (by norm_num)
    have hZ112_ge_dom : |lam23 0 i₀| ^ 112 ≤ sys.Z 112 (23 : ℝ) := by
      rw [hZ23_even 112 ⟨56, by omega⟩ (by omega)]
      have h0 : |lam23 0 i₀| ^ 112 ≤ ∑' i, lam23 0 i ^ 112 := by
        have hrew : ∀ i, lam23 0 i ^ 112 = |lam23 0 i| ^ 112 := fun i => by
          rw [show (112 : ℕ) = 14 * 8 by rfl, pow_mul, hpow14, ← pow_mul]
        simp_rw [hrew]
        exact (hsumm23 0 112 (by omega)).le_tsum i₀ (fun k _ => pow_nonneg (abs_nonneg _) 112)
      have hnn : ∀ s : Fin 4, 0 ≤ ∑' i, lam23 s i ^ 112 := fun s => by
        have hrew : ∀ i, lam23 s i ^ 112 = |lam23 s i| ^ 112 := fun i => by
          rw [show (112 : ℕ) = 14 * 8 by rfl, pow_mul, hpow14, ← pow_mul]
        simp_rw [hrew]; exact tsum_nonneg fun k => pow_nonneg (abs_nonneg _) 112
      linarith [hnn 1, hnn 2, hnn 3]
    have hlo14_pos : 0 < (caLo23_14_lo : ℝ) := by unfold caLo23_14_lo; norm_num
    have hlo56_pos : 0 < (caLo23_14_lo : ℝ) ^ 4 := pow_pos hlo14_pos 4
    have hdom56_ge : (caLo23_14_lo : ℝ) ^ 4 ≤ |lam23 0 i₀| ^ 56 := by
      rw [show (56 : ℕ) = 14 * 4 by rfl, pow_mul]
      have h14 : (caLo23_14_lo : ℝ) ≤ |lam23 0 i₀| ^ 14 :=
        le_trans (by exact_mod_cast hpows.2.2.2.2.2.2.1)
          (pow_le_pow_left₀ (by unfold caLo23; norm_num) hi₀.le 14)
      exact pow_le_pow_left₀ hlo14_pos.le h14 4
    have hdom56_pos : 0 < |lam23 0 i₀| ^ 56 := lt_of_lt_of_le hlo56_pos hdom56_ge
    have htail_nn : 0 ≤ (tail56Q : ℝ) := by exact_mod_cast hinit.2.2.2.2.2.2.2.2.2.1
    have hrat_le : sys.Z 56 (23 : ℝ) / |lam23 0 i₀| ^ 56 ≤ 1 + (tail56Q : ℝ) / (caLo23_14_lo : ℝ) ^ 4 := by
      have h1 : sys.Z 56 (23 : ℝ) / |lam23 0 i₀| ^ 56 =
          1 + (sys.Z 56 (23 : ℝ) - |lam23 0 i₀| ^ 56) / |lam23 0 i₀| ^ 56 := by
        rw [sub_div, div_self hdom56_pos.ne']; ring
      rw [h1]
      have h2 := div_le_div_of_nonneg_right hres56 hdom56_pos.le
      have h3 := div_le_div_of_nonneg_left htail_nn hlo56_pos hdom56_ge
      linarith
    have hinv1 : (1 + (tail56Q : ℝ) / (caLo23_14_lo : ℝ) ^ 4)⁻¹ ≤ |lam23 0 i₀| ^ 56 / sys.Z 56 (23 : ℝ) := by
      conv_rhs => rw [← inv_div]
      exact inv_anti₀ (div_pos hZ56_pos hdom56_pos) hrat_le
    have hS_ge : (1 + (tail56Q : ℝ) / (caLo23_14_lo : ℝ) ^ 4)⁻¹ ^ 2 ≤
        sys.Z 112 (23 : ℝ) / (sys.Z 56 (23 : ℝ)) ^ 2 := by
      have hsq : (|lam23 0 i₀| ^ 56 / sys.Z 56 (23 : ℝ)) ^ 2 ≤
          sys.Z 112 (23 : ℝ) / (sys.Z 56 (23 : ℝ)) ^ 2 := by
        rw [div_pow, ← pow_mul]
        exact div_le_div_of_nonneg_right hZ112_ge_dom (pow_nonneg hZ56_pos.le 2)
      exact (pow_le_pow_left₀ (by positivity) hinv1 2).trans hsq
    have hp_rat : (1 : ℝ) - (1 + (tail56Q : ℝ) / (caLo23_14_lo : ℝ) ^ 4)⁻¹ ^ 2 ≤ (caP0 : ℝ) := by
      have hp : ((1 - (1 + tail56Q / caLo23_14_lo ^ 4)⁻¹ ^ 2 : ℚ) : ℝ) ≤ (caP0 : ℝ) := by
        exact_mod_cast hinit.2.2.2.2.2.2.2.1
      push_cast at hp; exact hp
    have hSeq : sys.toPuritySystem1D.S 56 (23 : ℝ) = sys.Z 112 (23 : ℝ) / (sys.Z 56 (23 : ℝ)) ^ 2 := rfl
    rw [hSeq]; linarith
  exact ⟨⟨hS56, hT112⟩, ca_four_rounds_to_896_exact sys.toPuritySystem1D hS56 hT112⟩

/-- **Candidate A (`Δ = 1, D = 1/4`) Uniform Haldane Gap Theorem (`L ≥ 896`, `γ_L > log(20)/368`)**:
chains `candidate_a_seed896_from_raw_table` directly into `uniform_gap_from_purities` to prove
uniqueness of the ground state and the uniform spectral gap `γ_L > log(20) / 368 ≈ 0.00814`
for **every even ring length `L ≥ 896`**. -/
theorem candidate_a_uniform_gap_896 (sys : SpectralSystem1D)
    {ι155 ι23 : Fin 4 → Type*}
    (lam155 : ∀ s : Fin 4, ι155 s → ℝ)
    (lam23  : ∀ s : Fin 4, ι23 s → ℝ)
    (hsumm155 : ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam155 s i| ^ n))
    (hsumm23  : ∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam23 s i| ^ n))
    (hZ155_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (31 / 2 : ℝ) = (∑' i, lam155 0 i ^ n) + 2 * (∑' i, lam155 1 i ^ n) +
                              (∑' i, lam155 2 i ^ n) + 2 * (∑' i, lam155 3 i ^ n))
    (hZ23_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (23 : ℝ) = (∑' i, lam23 0 i ^ n) + 2 * (∑' i, lam23 1 i ^ n) +
                          (∑' i, lam23 2 i ^ n) + 2 * (∑' i, lam23 3 i ^ n))
    (hraw155_I : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) + 2 * (∑' i, lam155 1 i ^ n) + (∑' i, lam155 2 i ^ n) + 2 * (∑' i, lam155 3 i ^ n)) -
        ((caRawQuad caTable155 n).1 : ℝ)| ≤ (caEps : ℝ))
    (hraw155_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) + 2 * (∑' i, lam155 1 i ^ n) + (∑' i, lam155 2 i ^ n) - 2 * (∑' i, lam155 3 i ^ n)) -
        ((caRawQuad caTable155 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw155_X : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) - (∑' i, lam155 2 i ^ n)) -
        ((caRawQuad caTable155 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw155_F : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam155 0 i ^ n) - 2 * (∑' i, lam155 1 i ^ n) + (∑' i, lam155 2 i ^ n)) -
        ((caRawQuad caTable155 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_I : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) + 2 * (∑' i, lam23 1 i ^ n) + (∑' i, lam23 2 i ^ n) + 2 * (∑' i, lam23 3 i ^ n)) -
        ((caRawQuad caTable23 n).1 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) + 2 * (∑' i, lam23 1 i ^ n) + (∑' i, lam23 2 i ^ n) - 2 * (∑' i, lam23 3 i ^ n)) -
        ((caRawQuad caTable23 n).2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_X : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) - (∑' i, lam23 2 i ^ n)) -
        ((caRawQuad caTable23 n).2.2.1 : ℝ)| ≤ (caEps : ℝ))
    (hraw23_F : ∀ n : ℕ, 4 ≤ n → n ≤ 14 →
      |((∑' i, lam23 0 i ^ n) - 2 * (∑' i, lam23 1 i ^ n) + (∑' i, lam23 2 i ^ n)) -
        ((caRawQuad caTable23 n).2.2.2 : ℝ)| ≤ (caEps : ℝ))
    (htrial112 : ∃ k : Fin (sys.d 112), sys.E 112 k + sys.a * (112 : ℝ) ≤ 0)
    {L : ℕ} (hL_even : Even L) (hL_ge : 896 ≤ L) :
    ∃ k₀ : Fin (sys.d L),
      (∀ k : Fin (sys.d L), sys.E L k₀ ≤ sys.E L k) ∧
      (∀ k : Fin (sys.d L), k ≠ k₀ → Real.log 20 / 368 < sys.E L k - sys.E L k₀) := by
  have hseed := candidate_a_seed896_from_raw_table sys lam155 lam23 hsumm155 hsumm23
    hZ155_even hZ23_even hraw155_I hraw155_Z hraw155_X hraw155_F
    hraw23_I hraw23_Z hraw23_X hraw23_F htrial112
  have hp4 : (caP4 : ℝ) < (1 / 100 : ℝ) := by unfold caP4; norm_num
  have hq4 : (caQ4 : ℝ) < (1 / 100 : ℝ) := by unfold caQ4; norm_num
  have hS896 : 1 - sys.toPuritySystem1D.S 896 (368 : ℝ) ≤ (1 / 100 : ℝ) := by linarith [hseed.2.1]
  have hT1792 : 1 - sys.toPuritySystem1D.T 1792 (368 : ℝ) ≤ (1 / 100 : ℝ) := by linarith [hseed.2.2]
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
  refine ⟨k₀, fun k => hk₀_min k (Finset.mem_univ k), fun k hne => ?_⟩
  have h := hres.2 k hne
  rw [h20] at h; linarith

end PurityBootstrap.CandidateA
