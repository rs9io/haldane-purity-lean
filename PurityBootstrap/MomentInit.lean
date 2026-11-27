import PurityBootstrap.Basic
import PurityBootstrap.OneD
import PurityBootstrap.ExactCertificates
import Mathlib.Tactic

/-!
# Moment Initialization Machinery (`lem:cappedmass`, `lem:polynomial-filter`, `prop:seed2304`)

Formalizes the complete analytic moment-inference machinery shared by OpenAI's Haldane
initialization (`arXiv` Sep 24, 2026) and our axial `D₂`-sector Candidate A initialization:
1. **`capped_mass_finset` & `capped_mass_tsum`** (`lem:cappedmass`):
   for `0 ≤ t_i ≤ h` with `∑ t_i ≤ m` (`h > 0, m ≥ 0`) and `r ≥ 1`,
   `∑ t_i^r ≤ ⌊m / h⌋ * h^r + (m - ⌊m / h⌋ * h)^r`, plus the uncapped bound `∑ t_i^r ≤ m^r`.
2. **`polynomial_filter_tsum`** (`lem:polynomial-filter`):
   any nonnegative polynomial `F(x) = ∑ f_j x^j` whose centered moment upper bound `B`
   satisfies `B < F(x)` for all `|x| ≥ v` forces `|λ_i| < v` for every eigenvalue `λ_i`
   (without requiring summability of zero-coefficient terms such as `j = 0`).
3. **`filterPolyCoeffs_eval_eq` & `shiftedFilterCoeff_eval_eq`**:
   connects the computable `ExactCertificates.filterPolyCoeffs` and `shiftedFilterCoeff`
   Boolean checks directly to the real polynomials `x^4 * (∑ a_i x^i)^2` and `F(±(cap + y))`.
4. **`source1_gap_from_thermal_table`** (`prop:seed2304` closed!):
   derives `1 - S(36, 49/4) ≤ s1P0`, `1 - T(72, 49/4) ≤ s1Q0`, and hence
   `γ_L > log 20 / 784` for every even `L ≥ 2304` directly from the `b₀ = 49/4` thermal
   table (`lem:thermal-inputs`), `D₂`-sector decomposition (`Z_n = J_n + 3 N_n`, `Z_n(P) = J_n - N_n`),
   and trial energy bound `Z_72(b) > 1`.
-/

namespace PurityBootstrap.MomentInit

open scoped BigOperators
open PurityBootstrap PurityBootstrap.ExactCertificates

/-! ## Section 1: Capped-Mass Extremal Inequality (`lem:cappedmass`) -/

/-- Real capped-mass extremal bound `C(m, h, r) = ⌊m / h⌋ * h^r + (m - ⌊m / h⌋ * h)^r`. -/
noncomputable def cappedMassR (m h : ℝ) (r : ℕ) : ℝ :=
  (⌊m / h⌋ : ℝ) * h ^ r + (m - (⌊m / h⌋ : ℝ) * h) ^ r

lemma cappedMassQ_cast (m h : ℚ) (r : ℕ) :
    ((cappedMassQ m h r : ℚ) : ℝ) = cappedMassR (m : ℝ) (h : ℝ) r := by
  unfold cappedMassQ cappedMassR
  have hfl : (⌊m / h⌋ : ℤ) = ⌊(m : ℝ) / (h : ℝ)⌋ := by
    have hq : ((m / h : ℚ) : ℝ) = (m : ℝ) / (h : ℝ) := by push_cast; rfl
    rw [← hq, Rat.floor_cast]
  push_cast
  rw [hfl]

/-- Elementary convexity/telescoping step for `x ↦ x^r` (`r ≥ 1`): transferring mass `δ ≥ 0`
from a smaller `a` to a larger `b` (`0 ≤ a - δ`, `a ≤ b`) never decreases `a^r + b^r`. -/
private lemma pow_mass_transfer {a b δ : ℝ} (haδ : 0 ≤ a - δ) (hab : a ≤ b) (hδ : 0 ≤ δ) :
    ∀ r : ℕ, a ^ r + b ^ r ≤ (a - δ) ^ r + (b + δ) ^ r
  | 0 => by simp
  | r + 1 => by
    have hdiff : ∀ x y : ℝ, x ^ (r + 1) - y ^ (r + 1) =
        (x - y) * ∑ j ∈ Finset.range (r + 1), x ^ j * y ^ (r - j) := fun x y => by
      clear haδ hab hδ a b δ
      induction r with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, mul_add]
        have hstep : (x - y) * ∑ j ∈ Finset.range (k + 1), x ^ j * y ^ (k + 1 - j) =
            y * ((x - y) * ∑ j ∈ Finset.range (k + 1), x ^ j * y ^ (k - j)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]; ring
        rw [hstep, ← ih]; simp [pow_succ]; ring
    have hL := hdiff a (a - δ)
    have hR := hdiff (b + δ) b
    have hsum_le : ∑ j ∈ Finset.range (r + 1), a ^ j * (a - δ) ^ (r - j) ≤
        ∑ j ∈ Finset.range (r + 1), (b + δ) ^ j * b ^ (r - j) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 : a ^ j ≤ (b + δ) ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
      have h2 : (a - δ) ^ (r - j) ≤ b ^ (r - j) := pow_le_pow_left₀ haδ (by linarith) (r - j)
      exact mul_le_mul h1 h2 (pow_nonneg haδ _) (pow_nonneg (by linarith) _)
    have hmul : δ * ∑ j ∈ Finset.range (r + 1), a ^ j * (a - δ) ^ (r - j) ≤
        δ * ∑ j ∈ Finset.range (r + 1), (b + δ) ^ j * b ^ (r - j) :=
      mul_le_mul_of_nonneg_left hsum_le hδ
    have hsub1 : a - (a - δ) = δ := by ring
    have hsub2 : b + δ - b = δ := by ring
    rw [hsub1] at hL; rw [hsub2] at hR
    linarith

/-- Monotonicity of `cappedMassR m h r` in the total mass `m ≥ 0` (`h > 0`, `r ≥ 1`). -/
lemma cappedMassR_mono {m₁ m₂ h : ℝ} (hh : 0 < h) (hm1 : 0 ≤ m₁) (h12 : m₁ ≤ m₂)
    {r : ℕ} (hr : 1 ≤ r) :
    cappedMassR m₁ h r ≤ cappedMassR m₂ h r := by
  unfold cappedMassR
  set q₁ : ℤ := ⌊m₁ / h⌋
  set q₂ : ℤ := ⌊m₂ / h⌋
  have hq1_le_q2 : q₁ ≤ q₂ := Int.floor_mono (div_le_div_of_nonneg_right h12 hh.le)
  have hrem1_nn : 0 ≤ m₁ - (q₁ : ℝ) * h := by
    have := Int.floor_le (m₁ / h)
    have h1 := (le_div_iff₀ hh).mp this
    linarith
  have hrem1_lt : m₁ - (q₁ : ℝ) * h < h := by
    have := Int.lt_floor_add_one (m₁ / h)
    have h1 := (div_lt_iff₀ hh).mp this
    linarith
  have hrem2_nn : 0 ≤ m₂ - (q₂ : ℝ) * h := by
    have := Int.floor_le (m₂ / h)
    have h1 := (le_div_iff₀ hh).mp this
    linarith
  by_cases hqeq : q₁ = q₂
  · rw [hqeq] at hrem1_nn ⊢
    have hp : (m₁ - (q₂ : ℝ) * h) ^ r ≤ (m₂ - (q₂ : ℝ) * h) ^ r :=
      pow_le_pow_left₀ hrem1_nn (by linarith) r
    linarith
  · have hq_succ : (q₁ : ℝ) + 1 ≤ (q₂ : ℝ) := by
      have : q₁ + 1 ≤ q₂ := by omega
      exact_mod_cast this
    have h1 : (m₁ - (q₁ : ℝ) * h) ^ r ≤ h ^ r := pow_le_pow_left₀ hrem1_nn hrem1_lt.le r
    have h2 : 0 ≤ (m₂ - (q₂ : ℝ) * h) ^ r := pow_nonneg hrem2_nn r
    have h3 : ((q₁ : ℝ) + 1) * h ^ r ≤ (q₂ : ℝ) * h ^ r :=
      mul_le_mul_of_nonneg_right hq_succ (pow_nonneg hh.le r)
    linarith

/-- **Finite Capped-Mass Lemma (`lem:cappedmass`)**:
for any finite family `t : ι → ℝ` with `0 ≤ t i ≤ h` and `∑ i ∈ s, t i ≤ m` (`h > 0, m ≥ 0`),
and any `r ≥ 1`, `∑ i ∈ s, t i ^ r ≤ cappedMassR m h r`. -/
theorem capped_mass_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℝ)
    {m h : ℝ} (hh : 0 < h) (hm : 0 ≤ m)
    (ht0 : ∀ i ∈ s, 0 ≤ t i) (hth : ∀ i ∈ s, t i ≤ h)
    (hsum : ∑ i ∈ s, t i ≤ m) {r : ℕ} (hr : 1 ≤ r) :
    ∑ i ∈ s, t i ^ r ≤ cappedMassR m h r := by
  -- Prove by strong induction on the number of strict interior points `{i ∈ s | 0 < t i ∧ t i < h}`
  have hmain : ∀ k : ℕ, ∀ f : ι → ℝ,
      (s.filter (fun i => 0 < f i ∧ f i < h)).card ≤ k →
      (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ h) →
      ∑ i ∈ s, f i ≤ m →
      ∑ i ∈ s, f i ^ r ≤ cappedMassR m h r := by
    intro k
    induction k with
    | zero =>
      intro f hcard hf0 hfh hfs
      -- Every `i ∈ s` has `f i = 0` or `f i = h`
      let sH := s.filter (fun i => f i = h)
      have hcard0 : s.filter (fun i => 0 < f i ∧ f i < h) = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hdich : ∀ i ∈ s, f i = 0 ∨ f i = h := fun i hi => by
        by_contra hneither; push Not at hneither
        have hpos : 0 < f i := lt_of_le_of_ne (hf0 i hi) (Ne.symm hneither.1)
        have hlt : f i < h := lt_of_le_of_ne (hfh i hi) hneither.2
        have hmem : i ∈ s.filter (fun i => 0 < f i ∧ f i < h) :=
          Finset.mem_filter.mpr ⟨hi, hpos, hlt⟩
        rw [hcard0] at hmem; exact Finset.notMem_empty i hmem
      have hsum_eq : ∑ i ∈ s, f i = (sH.card : ℝ) * h := by
        rw [← Finset.sum_filter_add_sum_filter_not s (fun i => f i = h)]
        have h1 : ∑ i ∈ sH, f i = (sH.card : ℝ) * h := by
          calc ∑ i ∈ sH, f i = ∑ _i ∈ sH, h := Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
            _ = (sH.card : ℝ) * h := by simp
        have h2 : ∑ i ∈ s.filter (fun i => ¬ f i = h), f i = 0 :=
          Finset.sum_eq_zero fun i hi => by
            rcases Finset.mem_filter.mp hi with ⟨his, hne⟩
            exact (hdich i his).resolve_right hne
        rw [h1, h2, add_zero]
      have hpow_eq : ∑ i ∈ s, f i ^ r = (sH.card : ℝ) * h ^ r := by
        rw [← Finset.sum_filter_add_sum_filter_not s (fun i => f i = h)]
        have h1 : ∑ i ∈ sH, f i ^ r = (sH.card : ℝ) * h ^ r := by
          calc ∑ i ∈ sH, f i ^ r = ∑ _i ∈ sH, h ^ r :=
                Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
            _ = (sH.card : ℝ) * h ^ r := by simp
        have h2 : ∑ i ∈ s.filter (fun i => ¬ f i = h), f i ^ r = 0 :=
          Finset.sum_eq_zero fun i hi => by
            rcases Finset.mem_filter.mp hi with ⟨his, hne⟩
            rw [(hdich i his).resolve_right hne, zero_pow (by omega)]
        rw [h1, h2, add_zero]
      have hq_ge : (sH.card : ℝ) ≤ (⌊m / h⌋ : ℝ) := by
        have hle : ((sH.card : ℤ) : ℝ) ≤ m / h := by
          rw [le_div_iff₀ hh]; push_cast; linarith
        exact_mod_cast Int.le_floor.mpr hle
      have hrem_nn : 0 ≤ m - (⌊m / h⌋ : ℝ) * h := by
        have := (le_div_iff₀ hh).mp (Int.floor_le (m / h)); linarith
      unfold cappedMassR
      rw [hpow_eq]
      have hmul : (sH.card : ℝ) * h ^ r ≤ (⌊m / h⌋ : ℝ) * h ^ r :=
        mul_le_mul_of_nonneg_right hq_ge (pow_nonneg hh.le r)
      linarith [pow_nonneg hrem_nn r]
    | succ k ih =>
      intro f hcard hf0 hfh hfs
      let sI := s.filter (fun i => 0 < f i ∧ f i < h)
      by_cases hle1 : sI.card ≤ 1
      · by_cases hc0 : sI.card = 0
        · dsimp [sI] at hc0
          exact ih f (by omega) hf0 hfh hfs
        · -- Exactly 1 interior point `a`
          have hc1 : sI.card = 1 := by omega
          rcases Finset.card_eq_one.mp hc1 with ⟨a, ha_eq⟩
          have ha_mem : a ∈ sI := ha_eq ▸ Finset.mem_singleton_self a
          have ha_s : a ∈ s := (Finset.mem_filter.mp ha_mem).1
          have ha_pos : 0 < f a := (Finset.mem_filter.mp ha_mem).2.1
          have ha_lt : f a < h := (Finset.mem_filter.mp ha_mem).2.2
          let sH := s.filter (fun i => f i = h)
          have ha_notH : a ∉ sH := fun hm' => ne_of_lt ha_lt (Finset.mem_filter.mp hm').2
          have hrest_dich : ∀ i ∈ s, i ≠ a → f i = 0 ∨ f i = h := fun i hi hne => by
            by_contra hneither; push Not at hneither
            have hmem : i ∈ sI := Finset.mem_filter.mpr
              ⟨hi, lt_of_le_of_ne (hf0 i hi) (Ne.symm hneither.1), lt_of_le_of_ne (hfh i hi) hneither.2⟩
            rw [ha_eq, Finset.mem_singleton] at hmem
            exact hne hmem
          have hsum_eq : ∑ i ∈ s, f i = (sH.card : ℝ) * h + f a := by
            rw [← Finset.add_sum_erase s f ha_s, add_comm]
            congr 1
            rw [← Finset.sum_filter_add_sum_filter_not (s.erase a) (fun i => f i = h)]
            have hfilt_eq : (s.erase a).filter (fun i => f i = h) = sH := by
              ext i; simp only [sH, Finset.mem_filter, Finset.mem_erase]
              exact ⟨fun ⟨⟨_, his⟩, hfi⟩ => ⟨his, hfi⟩,
                fun ⟨his, hfi⟩ => ⟨⟨fun hia => ha_notH (hia ▸ Finset.mem_filter.mpr ⟨his, hfi⟩), his⟩, hfi⟩⟩
            have h1 : ∑ i ∈ (s.erase a).filter (fun i => f i = h), f i = (sH.card : ℝ) * h := by
              rw [hfilt_eq]
              calc ∑ i ∈ sH, f i = ∑ _i ∈ sH, h := Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
                _ = (sH.card : ℝ) * h := by simp
            have h2 : ∑ i ∈ (s.erase a).filter (fun i => ¬ f i = h), f i = 0 :=
              Finset.sum_eq_zero fun i hi => by
                rcases Finset.mem_filter.mp hi with ⟨hie, hne⟩
                rcases Finset.mem_erase.mp hie with ⟨hia, his⟩
                exact (hrest_dich i his hia).resolve_right hne
            rw [h1, h2, add_zero]
          have hpow_eq : ∑ i ∈ s, f i ^ r = (sH.card : ℝ) * h ^ r + f a ^ r := by
            rw [← Finset.add_sum_erase s (fun i => f i ^ r) ha_s, add_comm]
            congr 1
            rw [← Finset.sum_filter_add_sum_filter_not (s.erase a) (fun i => f i = h)]
            have hfilt_eq : (s.erase a).filter (fun i => f i = h) = sH := by
              ext i; simp only [sH, Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨⟨_, his⟩, hfi⟩; exact ⟨his, hfi⟩
              · rintro ⟨his, hfi⟩
                refine ⟨⟨?_, his⟩, hfi⟩
                rintro rfl; exact ha_notH (Finset.mem_filter.mpr ⟨his, hfi⟩)
            have h1 : ∑ i ∈ (s.erase a).filter (fun i => f i = h), f i ^ r = (sH.card : ℝ) * h ^ r := by
              rw [hfilt_eq]
              calc ∑ i ∈ sH, f i ^ r = ∑ _i ∈ sH, h ^ r :=
                    Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
                _ = (sH.card : ℝ) * h ^ r := by simp
            have h2 : ∑ i ∈ (s.erase a).filter (fun i => ¬ f i = h), f i ^ r = 0 :=
              Finset.sum_eq_zero fun i hi => by
                rcases Finset.mem_filter.mp hi with ⟨hie, hne⟩
                rcases Finset.mem_erase.mp hie with ⟨hia, his⟩
                rw [(hrest_dich i his hia).resolve_right hne, zero_pow (by omega)]
            rw [h1, h2, add_zero]
          -- Evaluate `cappedMassR (∑ f) h r` and use `cappedMassR_mono`!
          have hfl : ⌊((sH.card : ℝ) * h + f a) / h⌋ = (sH.card : ℤ) := by
            rw [Int.floor_eq_iff]
            constructor
            · rw [le_div_iff₀ hh]; push_cast; linarith
            · rw [div_lt_iff₀ hh]; push_cast; linarith
          have heq_cm : ∑ i ∈ s, f i ^ r = cappedMassR (∑ i ∈ s, f i) h r := by
            rw [hpow_eq, hsum_eq]; unfold cappedMassR; rw [hfl]; push_cast; ring
          rw [heq_cm]
          exact cappedMassR_mono hh (Finset.sum_nonneg fun i hi => hf0 i hi) hfs hr
      · -- At least 2 interior points `a ≠ b`: transfer mass from smaller to larger!
        have hge2 : 1 < sI.card := by omega
        rcases Finset.one_lt_card.mp hge2 with ⟨u, hu, v, hv, huv⟩
        -- Order `(a, b)` so `f a ≤ f b`
        let a := if f u ≤ f v then u else v
        let b := if f u ≤ f v then v else u
        have hab_ne : a ≠ b := by dsimp [a, b]; split_ifs <;> [exact huv; exact huv.symm]
        have ha_mem : a ∈ sI := by dsimp [a]; split_ifs <;> assumption
        have hb_mem : b ∈ sI := by dsimp [b]; split_ifs <;> assumption
        have hab_le : f a ≤ f b := by
          dsimp [a, b]; split_ifs with hle; · exact hle
          · linarith
        have ha_s : a ∈ s := (Finset.mem_filter.mp ha_mem).1
        have hb_s : b ∈ s := (Finset.mem_filter.mp hb_mem).1
        have ha_pos : 0 < f a := (Finset.mem_filter.mp ha_mem).2.1
        have ha_lt : f a < h := (Finset.mem_filter.mp ha_mem).2.2
        have hb_pos : 0 < f b := (Finset.mem_filter.mp hb_mem).2.1
        have hb_lt : f b < h := (Finset.mem_filter.mp hb_mem).2.2
        let δ : ℝ := min (f a) (h - f b)
        have hδ_pos : 0 < δ := lt_min ha_pos (by linarith)
        let f' : ι → ℝ := Function.update (Function.update f a (f a - δ)) b (f b + δ)
        have hf'a : f' a = f a - δ := by dsimp [f']; rw [Function.update_of_ne hab_ne, Function.update_self]
        have hf'b : f' b = f b + δ := by dsimp [f']; rw [Function.update_self]
        have hf'o : ∀ i, i ≠ a → i ≠ b → f' i = f i := fun i hia hib => by
          dsimp [f']; rw [Function.update_of_ne hib, Function.update_of_ne hia]
        have hf'0 : ∀ i ∈ s, 0 ≤ f' i := fun i hi => by
          by_cases hia : i = a
          · subst hia; rw [hf'a]; have : δ ≤ f a := min_le_left _ _; linarith
          · by_cases hib : i = b
            · subst hib; rw [hf'b]; linarith
            · rw [hf'o i hia hib]; exact hf0 i hi
        have hf'h : ∀ i ∈ s, f' i ≤ h := fun i hi => by
          by_cases hia : i = a
          · subst hia; rw [hf'a]; linarith
          · by_cases hib : i = b
            · subst hib; rw [hf'b]; have : δ ≤ h - f b := min_le_right _ _; linarith
            · rw [hf'o i hia hib]; exact hfh i hi
        have hsum_eq : ∑ i ∈ s, f' i = ∑ i ∈ s, f i := by
          have hb_er : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab_ne.symm, hb_s⟩
          rw [← Finset.add_sum_erase s f' ha_s, ← Finset.add_sum_erase (s.erase a) f' hb_er]
          rw [← Finset.add_sum_erase s f ha_s, ← Finset.add_sum_erase (s.erase a) f hb_er]
          have hrest : ∑ i ∈ (s.erase a).erase b, f' i = ∑ i ∈ (s.erase a).erase b, f i :=
            Finset.sum_congr rfl fun i hi => hf'o i
              (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1
          rw [hrest, hf'a, hf'b]; ring
        have hpow_le : ∑ i ∈ s, f i ^ r ≤ ∑ i ∈ s, f' i ^ r := by
          have hb_er : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab_ne.symm, hb_s⟩
          rw [← Finset.add_sum_erase s (fun i => f' i ^ r) ha_s,
            ← Finset.add_sum_erase (s.erase a) (fun i => f' i ^ r) hb_er]
          rw [← Finset.add_sum_erase s (fun i => f i ^ r) ha_s,
            ← Finset.add_sum_erase (s.erase a) (fun i => f i ^ r) hb_er]
          have hrest : ∑ i ∈ (s.erase a).erase b, f' i ^ r = ∑ i ∈ (s.erase a).erase b, f i ^ r :=
            Finset.sum_congr rfl fun i hi => by
              rw [hf'o i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1]
          rw [hrest, hf'a, hf'b]
          have htr := pow_mass_transfer (show 0 ≤ f a - δ by have := min_le_left (f a) (h - f b); linarith)
            hab_le hδ_pos.le r
          linarith
        -- Strict subset of interior points!
        have hsub : s.filter (fun i => 0 < f' i ∧ f' i < h) ⊂ sI := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases Finset.mem_filter.mp hi with ⟨his, hpos, hlt⟩
            by_cases hia : i = a
            · subst hia; exact ha_mem
            · by_cases hib : i = b
              · subst hib; exact hb_mem
              · rw [hf'o i hia hib] at hpos hlt
                exact Finset.mem_filter.mpr ⟨his, hpos, hlt⟩
          · intro heq
            by_cases hmin : f a ≤ h - f b
            · have hδ_eq : δ = f a := min_eq_left hmin
              have ha_in : a ∈ s.filter (fun i => 0 < f' i ∧ f' i < h) := heq ▸ ha_mem
              have := (Finset.mem_filter.mp ha_in).2.1
              rw [hf'a, hδ_eq, sub_self] at this; exact lt_irrefl 0 this
            · have hδ_eq : δ = h - f b := min_eq_right (le_of_not_ge hmin)
              have hb_in : b ∈ s.filter (fun i => 0 < f' i ∧ f' i < h) := heq ▸ hb_mem
              have := (Finset.mem_filter.mp hb_in).2.2
              rw [hf'b, hδ_eq] at this; linarith
        have hcard' : (s.filter (fun i => 0 < f' i ∧ f' i < h)).card ≤ k := by
          have := Finset.card_lt_card hsub; dsimp [sI] at this; omega
        exact hpow_le.trans (ih f' hcard' hf'0 hf'h (hsum_eq ▸ hfs))
  exact hmain _ t le_rfl ht0 hth hsum

/-- **Countable Capped-Mass Lemma (`lem:cappedmass`)**:
extends `capped_mass_finset` to any summable family `t : ι → ℝ` with `0 ≤ t i ≤ h` and `∑' i, t i ≤ m`. -/
theorem capped_mass_tsum {ι : Type*} (t : ι → ℝ)
    {m h : ℝ} (hh : 0 < h) (hm : 0 ≤ m)
    (ht0 : ∀ i, 0 ≤ t i) (hth : ∀ i, t i ≤ h)
    (hsumm : Summable t) (hsum : ∑' i, t i ≤ m) {r : ℕ} (hr : 1 ≤ r) :
    Summable (fun i => t i ^ r) ∧ ∑' i, t i ^ r ≤ cappedMassR m h r := by
  classical
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, t i ^ r ≤ cappedMassR m h r := fun s =>
    capped_mass_finset s t hh hm (fun i _ => ht0 i) (fun i _ => hth i)
      ((hsumm.sum_le_tsum s (fun i _ => ht0 i)).trans hsum) hr
  have hs_r : Summable (fun i => t i ^ r) :=
    summable_of_sum_le (fun i => pow_nonneg (ht0 i) r) hfin
  exact ⟨hs_r, hs_r.tsum_le_of_sum_le hfin⟩

/-- **Uncapped-Mass Lemma (`lem:cappedmass`, second part)**:
for any summable nonnegative family `t : ι → ℝ` with `∑' i, t i ≤ m` and `r ≥ 1`,
`∑' i, t i ^ r ≤ m ^ r`. -/
theorem uncapped_mass_tsum {ι : Type*} (t : ι → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (ht0 : ∀ i, 0 ≤ t i) (hsumm : Summable t) (hsum : ∑' i, t i ≤ m) {r : ℕ} (hr : 1 ≤ r) :
    Summable (fun i => t i ^ r) ∧ ∑' i, t i ^ r ≤ m ^ r := by
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, t i ^ r ≤ m ^ r := fun s => by
    have hts : ∑ i ∈ s, t i ≤ m := (hsumm.sum_le_tsum s (fun i _ => ht0 i)).trans hsum
    have h1 : ∑ i ∈ s, t i ^ r ≤ (∑ i ∈ s, t i) ^ r := by
      have hterm : ∀ i ∈ s, t i ^ r ≤ t i * (∑ j ∈ s, t j) ^ (r - 1) := fun i hi => by
        have hle : t i ≤ ∑ j ∈ s, t j := Finset.single_le_sum (fun j _ => ht0 j) hi
        have hpow : t i ^ (r - 1) ≤ (∑ j ∈ s, t j) ^ (r - 1) :=
          pow_le_pow_left₀ (ht0 i) hle (r - 1)
        calc t i ^ r = t i * t i ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr]
          _ ≤ t i * (∑ j ∈ s, t j) ^ (r - 1) := mul_le_mul_of_nonneg_left hpow (ht0 i)
      calc ∑ i ∈ s, t i ^ r ≤ ∑ i ∈ s, t i * (∑ j ∈ s, t j) ^ (r - 1) := Finset.sum_le_sum hterm
        _ = (∑ i ∈ s, t i) * (∑ j ∈ s, t j) ^ (r - 1) := (Finset.sum_mul _ _ _).symm
        _ = (∑ i ∈ s, t i) ^ r := by rw [← pow_succ', Nat.sub_add_cancel hr]
    exact h1.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => ht0 i) hts r)
  have hs_r : Summable (fun i => t i ^ r) :=
    summable_of_sum_le (fun i => pow_nonneg (ht0 i) r) hfin
  exact ⟨hs_r, hs_r.tsum_le_of_sum_le hfin⟩

/-! ## Section 2: Polynomial Filter Lemma (`lem:polynomial-filter`) -/

/-- **Polynomial Filter Lemma (`lem:polynomial-filter`)**:
if `F(x) = ∑_{j=0}^D f_j x^j ≥ 0` on `ℝ`, every nonzero-coefficient moment `j` converges
absolutely with `|∑'_i λ_i^j - c_j| ≤ ε`, and `F(x) > ∑ f_j c_j + ε ∑ |f_j|` whenever `|x| ≥ v`,
then `|λ_i| < v` for every `i`. Note: does NOT require summability when `f_j = 0`! -/
theorem polynomial_filter_tsum {ι : Type*} (lam : ι → ℝ) {D : ℕ}
    (f c : Fin (D + 1) → ℝ) {ε v : ℝ} (hε : 0 ≤ ε)
    (hmom : ∀ j : Fin (D + 1), f j ≠ 0 →
      Summable (fun i => |lam i| ^ j.val) ∧ |∑' i, lam i ^ j.val - c j| ≤ ε)
    (hF_nn : ∀ x : ℝ, 0 ≤ ∑ j : Fin (D + 1), f j * x ^ j.val)
    (hF_gt : ∀ x : ℝ, v ≤ |x| →
      (∑ j : Fin (D + 1), f j * c j) + ε * (∑ j : Fin (D + 1), |f j|) <
        ∑ j : Fin (D + 1), f j * x ^ j.val) :
    ∀ i : ι, |lam i| < v := by
  -- For each `j`, `i ↦ f j * lam i ^ j` is summable (trivially if `f j = 0`, by abs conv otherwise)
  have hterm_summ : ∀ j : Fin (D + 1), Summable (fun i => f j * lam i ^ j.val) := fun j => by
    by_cases hfj : f j = 0
    · simp [hfj, summable_zero]
    · have habs : Summable (fun i => |lam i ^ j.val|) := by
        simpa [abs_pow] using (hmom j hfj).1
      exact (Summable.of_abs habs).mul_left (f j)
  have hF_summ : Summable (fun i => ∑ j : Fin (D + 1), f j * lam i ^ j.val) :=
    summable_sum fun j _ => hterm_summ j
  have htsum_eq : ∑' i, (∑ j : Fin (D + 1), f j * lam i ^ j.val) =
      ∑ j : Fin (D + 1), f j * (∑' i, lam i ^ j.val) := by
    rw [Summable.tsum_finsetSum fun j _ => hterm_summ j]
    refine Finset.sum_congr rfl fun j _ => tsum_mul_left
  have htsum_le : ∑' i, (∑ j : Fin (D + 1), f j * lam i ^ j.val) ≤
      (∑ j : Fin (D + 1), f j * c j) + ε * (∑ j : Fin (D + 1), |f j|) := by
    rw [htsum_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hfj : f j = 0
    · simp [hfj]
    · have herr := (hmom j hfj).2
      have h1 : f j * (∑' i, lam i ^ j.val - c j) ≤ |f j| * ε := by
        calc f j * (∑' i, lam i ^ j.val - c j)
            ≤ |f j * (∑' i, lam i ^ j.val - c j)| := le_abs_self _
          _ = |f j| * |∑' i, lam i ^ j.val - c j| := abs_mul _ _
          _ ≤ |f j| * ε := mul_le_mul_of_nonneg_left herr (abs_nonneg _)
      linarith
  intro i
  by_contra hge
  push Not at hge
  have hsingle : (∑ j : Fin (D + 1), f j * lam i ^ j.val) ≤
      ∑' k, (∑ j : Fin (D + 1), f j * lam k ^ j.val) :=
    hF_summ.le_tsum i (fun k _ => hF_nn (lam k))
  have hgt := hF_gt (lam i) hge
  linarith

/-! ## Section 3: Exact Polynomial Bridge for `filterPolyCoeffs` & `shiftedFilterCoeff` -/

/-- `filterPolyCoeffs a` represents the nonnegative real polynomial `x^4 * (∑ a_i x^i)^2`! -/
lemma filterPolyCoeffs_eval_eq (a : List ℤ) (ha : a.length ≤ 5) (x : ℝ) :
    ∑ d : Fin 13, ((filterPolyCoeffs a).getD d.val 0 : ℝ) * x ^ d.val =
      x ^ 4 * (∑ i ∈ Finset.range a.length, (a.getD i 0 : ℝ) * x ^ i) ^ 2 := by
  have hget : ∀ d : Fin 13, ((filterPolyCoeffs a).getD d.val 0 : ℝ) =
      ∑ i ∈ Finset.range a.length, ∑ j ∈ Finset.range a.length,
        if i + j + 4 = d.val then (a.getD i 0 : ℝ) * (a.getD j 0 : ℝ) else 0 := by
    intro d
    unfold filterPolyCoeffs
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range d.isLt,
      Option.map_some, Option.getD_some]
    -- Convert nested `List.foldl` over `List.range a.length` into nested `Finset.sum`
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
        (List.range a.length).foldl
          (fun acc2 j => if i + j + 4 = d.val then acc2 + a.getD i 0 * a.getD j 0 else acc2) init =
        init + ∑ j ∈ Finset.range a.length,
          if i + j + 4 = d.val then a.getD i 0 * a.getD j 0 else 0 := fun i init => by
      have heq : (fun acc2 j => if i + j + 4 = d.val then acc2 + a.getD i 0 * a.getD j 0 else acc2) =
          (fun acc2 j => acc2 + if i + j + 4 = d.val then a.getD i 0 * a.getD j 0 else 0) := by
        funext acc2 j; split_ifs <;> ring
      rw [heq, hfold]
    have houter : (List.range a.length).foldl (fun acc i =>
        (List.range a.length).foldl
          (fun acc2 j => if i + j + 4 = d.val then acc2 + a.getD i 0 * a.getD j 0 else acc2) acc) 0 =
        ∑ i ∈ Finset.range a.length, ∑ j ∈ Finset.range a.length,
          if i + j + 4 = d.val then a.getD i 0 * a.getD j 0 else 0 := by
      have heq : (fun acc i => (List.range a.length).foldl
          (fun acc2 j => if i + j + 4 = d.val then acc2 + a.getD i 0 * a.getD j 0 else acc2) acc) =
          (fun acc i => acc + ∑ j ∈ Finset.range a.length,
            if i + j + 4 = d.val then a.getD i 0 * a.getD j 0 else 0) := by
        funext acc i; exact hinner i acc
      rw [heq, hfold, zero_add]
    rw [houter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  simp_rw [hget, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hswap2 : ∑ i ∈ Finset.range a.length, ∑ d : Fin 13,
      (∑ j ∈ Finset.range a.length,
        (if i + j + 4 = d.val then (a.getD i 0 : ℝ) * (a.getD j 0 : ℝ) else 0) * x ^ d.val) =
      ∑ i ∈ Finset.range a.length, ∑ j ∈ Finset.range a.length,
        (a.getD i 0 : ℝ) * (a.getD j 0 : ℝ) * x ^ (i + j + 4) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hi' : i < a.length := Finset.mem_range.mp hi
    have hj' : j < a.length := Finset.mem_range.mp hj
    have hd_lt : i + j + 4 < 13 := by omega
    rw [Finset.sum_eq_single ⟨i + j + 4, hd_lt⟩]
    · simp
    · intro d _ hne
      have : i + j + 4 ≠ d.val := fun heq => hne (Fin.ext heq.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hswap2, sq, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_add]; ring

/-- Taylor-shift identity: `shiftedFilterCoeff` gives the exact `y`-expansion of `F(sign * (cap + y))`! -/
lemma shiftedFilterCoeff_eval_eq (coeffs : List ℤ) (sign : ℤ) (cap : ℚ) (y : ℝ) :
    ∑ d : Fin 13, (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) * ((cap : ℝ) + y)) ^ d.val =
      ∑ j : Fin 13, (shiftedFilterCoeff coeffs sign cap j.val : ℝ) * y ^ j.val := by
  have hshift_cast : ∀ j : Fin 13, (shiftedFilterCoeff coeffs sign cap j.val : ℝ) =
      ∑ d : Fin 13, if j.val ≤ d.val then
        (Nat.choose d.val j.val : ℝ) * (coeffs.getD d.val 0 : ℝ) *
        ((sign : ℝ) ^ d.val) * ((cap : ℝ) ^ (d.val - j.val))
      else 0 := fun j => by
    unfold shiftedFilterCoeff
    have hlist : ∀ (n : ℕ) (g : ℕ → ℚ),
        (((List.range n).map g).sum : ℝ) = ∑ d ∈ Finset.range n, (g d : ℝ) := fun n g => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          Rat.cast_add, ih, Finset.sum_range_succ]
    rw [hlist, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> push_cast <;> rfl
  simp_rw [hshift_cast, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_pow, add_comm (cap : ℝ) y, add_pow]
  rw [Finset.mul_sum, Finset.mul_sum]
  have hrange : ∑ j : Fin 13,
      (if j.val ≤ d.val then
        (Nat.choose d.val j.val : ℝ) * (coeffs.getD d.val 0 : ℝ) *
        ((sign : ℝ) ^ d.val) * ((cap : ℝ) ^ (d.val - j.val))
      else 0) * y ^ j.val =
      ∑ j ∈ Finset.range (d.val + 1),
        (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) ^ d.val *
          (y ^ j * (cap : ℝ) ^ (d.val - j) * (Nat.choose d.val j : ℝ))) := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      (if j ≤ d.val then
        (Nat.choose d.val j : ℝ) * (coeffs.getD d.val 0 : ℝ) *
        ((sign : ℝ) ^ d.val) * ((cap : ℝ) ^ (d.val - j))
      else 0) * y ^ j)]
    have hsub : Finset.range (d.val + 1) ⊆ Finset.range 13 :=
      Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjle : j ≤ d.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [if_pos hjle]; ring
    · intro j _ hnot
      have hjgt : ¬ (j ≤ d.val) := by
        intro hle; exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [hjgt]
  exact hrange.symm

/-- Ray exclusion from the verified `shiftedFilterCoeff` Boolean check! -/
lemma filter_ray_gt_of_check (coeffs : List ℤ) (cap B : ℚ)
    (hpos : B < shiftedFilterCoeff coeffs 1 cap 0 ∧
      (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff coeffs 1 cap (j + 1))) = true)
    (hneg : B < shiftedFilterCoeff coeffs (-1) cap 0 ∧
      (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff coeffs (-1) cap (j + 1))) = true)
    {x : ℝ} (hx : (cap : ℝ) ≤ |x|) :
    (B : ℝ) < ∑ d : Fin 13, (coeffs.getD d.val 0 : ℝ) * x ^ d.val := by
  have hside : ∀ (sign : ℤ) (y : ℝ), 0 ≤ y →
      B < shiftedFilterCoeff coeffs sign cap 0 →
      (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff coeffs sign cap (j + 1))) = true →
      (B : ℝ) < ∑ d : Fin 13, (coeffs.getD d.val 0 : ℝ) * ((sign : ℝ) * ((cap : ℝ) + y)) ^ d.val := by
    intro sign y hy h0 hall
    rw [shiftedFilterCoeff_eval_eq, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    have h0R : (B : ℝ) < (shiftedFilterCoeff coeffs sign cap 0 : ℝ) * y ^ 0 := by
      simp only [pow_zero, mul_one]; exact_mod_cast h0
    have htail_nn : 0 ≤ ∑ j : Fin 12, (shiftedFilterCoeff coeffs sign cap (j.val + 1) : ℝ) * y ^ (j.val + 1) := by
      refine Finset.sum_nonneg fun j _ => ?_
      have hj_mem : j.val ∈ List.range 12 := List.mem_range.mpr j.isLt
      have hj_ok : (0 : ℚ) ≤ shiftedFilterCoeff coeffs sign cap (j.val + 1) := by
        have := List.all_eq_true.mp hall j.val hj_mem
        exact of_decide_eq_true this
      exact mul_nonneg (by exact_mod_cast hj_ok) (pow_nonneg hy _)
    linarith
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx
    have heq : x = ((1 : ℤ) : ℝ) * ((cap : ℝ) + (x - (cap : ℝ))) := by push_cast; ring
    rw [heq]
    exact hside 1 (x - (cap : ℝ)) (by linarith) hpos.1 hpos.2
  · rw [abs_of_neg hx0] at hx
    have heq : x = ((-1 : ℤ) : ℝ) * ((cap : ℝ) + (-x - (cap : ℝ))) := by push_cast; ring
    rw [heq]
    exact hside (-1) (-x - (cap : ℝ)) (by linarith) hneg.1 hneg.2

/-! ## Section 4: Closing OpenAI Source 1 Initialization (`prop:seed2304`) -/

private lemma inv_sq_ge_of_bounds {z u z2 : ℝ} (hz : 0 < z) (hzu : z ≤ u) (hz2 : 1 ≤ z2) :
    u⁻¹ ^ 2 ≤ z2 / z ^ 2 := by
  have h1 : z⁻¹ ^ 2 ≤ z2 / z ^ 2 := by
    rw [inv_pow, ← one_div]
    exact div_le_div_of_nonneg_right hz2 (pow_nonneg hz.le 2)
  have h2 : u⁻¹ ≤ z⁻¹ := inv_anti₀ hz hzu
  have hnn : 0 ≤ u⁻¹ := inv_nonneg.mpr (le_trans hz.le hzu)
  exact (pow_le_pow_left₀ hnn h2 2).trans h1

/-- **Source 1 Conditional Initialization (Projected-Moment Interface)**:
given an abstract `SpectralSystem1D` together with `D₂`-sector spatial eigenvalue families
`(lamJ, lamN)` at `b₀ = 49/4` satisfying the projected moment bounds
`|J_n - s1Moment 3 n| ≤ 30/10^6`, `|N_n - s1Moment (-1) n| ≤ 30/10^6` (`n = 4..12`),
`Z_n(49/4) = J_n + 3 N_n` (even `n ≥ 4`), and the single non-strict trial bound
`1 ≤ Z_72(49/2)`, derives BOTH:
- the initial `(36, 49/4)` defects `1 - S(36, 49/4) ≤ s1P0` and `1 - T(72, 49/4) ≤ s1Q0`, and
- the stronger exact `prop:seed2304` defects `1 - S(2304, 784) ≤ s1P6 = 84513/10^7` and
  `1 - T(4608, 784) ≤ s1Q6 = 27493/5000000`. -/
theorem source1_seed2304_from_projected_moments (sys : SpectralSystem1D)
    {ιJ ιN : Type*} (lamJ : ιJ → ℝ) (lamN : ιN → ℝ)
    (hsummJ : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamJ i| ^ n))
    (hsummN : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamN i| ^ n))
    (hZ_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (49 / 4 : ℝ) = (∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n))
    (htable_J : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |(∑' i, lamJ i ^ n) - (s1Moment 3 n : ℝ)| ≤ (s1Eps : ℝ))
    (htable_N : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |(∑' i, lamN i ^ n) - (s1Moment (-1) n : ℝ)| ≤ (s1Eps : ℝ))
    (hZ72_2b_ge1 : 1 ≤ sys.Z 72 (49 / 2 : ℝ)) :
    (1 - sys.toPuritySystem1D.S 36 (49 / 4 : ℝ) ≤ (s1P0 : ℝ) ∧
     1 - sys.toPuritySystem1D.T 72 (49 / 4 : ℝ) ≤ (s1Q0 : ℝ)) ∧
    (1 - sys.toPuritySystem1D.S 2304 (784 : ℝ) ≤ (s1P6 : ℝ) ∧
     1 - sys.toPuritySystem1D.T 4608 (784 : ℝ) ≤ (s1Q6 : ℝ)) := by
  -- Derive `1 ≤ sys.Z 72 (49/4)` automatically from `1 ≤ sys.Z 72 (49/2)` and `T(72, 49/4) ≤ 1`!
  have hZ72_ge1 : 1 ≤ sys.Z 72 (49 / 4 : ℝ) := by
    have hZpos : 0 < sys.Z 72 (49 / 4 : ℝ) := sys.Z_pos ⟨36, by omega⟩ (by omega) (by norm_num)
    have hTle : sys.toPuritySystem1D.T 72 (49 / 4 : ℝ) ≤ 1 :=
      sys.toPuritySystem1D.T_le_one 72 (49 / 4 : ℝ) ⟨36, by omega⟩ (by omega) (by norm_num)
    have hTeq : sys.toPuritySystem1D.T 72 (49 / 4 : ℝ) =
        sys.Z 72 (49 / 2 : ℝ) / (sys.Z 72 (49 / 4 : ℝ)) ^ 2 := by
      unfold PuritySystem1D.T
      have h2b : 2 * (49 / 4 : ℝ) = 49 / 2 := by norm_num
      rw [h2b]; rfl
    rw [hTeq, div_le_one (pow_pos hZpos 2)] at hTle
    have hsq_ge1 : (1 : ℝ) ≤ (sys.Z 72 (49 / 4 : ℝ)) ^ 2 := le_trans hZ72_2b_ge1 hTle
    nlinarith
  have hinit := s1_dominant_existence_and_initial_bounds
  -- Helper: connect `s1FilterUpper` to `∑ f_j c_j + ε ∑ |f_j|`
  have hUpper_eq : ∀ (coeffs : List ℤ) (k : ℤ),
      (s1FilterUpper coeffs k : ℝ) =
      (∑ d : Fin 13, (coeffs.getD d.val 0 : ℝ) * (s1Moment k d.val : ℝ)) +
      (s1Eps : ℝ) * (∑ d : Fin 13, |(coeffs.getD d.val 0 : ℝ)|) := fun coeffs k => by
    unfold s1FilterUpper
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
  have hzero_low : ∀ (a : List ℤ) (d : Fin 13), d.val < 4 → (filterPolyCoeffs a).getD d.val 0 = 0 := by
    intro a d hd
    unfold filterPolyCoeffs
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
  -- 1. Apply polynomial filters to bound `|lamJ i| < s1CapJ` and `|lamN i| < s1CapN`
  have hcapJ : ∀ i : ιJ, |lamJ i| < (s1CapJ : ℝ) := by
    refine polynomial_filter_tsum lamJ
      (fun d : Fin 13 => (s1FilterJ.getD d.val 0 : ℝ))
      (fun d : Fin 13 => (s1Moment 3 d.val : ℝ)) (ε := (s1Eps : ℝ)) (v := (s1CapJ : ℝ))
      (by unfold s1Eps; norm_num) ?_ ?_ ?_
    · intro d hne
      have hd4 : 4 ≤ d.val := by
        by_contra hlt; push Not at hlt
        apply hne
        rw [show s1FilterJ = filterPolyCoeffs [7, 17, -280, -185, 1000] from rfl, hzero_low _ d hlt]
        norm_num
      exact ⟨hsummJ d.val hd4, htable_J d.val hd4 (by omega)⟩
    · intro x
      rw [show s1FilterJ = filterPolyCoeffs [7, 17, -280, -185, 1000] from rfl,
        filterPolyCoeffs_eval_eq _ (by decide)]
      positivity
    · intro x hx
      rw [← hUpper_eq s1FilterJ 3]
      exact filter_ray_gt_of_check s1FilterJ s1CapJ (s1FilterUpper s1FilterJ 3)
        s1_filter_J_pos_ray s1_filter_J_neg_ray hx
  have hcapN : ∀ i : ιN, |lamN i| < (s1CapN : ℝ) := by
    refine polynomial_filter_tsum lamN
      (fun d : Fin 13 => (s1FilterN.getD d.val 0 : ℝ))
      (fun d : Fin 13 => (s1Moment (-1) d.val : ℝ)) (ε := (s1Eps : ℝ)) (v := (s1CapN : ℝ))
      (by unfold s1Eps; norm_num) ?_ ?_ ?_
    · intro d hne
      have hd4 : 4 ≤ d.val := by
        by_contra hlt; push Not at hlt
        apply hne
        rw [show s1FilterN = filterPolyCoeffs [12, 0, -394, 0, 1000] from rfl, hzero_low _ d hlt]
        norm_num
      exact ⟨hsummN d.val hd4, htable_N d.val hd4 (by omega)⟩
    · intro x
      rw [show s1FilterN = filterPolyCoeffs [12, 0, -394, 0, 1000] from rfl,
        filterPolyCoeffs_eval_eq _ (by decide)]
      positivity
    · intro x hx
      rw [← hUpper_eq s1FilterN (-1)]
      exact filter_ray_gt_of_check s1FilterN s1CapN (s1FilterUpper s1FilterN (-1))
        s1_filter_N_pos_ray s1_filter_N_neg_ray hx
  -- 2. 12th-moment bounds: `∑' i, lamJ i ^ 12 ≤ s1UpJ` and `∑' i, lamN i ^ 12 ≤ s1UpN`
  have hpow12_eq : ∀ x : ℝ, x ^ 12 = |x| ^ 12 := fun x => by
    have : (12 : ℕ) = 2 * 6 := rfl
    rw [this, pow_mul, pow_mul, sq_abs]
  have hJ12_le : ∑' i, |lamJ i| ^ 12 ≤ (s1UpJ : ℝ) := by
    have h := htable_J 12 (by omega) (by omega)
    have h1 : ∑' i, lamJ i ^ 12 ≤ (s1Moment 3 12 : ℝ) + (s1Eps : ℝ) := by linarith [(abs_le.mp h).2]
    unfold s1UpJ; push_cast
    simpa [hpow12_eq] using h1
  have hN12_le : ∑' i, |lamN i| ^ 12 ≤ (s1UpN : ℝ) := by
    have h := htable_N 12 (by omega) (by omega)
    have h1 : ∑' i, lamN i ^ 12 ≤ (s1Moment (-1) 12 : ℝ) + (s1Eps : ℝ) := by linarith [(abs_le.mp h).2]
    unfold s1UpN; push_cast
    simpa [hpow12_eq] using h1
  -- Bound `3 * N_{12*r} ≤ s1Non (12*r)` via `capped_mass_tsum`
  have hN_non : ∀ r : ℕ, 1 ≤ r →
      3 * (∑' i, lamN i ^ (12 * r)) ≤ (s1Non (12 * r) : ℝ) := fun r hr => by
    have hcap12 : ∀ i, |lamN i| ^ 12 ≤ (s1CapN : ℝ) ^ 12 := fun i =>
      pow_le_pow_left₀ (abs_nonneg _) (hcapN i).le 12
    have hcm := capped_mass_tsum (fun i => |lamN i| ^ 12)
      (by unfold s1CapN; positivity) (by unfold s1UpN s1Moment s1Table s1Eps; norm_num)
      (fun i => pow_nonneg (abs_nonneg _) 12) hcap12 (hsummN 12 (by omega)) hN12_le hr
    have hrew : ∀ i, lamN i ^ (12 * r) = (|lamN i| ^ 12) ^ r := fun i => by
      rw [pow_mul, hpow12_eq]
    simp_rw [hrew]
    unfold s1Non
    have hdiv : 12 * r / 12 = r := Nat.mul_div_right r (by norm_num)
    rw [hdiv]
    push_cast
    rw [cappedMassQ_cast]
    have hcast : ((s1CapN ^ 12 : ℚ) : ℝ) = (s1CapN : ℝ) ^ 12 := by push_cast; rfl
    rw [hcast]
    linarith [hcm.2]
  -- 3. Dominant eigenvalue `i₀ : ιJ` with `s1Lo < |lamJ i₀|`
  have hex_dom : ∃ i₀ : ιJ, (s1Lo : ℝ) < |lamJ i₀| := by
    by_contra hno; push Not at hno
    have hcap12 : ∀ i, |lamJ i| ^ 12 ≤ (s1Lo : ℝ) ^ 12 := fun i =>
      pow_le_pow_left₀ (abs_nonneg _) (hno i) 12
    have hcmJ := capped_mass_tsum (fun i => |lamJ i| ^ 12)
      (by unfold s1Lo; positivity) (by unfold s1UpJ s1Moment s1Table s1Eps; norm_num)
      (fun i => pow_nonneg (abs_nonneg _) 12) hcap12 (hsummJ 12 (by omega)) hJ12_le (r := 6) (by omega)
    have hJ72 : ∑' i, lamJ i ^ 72 ≤ (cappedMassQ s1UpJ (s1Lo ^ 12) 6 : ℝ) := by
      have hrew : ∀ i, lamJ i ^ 72 = (|lamJ i| ^ 12) ^ 6 := fun i => by
        rw [show (72 : ℕ) = 12 * 6 by rfl, pow_mul, hpow12_eq]
      simp_rw [hrew]
      rw [cappedMassQ_cast]
      have hcast : ((s1Lo ^ 12 : ℚ) : ℝ) = (s1Lo : ℝ) ^ 12 := by push_cast; rfl
      rw [hcast]; exact hcmJ.2
    have hN72 : 3 * (∑' i, lamN i ^ 72) ≤ (s1Non 72 : ℝ) := hN_non 6 (by omega)
    have hZ72_eq := hZ_even 72 ⟨36, by omega⟩ (by omega)
    have hlt1 : ((cappedMassQ s1UpJ (s1Lo ^ 12) 6 : ℚ) : ℝ) + (s1Non 72 : ℝ) < 1 := by
      exact_mod_cast hinit.1
    linarith
  rcases hex_dom with ⟨i₀, hi₀⟩
  -- 4. Split off `i₀` from `J`, bound residual mass by `s1Tail k` for `k = 36, 72`
  have hresid_bound : ∀ r : ℕ, 1 ≤ r →
      sys.Z (12 * r) (49 / 4 : ℝ) - |lamJ i₀| ^ (12 * r) ≤ (s1Tail (12 * r) : ℝ) := fun r hr => by
    classical
    let tRem : ιJ → ℝ := fun i => if i = i₀ then 0 else |lamJ i| ^ 12
    have htRem_nn : ∀ i, 0 ≤ tRem i := fun i => by dsimp [tRem]; split_ifs <;> positivity
    have hJ12_s : Summable (fun i => |lamJ i| ^ 12) := hsummJ 12 (by omega)
    have htRem_s : Summable tRem := by
      refine Summable.of_nonneg_of_le htRem_nn (fun i => ?_) hJ12_s
      dsimp [tRem]; split_ifs <;> [positivity; exact le_rfl]
    have htRem_sum : ∑' i, tRem i ≤ (s1UpJ : ℝ) - (s1Lo : ℝ) ^ 12 := by
      have hadd : (∑' i, tRem i) + |lamJ i₀| ^ 12 = ∑' i, |lamJ i| ^ 12 := by
        have hpt : ∀ i, tRem i + (if i = i₀ then |lamJ i₀| ^ 12 else 0) = |lamJ i| ^ 12 := fun i => by
          dsimp [tRem]; by_cases h : i = i₀ <;> simp [h]
        have h1s : Summable (fun i : ιJ => if i = i₀ then |lamJ i₀| ^ 12 else 0) :=
          (hasSum_ite_eq i₀ (|lamJ i₀| ^ 12)).summable
        have hsum_add := htRem_s.tsum_add h1s
        simp_rw [hpt] at hsum_add
        rw [tsum_ite_eq] at hsum_add
        exact hsum_add.symm
      have hi₀_12 : (s1Lo : ℝ) ^ 12 ≤ |lamJ i₀| ^ 12 :=
        pow_le_pow_left₀ (by unfold s1Lo; positivity) hi₀.le 12
      linarith
    have hdiff_nn : 0 ≤ (s1UpJ : ℝ) - (s1Lo : ℝ) ^ 12 := by
      have : (s1Lo : ℝ) ^ 12 < (s1UpJ : ℝ) := by exact_mod_cast hinit.2.1
      linarith
    have huncap := uncapped_mass_tsum tRem hdiff_nn htRem_nn htRem_s htRem_sum hr
    have hJ_split : (∑' i, lamJ i ^ (12 * r)) - |lamJ i₀| ^ (12 * r) = ∑' i, tRem i ^ r := by
      have hpt : ∀ i, tRem i ^ r + (if i = i₀ then |lamJ i₀| ^ (12 * r) else 0) = lamJ i ^ (12 * r) := fun i => by
        dsimp [tRem]
        by_cases h : i = i₀
        · subst h; rw [if_pos rfl, if_pos rfl, zero_pow (by omega : r ≠ 0), zero_add, pow_mul, ← hpow12_eq (lamJ i), ← pow_mul]
        · rw [if_neg h, if_neg h, add_zero, ← hpow12_eq (lamJ i), ← pow_mul]
      have h1s : Summable (fun i : ιJ => if i = i₀ then |lamJ i₀| ^ (12 * r) else 0) :=
        (hasSum_ite_eq i₀ (|lamJ i₀| ^ (12 * r))).summable
      have hsum_add := huncap.1.tsum_add h1s
      simp_rw [hpt] at hsum_add
      rw [tsum_ite_eq] at hsum_add
      linarith
    have hZ_eq := hZ_even (12 * r) ⟨6 * r, by omega⟩ (by omega)
    have hN := hN_non r hr
    unfold s1Tail
    have hdiv : 12 * r / 12 = r := Nat.mul_div_right r (by norm_num)
    rw [hdiv]; push_cast
    linarith [huncap.2]
  -- 5. Deduce `1 - S(36, 49/4) ≤ s1P0` and `1 - T(72, 49/4) ≤ s1Q0`
  have hS36 : 1 - sys.toPuritySystem1D.S 36 (49 / 4 : ℝ) ≤ (s1P0 : ℝ) := by
    have hZ36_pos : 0 < sys.Z 36 (49 / 4 : ℝ) := sys.Z_pos ⟨18, by omega⟩ (by omega) (by norm_num)
    have hres36 := hresid_bound 3 (by omega)
    have hZ72_ge : |lamJ i₀| ^ 72 ≤ sys.Z 72 (49 / 4 : ℝ) := by
      rw [hZ_even 72 ⟨36, by omega⟩ (by omega)]
      have hJ_ge : |lamJ i₀| ^ 72 ≤ ∑' i, lamJ i ^ 72 := by
        have hrew : ∀ i, lamJ i ^ 72 = |lamJ i| ^ 72 := fun i => by
          rw [show (72 : ℕ) = 12 * 6 by rfl, pow_mul, hpow12_eq, ← pow_mul]
        simp_rw [hrew]
        exact (hsummJ 72 (by omega)).le_tsum i₀ (fun k _ => pow_nonneg (abs_nonneg _) 72)
      have hN_nn : 0 ≤ ∑' i, lamN i ^ 72 := by
        have hrew : ∀ i, lamN i ^ 72 = |lamN i| ^ 72 := fun i => by
          rw [show (72 : ℕ) = 12 * 6 by rfl, pow_mul, hpow12_eq, ← pow_mul]
        simp_rw [hrew]
        exact tsum_nonneg fun k => pow_nonneg (abs_nonneg _) 72
      linarith
    have hlo36_pos : 0 < (s1Lo : ℝ) ^ 36 := by unfold s1Lo; positivity
    have hdom36_pos : 0 < |lamJ i₀| ^ 36 := pow_pos (lt_trans (by unfold s1Lo; norm_num) hi₀) 36
    have hdom36_ge : (s1Lo : ℝ) ^ 36 ≤ |lamJ i₀| ^ 36 :=
      pow_le_pow_left₀ (by unfold s1Lo; norm_num) hi₀.le 36
    have htail36_nn : 0 ≤ (s1Tail 36 : ℝ) := by
      have : (0 : ℚ) ≤ s1Tail 36 := by decide +kernel
      exact_mod_cast this
    have hrat_le : sys.Z 36 (49 / 4 : ℝ) / |lamJ i₀| ^ 36 ≤ 1 + (s1Tail 36 : ℝ) / (s1Lo : ℝ) ^ 36 := by
      have h1 : sys.Z 36 (49 / 4 : ℝ) / |lamJ i₀| ^ 36 =
          1 + (sys.Z 36 (49 / 4 : ℝ) - |lamJ i₀| ^ 36) / |lamJ i₀| ^ 36 := by
        rw [sub_div, div_self hdom36_pos.ne']; ring
      rw [h1]
      have h2 : (sys.Z 36 (49 / 4 : ℝ) - |lamJ i₀| ^ 36) / |lamJ i₀| ^ 36 ≤
          (s1Tail 36 : ℝ) / |lamJ i₀| ^ 36 :=
        div_le_div_of_nonneg_right hres36 hdom36_pos.le
      have h3 : (s1Tail 36 : ℝ) / |lamJ i₀| ^ 36 ≤ (s1Tail 36 : ℝ) / (s1Lo : ℝ) ^ 36 :=
        div_le_div_of_nonneg_left htail36_nn hlo36_pos hdom36_ge
      linarith
    have hinv_ge : (1 + (s1Tail 36 : ℝ) / (s1Lo : ℝ) ^ 36)⁻¹ ^ 2 ≤
        sys.Z 72 (49 / 4 : ℝ) / (sys.Z 36 (49 / 4 : ℝ)) ^ 2 := by
      have hS_ge : (|lamJ i₀| ^ 36 / sys.Z 36 (49 / 4 : ℝ)) ^ 2 ≤
          sys.Z 72 (49 / 4 : ℝ) / (sys.Z 36 (49 / 4 : ℝ)) ^ 2 := by
        rw [div_pow, ← pow_mul]
        exact div_le_div_of_nonneg_right hZ72_ge (pow_nonneg hZ36_pos.le 2)
      have hinv1 : (1 + (s1Tail 36 : ℝ) / (s1Lo : ℝ) ^ 36)⁻¹ ≤
          |lamJ i₀| ^ 36 / sys.Z 36 (49 / 4 : ℝ) := by
        conv_rhs => rw [← inv_div]
        exact inv_anti₀ (div_pos hZ36_pos hdom36_pos) hrat_le
      have hinv_nn : 0 ≤ (1 + (s1Tail 36 : ℝ) / (s1Lo : ℝ) ^ 36)⁻¹ := by positivity
      exact (pow_le_pow_left₀ hinv_nn hinv1 2).trans hS_ge
    have hSeq : sys.toPuritySystem1D.S 36 (49 / 4 : ℝ) =
        sys.Z 72 (49 / 4 : ℝ) / (sys.Z 36 (49 / 4 : ℝ)) ^ 2 := by
      unfold PuritySystem1D.S; rfl
    rw [hSeq]; unfold s1P0; push_cast
    exact sub_le_sub_left hinv_ge 1
  have hT72 : 1 - sys.toPuritySystem1D.T 72 (49 / 4 : ℝ) ≤ (s1Q0 : ℝ) := by
    have hZ72_pos : 0 < sys.Z 72 (49 / 4 : ℝ) := lt_of_lt_of_le zero_lt_one hZ72_ge1
    have hres72 : sys.Z 72 (49 / 4 : ℝ) - |lamJ i₀| ^ 72 ≤ (s1Tail 72 : ℝ) := by
      simpa only [show 12 * 6 = 72 from rfl] using hresid_bound 6 (by omega)
    have hcap72 : |lamJ i₀| ^ 72 ≤ (s1CapJ : ℝ) ^ 72 :=
      pow_le_pow_left₀ (abs_nonneg _) (hcapJ i₀).le 72
    have hZ72_le : sys.Z 72 (49 / 4 : ℝ) ≤ (s1CapJ : ℝ) ^ 72 + (s1Tail 72 : ℝ) :=
      (sub_le_iff_le_add'.mp hres72).trans (add_le_add hcap72 (le_refl (s1Tail 72 : ℝ)))
    have hinv_ge : ((s1CapJ : ℝ) ^ 72 + (s1Tail 72 : ℝ))⁻¹ ^ 2 ≤
        sys.Z 72 (49 / 2 : ℝ) / (sys.Z 72 (49 / 4 : ℝ)) ^ 2 :=
      inv_sq_ge_of_bounds hZ72_pos hZ72_le hZ72_2b_ge1
    have hTeq : sys.toPuritySystem1D.T 72 (49 / 4 : ℝ) =
        sys.Z 72 (49 / 2 : ℝ) / (sys.Z 72 (49 / 4 : ℝ)) ^ 2 := by
      unfold PuritySystem1D.T
      have h2b : 2 * (49 / 4 : ℝ) = 49 / 2 := by norm_num
      rw [h2b]; rfl
    rw [hTeq]; unfold s1Q0; push_cast
    exact sub_le_sub_left hinv_ge 1
  exact ⟨⟨hS36, hT72⟩, s1_six_rounds_to_2304_exact sys.toPuritySystem1D hS36 hT72⟩

/-- Raw tabulated untwisted center `z_n / 10^6` from OpenAI `lem:thermal-inputs` (`n = 4..12`). -/
def s1RawZ (n : ℕ) : ℚ :=
  if 4 ≤ n ∧ n ≤ 12 then
    match s1Table[n - 4]? with
    | some (z, _) => (z : ℚ) / 10 ^ 6
    | none => 0
  else 0

/-- Raw tabulated `P`-twisted center `p_n / 10^6` from OpenAI `lem:thermal-inputs` (`n = 4..12`). -/
def s1RawP (n : ℕ) : ℚ :=
  if 4 ≤ n ∧ n ≤ 12 then
    match s1Table[n - 4]? with
    | some (_, p) => (p : ℚ) / 10 ^ 6
    | none => 0
  else 0

private lemma s1Moment_eq_raw (k : ℤ) {n : ℕ} (h4 : 4 ≤ n) (h12 : n ≤ 12) :
    s1Moment k n = (s1RawZ n + (k : ℚ) * s1RawP n) / 4 := by
  unfold s1Moment s1RawZ s1RawP
  rw [dif_pos ⟨h4, h12⟩, if_pos ⟨h4, h12⟩, if_pos ⟨h4, h12⟩]
  cases h : s1Table[n - 4]? with
  | none => ring
  | some zp => rcases zp with ⟨z, p⟩; push_cast; ring

/-- **Source 1 Conditional Initialization (Raw-Table Wrapper for `prop:seed2304`)**:
takes the raw untwisted and `P`-twisted thermal table intervals
`|Z_n - z_n| ≤ 30/10^6` and `|Z_n(P) - p_n| ≤ 30/10^6` for **all** `n = 4..12` (including odd `n`),
expressed via the `D₂`-sector spatial eigenvalue decomposition `Z_n = J_n + 3 N_n` and
`Z_n(P) = J_n - N_n`, together with the single non-strict trial bound `1 ≤ Z_72(49/2)`.
Derives the projected bounds `|J_n - c_{J,n}| ≤ 30/10^6` and `|N_n - c_{N,n}| ≤ 30/10^6`
by the triangle inequality and exports both the initial `(36, 49/4)` bounds and the stronger
exact `prop:seed2304` pair `(s1P6 = 84513/10^7, s1Q6 = 27493/5000000)`. -/
theorem source1_seed2304_from_raw_table (sys : SpectralSystem1D)
    {ιJ ιN : Type*} (lamJ : ιJ → ℝ) (lamN : ιN → ℝ)
    (hsummJ : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamJ i| ^ n))
    (hsummN : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamN i| ^ n))
    (hZ_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (49 / 4 : ℝ) = (∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n))
    (hraw_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |((∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n)) - (s1RawZ n : ℝ)| ≤ (s1Eps : ℝ))
    (hraw_P : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |((∑' i, lamJ i ^ n) - (∑' i, lamN i ^ n)) - (s1RawP n : ℝ)| ≤ (s1Eps : ℝ))
    (hZ72_2b_ge1 : 1 ≤ sys.Z 72 (49 / 2 : ℝ)) :
    (1 - sys.toPuritySystem1D.S 36 (49 / 4 : ℝ) ≤ (s1P0 : ℝ) ∧
     1 - sys.toPuritySystem1D.T 72 (49 / 4 : ℝ) ≤ (s1Q0 : ℝ)) ∧
    (1 - sys.toPuritySystem1D.S 2304 (784 : ℝ) ≤ (s1P6 : ℝ) ∧
     1 - sys.toPuritySystem1D.T 4608 (784 : ℝ) ≤ (s1Q6 : ℝ)) := by
  have htable_J : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |(∑' i, lamJ i ^ n) - (s1Moment 3 n : ℝ)| ≤ (s1Eps : ℝ) := fun n h4 h12 => by
    rw [s1Moment_eq_raw 3 h4 h12]; push_cast
    have hZ := abs_le.mp (hraw_Z n h4 h12)
    have hP := abs_le.mp (hraw_P n h4 h12)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htable_N : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |(∑' i, lamN i ^ n) - (s1Moment (-1) n : ℝ)| ≤ (s1Eps : ℝ) := fun n h4 h12 => by
    rw [s1Moment_eq_raw (-1) h4 h12]; push_cast
    have hZ := abs_le.mp (hraw_Z n h4 h12)
    have hP := abs_le.mp (hraw_P n h4 h12)
    have hε : (0 : ℝ) ≤ (s1Eps : ℝ) := by unfold s1Eps; norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact source1_seed2304_from_projected_moments sys lamJ lamN hsummJ hsummN hZ_even
    htable_J htable_N hZ72_2b_ge1

/-- **Source 1 Conditional Uniform Haldane Gap (Raw-Table Interface)**:
chains `source1_seed2304_from_raw_table` directly into `haldane_gap_source1_from_initial_36`
to deduce uniqueness of the ground energy and the uniform spectral gap `γ_L > log 20 / 784`
for every even `L ≥ 2304`, from raw `Z_n` / `Z_n(P)` thermal intervals (`n = 4..12`) and the
single trial consequence `1 ≤ Z_72(49/2)`. -/
theorem source1_gap_from_raw_thermal_table (sys : SpectralSystem1D)
    {ιJ ιN : Type*} (lamJ : ιJ → ℝ) (lamN : ιN → ℝ)
    (hsummJ : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamJ i| ^ n))
    (hsummN : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamN i| ^ n))
    (hZ_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (49 / 4 : ℝ) = (∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n))
    (hraw_Z : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |((∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n)) - (s1RawZ n : ℝ)| ≤ (s1Eps : ℝ))
    (hraw_P : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |((∑' i, lamJ i ^ n) - (∑' i, lamN i ^ n)) - (s1RawP n : ℝ)| ≤ (s1Eps : ℝ))
    (hZ72_2b_ge1 : 1 ≤ sys.Z 72 (49 / 2 : ℝ))
    {L : ℕ} (hL_even : Even L) (hL_ge : 2304 ≤ L) :
    ∃ k₀ : Fin (sys.d L),
      (∀ k : Fin (sys.d L), sys.E L k₀ ≤ sys.E L k) ∧
      (∀ k : Fin (sys.d L), k ≠ k₀ → Real.log 20 / 784 < sys.E L k - sys.E L k₀) := by
  have hseed := source1_seed2304_from_raw_table sys lamJ lamN hsummJ hsummN hZ_even
    hraw_Z hraw_P hZ72_2b_ge1
  have hd_pos : 0 < sys.d L := sys.d_pos L hL_even (by omega)
  have hne : (Finset.univ : Finset (Fin (sys.d L))).Nonempty := ⟨⟨0, hd_pos⟩, Finset.mem_univ _⟩
  rcases Finset.exists_min_image Finset.univ (sys.E L) hne with ⟨k₀, _, hk₀_min⟩
  have hres := haldane_gap_source1_from_initial_36 sys.toPuritySystem1D sys.interp
    hseed.1.1 hseed.1.2 hL_even hL_ge (fun k => sys.E L k + sys.a * (L : ℝ)) k₀
    (fun k => by linarith [hk₀_min k (Finset.mem_univ k)])
    (fun b hb => sys.Z_eq L b hL_even (by omega) hb)
  refine ⟨k₀, fun k => hk₀_min k (Finset.mem_univ k), fun k hne => by linarith [hres.2 k hne]⟩

/-- Backwards-compatible projected-moment wrapper for `source1_gap_from_raw_thermal_table`. -/
theorem source1_gap_from_thermal_table (sys : SpectralSystem1D)
    {ιJ ιN : Type*} (lamJ : ιJ → ℝ) (lamN : ιN → ℝ)
    (hsummJ : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamJ i| ^ n))
    (hsummN : ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamN i| ^ n))
    (hZ_even : ∀ n : ℕ, Even n → 4 ≤ n →
      sys.Z n (49 / 4 : ℝ) = (∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n))
    (htable_J : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |(∑' i, lamJ i ^ n) - (s1Moment 3 n : ℝ)| ≤ (s1Eps : ℝ))
    (htable_N : ∀ n : ℕ, 4 ≤ n → n ≤ 12 →
      |(∑' i, lamN i ^ n) - (s1Moment (-1) n : ℝ)| ≤ (s1Eps : ℝ))
    (hZ72_2b_ge1 : 1 ≤ sys.Z 72 (49 / 2 : ℝ))
    {L : ℕ} (hL_even : Even L) (hL_ge : 2304 ≤ L) :
    ∃ k₀ : Fin (sys.d L),
      (∀ k : Fin (sys.d L), sys.E L k₀ ≤ sys.E L k) ∧
      (∀ k : Fin (sys.d L), k ≠ k₀ → Real.log 20 / 784 < sys.E L k - sys.E L k₀) := by
  have hseed := source1_seed2304_from_projected_moments sys lamJ lamN hsummJ hsummN hZ_even
    htable_J htable_N hZ72_2b_ge1
  have hd_pos : 0 < sys.d L := sys.d_pos L hL_even (by omega)
  have hne : (Finset.univ : Finset (Fin (sys.d L))).Nonempty := ⟨⟨0, hd_pos⟩, Finset.mem_univ _⟩
  rcases Finset.exists_min_image Finset.univ (sys.E L) hne with ⟨k₀, _, hk₀_min⟩
  have hres := haldane_gap_source1_from_initial_36 sys.toPuritySystem1D sys.interp
    hseed.1.1 hseed.1.2 hL_even hL_ge (fun k => sys.E L k + sys.a * (L : ℝ)) k₀
    (fun k => by linarith [hk₀_min k (Finset.mem_univ k)])
    (fun b hb => sys.Z_eq L b hL_even (by omega) hb)
  refine ⟨k₀, fun k => hk₀_min k (Finset.mem_univ k), fun k hne => by linarith [hres.2 k hne]⟩

end PurityBootstrap.MomentInit
