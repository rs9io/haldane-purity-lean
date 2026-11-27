import PurityBootstrap.Basic
import PurityBootstrap.OneD

/-!
# Tarun Grover's Symmetry-Twist Near-Degeneracy & Multiplet Theorems (`arXiv:2611.07400`, Sec. III)

Lean 4 formalization of Grover's Ising symmetry-twist purity bootstrap:
1. **Ising sector comparison (`eq:ising-purity-comparison` & `eq:ising-sector-comparison`)**:
   from `Z_± = Tr A₀^ℓ ± Tr A₁^ℓ` with `S_{+1} ≤ (1 + (Z_{-1}/Z_{+1})^2) / 2`,
   proves `0 ≤ 1 - Z_{-1} / Z_{+1} ≤ 2 * (1 - S_{+1})`.
2. **Twisted sector purity & gap (`eq:twisted-purity` & `eq:twist-gap`)**:
   proves `T_{-1}(ℓ, β_j) ≥ 1 - 9 u_j` and combined sector `k = -1` gap `> log 10 / β₀`.
3. **Full Ising Multiplet Theorem (`IsingTwistSystem.ising_multiplet_theorem`, Eq. `eq:multiplet`)**:
   from the signed two-block transfer interface `Z_± = Tr A₀^ℓ ± Tr A₁^ℓ`, the combined
   untwisted+twisted Gibbs representations, the within-sector seam ordering
   `E_{0,k,t=+} ≤ E_{0,k,t=-}`, and the initial seed `S_{+1}(L₀, β₀), T_{+1}(2 L₀, β₀) ≥ 99/100`,
   proves for every even `ℓ ≥ L₀`:
   - unique untwisted ground states `E₀` (`k = +1`) and `E₁` (`k = -1`) with `E₀ ≤ E₁`,
   - exponentially small splitting `W_ℓ = E₁ - E₀ ≤ (12 / (5 β₀)) * exp (-(log 20) * ℓ / (2 L₀))`,
   - uniform multiplet gap `Γ_ℓ > log 8 / β₀` above `E₁` for every other untwisted state
     (including a sorted-list spectrum version `ising_multiplet_sorted`).
4. **2D Volume-Law Squaring Recurrence (`volume_law_fourth_power_step`, `volume_law_iterated`)**:
   proves the abstract partition-function-difference recurrence `δ_{j+1} ≤ δ_j^4 ⇒ δ_j ≤ δ₀^(4^j)`.
-/

namespace PurityBootstrap.SymmetryTwists

open scoped BigOperators
open Real

/-- Elementary algebraic identity (`arXiv:2611.07400` Eq. `eq:ising-purity-comparison`):
`(a^2 + b^2) / (a + b)^2 = (1 + ((a - b)/(a + b))^2) / 2`. -/
lemma sum_sq_div_sq_sum {a b : ℝ} (hab : a + b ≠ 0) :
    (a ^ 2 + b ^ 2) / (a + b) ^ 2 = (1 + ((a - b) / (a + b)) ^ 2) / 2 := by
  field_simp [hab]
  ring

/-- Sector partition-function ratio bound (`arXiv:2611.07400` Eq. `eq:ising-sector-comparison`):
if `0 < Z₋ ≤ Z₊` and `S₊ ≤ (1 + (Z₋ / Z₊)^2) / 2`, then
`0 ≤ 1 - Z₋ / Z₊ ≤ 2 * (1 - S₊)`. -/
theorem ising_sector_ratio_bound {Zplus Zminus Splus : ℝ}
    (hZp : 0 < Zplus) (hZm : 0 < Zminus) (hle : Zminus ≤ Zplus)
    (hS : Splus ≤ (1 + (Zminus / Zplus) ^ 2) / 2) :
    0 ≤ 1 - Zminus / Zplus ∧ 1 - Zminus / Zplus ≤ 2 * (1 - Splus) := by
  set r := Zminus / Zplus
  have hr0 : 0 < r := div_pos hZm hZp
  have hr1 : r ≤ 1 := (div_le_one hZp).mpr hle
  have hr_sq : r ^ 2 ≤ r := by nlinarith
  refine ⟨by linarith, by linarith⟩

/-- Twisted-sector temporal purity transfer (`arXiv:2611.07400` Eq. `eq:twisted-purity`):
if `T₊ ≥ 1 - 3 u`, `Z₋(b) / Z₊(b) ≤ 1`, and `Z₋(2b) / Z₊(2b) ≥ 1 - 6 u`, then
`T₋ ≥ 1 - 9 u`. -/
theorem twisted_sector_purity_bound
    {Zp_b Zp_2b Zm_b Zm_2b u : ℝ}
    (hZpb : 0 < Zp_b) (hZmb : 0 < Zm_b)
    (hu0 : 0 ≤ u) (hu_le : u ≤ 1 / 100)
    (hTp : 1 - 3 * u ≤ Zp_2b / Zp_b ^ 2)
    (hRat_b : Zm_b ≤ Zp_b)
    (hRat_2b : 1 - 6 * u ≤ Zm_2b / Zp_2b) :
    1 - 9 * u ≤ Zm_2b / Zm_b ^ 2 := by
  have hZp2b_pos : 0 < Zp_2b := by
    have : 0 < 1 - 3 * u := by linarith
    have : 0 < Zp_2b / Zp_b ^ 2 := by linarith
    exact (div_pos_iff_of_pos_right (pow_pos hZpb 2)).mp this
  have hident :
      Zm_2b / Zm_b ^ 2 =
        (Zp_2b / Zp_b ^ 2) * (Zm_2b / Zp_2b) * (Zp_b / Zm_b) ^ 2 := by
    field_simp [hZpb.ne', hZmb.ne', hZp2b_pos.ne']
  rw [hident]
  have hge1 : 1 ≤ (Zp_b / Zm_b) ^ 2 := by
    have h1 : 1 ≤ Zp_b / Zm_b := (one_le_div hZmb).mpr hRat_b
    nlinarith
  have h1m3 : 0 ≤ 1 - 3 * u := by linarith
  have h1m6 : 0 ≤ 1 - 6 * u := by linarith
  have hprod : (1 - 3 * u) * (1 - 6 * u) ≤ (Zp_2b / Zp_b ^ 2) * (Zm_2b / Zp_2b) :=
    mul_le_mul hTp hRat_2b h1m6 (by linarith)
  have hprod_nn : 0 ≤ (Zp_2b / Zp_b ^ 2) * (Zm_2b / Zp_2b) :=
    le_trans (mul_nonneg h1m3 h1m6) hprod
  calc 1 - 9 * u
      ≤ (1 - 3 * u) * (1 - 6 * u) := by nlinarith
    _ ≤ (Zp_2b / Zp_b ^ 2) * (Zm_2b / Zp_2b) := hprod
    _ ≤ (Zp_2b / Zp_b ^ 2) * (Zm_2b / Zp_2b) * (Zp_b / Zm_b) ^ 2 := by nlinarith

/-- Elementary log bound: `-log(1 - x) ≤ x / (1 - x)` for `0 ≤ x < 1`. -/
lemma neg_log_one_sub_le {x : ℝ} (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hinv
  have : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp [hpos.ne']; ring
  linarith

/-- Exponentially small splitting between `k = +1` and `k = -1` ground states
(`arXiv:2611.07400` Eq. `eq:twist-band` & `eq:multiplet`):
from `T₋ ≥ 1 - 9 u_j`, `Z₋ / Z₊ ≥ 1 - 2 u_j`, and `T₋ Z₋ ≤ exp(-b_j E₀₋)` & `exp(-b_j E₀₊) ≤ Z₊`,
proves `E₀₋ - E₀₊ ≤ 12 u_j / b_j ≤ (12 / (5 b₀)) * exp(-(log 20) * ℓ / (2 L₀))`! -/
theorem ising_exponential_splitting
    {E0_plus E0_minus Zplus Zminus Tminus b₀ : ℝ} {L₀ ℓ j : ℕ}
    (hb₀ : 0 < b₀) (hL₀ : 0 < L₀)
    (hℓ_hi : ℓ ≤ 2 * (2 ^ j * L₀))
    (hZp : 0 < Zplus) (hZm : 0 < Zminus)
    (hTm_ge : 1 - 9 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) ≤ Tminus)
    (hRat_ge : 1 - 2 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) ≤ Zminus / Zplus)
    (hLower_m : Tminus * Zminus ≤ Real.exp (-((2 : ℝ) ^ j * b₀) * E0_minus))
    (hUpper_p : Real.exp (-((2 : ℝ) ^ j * b₀) * E0_plus) ≤ Zplus) :
    E0_minus - E0_plus ≤
      (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) := by
  set bj := (2 : ℝ) ^ j * b₀
  set uj := (1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)
  have hbj_pos : 0 < bj := by dsimp [bj]; positivity
  have huj_pos : 0 < uj := by dsimp [uj]; positivity
  have h2j_ge1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
  have huj_le : uj ≤ 1 / 100 := by
    dsimp [uj]
    have hpow : (1 / 20 : ℝ) ^ (2 ^ j) ≤ (1 / 20 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h2j_ge1
    linarith
  have h1m9 : 0 < 1 - 9 * uj := by linarith
  have h1m2 : 0 < 1 - 2 * uj := by linarith
  -- exp(-bj * (E0_minus - E0_plus)) ≥ Tminus * (Zminus / Zplus) ≥ (1 - 9 uj)(1 - 2 uj)
  have hexp_ge : (1 - 9 * uj) * (1 - 2 * uj) ≤ Real.exp (-bj * (E0_minus - E0_plus)) := by
    have h1 : Tminus * (Zminus / Zplus) ≤ Real.exp (-bj * (E0_minus - E0_plus)) := by
      have hdiv : Tminus * Zminus / Zplus ≤
          Real.exp (-bj * E0_minus) / Real.exp (-bj * E0_plus) := by
        calc Tminus * Zminus / Zplus
            ≤ Real.exp (-bj * E0_minus) / Zplus :=
              div_le_div_of_nonneg_right hLower_m hZp.le
          _ ≤ Real.exp (-bj * E0_minus) / Real.exp (-bj * E0_plus) :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hUpper_p
      rw [← Real.exp_sub] at hdiv
      have hexp_eq : -bj * E0_minus - -bj * E0_plus = -bj * (E0_minus - E0_plus) := by ring
      rw [hexp_eq] at hdiv
      simpa [mul_div_assoc] using hdiv
    have h2 : (1 - 9 * uj) * (1 - 2 * uj) ≤ Tminus * (Zminus / Zplus) :=
      mul_le_mul hTm_ge hRat_ge h1m2.le (by linarith)
    linarith
  -- Take logarithms: bj * (E0_minus - E0_plus) ≤ -log(1 - 9 uj) - log(1 - 2 uj) ≤ 12 uj
  have hlog : bj * (E0_minus - E0_plus) ≤ 12 * uj := by
    have hlt := Real.log_le_log (mul_pos h1m9 h1m2) hexp_ge
    rw [Real.log_mul h1m9.ne' h1m2.ne', Real.log_exp] at hlt
    have hl9 : -Real.log (1 - 9 * uj) ≤ (9 * uj) / (1 - 9 * uj) :=
      neg_log_one_sub_le (by linarith)
    have hl2 : -Real.log (1 - 2 * uj) ≤ (2 * uj) / (1 - 2 * uj) :=
      neg_log_one_sub_le (by linarith)
    have h9bound : (9 * uj) / (1 - 9 * uj) ≤ (9 / (91 / 100 : ℝ)) * uj := by
      have hden : (91 / 100 : ℝ) ≤ 1 - 9 * uj := by linarith
      calc (9 * uj) / (1 - 9 * uj) ≤ (9 * uj) / (91 / 100 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = (9 / (91 / 100 : ℝ)) * uj := by ring
    have h2bound : (2 * uj) / (1 - 2 * uj) ≤ (2 / (98 / 100 : ℝ)) * uj := by
      have hden : (98 / 100 : ℝ) ≤ 1 - 2 * uj := by linarith
      calc (2 * uj) / (1 - 2 * uj) ≤ (2 * uj) / (98 / 100 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = (2 / (98 / 100 : ℝ)) * uj := by ring
    have hcoeff : (9 / (91 / 100 : ℝ)) + (2 / (98 / 100 : ℝ)) ≤ 12 := by norm_num
    nlinarith
  -- Convert 12 * uj / bj to (12 / (5 * b₀)) * exp(-log(20) * ℓ / (2 * L₀))
  have h1 : E0_minus - E0_plus ≤ 12 * uj / bj := (le_div_iff₀ hbj_pos).mpr (by linarith)
  have h2 : 12 * uj / bj ≤ 12 * uj / b₀ := by
    have hbj_ge : b₀ ≤ bj := by
      dsimp [bj]
      have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    exact div_le_div_of_nonneg_left (by positivity) hb₀ hbj_ge
  have h3 : (1 / 20 : ℝ) ^ (2 ^ j) ≤ Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) := by
    have hpow_exp : (1 / 20 : ℝ) ^ (2 ^ j) = Real.exp (-(Real.log 20) * ((2 : ℝ) ^ j)) := by
      rw [← Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 20) (2 ^ j)),
        Real.log_pow, one_div, Real.log_inv]
      congr 1; push_cast; ring
    rw [hpow_exp]
    apply Real.exp_le_exp.mpr
    have hlog20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
    have hL0_pos : (0 : ℝ) < L₀ := Nat.cast_pos.mpr hL₀
    have hℓ_cast : (ℓ : ℝ) ≤ 2 * ((2 : ℝ) ^ j * (L₀ : ℝ)) := by exact_mod_cast hℓ_hi
    have hfrac : (ℓ : ℝ) / (2 * (L₀ : ℝ)) ≤ (2 : ℝ) ^ j := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have := mul_le_mul_of_nonneg_left hfrac hlog20.le
    have heq : -(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ)) =
        -(Real.log 20 * ((ℓ : ℝ) / (2 * (L₀ : ℝ)))) := by ring
    rw [heq]; linarith
  calc E0_minus - E0_plus ≤ 12 * uj / b₀ := h1.trans h2
    _ = (12 / (5 * b₀)) * (1 / 20 : ℝ) ^ (2 ^ j) := by dsimp [uj]; ring
    _ ≤ (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- 2D Volume-Law Squaring Step (`arXiv:2611.07400` Sec. III.C, Eq. `eq:volume-splitting`):
when `Sx > 1/2` and `Sy > 1/2`, doubling both spatial directions raises the relative
partition-function difference `δ = 1 - Z₋/Z₊` to its **fourth power** (`δ(2L, 2L) ≤ δ(L, L)^4`),
giving `e^{-c L^2}` volume-law splitting on `L × L` squares! -/
theorem volume_law_fourth_power_step
    {δ0 δx δxy Sx Sy : ℝ}
    (hδ0 : 0 ≤ δ0) (hδx : 0 ≤ δx)
    (hSx : 1 / 2 < Sx) (hSy : 1 / 2 < Sy)
    (hstep_x : δx ≤ δ0 ^ 2 / (2 * Sx))
    (hstep_y : δxy ≤ δx ^ 2 / (2 * Sy)) :
    δxy ≤ δ0 ^ 4 := by
  have h1 : δx ≤ δ0 ^ 2 := by
    have : 1 ≤ 2 * Sx := by linarith
    calc δx ≤ δ0 ^ 2 / (2 * Sx) := hstep_x
      _ ≤ δ0 ^ 2 / 1 := div_le_div_of_nonneg_left (sq_nonneg δ0) zero_lt_one this
      _ = δ0 ^ 2 := div_one _
  have h2 : δxy ≤ δx ^ 2 := by
    have : 1 ≤ 2 * Sy := by linarith
    calc δxy ≤ δx ^ 2 / (2 * Sy) := hstep_y
      _ ≤ δx ^ 2 / 1 := div_le_div_of_nonneg_left (sq_nonneg δx) zero_lt_one this
      _ = δx ^ 2 := div_one _
  have h3 : δx ^ 2 ≤ (δ0 ^ 2) ^ 2 := by nlinarith
  linarith [show (δ0 ^ 2) ^ 2 = δ0 ^ 4 by ring]

/-- Iterated 2D volume-law contraction: `δ_{j+1} ≤ δ_j^4` implies `δ_j ≤ δ₀^(4^j)`. -/
theorem volume_law_iterated {δ : ℕ → ℝ} (hnn : ∀ j, 0 ≤ δ j)
    (hstep : ∀ j, δ (j + 1) ≤ (δ j) ^ 4) :
    ∀ j, δ j ≤ (δ 0) ^ (4 ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc δ (j + 1) ≤ (δ j) ^ 4 := hstep j
      _ ≤ ((δ 0) ^ (4 ^ j)) ^ 4 := pow_le_pow_left₀ (hnn j) ih 4
      _ = (δ 0) ^ (4 ^ (j + 1)) := by rw [← pow_mul]; ring_nf

/-! ## Full Ising Multiplet Theorem (`arXiv:2611.07400`, Eq. `eq:multiplet`, App. `app:ising-bounds`) -/

/-- Elementary sharp numerical inequality `12 / 100 < log 10 - log 8` used to convert
`Γ_ℓ > log 10 / β₀ - 0.12 / β₀` into `Γ_ℓ > log 8 / β₀`. -/
lemma twelve_hundredths_lt_log_ten_sub_log_eight :
    (12 / 100 : ℝ) < Real.log 10 - Real.log 8 := by
  have hexp_neg : (22 / 25 : ℝ) ≤ Real.exp (-(3 / 25 : ℝ)) := by
    have := Real.add_one_le_exp (-(3 / 25 : ℝ))
    linarith
  have hexp_pos : Real.exp (3 / 25 : ℝ) ≤ 25 / 22 := by
    rw [Real.exp_neg] at hexp_neg
    have hpos : 0 < Real.exp (3 / 25 : ℝ) := Real.exp_pos _
    have hinv : (Real.exp (3 / 25 : ℝ))⁻¹ ≥ 22 / 25 := hexp_neg
    have hmul : (22 / 25 : ℝ) * Real.exp (3 / 25 : ℝ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hinv hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  have hexp_lt : Real.exp (12 / 100 : ℝ) < 5 / 4 := by
    have h1 : (12 / 100 : ℝ) = 3 / 25 := by norm_num
    rw [h1]
    linarith
  have hlog_lt : (12 / 100 : ℝ) < Real.log (5 / 4) := by
    have := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp] at this
  have hdiv : Real.log 10 - Real.log 8 = Real.log (5 / 4) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1; norm_num
  linarith

/-- Zero-temperature ordering from all-temperature partition-function dominance:
if `∑ exp(-b * EB_i) ≤ ∑ exp(-b * EA_j)` for all `b > 0`, then `min EA ≤ min EB`. -/
theorem gibbs_min_le_of_Z_le {dA dB : ℕ}
    (EA : Fin dA → ℝ) (EB : Fin dB → ℝ)
    (kA : Fin dA) (kB : Fin dB)
    (hminA : ∀ k, EA kA ≤ EA k)
    (hZ : ∀ b, 0 < b →
      ∑ k : Fin dB, Real.exp (-b * EB k) ≤ ∑ k : Fin dA, Real.exp (-b * EA k)) :
    EA kA ≤ EB kB := by
  by_contra hlt
  push_neg at hlt
  set δ := EA kA - EB kB
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set b := ((dA : ℝ) + 1) / δ
  have hb : 0 < b := div_pos (by positivity) hδ
  have hLB : Real.exp (-b * EB kB) ≤ ∑ k : Fin dB, Real.exp (-b * EB k) :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ kB)
  have hUB : ∑ k : Fin dA, Real.exp (-b * EA k) ≤ (dA : ℝ) * Real.exp (-b * EA kA) := by
    calc ∑ k : Fin dA, Real.exp (-b * EA k)
        ≤ ∑ _k : Fin dA, Real.exp (-b * EA kA) :=
          Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (by nlinarith [hminA k])
      _ = (dA : ℝ) * Real.exp (-b * EA kA) := by simp
  have hineq : Real.exp (-b * EB kB) ≤ (dA : ℝ) * Real.exp (-b * EA kA) :=
    hLB.trans ((hZ b hb).trans hUB)
  have hratio : Real.exp (b * δ) ≤ (dA : ℝ) := by
    have hpos : 0 < Real.exp (-b * EA kA) := Real.exp_pos _
    have hdiv := (div_le_iff₀ hpos).mpr hineq
    rw [← Real.exp_sub] at hdiv
    have heq : -b * EB kB - -b * EA kA = b * δ := by dsimp [δ]; ring
    rwa [heq] at hdiv
  have hbδ : b * δ = (dA : ℝ) + 1 := div_mul_cancel₀ _ hδ.ne'
  rw [hbδ] at hratio
  have hexp_lb : ((dA : ℝ) + 1) + 1 ≤ Real.exp ((dA : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((dA : ℝ) + 1)]
  linarith

/-- Gibbs ground-state bracket: `T * Z ≤ exp (-b * E k₀) ≤ Z` where
`Z = ∑ exp (-b * E k)` and `T = (∑ exp (-2 b * E k)) / Z^2`. -/
lemma gibbs_purity_mul_Z_le_ground {d : ℕ} (E : Fin d → ℝ) (k₀ : Fin d) {b : ℝ}
    (hb : 0 < b) (hmin : ∀ k, E k₀ ≤ E k) :
    ((∑ k : Fin d, Real.exp (-2 * b * E k)) / (∑ k : Fin d, Real.exp (-b * E k)) ^ 2) *
      (∑ k : Fin d, Real.exp (-b * E k)) ≤ Real.exp (-b * E k₀) := by
  set Z := ∑ k : Fin d, Real.exp (-b * E k)
  have hZ_pos : 0 < Z := by
    have hle := Finset.single_le_sum (f := fun k : Fin d => Real.exp (-b * E k))
      (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k₀)
    linarith [Real.exp_pos (-b * E k₀)]
  have hsimp : ((∑ k : Fin d, Real.exp (-2 * b * E k)) / Z ^ 2) * Z =
      (∑ k : Fin d, Real.exp (-2 * b * E k)) / Z := by
    field_simp [hZ_pos.ne']
  rw [hsimp, div_le_iff₀ hZ_pos]
  calc ∑ k : Fin d, Real.exp (-2 * b * E k)
      = ∑ k : Fin d, Real.exp (-b * E k) * Real.exp (-b * E k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ ∑ k : Fin d, Real.exp (-b * E k₀) * Real.exp (-b * E k) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hmin k]))
            (Real.exp_pos _).le
    _ = Real.exp (-b * E k₀) * Z := by rw [← Finset.mul_sum]

/-- Sharp `12 u_j / b_j` splitting estimate (Grover Eq. `eq:twist-band`),
exported directly so callers get both `≤ 12 u_j / b_j ≤ 12 / (100 b₀)` and
`≤ (12 / (5 b₀)) * exp (-(log 20) * ℓ / (2 L₀))`. -/
theorem ising_splitting_12uj
    {E0_plus E0_minus Zplus Zminus Tminus b₀ : ℝ} {j : ℕ}
    (hb₀ : 0 < b₀) (hZp : 0 < Zplus) (hZm : 0 < Zminus)
    (hTm_ge : 1 - 9 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) ≤ Tminus)
    (hRat_ge : 1 - 2 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) ≤ Zminus / Zplus)
    (hLower_m : Tminus * Zminus ≤ Real.exp (-((2 : ℝ) ^ j * b₀) * E0_minus))
    (hUpper_p : Real.exp (-((2 : ℝ) ^ j * b₀) * E0_plus) ≤ Zplus) :
    E0_minus - E0_plus ≤ 12 * ((1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)) / ((2 : ℝ) ^ j * b₀) := by
  set bj := (2 : ℝ) ^ j * b₀
  set uj := (1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j)
  have hbj_pos : 0 < bj := by dsimp [bj]; positivity
  have huj_pos : 0 < uj := by dsimp [uj]; positivity
  have h2j_ge1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
  have huj_le : uj ≤ 1 / 100 := by
    dsimp [uj]
    have hpow : (1 / 20 : ℝ) ^ (2 ^ j) ≤ (1 / 20 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h2j_ge1
    linarith
  have h1m9 : 0 < 1 - 9 * uj := by linarith
  have h1m2 : 0 < 1 - 2 * uj := by linarith
  have hexp_ge : (1 - 9 * uj) * (1 - 2 * uj) ≤ Real.exp (-bj * (E0_minus - E0_plus)) := by
    have h1 : Tminus * (Zminus / Zplus) ≤ Real.exp (-bj * (E0_minus - E0_plus)) := by
      have hdiv : Tminus * Zminus / Zplus ≤
          Real.exp (-bj * E0_minus) / Real.exp (-bj * E0_plus) := by
        calc Tminus * Zminus / Zplus
            ≤ Real.exp (-bj * E0_minus) / Zplus :=
              div_le_div_of_nonneg_right hLower_m hZp.le
          _ ≤ Real.exp (-bj * E0_minus) / Real.exp (-bj * E0_plus) :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hUpper_p
      rw [← Real.exp_sub] at hdiv
      have hexp_eq : -bj * E0_minus - -bj * E0_plus = -bj * (E0_minus - E0_plus) := by ring
      rw [hexp_eq] at hdiv
      simpa [mul_div_assoc] using hdiv
    have h2 : (1 - 9 * uj) * (1 - 2 * uj) ≤ Tminus * (Zminus / Zplus) :=
      mul_le_mul hTm_ge hRat_ge h1m2.le (by linarith)
    linarith
  have hlog : bj * (E0_minus - E0_plus) ≤ 12 * uj := by
    have hlt := Real.log_le_log (mul_pos h1m9 h1m2) hexp_ge
    rw [Real.log_mul h1m9.ne' h1m2.ne', Real.log_exp] at hlt
    have hl9 : -Real.log (1 - 9 * uj) ≤ (9 * uj) / (1 - 9 * uj) :=
      neg_log_one_sub_le (by linarith)
    have hl2 : -Real.log (1 - 2 * uj) ≤ (2 * uj) / (1 - 2 * uj) :=
      neg_log_one_sub_le (by linarith)
    have h9bound : (9 * uj) / (1 - 9 * uj) ≤ (9 / (91 / 100 : ℝ)) * uj := by
      have hden : (91 / 100 : ℝ) ≤ 1 - 9 * uj := by linarith
      calc (9 * uj) / (1 - 9 * uj) ≤ (9 * uj) / (91 / 100 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = (9 / (91 / 100 : ℝ)) * uj := by ring
    have h2bound : (2 * uj) / (1 - 2 * uj) ≤ (2 / (98 / 100 : ℝ)) * uj := by
      have hden : (98 / 100 : ℝ) ≤ 1 - 2 * uj := by linarith
      calc (2 * uj) / (1 - 2 * uj) ≤ (2 * uj) / (98 / 100 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = (2 / (98 / 100 : ℝ)) * uj := by ring
    have hcoeff : (9 / (91 / 100 : ℝ)) + (2 / (98 / 100 : ℝ)) ≤ 12 := by norm_num
    nlinarith
  exact (le_div_iff₀ hbj_pos).mpr (by linarith)

/-- Signed two-block Ising symmetry-twist interface (`arXiv:2611.07400`, Sec. III.A & App. B):
captures two Hermitian spatial transfer spectra `eig0`, `eig1` with
`Z_+(L, b) = Tr A₀^L + Tr A₁^L` and `Z_-(L, b) = Tr A₀^L - Tr A₁^L`,
combined untwisted (`t = +1`) + twisted (`t = -1`) Gibbs representations in both
`k = +1` and `k = -1` sectors, and the within-sector seam ordering `E_{0,k,t=+} ≤ E_{0,k,t=-}`. -/
structure IsingTwistSystem where
  eig0 : ℝ → ℕ → ℝ
  eig1 : ℝ → ℕ → ℝ
  summable0 : ∀ b, 0 < b → Summable (fun i => |eig0 b i| ^ (4 : ℕ))
  summable1 : ∀ b, 0 < b → Summable (fun i => |eig1 b i| ^ (4 : ℕ))
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
  a : ℝ
  Zplus_eq : ∀ L b, Even L → 4 ≤ L → 0 < b →
    (∑' i, |eig0 b i| ^ L) + (∑' i, |eig1 b i| ^ L) =
      (∑ k : Fin (d_pu L), Real.exp (-b * (E_pu L k + a * (L : ℝ)))) +
      (∑ k : Fin (d_pt L), Real.exp (-b * (E_pt L k + a * (L : ℝ))))
  Zminus_eq : ∀ L b, Even L → 4 ≤ L → 0 < b →
    (∑' i, |eig0 b i| ^ L) - (∑' i, |eig1 b i| ^ L) =
      (∑ k : Fin (d_mu L), Real.exp (-b * (E_mu L k + a * (L : ℝ)))) +
      (∑ k : Fin (d_mt L), Real.exp (-b * (E_mt L k + a * (L : ℝ))))
  seam_order_p : ∀ L, Even L → 4 ≤ L →
    ∀ kt : Fin (d_pt L), ∃ ku : Fin (d_pu L), E_pu L ku ≤ E_pt L kt
  seam_order_m : ∀ L, Even L → 4 ≤ L →
    ∀ kt : Fin (d_mt L), ∃ ku : Fin (d_mu L), E_mu L ku ≤ E_mt L kt

namespace IsingTwistSystem

noncomputable def Z0 (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  ∑' i, |sys.eig0 b i| ^ L

noncomputable def Z1 (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  ∑' i, |sys.eig1 b i| ^ L

noncomputable def Zplus (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Z0 L b + sys.Z1 L b

noncomputable def Zminus (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Z0 L b - sys.Z1 L b

noncomputable def Splus (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Zplus (2 * L) b / (sys.Zplus L b) ^ 2

noncomputable def Tplus (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Zplus L (2 * b) / (sys.Zplus L b) ^ 2

noncomputable def Tminus (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Zminus L (2 * b) / (sys.Zminus L b) ^ 2

lemma Zplus_pos (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) : 0 < sys.Zplus L b := by
  unfold Zplus Z0 Z1
  rw [sys.Zplus_eq L b hL h4 hb]
  let k0 : Fin (sys.d_pu L) := ⟨0, sys.d_pu_pos L hL h4⟩
  have h1 : Real.exp (-b * (sys.E_pu L k0 + sys.a * (L : ℝ))) ≤
      ∑ k : Fin (sys.d_pu L), Real.exp (-b * (sys.E_pu L k + sys.a * (L : ℝ))) :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k0)
  have h2 : 0 ≤ ∑ k : Fin (sys.d_pt L), Real.exp (-b * (sys.E_pt L k + sys.a * (L : ℝ))) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  linarith [Real.exp_pos (-b * (sys.E_pu L k0 + sys.a * (L : ℝ)))]

lemma Zminus_pos (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) : 0 < sys.Zminus L b := by
  unfold Zminus Z0 Z1
  rw [sys.Zminus_eq L b hL h4 hb]
  let k0 : Fin (sys.d_mu L) := ⟨0, sys.d_mu_pos L hL h4⟩
  have h1 : Real.exp (-b * (sys.E_mu L k0 + sys.a * (L : ℝ))) ≤
      ∑ k : Fin (sys.d_mu L), Real.exp (-b * (sys.E_mu L k + sys.a * (L : ℝ))) :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k0)
  have h2 : 0 ≤ ∑ k : Fin (sys.d_mt L), Real.exp (-b * (sys.E_mt L k + sys.a * (L : ℝ))) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  linarith [Real.exp_pos (-b * (sys.E_mu L k0 + sys.a * (L : ℝ)))]

lemma Z1_nonneg (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) : 0 ≤ sys.Z1 L b :=
  tsum_nonneg fun i => pow_nonneg (abs_nonneg _) L

lemma Zminus_le_Zplus (sys : IsingTwistSystem) (L : ℕ) (b : ℝ) :
    sys.Zminus L b ≤ sys.Zplus L b := by
  unfold Zminus Zplus
  linarith [sys.Z1_nonneg L b]

private def interleave (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then f (n / 2) else g (n / 2)

private lemma hasSum_interleave {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    HasSum (interleave f g) ((∑' i, f i) + (∑' i, g i)) := by
  let fe : ℕ → ℝ := fun n => if n % 2 = 0 then f (n / 2) else 0
  let fo : ℕ → ℝ := fun n => if n % 2 = 0 then 0 else g (n / 2)
  have hfe : HasSum fe (∑' i, f i) := by
    have hinj : Function.Injective (fun i : ℕ => 2 * i) := fun a b h => by dsimp at h; omega
    have hcomp : fe ∘ (fun i : ℕ => 2 * i) = f := by
      funext i; dsimp [fe]; rw [if_pos (by omega : 2 * i % 2 = 0)]; congr 1; omega
    have hout : ∀ n ∉ Set.range (fun i : ℕ => 2 * i), fe n = 0 := by
      intro n hn; dsimp [fe]
      split_ifs with h
      · exfalso; exact hn ⟨n / 2, by dsimp; omega⟩
      · rfl
    exact (hinj.hasSum_iff hout).mp (by rw [hcomp]; exact hf.hasSum)
  have hfo : HasSum fo (∑' i, g i) := by
    have hinj : Function.Injective (fun i : ℕ => 2 * i + 1) := fun a b h => by dsimp at h; omega
    have hcomp : fo ∘ (fun i : ℕ => 2 * i + 1) = g := by
      funext i; dsimp [fo]; rw [if_neg (by omega : ¬ (2 * i + 1) % 2 = 0)]; congr 1; omega
    have hout : ∀ n ∉ Set.range (fun i : ℕ => 2 * i + 1), fo n = 0 := by
      intro n hn; dsimp [fo]
      split_ifs with h
      · rfl
      · exfalso; exact hn ⟨n / 2, by dsimp; omega⟩
    exact (hinj.hasSum_iff hout).mp (by rw [hcomp]; exact hg.hasSum)
  have hsum : HasSum (fun n => fe n + fo n) ((∑' i, f i) + (∑' i, g i)) := hfe.add hfo
  have heq : (fun n => fe n + fo n) = interleave f g := by
    funext n; dsimp [fe, fo, interleave]; split_ifs <;> ring
  rwa [heq] at hsum

private lemma summable_interleave {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    Summable (interleave f g) :=
  (hasSum_interleave hf hg).summable

private lemma tsum_interleave {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    ∑' n : ℕ, interleave f g n = (∑' i, f i) + (∑' i, g i) :=
  (hasSum_interleave hf hg).tsum_eq

private lemma summable0_of_ge (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (h4 : 4 ≤ L) (hb : 0 < b) : Summable (fun i => |sys.eig0 b i| ^ L) := by
  have hsum4 : Summable (fun i => |sys.eig0 b i| ^ (4 : ℝ)) := by
    simpa [Real.rpow_natCast] using sys.summable0 b hb
  by_cases h0 : ∑' i, |sys.eig0 b i| ^ (4 : ℝ) = 0
  · have hall : ∀ i, |sys.eig0 b i| = 0 := fun i => by
      have hle : |sys.eig0 b i| ^ (4 : ℝ) ≤ ∑' j, |sys.eig0 b j| ^ (4 : ℝ) :=
        hsum4.le_tsum i (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      rw [h0] at hle
      have hzero : |sys.eig0 b i| ^ (4 : ℝ) = 0 :=
        le_antisymm hle (Real.rpow_nonneg (abs_nonneg _) _)
      by_contra hne
      have hpos : 0 < |sys.eig0 b i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      exact (Real.rpow_pos_of_pos hpos 4).ne' hzero
    have hfun : (fun i => |sys.eig0 b i| ^ L) = fun _ => 0 := by
      funext i; rw [hall i, zero_pow (by omega)]
    rw [hfun]; exact summable_zero
  · have hpos4 : 0 < ∑' i, |sys.eig0 b i| ^ (4 : ℝ) :=
      lt_of_le_of_ne (tsum_nonneg fun i => Real.rpow_nonneg (abs_nonneg _) _) (Ne.symm h0)
    have h := (tsum_rpow_le_rpow_div (fun i => |sys.eig0 b i|) (fun _ => abs_nonneg _)
      (p := (4 : ℝ)) (q := (L : ℝ)) (by norm_num) (by exact_mod_cast h4) hsum4 hpos4).1
    simpa [Real.rpow_natCast] using h

private lemma summable1_of_ge (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (h4 : 4 ≤ L) (hb : 0 < b) : Summable (fun i => |sys.eig1 b i| ^ L) := by
  have hsum4 : Summable (fun i => |sys.eig1 b i| ^ (4 : ℝ)) := by
    simpa [Real.rpow_natCast] using sys.summable1 b hb
  by_cases h0 : ∑' i, |sys.eig1 b i| ^ (4 : ℝ) = 0
  · have hall : ∀ i, |sys.eig1 b i| = 0 := fun i => by
      have hle : |sys.eig1 b i| ^ (4 : ℝ) ≤ ∑' j, |sys.eig1 b j| ^ (4 : ℝ) :=
        hsum4.le_tsum i (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      rw [h0] at hle
      have hzero : |sys.eig1 b i| ^ (4 : ℝ) = 0 :=
        le_antisymm hle (Real.rpow_nonneg (abs_nonneg _) _)
      by_contra hne
      have hpos : 0 < |sys.eig1 b i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      exact (Real.rpow_pos_of_pos hpos 4).ne' hzero
    have hfun : (fun i => |sys.eig1 b i| ^ L) = fun _ => 0 := by
      funext i; rw [hall i, zero_pow (by omega)]
    rw [hfun]; exact summable_zero
  · have hpos4 : 0 < ∑' i, |sys.eig1 b i| ^ (4 : ℝ) :=
      lt_of_le_of_ne (tsum_nonneg fun i => Real.rpow_nonneg (abs_nonneg _) _) (Ne.symm h0)
    have h := (tsum_rpow_le_rpow_div (fun i => |sys.eig1 b i|) (fun _ => abs_nonneg _)
      (p := (4 : ℝ)) (q := (L : ℝ)) (by norm_num) (by exact_mod_cast h4) hsum4 hpos4).1
    simpa [Real.rpow_natCast] using h

/-- Spatial purity upper bound from the two-block decomposition (`eq:ising-purity-comparison`):
`S_{+1}(L, b) ≤ (1 + (Z_{-1}(L, b) / Z_{+1}(L, b))^2) / 2`. -/
theorem Splus_le_sector_ratio (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 4 ≤ L) (hb : 0 < b) :
    sys.Splus L b ≤ (1 + (sys.Zminus L b / sys.Zplus L b) ^ 2) / 2 := by
  have hsq_le : ∀ (f : ℕ → ℝ), Summable (fun i => |f i| ^ L) →
      ∑' i, |f i| ^ (2 * L) ≤ (∑' i, |f i| ^ L) ^ 2 := fun f hf => by
    by_cases h0 : ∑' i, |f i| ^ L = 0
    · have hall : ∀ i, |f i| ^ L = 0 := fun i =>
        le_antisymm (by have h := hf.le_tsum i (fun j _ => pow_nonneg (abs_nonneg _) L); rwa [h0] at h)
          (pow_nonneg (abs_nonneg _) L)
      have hfun : (fun i => |f i| ^ (2 * L)) = fun _ => 0 := by
        funext i; rw [mul_comm, pow_mul, hall i, zero_pow (by norm_num)]
      rw [hfun, tsum_zero, h0, zero_pow (by norm_num)]
    · have hpos : 0 < ∑' i, |f i| ^ L :=
        lt_of_le_of_ne (tsum_nonneg fun i => pow_nonneg (abs_nonneg _) L) (Ne.symm h0)
      have hsum_r : Summable (fun i => |f i| ^ (L : ℝ)) := by simpa [Real.rpow_natCast] using hf
      have hpos_r : 0 < ∑' i, |f i| ^ (L : ℝ) := by simpa [Real.rpow_natCast] using hpos
      have h := (tsum_rpow_le_rpow_div (fun i => |f i|) (fun _ => abs_nonneg _)
        (p := (L : ℝ)) (q := ((2 * L : ℕ) : ℝ)) (by positivity)
        (by exact_mod_cast (by omega : L ≤ 2 * L)) hsum_r hpos_r).2
      have hdiv : ((2 * L : ℕ) : ℝ) / (L : ℝ) = (2 : ℝ) := by
        have hL0 : (L : ℝ) ≠ 0 := by positivity
        push_cast; field_simp [hL0]
      rw [hdiv, Real.rpow_two] at h
      have hL1 : (fun i => |f i| ^ ((2 * L : ℕ) : ℝ)) = fun i => |f i| ^ (2 * L) := by
        funext i; exact Real.rpow_natCast _ _
      have hL2 : (fun i => |f i| ^ (L : ℝ)) = fun i => |f i| ^ L := by
        funext i; exact Real.rpow_natCast _ _
      rwa [hL1, hL2] at h
  have h0_le : sys.Z0 (2 * L) b ≤ (sys.Z0 L b) ^ 2 :=
    hsq_le (sys.eig0 b) (sys.summable0_of_ge h4 hb)
  have h1_le : sys.Z1 (2 * L) b ≤ (sys.Z1 L b) ^ 2 :=
    hsq_le (sys.eig1 b) (sys.summable1_of_ge h4 hb)
  have hZp_pos : 0 < sys.Zplus L b := sys.Zplus_pos hL h4 hb
  unfold Splus Zplus Zminus
  have hident := sum_sq_div_sq_sum (a := sys.Z0 L b) (b := sys.Z1 L b) hZp_pos.ne'
  rw [← hident]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- Combined `k = +1` sector packaged as a `SpectralSystem1D` (`Z_+ = Tr (A₀ ⊕ A₁)^L`). -/
noncomputable def toSpectralSystem1D (sys : IsingTwistSystem) : SpectralSystem1D where
  spatialEig := fun b => interleave (sys.eig0 b) (sys.eig1 b)
  spatial_summable := fun b hb => by
    have heq : (fun n : ℕ => |interleave (sys.eig0 b) (sys.eig1 b) n| ^ (4 : ℕ)) =
        interleave (fun i => |sys.eig0 b i| ^ (4 : ℕ)) (fun i => |sys.eig1 b i| ^ (4 : ℕ)) := by
      funext n; unfold interleave; split_ifs <;> rfl
    rw [heq]
    exact summable_interleave (sys.summable0 b hb) (sys.summable1 b hb)
  d := fun L => sys.d_pu L + sys.d_pt L
  d_pos := fun L hL h4 => by have := sys.d_pu_pos L hL h4; omega
  E := fun L => Fin.addCases (sys.E_pu L) (sys.E_pt L)
  a := sys.a
  Z_eq := fun L b hL h4 hb => by
    have heq : (fun n : ℕ => |interleave (sys.eig0 b) (sys.eig1 b) n| ^ L) =
        interleave (fun i => |sys.eig0 b i| ^ L) (fun i => |sys.eig1 b i| ^ L) := by
      funext n; unfold interleave; split_ifs <;> rfl
    rw [heq, tsum_interleave (sys.summable0_of_ge h4 hb) (sys.summable1_of_ge h4 hb),
      sys.Zplus_eq L b hL h4 hb, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.addCases_left]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.addCases_right]

lemma toSpectralSystem1D_Z (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (h4 : 4 ≤ L) (hb : 0 < b) :
    sys.toSpectralSystem1D.Z L b = sys.Zplus L b := by
  unfold SpectralSystem1D.Z toSpectralSystem1D Zplus Z0 Z1
  dsimp only
  have heq : (fun n : ℕ => |interleave (sys.eig0 b) (sys.eig1 b) n| ^ L) =
      interleave (fun i => |sys.eig0 b i| ^ L) (fun i => |sys.eig1 b i| ^ L) := by
    funext n; unfold interleave; split_ifs <;> rfl
  rw [heq, tsum_interleave (sys.summable0_of_ge h4 hb) (sys.summable1_of_ge h4 hb)]

lemma toSpectralSystem1D_S (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (h4 : 4 ≤ L) (hb : 0 < b) :
    sys.toSpectralSystem1D.toPuritySystem1D.S L b = sys.Splus L b := by
  unfold PuritySystem1D.S Splus
  change sys.toSpectralSystem1D.Z (2 * L) b / (sys.toSpectralSystem1D.Z L b) ^ 2 = _
  rw [sys.toSpectralSystem1D_Z (by omega) hb, sys.toSpectralSystem1D_Z h4 hb]

lemma toSpectralSystem1D_T (sys : IsingTwistSystem) {L : ℕ} {b : ℝ}
    (h4 : 4 ≤ L) (hb : 0 < b) :
    sys.toSpectralSystem1D.toPuritySystem1D.T L b = sys.Tplus L b := by
  unfold PuritySystem1D.T Tplus
  change sys.toSpectralSystem1D.Z L (2 * b) / (sys.toSpectralSystem1D.Z L b) ^ 2 = _
  rw [sys.toSpectralSystem1D_Z h4 (by linarith), sys.toSpectralSystem1D_Z h4 hb]

/-- Helper: every nonempty finite real array `f : Fin d → ℝ` attains its minimum. -/
private lemma exists_fin_min {d : ℕ} (hd : 0 < d) (f : Fin d → ℝ) :
    ∃ k₀ : Fin d, ∀ k : Fin d, f k₀ ≤ f k := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  rcases Finset.exists_min_image Finset.univ f hne with ⟨k₀, _, hk₀⟩
  exact ⟨k₀, fun k => hk₀ k (Finset.mem_univ k)⟩

/-- **Full Ising Multiplet Theorem (`arXiv:2611.07400`, Eq. `eq:multiplet`, App. `app:ising-bounds`)**:
for any `IsingTwistSystem` satisfying the starting purity bounds
`S_{+1}(L₀, b₀) ≥ 99/100` and `T_{+1}(2 L₀, b₀) ≥ 99/100` at an even `L₀ ≥ 4` and `b₀ > 0`,
on **every** even length `ℓ ≥ L₀`:
1. There exist unique untwisted ground states `k₀` (in sector `k = +1`) and `k₁` (in sector `k = -1`)
   with `E₀ = E_pu ℓ k₀ ≤ E_mu ℓ k₁ = E₁`.
2. Their splitting is exponentially small:
   `0 ≤ E₁ - E₀ ≤ (12 / (5 b₀)) * exp (-(log 20) * ℓ / (2 L₀))` (and `≤ 12 / (100 b₀)`).
3. Every other untwisted state in sector `k = +1` lies more than `log 20 / b₀` above `E₀`
   (hence more than `log 8 / b₀` above `E₁`), and every other untwisted state in sector `k = -1`
   lies more than `log 10 / b₀` above `E₁` (hence more than `log 8 / b₀` above `E₁`). -/
theorem ising_multiplet_theorem (sys : IsingTwistSystem)
    {L₀ : ℕ} {b₀ : ℝ} (hL₀ : Even L₀) (h4 : 4 ≤ L₀) (hb₀ : 0 < b₀)
    (hS0 : 1 - sys.Splus L₀ b₀ ≤ 1 / 100)
    (hT0 : 1 - sys.Tplus (2 * L₀) b₀ ≤ 1 / 100)
    {ℓ : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : L₀ ≤ ℓ) :
    ∃ (k₀ : Fin (sys.d_pu ℓ)) (k₁ : Fin (sys.d_mu ℓ)),
      0 ≤ sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ∧
      sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤
        (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) ∧
      (∀ k : Fin (sys.d_pu ℓ), k ≠ k₀ → Real.log 20 / b₀ < sys.E_pu ℓ k - sys.E_pu ℓ k₀) ∧
      (∀ k : Fin (sys.d_mu ℓ), k ≠ k₁ → Real.log 10 / b₀ < sys.E_mu ℓ k - sys.E_mu ℓ k₁) ∧
      (∀ k : Fin (sys.d_pu ℓ), k ≠ k₀ → Real.log 8 / b₀ < sys.E_pu ℓ k - sys.E_mu ℓ k₁) ∧
      (∀ k : Fin (sys.d_mu ℓ), k ≠ k₁ → Real.log 8 / b₀ < sys.E_mu ℓ k - sys.E_mu ℓ k₁) := by
  have hℓ4 : 4 ≤ ℓ := le_trans h4 hℓ_ge
  let spec := sys.toSpectralSystem1D
  let psys := spec.toPuritySystem1D
  -- 1. Check bootstrap parameters for u₀ = 1/100, C = 5, r = 1/20
  have hG : bootstrapCoeff (1 / 100 : ℝ) ≤ 5 := by
    unfold bootstrapCoeff; norm_num
  have hS0' : 1 - psys.S L₀ b₀ ≤ 1 / 100 := by
    rwa [sys.toSpectralSystem1D_S h4 hb₀]
  have hT0' : 1 - psys.T (2 * L₀) b₀ ≤ 1 / 100 := by
    rwa [sys.toSpectralSystem1D_T (by omega) hb₀]
  -- 2. Locate ℓ in its dyadic interval [L_j, 2 L_j]
  rcases exists_dyadic_interval_exact (by omega : 0 < L₀) hℓ_ge with ⟨j, hj_lo, hj_hi⟩
  set Lj := 2 ^ j * L₀
  set bj := (2 : ℝ) ^ j * b₀
  set uj := dyadicDefect 5 (5 * (1 / 100 : ℝ)) j
  have hLj_even : Even Lj := by
    rcases hL₀ with ⟨m, hm⟩; exact ⟨2 ^ j * m, by dsimp [Lj]; rw [hm]; ring⟩
  have hLj4 : 4 ≤ Lj := by
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow; dsimp [Lj]; nlinarith
  have hbj_pos : 0 < bj := by dsimp [bj]; positivity
  have huj_eq : uj = (1 / 5 : ℝ) * (1 / 20 : ℝ) ^ (2 ^ j) := by
    dsimp [uj, dyadicDefect]; norm_num
  have huj_pos : 0 < uj := by rw [huj_eq]; positivity
  have huj_le : uj ≤ 1 / 100 := by
    rw [huj_eq]
    have hpow : (1 / 20 : ℝ) ^ (2 ^ j) ≤ (1 / 20 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) Nat.one_le_two_pow
    linarith
  -- 3. Dyadic purities at (L_j, b_j)
  have hdyad := psys.dyadic_purities hL₀ h4 hb₀ (by norm_num) (by norm_num) hG
    (by norm_num) hS0' hT0' j
  have hS_Lj_bj : 1 - uj ≤ psys.S Lj bj := by
    have h1 : 1 - psys.S Lj bj ≤ uj := hdyad.1
    linarith
  have hT_2Lj_bj : 1 - uj ≤ psys.T (2 * Lj) bj := by
    have h2 : 1 - psys.T (2 * Lj) bj ≤ uj := hdyad.2
    linarith
  -- 4. Intermediate-length bounds: S_+(ℓ, b_j) ≥ 1 - u_j, S_+(ℓ, 2 b_j) ≥ 1 - 3 u_j, T_+(ℓ, b_j) ≥ 1 - 3 u_j
  have hS_ℓ_bj : 1 - uj ≤ sys.Splus ℓ bj := by
    have hmono : psys.S Lj bj ≤ psys.S ℓ bj :=
      spec.spatial_purity_mono_even hLj_even hLj4 hℓ_even hj_lo hbj_pos
    have hSℓ : psys.S ℓ bj = sys.Splus ℓ bj := sys.toSpectralSystem1D_S hℓ4 hbj_pos
    linarith
  have hS_Lj_2bj : 1 - 3 * uj ≤ psys.S Lj (2 * bj) := by
    rw [psys.space_time_cancel hLj_even hLj4 hbj_pos]
    have hT_pos : 0 < psys.T Lj bj := psys.T_pos hLj_even hLj4 hbj_pos
    have hT_le1 : psys.T Lj bj ≤ 1 := psys.T_le_one Lj bj hLj_even hLj4 hbj_pos
    have hT_sq_le1 : psys.T Lj bj ^ 2 ≤ 1 := by nlinarith
    have h1mu : 0 ≤ 1 - uj := by linarith
    have hsq : (1 - uj) ^ 2 ≤ psys.S Lj bj ^ 2 := by nlinarith
    have hnum : (1 - uj) ^ 3 ≤ psys.S Lj bj ^ 2 * psys.T (2 * Lj) bj := by
      have hmul := mul_le_mul hsq hT_2Lj_bj h1mu (sq_nonneg _)
      linarith [show (1 - uj) ^ 3 = (1 - uj) ^ 2 * (1 - uj) by ring]
    have hbern : 1 - 3 * uj ≤ (1 - uj) ^ 3 := one_sub_three_mul_le_cube huj_pos.le (by linarith)
    have hdiv : psys.S Lj bj ^ 2 * psys.T (2 * Lj) bj ≤
        psys.S Lj bj ^ 2 * psys.T (2 * Lj) bj / psys.T Lj bj ^ 2 := by
      rw [le_div_iff₀ (pow_pos hT_pos 2)]
      have hnn : 0 ≤ psys.S Lj bj ^ 2 * psys.T (2 * Lj) bj :=
        mul_nonneg (sq_nonneg _) (psys.T_pos (even_two_mul Lj) (by omega) hbj_pos).le
      nlinarith
    linarith
  have hS_ℓ_2bj : 1 - 3 * uj ≤ sys.Splus ℓ (2 * bj) := by
    have hmono : psys.S Lj (2 * bj) ≤ psys.S ℓ (2 * bj) :=
      spec.spatial_purity_mono_even hLj_even hLj4 hℓ_even hj_lo (by linarith)
    have hSℓ : psys.S ℓ (2 * bj) = sys.Splus ℓ (2 * bj) := sys.toSpectralSystem1D_S hℓ4 (by linarith)
    linarith
  have hT_ℓ_bj : 1 - 3 * uj ≤ sys.Tplus ℓ bj := by
    rcases spec.interp Lj ℓ bj hLj_even hLj4 hℓ_even hj_lo hj_hi.le hbj_pos with ⟨hUp, hLo⟩
    have h2Lj : Even (2 * Lj) := even_two_mul Lj
    have hTint := purity_interpolation (by omega : 0 < Lj)
      (psys.Z_pos Lj bj hLj_even hLj4 hbj_pos)
      (psys.Z_pos (2 * Lj) bj h2Lj (by omega) hbj_pos)
      (psys.Z_pos (2 * Lj) (2 * bj) h2Lj (by omega) (by linarith))
      (psys.Z_pos ℓ bj hℓ_even hℓ4 hbj_pos) hUp hLo
    have h1mu : 0 ≤ 1 - uj := by linarith
    have hprod_ge : (1 - uj) ^ 3 ≤
        (psys.Z (2 * Lj) (2 * bj) / psys.Z (2 * Lj) bj ^ 2) *
        (psys.Z (2 * Lj) bj / psys.Z Lj bj ^ 2) ^ 2 := by
      have hsq : (1 - uj) ^ 2 ≤ psys.S Lj bj ^ 2 := by nlinarith
      have hmul := mul_le_mul hT_2Lj_bj hsq (sq_nonneg _) (by linarith)
      have hcube : (1 - uj) * (1 - uj) ^ 2 = (1 - uj) ^ 3 := by ring
      simpa [PuritySystem1D.S, PuritySystem1D.T, hcube] using hmul
    have hprod_le1 :
        (psys.Z (2 * Lj) (2 * bj) / psys.Z (2 * Lj) bj ^ 2) *
        (psys.Z (2 * Lj) bj / psys.Z Lj bj ^ 2) ^ 2 ≤ 1 := by
      have hS1 : psys.S Lj bj ≤ 1 := psys.S_le_one Lj bj hLj_even hLj4 hbj_pos
      have hT1 : psys.T (2 * Lj) bj ≤ 1 := psys.T_le_one (2 * Lj) bj h2Lj (by omega) hbj_pos
      have hS0nn : 0 ≤ psys.S Lj bj := (psys.S_pos hLj_even hLj4 hbj_pos).le
      have hsq : psys.S Lj bj ^ 2 ≤ 1 := by nlinarith
      simpa [PuritySystem1D.S, PuritySystem1D.T] using
        mul_le_mul hT1 hsq (sq_nonneg _) zero_le_one
    have hprod_pos : 0 < (psys.Z (2 * Lj) (2 * bj) / psys.Z (2 * Lj) bj ^ 2) *
        (psys.Z (2 * Lj) bj / psys.Z Lj bj ^ 2) ^ 2 :=
      lt_of_lt_of_le (pow_pos (by linarith : 0 < 1 - uj) 3) hprod_ge
    have hexp_le1 : (ℓ : ℝ) / (2 * (Lj : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hj_hi.le
    have hpow_ge := Real.rpow_le_rpow_of_exponent_ge hprod_pos hprod_le1 hexp_le1
    rw [Real.rpow_one] at hpow_ge
    have hbern : 1 - 3 * uj ≤ (1 - uj) ^ 3 := one_sub_three_mul_le_cube huj_pos.le (by linarith)
    have hTeq : psys.Z ℓ (2 * bj) / psys.Z ℓ bj ^ 2 = sys.Tplus ℓ bj :=
      sys.toSpectralSystem1D_T hℓ4 hbj_pos
    calc 1 - 3 * uj ≤ (1 - uj) ^ 3 := hbern
      _ ≤ (psys.Z (2 * Lj) (2 * bj) / psys.Z (2 * Lj) bj ^ 2) *
            (psys.Z (2 * Lj) bj / psys.Z Lj bj ^ 2) ^ 2 := hprod_ge
      _ ≤ ((psys.Z (2 * Lj) (2 * bj) / psys.Z (2 * Lj) bj ^ 2) *
            (psys.Z (2 * Lj) bj / psys.Z Lj bj ^ 2) ^ 2) ^ ((ℓ : ℝ) / (2 * (Lj : ℝ))) := hpow_ge
      _ ≤ psys.Z ℓ (2 * bj) / psys.Z ℓ bj ^ 2 := hTint
      _ = sys.Tplus ℓ bj := hTeq
  -- 5. Partition-function ratios Z_- / Z_+ at b_j and 2 b_j, and T_-(ℓ, b_j) ≥ 1 - 9 u_j
  have hRat_bj : 1 - 2 * uj ≤ sys.Zminus ℓ bj / sys.Zplus ℓ bj := by
    have h := (ising_sector_ratio_bound (sys.Zplus_pos hℓ_even hℓ4 hbj_pos)
      (sys.Zminus_pos hℓ_even hℓ4 hbj_pos) (sys.Zminus_le_Zplus ℓ bj)
      (sys.Splus_le_sector_ratio hℓ_even hℓ4 hbj_pos)).2
    linarith
  have hRat_2bj : 1 - 6 * uj ≤ sys.Zminus ℓ (2 * bj) / sys.Zplus ℓ (2 * bj) := by
    have h := (ising_sector_ratio_bound (sys.Zplus_pos hℓ_even hℓ4 (by linarith))
      (sys.Zminus_pos hℓ_even hℓ4 (by linarith)) (sys.Zminus_le_Zplus ℓ (2 * bj))
      (sys.Splus_le_sector_ratio hℓ_even hℓ4 (by linarith))).2
    linarith
  have hTm_ge : 1 - 9 * uj ≤ sys.Tminus ℓ bj :=
    twisted_sector_purity_bound (sys.Zplus_pos hℓ_even hℓ4 hbj_pos)
      (sys.Zminus_pos hℓ_even hℓ4 hbj_pos) huj_pos.le huj_le hT_ℓ_bj
      (sys.Zminus_le_Zplus ℓ bj) hRat_2bj
  -- 6. Combined spectra in both sectors, with minimums in untwisted subspaces via seam_order
  rcases exists_fin_min (sys.d_pu_pos ℓ hℓ_even hℓ4) (sys.E_pu ℓ) with ⟨k₀, hk₀_min⟩
  rcases exists_fin_min (sys.d_mu_pos ℓ hℓ_even hℓ4) (sys.E_mu ℓ) with ⟨k₁, hk₁_min⟩
  let Ep : Fin (sys.d_pu ℓ + sys.d_pt ℓ) → ℝ := Fin.addCases (sys.E_pu ℓ) (sys.E_pt ℓ)
  let Em : Fin (sys.d_mu ℓ + sys.d_mt ℓ) → ℝ := Fin.addCases (sys.E_mu ℓ) (sys.E_mt ℓ)
  let k₀_comb : Fin (sys.d_pu ℓ + sys.d_pt ℓ) := Fin.castAdd (sys.d_pt ℓ) k₀
  let k₁_comb : Fin (sys.d_mu ℓ + sys.d_mt ℓ) := Fin.castAdd (sys.d_mt ℓ) k₁
  have hEp_k0 : Ep k₀_comb = sys.E_pu ℓ k₀ := Fin.addCases_left _
  have hEm_k1 : Em k₁_comb = sys.E_mu ℓ k₁ := Fin.addCases_left _
  have hEp_min : ∀ k, Ep k₀_comb ≤ Ep k := fun k => by
    rw [hEp_k0]
    refine Fin.addCases (fun ku => ?_) (fun kt => ?_) k
    · simpa [Ep] using hk₀_min ku
    · rcases sys.seam_order_p ℓ hℓ_even hℓ4 kt with ⟨ku, hku⟩
      simpa [Ep] using (hk₀_min ku).trans hku
  have hEm_min : ∀ k, Em k₁_comb ≤ Em k := fun k => by
    rw [hEm_k1]
    refine Fin.addCases (fun ku => ?_) (fun kt => ?_) k
    · simpa [Em] using hk₁_min ku
    · rcases sys.seam_order_m ℓ hℓ_even hℓ4 kt with ⟨ku, hku⟩
      simpa [Em] using (hk₁_min ku).trans hku
  -- 7. Gibbs representations for Zplus and Zminus with shift a * ℓ
  let Ep_sh : Fin (sys.d_pu ℓ + sys.d_pt ℓ) → ℝ := fun k => Ep k + sys.a * (ℓ : ℝ)
  let Em_sh : Fin (sys.d_mu ℓ + sys.d_mt ℓ) → ℝ := fun k => Em k + sys.a * (ℓ : ℝ)
  have hZplus_gibbs : ∀ b, 0 < b →
      sys.Zplus ℓ b = ∑ k : Fin (sys.d_pu ℓ + sys.d_pt ℓ), Real.exp (-b * Ep_sh k) := fun b hb => by
    rw [← sys.toSpectralSystem1D_Z hℓ4 hb]
    exact sys.toSpectralSystem1D.Z_eq ℓ b hℓ_even hℓ4 hb
  have hZminus_gibbs : ∀ b, 0 < b →
      sys.Zminus ℓ b = ∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-b * Em_sh k) := fun b hb => by
    unfold Zminus Z0 Z1
    rw [sys.Zminus_eq ℓ b hℓ_even hℓ4 hb, Fin.sum_univ_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [Em_sh, Em]; rw [Fin.addCases_left]
    · refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [Em_sh, Em]; rw [Fin.addCases_right]
  -- 8. Ordering E₀ ≤ E₁ from Z_- ≤ Z_+ for all b > 0
  have hE0_le_E1 : sys.E_pu ℓ k₀ ≤ sys.E_mu ℓ k₁ := by
    have hmin_sh : ∀ k, Ep_sh k₀_comb ≤ Ep_sh k := fun k => by dsimp [Ep_sh]; linarith [hEp_min k]
    have hZle : ∀ b, 0 < b →
        ∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-b * Em_sh k) ≤
        ∑ k : Fin (sys.d_pu ℓ + sys.d_pt ℓ), Real.exp (-b * Ep_sh k) := fun b hb => by
      rw [← hZminus_gibbs b hb, ← hZplus_gibbs b hb]
      exact sys.Zminus_le_Zplus ℓ b
    have hsh := gibbs_min_le_of_Z_le Ep_sh Em_sh k₀_comb k₁_comb hmin_sh hZle
    dsimp [Ep_sh, Em_sh] at hsh
    rw [hEp_k0, hEm_k1] at hsh
    linarith
  -- 9. Splitting upper bounds: both ≤ 12 u_j / b_j ≤ 12 / (100 b₀) and exponential in ℓ
  have hLower_m : sys.Tminus ℓ bj * sys.Zminus ℓ bj ≤ Real.exp (-bj * Em_sh k₁_comb) := by
    unfold Tminus
    rw [hZminus_gibbs bj hbj_pos, hZminus_gibbs (2 * bj) (by linarith)]
    have h2 : ∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-(2 * bj) * Em_sh k) =
        ∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-2 * bj * Em_sh k) :=
      Finset.sum_congr rfl fun k _ => by congr 1; ring
    rw [h2]
    exact gibbs_purity_mul_Z_le_ground Em_sh k₁_comb hbj_pos (fun k => by dsimp [Em_sh]; linarith [hEm_min k])
  have hUpper_p : Real.exp (-bj * Ep_sh k₀_comb) ≤ sys.Zplus ℓ bj := by
    rw [hZplus_gibbs bj hbj_pos]
    exact Finset.single_le_sum (f := fun k => Real.exp (-bj * Ep_sh k))
      (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k₀_comb)
  have hsplit_12uj : sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤ 12 * uj / bj := by
    have hdiff : Em_sh k₁_comb - Ep_sh k₀_comb = sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ := by
      dsimp [Em_sh, Ep_sh]; rw [hEm_k1, hEp_k0]; ring
    rw [← hdiff, huj_eq]
    exact ising_splitting_12uj hb₀ (sys.Zplus_pos hℓ_even hℓ4 hbj_pos)
      (sys.Zminus_pos hℓ_even hℓ4 hbj_pos) (by rwa [← huj_eq]) (by rwa [← huj_eq])
      hLower_m hUpper_p
  have hsplit_exp : sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤
      (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ))) := by
    have hdiff : Em_sh k₁_comb - Ep_sh k₀_comb = sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ := by
      dsimp [Em_sh, Ep_sh]; rw [hEm_k1, hEp_k0]; ring
    rw [← hdiff]
    exact ising_exponential_splitting hb₀ (by omega : 0 < L₀) hj_hi.le
      (sys.Zplus_pos hℓ_even hℓ4 hbj_pos) (sys.Zminus_pos hℓ_even hℓ4 hbj_pos)
      (by rwa [← huj_eq]) (by rwa [← huj_eq]) hLower_m hUpper_p
  have hsplit_012 : sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀ ≤ (12 / 100 : ℝ) / b₀ := by
    have hbj_ge : b₀ ≤ bj := by
      dsimp [bj]
      have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    calc sys.E_mu ℓ k₁ - sys.E_pu ℓ k₀
        ≤ 12 * uj / bj := hsplit_12uj
      _ ≤ 12 * uj / b₀ := div_le_div_of_nonneg_left (by positivity) hb₀ hbj_ge
      _ ≤ (12 / 100 : ℝ) / b₀ := div_le_div_of_nonneg_right (by linarith) hb₀.le
  -- 10. Combined k = +1 sector gap > log 20 / b₀
  have hgap_p_spec := spec.uniform_gap hL₀ h4 hb₀ (by norm_num) (by norm_num) hG
    (by norm_num) (by norm_num) hS0' hT0' hℓ_even hℓ_ge k₀_comb hEp_min
  have hgap_p : ∀ k : Fin (sys.d_pu ℓ), k ≠ k₀ →
      Real.log 20 / b₀ < sys.E_pu ℓ k - sys.E_pu ℓ k₀ := fun k hne => by
    have hne_comb : Fin.castAdd (sys.d_pt ℓ) k ≠ k₀_comb := fun heq =>
      hne (Fin.castAdd_injective (sys.d_pu ℓ) (sys.d_pt ℓ) heq)
    have h := hgap_p_spec.2.1 (Fin.castAdd (sys.d_pt ℓ) k) hne_comb
    have h20 : (1 : ℝ) / (5 * (1 / 100 : ℝ)) = 20 := by norm_num
    rw [h20] at h
    simpa [spec, toSpectralSystem1D, Ep, k₀_comb] using h
  -- 11. Combined k = -1 sector gap > log 10 / b₀
  have hgap_m : ∀ k : Fin (sys.d_mu ℓ), k ≠ k₁ →
      Real.log 10 / b₀ < sys.E_mu ℓ k - sys.E_mu ℓ k₁ := by
    have hTm_gibbs : 1 - 9 * uj ≤
        (∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-2 * bj * Em_sh k)) /
        (∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-bj * Em_sh k)) ^ 2 := by
      have h2 : ∑ k : Fin (sys.d_mu ℓ + sys.d_mt ℓ), Real.exp (-2 * bj * Em_sh k) =
          sys.Zminus ℓ (2 * bj) := by
        rw [hZminus_gibbs (2 * bj) (by linarith)]
        refine Finset.sum_congr rfl fun k _ => by congr 1; ring
      rw [h2, ← hZminus_gibbs bj hbj_pos]
      exact hTm_ge
    have hgibbs_m := gibbs_purity_implies_unique_ground_and_gap Em_sh k₁_comb bj hbj_pos
      (fun k => by dsimp [Em_sh]; linarith [hEm_min k]) (by positivity) (by linarith) hTm_gibbs
    intro k hne
    have hne_comb : Fin.castAdd (sys.d_mt ℓ) k ≠ k₁_comb := fun heq =>
      hne (Fin.castAdd_injective (sys.d_mu ℓ) (sys.d_mt ℓ) heq)
    have hexp_le := hgibbs_m.2 (Fin.castAdd (sys.d_mt ℓ) k) hne_comb
    have hratio_lt : 9 * uj / (1 - 9 * uj) < (1 / 10 : ℝ) ^ (2 ^ j) := by
      have h1m_pos : 0 < 1 - 9 * uj := by linarith only [huj_le]
      have h10u : 9 * uj / (1 - 9 * uj) < 10 * uj := by
        rw [div_lt_iff₀ h1m_pos]
        nlinarith only [huj_pos, huj_le]
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
    have hexp_lt : Real.exp (-bj * (Em_sh (Fin.castAdd (sys.d_mt ℓ) k) - Em_sh k₁_comb)) <
        (1 / 10 : ℝ) ^ (2 ^ j) := lt_of_le_of_lt hexp_le hratio_lt
    have hlog_lt : -bj * (Em_sh (Fin.castAdd (sys.d_mt ℓ) k) - Em_sh k₁_comb) <
        (2 ^ j : ℕ) * Real.log (1 / 10) := by
      have := Real.log_lt_log (Real.exp_pos _) hexp_lt
      rwa [Real.log_exp, Real.log_pow] at this
    have hlog_inv : Real.log (1 / 10 : ℝ) = -Real.log 10 := by rw [one_div, Real.log_inv]
    rw [hlog_inv] at hlog_lt
    have hdiff_eq : Em_sh (Fin.castAdd (sys.d_mt ℓ) k) - Em_sh k₁_comb =
        sys.E_mu ℓ k - sys.E_mu ℓ k₁ := by
      dsimp [Em_sh, Em, k₁_comb]; simp
    rw [hdiff_eq] at hlog_lt
    rw [div_lt_iff₀ hb₀]
    have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hbj_eq : bj = (2 : ℝ) ^ j * b₀ := rfl
    rw [hbj_eq, Nat.cast_pow, Nat.cast_ofNat] at hlog_lt
    nlinarith only [hlog_lt, h2j_pos]
  -- 12. Assemble multiplet gap > log 8 / b₀ above E₁ for every other untwisted state
  have hlog8_lt_10 : Real.log 8 < Real.log 10 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog10_lt_20 : Real.log 10 < Real.log 20 := Real.log_lt_log (by norm_num) (by norm_num)
  have h12_lt := twelve_hundredths_lt_log_ten_sub_log_eight
  refine ⟨k₀, k₁, by linarith only [hE0_le_E1], hsplit_exp, hgap_p, hgap_m, ?_, ?_⟩
  · intro k hne
    have hgp := hgap_p k hne
    have h1 : (Real.log 10 - 12 / 100) / b₀ < (Real.log 20 - 12 / 100) / b₀ :=
      div_lt_div_of_pos_right (by linarith only [hlog10_lt_20]) hb₀
    have h2 : Real.log 8 / b₀ < (Real.log 10 - 12 / 100) / b₀ :=
      div_lt_div_of_pos_right (by linarith only [h12_lt]) hb₀
    have hsub : Real.log 20 / b₀ - (12 / 100 : ℝ) / b₀ = (Real.log 20 - 12 / 100) / b₀ := by ring
    linarith only [hgp, hsplit_012, h1, h2, hsub]
  · intro k hne
    have hgm := hgap_m k hne
    have hlt : Real.log 8 / b₀ < Real.log 10 / b₀ := div_lt_div_of_pos_right hlog8_lt_10 hb₀
    linarith only [hgm, hlt]

/-- Sorted-spectrum corollary of `ising_multiplet_theorem`:
sorting the full untwisted spectrum `List.ofFn (sys.E_pu ℓ) ++ List.ofFn (sys.E_mu ℓ)`
(with multiplicity) in ascending order `s = mergeSort (· ≤ ·)` yields
`W_ℓ = s[1] - s[0] ≤ (12 / (5 b₀)) * exp (-(log 20) * ℓ / (2 L₀))`
and for every higher level `i ≥ 2`, `s[i] - s[1] > log 8 / b₀`. -/
theorem ising_multiplet_sorted (sys : IsingTwistSystem)
    {L₀ : ℕ} {b₀ : ℝ} (hL₀ : Even L₀) (h4 : 4 ≤ L₀) (hb₀ : 0 < b₀)
    (hS0 : 1 - sys.Splus L₀ b₀ ≤ 1 / 100)
    (hT0 : 1 - sys.Tplus (2 * L₀) b₀ ≤ 1 / 100)
    {ℓ : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : L₀ ≤ ℓ) :
    let raw := List.ofFn (sys.E_pu ℓ) ++ List.ofFn (sys.E_mu ℓ)
    let sorted := raw.mergeSort (· ≤ ·)
    2 ≤ sorted.length ∧
    (∀ h0 h1, 0 ≤ sorted[1]'h1 - sorted[0]'h0 ∧
      sorted[1]'h1 - sorted[0]'h0 ≤
        (12 / (5 * b₀)) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / (2 * (L₀ : ℝ)))) ∧
    (∀ i (hi : i < sorted.length) (h1 : 1 < sorted.length), 2 ≤ i →
      Real.log 8 / b₀ < sorted[i]'hi - sorted[1]'h1) := by
  rcases sys.ising_multiplet_theorem hL₀ h4 hb₀ hS0 hT0 hℓ_even hℓ_ge with
    ⟨k₀, k₁, hord, hsplit, _, _, hgap_p, hgap_m⟩
  intro raw sorted
  have hℓ4 : 4 ≤ ℓ := le_trans h4 hℓ_ge
  have hperm : sorted.Perm raw := List.mergeSort_perm raw (· ≤ ·)
  have hlen : sorted.length = sys.d_pu ℓ + sys.d_mu ℓ := by
    rw [hperm.length_eq]; simp [raw]
  have hlen2 : 2 ≤ sorted.length := by
    have := sys.d_pu_pos ℓ hℓ_even hℓ4
    have := sys.d_mu_pos ℓ hℓ_even hℓ4
    omega
  have hsorted : sorted.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (· ≤ ·) raw
  -- Every element of `raw` except the two occurrences (k₀, k₁) is strictly > E₁ + log 8 / b₀.
  set E₀ := sys.E_pu ℓ k₀
  set E₁ := sys.E_mu ℓ k₁
  have hlog8_pos : 0 < Real.log 8 / b₀ := div_pos (Real.log_pos (by norm_num)) hb₀
  -- Count elements of `raw` that are ≤ E₁ + log 8 / b₀:
  -- In `ofFn (E_pu ℓ)`, only index `k₀` satisfies it; in `ofFn (E_mu ℓ)`, only index `k₁` does.
  have hcount_lt : ∀ {n : ℕ} (f : Fin n → ℝ) (kstar : Fin n),
      f kstar ≤ E₁ →
      (∀ k, k ≠ kstar → E₁ + Real.log 8 / b₀ < f k) →
      (List.ofFn f).countP (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = 1 := by
    intro n f kstar hle hgt
    rw [List.countP_eq_length_filter]
    have hmap : List.ofFn f = (List.finRange n).map f := List.ofFn_eq_map
    rw [hmap, List.filter_map, List.length_map]
    have hfilt : (List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) = [kstar] := by
      have hnodup : ((List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀))).Nodup :=
        (List.nodup_finRange n).filter _
      have hmem : ∀ k, k ∈ (List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) ↔
          k = kstar := by
        intro k
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        constructor
        · intro hk; by_contra hne; linarith [hgt k hne]
        · intro hk; subst hk; linarith
      cases hL : (List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) with
      | nil =>
        have := (hmem kstar).mpr rfl
        rw [hL] at this; exact absurd this List.not_mem_nil
      | cons a tl =>
        have ha : a = kstar := (hmem a).mp (by rw [hL]; simp)
        subst ha
        cases tl with
        | nil => rfl
        | cons b tl' =>
          have hb : b = a := (hmem b).mp (by rw [hL]; simp)
          subst hb
          rw [hL] at hnodup
          exact absurd (List.mem_cons_self) (List.nodup_cons.mp hnodup).1
    change (List.filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) (List.finRange n)).length = 1
    rw [hfilt]; rfl
  have hcp_raw : raw.countP (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = 2 := by
    dsimp [raw]
    rw [List.countP_append,
      hcount_lt (sys.E_pu ℓ) k₀ (by linarith) (fun k hne => by linarith [hgap_p k hne]),
      hcount_lt (sys.E_mu ℓ) k₁ le_rfl (fun k hne => by linarith [hgap_m k hne])]
  have hcp_sorted : sorted.countP (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = 2 := by
    rw [hperm.countP_eq, hcp_raw]
  -- Extract the exact two elements of `sorted.filter (≤ E₁ + log 8 / b₀)` as `[E₀, E₁]`
  have hfilt_raw_perm :
      (raw.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).Perm [E₀, E₁] := by
    have hfilt_single : ∀ {n : ℕ} (f : Fin n → ℝ) (kstar : Fin n),
        f kstar ≤ E₁ →
        (∀ k, k ≠ kstar → E₁ + Real.log 8 / b₀ < f k) →
        (List.ofFn f).filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [f kstar] := by
      intro n f kstar hle hgt
      rw [List.ofFn_eq_map, List.filter_map]
      have hfilt : (List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) = [kstar] := by
        have hnodup := (List.nodup_finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀))
        have hmem : ∀ k, k ∈ (List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) ↔
            k = kstar := by
          intro k
          simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
          constructor
          · intro hk; by_contra hne; linarith [hgt k hne]
          · intro hk; subst hk; linarith
        cases hL : (List.finRange n).filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) with
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
      change List.map f (List.filter (fun k => decide (f k ≤ E₁ + Real.log 8 / b₀)) (List.finRange n)) = [f kstar]
      rw [hfilt]; rfl
    dsimp [raw]
    rw [List.filter_append,
      hfilt_single (sys.E_pu ℓ) k₀ (by linarith) (fun k hne => by linarith [hgap_p k hne]),
      hfilt_single (sys.E_mu ℓ) k₁ le_rfl (fun k hne => by linarith [hgap_m k hne])]
    exact List.Perm.refl [E₀, E₁]
  have hfilt_sorted_perm :
      (sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).Perm [E₀, E₁] :=
    (hperm.filter _).trans hfilt_raw_perm
  -- Since `sorted` is sorted ascending, its prefix of length 2 equals `[E₀, E₁]`,
  -- and every element at index `i ≥ 2` is strictly greater than `E₁ + log 8 / b₀`!
  have htake2 : sorted.take 2 = [E₀, E₁] ∧
      ∀ i (hi : i < sorted.length), 2 ≤ i → E₁ + Real.log 8 / b₀ < sorted[i]'hi := by
    -- Write `sorted = a :: b :: rest` using `2 ≤ sorted.length`
    rcases List.exists_cons_of_length_pos (by omega : 0 < sorted.length) with ⟨a, t1, ht1⟩
    have ht1_len : 1 ≤ t1.length := by rw [ht1] at hlen2; simp at hlen2; omega
    rcases List.exists_cons_of_length_pos (by omega : 0 < t1.length) with ⟨b, rest, hrest⟩
    have hsorted_eq : sorted = a :: b :: rest := by rw [ht1, hrest]
    have hpw : (a :: b :: rest).Pairwise (· ≤ ·) := hsorted_eq ▸ hsorted
    have hab : a ≤ b := (List.pairwise_cons.mp hpw).1 b List.mem_cons_self
    have hbrest : ∀ x ∈ rest, b ≤ x := (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1
    have harest : ∀ x ∈ rest, a ≤ x := fun x hx => le_trans hab (hbrest x hx)
    -- Both `a` and `b` must pass the filter (otherwise filter length < 2!)
    have hfilt_len : (sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).length = 2 := by
      rw [hfilt_sorted_perm.length_eq]; rfl
    have hb_le : b ≤ E₁ + Real.log 8 / b₀ := by
      by_contra hgt; push_neg at hgt
      have hrest_gt : ∀ x ∈ rest, ¬ (x ≤ E₁ + Real.log 8 / b₀) :=
        fun x hx => by linarith [hbrest x hx]
      have hfilt_rest : rest.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; simp [hrest_gt x hx]
      have hlen_le1 : (sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀))).length ≤ 1 := by
        rw [hsorted_eq]
        simp [List.filter_cons, not_le.mpr hgt, hfilt_rest]
        split_ifs <;> simp
      omega
    have ha_le : a ≤ E₁ + Real.log 8 / b₀ := le_trans hab hb_le
    -- And NO element of `rest` passes the filter (otherwise filter length ≥ 3!)
    have hrest_gt : ∀ x ∈ rest, E₁ + Real.log 8 / b₀ < x := by
      intro x hx
      by_contra hle; push_neg at hle
      have hmem : x ∈ rest.filter (fun y => decide (y ≤ E₁ + Real.log 8 / b₀)) :=
        List.mem_filter.mpr ⟨hx, decide_eq_true hle⟩
      have hpos : 0 < (rest.filter (fun y => decide (y ≤ E₁ + Real.log 8 / b₀))).length :=
        List.length_pos_of_mem hmem
      have hge3 : 3 ≤ (sorted.filter (fun y => decide (y ≤ E₁ + Real.log 8 / b₀))).length := by
        rw [hsorted_eq]; simp [List.filter_cons, ha_le, hb_le]; omega
      omega
    have hfilt_rest : rest.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx; simp [not_le.mpr (hrest_gt x hx)]
    have hfilt_eq : sorted.filter (fun x => decide (x ≤ E₁ + Real.log 8 / b₀)) = [a, b] := by
      rw [hsorted_eq]; simp [List.filter_cons, ha_le, hb_le, hfilt_rest]
    rw [hfilt_eq] at hfilt_sorted_perm
    have hab_eq : a = E₀ ∧ b = E₁ := by
      have h1 : (a = E₀ ∧ b = E₁) ∨ (a = E₁ ∧ b = E₀) := by
        simpa using List.perm_pair.mp hfilt_sorted_perm
      rcases h1 with h | ⟨rfl, rfl⟩
      · exact h
      · exact ⟨le_antisymm hab (by linarith), le_antisymm (by linarith) hab⟩
    refine ⟨?_, ?_⟩
    · rw [hsorted_eq, hab_eq.1, hab_eq.2]; rfl
    · intro i hi hi2
      have hmem : sorted[i]'hi ∈ rest := by
        cases i with
        | zero => omega
        | succ i' =>
          cases i' with
          | zero => omega
          | succ j =>
            have hj : j < rest.length := by rw [hsorted_eq] at hi; simp at hi; omega
            have hget : sorted[j + 2]'hi = rest[j]'hj := by simp [hsorted_eq]
            rw [hget]
            exact List.getElem_mem hj
      exact hrest_gt _ hmem
  have hs0 : ∀ h0 : 0 < sorted.length, sorted[0]'h0 = E₀ := fun h0 => by
    have h := congrArg (fun l => l[0]?) htake2.1
    simp [List.getElem?_take_of_lt, h0] at h
    exact h
  have hs1 : ∀ h1 : 1 < sorted.length, sorted[1]'h1 = E₁ := fun h1 => by
    have h := congrArg (fun l => l[1]?) htake2.1
    simp [List.getElem?_take_of_lt, h1] at h
    exact h
  refine ⟨hlen2, ?_, ?_⟩
  · intro h0 h1
    rw [hs0 h0, hs1 h1]
    exact ⟨hord, hsplit⟩
  · intro i hi h1 hi2
    rw [hs1 h1]
    linarith [htake2.2 i hi hi2]

end IsingTwistSystem

end PurityBootstrap.SymmetryTwists
