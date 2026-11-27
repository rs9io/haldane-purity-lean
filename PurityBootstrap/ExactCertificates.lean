import PurityBootstrap.Basic
import PurityBootstrap.OneD

/-!
# Exact Rational Audit of OpenAI's Haldane Purity-Bootstrap Scalars (`source_1` & `source_2`)

Machine-checks the exact rational scalar inequalities for OpenAI's
`check-bootstrap-scalars.py` and `check-moment-initializations.py` inside Lean 4's kernel
using `decide +kernel` (zero `native_decide`, zero floating point, zero `sorry`), and connects
both certified parameter rows to `PurityBootstrap.uniform_gap_from_purities`:
- **Source 2 (`n₀ = 60, b₀ = 105/4, u₀ = 1/8, C = 79/10, r = 79/80`)**:
  conditional on the initial purities `(hS60, hT120)` and `PuritySystem1D` + `hInterp`,
  proves `γ_L > (4/105) * log (80/79)` for all even `L ≥ 60`.
- **Source 1 (`n₀ = 2304, b₀ = 784, u₀ = 1/100, C = 5, r = 1/20`)**:
  propagates the 6 exact rounded coupled updates from `(36, 49/4)` to `(2304, 784)` and,
  conditional on `(hS36, hT72)` and `PuritySystem1D` + `hInterp`,
  proves `γ_L > log 20 / 784` for all even `L ≥ 2304`.
- Also verifies the four Source 1 filter-ray inequalities (`s1_filter_*`), dominant-existence
  scalar bounds (`s1_dominant_existence_and_initial_bounds`), and Source 2 moment/residual
  scalar checks (`s2_all_scalar_initializations_exact`) directly in Lean's kernel.
-/

namespace PurityBootstrap.ExactCertificates

/-- Exact rational purity-update map `f_Q(u) = u^2 / (2 (1 - u)^2)`. -/
def fQ (u : ℚ) : ℚ :=
  u ^ 2 / (2 * (1 - u) ^ 2)

/-- Exact rational bootstrap coefficient `G_Q(u) = ((1-u)⁻¹ + (1-u)⁻² + (1-u)⁻³)^2 / 2`. -/
def GQ (u : ℚ) : ℚ :=
  ((1 - u)⁻¹ + (1 - u)⁻¹ ^ 2 + (1 - u)⁻¹ ^ 3) ^ 2 / 2

lemma fQ_cast (u : ℚ) : ((fQ u : ℚ) : ℝ) = purityUpdate (u : ℝ) := by
  unfold fQ purityUpdate
  push_cast
  rfl

lemma GQ_cast (u : ℚ) : ((GQ u : ℚ) : ℝ) = bootstrapCoeff (u : ℝ) := by
  unfold GQ bootstrapCoeff
  push_cast
  rfl

/-- Exact ceiling onto the `10⁻⁷` grid: `⌈x⌉₇ = ⌈10⁷ x⌉ / 10⁷`. -/
def ceilGrid7 (x : ℚ) : ℚ :=
  (⌈x * (10 ^ 7 : ℚ)⌉ : ℚ) / (10 ^ 7 : ℚ)

lemma le_ceilGrid7 (x : ℚ) : x ≤ ceilGrid7 x := by
  unfold ceilGrid7
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 7)]
  exact Int.le_ceil (x * (10 ^ 7 : ℚ))

/-- Exact rational capped mass `C(m, h, r) = q * h^r + (m - q * h)^r`, `q = ⌊m / h⌋`. -/
def cappedMassQ (m h : ℚ) (r : ℕ) : ℚ :=
  let q : ℤ := ⌊m / h⌋
  (q : ℚ) * h ^ r + (m - (q : ℚ) * h) ^ r

/-! ## Source 1 (`b₀ = 49/4`, 6 rounded rounds `(36, 49/4) → (2304, 784)`) -/

def s1Table : List (ℤ × ℤ) :=
  [(124885379, 65757), (2925, 2960742), (12870614, 286599),
   (54069, 1920414), (4639283, 510140), (195455, 1514846),
   (2654823, 675419), (377629, 1314544), (1900547, 787405)]

def s1Eps : ℚ := 30 / 10 ^ 6
def s1CapJ : ℚ := 100139 / 100000
def s1CapN : ℚ := 872 / 1000
def s1Lo : ℚ := 999 / 1000

/-- Shifted moments `J_n` (`k = 3`) and `N_n` (`k = -1`) for `n = 4..12`. -/
def s1Moment (k : ℤ) (n : ℕ) : ℚ :=
  if h : 4 ≤ n ∧ n ≤ 12 then
    match s1Table[n - 4]? with
    | some (z, p) => ((z + k * p : ℤ) : ℚ) / (4 * 10 ^ 6)
    | none => 0
  else 0

/-- Squared polynomial filter coefficients `x^4 * (∑ a_i x^i)^2` at degree `deg ∈ [0..12]`. -/
def filterPolyCoeffs (a : List ℤ) : List ℤ :=
  (List.range 13).map fun d =>
    (List.range a.length).foldl (fun acc i =>
      (List.range a.length).foldl (fun acc2 j =>
        if i + j + 4 = d then acc2 + a.getD i 0 * a.getD j 0 else acc2) acc) 0

def s1FilterJ : List ℤ := filterPolyCoeffs [7, 17, -280, -185, 1000]
def s1FilterN : List ℤ := filterPolyCoeffs [12, 0, -394, 0, 1000]

/-- Upper bound `B = ∑ f_j c_j + ε ∑ |f_j|` from Lemma `lem:polynomial-filter`. -/
def s1FilterUpper (coeffs : List ℤ) (k : ℤ) : ℚ :=
  ((List.range 13).map fun d =>
    let c : ℤ := coeffs.getD d 0
    (c : ℚ) * s1Moment k d + (|c| : ℚ) * s1Eps).sum

/-- Taylor-shifted coefficient of `F(sign * (cap + y))` at `y^j` (`j ∈ [0..12]`). -/
def shiftedFilterCoeff (coeffs : List ℤ) (sign : ℤ) (cap : ℚ) (j : ℕ) : ℚ :=
  ((List.range 13).map fun i =>
    if j ≤ i then
      (Nat.choose i j : ℚ) * (coeffs.getD i 0 : ℚ) * ((sign : ℚ) ^ i) * (cap ^ (i - j))
    else 0).sum

theorem s1_filter_J_pos_ray :
    s1FilterUpper s1FilterJ 3 < shiftedFilterCoeff s1FilterJ 1 s1CapJ 0 ∧
    (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff s1FilterJ 1 s1CapJ (j + 1))) = true := by
  constructor <;> decide +kernel

theorem s1_filter_J_neg_ray :
    s1FilterUpper s1FilterJ 3 < shiftedFilterCoeff s1FilterJ (-1) s1CapJ 0 ∧
    (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff s1FilterJ (-1) s1CapJ (j + 1))) = true := by
  constructor <;> decide +kernel

theorem s1_filter_N_pos_ray :
    s1FilterUpper s1FilterN (-1) < shiftedFilterCoeff s1FilterN 1 s1CapN 0 ∧
    (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff s1FilterN 1 s1CapN (j + 1))) = true := by
  constructor <;> decide +kernel

theorem s1_filter_N_neg_ray :
    s1FilterUpper s1FilterN (-1) < shiftedFilterCoeff s1FilterN (-1) s1CapN 0 ∧
    (List.range 12).all (fun j => decide (0 ≤ shiftedFilterCoeff s1FilterN (-1) s1CapN (j + 1))) = true := by
  constructor <;> decide +kernel

def s1UpJ : ℚ := s1Moment 3 12 + s1Eps
def s1UpN : ℚ := s1Moment (-1) 12 + s1Eps

def s1Non (n : ℕ) : ℚ := 3 * cappedMassQ s1UpN (s1CapN ^ 12) (n / 12)
def s1Tail (n : ℕ) : ℚ := s1Non n + (s1UpJ - s1Lo ^ 12) ^ (n / 12)

def s1P0 : ℚ := 1 - (1 + s1Tail 36 / s1Lo ^ 36)⁻¹ ^ 2
def s1Q0 : ℚ := 1 - (s1CapJ ^ 72 + s1Tail 72)⁻¹ ^ 2

theorem s1_dominant_existence_and_initial_bounds :
    cappedMassQ s1UpJ (s1Lo ^ 12) 6 + s1Non 72 < 1 ∧
    s1Lo ^ 12 < s1UpJ ∧
    s1UpJ < 2 * s1Lo ^ 12 ∧
    47915 / 10 ^ 6 < s1P0 ∧ s1P0 < 47916 / 10 ^ 6 ∧
    181520 / 10 ^ 6 < s1Q0 ∧ s1Q0 < 181521 / 10 ^ 6 := by
  decide +kernel

/-- Six exact rounded coupled-update pairs from OpenAI `prop:seed2304`. -/
def s1P1 : ℚ := 151249 / 2500000
def s1Q1 : ℚ := 433453 / 2500000
def s1P2 : ℚ := 343303 / 5000000
def s1Q2 : ℚ := 1632381 / 10000000
def s1P3 : ℚ := 44601 / 625000
def s1Q3 : ℚ := 361773 / 2500000
def s1P4 : ℚ := 632939 / 10000000
def s1Q4 : ℚ := 1055161 / 10000000
def s1P5 : ℚ := 375793 / 10000000
def s1Q5 : ℚ := 445941 / 10000000
def s1P6 : ℚ := 84513 / 10000000
def s1Q6 : ℚ := 27493 / 5000000

theorem s1_six_rounded_updates_exact :
    ceilGrid7 (fQ (1 - (1 - s1P0) ^ 2 * (1 - s1Q0))) = s1P1 ∧
    ceilGrid7 (fQ (1 - (1 - s1Q0) ^ 2 * (1 - s1P1))) = s1Q1 ∧
    ceilGrid7 (fQ (1 - (1 - s1P1) ^ 2 * (1 - s1Q1))) = s1P2 ∧
    ceilGrid7 (fQ (1 - (1 - s1Q1) ^ 2 * (1 - s1P2))) = s1Q2 ∧
    ceilGrid7 (fQ (1 - (1 - s1P2) ^ 2 * (1 - s1Q2))) = s1P3 ∧
    ceilGrid7 (fQ (1 - (1 - s1Q2) ^ 2 * (1 - s1P3))) = s1Q3 ∧
    ceilGrid7 (fQ (1 - (1 - s1P3) ^ 2 * (1 - s1Q3))) = s1P4 ∧
    ceilGrid7 (fQ (1 - (1 - s1Q3) ^ 2 * (1 - s1P4))) = s1Q4 ∧
    ceilGrid7 (fQ (1 - (1 - s1P4) ^ 2 * (1 - s1Q4))) = s1P5 ∧
    ceilGrid7 (fQ (1 - (1 - s1Q4) ^ 2 * (1 - s1P5))) = s1Q5 ∧
    ceilGrid7 (fQ (1 - (1 - s1P5) ^ 2 * (1 - s1Q5))) = s1P6 ∧
    ceilGrid7 (fQ (1 - (1 - s1Q5) ^ 2 * (1 - s1P6))) = s1Q6 ∧
    s1P6 < 1 / 100 ∧ s1Q6 < 1 / 100 := by
  decide +kernel

/-- Machine-checked propagation of `Source 1` initial `(p₀, q₀)` through all 6 coupled rounds
from `(36, 49/4)` to `(2304, 784)` inside `PuritySystem1D`, returning the exact stronger
`prop:seed2304` rational ceilings `(s1P6 = 84513/10^7, s1Q6 = 27493/5000000)`. -/
theorem s1_six_rounds_to_2304_exact (sys : PuritySystem1D)
    (hS0 : 1 - sys.S 36 (49 / 4 : ℝ) ≤ (s1P0 : ℝ))
    (hT0 : 1 - sys.T 72 (49 / 4 : ℝ) ≤ (s1Q0 : ℝ)) :
    1 - sys.S 2304 (784 : ℝ) ≤ (s1P6 : ℝ) ∧
    1 - sys.T 4608 (784 : ℝ) ≤ (s1Q6 : ℝ) := by
  have hex := s1_six_rounded_updates_exact
  have hinit := s1_dominant_existence_and_initial_bounds
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
      rw [fQ_cast] at hcast
      push_cast at hcast
      exact hcast
    have hq'_R : purityUpdate (1 - (1 - (q : ℝ)) ^ 2 * (1 - (p' : ℝ))) ≤ (q' : ℝ) := by
      have hcast : ((fQ (1 - (1 - q) ^ 2 * (1 - p')) : ℚ) : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'_le
      rw [fQ_cast] at hcast
      push_cast at hcast
      exact hcast
    exact sys.rounded_coupled_update hn h4 hb
      (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq0) (by exact_mod_cast hq1)
      (by exact_mod_cast hp'1) hS hT hp'_R hq'_R
  have r1 := step (n := 36) (b := 49 / 4) ⟨18, by omega⟩ (by omega) (by norm_num)
    (by linarith [hinit.2.2.2.1]) (by linarith [hinit.2.2.2.2.1])
    (by linarith [hinit.2.2.2.2.2.1]) (by linarith [hinit.2.2.2.2.2.2])
    (by unfold s1P1; norm_num) hex.1 hex.2.1 hS0 hT0
  have r2 := step (n := 72) (b := 49 / 2) ⟨36, by omega⟩ (by omega) (by norm_num)
    (by unfold s1P1; norm_num) (by unfold s1P1; norm_num)
    (by unfold s1Q1; norm_num) (by unfold s1Q1; norm_num)
    (by unfold s1P2; norm_num) hex.2.2.1 hex.2.2.2.1
    (by convert r1.1 using 2 <;> norm_num) (by convert r1.2 using 2 <;> norm_num)
  have r3 := step (n := 144) (b := 49) ⟨72, by omega⟩ (by omega) (by norm_num)
    (by unfold s1P2; norm_num) (by unfold s1P2; norm_num)
    (by unfold s1Q2; norm_num) (by unfold s1Q2; norm_num)
    (by unfold s1P3; norm_num) hex.2.2.2.2.1 hex.2.2.2.2.2.1
    (by convert r2.1 using 2 <;> norm_num) (by convert r2.2 using 2 <;> norm_num)
  have r4 := step (n := 288) (b := 98) ⟨144, by omega⟩ (by omega) (by norm_num)
    (by unfold s1P3; norm_num) (by unfold s1P3; norm_num)
    (by unfold s1Q3; norm_num) (by unfold s1Q3; norm_num)
    (by unfold s1P4; norm_num) hex.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.1
    (by convert r3.1 using 2 <;> norm_num) (by convert r3.2 using 2 <;> norm_num)
  have r5 := step (n := 576) (b := 196) ⟨288, by omega⟩ (by omega) (by norm_num)
    (by unfold s1P4; norm_num) (by unfold s1P4; norm_num)
    (by unfold s1Q4; norm_num) (by unfold s1Q4; norm_num)
    (by unfold s1P5; norm_num) hex.2.2.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.2.2.1
    (by convert r4.1 using 2 <;> norm_num) (by convert r4.2 using 2 <;> norm_num)
  have r6 := step (n := 1152) (b := 392) ⟨576, by omega⟩ (by omega) (by norm_num)
    (by unfold s1P5; norm_num) (by unfold s1P5; norm_num)
    (by unfold s1Q5; norm_num) (by unfold s1Q5; norm_num)
    (by unfold s1P6; norm_num) hex.2.2.2.2.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.2.2.2.2.1
    (by convert r5.1 using 2 <;> norm_num) (by convert r5.2 using 2 <;> norm_num)
  constructor
  · convert r6.1 using 2 <;> norm_num
  · convert r6.2 using 2 <;> norm_num

/-- Machine-checked propagation of `Source 1` initial `(p₀, q₀)` through all 6 coupled rounds
from `(36, 49/4)` to `(2304, 784)` inside `PuritySystem1D` (`≤ 1/100` reseeding bound)! -/
theorem s1_six_rounds_to_2304 (sys : PuritySystem1D)
    (hS0 : 1 - sys.S 36 (49 / 4 : ℝ) ≤ (s1P0 : ℝ))
    (hT0 : 1 - sys.T 72 (49 / 4 : ℝ) ≤ (s1Q0 : ℝ)) :
    1 - sys.S 2304 (784 : ℝ) ≤ (1 / 100 : ℝ) ∧
    1 - sys.T 4608 (784 : ℝ) ≤ (1 / 100 : ℝ) := by
  have hex := s1_six_rounds_to_2304_exact sys hS0 hT0
  have hp6 : (s1P6 : ℝ) < (1 / 100 : ℝ) := by unfold s1P6; norm_num
  have hq6 : (s1Q6 : ℝ) < (1 / 100 : ℝ) := by unfold s1Q6; norm_num
  exact ⟨by linarith [hex.1], by linarith [hex.2]⟩

/-! ## Source 2 (`b₀ = 21/2 → b = 105/4`, length 60 & 120 initialization) -/

def s2I (z p c : ℚ) : ℚ := (z + 3 * p + 8 * c) / 12
def s2O (z p c : ℚ) : ℚ := (z + 3 * p - 4 * c) / 12
def s2N (z p : ℚ) : ℚ := (z - p) / 4

def s2Eps : ℚ := 1 / 100000
def s2U : ℚ := 100245 / 100000
def s2V : ℚ := 88643 / 100000
def s2mI : ℚ := 1042655 / 10 ^ 6
def s2mO : ℚ := 40041 / 10 ^ 6
def s2mN : ℚ := 401625 / 10 ^ 6

def s2D : ℚ := 1450 / 1000
def s2E : ℚ := 1202 / 1000
def s2Ti : ℚ := 1225 / 1000
def s2T0 : ℚ := 1264 / 1000
def s2Rq : ℚ := 684 / 10000

def s2R (t : ℚ) : ℚ :=
  let eval (x y : ℚ) : ℚ := x ^ 2 + y ^ 2 / 2 + (s2D - t - x - y) ^ 2 / 3
  max (max (eval 0 0) (eval (s2Ti - t) 0))
      (max (eval (s2Ti - t) (s2T0 - s2Ti)) (eval 0 (s2T0 - t)))

theorem s2_all_scalar_initializations_exact :
    let z6 : ℚ := 8945303 / 10 ^ 6; let p6 : ℚ := 346734 / 10 ^ 6; let c6 : ℚ := 939987 / 10 ^ 6
    let z8 : ℚ := 3741281 / 10 ^ 6; let p8 : ℚ := 567167 / 10 ^ 6; let c8 : ℚ := 984108 / 10 ^ 6
    let z10 : ℚ := 2327547 / 10 ^ 6; let p10 : ℚ := 721090 / 10 ^ 6; let c10 : ℚ := 1002613 / 10 ^ 6
    let I6 := s2I z6 p6 c6; let I8 := s2I z8 p8 c8; let I10 := s2I z10 p10 c10
    let O10 := s2O z10 p10 c10
    let N6 := s2N z6 p6; let N8 := s2N z8 p8; let N10 := s2N z10 p10
    let A30 := s2U ^ 30 + (s2mI - s2U ^ 10) ^ 3
    let B30 := s2mO ^ 3
    let C30 := s2V ^ 30 + (s2mN - s2V ^ 10) ^ 3
    let A120 := s2U ^ 120 + (s2mI - s2U ^ 10) ^ 12
    let B120 := s2mO ^ 12
    let C120 := s2V ^ 120 + (s2mN - s2V ^ 10) ^ 12
    let m := A30 + 2 * B30 + 3 * C30
    let p := A30 + 2 * B30
    let q := A120 + 2 * B120 + 3 * C120
    I10 + s2Eps < s2mI ∧ O10 + s2Eps < s2mO ∧ N10 + s2Eps < s2mN ∧
    s2U ^ 10 < s2mI ∧ s2mI < 2 * s2U ^ 10 ∧
    s2V ^ 10 < s2mN ∧ s2mN < 2 * s2V ^ 10 ∧
    (4 * I6 - 40 * I8 + 100 * I10 + 144 * s2Eps) < s2U ^ 6 * (-2 + 10 * s2U ^ 2) ^ 2 ∧
    (625 * N6 - 5000 * N8 + 10000 * N10 + 15625 * s2Eps) < s2V ^ 6 * (-25 + 100 * s2V ^ 2) ^ 2 ∧
    m ^ 5 < s2D ^ 2 ∧ p ^ 5 < s2E ^ 2 ∧
    1 ≤ q ∧ (q - 1) ^ 5 < s2Rq ^ 2 ∧
    (s2D + 11 * s2E) / 12 ≤ s2Ti ∧ (s2D + 3 * s2E) / 4 ≤ s2T0 ∧
    s2D * (88 / 100 : ℚ) ^ 3 < 1 ∧ s2D < 2 * (88 / 100 : ℚ) ∧
    (99 / 100 : ℚ) ^ 4 + s2R (88 / 100) ^ 2 < 1 ∧
    (998 / 1000 : ℚ) ^ 4 + s2R (99 / 100) ^ 2 < 1 ∧
    (7 / 8 : ℚ) < (1 + s2R (998 / 1000) / (998 / 1000 : ℚ) ^ 2)⁻¹ ^ 2 ∧
    (7 / 8 : ℚ) < (1 + s2Rq)⁻¹ ^ 2 := by
  decide +kernel

/-! ## Both Parameter Rows Checked in Exact `ℚ` and Lifted to `ℝ` -/

theorem parameter_row_source1_exact :
    GQ (1 / 100) < 5 ∧
    (5 : ℚ) * (1 / 100) = 1 / 20 ∧
    (3 : ℚ) < 5 * (1 - 3 * (1 / 100)) := by
  decide +kernel

theorem parameter_row_source2_exact :
    GQ (1 / 8) = 913952 / 117649 ∧
    GQ (1 / 8) < 79 / 10 ∧
    (79 / 10 : ℚ) * (1 / 8) = 79 / 80 ∧
    (3 : ℚ) < (79 / 10) * (1 - 3 * (1 / 8)) := by
  decide +kernel

/-- **Machine-Checked Haldane Gap Deduction from Seed `(36, 49/4)` (Source 1, `L ≥ 2304`)**:
connects the 6-round exact rational audit directly to `uniform_gap_from_purities`
to yield `γ_L > log(20) / 784` for every even `L ≥ 2304` (conditional on the seed purities
`hS36`, `hT72` and the transfer/interpolation hypotheses `sys`, `hInterp`). -/
theorem haldane_gap_source1_from_initial_36
    (sys : PuritySystem1D)
    (hInterp : ∀ (n L : ℕ) (b : ℝ), Even n → 4 ≤ n → Even L → n ≤ L → L ≤ 2 * n → 0 < b →
      sys.Z L b ≤ sys.Z n b ^ ((L : ℝ) / (n : ℝ)) ∧
      sys.Z (2 * n) (2 * b) ^ ((L : ℝ) / (2 * (n : ℝ))) ≤ sys.Z L (2 * b))
    (hS36 : 1 - sys.S 36 (49 / 4 : ℝ) ≤ (s1P0 : ℝ))
    (hT72 : 1 - sys.T 72 (49 / 4 : ℝ) ≤ (s1Q0 : ℝ))
    {L d : ℕ} (hL_even : Even L) (hL_ge : 2304 ≤ L)
    (E : Fin d → ℝ) (k₀ : Fin d) (hmin : ∀ k, E k₀ ≤ E k)
    (hGibbs : ∀ b, 0 < b → sys.Z L b = ∑ k : Fin d, Real.exp (-b * E k)) :
    (∀ k : Fin d, E k = E k₀ → k = k₀) ∧
    (∀ k : Fin d, k ≠ k₀ → Real.log 20 / 784 < E k - E k₀) := by
  have h2304 := s1_six_rounds_to_2304 sys hS36 hT72
  have hG : bootstrapCoeff (1 / 100 : ℝ) ≤ 5 := by
    have hq : ((GQ (1 / 100) : ℚ) : ℝ) < (5 : ℝ) := by exact_mod_cast parameter_row_source1_exact.1
    rw [GQ_cast] at hq
    push_cast at hq
    exact hq.le
  have hres := uniform_gap_from_purities sys hInterp
    (n₀ := 2304) (b₀ := 784) (u₀ := 1 / 100) (C := 5)
    ⟨1152, by omega⟩ (by omega) (by norm_num)
    (by norm_num) (by norm_num) hG (by norm_num) (by norm_num)
    h2304.1 (by convert h2304.2 using 2) hL_even hL_ge E k₀ hmin hGibbs
  refine ⟨hres.1, fun k hne => ?_⟩
  have h := hres.2 k hne
  have h20 : (1 : ℝ) / (5 * (1 / 100 : ℝ)) = 20 := by norm_num
  rwa [h20] at h

/-- **Machine-Checked Haldane Gap Deduction from Seed `(60, 105/4)` (Source 2, `L ≥ 60`)**:
connects `Source 2` exact parameter verification directly to `uniform_gap_from_purities`
to yield `γ_L > (4/105) * log(80/79)` for every even `L ≥ 60` (conditional on the seed purities
`hS60`, `hT120` and the transfer/interpolation hypotheses `sys`, `hInterp`). -/
theorem haldane_gap_source2_from_initial_60
    (sys : PuritySystem1D)
    (hInterp : ∀ (n L : ℕ) (b : ℝ), Even n → 4 ≤ n → Even L → n ≤ L → L ≤ 2 * n → 0 < b →
      sys.Z L b ≤ sys.Z n b ^ ((L : ℝ) / (n : ℝ)) ∧
      sys.Z (2 * n) (2 * b) ^ ((L : ℝ) / (2 * (n : ℝ))) ≤ sys.Z L (2 * b))
    (hS60 : 1 - sys.S 60 (105 / 4 : ℝ) ≤ (1 / 8 : ℝ))
    (hT120 : 1 - sys.T 120 (105 / 4 : ℝ) ≤ (1 / 8 : ℝ))
    {L d : ℕ} (hL_even : Even L) (hL_ge : 60 ≤ L)
    (E : Fin d → ℝ) (k₀ : Fin d) (hmin : ∀ k, E k₀ ≤ E k)
    (hGibbs : ∀ b, 0 < b → sys.Z L b = ∑ k : Fin d, Real.exp (-b * E k)) :
    (∀ k : Fin d, E k = E k₀ → k = k₀) ∧
    (∀ k : Fin d, k ≠ k₀ → (4 / 105 : ℝ) * Real.log (80 / 79) < E k - E k₀) := by
  have hG : bootstrapCoeff (1 / 8 : ℝ) ≤ 79 / 10 := by
    have hq : ((GQ (1 / 8) : ℚ) : ℝ) < ((79 / 10 : ℚ) : ℝ) := by
      exact_mod_cast parameter_row_source2_exact.2.1
    rw [GQ_cast] at hq
    push_cast at hq
    exact hq.le
  have hres := uniform_gap_from_purities sys hInterp
    (n₀ := 60) (b₀ := 105 / 4) (u₀ := 1 / 8) (C := 79 / 10)
    ⟨30, by omega⟩ (by omega) (by norm_num)
    (by norm_num) (by norm_num) hG (by norm_num) (by norm_num)
    hS60 (by convert hT120 using 2) hL_even hL_ge E k₀ hmin hGibbs
  refine ⟨hres.1, fun k hne => ?_⟩
  have h := hres.2 k hne
  have h80 : (1 : ℝ) / ((79 / 10 : ℝ) * (1 / 8 : ℝ)) = 80 / 79 := by norm_num
  rw [h80] at h
  linarith [show Real.log (80 / 79) / (105 / 4 : ℝ) = (4 / 105 : ℝ) * Real.log (80 / 79) by ring]

end PurityBootstrap.ExactCertificates
