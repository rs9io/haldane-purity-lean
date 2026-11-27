import PurityBootstrap.Basic
import PurityBootstrap.OneD

/-!
# Tarun Grover's Higher-Dimensional Purity Bootstrap (`arXiv:2611.07400`, Sec. II)

Lean 4 formalization of Tarun Grover's higher-dimensional purity bootstrap:
1. **Universal `d`-dimensional scalar quadratic contraction (`a ≥ 3`, `u ≤ 1 / (2 a^2)`)**:
   proves `purityUpdate (1 - (1 - u)^a) ≤ a^2 * u^2` (`general_dim_quadratic_contraction`).
2. **2D square lattice (`a = 7`, `u ≤ 1/98`, `u_{j+1} = 49 u_j^2`)**:
   coupled 3-purity update `(S_x, S_y, T)` from `(L, L, β)` to `(2L, 2L, 2β)`,
   starting either from three individual high purities (`uniform_gap_2d_from_three`) or from the
   stronger single cube ratio `Q(L, β) = Z(2L, 2L, 2β) / Z(L, L, β)^8 ≥ 97/98`
   (`uniform_gap_2d`, proved as a corollary), plus intermediate even-square interpolation
   `T(ℓ, ℓ, β_j) ≥ 1 - 7 u_j` and uniform 2D spectral gap `Δ_ℓ > log 2 / β₀` for every even
   `ℓ ≥ L₀` (conditional on `PuritySystem2D` and square interpolation `hInterp`).
-/

namespace PurityBootstrap.HigherDim

open scoped BigOperators
open Real

/-- Generalized Bernoulli inequality: `1 - a * u ≤ (1 - u)^a` for `u ∈ [0, 1]` and `a : ℕ`. -/
lemma one_sub_mul_le_pow {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (a : ℕ) :
    1 - (a : ℝ) * u ≤ (1 - u) ^ a := by
  induction a with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [pow_succ]
    have h1mu : 0 ≤ 1 - u := by linarith
    have hmul : (1 - (k : ℝ) * u) * (1 - u) ≤ (1 - u) ^ k * (1 - u) :=
      mul_le_mul_of_nonneg_right ih h1mu
    have hku : 0 ≤ (k : ℝ) * u ^ 2 := by positivity
    nlinarith

/-- Universal `d`-dimensional quadratic contraction inequality (`arXiv:2611.07400` Sec. II):
for any integer `a ≥ 3` (in particular `a = 2^(d+1) - 1` for `d ≥ 1`) and `0 ≤ u ≤ 1 / (2 a^2)`:
`purityUpdate (1 - (1 - u)^a) ≤ a^2 * u^2`. -/
theorem general_dim_quadratic_contraction {a : ℕ} (ha : 3 ≤ a) {u : ℝ}
    (hu0 : 0 ≤ u) (hu_le : u ≤ 1 / (2 * (a : ℝ) ^ 2)) :
    purityUpdate (1 - (1 - u) ^ a) ≤ (a : ℝ) ^ 2 * u ^ 2 := by
  have ha_real : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha_pos : (0 : ℝ) < a := by linarith
  have ha2_pos : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
  have hau_le : (a : ℝ) * u ≤ 1 / (2 * (a : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hu_le ha_pos.le
    calc (a : ℝ) * u ≤ (a : ℝ) * (1 / (2 * (a : ℝ) ^ 2)) := this
      _ = 1 / (2 * (a : ℝ)) := by field_simp [ha_pos.ne']
  have hau_le_sixth : (a : ℝ) * u ≤ 1 / 6 := by
    have : 1 / (2 * (a : ℝ)) ≤ 1 / 6 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hu_le1 : u ≤ 1 := by nlinarith
  have hbern : 1 - (a : ℝ) * u ≤ (1 - u) ^ a := one_sub_mul_le_pow hu0 hu_le1 a
  have hpow_le1 : (1 - u) ^ a ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hmono : purityUpdate (1 - (1 - u) ^ a) ≤ purityUpdate ((a : ℝ) * u) :=
    purityUpdate_mono (by linarith) (by linarith) (by linarith)
  refine hmono.trans ?_
  unfold purityUpdate
  have hden_ge1 : (1 : ℝ) ≤ 2 * (1 - (a : ℝ) * u) ^ 2 := by nlinarith
  have hnum_nn : 0 ≤ ((a : ℝ) * u) ^ 2 := sq_nonneg _
  calc ((a : ℝ) * u) ^ 2 / (2 * (1 - (a : ℝ) * u) ^ 2)
      ≤ ((a : ℝ) * u) ^ 2 / 1 := div_le_div_of_nonneg_left hnum_nn zero_lt_one hden_ge1
    _ = (a : ℝ) ^ 2 * u ^ 2 := by ring

/-- Abstract 2D square/rectangular purity system (`arXiv:2611.07400` Sec. II & App. A.2–A.3). -/
structure PuritySystem2D where
  Z : ℕ → ℕ → ℝ → ℝ
  Z_pos : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b → 0 < Z lx ly b
  Sx_le_one : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b →
    Z (2 * lx) ly b / (Z lx ly b) ^ 2 ≤ 1
  Sy_le_one : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b →
    Z lx (2 * ly) b / (Z lx ly b) ^ 2 ≤ 1
  T_le_one : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b →
    Z lx ly (2 * b) / (Z lx ly b) ^ 2 ≤ 1
  Sx_square : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b →
    1 - Z (4 * lx) ly b / (Z (2 * lx) ly b) ^ 2 ≤
      purityUpdate (1 - Z (2 * lx) ly b / (Z lx ly b) ^ 2)
  Sy_square : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b →
    1 - Z lx (4 * ly) b / (Z lx (2 * ly) b) ^ 2 ≤
      purityUpdate (1 - Z lx (2 * ly) b / (Z lx ly b) ^ 2)
  T_square : ∀ lx ly b, Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b →
    1 - Z lx ly (4 * b) / (Z lx ly (2 * b)) ^ 2 ≤
      purityUpdate (1 - Z lx ly (2 * b) / (Z lx ly b) ^ 2)

namespace PuritySystem2D

noncomputable def Sx (sys : PuritySystem2D) (lx ly : ℕ) (b : ℝ) : ℝ :=
  sys.Z (2 * lx) ly b / (sys.Z lx ly b) ^ 2

noncomputable def Sy (sys : PuritySystem2D) (lx ly : ℕ) (b : ℝ) : ℝ :=
  sys.Z lx (2 * ly) b / (sys.Z lx ly b) ^ 2

noncomputable def T (sys : PuritySystem2D) (lx ly : ℕ) (b : ℝ) : ℝ :=
  sys.Z lx ly (2 * b) / (sys.Z lx ly b) ^ 2

/-- Single 2D finite-size cube ratio `Q(L, b) = Z(2L, 2L, 2b) / Z(L, L, b)^8`
(`arXiv:2611.07400` Eq. `eq:2d-cube`). -/
noncomputable def Q (sys : PuritySystem2D) (L : ℕ) (b : ℝ) : ℝ :=
  sys.Z (2 * L) (2 * L) (2 * b) / (sys.Z L L b) ^ 8

/-- Exact 2D cube factorization: `Q(L, b) = Sx(L, L, b)^4 * Sy(2L, L, b)^2 * T(2L, 2L, b)`. -/
theorem cube_factorization (sys : PuritySystem2D) {L : ℕ} {b : ℝ}
    (hL : Even L) (h4 : 2 ≤ L) (hb : 0 < b) :
    sys.Q L b = sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 * sys.T (2 * L) (2 * L) b := by
  unfold Q Sx Sy T
  have h2L : Even (2 * L) := even_two_mul L
  have h1 : sys.Z L L b ≠ 0 := (sys.Z_pos L L b hL h4 hL h4 hb).ne'
  have h2 : sys.Z (2 * L) L b ≠ 0 := (sys.Z_pos (2 * L) L b h2L (by omega) hL h4 hb).ne'
  have h3 : sys.Z (2 * L) (2 * L) b ≠ 0 :=
    (sys.Z_pos (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb).ne'
  field_simp [h1, h2, h3]

/-- Checking the single cube ratio `Q(L, b) ≥ 1 - u` implies all three starting purities
`Sx(L, L, b) ≥ 1 - u`, `Sy(2L, L, b) ≥ 1 - u`, `T(2L, 2L, b) ≥ 1 - u`! -/
theorem cube_implies_three_purities (sys : PuritySystem2D) {L : ℕ} {b u : ℝ}
    (hL : Even L) (h4 : 2 ≤ L) (hb : 0 < b)
    (hQ : 1 - u ≤ sys.Q L b) :
    1 - sys.Sx L L b ≤ u ∧ 1 - sys.Sy (2 * L) L b ≤ u ∧ 1 - sys.T (2 * L) (2 * L) b ≤ u := by
  have h2L : Even (2 * L) := even_two_mul L
  have hSx_pos : 0 < sys.Sx L L b :=
    div_pos (sys.Z_pos (2 * L) L b h2L (by omega) hL h4 hb)
      (pow_pos (sys.Z_pos L L b hL h4 hL h4 hb) 2)
  have hSy_pos : 0 < sys.Sy (2 * L) L b :=
    div_pos (sys.Z_pos (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb)
      (pow_pos (sys.Z_pos (2 * L) L b h2L (by omega) hL h4 hb) 2)
  have hT_pos : 0 < sys.T (2 * L) (2 * L) b :=
    div_pos (sys.Z_pos (2 * L) (2 * L) (2 * b) h2L (by omega) h2L (by omega) (by linarith))
      (pow_pos (sys.Z_pos (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb) 2)
  have hSx1 : sys.Sx L L b ≤ 1 := sys.Sx_le_one L L b hL h4 hL h4 hb
  have hSy1 : sys.Sy (2 * L) L b ≤ 1 := sys.Sy_le_one (2 * L) L b h2L (by omega) hL h4 hb
  have hT1 : sys.T (2 * L) (2 * L) b ≤ 1 := sys.T_le_one (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb
  rw [sys.cube_factorization hL h4 hb] at hQ
  have hSx4_le : sys.Sx L L b ^ 4 ≤ sys.Sx L L b := by
    have h2 : sys.Sx L L b ^ 2 ≤ sys.Sx L L b := by nlinarith
    have h3 : sys.Sx L L b ^ 3 ≤ sys.Sx L L b := by nlinarith
    nlinarith
  have hSy2_le : sys.Sy (2 * L) L b ^ 2 ≤ sys.Sy (2 * L) L b := by nlinarith
  have hQ_le_Sx : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 * sys.T (2 * L) (2 * L) b ≤ sys.Sx L L b := by
    have hSy2_1 : sys.Sy (2 * L) L b ^ 2 ≤ 1 := by nlinarith
    have h1 : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 ≤ sys.Sx L L b ^ 4 := by
      nlinarith [pow_nonneg hSx_pos.le 4]
    have h2 : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 * sys.T (2 * L) (2 * L) b ≤
        sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 := by
      nlinarith [mul_nonneg (pow_nonneg hSx_pos.le 4) (sq_nonneg (sys.Sy (2 * L) L b))]
    linarith
  have hQ_le_Sy : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 * sys.T (2 * L) (2 * L) b ≤
      sys.Sy (2 * L) L b := by
    have hSx4_1 : sys.Sx L L b ^ 4 ≤ 1 := pow_le_one₀ hSx_pos.le hSx1
    have h1 : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 ≤ sys.Sy (2 * L) L b ^ 2 := by
      nlinarith [sq_nonneg (sys.Sy (2 * L) L b)]
    have h2 : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 * sys.T (2 * L) (2 * L) b ≤
        sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 := by
      nlinarith [mul_nonneg (pow_nonneg hSx_pos.le 4) (sq_nonneg (sys.Sy (2 * L) L b))]
    linarith
  have hQ_le_T : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 * sys.T (2 * L) (2 * L) b ≤
      sys.T (2 * L) (2 * L) b := by
    have hSx4_1 : sys.Sx L L b ^ 4 ≤ 1 := pow_le_one₀ hSx_pos.le hSx1
    have hSy2_1 : sys.Sy (2 * L) L b ^ 2 ≤ 1 := by nlinarith
    have hprod1 : sys.Sx L L b ^ 4 * sys.Sy (2 * L) L b ^ 2 ≤ 1 := by
      nlinarith [pow_nonneg hSx_pos.le 4]
    nlinarith
  exact ⟨by linarith, by linarith, by linarith⟩

/-- One full 2D doubling round (`arXiv:2611.07400` Eq. `eq:2d-round`, App. A.2):
if `Sx(L, L, b), Sy(2L, L, b), T(2L, 2L, b) ≥ 1 - u` with `0 ≤ u ≤ 1/98`, then
`Sx(2L, 2L, 2b), Sy(4L, 2L, 2b), T(4L, 4L, 2b) ≥ 1 - 49 u^2`. -/
theorem doubling_round_2d (sys : PuritySystem2D) {L : ℕ} {b u : ℝ}
    (hL : Even L) (h4 : 2 ≤ L) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu_le : u ≤ 1 / 98)
    (hSx : 1 - sys.Sx L L b ≤ u)
    (hSy : 1 - sys.Sy (2 * L) L b ≤ u)
    (hT : 1 - sys.T (2 * L) (2 * L) b ≤ u) :
    1 - sys.Sx (2 * L) (2 * L) (2 * b) ≤ 49 * u ^ 2 ∧
    1 - sys.Sy (4 * L) (2 * L) (2 * b) ≤ 49 * u ^ 2 ∧
    1 - sys.T (4 * L) (4 * L) (2 * b) ≤ 49 * u ^ 2 := by
  have h2L : Even (2 * L) := even_two_mul L
  have h4L : Even (4 * L) := ⟨2 * L, by omega⟩
  have h2b : 0 < 2 * b := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have h49u2_le_u : 49 * u ^ 2 ≤ u := by nlinarith
  have hquad : purityUpdate (1 - (1 - u) ^ 7) ≤ 49 * u ^ 2 := by
    have := general_dim_quadratic_contraction (a := 7) (by omega) hu0 (by norm_num; linarith)
    norm_num at this
    exact this
  -- Helper: doubling upper bounds Z(2lx, ly, b) ≤ Z(lx, ly, b)^2 etc.
  have hZx_le : ∀ lx ly b', Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b' →
      sys.Z (2 * lx) ly b' ≤ sys.Z lx ly b' ^ 2 := fun lx ly b' hlx h4x hly h4y hb' =>
    (div_le_one (pow_pos (sys.Z_pos lx ly b' hlx h4x hly h4y hb') 2)).mp
      (sys.Sx_le_one lx ly b' hlx h4x hly h4y hb')
  have hZy_le : ∀ lx ly b', Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b' →
      sys.Z lx (2 * ly) b' ≤ sys.Z lx ly b' ^ 2 := fun lx ly b' hlx h4x hly h4y hb' =>
    (div_le_one (pow_pos (sys.Z_pos lx ly b' hlx h4x hly h4y hb') 2)).mp
      (sys.Sy_le_one lx ly b' hlx h4x hly h4y hb')
  have hZt_le : ∀ lx ly b', Even lx → 2 ≤ lx → Even ly → 2 ≤ ly → 0 < b' →
      sys.Z lx ly (2 * b') ≤ sys.Z lx ly b' ^ 2 := fun lx ly b' hlx h4x hly h4y hb' =>
    (div_le_one (pow_pos (sys.Z_pos lx ly b' hlx h4x hly h4y hb') 2)).mp
      (sys.T_le_one lx ly b' hlx h4x hly h4y hb')
  -- Step 1: Sx(2L, 2L, 2b)
  have hSx_new : 1 - sys.Sx (2 * L) (2 * L) (2 * b) ≤ 49 * u ^ 2 := by
    have hZ_den : sys.Z L (2 * L) (2 * b) ≤ sys.Z L L b ^ 4 := by
      have h1 := hZt_le L (2 * L) b hL h4 h2L (by omega) hb
      have h2 := hZy_le L L b hL h4 hL h4 hb
      have hpos := (sys.Z_pos L (2 * L) b hL h4 h2L (by omega) hb).le
      calc sys.Z L (2 * L) (2 * b) ≤ sys.Z L (2 * L) b ^ 2 := h1
        _ ≤ (sys.Z L L b ^ 2) ^ 2 := by nlinarith
        _ = sys.Z L L b ^ 4 := by ring
    have hSx_mid : (1 - u) ^ 7 ≤ sys.Sx L (2 * L) (2 * b) := by
      have hQ_ge : (1 - u) ^ 7 ≤ sys.Q L b := by
        rw [sys.cube_factorization hL h4 hb]
        have h1 : (1 - u) ^ 4 ≤ sys.Sx L L b ^ 4 := pow_le_pow_left₀ h1mu.le (by linarith) 4
        have h2 : (1 - u) ^ 2 ≤ sys.Sy (2 * L) L b ^ 2 := pow_le_pow_left₀ h1mu.le (by linarith) 2
        have h3 : 1 - u ≤ sys.T (2 * L) (2 * L) b := by linarith
        have h12 := mul_le_mul h1 h2 (pow_nonneg h1mu.le 2) (pow_nonneg (by linarith) 4)
        have h123 := mul_le_mul h12 h3 h1mu.le (mul_nonneg (pow_nonneg (by linarith) 4) (pow_nonneg (by linarith) 2))
        calc (1 - u) ^ 7 = (1 - u) ^ 4 * (1 - u) ^ 2 * (1 - u) := by ring
          _ ≤ _ := h123
      have hQ_le : sys.Q L b ≤ sys.Sx L (2 * L) (2 * b) := by
        unfold Q Sx
        have hden_sq : sys.Z L (2 * L) (2 * b) ^ 2 ≤ sys.Z L L b ^ 8 := by
          have hpos := (sys.Z_pos L (2 * L) (2 * b) hL h4 h2L (by omega) h2b).le
          calc sys.Z L (2 * L) (2 * b) ^ 2 ≤ (sys.Z L L b ^ 4) ^ 2 := by nlinarith
            _ = sys.Z L L b ^ 8 := by ring
        exact div_le_div_of_nonneg_left
          (sys.Z_pos (2 * L) (2 * L) (2 * b) h2L (by omega) h2L (by omega) h2b).le
          (pow_pos (sys.Z_pos L (2 * L) (2 * b) hL h4 h2L (by omega) h2b) 2) hden_sq
      linarith
    have hsq := sys.Sx_square L (2 * L) (2 * b) hL h4 h2L (by omega) h2b
    have hdef : sys.Sx (2 * L) (2 * L) (2 * b) =
        sys.Z (4 * L) (2 * L) (2 * b) / sys.Z (2 * L) (2 * L) (2 * b) ^ 2 := by
      unfold Sx; congr 2; omega
    rw [hdef]
    have hle1 : sys.Sx L (2 * L) (2 * b) ≤ 1 := sys.Sx_le_one L (2 * L) (2 * b) hL h4 h2L (by omega) h2b
    have hmono : purityUpdate (1 - sys.Sx L (2 * L) (2 * b)) ≤
        purityUpdate (1 - (1 - u) ^ 7) :=
      purityUpdate_mono (by linarith) (by linarith) (by linarith [pow_pos h1mu 7])
    exact hsq.trans (hmono.trans hquad)
  -- Step 2: Sy(4L, 2L, 2b)
  have hSy_new : 1 - sys.Sy (4 * L) (2 * L) (2 * b) ≤ 49 * u ^ 2 := by
    have hZ_den : sys.Z (4 * L) L (2 * b) ≤ sys.Z (2 * L) L b ^ 4 := by
      have h1 := hZx_le (2 * L) L (2 * b) h2L (by omega) hL h4 h2b
      have h2 := hZt_le (2 * L) L b h2L (by omega) hL h4 hb
      have hpos := (sys.Z_pos (2 * L) L (2 * b) h2L (by omega) hL h4 h2b).le
      have hmul : 2 * (2 * L) = 4 * L := by omega
      rw [hmul] at h1
      calc sys.Z (4 * L) L (2 * b) ≤ sys.Z (2 * L) L (2 * b) ^ 2 := h1
        _ ≤ (sys.Z (2 * L) L b ^ 2) ^ 2 := by nlinarith
        _ = sys.Z (2 * L) L b ^ 4 := by ring
    have hSy_mid : (1 - u) ^ 7 ≤ sys.Sy (4 * L) L (2 * b) := by
      have hfac : sys.Z (4 * L) (2 * L) (2 * b) / sys.Z (2 * L) L b ^ 8 =
          sys.Sy (2 * L) L b ^ 4 * sys.T (2 * L) (2 * L) b ^ 2 * sys.Sx (2 * L) (2 * L) (2 * b) := by
        unfold Sx Sy T
        have h1 : sys.Z (2 * L) L b ≠ 0 := (sys.Z_pos (2 * L) L b h2L (by omega) hL h4 hb).ne'
        have h2 : sys.Z (2 * L) (2 * L) b ≠ 0 :=
          (sys.Z_pos (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb).ne'
        have h3 : sys.Z (2 * L) (2 * L) (2 * b) ≠ 0 :=
          (sys.Z_pos (2 * L) (2 * L) (2 * b) h2L (by omega) h2L (by omega) h2b).ne'
        have hmul : 2 * (2 * L) = 4 * L := by omega
        rw [hmul]
        field_simp [h1, h2, h3]
      have hprod : (1 - u) ^ 7 ≤ sys.Z (4 * L) (2 * L) (2 * b) / sys.Z (2 * L) L b ^ 8 := by
        rw [hfac]
        have h1 : (1 - u) ^ 4 ≤ sys.Sy (2 * L) L b ^ 4 := pow_le_pow_left₀ h1mu.le (by linarith) 4
        have h2 : (1 - u) ^ 2 ≤ sys.T (2 * L) (2 * L) b ^ 2 := pow_le_pow_left₀ h1mu.le (by linarith) 2
        have h3 : 1 - u ≤ sys.Sx (2 * L) (2 * L) (2 * b) := by linarith
        have h12 := mul_le_mul h1 h2 (pow_nonneg h1mu.le 2) (pow_nonneg (by linarith) 4)
        have h123 := mul_le_mul h12 h3 h1mu.le (mul_nonneg (pow_nonneg (by linarith) 4) (pow_nonneg (by linarith) 2))
        calc (1 - u) ^ 7 = (1 - u) ^ 4 * (1 - u) ^ 2 * (1 - u) := by ring
          _ ≤ _ := h123
      have hdiv : sys.Z (4 * L) (2 * L) (2 * b) / sys.Z (2 * L) L b ^ 8 ≤ sys.Sy (4 * L) L (2 * b) := by
        unfold Sy
        have hden_sq : sys.Z (4 * L) L (2 * b) ^ 2 ≤ sys.Z (2 * L) L b ^ 8 := by
          have hpos := (sys.Z_pos (4 * L) L (2 * b) h4L (by omega) hL h4 h2b).le
          calc sys.Z (4 * L) L (2 * b) ^ 2 ≤ (sys.Z (2 * L) L b ^ 4) ^ 2 := by nlinarith
            _ = sys.Z (2 * L) L b ^ 8 := by ring
        exact div_le_div_of_nonneg_left
          (sys.Z_pos (4 * L) (2 * L) (2 * b) h4L (by omega) h2L (by omega) h2b).le
          (pow_pos (sys.Z_pos (4 * L) L (2 * b) h4L (by omega) hL h4 h2b) 2) hden_sq
      linarith
    have hsq := sys.Sy_square (4 * L) L (2 * b) h4L (by omega) hL h4 h2b
    have hdef : sys.Sy (4 * L) (2 * L) (2 * b) =
        sys.Z (4 * L) (4 * L) (2 * b) / sys.Z (4 * L) (2 * L) (2 * b) ^ 2 := by
      unfold Sy; congr 2; omega
    rw [hdef]
    have hle1 : sys.Sy (4 * L) L (2 * b) ≤ 1 := sys.Sy_le_one (4 * L) L (2 * b) h4L (by omega) hL h4 h2b
    have hmono : purityUpdate (1 - sys.Sy (4 * L) L (2 * b)) ≤
        purityUpdate (1 - (1 - u) ^ 7) :=
      purityUpdate_mono (by linarith) (by linarith) (by linarith [pow_pos h1mu 7])
    exact hsq.trans (hmono.trans hquad)
  -- Step 3: T(4L, 4L, 2b)
  have hT_new : 1 - sys.T (4 * L) (4 * L) (2 * b) ≤ 49 * u ^ 2 := by
    have hZ_den : sys.Z (4 * L) (4 * L) b ≤ sys.Z (2 * L) (2 * L) b ^ 4 := by
      have h1 := hZy_le (4 * L) (2 * L) b h4L (by omega) h2L (by omega) hb
      have h2 := hZx_le (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb
      have hpos := (sys.Z_pos (4 * L) (2 * L) b h4L (by omega) h2L (by omega) hb).le
      have hmul : 2 * (2 * L) = 4 * L := by omega
      rw [hmul] at h1 h2
      calc sys.Z (4 * L) (4 * L) b ≤ sys.Z (4 * L) (2 * L) b ^ 2 := h1
        _ ≤ (sys.Z (2 * L) (2 * L) b ^ 2) ^ 2 := by nlinarith
        _ = sys.Z (2 * L) (2 * L) b ^ 4 := by ring
    have hT_mid : (1 - u) ^ 7 ≤ sys.T (4 * L) (4 * L) b := by
      have hfac : sys.Z (4 * L) (4 * L) (2 * b) / sys.Z (2 * L) (2 * L) b ^ 8 =
          sys.T (2 * L) (2 * L) b ^ 4 * sys.Sx (2 * L) (2 * L) (2 * b) ^ 2 *
          sys.Sy (4 * L) (2 * L) (2 * b) := by
        unfold Sx Sy T
        have h1 : sys.Z (2 * L) (2 * L) b ≠ 0 :=
          (sys.Z_pos (2 * L) (2 * L) b h2L (by omega) h2L (by omega) hb).ne'
        have h2 : sys.Z (2 * L) (2 * L) (2 * b) ≠ 0 :=
          (sys.Z_pos (2 * L) (2 * L) (2 * b) h2L (by omega) h2L (by omega) h2b).ne'
        have h3 : sys.Z (4 * L) (2 * L) (2 * b) ≠ 0 :=
          (sys.Z_pos (4 * L) (2 * L) (2 * b) h4L (by omega) h2L (by omega) h2b).ne'
        have hmul : 2 * (2 * L) = 4 * L := by omega
        rw [hmul]
        field_simp [h1, h2, h3]
      have hprod : (1 - u) ^ 7 ≤ sys.Z (4 * L) (4 * L) (2 * b) / sys.Z (2 * L) (2 * L) b ^ 8 := by
        rw [hfac]
        have h1 : (1 - u) ^ 4 ≤ sys.T (2 * L) (2 * L) b ^ 4 := pow_le_pow_left₀ h1mu.le (by linarith) 4
        have h2 : (1 - u) ^ 2 ≤ sys.Sx (2 * L) (2 * L) (2 * b) ^ 2 :=
          pow_le_pow_left₀ h1mu.le (by linarith) 2
        have h3 : 1 - u ≤ sys.Sy (4 * L) (2 * L) (2 * b) := by linarith
        have h12 := mul_le_mul h1 h2 (pow_nonneg h1mu.le 2) (pow_nonneg (by linarith) 4)
        have h123 := mul_le_mul h12 h3 h1mu.le (mul_nonneg (pow_nonneg (by linarith) 4) (pow_nonneg (by linarith) 2))
        calc (1 - u) ^ 7 = (1 - u) ^ 4 * (1 - u) ^ 2 * (1 - u) := by ring
          _ ≤ _ := h123
      have hdiv : sys.Z (4 * L) (4 * L) (2 * b) / sys.Z (2 * L) (2 * L) b ^ 8 ≤ sys.T (4 * L) (4 * L) b := by
        unfold T
        have hden_sq : sys.Z (4 * L) (4 * L) b ^ 2 ≤ sys.Z (2 * L) (2 * L) b ^ 8 := by
          have hpos := (sys.Z_pos (4 * L) (4 * L) b h4L (by omega) h4L (by omega) hb).le
          calc sys.Z (4 * L) (4 * L) b ^ 2 ≤ (sys.Z (2 * L) (2 * L) b ^ 4) ^ 2 := by nlinarith
            _ = sys.Z (2 * L) (2 * L) b ^ 8 := by ring
        exact div_le_div_of_nonneg_left
          (sys.Z_pos (4 * L) (4 * L) (2 * b) h4L (by omega) h4L (by omega) h2b).le
          (pow_pos (sys.Z_pos (4 * L) (4 * L) b h4L (by omega) h4L (by omega) hb) 2) hden_sq
      linarith
    have hsq := sys.T_square (4 * L) (4 * L) b h4L (by omega) h4L (by omega) hb
    have hdef : sys.T (4 * L) (4 * L) (2 * b) =
        sys.Z (4 * L) (4 * L) (4 * b) / sys.Z (4 * L) (4 * L) (2 * b) ^ 2 := by
      unfold T; congr 1; ring_nf
    rw [hdef]
    have hle1 : sys.T (4 * L) (4 * L) b ≤ 1 := sys.T_le_one (4 * L) (4 * L) b h4L (by omega) h4L (by omega) hb
    have hmono : purityUpdate (1 - sys.T (4 * L) (4 * L) b) ≤
        purityUpdate (1 - (1 - u) ^ 7) :=
      purityUpdate_mono (by linarith) (by linarith) (by linarith [pow_pos h1mu 7])
    exact hsq.trans (hmono.trans hquad)
  exact ⟨hSx_new, hSy_new, hT_new⟩

/-- Iterated 2D dyadic purity bounds starting directly from three individual high purities
(`arXiv:2611.07400` Eq. `eq:2d-error`):
`u_j = (1/49) * (49 u₀)^(2^j) ≤ (1/49) * 2^(-2^j)`. -/
theorem dyadic_purities_2d_from_three (sys : PuritySystem2D) {L₀ : ℕ} {b₀ u₀ : ℝ}
    (hL₀ : Even L₀) (h4 : 2 ≤ L₀) (hb₀ : 0 < b₀)
    (hu0_pos : 0 < u₀) (hu0_le : u₀ ≤ 1 / 98)
    (hSx0 : 1 - sys.Sx L₀ L₀ b₀ ≤ u₀)
    (hSy0 : 1 - sys.Sy (2 * L₀) L₀ b₀ ≤ u₀)
    (hT0 : 1 - sys.T (2 * L₀) (2 * L₀) b₀ ≤ u₀) :
    ∀ j : ℕ,
      1 - sys.Sx (2 ^ j * L₀) (2 ^ j * L₀) (2 ^ j * b₀) ≤ dyadicDefect 49 (49 * u₀) j ∧
      1 - sys.Sy (2 * (2 ^ j * L₀)) (2 ^ j * L₀) (2 ^ j * b₀) ≤ dyadicDefect 49 (49 * u₀) j ∧
      1 - sys.T (2 * (2 ^ j * L₀)) (2 * (2 ^ j * L₀)) (2 ^ j * b₀) ≤ dyadicDefect 49 (49 * u₀) j := by
  intro j
  induction j with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_one]
    rw [dyadicDefect_zero (by norm_num)]
    exact ⟨hSx0, hSy0, hT0⟩
  | succ j ih =>
    rcases ih with ⟨ihSx, ihSy, ihT⟩
    set Lj := 2 ^ j * L₀
    set bj := (2 : ℝ) ^ j * b₀
    set uj := dyadicDefect 49 (49 * u₀) j
    have hLj_even : Even Lj := by
      rcases hL₀ with ⟨m, hm⟩; exact ⟨2 ^ j * m, by dsimp [Lj]; rw [hm]; ring⟩
    have hLj4 : 2 ≤ Lj := by
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow; dsimp [Lj]; nlinarith
    have hbj_pos : 0 < bj := by dsimp [bj]; positivity
    have huj_pos : 0 < uj := dyadicDefect_pos (by norm_num) (by positivity) j
    have huj_le : uj ≤ 1 / 98 :=
      (dyadicDefect_le_u0 (by norm_num) hu0_pos (by linarith) j).trans hu0_le
    have hstep := sys.doubling_round_2d hLj_even hLj4 hbj_pos huj_pos.le huj_le ihSx ihSy ihT
    have hsucc : dyadicDefect 49 (49 * u₀) (j + 1) = 49 * uj ^ 2 :=
      dyadicDefect_succ (by norm_num) j
    have h2L : 2 ^ (j + 1) * L₀ = 2 * Lj := by dsimp [Lj]; ring
    have h4L : 2 * (2 ^ (j + 1) * L₀) = 4 * Lj := by dsimp [Lj]; ring
    have h2b : (2 : ℝ) ^ (j + 1) * b₀ = 2 * bj := by dsimp [bj]; ring
    rw [h4L, h2L, h2b, hsucc]
    exact hstep

/-- Corollary: iterated 2D dyadic purity bounds from the single cube ratio `Q(L₀, b₀) ≥ 1 - u₀`. -/
theorem dyadic_purities_2d (sys : PuritySystem2D) {L₀ : ℕ} {b₀ u₀ : ℝ}
    (hL₀ : Even L₀) (h4 : 2 ≤ L₀) (hb₀ : 0 < b₀)
    (hu0_pos : 0 < u₀) (hu0_le : u₀ ≤ 1 / 98)
    (hQ0 : 1 - u₀ ≤ sys.Q L₀ b₀) :
    ∀ j : ℕ,
      1 - sys.Sx (2 ^ j * L₀) (2 ^ j * L₀) (2 ^ j * b₀) ≤ dyadicDefect 49 (49 * u₀) j ∧
      1 - sys.Sy (2 * (2 ^ j * L₀)) (2 ^ j * L₀) (2 ^ j * b₀) ≤ dyadicDefect 49 (49 * u₀) j ∧
      1 - sys.T (2 * (2 ^ j * L₀)) (2 * (2 ^ j * L₀)) (2 ^ j * b₀) ≤ dyadicDefect 49 (49 * u₀) j := by
  rcases sys.cube_implies_three_purities hL₀ h4 hb₀ hQ0 with ⟨hSx0, hSy0, hT0⟩
  exact sys.dyadic_purities_2d_from_three hL₀ h4 hb₀ hu0_pos hu0_le hSx0 hSy0 hT0

/-- Master 2D Uniform Spectral Gap Theorem from three individual purities
(`arXiv:2611.07400` Sec. II & App. A.3):
starting directly from `Sx(L₀, L₀, b₀), Sy(2L₀, L₀, b₀), T(2L₀, 2L₀, b₀) ≥ 97 / 98`
guarantees a unique ground state and a size-independent spectral gap `Δ_ℓ > log 2 / b₀`
on **every** even `ℓ × ℓ` square with `ℓ ≥ L₀`. -/
theorem uniform_gap_2d_from_three (sys : PuritySystem2D)
    (hInterp : ∀ (L ℓ : ℕ) (b : ℝ), Even L → 2 ≤ L → Even ℓ → L ≤ ℓ → ℓ ≤ 2 * L → 0 < b →
      sys.Z ℓ ℓ b ≤ sys.Z L L b ^ (((ℓ : ℝ) / (L : ℝ)) ^ 2) ∧
      sys.Z (2 * L) (2 * L) (2 * b) ^ (((ℓ : ℝ) / (2 * (L : ℝ))) ^ 2) ≤ sys.Z ℓ ℓ (2 * b))
    {L₀ : ℕ} {b₀ : ℝ}
    (hL₀ : Even L₀) (h4 : 2 ≤ L₀) (hb₀ : 0 < b₀)
    (hSx0 : 1 - sys.Sx L₀ L₀ b₀ ≤ 1 / 98)
    (hSy0 : 1 - sys.Sy (2 * L₀) L₀ b₀ ≤ 1 / 98)
    (hT0 : 1 - sys.T (2 * L₀) (2 * L₀) b₀ ≤ 1 / 98)
    {ℓ d : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : L₀ ≤ ℓ)
    (E : Fin d → ℝ) (k₀ : Fin d) (hmin : ∀ k, E k₀ ≤ E k)
    (hGibbs : ∀ b, 0 < b → sys.Z ℓ ℓ b = ∑ k : Fin d, Real.exp (-b * E k)) :
    (∀ k : Fin d, E k = E k₀ → k = k₀) ∧
    (∀ k : Fin d, k ≠ k₀ → Real.log 2 / b₀ < E k - E k₀) := by
  rcases exists_dyadic_interval_exact (by omega : 0 < L₀) hℓ_ge with ⟨j, hj_lo, hj_hi⟩
  set Lj := 2 ^ j * L₀
  set bj := (2 : ℝ) ^ j * b₀
  set uj := dyadicDefect 49 (49 * (1 / 98)) j
  have hLj_even : Even Lj := by
    rcases hL₀ with ⟨m, hm⟩; exact ⟨2 ^ j * m, by dsimp [Lj]; rw [hm]; ring⟩
  have hLj4 : 2 ≤ Lj := by
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow; dsimp [Lj]; nlinarith
  have hbj_pos : 0 < bj := by dsimp [bj]; positivity
  have hdyad := sys.dyadic_purities_2d_from_three hL₀ h4 hb₀ (by norm_num) le_rfl hSx0 hSy0 hT0 j
  have huj_pos : 0 < uj := dyadicDefect_pos (by norm_num) (by norm_num) j
  have huj_le : uj ≤ 1 / 98 := dyadicDefect_le_u0 (by norm_num) (by norm_num) (by norm_num) j
  -- Cube bound Q(Lj, bj) ≥ (1 - uj)^7 ≥ 1 - 7 uj
  have hSx_j : 1 - sys.Sx Lj Lj bj ≤ uj := hdyad.1
  have hSy_j : 1 - sys.Sy (2 * Lj) Lj bj ≤ uj := hdyad.2.1
  have hT_j : 1 - sys.T (2 * Lj) (2 * Lj) bj ≤ uj := hdyad.2.2
  have hQ_j_ge : (1 - uj) ^ 7 ≤ sys.Q Lj bj := by
    rw [sys.cube_factorization hLj_even hLj4 hbj_pos]
    have h1mu : 0 ≤ 1 - uj := by linarith
    have hSx_ge : 1 - uj ≤ sys.Sx Lj Lj bj := by linarith
    have hSy_ge : 1 - uj ≤ sys.Sy (2 * Lj) Lj bj := by linarith
    have hT_ge : 1 - uj ≤ sys.T (2 * Lj) (2 * Lj) bj := by linarith
    have h1 : (1 - uj) ^ 4 ≤ sys.Sx Lj Lj bj ^ 4 := pow_le_pow_left₀ h1mu hSx_ge 4
    have h2 : (1 - uj) ^ 2 ≤ sys.Sy (2 * Lj) Lj bj ^ 2 := pow_le_pow_left₀ h1mu hSy_ge 2
    have h12 := mul_le_mul h1 h2 (pow_nonneg h1mu 2) (pow_nonneg (by linarith) 4)
    have h123 := mul_le_mul h12 hT_ge h1mu (mul_nonneg (pow_nonneg (by linarith) 4) (pow_nonneg (by linarith) 2))
    calc (1 - uj) ^ 7 = (1 - uj) ^ 4 * (1 - uj) ^ 2 * (1 - uj) := by ring
      _ ≤ _ := h123
  have hQ_j_le1 : sys.Q Lj bj ≤ 1 := by
    rw [sys.cube_factorization hLj_even hLj4 hbj_pos]
    have h2Lj : Even (2 * Lj) := even_two_mul Lj
    have hS1 : sys.Sx Lj Lj bj ≤ 1 := sys.Sx_le_one Lj Lj bj hLj_even hLj4 hLj_even hLj4 hbj_pos
    have hSy1 : sys.Sy (2 * Lj) Lj bj ≤ 1 := sys.Sy_le_one (2 * Lj) Lj bj h2Lj (by omega) hLj_even hLj4 hbj_pos
    have hT1 : sys.T (2 * Lj) (2 * Lj) bj ≤ 1 := sys.T_le_one (2 * Lj) (2 * Lj) bj h2Lj (by omega) h2Lj (by omega) hbj_pos
    have hS0 : 0 ≤ sys.Sx Lj Lj bj :=
      (div_pos (sys.Z_pos (2 * Lj) Lj bj h2Lj (by omega) hLj_even hLj4 hbj_pos)
        (pow_pos (sys.Z_pos Lj Lj bj hLj_even hLj4 hLj_even hLj4 hbj_pos) 2)).le
    have hSy0 : 0 ≤ sys.Sy (2 * Lj) Lj bj :=
      (div_pos (sys.Z_pos (2 * Lj) (2 * Lj) bj h2Lj (by omega) h2Lj (by omega) hbj_pos)
        (pow_pos (sys.Z_pos (2 * Lj) Lj bj h2Lj (by omega) hLj_even hLj4 hbj_pos) 2)).le
    have h1 : sys.Sx Lj Lj bj ^ 4 ≤ 1 := pow_le_one₀ hS0 hS1
    have h2 : sys.Sy (2 * Lj) Lj bj ^ 2 ≤ 1 := by nlinarith
    have h12 : sys.Sx Lj Lj bj ^ 4 * sys.Sy (2 * Lj) Lj bj ^ 2 ≤ 1 := by
      nlinarith [pow_nonneg hS0 4]
    nlinarith [mul_nonneg (pow_nonneg hS0 4) (sq_nonneg (sys.Sy (2 * Lj) Lj bj))]
  -- 2D interpolation: T(ℓ, ℓ, bj) ≥ Q(Lj, bj)^((ℓ / (2 Lj))^2) ≥ 1 - 7 uj
  rcases hInterp Lj ℓ bj hLj_even hLj4 hℓ_even hj_lo hj_hi.le hbj_pos with ⟨hUp, hLo⟩
  set α := ((ℓ : ℝ) / (2 * (Lj : ℝ))) ^ 2
  have hα_le1 : α ≤ 1 := by
    dsimp [α]
    have h1 : (ℓ : ℝ) / (2 * (Lj : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hj_hi.le
    have h0 : 0 ≤ (ℓ : ℝ) / (2 * (Lj : ℝ)) := by positivity
    nlinarith
  have hZLj_pos := sys.Z_pos Lj Lj bj hLj_even hLj4 hLj_even hLj4 hbj_pos
  have hZ2Lj_pos := sys.Z_pos (2 * Lj) (2 * Lj) (2 * bj) (even_two_mul Lj) (by omega)
    (even_two_mul Lj) (by omega) (by linarith)
  have hZℓ_pos := sys.Z_pos ℓ ℓ bj hℓ_even (by omega) hℓ_even (by omega) hbj_pos
  have hden : sys.Z ℓ ℓ bj ^ 2 ≤ (sys.Z Lj Lj bj ^ 8) ^ α := by
    have hsq : sys.Z ℓ ℓ bj ^ 2 ≤ (sys.Z Lj Lj bj ^ (((ℓ : ℝ) / (Lj : ℝ)) ^ 2)) ^ 2 := by nlinarith
    have hpow : (sys.Z Lj Lj bj ^ (((ℓ : ℝ) / (Lj : ℝ)) ^ 2)) ^ 2 = (sys.Z Lj Lj bj ^ 8) ^ α := by
      have hLj0 : (Lj : ℝ) ≠ 0 := by positivity
      rw [← Real.rpow_natCast (sys.Z Lj Lj bj ^ _) 2, ← Real.rpow_mul hZLj_pos.le,
        ← Real.rpow_natCast (sys.Z Lj Lj bj) 8, ← Real.rpow_mul hZLj_pos.le]
      congr 1; dsimp [α]; push_cast; field_simp [hLj0]; ring
    linarith
  have hTℓ_ge : 1 - 7 * uj ≤ sys.Z ℓ ℓ (2 * bj) / sys.Z ℓ ℓ bj ^ 2 := by
    have hQ_pos : 0 < sys.Q Lj bj := lt_of_lt_of_le (pow_pos (by linarith : 0 < 1 - uj) 7) hQ_j_ge
    have hpow_ge : sys.Q Lj bj ≤ sys.Q Lj bj ^ α := by
      simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hQ_pos hQ_j_le1 hα_le1
    have hQ_rpow : sys.Q Lj bj ^ α ≤ sys.Z ℓ ℓ (2 * bj) / sys.Z ℓ ℓ bj ^ 2 := by
      unfold Q
      rw [Real.div_rpow hZ2Lj_pos.le (pow_nonneg hZLj_pos.le 8)]
      have hden_pos : 0 < (sys.Z Lj Lj bj ^ 8) ^ α :=
        Real.rpow_pos_of_pos (pow_pos hZLj_pos 8) _
      rw [div_le_div_iff₀ hden_pos (pow_pos hZℓ_pos 2)]
      have h1 : 0 ≤ sys.Z (2 * Lj) (2 * Lj) (2 * bj) ^ α := Real.rpow_nonneg hZ2Lj_pos.le _
      exact mul_le_mul hLo hden (pow_nonneg hZℓ_pos.le 2) (le_trans h1 hLo)
    have hbern : 1 - 7 * uj ≤ (1 - uj) ^ 7 := by
      have := one_sub_mul_le_pow huj_pos.le (by linarith) 7
      norm_num at this; linarith
    linarith
  have hGibbs_bj := hGibbs bj hbj_pos
  have hGibbs_2bj : sys.Z ℓ ℓ (2 * bj) = ∑ k : Fin d, Real.exp (-2 * bj * E k) := by
    rw [hGibbs (2 * bj) (by linarith)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring
  rw [hGibbs_bj, hGibbs_2bj] at hTℓ_ge
  rcases gibbs_purity_implies_unique_ground_and_gap E k₀ bj hbj_pos hmin
    (by linarith : 0 ≤ 7 * uj) (by linarith : 7 * uj < 1 / 2) hTℓ_ge with ⟨huniq, hgap⟩
  refine ⟨huniq, fun k hne => ?_⟩
  have hratio_lt : 7 * uj / (1 - 7 * uj) < (1 / 2 : ℝ) ^ (2 ^ j) := by
    have h1m_pos : 0 < 1 - 7 * uj := by linarith
    have h49_eq : 49 * uj = (1 / 2 : ℝ) ^ (2 ^ j) := by
      dsimp [uj, dyadicDefect]
      have : (49 : ℝ) * (1 / 98) = 1 / 2 := by norm_num
      rw [this]; ring
    rw [div_lt_iff₀ h1m_pos, ← h49_eq]
    nlinarith
  have hexp_lt : Real.exp (-bj * (E k - E k₀)) < (1 / 2 : ℝ) ^ (2 ^ j) :=
    lt_of_le_of_lt (hgap k hne) hratio_lt
  have hlog_lt : -bj * (E k - E k₀) < (2 ^ j : ℕ) * Real.log (1 / 2) := by
    have := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp, Real.log_pow] at this
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog_half] at hlog_lt
  rw [div_lt_iff₀ hb₀]
  have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hbj_eq : bj = (2 : ℝ) ^ j * b₀ := rfl
  rw [hbj_eq, Nat.cast_pow, Nat.cast_ofNat] at hlog_lt
  nlinarith

/-- Corollary: 2D Uniform Spectral Gap Theorem from the single cube ratio `Q(L₀, b₀) ≥ 97 / 98`
(`arXiv:2611.07400` Sec. II & App. A.3). -/
theorem uniform_gap_2d (sys : PuritySystem2D)
    (hInterp : ∀ (L ℓ : ℕ) (b : ℝ), Even L → 2 ≤ L → Even ℓ → L ≤ ℓ → ℓ ≤ 2 * L → 0 < b →
      sys.Z ℓ ℓ b ≤ sys.Z L L b ^ (((ℓ : ℝ) / (L : ℝ)) ^ 2) ∧
      sys.Z (2 * L) (2 * L) (2 * b) ^ (((ℓ : ℝ) / (2 * (L : ℝ))) ^ 2) ≤ sys.Z ℓ ℓ (2 * b))
    {L₀ : ℕ} {b₀ : ℝ}
    (hL₀ : Even L₀) (h4 : 2 ≤ L₀) (hb₀ : 0 < b₀)
    (hQ0 : 97 / 98 ≤ sys.Q L₀ b₀)
    {ℓ d : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : L₀ ≤ ℓ)
    (E : Fin d → ℝ) (k₀ : Fin d) (hmin : ∀ k, E k₀ ≤ E k)
    (hGibbs : ∀ b, 0 < b → sys.Z ℓ ℓ b = ∑ k : Fin d, Real.exp (-b * E k)) :
    (∀ k : Fin d, E k = E k₀ → k = k₀) ∧
    (∀ k : Fin d, k ≠ k₀ → Real.log 2 / b₀ < E k - E k₀) := by
  have hQ0' : 1 - (1 / 98 : ℝ) ≤ sys.Q L₀ b₀ := by linarith
  rcases sys.cube_implies_three_purities hL₀ h4 hb₀ hQ0' with ⟨hSx0, hSy0, hT0⟩
  exact sys.uniform_gap_2d_from_three hInterp hL₀ h4 hb₀ hSx0 hSy0 hT0 hℓ_even hℓ_ge E k₀ hmin hGibbs

end PuritySystem2D

end PurityBootstrap.HigherDim
