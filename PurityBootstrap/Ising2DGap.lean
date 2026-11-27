import PurityBootstrap.HigherDim
import PurityBootstrap.Ising2DTrotter
import PurityBootstrap.Ising2DSeed

/-!
# Unconditional 2D Quantum Spectral Gap Theorem for the 2D Transverse-Field Ising Torus

We prove an unconditional finite-volume spectral gap theorem for the two-dimensional
transverse-field Ising model on even square tori in Lean 4 using Tarun Grover's 2D purity
bootstrap (`arXiv:2611.07400`, Sec. II) together with a self-contained high-field 2×2 dimer
midpoint seed:

For **every** coupling pair `(Jx, Jy)` in the closed 2D coupling rectangle `|Jx| ≤ 1/192`,
`|Jy| ≤ 1/192` and **every** finite even square torus `L × L` with `L ≥ 2` (with positive-direction
periodic bonds, counted twice per undirected pair at `L = 2` and yielding the standard simple-edge
square torus for all even `L ≥ 4`), the concrete `2^(L^2) × 2^(L^2)` 2D transverse-field Ising
Hamiltonian `H_2d L L Jx Jy` has:
- a **simple ground energy** (exact multiplicity 1 in `(H_2d L L Jx Jy).charpoly.roots`), and
- a **common finite-volume spectral gap** strictly greater than `Real.log 2 / 5 ≈ 0.138629`.

Every ingredient — the 3D classical Lie–Trotter representation and exact real symmetric
spatial transfer matrices (`Ising2DTrotter`), the exact 2×2 dimer midpoint seed and
symbolic all-ones Rayleigh lower bound (`Ising2DSeed`), the spatial/temporal purity
inequalities and square interpolation (`Ising2DGap`), and the abstract 2D dyadic
contraction (`HigherDim`) — is proved from first principles with strictly standard axioms
`[propext, Classical.choice, Quot.sound]` and zero external numerical inputs or certificate tables.
-/

namespace PurityBootstrap.Ising2DGap

open scoped BigOperators Matrix
open Matrix Filter PurityBootstrap PurityBootstrap.HigherDim PurityBootstrap.LieTrotter
  PurityBootstrap.MatrixTools PurityBootstrap.Ising2DTrotter PurityBootstrap.Ising2DSeed

/-! ## 1. Finite-`M` Symmetric Spatial Transfer Inequalities & Positivity -/

private lemma kTime_pos {τ : ℝ} (hτ : 0 < τ) (a b : Bool) : 0 < kTime τ a b := by
  unfold kTime
  split_ifs
  · exact Real.cosh_pos τ
  · rw [Real.sinh_eq]
    have hlt : Real.exp (-τ) < Real.exp τ := Real.exp_lt_exp.mpr (by linarith)
    linarith

lemma Z_M_pos (lx ly : ℕ) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 1 ≤ M) :
    0 < Z_M lx ly Jx Jy a b M := by
  have hτ : 0 < b / (M : ℝ) := div_pos hb (by exact_mod_cast hM)
  unfold Z_M W_3d
  refine Finset.sum_pos (fun s _ => ?_) Finset.univ_nonempty
  refine Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => ?_
  exact mul_pos (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Real.exp_pos _))
    (kTime_pos hτ _ _)

/-- Exact coordinate-swap symmetry of the physical 2D partition function. -/
theorem Z_2d_swap_xy (lx ly : ℕ) (Jx Jy a b : ℝ) :
    Z_2d lx ly Jx Jy a b = Z_2d ly lx Jy Jx a b := by
  have h1 := tendsto_Z_M lx ly Jx Jy a b
  have h2 := tendsto_Z_M ly lx Jy Jx a b
  have h1' : Tendsto (Z_M ly lx Jy Jx a b) atTop (nhds (Z_2d lx ly Jx Jy a b)) :=
    h1.congr fun M => Z_M_swap_xy lx ly Jx Jy a b M
  exact tendsto_nhds_unique h1' h2

/-- Specialization of `LieTrotter.psd_pair_spatial_ineqs` to a single real symmetric matrix `T`. -/
private lemma symm_spatial_ineqs {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (hT : Tᵀ = T) :
    (∀ m : ℕ, 1 ≤ m → Matrix.trace (T ^ (4 * m)) ≤ Matrix.trace (T ^ (2 * m)) ^ 2) ∧
    (∀ m : ℕ, 1 ≤ m → 0 < Matrix.trace (T ^ (2 * m)) → 0 < Matrix.trace (T ^ (4 * m)) →
      1 - Matrix.trace (T ^ (8 * m)) / Matrix.trace (T ^ (4 * m)) ^ 2 ≤
        purityUpdate (1 - Matrix.trace (T ^ (4 * m)) / Matrix.trace (T ^ (2 * m)) ^ 2)) ∧
    (∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → 0 < Matrix.trace (T ^ (2 * m₁)) →
      Matrix.trace (T ^ (2 * m₂)) ≤ Matrix.trace (T ^ (2 * m₁)) ^ ((m₂ : ℝ) / (m₁ : ℝ))) := by
  have hgram : T * Tᵀ = T ^ 2 := by rw [hT, sq]
  have hzero_pow : ∀ k : ℕ, 1 ≤ k → ((0 : Matrix n n ℝ) * (0 : Matrix n n ℝ)ᵀ) ^ k = 0 := by
    intro k hk
    rw [Matrix.zero_mul, zero_pow (by omega)]
  have hZp_eq : ∀ k : ℕ, 1 ≤ k →
      Matrix.trace ((T * Tᵀ) ^ k) + Matrix.trace (((0 : Matrix n n ℝ) * (0 : Matrix n n ℝ)ᵀ) ^ k) =
        Matrix.trace (T ^ (2 * k)) := fun k hk => by
    rw [hgram, ← pow_mul, hzero_pow k hk, Matrix.trace_zero, add_zero]
  rcases psd_pair_spatial_ineqs T (0 : Matrix n n ℝ) with ⟨_, _, hsq, _, hupd, _, hrpow⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    have h := hsq m
    dsimp only at h
    rw [hZp_eq (2 * m) (by omega), hZp_eq m hm] at h
    simpa [show 2 * (2 * m) = 4 * m by ring] using h
  · intro m hm h1 h2
    have h := hupd m (by dsimp only; rwa [hZp_eq m hm]) (by
      dsimp only
      rw [hZp_eq (2 * m) (by omega)]
      simpa [show 2 * (2 * m) = 4 * m by ring] using h2)
    dsimp only at h
    rw [hZp_eq (4 * m) (by omega), hZp_eq (2 * m) (by omega), hZp_eq m hm] at h
    simpa [show 2 * (4 * m) = 8 * m by ring, show 2 * (2 * m) = 4 * m by ring] using h
  · intro m₁ m₂ hm₁ hle hpos
    have h := hrpow m₁ m₂ hm₁ hle (by dsimp only; rwa [hZp_eq m₁ hm₁])
    dsimp only at h
    rwa [hZp_eq m₂ (by omega), hZp_eq m₁ hm₁] at h

/-! ## 2. Limiting Spatial & Temporal Purity Inequalities for `Z_2d` -/

lemma Z_2d_Sx_le_one {lx ly : ℕ} (hlx : Even lx) (hlx2 : 2 ≤ lx) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) :
    Z_2d (2 * lx) ly Jx Jy a b / (Z_2d lx ly Jx Jy a b) ^ 2 ≤ 1 := by
  obtain ⟨m, rfl⟩ := hlx
  have hm : 1 ≤ m := by omega
  have h2m : m + m = 2 * m := by ring
  rw [h2m]
  have hlimL := (tendsto_Z_M (2 * (2 * m)) ly Jx Jy a b).div
    ((tendsto_Z_M (2 * m) ly Jx Jy a b).pow 2)
    (pow_ne_zero 2 (Z_2d_pos (2 * m) ly Jx Jy a b).ne')
  have hlimR : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hlimL hlimR ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  dsimp only [Pi.div_apply]
  rw [div_le_one (pow_pos (Z_M_pos (2 * m) ly Jx Jy a hb hM) 2)]
  rw [Z_M_eq_trace_Tx (2 * (2 * m)) ly Jx Jy a hb (by omega) hM,
      Z_M_eq_trace_Tx (2 * m) ly Jx Jy a hb (by omega) hM]
  have hineq := (symm_spatial_ineqs (T_x ly M Jx Jy a (b / (M : ℝ)))
    (T_x_transpose ly M Jx Jy a (b / (M : ℝ)))).1 m hm
  simpa [show 2 * (2 * m) = 4 * m by ring] using hineq

lemma Z_2d_Sy_le_one {lx ly : ℕ} (hly : Even ly) (hly2 : 2 ≤ ly) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) :
    Z_2d lx (2 * ly) Jx Jy a b / (Z_2d lx ly Jx Jy a b) ^ 2 ≤ 1 := by
  rw [Z_2d_swap_xy lx (2 * ly) Jx Jy a b, Z_2d_swap_xy lx ly Jx Jy a b]
  exact Z_2d_Sx_le_one hly hly2 Jy Jx a hb

lemma Z_2d_Sx_square {lx ly : ℕ} (hlx : Even lx) (hlx2 : 2 ≤ lx) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) :
    1 - Z_2d (4 * lx) ly Jx Jy a b / (Z_2d (2 * lx) ly Jx Jy a b) ^ 2 ≤
      purityUpdate (1 - Z_2d (2 * lx) ly Jx Jy a b / (Z_2d lx ly Jx Jy a b) ^ 2) := by
  obtain ⟨m, rfl⟩ := hlx
  have hm : 1 ≤ m := by omega
  have h2m : m + m = 2 * m := by ring
  rw [h2m]
  have hZ1_pos := Z_2d_pos (2 * m) ly Jx Jy a b
  have hZ2_pos := Z_2d_pos (2 * (2 * m)) ly Jx Jy a b
  have hlim1 := tendsto_Z_M (2 * m) ly Jx Jy a b
  have hlim2 := tendsto_Z_M (2 * (2 * m)) ly Jx Jy a b
  have hlim4 := tendsto_Z_M (4 * (2 * m)) ly Jx Jy a b
  have hlimS1 : Tendsto (fun M => Z_M (2 * (2 * m)) ly Jx Jy a b M / Z_M (2 * m) ly Jx Jy a b M ^ 2)
      atTop (nhds (Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2)) :=
    hlim2.div (hlim1.pow 2) (pow_ne_zero 2 hZ1_pos.ne')
  have hlimS2 : Tendsto (fun M => Z_M (4 * (2 * m)) ly Jx Jy a b M / Z_M (2 * (2 * m)) ly Jx Jy a b M ^ 2)
      atTop (nhds (Z_2d (4 * (2 * m)) ly Jx Jy a b / Z_2d (2 * (2 * m)) ly Jx Jy a b ^ 2)) :=
    hlim4.div (hlim2.pow 2) (pow_ne_zero 2 hZ2_pos.ne')
  have hlimL : Tendsto (fun M => 1 - Z_M (4 * (2 * m)) ly Jx Jy a b M / Z_M (2 * (2 * m)) ly Jx Jy a b M ^ 2)
      atTop (nhds (1 - Z_2d (4 * (2 * m)) ly Jx Jy a b / Z_2d (2 * (2 * m)) ly Jx Jy a b ^ 2)) :=
    tendsto_const_nhds.sub hlimS2
  have hS1_pos : 0 < Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2 :=
    div_pos hZ2_pos (pow_pos hZ1_pos 2)
  have hlimR : Tendsto (fun M => purityUpdate (1 - Z_M (2 * (2 * m)) ly Jx Jy a b M / Z_M (2 * m) ly Jx Jy a b M ^ 2))
      atTop (nhds (purityUpdate (1 - Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2))) := by
    unfold purityUpdate
    have hnum : Tendsto (fun M => (1 - Z_M (2 * (2 * m)) ly Jx Jy a b M / Z_M (2 * m) ly Jx Jy a b M ^ 2) ^ 2)
        atTop (nhds ((1 - Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2) ^ 2)) :=
      (tendsto_const_nhds.sub hlimS1).pow 2
    have hden_lim : 2 * (1 - (1 - Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2)) ^ 2 ≠ 0 := by
      have : 1 - (1 - Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2) =
          Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2 := by ring
      rw [this]
      positivity
    have hden : Tendsto (fun M => 2 * (1 - (1 - Z_M (2 * (2 * m)) ly Jx Jy a b M / Z_M (2 * m) ly Jx Jy a b M ^ 2)) ^ 2)
        atTop (nhds (2 * (1 - (1 - Z_2d (2 * (2 * m)) ly Jx Jy a b / Z_2d (2 * m) ly Jx Jy a b ^ 2)) ^ 2)) :=
      tendsto_const_nhds.mul ((tendsto_const_nhds.sub (tendsto_const_nhds.sub hlimS1)).pow 2)
    exact hnum.div hden hden_lim
  refine le_of_tendsto_of_tendsto hlimL hlimR ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hp1 := Z_M_pos (2 * m) ly Jx Jy a hb hM
  have hp2 := Z_M_pos (2 * (2 * m)) ly Jx Jy a hb hM
  rw [Z_M_eq_trace_Tx (4 * (2 * m)) ly Jx Jy a hb (by omega) hM,
      Z_M_eq_trace_Tx (2 * (2 * m)) ly Jx Jy a hb (by omega) hM,
      Z_M_eq_trace_Tx (2 * m) ly Jx Jy a hb (by omega) hM]
  rw [Z_M_eq_trace_Tx (2 * m) ly Jx Jy a hb (by omega) hM] at hp1
  rw [Z_M_eq_trace_Tx (2 * (2 * m)) ly Jx Jy a hb (by omega) hM] at hp2
  have hineq := (symm_spatial_ineqs (T_x ly M Jx Jy a (b / (M : ℝ)))
    (T_x_transpose ly M Jx Jy a (b / (M : ℝ)))).2.1 m hm hp1
    (by simpa [show 2 * (2 * m) = 4 * m by ring] using hp2)
  simpa [show 4 * (2 * m) = 8 * m by ring, show 2 * (2 * m) = 4 * m by ring] using hineq

lemma Z_2d_Sy_square {lx ly : ℕ} (hly : Even ly) (hly2 : 2 ≤ ly) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) :
    1 - Z_2d lx (4 * ly) Jx Jy a b / (Z_2d lx (2 * ly) Jx Jy a b) ^ 2 ≤
      purityUpdate (1 - Z_2d lx (2 * ly) Jx Jy a b / (Z_2d lx ly Jx Jy a b) ^ 2) := by
  rw [Z_2d_swap_xy lx (4 * ly) Jx Jy a b, Z_2d_swap_xy lx (2 * ly) Jx Jy a b,
      Z_2d_swap_xy lx ly Jx Jy a b]
  exact Z_2d_Sx_square hly hly2 Jy Jx a hb

/-- Single-axis `x`-direction real-power inequality for `Z_2d`. -/
lemma Z_2d_x_rpow_le {p q ly : ℕ} (hp : Even p) (hp2 : 2 ≤ p) (hq : Even q) (hle : p ≤ q)
    (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) :
    Z_2d q ly Jx Jy a b ≤ Z_2d p ly Jx Jy a b ^ ((q : ℝ) / (p : ℝ)) := by
  obtain ⟨m₁, rfl⟩ := hp
  obtain ⟨m₂, rfl⟩ := hq
  have hm₁ : 1 ≤ m₁ := by omega
  have hm_le : m₁ ≤ m₂ := by omega
  have h1 : m₁ + m₁ = 2 * m₁ := by ring
  have h2 : m₂ + m₂ = 2 * m₂ := by ring
  rw [h1, h2]
  have hratio : ((2 * m₂ : ℕ) : ℝ) / ((2 * m₁ : ℕ) : ℝ) = (m₂ : ℝ) / (m₁ : ℝ) := by
    push_cast
    have hm1_ne : (m₁ : ℝ) ≠ 0 := by positivity
    field_simp [hm1_ne]
  rw [hratio]
  have hlimL := tendsto_Z_M (2 * m₂) ly Jx Jy a b
  have hlimR : Tendsto (fun M => Z_M (2 * m₁) ly Jx Jy a b M ^ ((m₂ : ℝ) / (m₁ : ℝ)))
      atTop (nhds (Z_2d (2 * m₁) ly Jx Jy a b ^ ((m₂ : ℝ) / (m₁ : ℝ)))) :=
    (tendsto_Z_M (2 * m₁) ly Jx Jy a b).rpow_const (Or.inl (Z_2d_pos (2 * m₁) ly Jx Jy a b).ne')
  refine le_of_tendsto_of_tendsto hlimL hlimR ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hp1 := Z_M_pos (2 * m₁) ly Jx Jy a hb hM
  rw [Z_M_eq_trace_Tx (2 * m₂) ly Jx Jy a hb (by omega) hM,
      Z_M_eq_trace_Tx (2 * m₁) ly Jx Jy a hb (by omega) hM]
  rw [Z_M_eq_trace_Tx (2 * m₁) ly Jx Jy a hb (by omega) hM] at hp1
  exact (symm_spatial_ineqs (T_x ly M Jx Jy a (b / (M : ℝ)))
    (T_x_transpose ly M Jx Jy a (b / (M : ℝ)))).2.2 m₁ m₂ hm₁ hm_le hp1

/-- Single-axis `y`-direction real-power inequality for `Z_2d`. -/
lemma Z_2d_y_rpow_le {lx p q : ℕ} (hp : Even p) (hp2 : 2 ≤ p) (hq : Even q) (hle : p ≤ q)
    (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b) :
    Z_2d lx q Jx Jy a b ≤ Z_2d lx p Jx Jy a b ^ ((q : ℝ) / (p : ℝ)) := by
  rw [Z_2d_swap_xy lx q Jx Jy a b, Z_2d_swap_xy lx p Jx Jy a b]
  exact Z_2d_x_rpow_le hp hp2 hq hle Jy Jx a hb

/-- Exact Gibbs sum formula for `Z_2d lx ly Jx Jy a b`. -/
lemma Z_2d_eq_gibbs (lx ly : ℕ) (Jx Jy a b : ℝ) :
    Z_2d lx ly Jx Jy a b =
      ∑ k : Cfg lx ly, Real.exp (-b * ((H_2d_isHermitian lx ly Jx Jy).eigenvalues k + a * (lx * ly : ℝ))) := by
  unfold Z_2d matZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.exp_add]
  congr 1; ring

/-- Exact temporal purity inequalities (`T ≤ 1` and `T_square`) directly from `finset_purity_square_bound`. -/
lemma Z_2d_T_ineqs (lx ly : ℕ) (Jx Jy a b : ℝ) :
    Z_2d lx ly Jx Jy a (2 * b) / (Z_2d lx ly Jx Jy a b) ^ 2 ≤ 1 ∧
    1 - Z_2d lx ly Jx Jy a (4 * b) / (Z_2d lx ly Jx Jy a (2 * b)) ^ 2 ≤
      purityUpdate (1 - Z_2d lx ly Jx Jy a (2 * b) / (Z_2d lx ly Jx Jy a b) ^ 2) := by
  set E : Cfg lx ly → ℝ := fun k => (H_2d_isHermitian lx ly Jx Jy).eigenvalues k + a * (lx * ly : ℝ)
  set Z1 := Z_2d lx ly Jx Jy a b
  have hZ1_pos : 0 < Z1 := Z_2d_pos lx ly Jx Jy a b
  let p : Cfg lx ly → ℝ := fun k => Real.exp (-b * E k) / Z1
  have hp_nn : ∀ k ∈ (Finset.univ : Finset (Cfg lx ly)), 0 ≤ p k := fun k _ =>
    div_nonneg (Real.exp_pos _).le hZ1_pos.le
  have hp_sum : ∑ k ∈ (Finset.univ : Finset (Cfg lx ly)), p k = 1 := by
    simp only [p]
    rw [← Finset.sum_div, ← Z_2d_eq_gibbs lx ly Jx Jy a b, div_self hZ1_pos.ne']
  have hP2 : ∑ k : Cfg lx ly, (p k) ^ 2 = Z_2d lx ly Jx Jy a (2 * b) / Z1 ^ 2 := by
    simp only [p, div_pow, ← Finset.sum_div]
    congr 1
    rw [Z_2d_eq_gibbs lx ly Jx Jy a (2 * b)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hP4 : ∑ k : Cfg lx ly, (p k) ^ 4 = Z_2d lx ly Jx Jy a (4 * b) / Z1 ^ 4 := by
    simp only [p, div_pow, ← Finset.sum_div]
    congr 1
    rw [Z_2d_eq_gibbs lx ly Jx Jy a (4 * b)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h4 : (Real.exp (-b * E k)) ^ 4 = Real.exp (-(4 * b) * E k) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    exact h4
  have hbound := finset_purity_square_bound (Finset.univ : Finset (Cfg lx ly)) p hp_nn hp_sum
  rw [hP2, hP4] at hbound
  have hratio : (Z_2d lx ly Jx Jy a (4 * b) / Z1 ^ 4) / (Z_2d lx ly Jx Jy a (2 * b) / Z1 ^ 2) ^ 2 =
      Z_2d lx ly Jx Jy a (4 * b) / (Z_2d lx ly Jx Jy a (2 * b)) ^ 2 := by
    have hZ2_ne : Z_2d lx ly Jx Jy a (2 * b) ≠ 0 := (Z_2d_pos lx ly Jx Jy a (2 * b)).ne'
    field_simp [hZ1_pos.ne', hZ2_ne]
  rw [hratio] at hbound
  exact hbound.2

/-! ## 3. Concrete `PuritySystem2D` and Square Interpolation `hInterp` -/

/-- Concrete `PuritySystem2D` for the 2D transverse-field Ising torus Hamiltonian `H_2d`. -/
noncomputable def ising2DPuritySystem (Jx Jy a : ℝ) : PuritySystem2D where
  Z lx ly b := Z_2d lx ly Jx Jy a b
  Z_pos lx ly b _ _ _ _ _ := Z_2d_pos lx ly Jx Jy a b
  Sx_le_one _ _ _ hlx hlx2 _ _ hb := Z_2d_Sx_le_one hlx hlx2 Jx Jy a hb
  Sy_le_one _ _ _ _ _ hly hly2 hb := Z_2d_Sy_le_one hly hly2 Jx Jy a hb
  T_le_one lx ly b _ _ _ _ _ := (Z_2d_T_ineqs lx ly Jx Jy a b).1
  Sx_square _ _ _ hlx hlx2 _ _ hb := Z_2d_Sx_square hlx hlx2 Jx Jy a hb
  Sy_square _ _ _ _ _ hly hly2 hb := Z_2d_Sy_square hly hly2 Jx Jy a hb
  T_square lx ly b _ _ _ _ _ := (Z_2d_T_ineqs lx ly Jx Jy a b).2

/-- Exact two-axis square interpolation `hInterp` for `ising2DPuritySystem`. -/
theorem ising2D_hInterp (Jx Jy a : ℝ) :
    ∀ (L ℓ : ℕ) (b : ℝ), Even L → 2 ≤ L → Even ℓ → L ≤ ℓ → ℓ ≤ 2 * L → 0 < b →
      (ising2DPuritySystem Jx Jy a).Z ℓ ℓ b ≤
        (ising2DPuritySystem Jx Jy a).Z L L b ^ (((ℓ : ℝ) / (L : ℝ)) ^ 2) ∧
      (ising2DPuritySystem Jx Jy a).Z (2 * L) (2 * L) (2 * b) ^ (((ℓ : ℝ) / (2 * (L : ℝ))) ^ 2) ≤
        (ising2DPuritySystem Jx Jy a).Z ℓ ℓ (2 * b) := by
  intro L ℓ b hL hL2 hℓ hLℓ hℓ2L hb
  dsimp [ising2DPuritySystem]
  have hL_pos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  constructor
  · have h1 : Z_2d ℓ ℓ Jx Jy a b ≤ Z_2d L ℓ Jx Jy a b ^ ((ℓ : ℝ) / (L : ℝ)) :=
      Z_2d_x_rpow_le hL hL2 hℓ hLℓ Jx Jy a hb
    have h2 : Z_2d L ℓ Jx Jy a b ≤ Z_2d L L Jx Jy a b ^ ((ℓ : ℝ) / (L : ℝ)) :=
      Z_2d_y_rpow_le hL hL2 hℓ hLℓ Jx Jy a hb
    have h2pow : Z_2d L ℓ Jx Jy a b ^ ((ℓ : ℝ) / (L : ℝ)) ≤
        (Z_2d L L Jx Jy a b ^ ((ℓ : ℝ) / (L : ℝ))) ^ ((ℓ : ℝ) / (L : ℝ)) :=
      Real.rpow_le_rpow (Z_2d_pos L ℓ Jx Jy a b).le h2 (by positivity)
    calc Z_2d ℓ ℓ Jx Jy a b
        ≤ Z_2d L ℓ Jx Jy a b ^ ((ℓ : ℝ) / (L : ℝ)) := h1
      _ ≤ (Z_2d L L Jx Jy a b ^ ((ℓ : ℝ) / (L : ℝ))) ^ ((ℓ : ℝ) / (L : ℝ)) := h2pow
      _ = Z_2d L L Jx Jy a b ^ (((ℓ : ℝ) / (L : ℝ)) ^ 2) := by
          rw [← Real.rpow_mul (Z_2d_pos L L Jx Jy a b).le, sq]
  · have h2L_even : Even (2 * L) := even_two_mul L
    have h1 : Z_2d (2 * L) (2 * L) Jx Jy a (2 * b) ≤
        Z_2d ℓ (2 * L) Jx Jy a (2 * b) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) :=
      Z_2d_x_rpow_le hℓ (by omega) h2L_even hℓ2L Jx Jy a (by linarith)
    have h2 : Z_2d ℓ (2 * L) Jx Jy a (2 * b) ≤
        Z_2d ℓ ℓ Jx Jy a (2 * b) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) :=
      Z_2d_y_rpow_le hℓ (by omega) h2L_even hℓ2L Jx Jy a (by linarith)
    have hchain : Z_2d (2 * L) (2 * L) Jx Jy a (2 * b) ≤
        Z_2d ℓ ℓ Jx Jy a (2 * b) ^ ((((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) ^ 2) := by
      have h2pow : Z_2d ℓ (2 * L) Jx Jy a (2 * b) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) ≤
          (Z_2d ℓ ℓ Jx Jy a (2 * b) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ))) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) :=
        Real.rpow_le_rpow (Z_2d_pos ℓ (2 * L) Jx Jy a (2 * b)).le h2 (by positivity)
      calc Z_2d (2 * L) (2 * L) Jx Jy a (2 * b)
          ≤ Z_2d ℓ (2 * L) Jx Jy a (2 * b) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) := h1
        _ ≤ (Z_2d ℓ ℓ Jx Jy a (2 * b) ^ (((2 * L : ℕ) : ℝ) / (ℓ : ℝ))) ^
              (((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) := h2pow
        _ = Z_2d ℓ ℓ Jx Jy a (2 * b) ^ ((((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) ^ 2) := by
            rw [← Real.rpow_mul (Z_2d_pos ℓ ℓ Jx Jy a (2 * b)).le, sq]
    have hexp_nn : 0 ≤ ((ℓ : ℝ) / (2 * (L : ℝ))) ^ 2 := by positivity
    have hpow := Real.rpow_le_rpow (Z_2d_pos (2 * L) (2 * L) Jx Jy a (2 * b)).le hchain hexp_nn
    refine hpow.trans_eq ?_
    rw [← Real.rpow_mul (Z_2d_pos ℓ ℓ Jx Jy a (2 * b)).le]
    have hprod1 : ((((2 * L : ℕ) : ℝ) / (ℓ : ℝ)) ^ 2) * (((ℓ : ℝ) / (2 * (L : ℝ))) ^ 2) = 1 := by
      push_cast
      field_simp [hL_pos.ne', hℓ_pos.ne']
    rw [hprod1, Real.rpow_one]

/-! ## 4. Unconditional Physical 2D Spectral Gap Theorems -/

/-- **Unconditional 2D Quantum Spectral Gap Theorem (Eigenvalue Form)**:
for every `(Jx, Jy)` in the closed coupling rectangle `|Jx| ≤ 1/192, |Jy| ≤ 1/192` and every finite
even `L ≥ 2`, the concrete `2^(L^2) × 2^(L^2)` 2D transverse-field Ising square-torus Hamiltonian
`H_2d L L Jx Jy` has a unique minimizing index `k₀ : Cfg L L` with a simple ground energy and
finite-volume spectral gap strictly greater than `Real.log 2 / 5 ≈ 0.138629`. -/
theorem ising_2d_unconditional_rectangle_gap
    {Jx Jy : ℝ} (hJx : |Jx| ≤ 1 / 192) (hJy : |Jy| ≤ 1 / 192)
    {L : ℕ} (hL_even : Even L) (hL_ge : 2 ≤ L) :
    ∃ k₀ : Cfg L L,
      (∀ k : Cfg L L,
        (H_2d_isHermitian L L Jx Jy).eigenvalues k₀ ≤
          (H_2d_isHermitian L L Jx Jy).eigenvalues k) ∧
      (∀ k : Cfg L L, k ≠ k₀ →
        Real.log 2 / 5 <
          (H_2d_isHermitian L L Jx Jy).eigenvalues k -
            (H_2d_isHermitian L L Jx Jy).eigenvalues k₀) := by
  let sys := ising2DPuritySystem Jx Jy 1
  have hQ0 : 97 / 98 ≤ sys.Q 2 5 := by
    change 97 / 98 ≤ Z_2d (2 * 2) (2 * 2) Jx Jy 1 (2 * 5) / (Z_2d 2 2 Jx Jy 1 5) ^ 8
    have h25 : (2 * 5 : ℝ) = 10 := by norm_num
    rw [h25]
    exact ising2d_seed_2x2 hJx hJy
  let e : Cfg L L ≃ Fin (Fintype.card (Cfg L L)) := Fintype.equivFin (Cfg L L)
  let E : Fin (Fintype.card (Cfg L L)) → ℝ := fun i =>
    (H_2d_isHermitian L L Jx Jy).eigenvalues (e.symm i) + 1 * ((L : ℝ) * (L : ℝ))
  have hne : (Finset.univ : Finset (Fin (Fintype.card (Cfg L L)))).Nonempty := by
    refine ⟨e (fun _ => false), Finset.mem_univ _⟩
  rcases Finset.exists_min_image Finset.univ E hne with ⟨i₀, _, hi₀_min⟩
  have hGibbs : ∀ b, 0 < b → sys.Z L L b = ∑ i : Fin (Fintype.card (Cfg L L)), Real.exp (-b * E i) := by
    intro b _
    dsimp [sys, ising2DPuritySystem]
    rw [Z_2d_eq_gibbs L L Jx Jy 1 b]
    refine Fintype.sum_equiv e _ _ fun k => ?_
    simp [E]
  rcases sys.uniform_gap_2d (ising2D_hInterp Jx Jy 1)
      (by decide : Even (2 : ℕ)) (by norm_num) (by norm_num : (0 : ℝ) < 5)
      hQ0 hL_even hL_ge E i₀ (fun i => hi₀_min i (Finset.mem_univ i)) hGibbs with ⟨_, hsep⟩
  refine ⟨e.symm i₀, fun k => ?_, fun k hne_k => ?_⟩
  · have h := hi₀_min (e k) (Finset.mem_univ (e k))
    dsimp [E] at h
    rw [Equiv.symm_apply_apply] at h
    linarith
  · have hne_i : e k ≠ i₀ := fun heq => hne_k (by simpa [e] using congrArg e.symm heq)
    have h := hsep (e k) hne_i
    dsimp [E] at h
    rw [Equiv.symm_apply_apply] at h
    linarith

/-- Self-contained multiset bridge from `IsHermitian.eigenvalues` to `A.charpoly.roots`. -/
private lemma charpoly_roots_eq_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.charpoly.roots = Finset.univ.val.map hA.eigenvalues := by
  have h1 := hA.roots_charpoly_eq_eigenvalues₀
  let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have hcomp : (RCLike.ofReal ∘ hA.eigenvalues₀ : Fin (Fintype.card n) → ℝ) = hA.eigenvalues₀ := rfl
  rw [hcomp] at h1
  have hmap : Multiset.map hA.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card n))).val =
      Multiset.map hA.eigenvalues (Finset.univ : Finset n).val := by
    have huniv : (Finset.univ : Finset (Fin (Fintype.card n))).val =
        Multiset.map e (Finset.univ : Finset n).val := by
      have hfin : (Finset.univ : Finset (Fin (Fintype.card n))) = Finset.univ.map e.toEmbedding := by
        ext j; simp
      rw [hfin, Finset.map_val]
      rfl
    rw [huniv, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    rfl
  exact h1.trans hmap

/-- **Unconditional 2D Quantum Spectral Gap Theorem (Characteristic-Polynomial Roots Form)**:
states the unique ground state (exact multiplicity 1) and uniform gap `> Real.log 2 / 5`
directly on the multiset `(H_2d L L Jx Jy).charpoly.roots` for every finite even `L ≥ 2` and
every `|Jx|, |Jy| ≤ 1/192`. -/
theorem ising_2d_unconditional_rectangle_charpoly_gap
    {Jx Jy : ℝ} (hJx : |Jx| ≤ 1 / 192) (hJy : |Jy| ≤ 1 / 192)
    {L : ℕ} (hL_even : Even L) (hL_ge : 2 ≤ L) :
    ∃ (E₀ : ℝ) (rest : Multiset ℝ),
      (H_2d L L Jx Jy).charpoly.roots = E₀ ::ₘ rest ∧
      rest.card + 1 = 2 ^ (L * L) ∧
      ∀ E ∈ rest, Real.log 2 / 5 < E - E₀ := by
  rcases ising_2d_unconditional_rectangle_gap hJx hJy hL_even hL_ge with ⟨k₀, _, hsep⟩
  let hH := H_2d_isHermitian L L Jx Jy
  refine ⟨hH.eigenvalues k₀, (Finset.univ.erase k₀).val.map hH.eigenvalues, ?_, ?_, ?_⟩
  · rw [charpoly_roots_eq_eigenvalues _ hH]
    have hcons : (Finset.univ : Finset (Cfg L L)).val = k₀ ::ₘ (Finset.univ.erase k₀).val := by
      have := Finset.insert_erase (Finset.mem_univ k₀)
      conv_lhs => rw [← this]
      exact Finset.insert_val_of_notMem (Finset.notMem_erase k₀ _)
    rw [hcons, Multiset.map_cons]
  · have hcard : Fintype.card (Cfg L L) = 2 ^ (L * L) := by
      simp [Cfg, Site, Fintype.card_prod, Fintype.card_fin]
    have h1 : 1 ≤ 2 ^ (L * L) := Nat.one_le_pow (L * L) 2 (by omega)
    simp [hcard, Nat.sub_add_cancel h1]
  · intro E hE
    rcases Multiset.mem_map.mp hE with ⟨k, hk, rfl⟩
    have hne : k ≠ k₀ := (Finset.mem_erase.mp hk).1
    exact hsep k hne

end PurityBootstrap.Ising2DGap
