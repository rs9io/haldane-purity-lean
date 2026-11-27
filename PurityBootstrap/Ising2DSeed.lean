import PurityBootstrap.Ising2DTrotter
import PurityBootstrap.MatrixTools

/-!
# Concrete 2×2 Seed Certificate for the 2D Transverse-Field Ising Torus

Certifies the exact 2D purity-bootstrap seed on the closed coupling rectangle
`|Jx| ≤ 1/192`, `|Jy| ≤ 1/192` at `(L₀, b₀) = (2, 5)` with zero external
numerical inputs and strictly standard Lean axioms:

1. **Exact 2-qubit dimer trace (`matZ_bond2Q`)**:
   for `bond2Q J = -(X₀ + X₁) - 4 J Z₀ Z₁ + 2 I` on `Bool × Bool`,
   `matZ (bond2Q J) _ b = F_bond b J`
   where `F_bond b J = exp(2b(√(1+4J²) - 1)) + exp(-2b(√(1+4J²) + 1)) + 2 exp(-2b) cosh(4bJ)`.
   Proved algebraically using commuting involutions and `LieTrotter.exp_involutive`.
2. **Exact 2×2 midpoint decomposition (`H_2d_2x2_midpoint`)**:
   `H_2d 2 2 Jx Jy + 4 • 1 = (1/2) • A_x + (1/2) • A_y` where `A_x` and `A_y` are
   disjoint horizontal/vertical dimer pairs. By `MatrixTools.matZ_convex_combo_le`
   at `θ = 1/2`, `Z_2d 2 2 Jx Jy 1 b ≤ F_bond b Jx * F_bond b Jy`.
3. **Symbolic all-ones Rayleigh lower bound (`one_le_Z_2d_shift_one`)**:
   for all `lx ≥ 2`, `ly ≥ 2`, `b > 0`, `1 ≤ Z_2d lx ly Jx Jy 1 b` via
   `MatrixTools.exp_rayleigh_le_matZ` on the all-ones vector.
4. **Rational scalar certificate (`scalar_F5_pow16_le`) & rectangle seed (`ising2d_seed_2x2`)**:
   for all `|Jx| ≤ 1/192` and `|Jy| ≤ 1/192`,
   `97 / 98 ≤ Z_2d 4 4 Jx Jy 1 10 / (Z_2d 2 2 Jx Jy 1 5) ^ 8`.
-/

namespace PurityBootstrap.Ising2DSeed

open scoped BigOperators Matrix
open Matrix PurityBootstrap.LieTrotter PurityBootstrap.MatrixTools PurityBootstrap.Ising2DTrotter

/-! ## 1. Exact Two-Qubit Dimer Trace `F_bond b J` -/

abbrev PairCfg := Bool × Bool

/-- Exact two-qubit dimer partition function at inverse temperature `b` and coupling `J`. -/
noncomputable def F_bond (b J : ℝ) : ℝ :=
  Real.exp (2 * b * (Real.sqrt (1 + 4 * J ^ 2) - 1)) +
    Real.exp (-2 * b * (Real.sqrt (1 + 4 * J ^ 2) + 1)) +
    2 * Real.exp (-2 * b) * Real.cosh (4 * b * J)

lemma F_bond_pos (b J : ℝ) : 0 < F_bond b J := by
  unfold F_bond
  have h1 : 0 < Real.exp (2 * b * (Real.sqrt (1 + 4 * J ^ 2) - 1)) := Real.exp_pos _
  have h2 : 0 < Real.exp (-2 * b * (Real.sqrt (1 + 4 * J ^ 2) + 1)) := Real.exp_pos _
  have h3 : 0 < 2 * Real.exp (-2 * b) * Real.cosh (4 * b * J) :=
    mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (Real.cosh_pos _)
  linarith

/-- Two-qubit dimer Hamiltonian `-(X₀ + X₁) - 4 J Z₀ Z₁ + 2 I` on `Bool × Bool`. -/
noncomputable def bond2Q (J : ℝ) : Matrix PairCfg PairCfg ℝ :=
  Matrix.of fun u v =>
    (if u = v then 2 - 4 * J * spinSign u.1 * spinSign u.2 else 0) -
    (if u.1 = !v.1 ∧ u.2 = v.2 then 1 else 0) -
    (if u.1 = v.1 ∧ u.2 = !v.2 then 1 else 0)

lemma bond2Q_isHermitian (J : ℝ) : (bond2Q J).IsHermitian := by
  ext u v
  simp only [Matrix.conjTranspose_apply, star_trivial, bond2Q, Matrix.of_apply]
  rcases u with ⟨a, b⟩; rcases v with ⟨a', b'⟩
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp [spinSign]

private def swapBoth : Matrix PairCfg PairCfg ℝ :=
  Matrix.of fun u v => if u.1 = !v.1 ∧ u.2 = !v.2 then 1 else 0

private def zzMat : Matrix PairCfg PairCfg ℝ :=
  Matrix.diagonal fun u => spinSign u.1 * spinSign u.2

private noncomputable def pPlus : Matrix PairCfg PairCfg ℝ := (1 / 2 : ℝ) • (1 + swapBoth)
private noncomputable def pMinus : Matrix PairCfg PairCfg ℝ := (1 / 2 : ℝ) • (1 - swapBoth)

private noncomputable def kDimer (J : ℝ) : Matrix PairCfg PairCfg ℝ :=
  Matrix.of fun u v =>
    (if u = v then 4 * J * spinSign u.1 * spinSign u.2 else 0) +
    (if u.1 = !v.1 ∧ u.2 = v.2 then 1 else 0) +
    (if u.1 = v.1 ∧ u.2 = !v.2 then 1 else 0)

private noncomputable def rPlus (J : ℝ) : Matrix PairCfg PairCfg ℝ :=
  (1 / (2 * Real.sqrt (1 + 4 * J ^ 2))) • (pPlus * kDimer J)

private noncomputable def rMinus : Matrix PairCfg PairCfg ℝ := pMinus * zzMat

private noncomputable def invM1 (J : ℝ) : Matrix PairCfg PairCfg ℝ := rPlus J + pMinus
private noncomputable def invM2 : Matrix PairCfg PairCfg ℝ := pPlus + rMinus
private def invM3 : Matrix PairCfg PairCfg ℝ := swapBoth

private lemma sqrt_pos_1_4J2 (J : ℝ) : 0 < Real.sqrt (1 + 4 * J ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

private lemma invM3_sq : invM3 * invM3 = 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [invM3, swapBoth, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> cases a' <;> cases b' <;> norm_num

private lemma invM2_sq : invM2 * invM2 = 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [invM2, pPlus, rMinus, pMinus, swapBoth, zzMat, Matrix.mul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply,
    smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> cases a' <;> cases b' <;> norm_num [spinSign]

private lemma invM1_sq (J : ℝ) : invM1 J * invM1 J = 1 := by
  have hs_ne : Real.sqrt (1 + 4 * J ^ 2) ≠ 0 := (sqrt_pos_1_4J2 J).ne'
  have hsq : Real.sqrt (1 + 4 * J ^ 2) ^ 2 = 1 + 4 * J ^ 2 := Real.sq_sqrt (by positivity)
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [invM1, rPlus, pPlus, pMinus, swapBoth, kDimer, Matrix.mul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    (simp [spinSign]; field_simp [hs_ne]; nlinarith [hsq])

private lemma comm_M1_M2 (J : ℝ) : Commute (invM1 J) invM2 := by
  show invM1 J * invM2 = invM2 * invM1 J
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [invM1, invM2, rPlus, rMinus, pPlus, pMinus, swapBoth, kDimer, zzMat,
    Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> cases a' <;> cases b' <;> (simp [spinSign]; ring)

private lemma comm_M1_M3 (J : ℝ) : Commute (invM1 J) invM3 := by
  show invM1 J * invM3 = invM3 * invM1 J
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [invM1, invM3, rPlus, pPlus, pMinus, swapBoth, kDimer,
    Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp [spinSign]

private lemma comm_M2_M3 : Commute invM2 invM3 := by
  show invM2 * invM3 = invM3 * invM2
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [invM2, invM3, rMinus, pPlus, pMinus, swapBoth, zzMat,
    Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp [spinSign]

private lemma neg_b_bond2Q_decomp (b J : ℝ) :
    let s := Real.sqrt (1 + 4 * J ^ 2)
    (-b) • bond2Q J =
      ((-2 * b - b * s - 2 * b * J) • (1 : Matrix PairCfg PairCfg ℝ) +
       (b * s - 2 * b * J) • invM3) +
      ((2 * b * s) • invM1 J + (4 * b * J) • invM2) := by
  have hs_ne : Real.sqrt (1 + 4 * J ^ 2) ≠ 0 := (sqrt_pos_1_4J2 J).ne'
  ext ⟨a, b'⟩ ⟨c, d⟩
  simp only [bond2Q, invM1, invM2, invM3, rPlus, rMinus, pPlus, pMinus, swapBoth, kDimer, zzMat,
    Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b' <;> cases c <;> cases d <;>
    (simp [spinSign]; field_simp [hs_ne]; ring)

private lemma trace_one_pair : Matrix.trace (1 : Matrix PairCfg PairCfg ℝ) = 4 := by
  simp [Matrix.trace]

private lemma trace_invM3 : Matrix.trace invM3 = 0 := by
  simp [invM3, swapBoth, Matrix.trace]

private lemma trace_invM1 (J : ℝ) : Matrix.trace (invM1 J) = 2 := by
  simp [invM1, rPlus, pPlus, pMinus, swapBoth, kDimer, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, spinSign]
  ring

private lemma trace_invM2 : Matrix.trace invM2 = 2 := by
  simp [invM2, rMinus, pPlus, pMinus, swapBoth, zzMat, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, spinSign]
  ring

private lemma trace_invM12 (J : ℝ) : Matrix.trace (invM1 J * invM2) = 0 := by
  simp [invM1, invM2, rPlus, rMinus, pPlus, pMinus, swapBoth, kDimer, zzMat, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type, spinSign]
  ring

private lemma trace_invM31 (J : ℝ) : Matrix.trace (invM3 * invM1 J) = -2 := by
  simp [invM3, invM1, rPlus, pPlus, pMinus, swapBoth, kDimer, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, spinSign]
  ring

private lemma trace_invM32 : Matrix.trace (invM3 * invM2) = 2 := by
  simp [invM3, invM2, rMinus, pPlus, pMinus, swapBoth, zzMat, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, spinSign]
  ring

private lemma trace_invM312 (J : ℝ) : Matrix.trace (invM3 * (invM1 J * invM2)) = 0 := by
  simp [invM3, invM1, invM2, rPlus, rMinus, pPlus, pMinus, swapBoth, kDimer, zzMat, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type, spinSign]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Exact thermal partition function of the two-qubit dimer Hamiltonian `bond2Q J`. -/
theorem matZ_bond2Q (b J : ℝ) :
    matZ (bond2Q J) (bond2Q_isHermitian J) b = F_bond b J := by
  let _ := Matrix.linftyOpNormedRing (n := PairCfg) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := PairCfg) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := PairCfg) (R := ℚ) (α := ℝ)
  rw [← trace_exp_eq_matZ (bond2Q J) (bond2Q_isHermitian J) b]
  set s := Real.sqrt (1 + 4 * J ^ 2)
  set c0 := -2 * b - b * s - 2 * b * J
  set c3 := b * s - 2 * b * J
  set c1 := 2 * b * s
  set c2 := 4 * b * J
  rw [neg_b_bond2Q_decomp b J]
  have hcomm_0_3 : Commute (c0 • (1 : Matrix PairCfg PairCfg ℝ)) (c3 • invM3) :=
    Commute.smul_left (Commute.smul_right (Commute.one_left _) _) _
  have hcomm_1_2 : Commute (c1 • invM1 J) (c2 • invM2) :=
    Commute.smul_left (Commute.smul_right (comm_M1_M2 J) _) _
  have hcomm_13 : Commute (c3 • invM3) (c1 • invM1 J) :=
    Commute.smul_left (Commute.smul_right (comm_M1_M3 J).symm _) _
  have hcomm_23 : Commute (c3 • invM3) (c2 • invM2) :=
    Commute.smul_left (Commute.smul_right comm_M2_M3.symm _) _
  have hcomm_left_right :
      Commute (c0 • (1 : Matrix PairCfg PairCfg ℝ) + c3 • invM3)
              (c1 • invM1 J + c2 • invM2) := by
    refine Commute.add_left ?_ ?_
    · exact Commute.smul_left (Commute.one_left _) _
    · exact Commute.add_right hcomm_13 hcomm_23
  rw [NormedSpace.exp_add_of_commute hcomm_left_right,
      NormedSpace.exp_add_of_commute hcomm_0_3,
      NormedSpace.exp_add_of_commute hcomm_1_2]
  have hexp0 : NormedSpace.exp (c0 • (1 : Matrix PairCfg PairCfg ℝ)) =
      Real.exp c0 • (1 : Matrix PairCfg PairCfg ℝ) := by
    have h1sq : (1 : Matrix PairCfg PairCfg ℝ) * 1 = 1 := Matrix.one_mul 1
    rw [exp_involutive h1sq c0, ← add_smul, Real.cosh_add_sinh]
  rw [hexp0, exp_involutive invM3_sq c3, exp_involutive (invM1_sq J) c1,
      exp_involutive invM2_sq c2]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have htr : Matrix.trace
      ((Real.cosh c3 • (1 : Matrix PairCfg PairCfg ℝ) + Real.sinh c3 • invM3) *
       ((Real.cosh c1 • 1 + Real.sinh c1 • invM1 J) *
        (Real.cosh c2 • 1 + Real.sinh c2 • invM2))) =
      2 * (Real.cosh c3 + Real.sinh c3) * Real.cosh c1 * (Real.cosh c2 + Real.sinh c2) +
      2 * (Real.cosh c3 - Real.sinh c3) * (Real.cosh c1 + Real.sinh c1) * Real.cosh c2 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      trace_one_pair, trace_invM3, trace_invM1, trace_invM2, trace_invM12,
      trace_invM31, trace_invM32, trace_invM312]
    ring
  rw [htr]
  have hcs3 : Real.cosh c3 + Real.sinh c3 = Real.exp c3 := Real.cosh_add_sinh c3
  have hcm3 : Real.cosh c3 - Real.sinh c3 = Real.exp (-c3) := Real.cosh_sub_sinh c3
  have hcs1 : Real.cosh c1 + Real.sinh c1 = Real.exp c1 := Real.cosh_add_sinh c1
  have hcs2 : Real.cosh c2 + Real.sinh c2 = Real.exp c2 := Real.cosh_add_sinh c2
  rw [hcs3, hcm3, hcs1, hcs2]
  unfold F_bond
  have hterm1 : Real.exp c0 * (2 * Real.exp c3 * Real.cosh c1 * Real.exp c2) =
      Real.exp (2 * b * (s - 1)) + Real.exp (-2 * b * (s + 1)) := by
    rw [Real.cosh_eq]
    have hmul : Real.exp c0 * (2 * Real.exp c3 * ((Real.exp c1 + Real.exp (-c1)) / 2) * Real.exp c2) =
        Real.exp c0 * Real.exp c3 * Real.exp c2 * Real.exp c1 +
        Real.exp c0 * Real.exp c3 * Real.exp c2 * Real.exp (-c1) := by ring
    rw [hmul]
    simp only [← Real.exp_add]
    congr 1 <;> (dsimp [c0, c1, c2, c3]; congr 1; ring)
  have hterm2 : Real.exp c0 * (2 * Real.exp (-c3) * Real.exp c1 * Real.cosh c2) =
      2 * Real.exp (-2 * b) * Real.cosh (4 * b * J) := by
    have hmul : Real.exp c0 * (2 * Real.exp (-c3) * Real.exp c1 * Real.cosh c2) =
        2 * (Real.exp c0 * Real.exp (-c3) * Real.exp c1) * Real.cosh c2 := by ring
    rw [hmul, ← Real.exp_add, ← Real.exp_add]
    have hexp_eq : c0 + -c3 + c1 = -2 * b := by dsimp [c0, c1, c3]; ring
    rw [hexp_eq]
  calc Real.exp c0 *
        (2 * Real.exp c3 * Real.cosh c1 * Real.exp c2 +
         2 * Real.exp (-c3) * Real.exp c1 * Real.cosh c2)
      = Real.exp c0 * (2 * Real.exp c3 * Real.cosh c1 * Real.exp c2) +
        Real.exp c0 * (2 * Real.exp (-c3) * Real.exp c1 * Real.cosh c2) := by ring
    _ = (Real.exp (2 * b * (s - 1)) + Real.exp (-2 * b * (s + 1))) +
        2 * Real.exp (-2 * b) * Real.cosh (4 * b * J) := by rw [hterm1, hterm2]

/-! ## 2. Exact 2×2 Midpoint Decomposition & Tensor Trace -/

/-- Reindexing `Cfg 2 2 ≃ PairCfg × PairCfg` by grouping the two horizontal rows. -/
private def rowSplitEquiv : Cfg 2 2 ≃ PairCfg × PairCfg where
  toFun u := ((u (0, 0), u (1, 0)), (u (0, 1), u (1, 1)))
  invFun p v :=
    if v.2 = 0 then (if v.1 = 0 then p.1.1 else p.1.2)
    else (if v.1 = 0 then p.2.1 else p.2.2)
  left_inv u := by
    funext ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

/-- Reindexing `Cfg 2 2 ≃ PairCfg × PairCfg` by grouping the two vertical columns. -/
private def colSplitEquiv : Cfg 2 2 ≃ PairCfg × PairCfg where
  toFun u := ((u (0, 0), u (0, 1)), (u (1, 0), u (1, 1)))
  invFun p v :=
    if v.1 = 0 then (if v.2 = 0 then p.1.1 else p.1.2)
    else (if v.2 = 0 then p.2.1 else p.2.2)
  left_inv u := by
    funext ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

/-- Tensor-sum Hamiltonian `A ⊗ I + I ⊗ B` on `α × β`. -/
private def kronSum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) : Matrix (α × β) (α × β) ℝ :=
  Matrix.of fun u v =>
    (if u.2 = v.2 then A u.1 v.1 else 0) + (if u.1 = v.1 then B u.2 v.2 else 0)

private lemma kronSum_isHermitian {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Matrix α α ℝ} {B : Matrix β β ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (kronSum A B).IsHermitian := by
  ext ⟨a1, b1⟩ ⟨a2, b2⟩
  simp only [Matrix.conjTranspose_apply, star_trivial, kronSum, Matrix.of_apply]
  have ha : A a2 a1 = A a1 a2 := by
    have := congrFun (congrFun hA a1) a2
    simpa [Matrix.conjTranspose_apply] using this
  have hb : B b2 b1 = B b1 b2 := by
    have := congrFun (congrFun hB b1) b2
    simpa [Matrix.conjTranspose_apply] using this
  by_cases h1 : a1 = a2 <;> by_cases h2 : b1 = b2 <;> simp [h1, h2, eq_comm, ha, hb]

set_option backward.isDefEq.respectTransparency false in
/-- Exact partition function factorization `matZ (A ⊗ I + I ⊗ B) b = matZ A b * matZ B b`. -/
private lemma matZ_kronSum {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℝ) (hA : A.IsHermitian) (B : Matrix β β ℝ) (hB : B.IsHermitian) (b : ℝ) :
    matZ (kronSum A B) (kronSum_isHermitian hA hB) b = matZ A hA b * matZ B hB b := by
  -- Express via matrix exponentials using the left/right embedding ring homomorphisms.
  let _ := Matrix.linftyOpNormedRing (n := α) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := α) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := α) (R := ℚ) (α := ℝ)
  let _ := Matrix.linftyOpNormedRing (n := β) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := β) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := β) (R := ℚ) (α := ℝ)
  let _ := Matrix.linftyOpNormedRing (n := α × β) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := α × β) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := α × β) (R := ℚ) (α := ℝ)
  rw [← trace_exp_eq_matZ (kronSum A B) (kronSum_isHermitian hA hB) b,
      ← trace_exp_eq_matZ A hA b, ← trace_exp_eq_matZ B hB b]
  let embL : Matrix α α ℝ →ₗ[ℝ] Matrix (α × β) (α × β) ℝ :=
    { toFun := fun M => Matrix.of fun u v => if u.2 = v.2 then M u.1 v.1 else 0
      map_add' := fun M N => by ext ⟨a1, b1⟩ ⟨a2, b2⟩; by_cases h : b1 = b2 <;> simp [h]
      map_smul' := fun r M => by ext ⟨a1, b1⟩ ⟨a2, b2⟩; by_cases h : b1 = b2 <;> simp [h] }
  let embR : Matrix β β ℝ →ₗ[ℝ] Matrix (α × β) (α × β) ℝ :=
    { toFun := fun N => Matrix.of fun u v => if u.1 = v.1 then N u.2 v.2 else 0
      map_add' := fun M N => by ext ⟨a1, b1⟩ ⟨a2, b2⟩; by_cases h : a1 = a2 <;> simp [h]
      map_smul' := fun r M => by ext ⟨a1, b1⟩ ⟨a2, b2⟩; by_cases h : a1 = a2 <;> simp [h] }
  have hembL_one : embL 1 = 1 := by
    ext ⟨a1, b1⟩ ⟨a2, b2⟩
    by_cases h1 : a1 = a2 <;> by_cases h2 : b1 = b2 <;> simp [embL, Matrix.one_apply, h1, h2]
  have hembR_one : embR 1 = 1 := by
    ext ⟨a1, b1⟩ ⟨a2, b2⟩
    by_cases h1 : a1 = a2 <;> by_cases h2 : b1 = b2 <;> simp [embR, Matrix.one_apply, h1, h2]
  have hembL_mul : ∀ M N, embL (M * N) = embL M * embL N := fun M N => by
    ext ⟨a1, b1⟩ ⟨a2, b2⟩
    simp only [embL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    by_cases h : b1 = b2
    · subst h; simp
    · simp only [h, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : b1 = y
      · subst hy; simp [h]
      · simp [hy]
  have hembR_mul : ∀ M N, embR (M * N) = embR M * embR N := fun M N => by
    ext ⟨a1, b1⟩ ⟨a2, b2⟩
    simp only [embR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    by_cases h : a1 = a2
    · subst h; simp
    · simp only [h, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hx : a1 = x
      · subst hx; simp [h]
      · simp [hx]
  have hembL_pow : ∀ M (k : ℕ), embL (M ^ k) = (embL M) ^ k := fun M k => by
    induction k with
    | zero => simpa using hembL_one
    | succ k ih => rw [pow_succ, pow_succ, hembL_mul, ih]
  have hembR_pow : ∀ N (k : ℕ), embR (N ^ k) = (embR N) ^ k := fun N k => by
    induction k with
    | zero => simpa using hembR_one
    | succ k ih => rw [pow_succ, pow_succ, hembR_mul, ih]
  have hembL_exp : ∀ M, NormedSpace.exp (embL M) = embL (NormedSpace.exp M) := fun M => by
    have hcont : Continuous embL := LinearMap.continuous_of_finiteDimensional embL
    have h1 := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) M).map embL.toAddMonoidHom hcont
    have hcomp : (embL.toAddMonoidHom ∘ fun k => NormedSpace.expSeries ℝ (Matrix α α ℝ) k fun _ => M) =
        fun k => NormedSpace.expSeries ℝ (Matrix (α × β) (α × β) ℝ) k fun _ => embL M := by
      funext k
      change embL (NormedSpace.expSeries ℝ (Matrix α α ℝ) k fun _ => M) =
        NormedSpace.expSeries ℝ (Matrix (α × β) (α × β) ℝ) k fun _ => embL M
      rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq,
        embL.map_smul, hembL_pow]
    rw [hcomp] at h1
    exact (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (embL M)).unique h1
  have hembR_exp : ∀ N, NormedSpace.exp (embR N) = embR (NormedSpace.exp N) := fun N => by
    have hcont : Continuous embR := LinearMap.continuous_of_finiteDimensional embR
    have h1 := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) N).map embR.toAddMonoidHom hcont
    have hcomp : (embR.toAddMonoidHom ∘ fun k => NormedSpace.expSeries ℝ (Matrix β β ℝ) k fun _ => N) =
        fun k => NormedSpace.expSeries ℝ (Matrix (α × β) (α × β) ℝ) k fun _ => embR N := by
      funext k
      change embR (NormedSpace.expSeries ℝ (Matrix β β ℝ) k fun _ => N) =
        NormedSpace.expSeries ℝ (Matrix (α × β) (α × β) ℝ) k fun _ => embR N
      rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq,
        embR.map_smul, hembR_pow]
    rw [hcomp] at h1
    exact (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (embR N)).unique h1
  have hcomm : Commute (embL ((-b) • A)) (embR ((-b) • B)) := by
    show embL ((-b) • A) * embR ((-b) • B) = embR ((-b) • B) * embL ((-b) • A)
    ext ⟨a1, b1⟩ ⟨a2, b2⟩
    simp only [embL, embR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    simp [mul_comm]
  have hsplit : (-b) • kronSum A B = embL ((-b) • A) + embR ((-b) • B) := by
    ext ⟨a1, b1⟩ ⟨a2, b2⟩
    simp only [kronSum, embL, embR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm, hembL_exp, hembR_exp]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, embL, embR, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.of_apply, Fintype.sum_prod_type]
  simp [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Pullback of a Hermitian matrix along an index equivalence preserves `matZ`. -/
private lemma matZ_reindex {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (M : Matrix β β ℝ) (hM : M.IsHermitian) (b : ℝ) :
    let M' : Matrix α α ℝ := Matrix.submatrix M e e
    have hM' : M'.IsHermitian := by
      ext u v
      have := congrFun (congrFun hM (e u)) (e v)
      simpa [M', Matrix.submatrix_apply, Matrix.conjTranspose_apply] using this
    matZ M' hM' b = matZ M hM b := by
  intro M' hM'
  let _ := Matrix.linftyOpNormedRing (n := α) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := α) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := α) (R := ℚ) (α := ℝ)
  let _ := Matrix.linftyOpNormedRing (n := β) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := β) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := β) (R := ℚ) (α := ℝ)
  rw [← trace_exp_eq_matZ M' hM' b, ← trace_exp_eq_matZ M hM b]
  let φ : Matrix β β ℝ →ₗ[ℝ] Matrix α α ℝ :=
    { toFun := fun X => Matrix.submatrix X e e
      map_add' := fun X Y => by ext u v; rfl
      map_smul' := fun r X => by ext u v; rfl }
  have hφ_one : φ 1 = 1 := by
    ext u v; simp [φ, Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  have hφ_mul : ∀ X Y, φ (X * Y) = φ X * φ Y := fun X Y => by
    ext u v
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, Matrix.mul_apply]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  have hφ_pow : ∀ X (k : ℕ), φ (X ^ k) = (φ X) ^ k := fun X k => by
    induction k with
    | zero => simpa using hφ_one
    | succ k ih => rw [pow_succ, pow_succ, hφ_mul, ih]
  have hφ_exp : NormedSpace.exp (φ ((-b) • M)) = φ (NormedSpace.exp ((-b) • M)) := by
    have hcont : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
    have h1 := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ((-b) • M)).map φ.toAddMonoidHom hcont
    have h1' : HasSum (fun k => NormedSpace.expSeries ℝ (Matrix α α ℝ) k fun _ => φ ((-b) • M))
        (φ (NormedSpace.exp ((-b) • M))) := by
      refine h1.congr_fun fun k => ?_
      symm
      change φ (NormedSpace.expSeries ℝ (Matrix β β ℝ) k fun _ => (-b) • M) =
        NormedSpace.expSeries ℝ (Matrix α α ℝ) k fun _ => φ ((-b) • M)
      rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, φ.map_smul, hφ_pow]
    exact (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (φ ((-b) • M))).unique h1'
  have hM'_eq : (-b) • M' = φ ((-b) • M) := by ext u v; rfl
  rw [hM'_eq, hφ_exp]
  simp only [Matrix.trace, Matrix.diag_apply, φ, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.submatrix_apply]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Horizontal dimer-pair Hamiltonian on `Cfg 2 2`. -/
noncomputable def dimerAx (Jx : ℝ) : Matrix (Cfg 2 2) (Cfg 2 2) ℝ :=
  Matrix.submatrix (kronSum (bond2Q Jx) (bond2Q Jx)) rowSplitEquiv rowSplitEquiv

/-- Vertical dimer-pair Hamiltonian on `Cfg 2 2`. -/
noncomputable def dimerAy (Jy : ℝ) : Matrix (Cfg 2 2) (Cfg 2 2) ℝ :=
  Matrix.submatrix (kronSum (bond2Q Jy) (bond2Q Jy)) colSplitEquiv colSplitEquiv

private lemma dimerAx_isHermitian (Jx : ℝ) : (dimerAx Jx).IsHermitian := by
  ext u v
  have h := congrFun (congrFun (kronSum_isHermitian (bond2Q_isHermitian Jx) (bond2Q_isHermitian Jx))
    (rowSplitEquiv u)) (rowSplitEquiv v)
  simpa [dimerAx, Matrix.submatrix_apply, Matrix.conjTranspose_apply] using h

private lemma dimerAy_isHermitian (Jy : ℝ) : (dimerAy Jy).IsHermitian := by
  ext u v
  have h := congrFun (congrFun (kronSum_isHermitian (bond2Q_isHermitian Jy) (bond2Q_isHermitian Jy))
    (colSplitEquiv u)) (colSplitEquiv v)
  simpa [dimerAy, Matrix.submatrix_apply, Matrix.conjTranspose_apply] using h

/-- **Exact 2×2 midpoint identity**: `H_2d 2 2 Jx Jy + 4 • 1 = (1/2) • dimerAx Jx + (1/2) • dimerAy Jy`. -/
theorem H_2d_2x2_midpoint (Jx Jy : ℝ) :
    H_2d 2 2 Jx Jy + (4 : ℝ) • (1 : Matrix (Cfg 2 2) (Cfg 2 2) ℝ) =
      (1 - (1 / 2 : ℝ)) • dimerAx Jx + (1 / 2 : ℝ) • dimerAy Jy := by
  ext u v
  have hr0 : finRotate 2 0 = 1 := by decide
  have hr1 : finRotate 2 1 = 0 := by decide
  -- Decompose `u, v : Cfg 2 2` into their 4 boolean values
  have hpot : potZ 2 2 Jx Jy u =
      -(2 * Jx * spinSign (u (0, 0)) * spinSign (u (1, 0)) +
        2 * Jx * spinSign (u (0, 1)) * spinSign (u (1, 1)) +
        2 * Jy * spinSign (u (0, 0)) * spinSign (u (0, 1)) +
        2 * Jy * spinSign (u (1, 0)) * spinSign (u (1, 1))) := by
    unfold potZ
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, hr0, hr1]
    ring
  have hX : H_X 2 2 u v =
      -(opX 2 2 (0, 0) u v + opX 2 2 (1, 0) u v + opX 2 2 (0, 1) u v + opX 2 2 (1, 1) u v) := by
    unfold H_X
    simp only [Matrix.neg_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply]
    ring
  have heq_iff : u = v ↔
      u (0, 0) = v (0, 0) ∧ u (1, 0) = v (1, 0) ∧ u (0, 1) = v (0, 1) ∧ u (1, 1) = v (1, 1) := by
    constructor
    · intro h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩
    · rintro ⟨h00, h10, h01, h11⟩
      funext ⟨x, y⟩; fin_cases x <;> fin_cases y <;> assumption
  have hflip : ∀ w : Site 2 2, opX 2 2 w u v = if flipSite u w = v then 1 else 0 :=
    fun w => by simp [opX, eq_comm]
  have hf00 : flipSite u (0, 0) = v ↔
      (!u (0, 0)) = v (0, 0) ∧ u (1, 0) = v (1, 0) ∧ u (0, 1) = v (0, 1) ∧ u (1, 1) = v (1, 1) := by
    constructor
    · intro h
      refine ⟨by simpa [flipSite] using congrFun h (0, 0),
              by simpa [flipSite] using congrFun h (1, 0),
              by simpa [flipSite] using congrFun h (0, 1),
              by simpa [flipSite] using congrFun h (1, 1)⟩
    · rintro ⟨h00, h10, h01, h11⟩
      funext ⟨x, y⟩; fin_cases x <;> fin_cases y <;> simp [flipSite, h00, h10, h01, h11]
  have hf10 : flipSite u (1, 0) = v ↔
      u (0, 0) = v (0, 0) ∧ (!u (1, 0)) = v (1, 0) ∧ u (0, 1) = v (0, 1) ∧ u (1, 1) = v (1, 1) := by
    constructor
    · intro h
      refine ⟨by simpa [flipSite] using congrFun h (0, 0),
              by simpa [flipSite] using congrFun h (1, 0),
              by simpa [flipSite] using congrFun h (0, 1),
              by simpa [flipSite] using congrFun h (1, 1)⟩
    · rintro ⟨h00, h10, h01, h11⟩
      funext ⟨x, y⟩; fin_cases x <;> fin_cases y <;> simp [flipSite, h00, h10, h01, h11]
  have hf01 : flipSite u (0, 1) = v ↔
      u (0, 0) = v (0, 0) ∧ u (1, 0) = v (1, 0) ∧ (!u (0, 1)) = v (0, 1) ∧ u (1, 1) = v (1, 1) := by
    constructor
    · intro h
      refine ⟨by simpa [flipSite] using congrFun h (0, 0),
              by simpa [flipSite] using congrFun h (1, 0),
              by simpa [flipSite] using congrFun h (0, 1),
              by simpa [flipSite] using congrFun h (1, 1)⟩
    · rintro ⟨h00, h10, h01, h11⟩
      funext ⟨x, y⟩; fin_cases x <;> fin_cases y <;> simp [flipSite, h00, h10, h01, h11]
  have hf11 : flipSite u (1, 1) = v ↔
      u (0, 0) = v (0, 0) ∧ u (1, 0) = v (1, 0) ∧ u (0, 1) = v (0, 1) ∧ (!u (1, 1)) = v (1, 1) := by
    constructor
    · intro h
      refine ⟨by simpa [flipSite] using congrFun h (0, 0),
              by simpa [flipSite] using congrFun h (1, 0),
              by simpa [flipSite] using congrFun h (0, 1),
              by simpa [flipSite] using congrFun h (1, 1)⟩
    · rintro ⟨h00, h10, h01, h11⟩
      funext ⟨x, y⟩; fin_cases x <;> fin_cases y <;> simp [flipSite, h00, h10, h01, h11]
  simp only [H_2d, H_Z, hX, hflip, dimerAx, dimerAy, kronSum, bond2Q, rowSplitEquiv, colSplitEquiv,
    Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.submatrix_apply, Matrix.of_apply, Equiv.coe_fn_mk, smul_eq_mul,
    hpot, heq_iff, hf00, hf10, hf01, hf11, Prod.mk.injEq]
  generalize u (0, 0) = a00
  generalize u (1, 0) = a10
  generalize u (0, 1) = a01
  generalize u (1, 1) = a11
  generalize v (0, 0) = b00
  generalize v (1, 0) = b10
  generalize v (0, 1) = b01
  generalize v (1, 1) = b11
  cases a00 <;> cases a10 <;> cases a01 <;> cases a11 <;>
    cases b00 <;> cases b10 <;> cases b01 <;> cases b11 <;>
    (simp [spinSign]; try ring)

set_option backward.isDefEq.respectTransparency false in
/-- Exact shift identity: `Z_2d lx ly Jx Jy a b = matZ (H_2d lx ly Jx Jy + (a * lx * ly) • 1) _ b`. -/
lemma Z_2d_eq_matZ_shift (lx ly : ℕ) (Jx Jy a b : ℝ)
    (hHs : (H_2d lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)).IsHermitian) :
    Z_2d lx ly Jx Jy a b =
      matZ (H_2d lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) hHs b := by
  let _ := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℚ) (α := ℝ)
  rw [Z_2d, ← trace_exp_eq_matZ (H_2d lx ly Jx Jy) (H_2d_isHermitian lx ly Jx Jy) b,
      ← trace_exp_eq_matZ _ hHs b]
  have hsplit : (-b) • (H_2d lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) =
      (-b) • H_2d lx ly Jx Jy + (-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := by
    ext u v
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((-b) • H_2d lx ly Jx Jy)
      ((-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) :=
    Commute.smul_left (Commute.smul_right (Commute.one_right _) _) _
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm]
  have hexp1 : NormedSpace.exp ((-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) =
      Real.exp (-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := by
    have h1sq : (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ) * 1 = 1 := Matrix.one_mul 1
    rw [exp_involutive h1sq (-b * a * (lx * ly : ℝ)), ← add_smul, Real.cosh_add_sinh]
  rw [hexp1, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- **2×2 upper bound**: `Z_2d 2 2 Jx Jy 1 b ≤ F_bond b Jx * F_bond b Jy` for all `Jx, Jy, b`. -/
theorem Z_2d_2x2_le (Jx Jy b : ℝ) :
    Z_2d 2 2 Jx Jy 1 b ≤ F_bond b Jx * F_bond b Jy := by
  have hHs : (H_2d 2 2 Jx Jy + (1 * ((2 : ℕ) * (2 : ℕ) : ℝ)) • (1 : Matrix (Cfg 2 2) (Cfg 2 2) ℝ)).IsHermitian := by
    refine (H_2d_isHermitian 2 2 Jx Jy).add ?_
    ext u v
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  have hEqShift : H_2d 2 2 Jx Jy + (1 * ((2 : ℕ) * (2 : ℕ) : ℝ)) • (1 : Matrix (Cfg 2 2) (Cfg 2 2) ℝ) =
      (1 - (1 / 2 : ℝ)) • dimerAx Jx + (1 / 2 : ℝ) • dimerAy Jy := by
    have h4 : (1 * ((2 : ℕ) * (2 : ℕ) : ℝ)) = 4 := by norm_num
    rw [h4, H_2d_2x2_midpoint Jx Jy]
  have hHmid : ((1 - (1 / 2 : ℝ)) • dimerAx Jx + (1 / 2 : ℝ) • dimerAy Jy).IsHermitian :=
    hEqShift ▸ hHs
  rw [Z_2d_eq_matZ_shift 2 2 Jx Jy 1 b hHs]
  have hmatZ_eq : matZ (H_2d 2 2 Jx Jy + (1 * ((2 : ℕ) * (2 : ℕ) : ℝ)) • 1) hHs b =
      matZ ((1 - (1 / 2 : ℝ)) • dimerAx Jx + (1 / 2 : ℝ) • dimerAy Jy) hHmid b := by
    congr 1
  rw [hmatZ_eq]
  have hconv := matZ_convex_combo_le (dimerAx Jx) (dimerAy Jy)
    (dimerAx_isHermitian Jx) (dimerAy_isHermitian Jy)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hHmid b
  have hAx : matZ (dimerAx Jx) (dimerAx_isHermitian Jx) b = (F_bond b Jx) ^ 2 := by
    have h1 := matZ_reindex rowSplitEquiv (kronSum (bond2Q Jx) (bond2Q Jx))
      (kronSum_isHermitian (bond2Q_isHermitian Jx) (bond2Q_isHermitian Jx)) b
    rw [matZ_kronSum (bond2Q Jx) (bond2Q_isHermitian Jx) (bond2Q Jx) (bond2Q_isHermitian Jx) b,
      matZ_bond2Q b Jx, ← sq] at h1
    exact h1
  have hAy : matZ (dimerAy Jy) (dimerAy_isHermitian Jy) b = (F_bond b Jy) ^ 2 := by
    have h1 := matZ_reindex colSplitEquiv (kronSum (bond2Q Jy) (bond2Q Jy))
      (kronSum_isHermitian (bond2Q_isHermitian Jy) (bond2Q_isHermitian Jy)) b
    rw [matZ_kronSum (bond2Q Jy) (bond2Q_isHermitian Jy) (bond2Q Jy) (bond2Q_isHermitian Jy) b,
      matZ_bond2Q b Jy, ← sq] at h1
    exact h1
  rw [hAx, hAy] at hconv
  have hpow : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x hx => by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    norm_num
  have h12 : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  calc matZ ((1 - (1 / 2 : ℝ)) • dimerAx Jx + (1 / 2 : ℝ) • dimerAy Jy) hHmid b
      ≤ ((F_bond b Jx) ^ 2) ^ (1 - (1 / 2 : ℝ)) * ((F_bond b Jy) ^ 2) ^ (1 / 2 : ℝ) := hconv
    _ = F_bond b Jx * F_bond b Jy := by
        rw [h12, hpow _ (F_bond_pos b Jx), hpow _ (F_bond_pos b Jy)]

/-! ## 3. Symbolic All-Ones Rayleigh Lower Bound `1 ≤ Z_2d lx ly Jx Jy 1 b` -/

/-- On any finite grid with `n ≥ 2`, `finRotate n x ≠ x`. -/
private lemma finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (x : Fin n) : finRotate n x ≠ x := by
  cases n with
  | zero => omega
  | succ m =>
    intro h
    have hv := congrArg Fin.val h
    by_cases hlt : x.val < m
    · have h1 : finRotate (m + 1) x = ⟨x.val + 1, by omega⟩ := by
        simpa using finRotate_of_lt (k := x) hlt
      rw [h1] at hv
      dsimp at hv
      omega
    · have hx : x = Fin.last m := by ext; simp; omega
      rw [hx, finRotate_last] at hv
      simp at hv
      omega

/-- Summing `spinSign (u w₁) * spinSign (u w₂)` over all configurations is zero whenever `w₁ ≠ w₂`. -/
private lemma sum_spinSign_mul_eq_zero {lx ly : ℕ} {w₁ w₂ : Site lx ly} (hne : w₁ ≠ w₂) :
    ∑ u : Cfg lx ly, spinSign (u w₁) * spinSign (u w₂) = 0 := by
  have hinv : ∀ u : Cfg lx ly, flipSite (flipSite u w₁) w₁ = u := fun u => by
    funext w; by_cases h : w = w₁ <;> simp [flipSite, h]
  let e : Cfg lx ly ≃ Cfg lx ly :=
    { toFun := fun u => flipSite u w₁
      invFun := fun u => flipSite u w₁
      left_inv := hinv
      right_inv := hinv }
  have hneg : ∑ u : Cfg lx ly, spinSign (u w₁) * spinSign (u w₂) =
      -(∑ u : Cfg lx ly, spinSign (u w₁) * spinSign (u w₂)) := by
    calc ∑ u : Cfg lx ly, spinSign (u w₁) * spinSign (u w₂)
        = ∑ u : Cfg lx ly, spinSign (e u w₁) * spinSign (e u w₂) :=
          (Fintype.sum_equiv e _ _ fun _ => rfl).symm
      _ = ∑ u : Cfg lx ly, -(spinSign (u w₁) * spinSign (u w₂)) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          have h1 : e u w₁ = !u w₁ := by simp [e, flipSite]
          have h2 : e u w₂ = u w₂ := by simp [e, flipSite, hne.symm]
          rw [h1, h2]
          cases u w₁ <;> cases u w₂ <;> simp [spinSign]
      _ = -(∑ u : Cfg lx ly, spinSign (u w₁) * spinSign (u w₂)) := by
          rw [Finset.sum_neg_distrib]
  linarith

/-- **Symbolic all-ones Rayleigh lower bound**:
for every `lx ≥ 2`, `ly ≥ 2`, arbitrary `Jx, Jy`, and `b > 0`, `1 ≤ Z_2d lx ly Jx Jy 1 b`. -/
theorem one_le_Z_2d_shift_one {lx ly : ℕ} (hlx : 2 ≤ lx) (hly : 2 ≤ ly)
    (Jx Jy : ℝ) {b : ℝ} (hb : 0 < b) :
    1 ≤ Z_2d lx ly Jx Jy 1 b := by
  let v : Cfg lx ly → ℝ := fun _ => 1
  have hv_dot : dotProduct v v = (Fintype.card (Cfg lx ly) : ℝ) := by
    simp [v, dotProduct]
  have hv_pos : 0 < dotProduct v v := by
    rw [hv_dot]
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hHZ : dotProduct v ((H_Z lx ly Jx Jy).mulVec v) = 0 := by
    simp only [H_Z, dotProduct, v, one_mul, Matrix.mulVec_diagonal, mul_one, potZ]
    rw [Finset.sum_neg_distrib, neg_eq_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun w _ => ?_
    simp only [Finset.sum_add_distrib]
    have hx : (∑ u : Cfg lx ly, Jx * spinSign (u w) * spinSign (u (finRotate lx w.1, w.2))) = 0 := by
      have hne : w ≠ (finRotate lx w.1, w.2) := fun h =>
        finRotate_ne_self hlx w.1 (congrArg Prod.fst h).symm
      calc ∑ u : Cfg lx ly, Jx * spinSign (u w) * spinSign (u (finRotate lx w.1, w.2))
          = Jx * ∑ u : Cfg lx ly, spinSign (u w) * spinSign (u (finRotate lx w.1, w.2)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
        _ = 0 := by rw [sum_spinSign_mul_eq_zero hne, mul_zero]
    have hy : (∑ u : Cfg lx ly, Jy * spinSign (u w) * spinSign (u (w.1, finRotate ly w.2))) = 0 := by
      have hne : w ≠ (w.1, finRotate ly w.2) := fun h =>
        finRotate_ne_self hly w.2 (congrArg Prod.snd h).symm
      calc ∑ u : Cfg lx ly, Jy * spinSign (u w) * spinSign (u (w.1, finRotate ly w.2))
          = Jy * ∑ u : Cfg lx ly, spinSign (u w) * spinSign (u (w.1, finRotate ly w.2)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
        _ = 0 := by rw [sum_spinSign_mul_eq_zero hne, mul_zero]
    linarith
  have hHX : dotProduct v ((H_X lx ly).mulVec v) = -((lx * ly : ℝ) * (Fintype.card (Cfg lx ly) : ℝ)) := by
    simp only [H_X, Matrix.neg_mulVec, dotProduct_neg, Matrix.sum_mulVec, dotProduct_sum]
    have hsite : ∀ w : Site lx ly, dotProduct v ((opX lx ly w).mulVec v) = (Fintype.card (Cfg lx ly) : ℝ) := by
      intro w
      simp only [dotProduct, Matrix.mulVec, v, one_mul, mul_one, opX, Matrix.of_apply]
      simp
    simp [hsite, Fintype.card_prod, Fintype.card_fin]
  have hquad : dotProduct v ((H_2d lx ly Jx Jy).mulVec v) / dotProduct v v = -(lx * ly : ℝ) := by
    rw [H_2d, Matrix.add_mulVec, dotProduct_add, hHZ, hHX, add_zero, hv_dot]
    have hcard_ne : (Fintype.card (Cfg lx ly) : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr Fintype.card_pos).ne'
    field_simp [hcard_ne]
  have hray := exp_rayleigh_le_matZ (H_2d lx ly Jx Jy) (H_2d_isHermitian lx ly Jx Jy) hb v hv_pos
  rw [hquad] at hray
  unfold Z_2d
  have hprod := mul_le_mul_of_nonneg_left hray (Real.exp_pos (-b * 1 * (lx * ly : ℝ))).le
  have hcancel : Real.exp (-b * 1 * (lx * ly : ℝ)) * Real.exp (-b * -(lx * ly : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have h0 : -b * 1 * (lx * ly : ℝ) + -b * -(lx * ly : ℝ) = 0 := by ring
    rw [h0, Real.exp_zero]
  linarith

/-! ## 4. Pure-Kernel Rational Scalar Certificate & 2×2 Rectangle Seed -/

private theorem exp_le_frac {x : ℝ} (h : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  rw [le_div_iff₀ (by linarith)]
  simpa [← Real.exp_add] using mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg x) (Real.exp_pos x).le

private theorem cosh_le_frac {x : ℝ} (hx : |x| < 1) : Real.cosh x ≤ 1 / (1 - x ^ 2) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  rw [Real.cosh_eq]
  calc (Real.exp x + Real.exp (-x)) / 2
      ≤ (1 / (1 - x) + 1 / (1 + x)) / 2 := by
        gcongr
        · exact exp_le_frac h2
        · simpa using exp_le_frac (x := -x) (by linarith)
    _ = 1 / (1 - x ^ 2) := by
        have h3 : 0 < 1 - x ^ 2 := by nlinarith [mul_pos (sub_pos.mpr h2) (show 0 < 1 + x by linarith)]
        field_simp [(sub_pos.mpr h2).ne', (show 0 < 1 + x by linarith).ne', h3.ne']
        ring

private theorem F_bond_rational_bound {b J r q : ℝ} (hb : 0 < b) (hj : |J| ≤ r)
    (hbr : 4 * b * r < 1) (hz : 4 * b * r ^ 2 < 1) (hq : Real.exp (-2 * b) ≤ q) :
    F_bond b J ≤ 1 / (1 - 4 * b * r ^ 2) + q ^ 2 + 2 * q / (1 - (4 * b * r) ^ 2) := by
  unfold F_bond
  have hr := (abs_nonneg J).trans hj
  have hJ2 : J ^ 2 ≤ r ^ 2 := by nlinarith [sq_abs J, mul_self_le_mul_self (abs_nonneg J) hj]
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 4 * J ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (1 + 4 * J ^ 2)
  have hs1 : 1 ≤ Real.sqrt (1 + 4 * J ^ 2) := by nlinarith [sq_nonneg J]
  have hs2 : Real.sqrt (1 + 4 * J ^ 2) ≤ 1 + 2 * r ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + 4 * J ^ 2) - 1)]
  have hA := (Real.exp_le_exp.mpr
    (show 2 * b * (Real.sqrt (1 + 4 * J ^ 2) - 1) ≤ 4 * b * r ^ 2 by
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hs2)])).trans (exp_le_frac hz)
  have hB : Real.exp (-2 * b * (Real.sqrt (1 + 4 * J ^ 2) + 1)) ≤ q ^ 2 := by
    calc Real.exp (-2 * b * (Real.sqrt (1 + 4 * J ^ 2) + 1))
        ≤ Real.exp (-2 * b + (-2 * b)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hs1)])
      _ = (Real.exp (-2 * b)) ^ 2 := by rw [Real.exp_add, sq]
      _ ≤ q ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hq _
  have hC : Real.cosh (4 * b * J) ≤ 1 / (1 - (4 * b * r) ^ 2) := by
    have habs_le : |4 * b * J| ≤ 4 * b * r := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hb.le]
      nlinarith
    have hlt1 : |4 * b * J| < 1 := lt_of_le_of_lt habs_le hbr
    have hsq_le : (4 * b * J) ^ 2 ≤ (4 * b * r) ^ 2 := by
      have h1 : (4 * b * J) ^ 2 = (4 * b) ^ 2 * J ^ 2 := by ring
      have h2 : (4 * b * r) ^ 2 = (4 * b) ^ 2 * r ^ 2 := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hJ2 (sq_nonneg _)
    have hden_pos : 0 < 1 - (4 * b * r) ^ 2 := by
      have hbr_nn : 0 ≤ 4 * b * r := by positivity
      nlinarith
    exact (cosh_le_frac hlt1).trans (one_div_le_one_div_of_le hden_pos (by linarith))
  have hterm3 : 2 * Real.exp (-2 * b) * Real.cosh (4 * b * J) ≤ 2 * q / (1 - (4 * b * r) ^ 2) := by
    have h1 : 2 * Real.exp (-2 * b) ≤ 2 * q := by linarith
    have h2 : 0 ≤ 2 * q := by linarith [Real.exp_pos (-2 * b)]
    have hmul : 2 * Real.exp (-2 * b) * Real.cosh (4 * b * J) ≤ 2 * q * (1 / (1 - (4 * b * r) ^ 2)) :=
      mul_le_mul h1 hC (Real.cosh_pos _).le h2
    have hrew : 2 * q * (1 / (1 - (4 * b * r) ^ 2)) = 2 * q / (1 - (4 * b * r) ^ 2) := by ring
    linarith
  linarith

/-- Kernel-certified scalar bound: for `|J| ≤ 1/192`, `(F_bond 5 J) ^ 16 ≤ 98 / 97`. -/
theorem scalar_F5_pow16_le {J : ℝ} (hj : |J| ≤ 1 / 192) :
    (F_bond 5 J) ^ 16 ≤ 98 / 97 := by
  have hq : Real.exp (-2 * 5) ≤ (1 : ℝ) / 22000 := by
    rw [show (-2 * 5 : ℝ) = -10 by norm_num]
    apply (exp_neg_div_pow2_upper (x := 10) (by norm_num) 3 10 (by norm_num)).trans
    norm_num [Finset.sum_range_succ, Nat.factorial]
  apply (pow_le_pow_left₀ (F_bond_pos 5 J).le
    (F_bond_rational_bound (b := 5) (by norm_num) hj (by norm_num) (by norm_num) hq) 16).trans
  norm_num

/-- **Master 2×2 Rectangle Seed Theorem**:
for every `(Jx, Jy)` in the closed 2D rectangle `|Jx| ≤ 1/192, |Jy| ≤ 1/192`,
the concrete 2D transverse-field Ising partition function satisfies
`97 / 98 ≤ Z_2d 4 4 Jx Jy 1 10 / (Z_2d 2 2 Jx Jy 1 5) ^ 8`. -/
theorem ising2d_seed_2x2 {Jx Jy : ℝ} (hJx : |Jx| ≤ 1 / 192) (hJy : |Jy| ≤ 1 / 192) :
    97 / 98 ≤ Z_2d 4 4 Jx Jy 1 10 / (Z_2d 2 2 Jx Jy 1 5) ^ 8 := by
  have hFx := scalar_F5_pow16_le hJx
  have hFy := scalar_F5_pow16_le hJy
  have hprod16 : (F_bond 5 Jx * F_bond 5 Jy) ^ 16 ≤ (98 / 97 : ℝ) ^ 2 := by
    rw [mul_pow, sq]
    exact mul_le_mul hFx hFy (pow_nonneg (F_bond_pos 5 Jy).le 16) (by norm_num)
  have hprod8 : (F_bond 5 Jx * F_bond 5 Jy) ^ 8 ≤ 98 / 97 := by
    have hnn : 0 ≤ (F_bond 5 Jx * F_bond 5 Jy) ^ 8 :=
      pow_nonneg (mul_pos (F_bond_pos 5 Jx) (F_bond_pos 5 Jy)).le 8
    have hsq : ((F_bond 5 Jx * F_bond 5 Jy) ^ 8) ^ 2 ≤ (98 / 97 : ℝ) ^ 2 := by
      simpa [← pow_mul] using hprod16
    nlinarith
  have hZ2_pos : 0 < Z_2d 2 2 Jx Jy 1 5 := Z_2d_pos 2 2 Jx Jy 1 5
  have hZ2_le : Z_2d 2 2 Jx Jy 1 5 ≤ F_bond 5 Jx * F_bond 5 Jy := Z_2d_2x2_le Jx Jy 5
  have hZ2_pow8 : (Z_2d 2 2 Jx Jy 1 5) ^ 8 ≤ 98 / 97 :=
    (pow_le_pow_left₀ hZ2_pos.le hZ2_le 8).trans hprod8
  have hZ4_ge : (1 : ℝ) ≤ Z_2d 4 4 Jx Jy 1 10 :=
    one_le_Z_2d_shift_one (by norm_num) (by norm_num) Jx Jy (by norm_num)
  rw [le_div_iff₀ (pow_pos hZ2_pos 8)]
  nlinarith

end PurityBootstrap.Ising2DSeed
