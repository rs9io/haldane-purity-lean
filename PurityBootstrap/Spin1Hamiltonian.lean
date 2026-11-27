import PurityBootstrap.MatrixTools
import PurityBootstrap.LieTrotter
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Concrete Physical Spin-1 Heisenberg + Single-Ion Anisotropy Hamiltonian (`H_spin1`)

Defines the concrete `3^n × 3^n` physical spin-1 ring Hamiltonian in the Cartesian basis on
`Fin n → Fin 3`:
  `H_spin1 n hn D g = ∑_{j=0}^{n-2} h_{j, j+1} + h_{n-1, 0}(g) + D ∑_{j=0}^{n-1} (S_j^z)^2`
where `h_{j, k}(g) = -∑_{α ∈ {x,y,z}} (G_α)_j ⊗ (g G_α gᵀ)_k`, `G_α = i S^α` are the real
skew-symmetric `3 × 3` spin-1 generators `(G_α)_{ij} = ε_{α i j}`, and `(S^z)^2 = diag(1, 1, 0)`.

Key machine-checked results:
1. Exact `SO(3)` algebra and rotation covariance `g * G_mat α * gᵀ = ∑ β, g β α • G_mat β` for all
   required rotations `rotI`, `rotZ` (`R_z(π)`), `rotX` (`R_x(π)`), `rotY` (`R_y(π)`), `rotF`
   (`R_z(π/2)`), `rotR` (`R_z(π/4)`), and `rotC` (cyclic `e_x ↦ e_y ↦ e_z ↦ e_x`).
2. Explicit unitary equivalence `U_cart_to_sz` between `-i G_α`, `diag(1, 1, 0)` and the standard
   complex spin-1 weight-basis operators `S^x, S^y, S^z, (S^z)^2`.
3. Symmetry `H_spin1_isHermitian`, shifted Hamiltonian `H_spin1_shifted`, and concrete physical
   partition function `Z_spin1 n hn D a g b = Tr(exp(-b (H_spin1 + a n I))) = matZ ...`.
-/

namespace PurityBootstrap.Spin1Hamiltonian

open scoped BigOperators Matrix
open Matrix PurityBootstrap.MatrixTools PurityBootstrap.LieTrotter

/-! ## 1. Cartesian `3 × 3` Spin-1 Generators `G_α = i S^α` and `SO(3)` Rotations -/

/-- Real skew-symmetric `3 × 3` Cartesian generators `(G_mat α) i j = ε_{α i j}` (`0=x, 1=y, 2=z`). -/
def G_mat : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ
  | ⟨0, _⟩ => !![0, 0, 0; 0, 0, 1; 0, -1, 0]
  | ⟨1, _⟩ => !![0, 0, -1; 0, 0, 0; 1, 0, 0]
  | ⟨2, _⟩ => !![0, 1, 0; -1, 0, 0; 0, 0, 0]

lemma G_mat_transpose (α : Fin 3) : (G_mat α)ᵀ = -G_mat α := by
  fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [G_mat]

/-- Single-site shifted anisotropy `V_mat D a = D (S^z)^2 + a I = diag(D + a, D + a, a)`. -/
def V_mat (D a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![D + a, D + a, a]

/-- Pure single-ion anisotropy `(S^z)^2 = -G_z^2 = diag(1, 1, 0)`. -/
def SzSq_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, 1, 0]

lemma neg_Gz_sq_eq_SzSq : -(G_mat 2 * G_mat 2) = SzSq_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, G_mat, SzSq_mat, Fin.sum_univ_three]

lemma V_mat_eq (D a : ℝ) : V_mat D a = D • SzSq_mat + a • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [V_mat, SzSq_mat]

lemma SzSq_mat_transpose : SzSq_matᵀ = SzSq_mat := by
  simp [SzSq_mat]

lemma V_mat_transpose (D a : ℝ) : (V_mat D a)ᵀ = V_mat D a := by
  simp [V_mat]

/-- Identity rotation `I ∈ SO(3)`. -/
def rotI : Matrix (Fin 3) (Fin 3) ℝ := 1

/-- `R_z(π) = diag(-1, -1, 1) ∈ D_4 ⊂ SO(3)`. -/
def rotZ : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- `R_x(π) = diag(1, -1, -1) ∈ D_4 ⊂ SO(3)`. -/
def rotX : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

/-- `R_y(π) = diag(-1, 1, -1) ∈ D_4 ⊂ SO(3)`. -/
def rotY : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- `R_z(π/2) ∈ D_4 ⊂ SO(3)` (`e_x ↦ e_y, e_y ↦ -e_x, e_z ↦ e_z`). -/
def rotF : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- `R_z(π/4) ∈ O(2) ⊂ SO(3)` (pairs the `B_1` and `B_2` sectors of `D_4`). -/
noncomputable def rotR : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt 2 / 2, -(Real.sqrt 2 / 2), 0;
     Real.sqrt 2 / 2, Real.sqrt 2 / 2, 0;
     0, 0, 1]

/-- Cyclic axis rotation `C ∈ SO(3)` (`e_x ↦ e_y ↦ e_z ↦ e_x`, for isotropic `D = 0`). -/
def rotC : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- Predicate bundling `g ∈ SO(3)` together with the `G_α` rotation-covariance identity. -/
structure IsSpin1Rot (g : Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  orth_right : g * gᵀ = 1
  orth_left : gᵀ * g = 1
  cov : ∀ α : Fin 3, g * G_mat α * gᵀ = ∑ β : Fin 3, (g β α) • G_mat β

/-- Predicate for `O(2) ⊂ SO(3)` rotations preserving `(S^z)^2` (hence `V_mat D a` for all `D`). -/
structure IsAxialRot (g : Matrix (Fin 3) (Fin 3) ℝ) : Prop extends IsSpin1Rot g where
  pres_SzSq : g * SzSq_mat * gᵀ = SzSq_mat

lemma IsAxialRot.pres_V {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsAxialRot g) (D a : ℝ) :
    g * V_mat D a * gᵀ = V_mat D a := by
  rw [V_mat_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hg.pres_SzSq, hg.orth_right]

lemma IsSpin1Rot.pres_V_zero {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) (a : ℝ) :
    g * V_mat 0 a * gᵀ = V_mat 0 a := by
  rw [V_mat_eq, zero_smul, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hg.orth_right]

lemma IsSpin1Rot.mul {g h : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) (hh : IsSpin1Rot h) :
    IsSpin1Rot (g * h) where
  orth_right := by
    calc (g * h) * (g * h)ᵀ = g * (h * hᵀ) * gᵀ := by rw [Matrix.transpose_mul]; simp [Matrix.mul_assoc]
      _ = g * 1 * gᵀ := by rw [hh.orth_right]
      _ = 1 := by rw [Matrix.mul_one, hg.orth_right]
  orth_left := by
    calc (g * h)ᵀ * (g * h) = hᵀ * (gᵀ * g) * h := by rw [Matrix.transpose_mul]; simp [Matrix.mul_assoc]
      _ = hᵀ * 1 * h := by rw [hg.orth_left]
      _ = 1 := by rw [Matrix.mul_one, hh.orth_left]
  cov α := by
    calc (g * h) * G_mat α * (g * h)ᵀ
        = g * (h * G_mat α * hᵀ) * gᵀ := by rw [Matrix.transpose_mul]; simp [Matrix.mul_assoc]
      _ = g * (∑ β : Fin 3, (h β α) • G_mat β) * gᵀ := by rw [hh.cov α]
      _ = ∑ β : Fin 3, (h β α) • (g * G_mat β * gᵀ) := by
            rw [Matrix.mul_sum, Matrix.sum_mul]
            refine Finset.sum_congr rfl fun β _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = ∑ β : Fin 3, (h β α) • (∑ γ : Fin 3, (g γ β) • G_mat γ) := by
            simp_rw [hg.cov]
      _ = ∑ γ : Fin 3, (∑ β : Fin 3, g γ β * h β α) • G_mat γ := by
            simp_rw [Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun γ _ => ?_
            rw [← Finset.sum_smul]
            congr 1
            exact Finset.sum_congr rfl fun β _ => mul_comm _ _
      _ = ∑ γ : Fin 3, ((g * h) γ α) • G_mat γ := by
            refine Finset.sum_congr rfl fun γ _ => by rw [Matrix.mul_apply]

lemma IsSpin1Rot.transpose {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) :
    IsSpin1Rot gᵀ where
  orth_right := by rw [Matrix.transpose_transpose]; exact hg.orth_left
  orth_left := by rw [Matrix.transpose_transpose]; exact hg.orth_right
  cov α := by
    have h1 : g * (gᵀ * G_mat α * g) * gᵀ = g * (∑ β : Fin 3, (g α β) • G_mat β) * gᵀ := by
      have hL : g * (gᵀ * G_mat α * g) * gᵀ = G_mat α := by
        calc g * (gᵀ * G_mat α * g) * gᵀ
            = (g * gᵀ) * G_mat α * (g * gᵀ) := by simp [Matrix.mul_assoc]
          _ = G_mat α := by rw [hg.orth_right, Matrix.one_mul, Matrix.mul_one]
      have hR : g * (∑ β : Fin 3, (g α β) • G_mat β) * gᵀ = G_mat α := by
        calc g * (∑ β : Fin 3, (g α β) • G_mat β) * gᵀ
            = ∑ β : Fin 3, (g α β) • (g * G_mat β * gᵀ) := by
                rw [Matrix.mul_sum, Matrix.sum_mul]
                exact Finset.sum_congr rfl fun β _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
          _ = ∑ β : Fin 3, (g α β) • (∑ γ : Fin 3, (g γ β) • G_mat γ) := by simp_rw [hg.cov]
          _ = ∑ γ : Fin 3, (∑ β : Fin 3, g α β * g γ β) • G_mat γ := by
                simp_rw [Finset.smul_sum, smul_smul]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun γ _ => by rw [← Finset.sum_smul]
          _ = ∑ γ : Fin 3, (if α = γ then (1 : ℝ) else 0) • G_mat γ := by
                refine Finset.sum_congr rfl fun γ _ => ?_
                have horth : ∑ β : Fin 3, g α β * g γ β = if α = γ then 1 else 0 := by
                  have h := congrFun (congrFun hg.orth_right α) γ
                  simpa [Matrix.mul_apply, Matrix.one_apply] using h
                rw [horth]
          _ = G_mat α := by simp
      rw [hL, hR]
    calc gᵀ * G_mat α * gᵀᵀ = gᵀ * G_mat α * g := by rw [Matrix.transpose_transpose]
      _ = gᵀ * (g * (gᵀ * G_mat α * g) * gᵀ) * g := by
            calc gᵀ * G_mat α * g = 1 * (gᵀ * G_mat α * g) * 1 := by simp
              _ = (gᵀ * g) * (gᵀ * G_mat α * g) * (gᵀ * g) := by rw [hg.orth_left]
              _ = gᵀ * (g * (gᵀ * G_mat α * g) * gᵀ) * g := by simp [Matrix.mul_assoc]
      _ = gᵀ * (g * (∑ β : Fin 3, (g α β) • G_mat β) * gᵀ) * g := by rw [h1]
      _ = (gᵀ * g) * (∑ β : Fin 3, (g α β) • G_mat β) * (gᵀ * g) := by simp [Matrix.mul_assoc]
      _ = ∑ β : Fin 3, (gᵀ β α) • G_mat β := by
            rw [hg.orth_left, Matrix.one_mul, Matrix.mul_one]
            rfl

private lemma sqrt2_half_sq : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linarith

lemma isAxialRot_rotI : IsAxialRot rotI where
  orth_right := by simp [rotI]
  orth_left := by simp [rotI]
  cov α := by
    simp [rotI, Matrix.one_apply]
  pres_SzSq := by simp [rotI]

lemma isAxialRot_rotZ : IsAxialRot rotZ where
  orth_right := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotZ, Fin.sum_univ_three]
  orth_left := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotZ, Fin.sum_univ_three]
  cov α := by
    fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotZ, G_mat, Fin.sum_univ_three]
  pres_SzSq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul_diagonal, rotZ, SzSq_mat, Fin.sum_univ_three]

lemma isAxialRot_rotX : IsAxialRot rotX where
  orth_right := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotX, Fin.sum_univ_three]
  orth_left := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotX, Fin.sum_univ_three]
  cov α := by
    fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotX, G_mat, Fin.sum_univ_three]
  pres_SzSq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul_diagonal, rotX, SzSq_mat, Fin.sum_univ_three]

lemma isAxialRot_rotY : IsAxialRot rotY where
  orth_right := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotY, Fin.sum_univ_three]
  orth_left := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotY, Fin.sum_univ_three]
  cov α := by
    fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotY, G_mat, Fin.sum_univ_three]
  pres_SzSq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul_diagonal, rotY, SzSq_mat, Fin.sum_univ_three]

lemma isAxialRot_rotF : IsAxialRot rotF where
  orth_right := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotF, Fin.sum_univ_three]
  orth_left := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotF, Fin.sum_univ_three]
  cov α := by
    fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotF, G_mat, Fin.sum_univ_three]
  pres_SzSq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul_diagonal, rotF, SzSq_mat, Fin.sum_univ_three]

lemma isAxialRot_rotR : IsAxialRot rotR where
  orth_right := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotR, Fin.sum_univ_three] <;> linarith [sqrt2_half_sq]
  orth_left := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotR, Fin.sum_univ_three] <;> linarith [sqrt2_half_sq]
  cov α := by
    fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotR, G_mat, Fin.sum_univ_three] <;> linarith [sqrt2_half_sq]
  pres_SzSq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul_diagonal, rotR, SzSq_mat, Fin.sum_univ_three] <;>
      linarith [sqrt2_half_sq]

lemma isSpin1Rot_rotC : IsSpin1Rot rotC where
  orth_right := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotC, Fin.sum_univ_three]
  orth_left := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotC, Fin.sum_univ_three]
  cov α := by
    fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, rotC, G_mat, Fin.sum_univ_three]

/-! ### Exact `D_4`, `O(2)`, and `D_2 ⋊ C_3` Group Relations -/

lemma rotF_sq : rotF * rotF = rotZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotF, rotZ, Fin.sum_univ_three]

lemma rotZ_sq : rotZ * rotZ = rotI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotZ, rotI, Fin.sum_univ_three]

lemma rotX_sq : rotX * rotX = rotI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotX, rotI, Fin.sum_univ_three]

lemma rotY_sq : rotY * rotY = rotI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotY, rotI, Fin.sum_univ_three]

lemma rotZ_transpose : rotZᵀ = rotZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotZ]

lemma rotX_transpose : rotXᵀ = rotX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotX]

lemma rotY_transpose : rotYᵀ = rotY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotY]

lemma rotF_mul_rotZ : rotF * rotZ = rotFᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotF, rotZ, Fin.sum_univ_three]

lemma rotZ_mul_rotF : rotZ * rotF = rotFᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotF, rotZ, Fin.sum_univ_three]

lemma rotX_mul_rotF_mul_rotX : rotX * rotF * rotX = rotFᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotX, rotF, Fin.sum_univ_three]

lemma rotF_mul_rotX_mul_rotFT : rotF * rotX * rotFᵀ = rotZ * rotX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotF, rotX, rotZ, Fin.sum_univ_three]

lemma rotR_sq : rotR * rotR = rotF := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, rotR, rotF, Fin.sum_univ_three] <;> linarith [sqrt2_half_sq]

lemma rotR_mul_rotF : rotR * rotF = rotF * rotR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, rotR, rotF, Fin.sum_univ_three] <;> ring

lemma rotR_mul_rotZ : rotR * rotZ = rotZ * rotR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, rotR, rotZ, Fin.sum_univ_three]

lemma rotR_mul_rotX_mul_rotRT : rotR * rotX * rotRᵀ = rotF * rotX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, rotR, rotX, rotF, Fin.sum_univ_three] <;> linarith [sqrt2_half_sq]

lemma rotX_mul_rotY : rotX * rotY = rotZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotX, rotY, rotZ, Fin.sum_univ_three]

lemma rotY_mul_rotX : rotY * rotX = rotZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotX, rotY, rotZ, Fin.sum_univ_three]

lemma rotZ_mul_rotX : rotZ * rotX = rotY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotX, rotY, rotZ, Fin.sum_univ_three]

lemma rotX_mul_rotZ : rotX * rotZ = rotY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotX, rotY, rotZ, Fin.sum_univ_three]

lemma rotC_mul_rotX_mul_rotCT : rotC * rotX * rotCᵀ = rotY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotC, rotX, rotY, Fin.sum_univ_three]

lemma rotC_mul_rotY_mul_rotCT : rotC * rotY * rotCᵀ = rotZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotC, rotY, rotZ, Fin.sum_univ_three]

lemma rotC_mul_rotZ_mul_rotCT : rotC * rotZ * rotCᵀ = rotX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, rotC, rotZ, rotX, Fin.sum_univ_three]

/-! ## 2. Unitary Equivalence Between Cartesian Basis and Standard `S^z` Weight Basis -/

/-- Standard complex spin-1 matrices `S^x, S^y, S^z` in the weight basis `(|1⟩, |0⟩, |-1⟩)`. -/
noncomputable def S_weight : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ
  | ⟨0, _⟩ =>
      let r : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
      !![0, r, 0; r, 0, r; 0, r, 0]
  | ⟨1, _⟩ =>
      let r : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
      !![0, -Complex.I * r, 0; Complex.I * r, 0, -Complex.I * r; 0, Complex.I * r, 0]
  | ⟨2, _⟩ =>
      !![1, 0, 0; 0, 0, 0; 0, 0, -1]

/-- Unitary change of basis from Cartesian `(e_x, e_y, e_z)` to weight basis `(|1⟩, |0⟩, |-1⟩)`. -/
noncomputable def U_cart_to_sz : Matrix (Fin 3) (Fin 3) ℂ :=
  let r : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
  !![-r, Complex.I * r, 0;
     0, 0, 1;
     r, Complex.I * r, 0]

lemma U_cart_to_sz_unitary : U_cart_to_sz * U_cart_to_szᴴ = 1 ∧ U_cart_to_szᴴ * U_cart_to_sz = 1 := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, U_cart_to_sz, Fin.sum_univ_three,
        Complex.ofReal_div, Complex.ofReal_ofNat, map_ofNat] <;>
      ring_nf <;>
      simp [Complex.I_sq, hsq] <;>
      norm_num

/-- Conjugating `-i G_α` by `U_cart_to_sz` gives the exact textbook spin-1 matrix `S^α`. -/
theorem U_cart_to_sz_conj_S (α : Fin 3) :
    U_cart_to_sz * ((-Complex.I) • (G_mat α).map Complex.ofReal) * U_cart_to_szᴴ = S_weight α := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  fin_cases α <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct,
      Matrix.map_apply, U_cart_to_sz, G_mat, S_weight, Fin.sum_univ_three,
      Complex.ofReal_div, Complex.ofReal_ofNat, map_ofNat] <;>
    ring_nf <;>
    try simp [Complex.I_sq, hsq] <;>
    try ring

/-- Conjugating `SzSq_mat = diag(1, 1, 0)` by `U_cart_to_sz` gives `(S^z)^2 = diag(1, 0, 1)`. -/
theorem U_cart_to_sz_conj_SzSq :
    U_cart_to_sz * SzSq_mat.map Complex.ofReal * U_cart_to_szᴴ = S_weight 2 * S_weight 2 := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct,
      Matrix.map_apply, U_cart_to_sz, SzSq_mat, S_weight, Fin.sum_univ_three,
      Complex.ofReal_div, Complex.ofReal_ofNat, map_ofNat] <;>
    ring_nf <;>
    try simp [Complex.I_sq, hsq] <;>
    try ring

/-! ## 3. Concrete `3^n × 3^n` Physical Spin-1 Ring Hamiltonian `H_spin1` -/

/-- Configuration space of `n` spin-1 sites in the Cartesian basis (`3^n` basis states). -/
abbrev Spin1Cfg (n : ℕ) := Fin n → Fin 3

/-- Single-site operator `A` acting on site `j` of an `n`-site spin-1 chain. -/
def singleSite (n : ℕ) (j : Fin n) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  Matrix.of fun σ τ => if ∀ m : Fin n, m ≠ j → σ m = τ m then A (σ j) (τ j) else 0

lemma singleSite_transpose (n : ℕ) (j : Fin n) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (singleSite n j A)ᵀ = singleSite n j Aᵀ := by
  ext σ τ
  simp only [Matrix.transpose_apply, singleSite, Matrix.of_apply]
  have hiff : (∀ m : Fin n, m ≠ j → τ m = σ m) ↔ (∀ m : Fin n, m ≠ j → σ m = τ m) :=
    ⟨fun h m hm => (h m hm).symm, fun h m hm => (h m hm).symm⟩
  simp [hiff]

lemma singleSite_mul_comm {n : ℕ} {j k : Fin n} (hjk : j ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    singleSite n j A * singleSite n k B = singleSite n k B * singleSite n j A := by
  ext σ τ
  have hmul : ∀ (p q : Fin n) (hpq : p ≠ q) (P Q : Matrix (Fin 3) (Fin 3) ℝ),
      (singleSite n p P * singleSite n q Q) σ τ =
        if ∀ m : Fin n, m ≠ p → m ≠ q → σ m = τ m then P (σ p) (τ p) * Q (σ q) (τ q) else 0 := by
    intro p q hpq P Q
    rw [Matrix.mul_apply]
    let μ : Spin1Cfg n := Function.update σ p (τ p)
    rw [Finset.sum_eq_single μ]
    · simp only [singleSite, Matrix.of_apply]
      have h1 : ∀ m : Fin n, m ≠ p → σ m = μ m := fun m hm => by
        simp [μ, Function.update_of_ne hm]
      have hμp : μ p = τ p := by simp [μ]
      have hμq : μ q = σ q := by simp [μ, Function.update_of_ne hpq.symm]
      have h2 : (∀ m : Fin n, m ≠ q → μ m = τ m) ↔ (∀ m : Fin n, m ≠ p → m ≠ q → σ m = τ m) := by
        constructor
        · intro h m hmp hmq
          have := h m hmq
          rwa [← h1 m hmp] at this
        · intro h m hmq
          by_cases hmp : m = p
          · rw [hmp]; exact hμp
          · rw [← h1 m hmp]; exact h m hmp hmq
      simp only [h1, ite_true, h2, hμp, hμq]
      split_ifs <;> ring
    · intro ρ _ hρ
      simp only [singleSite, Matrix.of_apply]
      split_ifs with h1 h2
      · exfalso; apply hρ; funext m
        by_cases hmp : m = p
        · rw [hmp]; simp [μ, h2 p hpq]
        · simp [μ, Function.update_of_ne hmp, (h1 m hmp).symm]
      · simp
      · simp
      · simp
    · intro h; exact absurd (Finset.mem_univ μ) h
  rw [hmul j k hjk A B, hmul k j hjk.symm B A]
  have hiff : (∀ m : Fin n, m ≠ j → m ≠ k → σ m = τ m) ↔
      (∀ m : Fin n, m ≠ k → m ≠ j → σ m = τ m) :=
    ⟨fun h m hmk hmj => h m hmj hmk, fun h m hmj hmk => h m hmk hmj⟩
  simp [hiff, mul_comm]

/-- Twisted two-site Heisenberg bond operator
`h_{j, k}(g) = -∑_α (G_α)_j ⊗ (g G_α gᵀ)_k` (for distinct sites `j ≠ k`). -/
def bondOp (n : ℕ) (j k : Fin n) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  -(∑ α : Fin 3, singleSite n j (G_mat α) * singleSite n k (g * G_mat α * gᵀ))

lemma bondOp_transpose {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    (bondOp n j k g)ᵀ = bondOp n j k g := by
  unfold bondOp
  rw [Matrix.transpose_neg, Matrix.transpose_sum]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Matrix.transpose_mul, singleSite_transpose, singleSite_transpose,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    G_mat_transpose, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc g (G_mat α) gᵀ,
    show singleSite n k (-(g * G_mat α * gᵀ)) = -singleSite n k (g * G_mat α * gᵀ) by
      ext σ τ; simp only [singleSite, Matrix.of_apply, Matrix.neg_apply]; split_ifs <;> ring,
    show singleSite n j (-G_mat α) = -singleSite n j (G_mat α) by
      ext σ τ; simp only [singleSite, Matrix.of_apply, Matrix.neg_apply]; split_ifs <;> ring,
    neg_mul_neg, singleSite_mul_comm hjk.symm]

/-- Next site modulo `n` on a ring of length `n ≥ 3`. -/
def nextSite {n : ℕ} (hn : 3 ≤ n) (j : Fin n) : Fin n :=
  ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩

lemma ne_nextSite {n : ℕ} (hn : 3 ≤ n) (j : Fin n) : j ≠ nextSite hn j := by
  intro h
  have hv : j.val = (j.val + 1) % n := congrArg Fin.val h
  by_cases hlast : j.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlast] at hv; omega
  · have heq : j.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv; omega

/-- Bond sum `∑_{j=0}^{n-2} h_{j, j+1} + h_{n-1, 0}(g)` on a ring of length `n ≥ 3`. -/
def H_bonds (n : ℕ) (hn : 3 ≤ n) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  ∑ j : Fin n, bondOp n j (nextSite hn j) (if j.val + 1 = n then g else rotI)

/-- Single-ion anisotropy term `D ∑_{j=0}^{n-1} (S_j^z)^2`. -/
def H_aniso (n : ℕ) (D : ℝ) : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  D • ∑ j : Fin n, singleSite n j SzSq_mat

/-- **Concrete `3^n × 3^n` physical spin-1 ring Hamiltonian**
`H_spin1 n hn D g = ∑_{j=0}^{n-2} h_{j, j+1} + h_{n-1, 0}(g) + D ∑_{j=0}^{n-1} (S_j^z)^2`. -/
def H_spin1 (n : ℕ) (hn : 3 ≤ n) (D : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  H_bonds n hn g + H_aniso n D

/-- Energy-shifted physical Hamiltonian `H_spin1 n hn D g + (a * n) • I`. -/
def H_spin1_shifted (n : ℕ) (hn : 3 ≤ n) (D a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  H_spin1 n hn D g + (a * (n : ℝ)) • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ)

lemma H_bonds_isHermitian (n : ℕ) (hn : 3 ≤ n) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    (H_bonds n hn g).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold H_bonds
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun j _ => bondOp_transpose (ne_nextSite hn j) _

lemma H_aniso_isHermitian (n : ℕ) (D : ℝ) : (H_aniso n D).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold H_aniso
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [singleSite_transpose, SzSq_mat_transpose]

lemma H_spin1_isHermitian (n : ℕ) (hn : 3 ≤ n) (D : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    (H_spin1 n hn D g).IsHermitian :=
  (H_bonds_isHermitian n hn g).add (H_aniso_isHermitian n D)

lemma H_spin1_shifted_isHermitian (n : ℕ) (hn : 3 ≤ n) (D a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    (H_spin1_shifted n hn D a g).IsHermitian := by
  refine (H_spin1_isHermitian n hn D g).add ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp

/-- Onsite shifted operator `∑_j (V_mat D a)_j = H_aniso n D + (a * n) • I`. -/
def H_onsite (n : ℕ) (D a : ℝ) : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  ∑ j : Fin n, singleSite n j (V_mat D a)

lemma H_onsite_eq_diagonal (n : ℕ) (D a : ℝ) :
    H_onsite n D a = Matrix.diagonal (fun σ : Spin1Cfg n => ∑ j : Fin n, V_mat D a (σ j) (σ j)) := by
  ext σ τ
  simp only [H_onsite, Matrix.sum_apply, singleSite, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hστ : σ = τ
  · subst hστ
    simp
  · rw [if_neg hστ]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hother
    · have hne : σ j ≠ τ j := by
        intro hEq
        apply hστ; funext m
        by_cases hmj : m = j
        · rw [hmj]; exact hEq
        · exact hother m hmj
      simp [V_mat, Matrix.diagonal_apply_ne _ hne]
    · rfl

lemma H_spin1_shifted_eq_bonds_add_onsite (n : ℕ) (hn : 3 ≤ n) (D a : ℝ)
    (g : Matrix (Fin 3) (Fin 3) ℝ) :
    H_spin1_shifted n hn D a g = H_bonds n hn g + H_onsite n D a := by
  unfold H_spin1_shifted H_spin1 H_aniso H_onsite
  have h1 : ∀ j : Fin n,
      singleSite n j (V_mat D a) = D • singleSite n j SzSq_mat + a • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) := by
    intro j; ext σ τ
    simp only [singleSite, Matrix.of_apply, V_mat_eq, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases hστ : σ = τ
    · subst hστ; simp
    · simp only [hστ, ite_false, mul_zero, add_zero]
      by_cases hother : ∀ m : Fin n, m ≠ j → σ m = τ m
      · have hne : σ j ≠ τ j := fun hEq => hστ (funext fun m =>
          if hmj : m = j then hmj ▸ hEq else hother m hmj)
        simp [hother, hne]
      · simp [hother]
  simp_rw [h1, Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  abel

/-- **Concrete physical spin-1 partition function**:
`Z_spin1 n hn D a g b = Tr(exp(-b * (H_spin1 n hn D g + a * n * I)))`. -/
noncomputable def Z_spin1 (n : ℕ) (hn : 3 ≤ n) (D a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ) : ℝ :=
  Matrix.trace (NormedSpace.exp ((-b) • H_spin1_shifted n hn D a g))

set_option backward.isDefEq.respectTransparency false in
/-- `Z_spin1` equals the explicit Gibbs eigenvalue sum of `H_spin1` shifted by `a * n`. -/
theorem Z_spin1_eq_sum_exp (n : ℕ) (hn : 3 ≤ n) (D a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ) :
    Z_spin1 n hn D a g b =
      ∑ k : Spin1Cfg n, Real.exp (-b * ((H_spin1_isHermitian n hn D g).eigenvalues k + a * (n : ℝ))) := by
  letI := Matrix.linftyOpNormedRing (n := Spin1Cfg n) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := Spin1Cfg n) (R := ℝ) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := Spin1Cfg n) (R := ℚ) (α := ℝ)
  letI : CompleteSpace (Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) := FiniteDimensional.complete ℝ _
  unfold Z_spin1
  have hcomm : Commute ((-b) • H_spin1 n hn D g)
      ((-b * (a * (n : ℝ))) • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ)) :=
    Commute.smul_left (Commute.smul_right (Commute.one_right _) _) _
  have hsum : (-b) • H_spin1_shifted n hn D a g =
      (-b) • H_spin1 n hn D g + (-b * (a * (n : ℝ))) • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) := by
    unfold H_spin1_shifted; rw [smul_add, smul_smul]
  have hadd := NormedSpace.exp_add_of_commute hcomm
  rw [hsum, hadd]
  have hexp1 : NormedSpace.exp ((-b * (a * (n : ℝ))) • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ)) =
      Real.exp (-b * (a * (n : ℝ))) • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) := by
    have hdiag : ((-b * (a * (n : ℝ))) • (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ)) =
        Matrix.diagonal (fun _ : Spin1Cfg n => -b * (a * (n : ℝ))) := by
      ext σ τ; simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [hdiag, Matrix.exp_diagonal]
    ext σ τ; simp [Matrix.diagonal_apply, Matrix.one_apply, Real.exp_eq_exp_ℝ]
  rw [hexp1, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
    trace_exp_eq_matZ (H_spin1 n hn D g) (H_spin1_isHermitian n hn D g) b, matZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- Rayleigh–Ritz criterion for the concrete spin-1 Hamiltonian:
any nonzero vector `ψ` with `⟨ψ, (H_spin1 + a n I) ψ⟩ ≤ 0` yields an eigenvalue `E_k + a n ≤ 0`. -/
theorem exists_eig_le_of_rayleigh {n : ℕ} (hn : 3 ≤ n) (D a : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (ψ : Spin1Cfg n → ℝ) (hψ_nz : 0 < dotProduct ψ ψ)
    (hψ_le : dotProduct ψ ((H_spin1 n hn D g).mulVec ψ) + (a * (n : ℝ)) * dotProduct ψ ψ ≤ 0) :
    ∃ k : Spin1Cfg n, (H_spin1_isHermitian n hn D g).eigenvalues k + a * (n : ℝ) ≤ 0 := by
  let hH := H_spin1_isHermitian n hn D g
  rcases Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty with ⟨k₀, _, hk₀⟩
  refine ⟨k₀, ?_⟩
  have hmin : hH.eigenvalues k₀ * dotProduct ψ ψ ≤ dotProduct ψ ((H_spin1 n hn D g).mulVec ψ) := by
    rw [dotProduct_mulVec_eq_sum_eigenvalues _ hH ψ, dotProduct_self_eq_sum_sq _ hH ψ, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (hk₀ k (Finset.mem_univ k)) (sq_nonneg _)
  have hprod : (hH.eigenvalues k₀ + a * (n : ℝ)) * dotProduct ψ ψ ≤ 0 := by nlinarith
  exact nonpos_of_mul_nonpos_left hprod hψ_nz

end PurityBootstrap.Spin1Hamiltonian
