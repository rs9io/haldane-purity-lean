import PurityBootstrap.Spin1Hamiltonian
import PurityBootstrap.Spin1Compactness
import Mathlib.Tactic

/-!
# Finite-Dimensional No-Collision Spin-1 Spatial Transfer Matrix (`K_mat`) & Sector Moments

Eliminates all infinite-dimensional continuous-time operator hypotheses for the spin-1
Heisenberg + single-ion anisotropy ring `H_spin1 n hn D g`:
1. Constructs the `4^M × 4^M` real symmetric no-collision transfer matrix `K_mat M D a b`
   on `Word M := Fin M → Fin 4`, commuting with `U_mat M g = (1 ⊕ g)^{⊗ M}` for every
   `IsAxialRot g` (and every `IsSpin1Rot g` when `D = 0`).
2. Proves the exact cycle contraction identity for all `n ≥ 3`, `M ≥ 1`:
     `Tr((K_mat M D a b)^n * U_mat M g) = Tr((T_slice n hn D a (b / M) g)^M)`
   and proves `Tr((T_slice ...)^M) → Z_spin1 n hn D a g b` as `M → ∞`.
3. Proves the uniform Hilbert–Schmidt bound
     `Tr((K_mat M D a b)^2) ≤ 9 * exp(2 * b * (|D| + |a| + 3))`.
4. Combines the exact finite-`M` real symmetric block decompositions (`D_4` + `R_z(π/4)` for
   general `D`, and `D_2` + `C_3` for `D = 0`) with `l2_seq_compact_moments` to construct
   exact summable real sector eigenvalue families reproducing all twisted physical partition
   functions `Z_spin1 n hn D a g b` for every `n ≥ 4` (even and odd).
-/

namespace PurityBootstrap.Spin1Transfer

open scoped BigOperators Matrix
open Filter Matrix NormedSpace PurityBootstrap.Spin1Hamiltonian PurityBootstrap.Spin1Compactness

/-! ## 1. Local Slice Matrices `diagExp3`, `Phi`, `lift4`, and `sliceProd` -/

/-- Configuration word of `M` time slices on one bond (`0` = empty, `1,2,3` = `x,y,z`). -/
abbrev Word (M : ℕ) := Fin M → Fin 4

/-- Diagonal single-site Boltzmann factor `exp(-τ * V_mat D a)`. -/
noncomputable def diagExp3 (τ D a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![Real.exp (-τ * (D + a)), Real.exp (-τ * (D + a)), Real.exp (-τ * a)]

lemma diagExp3_eq_lin (τ D a : ℝ) :
    diagExp3 τ D a =
      (Real.exp (-τ * (D + a)) - Real.exp (-τ * a)) • SzSq_mat +
        Real.exp (-τ * a) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagExp3, SzSq_mat]

lemma diagExp3_conj_axial {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsAxialRot g) (τ D a : ℝ) :
    g * diagExp3 τ D a * gᵀ = diagExp3 τ D a := by
  rw [diagExp3_eq_lin, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hg.pres_SzSq, hg.orth_right]

lemma diagExp3_conj_iso {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) (τ a : ℝ) :
    g * diagExp3 τ 0 a * gᵀ = diagExp3 τ 0 a := by
  rw [diagExp3_eq_lin]
  simp only [zero_add, sub_self, zero_smul, zero_add]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hg.orth_right]

/-- Local no-collision slice matrix `Φ_τ(u, v)` on `Fin 4 × Fin 4 → M_3(ℝ)`. -/
noncomputable def Phi (τ : ℝ) : Fin 4 → Fin 4 → Matrix (Fin 3) (Fin 3) ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨j + 1, hj⟩ => Real.sqrt τ • G_mat ⟨j, by omega⟩
  | ⟨i + 1, hi⟩, ⟨0, _⟩ => Real.sqrt τ • G_mat ⟨i, by omega⟩
  | ⟨_ + 1, _⟩, ⟨_ + 1, _⟩ => 0

lemma Phi_symm (τ : ℝ) (u v : Fin 4) : Phi τ u v = Phi τ v u := by
  fin_cases u <;> fin_cases v <;> rfl

/-- Lift `g ∈ SO(3)` to `1 ⊕ g` on `Fin 4` (`0 ↦ 0`, `α+1 ↦ g(α)+1`). -/
def lift4 (g : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun u v =>
    match u, v with
    | ⟨0, _⟩, ⟨0, _⟩ => 1
    | ⟨0, _⟩, ⟨_ + 1, _⟩ => 0
    | ⟨_ + 1, _⟩, ⟨0, _⟩ => 0
    | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩ => g ⟨i, by omega⟩ ⟨j, by omega⟩

lemma lift4_one : lift4 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext u v; fin_cases u <;> fin_cases v <;> simp [lift4]

lemma lift4_transpose (g : Matrix (Fin 3) (Fin 3) ℝ) : (lift4 g)ᵀ = lift4 gᵀ := by
  ext u v; fin_cases u <;> fin_cases v <;> simp [lift4]

lemma lift4_mul (g h : Matrix (Fin 3) (Fin 3) ℝ) : lift4 (g * h) = lift4 g * lift4 h := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [lift4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

lemma Phi_cov {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) (τ : ℝ) (u v : Fin 4) :
    g * Phi τ u v * gᵀ = ∑ u' : Fin 4, ∑ v' : Fin 4, (lift4 g u' u * lift4 g v' v) • Phi τ u' v' := by
  fin_cases u <;> fin_cases v
  · simp [Phi, lift4, Fin.sum_univ_four, hg.orth_right]
  · simp only [Phi, lift4, Matrix.mul_smul, Matrix.smul_mul, hg.cov, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.of_apply]
    simp [smul_smul, Finset.smul_sum, mul_comm]
  · simp only [Phi, lift4, Matrix.mul_smul, Matrix.smul_mul, hg.cov, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.of_apply]
    simp [smul_smul, Finset.smul_sum, mul_comm]
  · simp only [Phi, lift4, Matrix.mul_smul, Matrix.smul_mul, hg.cov, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.of_apply]
    simp [smul_smul, Finset.smul_sum, mul_comm]
  · simp only [Phi, lift4, Matrix.mul_smul, Matrix.smul_mul, hg.cov, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.of_apply]
    simp [smul_smul, Finset.smul_sum, mul_comm]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp only [Phi, lift4, Matrix.mul_smul, Matrix.smul_mul, hg.cov, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.of_apply]
    simp [smul_smul, Finset.smul_sum, mul_comm]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp only [Phi, lift4, Matrix.mul_smul, Matrix.smul_mul, hg.cov, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.of_apply]
    simp [smul_smul, Finset.smul_sum, mul_comm]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp [Phi, lift4, Fin.sum_univ_four]
  · simp [Phi, lift4, Fin.sum_univ_four]

/-- Ordered time-slice product `f 0 * f 1 * ... * f (M - 1)` of `3 × 3` real matrices. -/
def sliceProd : ∀ {M : ℕ}, (Fin M → Matrix (Fin 3) (Fin 3) ℝ) → Matrix (Fin 3) (Fin 3) ℝ
  | 0, _ => 1
  | M + 1, f => sliceProd (fun t : Fin M => f t.castSucc) * f (Fin.last M)

lemma sliceProd_conj {g : Matrix (Fin 3) (Fin 3) ℝ} (hg_r : g * gᵀ = 1) (hg_l : gᵀ * g = 1) :
    ∀ {M : ℕ} (f : Fin M → Matrix (Fin 3) (Fin 3) ℝ),
      g * sliceProd f * gᵀ = sliceProd (fun t => g * f t * gᵀ)
  | 0, _ => by simp [sliceProd, hg_r]
  | M + 1, f => by
      simp only [sliceProd]
      rw [← sliceProd_conj hg_r hg_l (fun t : Fin M => f t.castSucc)]
      calc g * (sliceProd (fun t : Fin M => f t.castSucc) * f (Fin.last M)) * gᵀ
          = g * sliceProd (fun t : Fin M => f t.castSucc) * (1 * f (Fin.last M)) * gᵀ := by
              simp [Matrix.mul_assoc]
        _ = g * sliceProd (fun t : Fin M => f t.castSucc) * ((gᵀ * g) * f (Fin.last M)) * gᵀ := by
              rw [hg_l]
        _ = (g * sliceProd (fun t : Fin M => f t.castSucc) * gᵀ) * (g * f (Fin.last M) * gᵀ) := by
              simp [Matrix.mul_assoc]

lemma sliceProd_smul : ∀ {M : ℕ} (c : Fin M → ℝ) (f : Fin M → Matrix (Fin 3) (Fin 3) ℝ),
    sliceProd (fun t => c t • f t) = (∏ t : Fin M, c t) • sliceProd f
  | 0, _, _ => by simp [sliceProd]
  | M + 1, c, f => by
      simp only [sliceProd, Fin.prod_univ_castSucc]
      rw [sliceProd_smul (fun t : Fin M => c t.castSucc) (fun t : Fin M => f t.castSucc),
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma sliceProd_sum {α : Type*} [Fintype α] :
    ∀ {M : ℕ} (F : Fin M → α → Matrix (Fin 3) (Fin 3) ℝ),
      sliceProd (fun t => ∑ a : α, F t a) = ∑ x : Fin M → α, sliceProd (fun t => F t (x t))
  | 0, _ => by
      simp [sliceProd]
  | M + 1, F => by
      simp only [sliceProd]
      rw [sliceProd_sum (fun t : Fin M => F t.castSucc), Matrix.sum_mul]
      simp_rw [Matrix.mul_sum]
      rw [← Fintype.sum_prod_type']
      let e : (Fin M → α) × α ≃ (Fin (M + 1) → α) :=
        { toFun := fun p => Fin.snoc p.1 p.2
          invFun := fun x => (fun t : Fin M => x t.castSucc, x (Fin.last M))
          left_inv := fun ⟨x, a⟩ => by ext t <;> simp
          right_inv := fun x => by
            ext t; refine Fin.lastCases ?_ ?_ t <;> simp }
      refine Fintype.sum_equiv e _ _ fun ⟨x, a⟩ => ?_
      simp [e, sliceProd]

/-! ## 2. Finite-`M` Transfer Matrix `K_mat`, Symmetry `U_mat`, and Hilbert–Schmidt Bound -/

/-- **Finite-`M` no-collision real symmetric spin-1 transfer matrix** on `Word M` (`dim 4^M`). -/
noncomputable def K_mat (M : ℕ) (D a b : ℝ) : Matrix (Word M) (Word M) ℝ :=
  Matrix.of fun x y =>
    Matrix.trace (sliceProd (fun t : Fin M => diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) (x t) (y t)))

lemma K_mat_transpose (M : ℕ) (D a b : ℝ) : (K_mat M D a b)ᵀ = K_mat M D a b := by
  ext x y
  simp only [Matrix.transpose_apply, K_mat, Matrix.of_apply]
  congr 2; ext t; rw [Phi_symm]

lemma K_mat_isHermitian (M : ℕ) (D a b : ℝ) : (K_mat M D a b).IsHermitian :=
  isHermitian_of_transpose_eq (K_mat_transpose M D a b)

/-- Real orthogonal representation `U_mat M g = (1 ⊕ g)^{⊗ M}` on `Word M`. -/
def U_mat (M : ℕ) (g : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Word M) (Word M) ℝ :=
  Matrix.of fun x y => ∏ t : Fin M, lift4 g (x t) (y t)

lemma U_mat_one (M : ℕ) : U_mat M (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext x y
  simp only [U_mat, Matrix.of_apply, lift4_one, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    have hex : ∃ t : Fin M, x t ≠ y t := by
      by_contra hall; push_neg at hall; exact hxy (funext hall)
    rcases hex with ⟨t, ht⟩
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])

lemma U_mat_transpose (M : ℕ) (g : Matrix (Fin 3) (Fin 3) ℝ) : (U_mat M g)ᵀ = U_mat M gᵀ := by
  ext x y
  simp only [Matrix.transpose_apply, U_mat, Matrix.of_apply]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [← lift4_transpose]; rfl

lemma U_mat_mul (M : ℕ) (g h : Matrix (Fin 3) (Fin 3) ℝ) :
    U_mat M (g * h) = U_mat M g * U_mat M h := by
  ext x y
  simp only [U_mat, Matrix.of_apply, lift4_mul, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma U_mat_orth_right (M : ℕ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g * gᵀ = 1) :
    U_mat M g * (U_mat M g)ᵀ = 1 := by
  rw [U_mat_transpose, ← U_mat_mul, hg, U_mat_one]

lemma U_mat_orth_left (M : ℕ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : gᵀ * g = 1) :
    (U_mat M g)ᵀ * U_mat M g = 1 := by
  rw [U_mat_transpose, ← U_mat_mul, hg, U_mat_one]

/-- Exact commutation `U_mat M g * K_mat M D a b = K_mat M D a b * U_mat M g`. -/
theorem K_mat_comm_U (M : ℕ) (D a b : ℝ) {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : IsSpin1Rot g)
    (hgV : g * diagExp3 (b / (M : ℝ)) D a * gᵀ = diagExp3 (b / (M : ℝ)) D a) :
    U_mat M g * K_mat M D a b = K_mat M D a b * U_mat M g := by
  suffices hconj : (U_mat M g)ᵀ * K_mat M D a b * U_mat M g = K_mat M D a b by
    calc U_mat M g * K_mat M D a b
        = U_mat M g * ((U_mat M g)ᵀ * K_mat M D a b * U_mat M g) := by rw [hconj]
      _ = (U_mat M g * (U_mat M g)ᵀ) * K_mat M D a b * U_mat M g := by simp [Matrix.mul_assoc]
      _ = K_mat M D a b * U_mat M g := by rw [U_mat_orth_right M hg.orth_right, Matrix.one_mul]
  ext x y
  -- Compute `(U_gᵀ * K * U_g) x y = ∑ u v, (∏ t, lift4 g (u t) (x t) * lift4 g (v t) (y t)) * K u v`
  have hL : ((U_mat M g)ᵀ * K_mat M D a b * U_mat M g) x y =
      ∑ p : Word M × Word M,
        (∏ t : Fin M, lift4 g (p.1 t) (x t) * lift4 g (p.2 t) (y t)) * K_mat M D a b p.1 p.2 := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp only [U_mat, Matrix.transpose_apply, Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  rw [hL]
  -- Move `∑` inside `Matrix.trace` and `sliceProd` via `sliceProd_sum`
  have hKeq : K_mat M D a b x y =
      Matrix.trace (sliceProd (fun t : Fin M =>
        g * (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) (x t) (y t)) * gᵀ)) := by
    simp only [K_mat, Matrix.of_apply]
    rw [← sliceProd_conj hg.orth_right hg.orth_left, Matrix.trace_mul_cycle, hg.orth_left, Matrix.one_mul]
  rw [hKeq]
  have hfactor : ∀ t : Fin M,
      g * (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) (x t) (y t)) * gᵀ =
        ∑ p : Fin 4 × Fin 4,
          (lift4 g p.1 (x t) * lift4 g p.2 (y t)) •
            (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) p.1 p.2) := fun t => by
    calc g * (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) (x t) (y t)) * gᵀ
        = (g * diagExp3 (b / (M : ℝ)) D a * gᵀ) * (g * Phi (b / (M : ℝ)) (x t) (y t) * gᵀ) := by
            calc g * (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) (x t) (y t)) * gᵀ
                = g * diagExp3 (b / (M : ℝ)) D a * (1 * Phi (b / (M : ℝ)) (x t) (y t)) * gᵀ := by
                    simp [Matrix.mul_assoc]
              _ = g * diagExp3 (b / (M : ℝ)) D a * ((gᵀ * g) * Phi (b / (M : ℝ)) (x t) (y t)) * gᵀ := by
                    rw [hg.orth_left]
              _ = (g * diagExp3 (b / (M : ℝ)) D a * gᵀ) * (g * Phi (b / (M : ℝ)) (x t) (y t) * gᵀ) := by
                    simp [Matrix.mul_assoc]
      _ = diagExp3 (b / (M : ℝ)) D a *
            (∑ u' : Fin 4, ∑ v' : Fin 4, (lift4 g u' (x t) * lift4 g v' (y t)) • Phi (b / (M : ℝ)) u' v') := by
            rw [hgV, Phi_cov hg]
      _ = ∑ p : Fin 4 × Fin 4,
            (lift4 g p.1 (x t) * lift4 g p.2 (y t)) •
              (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) p.1 p.2) := by
            rw [Fintype.sum_prod_type, Matrix.mul_sum]
            refine Finset.sum_congr rfl fun u' _ => ?_
            rw [Matrix.mul_sum]
            refine Finset.sum_congr rfl fun v' _ => by rw [Matrix.mul_smul]
  simp_rw [hfactor]
  rw [sliceProd_sum, Matrix.trace_sum]
  let e : Word M × Word M ≃ (Fin M → Fin 4 × Fin 4) :=
    { toFun := fun p t => (p.1 t, p.2 t)
      invFun := fun f => (fun t => (f t).1, fun t => (f t).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ fun ⟨u, v⟩ => ?_
  simp only [e, sliceProd_smul, Matrix.trace_smul, smul_eq_mul, K_mat, Matrix.of_apply]
  -- Wait: check if LHS and RHS match!
  rfl

/-! ### Uniform Hilbert–Schmidt Bound `Tr(K_mat^2) ≤ 9 * exp(2 * b * (|D| + |a| + 3))` -/

section HSBound
open scoped Matrix.Norms.Operator

private lemma norm_G_mat_le_one (α : Fin 3) : ‖G_mat α‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  have h : Finset.univ.sup (fun i : Fin 3 => ∑ j : Fin 3, ‖(G_mat α) i j‖₊) ≤ (1 : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    fin_cases α <;> fin_cases i <;> simp [G_mat, Fin.sum_univ_three]
  exact_mod_cast h

private lemma norm_diagExp3_le {τ : ℝ} (hτ : 0 ≤ τ) (D a : ℝ) :
    ‖diagExp3 τ D a‖ ≤ Real.exp (τ * (|D| + |a|)) := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : Real.exp (-τ * (D + a)) ≤ Real.exp (τ * (|D| + |a|)) := by
    refine Real.exp_le_exp.mpr ?_
    have hD : -D ≤ |D| := neg_le_abs D
    have ha : -a ≤ |a| := neg_le_abs a
    nlinarith
  have h2 : Real.exp (-τ * a) ≤ Real.exp (τ * (|D| + |a|)) := by
    refine Real.exp_le_exp.mpr ?_
    have ha : -a ≤ |a| := neg_le_abs a
    have hD : 0 ≤ |D| := abs_nonneg D
    nlinarith
  have hsup : Finset.univ.sup (fun i : Fin 3 => ∑ j : Fin 3, ‖(diagExp3 τ D a) i j‖₊) ≤
      Real.toNNReal (Real.exp (τ * (|D| + |a|))) := by
    refine Finset.sup_le fun i _ => ?_
    fin_cases i <;>
    · simp only [diagExp3, Fin.sum_univ_three, Matrix.diagonal_apply]
      norm_num
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.exp_pos _).le, coe_nnNorm,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← neg_mul]
      first | exact h1 | exact h2
  have hcoe : ((Finset.univ.sup (fun i : Fin 3 => ∑ j : Fin 3, ‖(diagExp3 τ D a) i j‖₊) : NNReal) : ℝ) ≤
      Real.exp (τ * (|D| + |a|)) := by
    calc ((Finset.univ.sup (fun i : Fin 3 => ∑ j : Fin 3, ‖(diagExp3 τ D a) i j‖₊) : NNReal) : ℝ)
        ≤ (Real.toNNReal (Real.exp (τ * (|D| + |a|))) : ℝ) := by exact_mod_cast hsup
      _ = Real.exp (τ * (|D| + |a|)) := Real.coe_toNNReal _ (Real.exp_pos _).le
  exact hcoe

private noncomputable def phiNormSq (τ : ℝ) : Fin 4 → Fin 4 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨_ + 1, _⟩ => τ
  | ⟨_ + 1, _⟩, ⟨0, _⟩ => τ
  | ⟨_ + 1, _⟩, ⟨_ + 1, _⟩ => 0

private lemma norm_one3_le : ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  have h : Finset.univ.sup (fun i : Fin 3 => ∑ j : Fin 3, ‖(1 : Matrix (Fin 3) (Fin 3) ℝ) i j‖₊) ≤ 1 := by
    refine Finset.sup_le fun i _ => ?_
    fin_cases i <;> simp [Fin.sum_univ_three, Matrix.one_apply]
  exact_mod_cast h

private lemma norm_Phi_le {τ : ℝ} (hτ : 0 ≤ τ) (u v : Fin 4) :
    ‖Phi τ u v‖ ≤ Real.sqrt (phiNormSq τ u v) := by
  cases u using Fin.cases with
  | zero =>
    cases v using Fin.cases with
    | zero =>
      change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ Real.sqrt 1
      rw [Real.sqrt_one]; exact norm_one3_le
    | succ β =>
      change ‖Real.sqrt τ • G_mat β‖ ≤ Real.sqrt τ
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (norm_G_mat_le_one β)
  | succ α =>
    cases v using Fin.cases with
    | zero =>
      change ‖Real.sqrt τ • G_mat α‖ ≤ Real.sqrt τ
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (norm_G_mat_le_one α)
    | succ β =>
      change ‖(0 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ Real.sqrt 0
      simp

private lemma finset_prod_le_prod {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hga : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfs : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hga hgs hfs (le_trans hfa hga)

private lemma norm_sliceProd_le :
    ∀ {M : ℕ} (f : Fin M → Matrix (Fin 3) (Fin 3) ℝ), ‖sliceProd f‖ ≤ ∏ t : Fin M, ‖f t‖
  | 0, _ => by
      simp only [sliceProd, Finset.univ_eq_empty, Finset.prod_empty]
      exact norm_one3_le
  | M + 1, f => by
      simp only [sliceProd, Fin.prod_univ_castSucc]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_sliceProd_le (fun t : Fin M => f t.castSucc)) (norm_nonneg _))

/-- Uniform Hilbert–Schmidt bound `Tr(K_mat^2) ≤ 9 * exp(2 * b * (|D| + |a| + 3))` for all `M ≥ 1`, `b > 0`. -/
theorem K_mat_hilbert_schmidt_le {M : ℕ} (hM : 1 ≤ M) (D a : ℝ) {b : ℝ} (hb : 0 < b) :
    Matrix.trace ((K_mat M D a b) ^ 2) ≤ 9 * Real.exp (2 * b * (|D| + |a| + 3)) := by
  rw [trace_sq_eq_sum_entries_sq (K_mat_transpose M D a b)]
  let τ : ℝ := b / (M : ℝ)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hτ_nn : 0 ≤ τ := div_nonneg hb.le hMpos.le
  have hentry : ∀ x y : Word M,
      (K_mat M D a b x y) ^ 2 ≤
        9 * Real.exp (2 * b * (|D| + |a|)) * ∏ t : Fin M, phiNormSq τ (x t) (y t) := by
    intro x y
    have htr : |K_mat M D a b x y| ≤
        3 * Real.exp (b * (|D| + |a|)) * ∏ t : Fin M, Real.sqrt (phiNormSq τ (x t) (y t)) := by
      simp only [K_mat, Matrix.of_apply]
      have h1 := abs_trace_le_card_mul_opNorm
        (sliceProd (fun t : Fin M => diagExp3 τ D a * Phi τ (x t) (y t)))
      simp only [Fintype.card_fin, Nat.cast_ofNat] at h1
      have h2 := norm_sliceProd_le (fun t : Fin M => diagExp3 τ D a * Phi τ (x t) (y t))
      have h3 : ∏ t : Fin M, ‖diagExp3 τ D a * Phi τ (x t) (y t)‖ ≤
          ∏ t : Fin M, (Real.exp (τ * (|D| + |a|)) * Real.sqrt (phiNormSq τ (x t) (y t))) :=
        finset_prod_le_prod Finset.univ _ _ (fun _ _ => norm_nonneg _) fun t _ =>
          (norm_mul_le _ _).trans
            (mul_le_mul (norm_diagExp3_le hτ_nn D a) (norm_Phi_le hτ_nn (x t) (y t))
              (norm_nonneg _) (Real.exp_pos _).le)
      have h4 : ∏ t : Fin M, (Real.exp (τ * (|D| + |a|)) * Real.sqrt (phiNormSq τ (x t) (y t))) =
          Real.exp (b * (|D| + |a|)) * ∏ t : Fin M, Real.sqrt (phiNormSq τ (x t) (y t)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_nat_mul]
        congr 2; dsimp [τ]; field_simp [hMpos.ne']
      calc |Matrix.trace (sliceProd (fun t : Fin M => diagExp3 τ D a * Phi τ (x t) (y t)))|
          ≤ 3 * ‖sliceProd (fun t : Fin M => diagExp3 τ D a * Phi τ (x t) (y t))‖ := h1
        _ ≤ 3 * ∏ t : Fin M, ‖diagExp3 τ D a * Phi τ (x t) (y t)‖ :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ ≤ 3 * (Real.exp (b * (|D| + |a|)) * ∏ t : Fin M, Real.sqrt (phiNormSq τ (x t) (y t))) := by
            rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 3 * Real.exp (b * (|D| + |a|)) * ∏ t : Fin M, Real.sqrt (phiNormSq τ (x t) (y t)) := by ring
    have hsq := pow_le_pow_left₀ (abs_nonneg _) htr 2
    rw [sq_abs, mul_pow, mul_pow, ← Finset.prod_pow] at hsq
    have hprod_sq : ∏ t : Fin M, Real.sqrt (phiNormSq τ (x t) (y t)) ^ 2 =
        ∏ t : Fin M, phiNormSq τ (x t) (y t) := by
      refine Finset.prod_congr rfl fun t _ => Real.sq_sqrt ?_
      generalize x t = u; generalize y t = v
      fin_cases u <;> fin_cases v <;> simp [phiNormSq, hτ_nn]
    rw [hprod_sq, ← Real.exp_nat_mul] at hsq
    have h9 : (3 : ℝ) ^ 2 * Real.exp ((2 : ℕ) * (b * (|D| + |a|))) =
        9 * Real.exp (2 * b * (|D| + |a|)) := by
      rw [show (3 : ℝ) ^ 2 = 9 by norm_num,
        show ((2 : ℕ) : ℝ) * (b * (|D| + |a|)) = 2 * b * (|D| + |a|) by push_cast; ring]
    rw [h9] at hsq
    exact hsq
  calc ∑ x : Word M, ∑ y : Word M, (K_mat M D a b x y) ^ 2
      ≤ ∑ x : Word M, ∑ y : Word M,
          9 * Real.exp (2 * b * (|D| + |a|)) * ∏ t : Fin M, phiNormSq τ (x t) (y t) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hentry x y
    _ = 9 * Real.exp (2 * b * (|D| + |a|)) *
          ∑ x : Word M, ∑ y : Word M, ∏ t : Fin M, phiNormSq τ (x t) (y t) := by
        simp_rw [← Finset.mul_sum]
    _ = 9 * Real.exp (2 * b * (|D| + |a|)) * (1 + 6 * τ) ^ M := by
        congr 1
        have hpair_sum :
            (∑ x : Word M, ∑ y : Word M, ∏ t : Fin M, phiNormSq τ (x t) (y t)) =
              ∑ p : Word M × Word M, ∏ t : Fin M, phiNormSq τ (p.1 t) (p.2 t) :=
          (Fintype.sum_prod_type (fun p : Word M × Word M => ∏ t : Fin M, phiNormSq τ (p.1 t) (p.2 t))).symm
        rw [hpair_sum]
        let e : Word M × Word M ≃ (Fin M → Fin 4 × Fin 4) :=
          { toFun := fun p t => (p.1 t, p.2 t)
            invFun := fun f => (fun t => (f t).1, fun t => (f t).2)
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun _ => rfl }
        rw [Fintype.sum_equiv e (fun p => ∏ t : Fin M, phiNormSq τ (p.1 t) (p.2 t))
          (fun f => ∏ t : Fin M, phiNormSq τ (f t).1 (f t).2) (fun _ => rfl)]
        rw [show (∑ f : Fin M → Fin 4 × Fin 4, ∏ t : Fin M, phiNormSq τ (f t).1 (f t).2) =
            ∏ _t : Fin M, ∑ q : Fin 4 × Fin 4, phiNormSq τ q.1 q.2 from
          (Fintype.prod_sum (fun (_t : Fin M) (q : Fin 4 × Fin 4) => phiNormSq τ q.1 q.2)).symm]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        rw [Fintype.sum_prod_type]
        simp only [Fin.sum_univ_four, phiNormSq]
        ring
    _ ≤ 9 * Real.exp (2 * b * (|D| + |a|)) * Real.exp (6 * b) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : 1 + 6 * τ ≤ Real.exp (6 * τ) := by linarith [Real.add_one_le_exp (6 * τ)]
        calc (1 + 6 * τ) ^ M ≤ (Real.exp (6 * τ)) ^ M := pow_le_pow_left₀ (by positivity) h1 M
          _ = Real.exp (6 * b) := by
              rw [← Real.exp_nat_mul]; congr 1; dsimp [τ]; field_simp [hMpos.ne']
    _ = 9 * Real.exp (2 * b * (|D| + |a| + 3)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end HSBound

/-! ## 3. Exact Cycle Contraction `Tr(K_mat^n * U_mat g) = Tr(T_slice^M)` & `M → ∞` Limit -/

/-- Seam-twisted local slice matrix `Φ_τ^g(u, v) = ∑ z, (lift4 g z v) • Φ_τ(u, z)`. -/
noncomputable def PhiTwist (τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 4) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ z : Fin 4, lift4 g z v • Phi τ u z

/-- Local matrix inserted on site `s : Fin n` for bond-slice labels `c : Fin n → Fin 4`
(with seam bond `n - 1` twisted by `g` on site `0`). -/
noncomputable def sitePhi (n : ℕ) (hn : 3 ≤ n) (τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin n → Fin 4) (s : Fin n) : Matrix (Fin 3) (Fin 3) ℝ :=
  if s.val = 0 then
    PhiTwist τ g (c s) (c ⟨n - 1, by omega⟩)
  else
    Phi τ (c s) (c ⟨s.val - 1, by omega⟩)

/-- Single-slice physical operator `T_slice` on `Spin1Cfg n` (`dim 3^n`). -/
noncomputable def T_slice (n : ℕ) (hn : 3 ≤ n) (D a τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  Matrix.of fun σ σ' =>
    ∑ c : Fin n → Fin 4, ∏ s : Fin n, (diagExp3 τ D a * sitePhi n hn τ g c s) (σ s) (σ' s)

private lemma K_mul_U_entry (M : ℕ) (D a b : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (x y : Word M) :
    (K_mat M D a b * U_mat M g) x y =
      Matrix.trace (sliceProd (fun t : Fin M =>
        diagExp3 (b / (M : ℝ)) D a * PhiTwist (b / (M : ℝ)) g (x t) (y t))) := by
  rw [Matrix.mul_apply]
  simp only [K_mat, U_mat, Matrix.of_apply, PhiTwist]
  have h1 : ∀ t : Fin M,
      diagExp3 (b / (M : ℝ)) D a * ∑ z : Fin 4, lift4 g z (y t) • Phi (b / (M : ℝ)) (x t) z =
        ∑ z : Fin 4, lift4 g z (y t) • (diagExp3 (b / (M : ℝ)) D a * Phi (b / (M : ℝ)) (x t) z) := fun t => by
    rw [Matrix.mul_sum]
    exact Finset.sum_congr rfl fun z _ => Matrix.mul_smul _ _ _
  simp_rw [h1]
  rw [sliceProd_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sliceProd_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]

private lemma pow_entry_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) : ∀ (m : ℕ) (x y : ι),
      (K ^ (m + 1)) x y =
        ∑ w : Fin m → ι,
          ∏ j : Fin (m + 1),
            K (if h : j.val = 0 then x else w ⟨j.val - 1, by omega⟩)
              (if h : j.val < m then w ⟨j.val, h⟩ else y)
  | 0, x, y => by simp
  | m + 1, x, y => by
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [pow_entry_eq_sum K m]
      simp_rw [Finset.sum_mul]
      let F : ι × (Fin m → ι) → ℝ := fun p =>
        (∏ j : Fin (m + 1),
          K (if h : j.val = 0 then x else p.2 ⟨j.val - 1, by omega⟩)
            (if h : j.val < m then p.2 ⟨j.val, h⟩ else p.1)) * K p.1 y
      have hprod : (∑ z : ι, ∑ w : Fin m → ι, F (z, w)) = ∑ p : ι × (Fin m → ι), F p :=
        (Fintype.sum_prod_type F).symm
      change (∑ z : ι, ∑ w : Fin m → ι, F (z, w)) = _
      rw [hprod]
      let e : ι × (Fin m → ι) ≃ (Fin (m + 1) → ι) :=
        { toFun := fun p => Fin.snoc p.2 p.1
          invFun := fun w => (w (Fin.last m), fun t : Fin m => w t.castSucc)
          left_inv := fun ⟨z, w⟩ => by ext <;> simp
          right_inv := fun w => by
            ext t; refine Fin.lastCases ?_ ?_ t <;> simp }
      refine Fintype.sum_equiv e F _ fun ⟨z, w⟩ => ?_
      dsimp only [F]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      have hlast1 : (if h : (Fin.last (m + 1)).val = 0 then x else e (z, w) ⟨(Fin.last (m + 1)).val - 1, by omega⟩) = z := by
        have hne : (Fin.last (m + 1)).val ≠ 0 := by simp
        rw [dif_neg hne]
        have hidx : (⟨(Fin.last (m + 1)).val - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
        rw [hidx]; simp [e]
      have hlast2 : (if h : (Fin.last (m + 1)).val < m + 1 then e (z, w) ⟨(Fin.last (m + 1)).val, h⟩ else y) = y := by
        simp
      rw [hlast1, hlast2]
      have he_val : ∀ (k : ℕ) (hk : k < m + 1),
          e (z, w) ⟨k, hk⟩ = if h : k < m then w ⟨k, h⟩ else z := by
        intro k hk
        have hdef : e (z, w) = Fin.snoc (α := fun _ => ι) w z := rfl
        rw [hdef]
        by_cases hkm : k < m
        · rw [dif_pos hkm]
          have hcast : (⟨k, hk⟩ : Fin (m + 1)) = (⟨k, hkm⟩ : Fin m).castSucc := rfl
          rw [hcast, Fin.snoc_castSucc]
        · rw [dif_neg hkm]
          have hlast : (⟨k, hk⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by dsimp; omega)
          rw [hlast, Fin.snoc_last]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Fin.val_castSucc]
      have hjlt : j.val < m + 1 := j.isLt
      by_cases hj0 : j.val = 0
      · by_cases hjm : j.val < m
        · rw [dif_pos hj0, dif_pos hjm, dif_pos hj0, dif_pos hjlt, he_val j.val hjlt, dif_pos hjm]
        · rw [dif_pos hj0, dif_neg hjm, dif_pos hj0, dif_pos hjlt, he_val j.val hjlt, dif_neg hjm]
      · have hprev : j.val - 1 < m := by omega
        have hprev1 : j.val - 1 < m + 1 := by omega
        by_cases hjm : j.val < m
        · rw [dif_neg hj0, dif_pos hjm, dif_neg hj0, dif_pos hjlt,
            he_val (j.val - 1) hprev1, dif_pos hprev, he_val j.val hjlt, dif_pos hjm]
        · rw [dif_neg hj0, dif_neg hjm, dif_neg hj0, dif_pos hjlt,
            he_val (j.val - 1) hprev1, dif_pos hprev, he_val j.val hjlt, dif_neg hjm]

private lemma trace_pow_mul_eq_cycle_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K U : Matrix ι ι ℝ) {n : ℕ} (hn : 3 ≤ n) :
    Matrix.trace (K ^ n * U) =
      ∑ w : Fin n → ι,
        (K * U) (w ⟨0, by omega⟩) (w ⟨n - 1, by omega⟩) *
        ∏ j : Fin (n - 1), K (w ⟨j.val + 1, by omega⟩) (w ⟨j.val, by omega⟩) := by
  have hn_eq : n = (n - 2) + 2 := by omega
  have hKU : K ^ n * U = K ^ ((n - 2) + 1) * (K * U) := by
    conv_lhs => rw [hn_eq, pow_succ, Matrix.mul_assoc]
  rw [hKU, Matrix.trace]
  have hdiag : ∀ x : ι, Matrix.diag (K ^ ((n - 2) + 1) * (K * U)) x =
      ∑ y : ι, (K ^ ((n - 2) + 1)) x y * (K * U) y x := fun x => Matrix.mul_apply
  simp_rw [hdiag, pow_entry_eq_sum K (n - 2), Finset.sum_mul]
  let G : (ι × ι) × (Fin (n - 2) → ι) → ℝ := fun p =>
    (∏ j : Fin ((n - 2) + 1),
      K (if h : j.val = 0 then p.1.1 else p.2 ⟨j.val - 1, by omega⟩)
        (if h : j.val < n - 2 then p.2 ⟨j.val, h⟩ else p.1.2)) * (K * U) p.1.2 p.1.1
  have hprod : (∑ x : ι, ∑ y : ι, ∑ v : Fin (n - 2) → ι, G ((x, y), v)) =
      ∑ p : (ι × ι) × (Fin (n - 2) → ι), G p := by
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
  change (∑ x : ι, ∑ y : ι, ∑ v : Fin (n - 2) → ι, G ((x, y), v)) = _
  rw [hprod]
  let e : (ι × ι) × (Fin (n - 2) → ι) ≃ (Fin n → ι) :=
    { toFun := fun p s =>
        if hs0 : s.val = 0 then p.1.2
        else if hsn : s.val = n - 1 then p.1.1
        else p.2 ⟨n - 2 - s.val, by omega⟩
      invFun := fun w => ((w ⟨n - 1, by omega⟩, w ⟨0, by omega⟩), fun k => w ⟨n - 2 - k.val, by omega⟩)
      left_inv := fun ⟨⟨x, y⟩, v⟩ => by
        ext
        · simp [show n - 1 ≠ 0 by omega]
        · simp
        · rename_i k
          have h1 : n - 2 - k.val ≠ 0 := by omega
          have h2 : n - 2 - k.val ≠ n - 1 := by omega
          simp only [h1, dite_false, h2]
          congr 1; ext; dsimp; omega
      right_inv := fun w => by
        funext s
        dsimp only
        by_cases hs0 : s.val = 0
        · rw [dif_pos hs0]; exact congrArg w (Fin.ext (by dsimp; omega))
        · by_cases hsn : s.val = n - 1
          · rw [dif_neg hs0, dif_pos hsn]; exact congrArg w (Fin.ext (by dsimp; omega))
          · rw [dif_neg hs0, dif_neg hsn]; exact congrArg w (Fin.ext (by dsimp; omega)) }
  refine Fintype.sum_equiv e G _ fun ⟨⟨x, y⟩, v⟩ => ?_
  dsimp only [G]
  rw [mul_comm]
  have hw0 : e ((x, y), v) ⟨0, by omega⟩ = y := by simp [e]
  have hwn1 : e ((x, y), v) ⟨n - 1, by omega⟩ = x := by simp [e, show n - 1 ≠ 0 by omega]
  rw [hw0, hwn1]
  congr 1
  let rev : Fin ((n - 2) + 1) ≃ Fin (n - 1) :=
    { toFun := fun j => ⟨(n - 2) - j.val, by omega⟩
      invFun := fun j => ⟨(n - 2) - j.val, by omega⟩
      left_inv := fun j => Fin.ext (by dsimp; omega)
      right_inv := fun j => Fin.ext (by dsimp; omega) }
  refine Fintype.prod_equiv rev _ _ fun j => ?_
  dsimp only [rev, e]
  have hjlt : j.val < (n - 2) + 1 := j.isLt
  have harg1 : (if h : j.val = 0 then x else v ⟨j.val - 1, by omega⟩) =
      (if hs0 : n - 2 - j.val + 1 = 0 then y
       else if hsn : n - 2 - j.val + 1 = n - 1 then x
       else v ⟨n - 2 - (n - 2 - j.val + 1), by omega⟩) := by
    by_cases hj0 : j.val = 0
    · have h1 : n - 2 - j.val + 1 ≠ 0 := by omega
      have h2 : n - 2 - j.val + 1 = n - 1 := by omega
      rw [dif_pos hj0, dif_neg h1, dif_pos h2]
    · have h1 : n - 2 - j.val + 1 ≠ 0 := by omega
      have h2 : n - 2 - j.val + 1 ≠ n - 1 := by omega
      rw [dif_neg hj0, dif_neg h1, dif_neg h2]
      congr 1; exact Fin.ext (by dsimp; omega)
  have harg2 : (if h : j.val < n - 2 then v ⟨j.val, h⟩ else y) =
      (if hs0 : n - 2 - j.val = 0 then y
       else if hsn : n - 2 - j.val = n - 1 then x
       else v ⟨n - 2 - (n - 2 - j.val), by omega⟩) := by
    by_cases hjm : j.val < n - 2
    · have h1 : n - 2 - j.val ≠ 0 := by omega
      have h2 : n - 2 - j.val ≠ n - 1 := by omega
      rw [dif_pos hjm, dif_neg h1, dif_neg h2]
      congr 1; exact Fin.ext (by dsimp; omega)
    · have h1 : n - 2 - j.val = 0 := by omega
      rw [dif_neg hjm, dif_pos h1]
  exact congrArg₂ K harg1 harg2

private lemma T_slice_pow_entry (n : ℕ) (hn : 3 ≤ n) (D a τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    ∀ (M : ℕ) (σ σ' : Spin1Cfg n),
      ((T_slice n hn D a τ g) ^ M) σ σ' =
        ∑ c : Fin M → Fin n → Fin 4,
          ∏ s : Fin n,
            (sliceProd (fun t : Fin M => diagExp3 τ D a * sitePhi n hn τ g (c t) s)) (σ s) (σ' s)
  | 0, σ, σ' => by
      simp only [pow_zero, Matrix.one_apply, sliceProd, Fintype.sum_unique]
      by_cases h : σ = σ'
      · subst h
        rw [if_pos rfl]
        exact (Finset.prod_eq_one fun s _ => Matrix.one_apply_eq (σ s)).symm
      · rw [if_neg h]
        have hex : ∃ s : Fin n, σ s ≠ σ' s := by
          by_contra hall; push_neg at hall; exact h (funext hall)
        rcases hex with ⟨s, hs⟩
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ s) (Matrix.one_apply_ne hs)
  | M + 1, σ, σ' => by
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [T_slice_pow_entry n hn D a τ g M, T_slice, Matrix.of_apply]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Spin1Cfg n)))]
      let H : (Fin M → Fin n → Fin 4) × (Fin n → Fin 4) → ℝ := fun p =>
        ∑ μ : Spin1Cfg n,
          (∏ s : Fin n, sliceProd (fun t => diagExp3 τ D a * sitePhi n hn τ g (p.1 t) s) (σ s) (μ s)) *
          (∏ s : Fin n, (diagExp3 τ D a * sitePhi n hn τ g p.2 s) (μ s) (σ' s))
      have hprod : (∑ c1, ∑ c2, H (c1, c2)) = ∑ p, H p := (Fintype.sum_prod_type H).symm
      change (∑ c1, ∑ c2, H (c1, c2)) = _
      rw [hprod]
      let e : (Fin M → Fin n → Fin 4) × (Fin n → Fin 4) ≃ (Fin (M + 1) → Fin n → Fin 4) :=
        { toFun := fun p => Fin.snoc p.1 p.2
          invFun := fun c => (fun t : Fin M => c t.castSucc, c (Fin.last M))
          left_inv := fun ⟨c1, c2⟩ => by ext t s <;> simp
          right_inv := fun c => by
            ext t s; refine Fin.lastCases ?_ ?_ t <;> simp }
      refine Fintype.sum_equiv e H _ fun ⟨c1, c2⟩ => ?_
      dsimp only [H]
      simp_rw [← Finset.prod_mul_distrib]
      have hps := Fintype.prod_sum (fun (s : Fin n) (a3 : Fin 3) =>
        sliceProd (fun t => diagExp3 τ D a * sitePhi n hn τ g (c1 t) s) (σ s) a3 *
        (diagExp3 τ D a * sitePhi n hn τ g c2 s) a3 (σ' s))
      rw [← hps]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hcast : (fun t : Fin M => diagExp3 τ D a * sitePhi n hn τ g (e (c1, c2) t.castSucc) s) =
          (fun t : Fin M => diagExp3 τ D a * sitePhi n hn τ g (c1 t) s) :=
        funext fun t => by simp [e]
      have hlast : e (c1, c2) (Fin.last M) = c2 := by simp [e]
      change ∑ a3 : Fin 3, sliceProd (fun t => diagExp3 τ D a * sitePhi n hn τ g (c1 t) s) (σ s) a3 *
          (diagExp3 τ D a * sitePhi n hn τ g c2 s) a3 (σ' s) =
        (sliceProd (fun t : Fin M => diagExp3 τ D a * sitePhi n hn τ g (e (c1, c2) t.castSucc) s) *
          (diagExp3 τ D a * sitePhi n hn τ g (e (c1, c2) (Fin.last M)) s)) (σ s) (σ' s)
      rw [hcast, hlast, Matrix.mul_apply]

/-- **Exact Cycle Contraction Identity**: for every `n ≥ 3`, `M : ℕ`, `D, a, b : ℝ`, and `g`,
`Tr((K_mat M D a b)^n * U_mat M g) = Tr((T_slice n hn D a (b / M) g)^M)`. -/
theorem trace_K_pow_mul_U_eq_trace_T_slice_pow {n : ℕ} (hn : 3 ≤ n) (M : ℕ)
    (D a b : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace ((K_mat M D a b) ^ n * U_mat M g) =
      Matrix.trace ((T_slice n hn D a (b / (M : ℝ)) g) ^ M) := by
  rw [trace_pow_mul_eq_cycle_sum _ _ hn]
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, T_slice_pow_entry n hn D a (b / (M : ℝ)) g M]
  rw [Finset.sum_comm]
  let e : (Fin n → Word M) ≃ (Fin M → Fin n → Fin 4) :=
    { toFun := fun w t s => w s t
      invFun := fun c s t => c t s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ fun w => ?_
  have hsplit : ∀ f : Fin n → ℝ,
      (∏ s : Fin n, f s) = f ⟨0, by omega⟩ * ∏ j : Fin (n - 1), f ⟨j.val + 1, by omega⟩ := fun f => by
    let e' : Option (Fin (n - 1)) ≃ Fin n :=
      { toFun := fun o => match o with
          | none => ⟨0, by omega⟩
          | some j => ⟨j.val + 1, by omega⟩
        invFun := fun s => if h : s.val = 0 then none else some ⟨s.val - 1, by omega⟩
        left_inv := fun o => by cases o <;> simp
        right_inv := fun s => by
          by_cases h : s.val = 0
          · simp [h]; exact Fin.ext h.symm
          · simp [h]; ext; dsimp; omega }
    rw [← Fintype.prod_equiv e' (fun o => f (e' o)) f (fun _ => rfl), Fintype.prod_option]
    rfl
  have hps := Fintype.prod_sum (fun (s : Fin n) (a3 : Fin 3) =>
    (sliceProd fun t => diagExp3 (b / (M : ℝ)) D a * sitePhi n hn (b / (M : ℝ)) g (e w t) s) a3 a3)
  rw [← hps, hsplit]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [K_mul_U_entry]
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun a3 _ => ?_
    simp [Matrix.diag_apply, e, sitePhi]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [K_mat, Matrix.of_apply, Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun a3 _ => ?_
    simp [e, sitePhi]

/-! ### First-Order Expansion of `T_slice` and `M → ∞` Convergence to `Z_spin1` -/

section SliceLimit
open scoped Matrix.Norms.Operator

private noncomputable def tensorProd (n : ℕ) (A : Fin n → Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  Matrix.of fun σ σ' => ∏ s : Fin n, A s (σ s) (σ' s)

private noncomputable def diagExpRing (n : ℕ) (D a τ : ℝ) : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  Matrix.diagonal (fun σ : Spin1Cfg n => ∏ s : Fin n, diagExp3 τ D a (σ s) (σ s))

private noncomputable def B_slice (n : ℕ) (hn : 3 ≤ n) (τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ :=
  ∑ c : Fin n → Fin 4, tensorProd n (sitePhi n hn τ g c)

private lemma T_slice_eq_mul (n : ℕ) (hn : 3 ≤ n) (D a τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    T_slice n hn D a τ g = diagExpRing n D a τ * B_slice n hn τ g := by
  ext σ σ'
  simp only [T_slice, B_slice, diagExpRing, tensorProd, Matrix.of_apply, Matrix.diagonal_mul,
    Matrix.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [diagExp3, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

private lemma diagExpRing_eq_exp (n : ℕ) (D a τ : ℝ) :
    diagExpRing n D a τ = NormedSpace.exp ((-τ) • H_onsite n D a) := by
  rw [H_onsite_eq_diagonal]
  have hsmul : (-τ) • Matrix.diagonal (fun σ : Spin1Cfg n => ∑ j : Fin n, V_mat D a (σ j) (σ j)) =
      Matrix.diagonal (fun σ : Spin1Cfg n => (-τ) * ∑ j : Fin n, V_mat D a (σ j) (σ j)) := by
    ext σ σ'; simp [Matrix.diagonal_apply]
  rw [hsmul, Matrix.exp_diagonal]
  ext σ σ'
  simp only [diagExpRing, Matrix.diagonal_apply]
  split_ifs with h
  · let v : Spin1Cfg n → ℝ := fun σ => (-τ) * ∑ j : Fin n, V_mat D a (σ j) (σ j)
    have hpi : NormedSpace.exp v σ = Real.exp (v σ) := by
      rw [Real.exp_eq_exp_ℝ]
      have h1 := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) v
      have h2 : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * (v σ) ^ k) (NormedSpace.exp v σ) := by
        have hm := h1.map (Pi.evalAddMonoidHom (fun _ : Spin1Cfg n => ℝ) σ) (continuous_apply σ)
        exact hm.congr_fun fun k => by simp [NormedSpace.expSeries_apply_eq]
      have h3 : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * (v σ) ^ k) (NormedSpace.exp (v σ)) := by
        have hx := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (v σ)
        exact hx.congr_fun fun k => by rw [div_eq_inv_mul]
      exact h2.unique h3
    change (∏ s : Fin n, diagExp3 τ D a (σ s) (σ s)) = NormedSpace.exp v σ
    rw [hpi]
    dsimp only [v]
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    generalize σ j = u
    fin_cases u <;> simp [diagExp3, V_mat]
  · rfl

private lemma PhiTwist_zero_zero (τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    PhiTwist τ g 0 0 = 1 := by
  simp [PhiTwist, lift4, Phi, Fin.sum_univ_four]

private lemma PhiTwist_succ_zero (τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (α : Fin 3) :
    PhiTwist τ g α.succ 0 = Real.sqrt τ • G_mat α := by
  fin_cases α <;> simp [PhiTwist, lift4, Phi, Fin.sum_univ_four]

private lemma PhiTwist_zero_succ {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g)
    (τ : ℝ) (α : Fin 3) :
    PhiTwist τ g 0 α.succ = Real.sqrt τ • (g * G_mat α * gᵀ) := by
  rw [hg.cov α, Finset.smul_sum]
  fin_cases α <;>
    simp [PhiTwist, lift4, Phi, Fin.sum_univ_four, Fin.sum_univ_three, smul_smul, mul_comm]

private lemma PhiTwist_succ_succ (τ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (α β : Fin 3) :
    PhiTwist τ g α.succ β.succ = 0 := by
  fin_cases α <;> fin_cases β <;> simp [PhiTwist, lift4, Phi, Fin.sum_univ_four]

private lemma tensorProd_one (n : ℕ) : tensorProd n (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
  ext σ σ'
  simp only [tensorProd, Matrix.of_apply, Matrix.one_apply]
  by_cases h : σ = σ'
  · subst h; simp
  · rw [if_neg h]
    have hex : ∃ s : Fin n, σ s ≠ σ' s := by
      by_contra hall; push_neg at hall; exact h (funext hall)
    rcases hex with ⟨s, hs⟩
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

private lemma tensorProd_two_sites {n : ℕ} {j k : Fin n} (hjk : j ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorProd n (fun s => if s = j then A else if s = k then B else 1) =
      singleSite n j A * singleSite n k B := by
  ext σ σ'
  simp only [tensorProd, Matrix.of_apply]
  rw [Matrix.mul_apply]
  let μ : Spin1Cfg n := Function.update σ j (σ' j)
  rw [Finset.sum_eq_single μ]
  · simp only [singleSite, Matrix.of_apply]
    have h1 : ∀ m : Fin n, m ≠ j → σ m = μ m := fun m hm => by simp [μ, Function.update_of_ne hm]
    have hμj : μ j = σ' j := by simp [μ]
    have hμk : μ k = σ k := by simp [μ, Function.update_of_ne hjk.symm]
    have h2 : (∀ m : Fin n, m ≠ k → μ m = σ' m) ↔ (∀ m : Fin n, m ≠ j → m ≠ k → σ m = σ' m) := by
      constructor
      · intro h m hmj hmk; rw [h1 m hmj]; exact h m hmk
      · intro h m hmk
        by_cases hmj : m = j
        · rw [hmj]; exact hμj
        · rw [← h1 m hmj]; exact h m hmj hmk
    simp only [if_pos h1, h2, hμj, hμk]
    by_cases hall : ∀ m : Fin n, m ≠ j → m ≠ k → σ m = σ' m
    · rw [if_pos hall]
      have hsplit : (∏ s : Fin n, (if s = j then A else if s = k then B else 1) (σ s) (σ' s)) =
          A (σ j) (σ' j) * B (σ k) (σ' k) *
            ∏ s ∈ (Finset.univ.erase j).erase k, (1 : Matrix (Fin 3) (Fin 3) ℝ) (σ s) (σ' s) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        have hkmem : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
        rw [← Finset.mul_prod_erase (Finset.univ.erase j) _ hkmem]
        simp only [ite_true, hjk.symm, ite_false]
        rw [mul_assoc]
        congr 2
        refine Finset.prod_congr rfl fun s hs => ?_
        have hsk : s ≠ k := (Finset.mem_erase.mp hs).1
        have hsj : s ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
        simp [hsj, hsk]
      rw [hsplit]
      have hone : ∏ s ∈ (Finset.univ.erase j).erase k, (1 : Matrix (Fin 3) (Fin 3) ℝ) (σ s) (σ' s) = 1 := by
        refine Finset.prod_eq_one fun s hs => ?_
        have hsk : s ≠ k := (Finset.mem_erase.mp hs).1
        have hsj : s ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
        simp [Matrix.one_apply, hall s hsj hsk]
      rw [hone, mul_one]
    · rw [if_neg hall, mul_zero]
      push_neg at hall
      rcases hall with ⟨m, hmj, hmk, hmne⟩
      refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
      simp [hmj, hmk, Matrix.one_apply, hmne]
  · intro ρ _ hρ
    simp only [singleSite, Matrix.of_apply]
    split_ifs with h1 h2
    · exfalso; apply hρ; funext m
      by_cases hmj : m = j
      · rw [hmj]; simp [μ, h2 j hjk]
      · simp [μ, Function.update_of_ne hmj, (h1 m hmj).symm]
    · simp
    · simp
    · simp
  · intro h; exact absurd (Finset.mem_univ μ) h

private lemma sitePhi_single_bond {n : ℕ} (hn : 3 ≤ n) {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : IsSpin1Rot g) {τ : ℝ} (hτ : 0 ≤ τ) (j : Fin n) (α : Fin 3) :
    tensorProd n (sitePhi n hn τ g (Function.update (0 : Fin n → Fin 4) j α.succ)) =
      τ • (singleSite n j (G_mat α) *
        singleSite n (nextSite hn j) ((if j.val + 1 = n then g else rotI) * G_mat α * (if j.val + 1 = n then g else rotI)ᵀ)) := by
  let c : Fin n → Fin 4 := Function.update (0 : Fin n → Fin 4) j α.succ
  let k : Fin n := nextSite hn j
  have hjk : j ≠ k := ne_nextSite hn j
  let g_eff : Matrix (Fin 3) (Fin 3) ℝ := if j.val + 1 = n then g else rotI
  have hsite : ∀ s : Fin n,
      sitePhi n hn τ g c s =
        if s = j then Real.sqrt τ • G_mat α
        else if s = k then Real.sqrt τ • (g_eff * G_mat α * g_effᵀ)
        else 1 := fun s => by
    unfold sitePhi
    by_cases hs0 : s.val = 0
    · rw [if_pos hs0]
      have hs_eq0 : s = ⟨0, by omega⟩ := Fin.ext hs0
      by_cases hj0 : j = s
      · subst hj0
        have hlast_ne : (⟨n - 1, by omega⟩ : Fin n) ≠ j := by
          intro h; have h1 : n - 1 = j.val := congrArg Fin.val h; omega
        simp only [c, Function.update_self, Function.update_of_ne hlast_ne, Pi.zero_apply,
          PhiTwist_succ_zero, ite_true]
      · have hcs : c s = 0 := by simp [c, Function.update_of_ne (Ne.symm hj0)]
        by_cases hjlast : j.val + 1 = n
        · have hjeq : j = ⟨n - 1, by omega⟩ := Fin.ext (show j.val = n - 1 by omega)
          have hks : s = k := Fin.ext (by rw [hs0]; simp [k, nextSite, hjlast])
          have hcs' : c s = 0 := hcs
          have hclast : c ⟨n - 1, by omega⟩ = α.succ := by rw [← hjeq]; simp [c]
          rw [hcs', hclast, PhiTwist_zero_succ hg, if_neg (Ne.symm hj0), if_pos hks]
          simp [g_eff, hjlast]
        · have hne_last : (⟨n - 1, by omega⟩ : Fin n) ≠ j := by
            intro h; have h1 : n - 1 = j.val := congrArg Fin.val h; have := j.isLt; omega
          have hks : s ≠ k := by
            intro h; have h1 : s.val = (j.val + 1) % n := congrArg Fin.val h; have := j.isLt
            have hlt : j.val + 1 < n := by omega
            rw [Nat.mod_eq_of_lt hlt] at h1; omega
          simp [c, hcs, Function.update_of_ne hne_last, PhiTwist_zero_zero, Ne.symm hj0, hks]
    · rw [if_neg hs0]
      have hprev_eq : (⟨s.val - 1, by omega⟩ : Fin n) = j ↔ s = k := by
        constructor
        · intro h; have hv : s.val - 1 = j.val := congrArg Fin.val h; have := s.isLt
          ext; simp only [k, nextSite]
          have hlt : j.val + 1 < n := by omega
          rw [Nat.mod_eq_of_lt hlt]; omega
        · intro h; have hv : s.val = (j.val + 1) % n := congrArg Fin.val h; have := j.isLt
          by_cases hjlast : j.val + 1 = n
          · rw [hjlast, Nat.mod_self] at hv; exact absurd hv hs0
          · have hlt : j.val + 1 < n := by omega
            rw [Nat.mod_eq_of_lt hlt] at hv; ext; dsimp; omega
      by_cases hjs : s = j
      · have hne_prev : (⟨s.val - 1, by omega⟩ : Fin n) ≠ j := by
          intro h; have := congrArg Fin.val h; have := congrArg Fin.val hjs; omega
        have hcp : c ⟨s.val - 1, by omega⟩ = 0 := by
          simp [c, Function.update_of_ne hne_prev]
        have hcs : c s = α.succ := by simp [c, hjs]
        rw [hcp, hcs, if_pos hjs]
        fin_cases α <;> rfl
      · have hcs : c s = 0 := by simp [c, Function.update_of_ne hjs]
        by_cases hsk : s = k
        · have hprev_j : (⟨s.val - 1, by omega⟩ : Fin n) = j := hprev_eq.mpr hsk
          have hjnotlast : j.val + 1 ≠ n := by
            intro hlast
            have hv : s.val = (j.val + 1) % n := congrArg Fin.val hsk
            rw [hlast, Nat.mod_self] at hv; exact hs0 hv
          have hcp : c ⟨s.val - 1, by omega⟩ = α.succ := by simp [c, hprev_j]
          rw [hcs, hcp, if_neg hjs, if_pos hsk]
          simp only [g_eff, hjnotlast, ite_false, rotI, Matrix.one_mul, Matrix.transpose_one,
            Matrix.mul_one]
          fin_cases α <;> rfl
        · have hne_prev : (⟨s.val - 1, by omega⟩ : Fin n) ≠ j := fun h => hsk (hprev_eq.mp h)
          simp [c, hcs, Function.update_of_ne hne_prev, hjs, hsk, Phi]
  have htp : tensorProd n (sitePhi n hn τ g c) =
      tensorProd n (fun s => if s = j then Real.sqrt τ • G_mat α
        else if s = k then Real.sqrt τ • (g_eff * G_mat α * g_effᵀ) else 1) := by
    congr 1; funext s; exact hsite s
  rw [htp, tensorProd_two_sites hjk]
  have hss1 : singleSite n j (Real.sqrt τ • G_mat α) = Real.sqrt τ • singleSite n j (G_mat α) := by
    ext σ σ'; simp only [singleSite, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring
  have hss2 : singleSite n k (Real.sqrt τ • (g_eff * G_mat α * g_effᵀ)) =
      Real.sqrt τ • singleSite n k (g_eff * G_mat α * g_effᵀ) := by
    ext σ σ'; simp only [singleSite, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring
  rw [hss1, hss2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hτ]

private noncomputable def sitePhiUnit (n : ℕ) (hn : 3 ≤ n) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin n → Fin 4) (s : Fin n) : Matrix (Fin 3) (Fin 3) ℝ :=
  sitePhi n hn 1 g c s

private lemma sitePhi_eq_smul_unit (n : ℕ) (hn : 3 ≤ n) {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : IsSpin1Rot g) {τ : ℝ} (hτ : 0 ≤ τ) (c : Fin n → Fin 4) (s : Fin n) :
    sitePhi n hn τ g c s =
      ((if c s = 0 then 1 else Real.sqrt τ) *
       (if c (if s.val = 0 then ⟨n - 1, by omega⟩ else ⟨s.val - 1, by omega⟩) = 0 then 1 else Real.sqrt τ)) •
        sitePhiUnit n hn g c s := by
  unfold sitePhiUnit sitePhi
  by_cases hs0 : s.val = 0
  · simp only [hs0, ite_true]
    generalize c s = u
    generalize c ⟨n - 1, by omega⟩ = v
    cases u using Fin.cases with
    | zero =>
      cases v using Fin.cases with
      | zero => simp [PhiTwist_zero_zero]
      | succ β => simp [PhiTwist_zero_succ hg, Real.sqrt_one, Fin.succ_ne_zero]
    | succ α =>
      cases v using Fin.cases with
      | zero => simp [PhiTwist_succ_zero, Real.sqrt_one, Fin.succ_ne_zero]
      | succ β => simp [PhiTwist_succ_succ]
  · simp only [hs0, ite_false]
    generalize c s = u
    generalize c ⟨s.val - 1, by omega⟩ = v
    cases u using Fin.cases with
    | zero =>
      cases v using Fin.cases with
      | zero => simp [Phi]
      | succ β =>
        simp only [ite_true, Fin.succ_ne_zero, ite_false, one_mul]
        change Real.sqrt τ • G_mat β = Real.sqrt τ • (Real.sqrt 1 • G_mat β)
        simp [Real.sqrt_one]
    | succ α =>
      cases v using Fin.cases with
      | zero =>
        simp only [ite_true, Fin.succ_ne_zero, ite_false, mul_one]
        change Real.sqrt τ • G_mat α = Real.sqrt τ • (Real.sqrt 1 • G_mat α)
        simp [Real.sqrt_one]
      | succ β =>
        change (0 : Matrix (Fin 3) (Fin 3) ℝ) = _ • (0 : Matrix (Fin 3) (Fin 3) ℝ)
        simp

private lemma tensorProd_sitePhi_eq_pow_mul_unit (n : ℕ) (hn : 3 ≤ n)
    {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) {τ : ℝ} (hτ : 0 ≤ τ) (c : Fin n → Fin 4) :
    tensorProd n (sitePhi n hn τ g c) =
      (τ ^ (Finset.univ.filter fun j : Fin n => c j ≠ 0).card) • tensorProd n (sitePhiUnit n hn g c) := by
  ext σ σ'
  simp only [tensorProd, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hrew : ∀ s : Fin n,
      sitePhi n hn τ g c s (σ s) (σ' s) =
        ((if c s = 0 then 1 else Real.sqrt τ) *
         (if c (if s.val = 0 then ⟨n - 1, by omega⟩ else ⟨s.val - 1, by omega⟩) = 0 then 1 else Real.sqrt τ)) *
          sitePhiUnit n hn g c s (σ s) (σ' s) := fun s => by
    rw [sitePhi_eq_smul_unit n hn hg hτ c s]; rfl
  simp_rw [hrew, Finset.prod_mul_distrib]
  congr 1
  let prev : Fin n ≃ Fin n :=
    { toFun := fun s => if s.val = 0 then ⟨n - 1, by omega⟩ else ⟨s.val - 1, by omega⟩
      invFun := fun s => nextSite hn s
      left_inv := fun s => by
        by_cases h : s.val = 0
        · simp only [h, ite_true, nextSite]; ext; dsimp
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self]; exact h.symm
        · simp only [h, ite_false, nextSite]; ext; dsimp
          rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt s.isLt]
      right_inv := fun s => by
        by_cases h : s.val + 1 = n
        · have hmod : (nextSite hn s).val = 0 := by simp [nextSite, h]
          simp only [hmod, ite_true]; ext; dsimp; omega
        · have hlt : s.val + 1 < n := by omega
          have hmod : (nextSite hn s).val = s.val + 1 := by
            simp only [nextSite]; exact Nat.mod_eq_of_lt hlt
          have hne0 : (nextSite hn s).val ≠ 0 := by omega
          simp only [hne0, ite_false]; ext; dsimp; omega }
  have hprev : (∏ s : Fin n, if c (prev s) = 0 then (1 : ℝ) else Real.sqrt τ) =
      ∏ s : Fin n, if c s = 0 then (1 : ℝ) else Real.sqrt τ :=
    Fintype.prod_equiv prev _ _ fun _ => rfl
  change (∏ s : Fin n, if c s = 0 then (1 : ℝ) else Real.sqrt τ) *
      (∏ s : Fin n, if c (prev s) = 0 then (1 : ℝ) else Real.sqrt τ) = _
  rw [hprev, ← Finset.prod_mul_distrib]
  have hpair : ∀ s : Fin n,
      (if c s = 0 then (1 : ℝ) else Real.sqrt τ) * (if c s = 0 then (1 : ℝ) else Real.sqrt τ) =
        if c s ≠ 0 then τ else 1 := fun s => by
    by_cases h : c s = 0
    · simp [h]
    · simp [h, Real.mul_self_sqrt hτ]
  simp_rw [hpair, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

/-- **First-order Trotter convergence**: for every `n ≥ 3`, `b > 0`, `D, a : ℝ`, and `IsSpin1Rot g`,
`Tr((K_mat M D a b)^n * U_mat M g) → Z_spin1 n hn D a g b` as `M → ∞`. -/
theorem tendsto_trace_K_pow_mul_U {n : ℕ} (hn : 3 ≤ n) (D a : ℝ) {b : ℝ} (hb : 0 < b)
    {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsSpin1Rot g) :
    Tendsto (fun M : ℕ => Matrix.trace ((K_mat M D a b) ^ n * U_mat M g))
      atTop (nhds (Z_spin1 n hn D a g b)) := by
  simp_rw [trace_K_pow_mul_U_eq_trace_T_slice_pow hn]
  unfold Z_spin1
  -- Decompose `B_slice τ = 1 - τ • H_bonds + R_B τ` for `0 ≤ τ ≤ 1`
  let S_hi : Finset (Fin n → Fin 4) :=
    Finset.univ.filter fun c => 2 ≤ (Finset.univ.filter fun j : Fin n => c j ≠ 0).card
  let C_B : ℝ := ∑ c ∈ S_hi, ‖tensorProd n (sitePhiUnit n hn g c)‖
  have hCB_nn : 0 ≤ C_B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB_decomp : ∀ {τ : ℝ}, 0 ≤ τ → τ ≤ 1 →
      ‖B_slice n hn τ g - (1 + (-τ) • H_bonds n hn g)‖ ≤ C_B * τ ^ 2 := by
    intro τ hτ0 hτ1
    let S_0 : Finset (Fin n → Fin 4) :=
      Finset.univ.filter fun c => (Finset.univ.filter fun j : Fin n => c j ≠ 0).card = 0
    let S_1 : Finset (Fin n → Fin 4) :=
      Finset.univ.filter fun c => (Finset.univ.filter fun j : Fin n => c j ≠ 0).card = 1
    have hpart : B_slice n hn τ g =
        (∑ c ∈ S_0, tensorProd n (sitePhi n hn τ g c)) +
        (∑ c ∈ S_1, tensorProd n (sitePhi n hn τ g c)) +
        (∑ c ∈ S_hi, tensorProd n (sitePhi n hn τ g c)) := by
      unfold B_slice
      have hdisj01 : Disjoint S_0 S_1 := Finset.disjoint_filter.mpr fun _ _ h0 h1 => by omega
      have hdisj01hi : Disjoint (S_0 ∪ S_1) S_hi := by
        rw [Finset.disjoint_left]
        intro c hc1 hc2
        simp only [Finset.mem_union, S_0, S_1, S_hi, Finset.mem_filter, Finset.mem_univ,
          true_and] at hc1 hc2
        omega
      have huniv : S_0 ∪ S_1 ∪ S_hi = Finset.univ := by
        ext c
        simp only [Finset.mem_union, S_0, S_1, S_hi, Finset.mem_filter, Finset.mem_univ,
          true_and, iff_true]
        omega
      rw [← huniv, Finset.sum_union hdisj01hi, Finset.sum_union hdisj01]
    have hsum0 : ∑ c ∈ S_0, tensorProd n (sitePhi n hn τ g c) = 1 := by
      have hS0 : S_0 = {0} := by
        ext c
        simp only [S_0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        exact ⟨fun h => funext fun j => by simpa using h j, fun h j => by simp [h]⟩
      rw [hS0, Finset.sum_singleton]
      have hsite0 : sitePhi n hn τ g 0 = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        funext s; unfold sitePhi; split_ifs <;> simp [PhiTwist_zero_zero, Phi]
      rw [hsite0, tensorProd_one]
    have hsum1 : ∑ c ∈ S_1, tensorProd n (sitePhi n hn τ g c) = (-τ) • H_bonds n hn g := by
      let f1 : Fin n × Fin 3 → (Fin n → Fin 4) := fun p => Function.update 0 p.1 p.2.succ
      have hf1_bij : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin 3)), f1 p ∈ S_1 := fun ⟨j, α⟩ _ => by
        simp only [S_1, f1, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfilt : (Finset.univ.filter fun m : Fin n => Function.update (0 : Fin n → Fin 4) j α.succ m ≠ 0) = {j} := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          by_cases hmj : m = j
          · subst hmj; simp
          · simp [Function.update_of_ne hmj, hmj]
        rw [hfilt, Finset.card_singleton]
      have hf1_inj : ∀ p₁ ∈ (Finset.univ : Finset (Fin n × Fin 3)),
          ∀ p₂ ∈ (Finset.univ : Finset (Fin n × Fin 3)), f1 p₁ = f1 p₂ → p₁ = p₂ := by
        intro ⟨j₁, α₁⟩ _ ⟨j₂, α₂⟩ _ h
        have hval := congrFun h j₁
        by_cases hj : j₁ = j₂
        · subst hj
          simp only [f1, Function.update_self] at hval
          have : α₁ = α₂ := Fin.succ_inj.mp hval
          subst this; rfl
        · simp only [f1, Function.update_self, Function.update_of_ne hj, Pi.zero_apply] at hval
          exact absurd hval (Fin.succ_ne_zero _)
      have hf1_surj : ∀ c ∈ S_1, ∃ p, ∃ _hp : p ∈ (Finset.univ : Finset (Fin n × Fin 3)), f1 p = c := by
        intro c hc
        simp only [S_1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_one] at hc
        rcases hc with ⟨j, hj⟩
        have hcj_ne : c j ≠ 0 := by
          have : j ∈ Finset.univ.filter (fun m : Fin n => c m ≠ 0) := by rw [hj]; exact Finset.mem_singleton_self j
          exact (Finset.mem_filter.mp this).2
        obtain ⟨α, hα⟩ := Fin.eq_succ_of_ne_zero hcj_ne
        refine ⟨(j, α), Finset.mem_univ _, ?_⟩
        funext m
        by_cases hmj : m = j
        · subst hmj; simp [f1, hα]
        · have hm0 : c m = 0 := by
            by_contra hne
            have : m ∈ Finset.univ.filter (fun m : Fin n => c m ≠ 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
            rw [hj, Finset.mem_singleton] at this
            exact hmj this
          simp [f1, Function.update_of_ne hmj, hm0]
      rw [← Finset.sum_bij (fun p _ => f1 p) hf1_bij hf1_inj hf1_surj (fun _ _ => rfl)]
      rw [Fintype.sum_prod_type]
      unfold H_bonds bondOp
      simp only [Finset.smul_sum, smul_neg, neg_smul, neg_neg, Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact Finset.sum_congr rfl fun α _ => sitePhi_single_bond hn hg hτ0 j α
    rw [hpart, hsum0, hsum1, add_sub_cancel_left]
    calc ‖∑ c ∈ S_hi, tensorProd n (sitePhi n hn τ g c)‖
        ≤ ∑ c ∈ S_hi, ‖tensorProd n (sitePhi n hn τ g c)‖ := norm_sum_le _ _
      _ = ∑ c ∈ S_hi, τ ^ (Finset.univ.filter fun j : Fin n => c j ≠ 0).card *
            ‖tensorProd n (sitePhiUnit n hn g c)‖ := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [tensorProd_sitePhi_eq_pow_mul_unit n hn hg hτ0 c, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hτ0 _)]
      _ ≤ ∑ c ∈ S_hi, τ ^ 2 * ‖tensorProd n (sitePhiUnit n hn g c)‖ := by
          refine Finset.sum_le_sum fun c hc => ?_
          have hcard : 2 ≤ (Finset.univ.filter fun j : Fin n => c j ≠ 0).card :=
            (Finset.mem_filter.mp hc).2
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hτ0 hτ1 hcard) (norm_nonneg _)
      _ = C_B * τ ^ 2 := by rw [← Finset.mul_sum, mul_comm]
  -- Combine `diagExpRing τ = 1 - τ • H_onsite + O(τ^2)` and `B_slice τ = 1 - τ • H_bonds + O(τ^2)`
  let H_O := H_onsite n D a
  let H_B := H_bonds n hn g
  let C_V : ℝ := ‖H_O‖ ^ 2 * Real.exp ‖H_O‖
  let C_tot : ℝ := C_V * (1 + ‖H_B‖ + C_B) + ‖H_O‖ * (‖H_B‖ + C_B) + C_B
  have hCtot_nn : 0 ≤ C_tot := by positivity
  obtain ⟨M₀, hM₀_gt⟩ := exists_nat_gt (max b 1)
  have hM₀_ge1 : 1 ≤ M₀ := by
    have : (1 : ℝ) < (M₀ : ℝ) := lt_of_le_of_lt (le_max_right b 1) hM₀_gt
    exact_mod_cast this.le
  refine tendsto_trace_pow_of_first_order
    (X := fun M => T_slice n hn D a (b / (M : ℝ)) g)
    (A := (-b) • H_spin1_shifted n hn D a g)
    (C := C_tot * b ^ 2) (by positivity) hM₀_ge1 ?_
  intro M hM
  let τ : ℝ := b / (M : ℝ)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans hM₀_ge1 hM))
  have hτ0 : 0 ≤ τ := div_nonneg hb.le hMpos.le
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    rw [div_le_one hMpos]
    have hbM : b < (M₀ : ℝ) := lt_of_le_of_lt (le_max_left b 1) hM₀_gt
    have hMM : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hA_eq : ((M : ℝ)⁻¹) • ((-b) • H_spin1_shifted n hn D a g) = (-τ) • H_B + (-τ) • H_O := by
    rw [H_spin1_shifted_eq_bonds_add_onsite, smul_add, smul_add, smul_smul, smul_smul]
    have hτeq : (M : ℝ)⁻¹ * -b = -τ := by dsimp [τ]; ring
    rw [hτeq]
  rw [hA_eq, T_slice_eq_mul, diagExpRing_eq_exp]
  let EV := NormedSpace.exp ((-τ) • H_O)
  let rV := EV - 1 - (-τ) • H_O
  let rB := B_slice n hn τ g - (1 + (-τ) • H_B)
  have hrV : ‖rV‖ ≤ C_V * τ ^ 2 := by
    have h1 := PurityBootstrap.LieTrotter.norm_exp_sub_one_sub_le ((-τ) • H_O)
    have hn1 : ‖(-τ) • H_O‖ = τ * ‖H_O‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ0]
    have hexp : Real.exp (τ * ‖H_O‖) ≤ Real.exp ‖H_O‖ :=
      Real.exp_le_exp.mpr (by nlinarith [norm_nonneg H_O])
    calc ‖rV‖ ≤ ‖(-τ) • H_O‖ ^ 2 * Real.exp ‖(-τ) • H_O‖ := h1
      _ = (τ * ‖H_O‖) ^ 2 * Real.exp (τ * ‖H_O‖) := by rw [hn1]
      _ ≤ (τ * ‖H_O‖) ^ 2 * Real.exp ‖H_O‖ := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = C_V * τ ^ 2 := by dsimp [C_V]; ring
  have hrB : ‖rB‖ ≤ C_B * τ ^ 2 := hB_decomp hτ0 hτ1
  have hB_norm : ‖B_slice n hn τ g‖ ≤ 1 + ‖H_B‖ + C_B := by
    have hdecomp : B_slice n hn τ g = (1 + (-τ) • H_B) + rB := by dsimp [rB]; abel
    rw [hdecomp]
    have h1 : ‖(1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ)‖ ≤ 1 := by
      rw [Matrix.linfty_opNorm_def]
      have h : Finset.univ.sup (fun i : Spin1Cfg n => ∑ j : Spin1Cfg n, ‖(1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) i j‖₊) ≤ 1 := by
        refine Finset.sup_le fun i _ => ?_
        have hs : ∑ j : Spin1Cfg n, ‖(1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) i j‖₊ = 1 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Matrix.one_apply, Ne.symm hji]
          · intro hi; exact absurd (Finset.mem_univ i) hi
        exact hs.le
      exact_mod_cast h
    have h2 : ‖(-τ) • H_B‖ ≤ ‖H_B‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ0]
      exact mul_le_of_le_one_left (norm_nonneg _) hτ1
    have h3 : ‖rB‖ ≤ C_B := by
      have hsq : τ ^ 2 ≤ 1 := by nlinarith
      exact hrB.trans (mul_le_of_le_one_right hCB_nn hsq)
    calc ‖1 + (-τ) • H_B + rB‖ ≤ ‖1 + (-τ) • H_B‖ + ‖rB‖ := norm_add_le _ _
      _ ≤ (‖(1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ)‖ + ‖(-τ) • H_B‖) + ‖rB‖ := by
          linarith [norm_add_le (1 : Matrix (Spin1Cfg n) (Spin1Cfg n) ℝ) ((-τ) • H_B)]
      _ ≤ 1 + ‖H_B‖ + C_B := by linarith
  have hdiff : EV * B_slice n hn τ g - (1 + ((-τ) • H_B + (-τ) • H_O)) =
      rV * B_slice n hn τ g + ((-τ) • H_O) * ((-τ) • H_B + rB) + rB := by
    have hEV : EV = 1 + (-τ) • H_O + rV := by dsimp [rV]; abel
    have hB : B_slice n hn τ g = 1 + (-τ) • H_B + rB := by dsimp [rB]; abel
    calc EV * B_slice n hn τ g - (1 + ((-τ) • H_B + (-τ) • H_O))
        = (1 + (-τ) • H_O + rV) * B_slice n hn τ g - (1 + ((-τ) • H_B + (-τ) • H_O)) := by rw [← hEV]
      _ = rV * B_slice n hn τ g + ((-τ) • H_O) * (B_slice n hn τ g - 1) +
            (B_slice n hn τ g - (1 + (-τ) • H_B)) := by
            simp only [add_mul, mul_sub, one_mul, mul_one]; abel
      _ = rV * B_slice n hn τ g + ((-τ) • H_O) * ((-τ) • H_B + rB) + rB := by
            have hB1 : B_slice n hn τ g - 1 = (-τ) • H_B + rB := by rw [hB]; abel
            rw [hB1]
  rw [hdiff]
  have ht1 : ‖rV * B_slice n hn τ g‖ ≤ C_V * (1 + ‖H_B‖ + C_B) * τ ^ 2 := by
    calc ‖rV * B_slice n hn τ g‖ ≤ ‖rV‖ * ‖B_slice n hn τ g‖ := norm_mul_le _ _
      _ ≤ (C_V * τ ^ 2) * (1 + ‖H_B‖ + C_B) :=
          mul_le_mul hrV hB_norm (norm_nonneg _) (by positivity)
      _ = C_V * (1 + ‖H_B‖ + C_B) * τ ^ 2 := by ring
  have ht2 : ‖((-τ) • H_O) * ((-τ) • H_B + rB)‖ ≤ ‖H_O‖ * (‖H_B‖ + C_B) * τ ^ 2 := by
    have hnO : ‖(-τ) • H_O‖ = τ * ‖H_O‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ0]
    have hnB : ‖(-τ) • H_B + rB‖ ≤ τ * (‖H_B‖ + C_B) := by
      have hsq : C_B * τ ^ 2 ≤ C_B * τ := by
        have : τ ^ 2 ≤ τ := by nlinarith
        exact mul_le_mul_of_nonneg_left this hCB_nn
      calc ‖(-τ) • H_B + rB‖ ≤ ‖(-τ) • H_B‖ + ‖rB‖ := norm_add_le _ _
        _ ≤ τ * ‖H_B‖ + C_B * τ ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ0]
            linarith
        _ ≤ τ * ‖H_B‖ + C_B * τ := by linarith
        _ = τ * (‖H_B‖ + C_B) := by ring
    calc ‖((-τ) • H_O) * ((-τ) • H_B + rB)‖
        ≤ ‖(-τ) • H_O‖ * ‖(-τ) • H_B + rB‖ := norm_mul_le _ _
      _ ≤ (τ * ‖H_O‖) * (τ * (‖H_B‖ + C_B)) := by
          rw [hnO]; exact mul_le_mul_of_nonneg_left hnB (by positivity)
      _ = ‖H_O‖ * (‖H_B‖ + C_B) * τ ^ 2 := by ring
  have hsum_bound : ‖rV * B_slice n hn τ g + ((-τ) • H_O) * ((-τ) • H_B + rB) + rB‖ ≤ C_tot * τ ^ 2 := by
    calc ‖rV * B_slice n hn τ g + ((-τ) • H_O) * ((-τ) • H_B + rB) + rB‖
        ≤ ‖rV * B_slice n hn τ g + ((-τ) • H_O) * ((-τ) • H_B + rB)‖ + ‖rB‖ := norm_add_le _ _
      _ ≤ (‖rV * B_slice n hn τ g‖ + ‖((-τ) • H_O) * ((-τ) • H_B + rB)‖) + ‖rB‖ := by
          linarith [norm_add_le (rV * B_slice n hn τ g) (((-τ) • H_O) * ((-τ) • H_B + rB))]
      _ ≤ C_V * (1 + ‖H_B‖ + C_B) * τ ^ 2 + ‖H_O‖ * (‖H_B‖ + C_B) * τ ^ 2 + C_B * τ ^ 2 := by linarith
      _ = C_tot * τ ^ 2 := by dsimp [C_tot]; ring
  have hdiv : C_tot * τ ^ 2 = C_tot * b ^ 2 / (M : ℝ) ^ 2 := by dsimp [τ]; field_simp [hMpos.ne']
  linarith

end SliceLimit

/-! ## 4. Exact `D_4` (Candidate A) and `D_2` (Source 1) Sector-Moment Existence Theorems -/

set_option maxHeartbeats 600000 in
/-- **Spin-1 `D_4` Signed Sector-Moment Theorem** (for arbitrary anisotropy `D`, shift `a`, and `b > 0`):
constructs 4 real eigenvalue families `lam : Fin 4 → ℕ → ℝ` with absolutely summable `n`-th powers
for all `n ≥ 4` (`Summable (fun i => |lam s i| ^ n)`), whose `n`-th signed power sums reproduce all
four twisted physical partition functions `Z_spin1 n hn D a g b` (`g ∈ {rotI, rotZ, rotX, rotF}`)
for EVERY `n ≥ 4` (even and odd!). -/
theorem spin1_D4_sector_moments (D a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ lam : Fin 4 → ℕ → ℝ,
      (∀ s : Fin 4, ∀ n : ℕ, 4 ≤ n → Summable (fun i => |lam s i| ^ n)) ∧
      (∀ n : ℕ, ∀ hn : 4 ≤ n,
        Z_spin1 n (by omega) D a rotI b =
          (∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n) + 2 * (∑' i, lam 3 i ^ n)) ∧
      (∀ n : ℕ, ∀ hn : 4 ≤ n,
        Z_spin1 n (by omega) D a rotZ b =
          (∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n) - 2 * (∑' i, lam 3 i ^ n)) ∧
      (∀ n : ℕ, ∀ hn : 4 ≤ n,
        Z_spin1 n (by omega) D a rotX b =
          (∑' i, lam 0 i ^ n) - (∑' i, lam 2 i ^ n)) ∧
      (∀ n : ℕ, ∀ hn : 4 ≤ n,
        Z_spin1 n (by omega) D a rotF b =
          (∑' i, lam 0 i ^ n) - 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n)) := by
  -- Work along `M = m + 1 ≥ 1`
  let K : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => K_mat (m + 1) D a b
  let UF : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotF
  let UZ : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotZ
  let UX : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotX
  let UR : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotR
  let UFT : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (UF m)ᵀ
  -- Six real symmetric projections of `D_4`: A1, B1, B2, A2, E+, E-
  let PA1 : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m =>
    ((1 / 8 : ℝ) • (1 + UZ m + UF m + UFT m)) * (1 + UX m)
  let PA2 : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m =>
    ((1 / 8 : ℝ) • (1 + UZ m + UF m + UFT m)) * (1 - UX m)
  let PB1 : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m =>
    ((1 / 8 : ℝ) • (1 + UZ m - UF m - UFT m)) * (1 + UX m)
  let PB2 : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m =>
    ((1 / 8 : ℝ) • (1 + UZ m - UF m - UFT m)) * (1 - UX m)
  let PEp : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m =>
    ((1 / 4 : ℝ) • (1 - UZ m)) * (1 + UX m)
  let PEm : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m =>
    ((1 / 4 : ℝ) • (1 - UZ m)) * (1 - UX m)
  -- Group identities lifted to `U_mat (m + 1)`
  have hF2 : ∀ m, UF m * UF m = UZ m := fun m => by
    dsimp [UF, UZ]; rw [← U_mat_mul, rotF_sq]
  have hZ2 : ∀ m, UZ m * UZ m = 1 := fun m => by
    dsimp [UZ]; rw [← U_mat_mul, rotZ_sq, rotI, U_mat_one]
  have hX2 : ∀ m, UX m * UX m = 1 := fun m => by
    dsimp [UX]; rw [← U_mat_mul, rotX_sq, rotI, U_mat_one]
  have hZT : ∀ m, (UZ m)ᵀ = UZ m := fun m => by
    dsimp [UZ]; rw [U_mat_transpose, rotZ_transpose]
  have hXT : ∀ m, (UX m)ᵀ = UX m := fun m => by
    dsimp [UX]; rw [U_mat_transpose, rotX_transpose]
  have hFFt : ∀ m, UF m * UFT m = 1 := fun m => U_mat_orth_right _ isAxialRot_rotF.orth_right
  have hFtF : ∀ m, UFT m * UF m = 1 := fun m => U_mat_orth_left _ isAxialRot_rotF.orth_left
  have hFZ : ∀ m, UF m * UZ m = UFT m := fun m => by
    dsimp [UF, UZ, UFT]; rw [U_mat_transpose, ← U_mat_mul, rotF_mul_rotZ]
  have hZF : ∀ m, UZ m * UF m = UFT m := fun m => by
    dsimp [UF, UZ, UFT]; rw [U_mat_transpose, ← U_mat_mul, rotZ_mul_rotF]
  have hFtZ : ∀ m, UFT m * UZ m = UF m := fun m => by
    calc UFT m * UZ m = (UF m * UZ m) * UZ m := by rw [hFZ]
      _ = UF m * (UZ m * UZ m) := Matrix.mul_assoc _ _ _
      _ = UF m := by rw [hZ2, Matrix.mul_one]
  have hZFt : ∀ m, UZ m * UFT m = UF m := fun m => by
    calc UZ m * UFT m = UZ m * (UZ m * UF m) := by rw [hZF]
      _ = (UZ m * UZ m) * UF m := (Matrix.mul_assoc _ _ _).symm
      _ = UF m := by rw [hZ2, Matrix.one_mul]
  have hFt2 : ∀ m, UFT m * UFT m = UZ m := fun m => by
    calc UFT m * UFT m = (UF m * UZ m) * (UZ m * UF m) := by rw [hFZ, hZF]
      _ = UF m * (UZ m * UZ m) * UF m := by simp [Matrix.mul_assoc]
      _ = UF m * UF m := by rw [hZ2, Matrix.mul_one]
      _ = UZ m := hF2 m
  have hXZ : ∀ m, UX m * UZ m = UZ m * UX m := fun m => by
    dsimp [UX, UZ]; rw [← U_mat_mul, ← U_mat_mul, rotX_mul_rotZ, rotZ_mul_rotX]
  have hXFX : ∀ m, UX m * UF m * UX m = UFT m := fun m => by
    dsimp [UX, UF, UFT]; rw [U_mat_transpose, ← U_mat_mul, ← U_mat_mul, rotX_mul_rotF_mul_rotX]
  have hXFtX : ∀ m, UX m * UFT m * UX m = UF m := fun m => by
    calc UX m * UFT m * UX m = UX m * (UX m * UF m * UX m) * UX m := by rw [hXFX]
      _ = (UX m * UX m) * UF m * (UX m * UX m) := by simp [Matrix.mul_assoc]
      _ = UF m := by rw [hX2, Matrix.one_mul, Matrix.mul_one]
  have hFX : ∀ m, UF m * UX m = UX m * UFT m := fun m => by
    calc UF m * UX m = (UX m * UX m) * UF m * UX m := by rw [hX2, Matrix.one_mul]
      _ = UX m * (UX m * UF m * UX m) := by simp [Matrix.mul_assoc]
      _ = UX m * UFT m := by rw [hXFX]
  have hFtX : ∀ m, UFT m * UX m = UX m * UF m := fun m => by
    calc UFT m * UX m = (UX m * UX m) * UFT m * UX m := by rw [hX2, Matrix.one_mul]
      _ = UX m * (UX m * UFT m * UX m) := by simp [Matrix.mul_assoc]
      _ = UX m * UF m := by rw [hXFtX]
  have hRF : ∀ m, UR m * UF m = UF m * UR m := fun m => by
    dsimp [UR, UF]; rw [← U_mat_mul, ← U_mat_mul, rotR_mul_rotF]
  have hRZ : ∀ m, UR m * UZ m = UZ m * UR m := fun m => by
    dsimp [UR, UZ]; rw [← U_mat_mul, ← U_mat_mul, rotR_mul_rotZ]
  have hRFt : ∀ m, UR m * UFT m = UFT m * UR m := fun m => by
    calc UR m * UFT m = UR m * (UF m * UZ m) := by rw [hFZ]
      _ = (UR m * UF m) * UZ m := (Matrix.mul_assoc _ _ _).symm
      _ = UF m * (UR m * UZ m) := by rw [hRF, Matrix.mul_assoc]
      _ = UF m * (UZ m * UR m) := by rw [hRZ]
      _ = UFT m * UR m := by rw [← Matrix.mul_assoc, hFZ]
  have hRXRt : ∀ m, UR m * UX m * (UR m)ᵀ = UF m * UX m := fun m => by
    dsimp [UR, UX, UF]; rw [U_mat_transpose, ← U_mat_mul, ← U_mat_mul, rotR_mul_rotX_mul_rotRT, U_mat_mul]
  have hFXFt : ∀ m, UF m * UX m * UFT m = UZ m * UX m := fun m => by
    dsimp [UF, UX, UFT, UZ]; rw [U_mat_transpose, ← U_mat_mul, ← U_mat_mul, rotF_mul_rotX_mul_rotFT, U_mat_mul]
  -- Commutation with `K m`
  have hKF : ∀ m, UF m * K m = K m * UF m := fun m =>
    K_mat_comm_U _ D a b isAxialRot_rotF.toIsSpin1Rot (diagExp3_conj_axial isAxialRot_rotF _ D a)
  have hKZ : ∀ m, UZ m * K m = K m * UZ m := fun m =>
    K_mat_comm_U _ D a b isAxialRot_rotZ.toIsSpin1Rot (diagExp3_conj_axial isAxialRot_rotZ _ D a)
  have hKX : ∀ m, UX m * K m = K m * UX m := fun m =>
    K_mat_comm_U _ D a b isAxialRot_rotX.toIsSpin1Rot (diagExp3_conj_axial isAxialRot_rotX _ D a)
  have hKR : ∀ m, UR m * K m = K m * UR m := fun m =>
    K_mat_comm_U _ D a b isAxialRot_rotR.toIsSpin1Rot (diagExp3_conj_axial isAxialRot_rotR _ D a)
  have hKFt : ∀ m, UFT m * K m = K m * UFT m := fun m => by
    calc UFT m * K m = (UF m * UZ m) * K m := by rw [hFZ]
      _ = UF m * (UZ m * K m) := Matrix.mul_assoc _ _ _
      _ = UF m * (K m * UZ m) := by rw [hKZ]
      _ = (UF m * K m) * UZ m := (Matrix.mul_assoc _ _ _).symm
      _ = (K m * UF m) * UZ m := by rw [hKF]
      _ = K m * UFT m := by rw [Matrix.mul_assoc, hFZ]
  -- Factor the six projections as commuting products of `QFp, QFm, QE` and `Xp, Xm`
  let QFp : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 4 : ℝ) • (1 + UZ m + UF m + UFT m)
  let QFm : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 4 : ℝ) • (1 + UZ m - UF m - UFT m)
  let QE  : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 2 : ℝ) • (1 - UZ m)
  let Xp  : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 2 : ℝ) • (1 + UX m)
  let Xm  : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 2 : ℝ) • (1 - UX m)
  have hPA1_eq : ∀ m, PA1 m = QFp m * Xp m := fun m => by
    dsimp [PA1, QFp, Xp]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hPA2_eq : ∀ m, PA2 m = QFp m * Xm m := fun m => by
    dsimp [PA2, QFp, Xm]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hPB1_eq : ∀ m, PB1 m = QFm m * Xp m := fun m => by
    dsimp [PB1, QFm, Xp]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hPB2_eq : ∀ m, PB2 m = QFm m * Xm m := fun m => by
    dsimp [PB2, QFm, Xm]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hPEp_eq : ∀ m, PEp m = QE m * Xp m := fun m => by
    dsimp [PEp, QE, Xp]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hPEm_eq : ∀ m, PEm m = QE m * Xm m := fun m => by
    dsimp [PEm, QE, Xm]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  have hXp_symm : ∀ m, (Xp m)ᵀ = Xp m := fun m => by
    dsimp [Xp]; simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one, hXT]
  have hXm_symm : ∀ m, (Xm m)ᵀ = Xm m := fun m => by
    dsimp [Xm]; simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, hXT]
  have hQFp_symm : ∀ m, (QFp m)ᵀ = QFp m := fun m => by
    dsimp [QFp]; simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      hZT, Matrix.transpose_transpose]; congr 1; abel
  have hQFm_symm : ∀ m, (QFm m)ᵀ = QFm m := fun m => by
    dsimp [QFm]; simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_sub,
      Matrix.transpose_one, hZT, Matrix.transpose_transpose]; congr 1; abel
  have hQE_symm : ∀ m, (QE m)ᵀ = QE m := fun m => by
    dsimp [QE]; simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, hZT]
  have hXp_idem : ∀ m, Xp m * Xp m = Xp m := fun m => by
    dsimp [Xp]; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hX2]
    ext x y; simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring
  have hXm_idem : ∀ m, Xm m * Xm m = Xm m := fun m => by
    dsimp [Xm]; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hX2]
    ext x y; simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
  have hQFp_idem : ∀ m, QFp m * QFp m = QFp m := fun m => by
    dsimp [QFp]; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      hF2, hZ2, hFFt, hFtF, hFZ, hZF, hFtZ, hZFt, hFt2]
    ext x y; simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring
  have hQFm_idem : ∀ m, QFm m * QFm m = QFm m := fun m => by
    dsimp [QFm]; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hF2, hZ2, hFFt, hFtF, hFZ, hZF, hFtZ, hZFt, hFt2]
    ext x y; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]; ring
  have hQE_idem : ∀ m, QE m * QE m = QE m := fun m => by
    dsimp [QE]; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hZ2]
    ext x y; simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
  have hQFp_X : ∀ m, QFp m * UX m = UX m * QFp m := fun m => by
    dsimp [QFp]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hXZ, hFX, hFtX]; abel
  have hQFm_X : ∀ m, QFm m * UX m = UX m * QFm m := fun m => by
    dsimp [QFm]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hXZ, hFX, hFtX]; abel
  have hQE_X : ∀ m, QE m * UX m = UX m * QE m := fun m => by
    dsimp [QE]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hXZ]
  have hcomm_Xp : ∀ {Q : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ},
      (∀ m, Q m * UX m = UX m * Q m) → ∀ m, Q m * Xp m = Xp m * Q m := fun hQ m => by
    dsimp [Xp]; rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hQ]
  have hcomm_Xm : ∀ {Q : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ},
      (∀ m, Q m * UX m = UX m * Q m) → ∀ m, Q m * Xm m = Xm m * Q m := fun hQ m => by
    dsimp [Xm]; rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hQ]
  have hQFp_K : ∀ m, QFp m * K m = K m * QFp m := fun m => by
    dsimp [QFp]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hKZ, hKF, hKFt]
  have hQFm_K : ∀ m, QFm m * K m = K m * QFm m := fun m => by
    dsimp [QFm]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hKZ, hKF, hKFt]
  have hQE_K : ∀ m, QE m * K m = K m * QE m := fun m => by
    dsimp [QE]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hKZ]
  have hXp_K : ∀ m, Xp m * K m = K m * Xp m := fun m => by
    dsimp [Xp]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hKX]
  have hXm_K : ∀ m, Xm m * K m = K m * Xm m := fun m => by
    dsimp [Xm]; rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hKX]
  -- Symmetry, idempotence, and commutation of the 4 representative projections `P_sec`
  let P_sec : ∀ m, Fin 4 → Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m s =>
    match s.val with
    | 0 => PA1 m
    | 1 => PB1 m
    | 2 => PA2 m
    | _ => PEp m
  have hprod_symm : ∀ {m : ℕ} {A B : Matrix (Word (m + 1)) (Word (m + 1)) ℝ},
      Aᵀ = A → Bᵀ = B → A * B = B * A → (A * B)ᵀ = A * B := by
    intro m A B hA hB hAB
    rw [Matrix.transpose_mul, hB, hA, hAB]
  have hprod_idem : ∀ {m : ℕ} {A B : Matrix (Word (m + 1)) (Word (m + 1)) ℝ},
      A * A = A → B * B = B → A * B = B * A → (A * B) * (A * B) = A * B := by
    intro m A B hA hB hAB
    calc (A * B) * (A * B) = A * (B * A) * B := by simp [Matrix.mul_assoc]
      _ = A * (A * B) * B := by rw [← hAB]
      _ = (A * A) * (B * B) := by simp [Matrix.mul_assoc]
      _ = A * B := by rw [hA, hB]
  have hprod_comm : ∀ {m : ℕ} {A B C : Matrix (Word (m + 1)) (Word (m + 1)) ℝ},
      A * C = C * A → B * C = C * B → (A * B) * C = C * (A * B) := by
    intro m A B C hAC hBC
    calc (A * B) * C = A * (B * C) := Matrix.mul_assoc _ _ _
      _ = A * (C * B) := by rw [hBC]
      _ = (A * C) * B := (Matrix.mul_assoc _ _ _).symm
      _ = (C * A) * B := by rw [hAC]
      _ = C * (A * B) := Matrix.mul_assoc _ _ _
  have hP_symm : ∀ m s, (P_sec m s)ᵀ = P_sec m s := by
    intro m s; fin_cases s
    · change (PA1 m)ᵀ = PA1 m; rw [hPA1_eq]; exact hprod_symm (hQFp_symm m) (hXp_symm m) (hcomm_Xp hQFp_X m)
    · change (PB1 m)ᵀ = PB1 m; rw [hPB1_eq]; exact hprod_symm (hQFm_symm m) (hXp_symm m) (hcomm_Xp hQFm_X m)
    · change (PA2 m)ᵀ = PA2 m; rw [hPA2_eq]; exact hprod_symm (hQFp_symm m) (hXm_symm m) (hcomm_Xm hQFp_X m)
    · change (PEp m)ᵀ = PEp m; rw [hPEp_eq]; exact hprod_symm (hQE_symm m) (hXp_symm m) (hcomm_Xp hQE_X m)
  have hP_idem : ∀ m s, P_sec m s * P_sec m s = P_sec m s := by
    intro m s; fin_cases s
    · change PA1 m * PA1 m = PA1 m; rw [hPA1_eq]; exact hprod_idem (hQFp_idem m) (hXp_idem m) (hcomm_Xp hQFp_X m)
    · change PB1 m * PB1 m = PB1 m; rw [hPB1_eq]; exact hprod_idem (hQFm_idem m) (hXp_idem m) (hcomm_Xp hQFm_X m)
    · change PA2 m * PA2 m = PA2 m; rw [hPA2_eq]; exact hprod_idem (hQFp_idem m) (hXm_idem m) (hcomm_Xm hQFp_X m)
    · change PEp m * PEp m = PEp m; rw [hPEp_eq]; exact hprod_idem (hQE_idem m) (hXp_idem m) (hcomm_Xp hQE_X m)
  have hP_comm : ∀ m s, P_sec m s * K m = K m * P_sec m s := by
    intro m s; fin_cases s
    · change PA1 m * K m = K m * PA1 m; rw [hPA1_eq]; exact hprod_comm (hQFp_K m) (hXp_K m)
    · change PB1 m * K m = K m * PB1 m; rw [hPB1_eq]; exact hprod_comm (hQFm_K m) (hXp_K m)
    · change PA2 m * K m = K m * PA2 m; rw [hPA2_eq]; exact hprod_comm (hQFp_K m) (hXm_K m)
    · change PEp m * K m = K m * PEp m; rw [hPEp_eq]; exact hprod_comm (hQE_K m) (hXp_K m)
  -- Eigenvalue identities `QFm * UF = -QFm` and `QE * UZ = -QE`
  have hQFm_F : ∀ m, QFm m * UF m = -QFm m := fun m => by
    dsimp [QFm]; rw [Matrix.smul_mul, ← smul_neg]; congr 1
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hF2, hZF, hFtF]; abel
  have hQE_Z : ∀ m, QE m * UZ m = -QE m := fun m => by
    dsimp [QE]; rw [Matrix.smul_mul, ← smul_neg]; congr 1
    simp only [Matrix.sub_mul, Matrix.one_mul, hZ2]; abel
  -- Pairing identities: `UR` conjugates `PB1 ↦ PB2`, `UF` conjugates `PEp ↦ PEm`
  have hR_pair : ∀ m, UR m * PB1 m * (UR m)ᵀ = PB2 m := fun m => by
    have hRorth := U_mat_orth_right (m + 1) isAxialRot_rotR.orth_right
    have hRcomm : UR m * QFm m = QFm m * UR m := by
      dsimp [QFm]; rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, Matrix.one_mul, hRZ, hRF, hRFt]
    rw [hPB1_eq, hPB2_eq]
    calc UR m * (QFm m * Xp m) * (UR m)ᵀ
        = QFm m * (UR m * Xp m * (UR m)ᵀ) := by rw [← Matrix.mul_assoc, hRcomm]; simp [Matrix.mul_assoc]
      _ = QFm m * ((1 / 2 : ℝ) • (1 + UF m * UX m)) := by
            congr 1; dsimp [Xp]; rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRorth, hRXRt]
      _ = QFm m * Xm m := by
            dsimp [Xm]; rw [Matrix.mul_smul, Matrix.mul_smul]; congr 1
            rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQFm_F, Matrix.neg_mul]
            abel
  have hF_pair : ∀ m, UF m * PEp m * UFT m = PEm m := fun m => by
    have hFcomm : UF m * QE m = QE m * UF m := by
      dsimp [QE]; rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hFZ, hZF]
    rw [hPEp_eq, hPEm_eq]
    calc UF m * (QE m * Xp m) * UFT m
        = QE m * (UF m * Xp m * UFT m) := by rw [← Matrix.mul_assoc, hFcomm]; simp [Matrix.mul_assoc]
      _ = QE m * ((1 / 2 : ℝ) • (1 + UZ m * UX m)) := by
            congr 1; dsimp [Xp]; rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hFFt, hFXFt]
      _ = QE m * Xm m := by
            dsimp [Xm]; rw [Matrix.mul_smul, Matrix.mul_smul]; congr 1
            rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQE_Z, Matrix.neg_mul]
            abel
  -- Trace vanishing on `E` for `UF`: `Tr((1 - UZ) * K^n * UF) = 0`
  have hE_F_zero : ∀ m n, Matrix.trace (((1 - UZ m) * UF m) * (K m) ^ n) = 0 := fun m n => by
    have hconj : UX m * (((1 - UZ m) * UF m) * (K m) ^ n) * UX m =
        -(((1 - UZ m) * UF m) * (K m) ^ n) := by
      have hXKn : UX m * (K m) ^ n = (K m) ^ n * UX m := (Commute.pow_right (hKX m) n).eq
      have h1Z : (1 - UZ m) * UFT m = -((1 - UZ m) * UF m) := by
        rw [← hZF, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, hZ2, Matrix.one_mul,
          Matrix.sub_mul, Matrix.one_mul]; abel
      calc UX m * (((1 - UZ m) * UF m) * (K m) ^ n) * UX m
          = UX m * ((1 - UZ m) * UF m) * ((K m) ^ n * UX m) := by simp [Matrix.mul_assoc]
        _ = UX m * ((1 - UZ m) * UF m) * (UX m * (K m) ^ n) := by rw [← hXKn]
        _ = ((1 - UZ m) * (UX m * UF m * UX m)) * (K m) ^ n := by
              have h1 : UX m * (1 - UZ m) = (1 - UZ m) * UX m := by
                simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hXZ]
              calc UX m * ((1 - UZ m) * UF m) * (UX m * (K m) ^ n)
                  = ((UX m * (1 - UZ m)) * UF m * UX m) * (K m) ^ n := by simp [Matrix.mul_assoc]
                _ = (((1 - UZ m) * UX m) * UF m * UX m) * (K m) ^ n := by rw [h1]
                _ = ((1 - UZ m) * (UX m * UF m * UX m)) * (K m) ^ n := by simp [Matrix.mul_assoc]
        _ = ((1 - UZ m) * UFT m) * (K m) ^ n := by rw [hXFX]
        _ = (-((1 - UZ m) * UF m)) * (K m) ^ n := by rw [h1Z]
        _ = -(((1 - UZ m) * UF m) * (K m) ^ n) := Matrix.neg_mul _ _
    have htr : Matrix.trace (((1 - UZ m) * UF m) * (K m) ^ n) =
        -Matrix.trace (((1 - UZ m) * UF m) * (K m) ^ n) := by
      have hcyc : Matrix.trace ((UX m * (((1 - UZ m) * UF m) * (K m) ^ n)) * UX m) =
          Matrix.trace (((1 - UZ m) * UF m) * (K m) ^ n) := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hX2, Matrix.one_mul]
      calc Matrix.trace (((1 - UZ m) * UF m) * (K m) ^ n)
          = Matrix.trace ((UX m * (((1 - UZ m) * UF m) * (K m) ^ n)) * UX m) := hcyc.symm
        _ = Matrix.trace (-(((1 - UZ m) * UF m) * (K m) ^ n)) := by rw [hconj]
        _ = -Matrix.trace (((1 - UZ m) * UF m) * (K m) ^ n) := Matrix.trace_neg _
    linarith
  -- Four exact finite-`M` trace decompositions (all `n ≥ 1`)
  let K_sec : ∀ m, Fin 4 → Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m s =>
    P_sec m s * K m * P_sec m s
  have hKsec_herm : ∀ m s, (K_sec m s).IsHermitian := fun m s =>
    proj_mul_isHermitian (K_mat_transpose _ D a b) (hP_symm m s)
  let eigs : ∀ m, Fin 4 → Word (m + 1) → ℝ := fun m s => (hKsec_herm m s).eigenvalues
  have heigs_pow : ∀ m s n, 1 ≤ n →
      ∑ i : Word (m + 1), (eigs m s i) ^ n = Matrix.trace (P_sec m s * (K m) ^ n) := fun m s n hn => by
    rw [← trace_pow_eq_sum_eigenvalues (K_sec m s) (hKsec_herm m s) n,
      proj_mul_pow (hP_idem m s) (hP_comm m s) n hn]
  have htr_B : ∀ m n, Matrix.trace (PB2 m * (K m) ^ n) = Matrix.trace (PB1 m * (K m) ^ n) := fun m n =>
    trace_proj_conj_eq (U_mat_orth_left _ isAxialRot_rotR.orth_left) (hKR m) (hR_pair m) n
  have htr_E : ∀ m n, Matrix.trace (PEm m * (K m) ^ n) = Matrix.trace (PEp m * (K m) ^ n) := fun m n =>
    trace_proj_conj_eq (hFtF m) (hKF m) (hF_pair m) n
  have hXpXm_add : ∀ m, Xp m + Xm m = 1 := fun m => by
    dsimp [Xp, Xm]; ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hXpXm_sub : ∀ m, Xp m - Xm m = UX m := fun m => by
    dsimp [Xp, Xm]; ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hQ_add : ∀ m, QFp m + QFm m + QE m = 1 := fun m => by
    dsimp [QFp, QFm, QE]; ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hQ_subE : ∀ m, QFp m + QFm m - QE m = UZ m := fun m => by
    dsimp [QFp, QFm, QE]; ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hQ_subF : ∀ m, QFp m - QFm m = (1 / 2 : ℝ) • (UF m + UFT m) := fun m => by
    dsimp [QFp, QFm]; ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hdec_I : ∀ m n, 1 ≤ n →
      Matrix.trace ((K m) ^ n * U_mat (m + 1) rotI) =
        (∑ i, eigs m 0 i ^ n) + 2 * (∑ i, eigs m 1 i ^ n) + (∑ i, eigs m 2 i ^ n) + 2 * (∑ i, eigs m 3 i ^ n) := by
    intro m n hn
    rw [rotI, U_mat_one, Matrix.mul_one, heigs_pow m 0 n hn, heigs_pow m 1 n hn,
      heigs_pow m 2 n hn, heigs_pow m 3 n hn]
    change Matrix.trace ((K m) ^ n) =
      Matrix.trace (PA1 m * (K m) ^ n) + 2 * Matrix.trace (PB1 m * (K m) ^ n) +
      Matrix.trace (PA2 m * (K m) ^ n) + 2 * Matrix.trace (PEp m * (K m) ^ n)
    have hsumP : PA1 m + PB1 m + PB2 m + PA2 m + PEp m + PEm m = 1 := by
      rw [hPA1_eq, hPB1_eq, hPB2_eq, hPA2_eq, hPEp_eq, hPEm_eq]
      calc QFp m * Xp m + QFm m * Xp m + QFm m * Xm m + QFp m * Xm m + QE m * Xp m + QE m * Xm m
          = (QFp m + QFm m + QE m) * (Xp m + Xm m) := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
        _ = 1 := by rw [hQ_add, hXpXm_add, Matrix.one_mul]
    have h1 : Matrix.trace ((K m) ^ n) =
        Matrix.trace ((PA1 m + PB1 m + PB2 m + PA2 m + PEp m + PEm m) * (K m) ^ n) := by
      rw [hsumP, Matrix.one_mul]
    rw [h1]
    simp only [Matrix.add_mul, Matrix.trace_add]
    linarith [htr_B m n, htr_E m n]
  have hdec_Z : ∀ m n, 1 ≤ n →
      Matrix.trace ((K m) ^ n * U_mat (m + 1) rotZ) =
        (∑ i, eigs m 0 i ^ n) + 2 * (∑ i, eigs m 1 i ^ n) + (∑ i, eigs m 2 i ^ n) - 2 * (∑ i, eigs m 3 i ^ n) := by
    intro m n hn
    rw [heigs_pow m 0 n hn, heigs_pow m 1 n hn, heigs_pow m 2 n hn, heigs_pow m 3 n hn]
    change Matrix.trace ((K m) ^ n * UZ m) =
      Matrix.trace (PA1 m * (K m) ^ n) + 2 * Matrix.trace (PB1 m * (K m) ^ n) +
      Matrix.trace (PA2 m * (K m) ^ n) - 2 * Matrix.trace (PEp m * (K m) ^ n)
    have hsumZ : PA1 m + PB1 m + PB2 m + PA2 m - PEp m - PEm m = UZ m := by
      rw [hPA1_eq, hPB1_eq, hPB2_eq, hPA2_eq, hPEp_eq, hPEm_eq]
      calc QFp m * Xp m + QFm m * Xp m + QFm m * Xm m + QFp m * Xm m - QE m * Xp m - QE m * Xm m
          = (QFp m + QFm m - QE m) * (Xp m + Xm m) := by
              simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add]; abel
        _ = UZ m := by rw [hQ_subE, hXpXm_add, Matrix.mul_one]
    rw [Matrix.trace_mul_comm, ← hsumZ]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub]
    linarith [htr_B m n, htr_E m n]
  have hdec_X : ∀ m n, 1 ≤ n →
      Matrix.trace ((K m) ^ n * U_mat (m + 1) rotX) =
        (∑ i, eigs m 0 i ^ n) - (∑ i, eigs m 2 i ^ n) := by
    intro m n hn
    rw [heigs_pow m 0 n hn, heigs_pow m 2 n hn]
    change Matrix.trace ((K m) ^ n * UX m) =
      Matrix.trace (PA1 m * (K m) ^ n) - Matrix.trace (PA2 m * (K m) ^ n)
    have hsumX : PA1 m + PB1 m + PEp m - PA2 m - PB2 m - PEm m = UX m := by
      rw [hPA1_eq, hPB1_eq, hPB2_eq, hPA2_eq, hPEp_eq, hPEm_eq]
      calc QFp m * Xp m + QFm m * Xp m + QE m * Xp m - QFp m * Xm m - QFm m * Xm m - QE m * Xm m
          = (QFp m + QFm m + QE m) * (Xp m - Xm m) := by
              simp only [Matrix.add_mul, Matrix.mul_sub]; abel
        _ = UX m := by rw [hQ_add, hXpXm_sub, Matrix.one_mul]
    rw [Matrix.trace_mul_comm, ← hsumX]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub]
    linarith [htr_B m n, htr_E m n]
  have hdec_F : ∀ m n, 1 ≤ n →
      Matrix.trace ((K m) ^ n * U_mat (m + 1) rotF) =
        (∑ i, eigs m 0 i ^ n) - 2 * (∑ i, eigs m 1 i ^ n) + (∑ i, eigs m 2 i ^ n) := by
    intro m n hn
    rw [heigs_pow m 0 n hn, heigs_pow m 1 n hn, heigs_pow m 2 n hn]
    change Matrix.trace ((K m) ^ n * UF m) =
      Matrix.trace (PA1 m * (K m) ^ n) - 2 * Matrix.trace (PB1 m * (K m) ^ n) +
      Matrix.trace (PA2 m * (K m) ^ n)
    have hsumF : (PA1 m + PA2 m - PB1 m - PB2 m) + (1 / 2 : ℝ) • ((1 - UZ m) * UF m) =
        (1 / 2 : ℝ) • (UF m + UFT m) + (1 / 2 : ℝ) • ((1 - UZ m) * UF m) := by
      congr 1
      rw [hPA1_eq, hPA2_eq, hPB1_eq, hPB2_eq]
      calc QFp m * Xp m + QFp m * Xm m - QFm m * Xp m - QFm m * Xm m
          = (QFp m - QFm m) * (Xp m + Xm m) := by simp only [Matrix.sub_mul, Matrix.mul_add]; abel
        _ = (1 / 2 : ℝ) • (UF m + UFT m) := by rw [hQ_subF, hXpXm_add, Matrix.mul_one]
    have htrFt : Matrix.trace (UFT m * (K m) ^ n) = Matrix.trace (UF m * (K m) ^ n) := by
      have hXKn : UX m * (K m) ^ n = (K m) ^ n * UX m := (Commute.pow_right (hKX m) n).eq
      calc Matrix.trace (UFT m * (K m) ^ n)
          = Matrix.trace ((UX m * UF m * UX m) * (K m) ^ n) := by rw [hXFX]
        _ = Matrix.trace ((UX m * UF m) * ((K m) ^ n * UX m)) := by rw [Matrix.mul_assoc, hXKn]
        _ = Matrix.trace (UX m * (UX m * UF m) * (K m) ^ n) := by
              rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
        _ = Matrix.trace (UF m * (K m) ^ n) := by
              rw [← Matrix.mul_assoc, hX2, Matrix.one_mul]
    have hF_split : Matrix.trace ((K m) ^ n * UF m) =
        Matrix.trace ((PA1 m + PA2 m - PB1 m - PB2 m) * (K m) ^ n) := by
      have h1 : Matrix.trace (((1 / 2 : ℝ) • (UF m + UFT m) + (1 / 2 : ℝ) • ((1 - UZ m) * UF m)) * (K m) ^ n) =
          Matrix.trace (UF m * (K m) ^ n) := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, hE_F_zero m n, smul_zero, add_zero,
          Matrix.add_mul, Matrix.trace_add, htrFt, smul_eq_mul]
        ring
      rw [Matrix.trace_mul_comm, ← h1, ← hsumF, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
        Matrix.trace_smul, hE_F_zero m n, smul_zero, add_zero]
    rw [hF_split]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub]
    linarith [htr_B m n]
  -- Apply `l2_seq_compact_moments` with `C = 9 * exp(2 * b * (|D| + |a| + 3))`
  let C : ℝ := 9 * Real.exp (2 * b * (|D| + |a| + 3))
  have hl2 : ∀ m (s : Fin 4), ∑ i : Word (m + 1), (eigs m s i) ^ 2 ≤ C := fun m s => by
    rw [← trace_pow_eq_sum_eigenvalues (K_sec m s) (hKsec_herm m s) 2]
    exact (trace_proj_sq_le (K_mat_transpose _ D a b) (hP_symm m s) (hP_idem m s) (hP_comm m s)).trans
      (K_mat_hilbert_schmidt_le (Nat.succ_pos m) D a hb)
  rcases l2_seq_compact_moments eigs (by positivity) hl2 with ⟨φ, lam, hφ_mono, hlam_summ, hlam_lim⟩
  have hφ_atTop : Tendsto (fun j => φ j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ_mono.tendsto_atTop
  refine ⟨lam, fun s n hn => hlam_summ s n (by omega), ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) D a hb isAxialRot_rotI.toIsSpin1Rot).comp hφ_atTop
    have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotI)) atTop
        (nhds ((∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n) + 2 * (∑' i, lam 3 i ^ n))) := by
      simp_rw [hdec_I _ n (by omega)]
      exact ((((hlam_lim 0 n (by omega)).add ((hlam_lim 1 n (by omega)).const_mul 2)).add
        (hlam_lim 2 n (by omega))).add ((hlam_lim 3 n (by omega)).const_mul 2))
    exact tendsto_nhds_unique hL hR
  · intro n hn
    have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) D a hb isAxialRot_rotZ.toIsSpin1Rot).comp hφ_atTop
    have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotZ)) atTop
        (nhds ((∑' i, lam 0 i ^ n) + 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n) - 2 * (∑' i, lam 3 i ^ n))) := by
      simp_rw [hdec_Z _ n (by omega)]
      exact ((((hlam_lim 0 n (by omega)).add ((hlam_lim 1 n (by omega)).const_mul 2)).add
        (hlam_lim 2 n (by omega))).sub ((hlam_lim 3 n (by omega)).const_mul 2))
    exact tendsto_nhds_unique hL hR
  · intro n hn
    have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) D a hb isAxialRot_rotX.toIsSpin1Rot).comp hφ_atTop
    have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotX)) atTop
        (nhds ((∑' i, lam 0 i ^ n) - (∑' i, lam 2 i ^ n))) := by
      simp_rw [hdec_X _ n (by omega)]
      exact (hlam_lim 0 n (by omega)).sub (hlam_lim 2 n (by omega))
    exact tendsto_nhds_unique hL hR
  · intro n hn
    have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) D a hb isAxialRot_rotF.toIsSpin1Rot).comp hφ_atTop
    have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotF)) atTop
        (nhds ((∑' i, lam 0 i ^ n) - 2 * (∑' i, lam 1 i ^ n) + (∑' i, lam 2 i ^ n))) := by
      simp_rw [hdec_F _ n (by omega)]
      exact ((hlam_lim 0 n (by omega)).sub ((hlam_lim 1 n (by omega)).const_mul 2)).add
        (hlam_lim 2 n (by omega))
    exact tendsto_nhds_unique hL hR

/-- **Isotropic Spin-1 `D_2` Signed Sector-Moment Theorem** (for `D = 0`, arbitrary shift `a`, `b > 0`,
matching OpenAI Source 1): constructs two real eigenvalue families `lamJ, lamN : ℕ → ℝ` with
absolutely summable `n`-th powers for all `n ≥ 4` (`Summable (fun i => |lam i| ^ n)`),
reproducing `Z_spin1 n hn 0 a rotI b = J_n + 3 N_n` and `Z_spin1 n hn 0 a rotX b = J_n - N_n`
for EVERY `n ≥ 4` (even and odd!). -/
theorem spin1_D2_sector_moments (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ (lamJ lamN : ℕ → ℝ),
      (∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamJ i| ^ n)) ∧
      (∀ n : ℕ, 4 ≤ n → Summable (fun i => |lamN i| ^ n)) ∧
      (∀ n : ℕ, ∀ hn : 4 ≤ n,
        Z_spin1 n (by omega) 0 a rotI b = (∑' i, lamJ i ^ n) + 3 * (∑' i, lamN i ^ n)) ∧
      (∀ n : ℕ, ∀ hn : 4 ≤ n,
        Z_spin1 n (by omega) 0 a rotX b = (∑' i, lamJ i ^ n) - (∑' i, lamN i ^ n)) := by
  let K : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => K_mat (m + 1) 0 a b
  let UX : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotX
  let UY : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotY
  let UZ : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotZ
  let UC : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => U_mat (m + 1) rotC
  let PJ : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 4 : ℝ) • (1 + UX m + UY m + UZ m)
  let PNx : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 4 : ℝ) • (1 + UX m - UY m - UZ m)
  let PNy : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 4 : ℝ) • (1 - UX m + UY m - UZ m)
  let PNz : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => (1 / 4 : ℝ) • (1 - UX m - UY m + UZ m)
  have hX2 : ∀ m, UX m * UX m = 1 := fun m => by dsimp [UX]; rw [← U_mat_mul, rotX_sq, rotI, U_mat_one]
  have hY2 : ∀ m, UY m * UY m = 1 := fun m => by dsimp [UY]; rw [← U_mat_mul, rotY_sq, rotI, U_mat_one]
  have hZ2 : ∀ m, UZ m * UZ m = 1 := fun m => by dsimp [UZ]; rw [← U_mat_mul, rotZ_sq, rotI, U_mat_one]
  have hXY : ∀ m, UX m * UY m = UZ m := fun m => by dsimp [UX, UY, UZ]; rw [← U_mat_mul, rotX_mul_rotY]
  have hYX : ∀ m, UY m * UX m = UZ m := fun m => by dsimp [UX, UY, UZ]; rw [← U_mat_mul, rotY_mul_rotX]
  have hXZ : ∀ m, UX m * UZ m = UY m := fun m => by dsimp [UX, UY, UZ]; rw [← U_mat_mul, rotX_mul_rotZ]
  have hZX : ∀ m, UZ m * UX m = UY m := fun m => by dsimp [UX, UY, UZ]; rw [← U_mat_mul, rotZ_mul_rotX]
  have hYZ : ∀ m, UY m * UZ m = UX m := fun m => by
    calc UY m * UZ m = UY m * (UY m * UX m) := by rw [hYX]
      _ = (UY m * UY m) * UX m := (Matrix.mul_assoc _ _ _).symm
      _ = UX m := by rw [hY2, Matrix.one_mul]
  have hZY : ∀ m, UZ m * UY m = UX m := fun m => by
    calc UZ m * UY m = (UX m * UY m) * UY m := by rw [hXY]
      _ = UX m * (UY m * UY m) := Matrix.mul_assoc _ _ _
      _ = UX m := by rw [hY2, Matrix.mul_one]
  have hXT : ∀ m, (UX m)ᵀ = UX m := fun m => by dsimp [UX]; rw [U_mat_transpose, rotX_transpose]
  have hYT : ∀ m, (UY m)ᵀ = UY m := fun m => by dsimp [UY]; rw [U_mat_transpose, rotY_transpose]
  have hZT : ∀ m, (UZ m)ᵀ = UZ m := fun m => by dsimp [UZ]; rw [U_mat_transpose, rotZ_transpose]
  have hKX : ∀ m, UX m * K m = K m * UX m := fun m =>
    K_mat_comm_U _ 0 a b isAxialRot_rotX.toIsSpin1Rot (diagExp3_conj_iso isAxialRot_rotX.toIsSpin1Rot _ a)
  have hKY : ∀ m, UY m * K m = K m * UY m := fun m =>
    K_mat_comm_U _ 0 a b isAxialRot_rotY.toIsSpin1Rot (diagExp3_conj_iso isAxialRot_rotY.toIsSpin1Rot _ a)
  have hKZ : ∀ m, UZ m * K m = K m * UZ m := fun m =>
    K_mat_comm_U _ 0 a b isAxialRot_rotZ.toIsSpin1Rot (diagExp3_conj_iso isAxialRot_rotZ.toIsSpin1Rot _ a)
  have hKC : ∀ m, UC m * K m = K m * UC m := fun m =>
    K_mat_comm_U _ 0 a b isSpin1Rot_rotC (diagExp3_conj_iso isSpin1Rot_rotC _ a)
  have hCX : ∀ m, UC m * UX m * (UC m)ᵀ = UY m := fun m => by
    dsimp [UC, UX, UY]; rw [U_mat_transpose, ← U_mat_mul, ← U_mat_mul, rotC_mul_rotX_mul_rotCT]
  have hCY : ∀ m, UC m * UY m * (UC m)ᵀ = UZ m := fun m => by
    dsimp [UC, UY, UZ]; rw [U_mat_transpose, ← U_mat_mul, ← U_mat_mul, rotC_mul_rotY_mul_rotCT]
  have hCZ : ∀ m, UC m * UZ m * (UC m)ᵀ = UX m := fun m => by
    dsimp [UC, UZ, UX]; rw [U_mat_transpose, ← U_mat_mul, ← U_mat_mul, rotC_mul_rotZ_mul_rotCT]
  have hC_orth_r : ∀ m, UC m * (UC m)ᵀ = 1 := fun m => U_mat_orth_right _ isSpin1Rot_rotC.orth_right
  have hC_orth_l : ∀ m, (UC m)ᵀ * UC m = 1 := fun m => U_mat_orth_left _ isSpin1Rot_rotC.orth_left
  have hC_Nx_Ny : ∀ m, UC m * PNx m * (UC m)ᵀ = PNy m := fun m => by
    dsimp [PNx, PNy]
    simp only [Matrix.mul_smul, Matrix.smul_mul]; congr 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hC_orth_r, hCX, hCY, hCZ]
    abel
  have hC_Ny_Nz : ∀ m, UC m * PNy m * (UC m)ᵀ = PNz m := fun m => by
    dsimp [PNy, PNz]
    simp only [Matrix.mul_smul, Matrix.smul_mul]; congr 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hC_orth_r, hCX, hCY, hCZ]
    abel
  let P_sec : ∀ m, Fin 2 → Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m s =>
    if s.val = 0 then PJ m else PNx m
  have hP_symm : ∀ m s, (P_sec m s)ᵀ = P_sec m s := by
    intro m s; fin_cases s <;>
    · dsimp [P_sec, PJ, PNx]
      simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_sub,
        Matrix.transpose_one, hXT, hYT, hZT]
  have hP_idem : ∀ m s, P_sec m s * P_sec m s = P_sec m s := by
    intro m s; fin_cases s <;>
    · dsimp [P_sec, PJ, PNx]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        hX2, hY2, hZ2, hXY, hYX, hXZ, hZX, hYZ, hZY]
      ext x y
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring
  have hP_comm : ∀ m s, P_sec m s * K m = K m * P_sec m s := by
    intro m s; fin_cases s <;>
    · dsimp [P_sec, PJ, PNx]
      simp only [Matrix.smul_mul, Matrix.mul_smul]; congr 1
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hKX, hKY, hKZ]
  let K_sec : ∀ m, Fin 2 → Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m s =>
    P_sec m s * K m * P_sec m s
  have hKsec_herm : ∀ m s, (K_sec m s).IsHermitian := fun m s =>
    proj_mul_isHermitian (K_mat_transpose _ 0 a b) (hP_symm m s)
  let eigs : ∀ m, Fin 2 → Word (m + 1) → ℝ := fun m s => (hKsec_herm m s).eigenvalues
  have heigs_pow : ∀ m s n, 1 ≤ n →
      ∑ i : Word (m + 1), (eigs m s i) ^ n = Matrix.trace (P_sec m s * (K m) ^ n) := fun m s n hn => by
    rw [← trace_pow_eq_sum_eigenvalues (K_sec m s) (hKsec_herm m s) n,
      proj_mul_pow (hP_idem m s) (hP_comm m s) n hn]
  have htr_Ny : ∀ m n, Matrix.trace (PNy m * (K m) ^ n) = Matrix.trace (PNx m * (K m) ^ n) := fun m n =>
    trace_proj_conj_eq (hC_orth_l m) (hKC m) (hC_Nx_Ny m) n
  have htr_Nz : ∀ m n, Matrix.trace (PNz m * (K m) ^ n) = Matrix.trace (PNy m * (K m) ^ n) := fun m n =>
    trace_proj_conj_eq (hC_orth_l m) (hKC m) (hC_Ny_Nz m) n
  have hdec_I : ∀ m n, 1 ≤ n →
      Matrix.trace ((K m) ^ n * U_mat (m + 1) rotI) =
        (∑ i, eigs m 0 i ^ n) + 3 * (∑ i, eigs m 1 i ^ n) := by
    intro m n hn
    rw [rotI, U_mat_one, Matrix.mul_one, heigs_pow m 0 n hn, heigs_pow m 1 n hn]
    change Matrix.trace ((K m) ^ n) = Matrix.trace (PJ m * (K m) ^ n) + 3 * Matrix.trace (PNx m * (K m) ^ n)
    have hsumP : PJ m + PNx m + PNy m + PNz m = 1 := by
      dsimp [PJ, PNx, PNy, PNz]
      ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [show Matrix.trace ((K m) ^ n) = Matrix.trace ((PJ m + PNx m + PNy m + PNz m) * (K m) ^ n) by
      rw [hsumP, Matrix.one_mul]]
    simp only [Matrix.add_mul, Matrix.trace_add]
    linarith [htr_Ny m n, htr_Nz m n]
  have hdec_X : ∀ m n, 1 ≤ n →
      Matrix.trace ((K m) ^ n * U_mat (m + 1) rotX) =
        (∑ i, eigs m 0 i ^ n) - (∑ i, eigs m 1 i ^ n) := by
    intro m n hn
    rw [heigs_pow m 0 n hn, heigs_pow m 1 n hn]
    change Matrix.trace ((K m) ^ n * UX m) = Matrix.trace (PJ m * (K m) ^ n) - Matrix.trace (PNx m * (K m) ^ n)
    have hsumX : PJ m + PNx m - PNy m - PNz m = UX m := by
      dsimp [PJ, PNx, PNy, PNz]
      ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [Matrix.trace_mul_comm, ← hsumX]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub]
    linarith [htr_Ny m n, htr_Nz m n]
  let C : ℝ := 9 * Real.exp (2 * b * (|(0 : ℝ)| + |a| + 3))
  have hl2 : ∀ m (s : Fin 2), ∑ i : Word (m + 1), (eigs m s i) ^ 2 ≤ C := fun m s => by
    rw [← trace_pow_eq_sum_eigenvalues (K_sec m s) (hKsec_herm m s) 2]
    exact (trace_proj_sq_le (K_mat_transpose _ 0 a b) (hP_symm m s) (hP_idem m s) (hP_comm m s)).trans
      (K_mat_hilbert_schmidt_le (Nat.succ_pos m) 0 a hb)
  rcases l2_seq_compact_moments eigs (by positivity) hl2 with ⟨φ, lam, hφ_mono, hlam_summ, hlam_lim⟩
  have hφ_atTop : Tendsto (fun j => φ j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ_mono.tendsto_atTop
  refine ⟨lam 0, lam 1, fun n hn => hlam_summ 0 n (by omega), fun n hn => hlam_summ 1 n (by omega), ?_, ?_⟩
  · intro n hn
    have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) 0 a hb isAxialRot_rotI.toIsSpin1Rot).comp hφ_atTop
    have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotI)) atTop
        (nhds ((∑' i, lam 0 i ^ n) + 3 * (∑' i, lam 1 i ^ n))) := by
      simp_rw [hdec_I _ n (by omega)]
      exact (hlam_lim 0 n (by omega)).add ((hlam_lim 1 n (by omega)).const_mul 3)
    exact tendsto_nhds_unique hL hR
  · intro n hn
    have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) 0 a hb isAxialRot_rotX.toIsSpin1Rot).comp hφ_atTop
    have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotX)) atTop
        (nhds ((∑' i, lam 0 i ^ n) - (∑' i, lam 1 i ^ n))) := by
      simp_rw [hdec_X _ n (by omega)]
      exact (hlam_lim 0 n (by omega)).sub (hlam_lim 1 n (by omega))
    exact tendsto_nhds_unique hL hR

/-- **Unconditional Single-List Spatial Eigenvalues**: for arbitrary `D, a : ℝ` and `b > 0`,
there exists a real sequence `lam : ℕ → ℝ` with absolutely summable fourth powers
(`Summable (fun i => |lam i| ^ 4)`) whose `n`-th powers reproduce
`Z_spin1 n hn D a rotI b` for every `n ≥ 4` (giving `SpectralSystem1D` directly!). -/
theorem spin1_spatial_eigs (D a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ lam : ℕ → ℝ,
      Summable (fun i => |lam i| ^ (4 : ℕ)) ∧
      ∀ n : ℕ, ∀ hn : 4 ≤ n, Z_spin1 n (by omega) D a rotI b = ∑' i, lam i ^ n := by
  let K : ∀ m, Matrix (Word (m + 1)) (Word (m + 1)) ℝ := fun m => K_mat (m + 1) D a b
  let eigs : ∀ m, Fin 1 → Word (m + 1) → ℝ := fun m _ => (K_mat_isHermitian (m + 1) D a b).eigenvalues
  let C : ℝ := 9 * Real.exp (2 * b * (|D| + |a| + 3))
  have hl2 : ∀ m (s : Fin 1), ∑ i : Word (m + 1), (eigs m s i) ^ 2 ≤ C := fun m _ => by
    rw [← trace_pow_eq_sum_eigenvalues (K m) (K_mat_isHermitian (m + 1) D a b) 2]
    exact K_mat_hilbert_schmidt_le (Nat.succ_pos m) D a hb
  rcases l2_seq_compact_moments eigs (by positivity) hl2 with ⟨φ, lam, hφ_mono, hlam_summ, hlam_lim⟩
  have hφ_atTop : Tendsto (fun j => φ j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ_mono.tendsto_atTop
  refine ⟨lam 0, hlam_summ 0 4 (by omega), fun n hn => ?_⟩
  have hL := (tendsto_trace_K_pow_mul_U (by omega : 3 ≤ n) D a hb isAxialRot_rotI.toIsSpin1Rot).comp hφ_atTop
  have hR : Tendsto (fun j => Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotI)) atTop
      (nhds (∑' i, lam 0 i ^ n)) := by
    have hrew : ∀ j, Matrix.trace ((K (φ j)) ^ n * U_mat (φ j + 1) rotI) =
        ∑ i : Word (φ j + 1), (eigs (φ j) 0 i) ^ n := fun j => by
      rw [rotI, U_mat_one, Matrix.mul_one,
        trace_pow_eq_sum_eigenvalues (K (φ j)) (K_mat_isHermitian (φ j + 1) D a b) n]
    simp_rw [hrew]
    exact hlam_lim 0 n (by omega)
  exact tendsto_nhds_unique hL hR

end PurityBootstrap.Spin1Transfer
