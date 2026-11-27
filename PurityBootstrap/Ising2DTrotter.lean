import PurityBootstrap.LieTrotter
import PurityBootstrap.MatrixTools
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
# 2D Transverse-Field Ising Model on Even Tori: Concrete Hamiltonian and 3D Classical Transfer Limit

Constructs the concrete `2^(lx * ly) × 2^(lx * ly)` real symmetric 2D transverse-field Ising
Hamiltonian on a periodic torus `Fin lx × Fin ly` with independent axial couplings `(Jx, Jy)`:
`H_2d lx ly Jx Jy = - ∑_v X_v - ∑_v (Jx Z_v Z_{v + x̂} + Jy Z_v Z_{v + ŷ})`,
defines its shifted partition function `Z_2d lx ly Jx Jy a b = exp (-b a lx ly) * matZ H_2d b`,
and establishes a single finite-`M` 3D classical Ising sum `Z_M` (with strictly positive history
weights whenever `b > 0` and `M ≥ 1`) admitting:
1. exact temporal Lie–Trotter trace `Z_M = Tr((exp(-τ (H_Z + a N I)) * exp(-τ H_X))^M)` (for `M ≥ 1`)
   and convergence `Z_M → Z_2d` as `M → ∞` via `LieTrotter.tendsto_trotter3`;
2. exact real symmetric `x`-transfer matrix `T_x` with `Z_M = Tr(T_x ^ lx)` (for `lx ≥ 1`, `M ≥ 1`, `b > 0`);
3. exact coordinate-swap symmetry `Z_M lx ly Jx Jy = Z_M ly lx Jy Jx`, yielding the real symmetric
   `y`-transfer matrix `T_y` with `Z_M = Tr(T_y ^ ly)` (for `ly ≥ 1`, `M ≥ 1`, `b > 0`).
-/

namespace PurityBootstrap.Ising2DTrotter

open scoped BigOperators Matrix
open Filter Matrix NormedSpace Topology
open PurityBootstrap.LieTrotter PurityBootstrap.MatrixTools

/-! ## 1. Concrete 2D Torus Configurations and Pauli Operators -/

abbrev Site (lx ly : ℕ) := Fin lx × Fin ly
abbrev Cfg (lx ly : ℕ) := Site lx ly → Bool

/-- Spin sign `±1` of a boolean qubit state (`true ↦ +1`, `false ↦ -1`). -/
def spinSign (b : Bool) : ℝ := if b then 1 else -1

lemma spinSign_sq (b : Bool) : spinSign b * spinSign b = 1 := by
  cases b <;> norm_num [spinSign]

lemma spinSign_not (b : Bool) : spinSign (!b) = -spinSign b := by
  cases b <;> norm_num [spinSign]

/-- Flip bit `v` in a 2D spin configuration `s`. -/
def flipSite {lx ly : ℕ} (s : Cfg lx ly) (v : Site lx ly) : Cfg lx ly :=
  Function.update s v (!s v)

lemma flipSite_self {lx ly : ℕ} (s : Cfg lx ly) (v : Site lx ly) :
    flipSite (flipSite s v) v = s := by
  funext w
  unfold flipSite
  by_cases hw : w = v
  · subst hw; simp
  · simp [hw]

lemma flipSite_comm {lx ly : ℕ} (s : Cfg lx ly) (u v : Site lx ly) :
    flipSite (flipSite s u) v = flipSite (flipSite s v) u := by
  funext w
  unfold flipSite
  by_cases huv : u = v
  · subst huv; rfl
  · by_cases hwu : w = u
    · subst hwu; simp [huv]
    · by_cases hwv : w = v
      · subst hwv; simp [Ne.symm huv]
      · simp [hwu, hwv]

lemma eq_flipSite_iff {lx ly : ℕ} (s t : Cfg lx ly) (v : Site lx ly) :
    t = flipSite s v ↔ s = flipSite t v := by
  constructor <;> intro h <;> subst h <;> exact (flipSite_self _ _).symm

/-- Single-site Pauli `X_v` permutation matrix on `Cfg lx ly`. -/
def opX (lx ly : ℕ) (v : Site lx ly) : Matrix (Cfg lx ly) (Cfg lx ly) ℝ :=
  Matrix.of fun s t => if t = flipSite s v then 1 else 0

lemma opX_transpose (lx ly : ℕ) (v : Site lx ly) : (opX lx ly v)ᵀ = opX lx ly v := by
  ext s t
  simp only [Matrix.transpose_apply, opX, Matrix.of_apply, eq_flipSite_iff]

lemma opX_mul_apply (lx ly : ℕ) (v : Site lx ly) (A : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)
    (s t : Cfg lx ly) :
    (opX lx ly v * A) s t = A (flipSite s v) t := by
  rw [Matrix.mul_apply]
  simp only [opX, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (flipSite s v)]
  simp

lemma mul_opX_apply (lx ly : ℕ) (v : Site lx ly) (A : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)
    (s t : Cfg lx ly) :
    (A * opX lx ly v) s t = A s (flipSite t v) := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_single (flipSite t v) ?_ ?_).trans ?_
  · intro x _ hx
    have hne : t ≠ flipSite x v := fun h => hx ((eq_flipSite_iff x t v).mp h)
    simp [opX, hne]
  · intro h; exact absurd (Finset.mem_univ _) h
  · simp [opX, flipSite_self]

lemma opX_sq (lx ly : ℕ) (v : Site lx ly) : opX lx ly v * opX lx ly v = 1 := by
  ext s t
  rw [opX_mul_apply]
  simp only [opX, Matrix.of_apply, flipSite_self, Matrix.one_apply, eq_comm]

lemma opX_comm (lx ly : ℕ) (u v : Site lx ly) :
    opX lx ly u * opX lx ly v = opX lx ly v * opX lx ly u := by
  ext s t
  rw [opX_mul_apply, opX_mul_apply]
  simp only [opX, Matrix.of_apply, flipSite_comm]

/-- Transverse-field operator `H_X = -∑_v X_v`. -/
def H_X (lx ly : ℕ) : Matrix (Cfg lx ly) (Cfg lx ly) ℝ :=
  -(∑ v : Site lx ly, opX lx ly v)

lemma H_X_isHermitian (lx ly : ℕ) : (H_X lx ly).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold H_X
  rw [Matrix.transpose_neg, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun v _ => opX_transpose lx ly v

/-- Classical Ising bond potential `-∑_v (Jx Z_v Z_{v+x̂} + Jy Z_v Z_{v+ŷ})` (enumerated by site
and positive axis direction, with periodic wrap via `finRotate`). -/
def potZ (lx ly : ℕ) (Jx Jy : ℝ) (s : Cfg lx ly) : ℝ :=
  -(∑ v : Site lx ly,
      (Jx * spinSign (s v) * spinSign (s (finRotate lx v.1, v.2)) +
       Jy * spinSign (s v) * spinSign (s (v.1, finRotate ly v.2))))

/-- Diagonal Ising coupling operator `H_Z = diag(potZ)`. -/
def H_Z (lx ly : ℕ) (Jx Jy : ℝ) : Matrix (Cfg lx ly) (Cfg lx ly) ℝ :=
  Matrix.diagonal (potZ lx ly Jx Jy)

lemma H_Z_isHermitian (lx ly : ℕ) (Jx Jy : ℝ) : (H_Z lx ly Jx Jy).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [H_Z]

/-- **Concrete `2^(lx*ly) × 2^(lx*ly)` 2D transverse-field Ising torus Hamiltonian**:
`H_2d lx ly Jx Jy = -∑_v X_v - ∑_v (Jx Z_v Z_{v+x̂} + Jy Z_v Z_{v+ŷ})`. -/
def H_2d (lx ly : ℕ) (Jx Jy : ℝ) : Matrix (Cfg lx ly) (Cfg lx ly) ℝ :=
  H_X lx ly + H_Z lx ly Jx Jy

lemma H_2d_isHermitian (lx ly : ℕ) (Jx Jy : ℝ) : (H_2d lx ly Jx Jy).IsHermitian :=
  (H_X_isHermitian lx ly).add (H_Z_isHermitian lx ly Jx Jy)

/-- Shifted 2D physical partition function `Z_2d lx ly Jx Jy a b = exp(-b a lx ly) * matZ H_2d b`. -/
noncomputable def Z_2d (lx ly : ℕ) (Jx Jy a b : ℝ) : ℝ :=
  Real.exp (-b * a * (lx * ly : ℝ)) * matZ (H_2d lx ly Jx Jy) (H_2d_isHermitian lx ly Jx Jy) b

lemma Z_2d_eq_sum_exp (lx ly : ℕ) (Jx Jy a b : ℝ) :
    Z_2d lx ly Jx Jy a b =
      ∑ k : Cfg lx ly,
        Real.exp (-b * ((H_2d_isHermitian lx ly Jx Jy).eigenvalues k + a * (lx * ly : ℝ))) := by
  unfold Z_2d matZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

lemma Z_2d_pos (lx ly : ℕ) (Jx Jy a b : ℝ) : 0 < Z_2d lx ly Jx Jy a b :=
  mul_pos (Real.exp_pos _) (matZ_pos _ _ _)

/-! ## 2. Exact Single-Site Transverse-Field Exponential `exp (-τ • H_X)` -/

/-- Exact 1-qubit imaginary-time flip kernel `k_τ(s, s') = cosh τ` if `s = s'` else `sinh τ`. -/
noncomputable def kTime (τ : ℝ) (b₁ b₂ : Bool) : ℝ :=
  if b₁ = b₂ then Real.cosh τ else Real.sinh τ

lemma kTime_symm (τ : ℝ) (b₁ b₂ : Bool) : kTime τ b₁ b₂ = kTime τ b₂ b₁ := by
  unfold kTime; by_cases h : b₁ = b₂ <;> simp [h, eq_comm]

lemma kTime_pos {τ : ℝ} (hτ : 0 < τ) (b₁ b₂ : Bool) : 0 < kTime τ b₁ b₂ := by
  unfold kTime
  split_ifs
  · exact Real.cosh_pos τ
  · rw [Real.sinh_eq]
    have h : Real.exp (-τ) < Real.exp τ := Real.exp_lt_exp.mpr (by linarith)
    linarith

set_option backward.isDefEq.respectTransparency false in
/-- Partial product formula for `exp (τ • ∑_{v ∈ S} opX v)`. -/
lemma exp_sum_opX_apply (lx ly : ℕ) (τ : ℝ) (S : Finset (Site lx ly)) :
    letI := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
    ∀ (u v : Cfg lx ly),
      (NormedSpace.exp (τ • ∑ w ∈ S, opX lx ly w)) u v =
        if ∀ w ∉ S, u w = v w then ∏ w ∈ S, kTime τ (u w) (v w) else 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℚ) (α := ℝ)
  let _ : CompleteSpace (Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := FiniteDimensional.completeSpace ℝ _
  induction S using Finset.induction_on with
  | empty =>
    intro u v
    simp only [Finset.sum_empty, smul_zero, NormedSpace.exp_zero, Matrix.one_apply,
      Finset.notMem_empty, not_false_eq_true, forall_true_left, Finset.prod_empty]
    by_cases h : u = v
    · subst h; simp
    · simp only [h, ↓reduceIte]
      rw [if_neg]
      intro hall; exact h (funext hall)
  | insert w₀ S hw₀ ih =>
    intro u v
    have hcomm : Commute (τ • opX lx ly w₀) (τ • ∑ w ∈ S, opX lx ly w) := by
      refine Commute.smul_left (Commute.smul_right ?_ τ) τ
      show opX lx ly w₀ * (∑ w ∈ S, opX lx ly w) = (∑ w ∈ S, opX lx ly w) * opX lx ly w₀
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => opX_comm lx ly w₀ w
    rw [Finset.sum_insert hw₀, smul_add, NormedSpace.exp_add_of_commute hcomm,
      exp_involutive (opX_sq lx ly w₀) τ, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul, opX_mul_apply, ih u v, ih (flipSite u w₀) v]
    have hEq_outside : ∀ (x : Cfg lx ly), (∀ w ∉ S, x w = v w) ↔
        ((∀ w ∉ insert w₀ S, x w = v w) ∧ x w₀ = v w₀) := fun x => by
      constructor
      · intro h; exact ⟨fun w hw => h w (fun hmem => hw (Finset.mem_insert_of_mem hmem)), h w₀ hw₀⟩
      · rintro ⟨h1, h2⟩ w hw
        by_cases hww : w = w₀
        · subst hww; exact h2
        · exact h1 w (by simp [hww, hw])
    have hflip_out : (∀ w ∉ insert w₀ S, flipSite u w₀ w = v w) ↔ (∀ w ∉ insert w₀ S, u w = v w) := by
      refine forall₂_congr fun w hw => ?_
      have hne : w ≠ w₀ := fun h => hw (h ▸ Finset.mem_insert_self w₀ S)
      simp [flipSite, hne]
    have hflip_in : ∏ w ∈ S, kTime τ (flipSite u w₀ w) (v w) = ∏ w ∈ S, kTime τ (u w) (v w) := by
      refine Finset.prod_congr rfl fun w hw => ?_
      have hne : w ≠ w₀ := fun h => hw₀ (h ▸ hw)
      simp [flipSite, hne]
    simp only [hEq_outside u, hEq_outside (flipSite u w₀), hflip_out, hflip_in]
    by_cases hout : ∀ w ∉ insert w₀ S, u w = v w
    · have hfw : flipSite u w₀ w₀ = (!u w₀) := by simp [flipSite]
      rw [hfw, Finset.prod_insert hw₀, if_pos hout]
      by_cases hbit : u w₀ = v w₀
      · have hne : (!u w₀) ≠ v w₀ := by rw [← hbit]; cases u w₀ <;> decide
        rw [if_pos ⟨hout, hbit⟩, if_neg (fun h => hne h.2)]
        simp only [kTime, hbit, ↓reduceIte, mul_zero, add_zero]
      · have heq : (!u w₀) = v w₀ := by
          cases hu : u w₀ <;> cases hv : v w₀ <;> simp_all
        rw [if_neg (fun h => hbit h.2), if_pos ⟨hout, heq⟩]
        simp only [kTime, hbit, ↓reduceIte, mul_zero, zero_add]
    · rw [if_neg (fun h => hout h.1), if_neg (fun h => hout h.1), if_neg hout]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Full exact entry formula for `exp (-τ • H_X lx ly)`. -/
theorem exp_neg_H_X_apply (lx ly : ℕ) (τ : ℝ) (u v : Cfg lx ly) :
    letI := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
    (NormedSpace.exp ((-τ) • H_X lx ly)) u v = ∏ w : Site lx ly, kTime τ (u w) (v w) := by
  let _ := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
  have hEq : (-τ) • H_X lx ly = τ • ∑ w : Site lx ly, opX lx ly w := by
    unfold H_X; rw [smul_neg, neg_smul, neg_neg]
  rw [hEq, exp_sum_opX_apply lx ly τ Finset.univ u v]
  simp

/-! ## 3. Cyclic Matrix-Power Trace Identity Indexed by `finRotate` -/

/-- Exact path-sum expansion of `(A ^ (k + 1)) u v` with internal indices `p : Fin k → ι`. -/
private lemma pow_succ_entry_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ∀ (k : ℕ) (u v : ι),
    (A ^ (k + 1)) u v =
      ∑ p : Fin k → ι,
        (∏ j : Fin k, A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j)) *
        A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) v := by
  intro k
  induction k with
  | zero =>
    intro u v
    simp [pow_one]
  | succ k ih =>
    intro u v
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih u]
    have hsplit : (∑ w : ι, (∑ p : Fin k → ι,
        (∏ j : Fin k, A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j)) *
        A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) w) * A w v) =
        ∑ p : Fin (k + 1) → ι,
          (∏ j : Fin (k + 1), A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j)) *
          A (p ⟨k, by omega⟩) v := by
      simp_rw [Finset.sum_mul]
      rw [← Fintype.sum_prod_type' (fun w (p : Fin k → ι) =>
        ((∏ j : Fin k, A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j)) *
          A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) w) * A w v)]
      let e : (ι × (Fin k → ι)) ≃ (Fin (k + 1) → ι) :=
        { toFun := fun ⟨w, p⟩ => Fin.snoc (α := fun _ => ι) p w
          invFun := fun q => ⟨q (Fin.last k), Fin.init q⟩
          left_inv := fun ⟨w, p⟩ => by
            ext
            · simp
            · simp
          right_inv := fun q => by
            funext j
            refine Fin.lastCases ?_ ?_ j
            · simp
            · intro i; simp [Fin.init] }
      refine Fintype.sum_equiv e _ _ fun ⟨w, p⟩ => ?_
      dsimp only [e, Equiv.coe_fn_mk]
      rw [Fin.prod_univ_castSucc]
      have hlast : Fin.snoc (α := fun _ => ι) p w ⟨k, by omega⟩ = w := by
        simpa [Fin.last] using Fin.snoc_last (α := fun _ => ι) w p
      have hprev : (if h : (Fin.last k).val = 0 then u
          else Fin.snoc (α := fun _ => ι) p w ⟨(Fin.last k).val - 1, by omega⟩) =
          (if h : k = 0 then u else p ⟨k - 1, by omega⟩) := by
        by_cases hk : k = 0
        · simp [hk]
        · simp only [Fin.val_last, hk, ↓reduceDIte]
          have hlt : k - 1 < k := by omega
          simpa using Fin.snoc_castSucc (α := fun _ => ι) w p ⟨k - 1, hlt⟩
      have hprod : ∏ j : Fin k,
          A (if h : j.castSucc.val = 0 then u
              else Fin.snoc (α := fun _ => ι) p w ⟨j.castSucc.val - 1, by omega⟩)
            (Fin.snoc (α := fun _ => ι) p w j.castSucc) =
          ∏ j : Fin k, A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        have harg2 : Fin.snoc (α := fun _ => ι) p w j.castSucc = p j :=
          Fin.snoc_castSucc (α := fun _ => ι) w p j
        have harg1 : (if h : j.castSucc.val = 0 then u
            else Fin.snoc (α := fun _ => ι) p w ⟨j.castSucc.val - 1, by omega⟩) =
            (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) := by
          by_cases hj : j.val = 0
          · simp [hj]
          · simp only [Fin.val_castSucc, hj, ↓reduceDIte]
            have hlt : j.val - 1 < k := by omega
            simpa using Fin.snoc_castSucc (α := fun _ => ι) w p ⟨j.val - 1, hlt⟩
        exact congrArg₂ A harg1 harg2
      rw [hprod, hprev, Fin.snoc_last, hlast]
    simpa using hsplit

/-- **Cyclic Matrix-Power Trace Identity**:
for any `m ≥ 1`, `Tr(A ^ m) = ∑ β : Fin m → ι, ∏ j : Fin m, A (β j) (β (finRotate m j))`. -/
theorem trace_pow_eq_sum_cycle_rot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Matrix.trace (A ^ m) =
      ∑ β : Fin m → ι, ∏ j : Fin m, A (β j) (β (finRotate m j)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply, pow_succ_entry_eq_sum A k]
  rw [← Fintype.sum_prod_type' (fun u (p : Fin k → ι) =>
    (∏ j : Fin k, A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j)) *
    A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) u)]
  let e : (ι × (Fin k → ι)) ≃ (Fin (k + 1) → ι) :=
    { toFun := fun ⟨u, p⟩ => Fin.cons u p
      invFun := fun β => ⟨β 0, Fin.tail β⟩
      left_inv := fun ⟨u, p⟩ => by
        ext
        · simp
        · simp
      right_inv := fun β => by
        funext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i; simp [Fin.tail] }
  refine Fintype.sum_equiv e _ _ fun ⟨u, p⟩ => ?_
  dsimp only [e, Equiv.coe_fn_mk]
  rw [Fin.prod_univ_castSucc]
  have hlast : A (Fin.cons (α := fun _ => ι) u p (Fin.last k))
      (Fin.cons (α := fun _ => ι) u p (finRotate (k + 1) (Fin.last k))) =
      A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) u := by
    have hrot : finRotate (k + 1) (Fin.last k) = 0 := finRotate_last
    rw [hrot, Fin.cons_zero]
    congr 1
    by_cases hk : k = 0
    · subst hk; simp
    · simp only [hk, ↓reduceDIte]
      have hlast_eq : Fin.last k = Fin.succ ⟨k - 1, by omega⟩ := by
        ext; simp; omega
      rw [hlast_eq, Fin.cons_succ]
  have hinit : ∏ j : Fin k,
      A (Fin.cons (α := fun _ => ι) u p j.castSucc)
        (Fin.cons (α := fun _ => ι) u p (finRotate (k + 1) j.castSucc)) =
      ∏ j : Fin k, A (if h : j.val = 0 then u else p ⟨j.val - 1, by omega⟩) (p j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    have hrot : finRotate (k + 1) j.castSucc = j.succ := by
      rw [finRotate_of_lt (show (j.castSucc : ℕ) < k from j.isLt)]
      ext; simp
    rw [hrot, Fin.cons_succ]
    congr 1
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceDIte]
      have h0 : j.castSucc = (0 : Fin (k + 1)) := by ext; exact hj
      rw [h0, Fin.cons_zero]
    · simp only [hj, ↓reduceDIte]
      have hs : j.castSucc = Fin.succ ⟨j.val - 1, by omega⟩ := by
        ext; simp; omega
      rw [hs, Fin.cons_succ]
  rw [hinit, hlast]

/-! ## 4. Finite-`M` 3D Classical Ising Partition Function: One Temporal Trace and Two Symmetric Spatial Cuts -/

abbrev Hist (lx ly M : ℕ) := Fin lx × Fin ly × Fin M → Bool

/-- Unnormalized 3D classical Ising weight of a spacetime history `s` (strictly positive when `τ > 0`). -/
noncomputable def W_3d (lx ly M : ℕ) (Jx Jy a τ : ℝ) (s : Hist lx ly M) : ℝ :=
  ∏ x : Fin lx, ∏ y : Fin ly, ∏ r : Fin M,
    (Real.exp (-τ * a) *
     Real.exp (τ * Jx * spinSign (s (x, y, r)) * spinSign (s (finRotate lx x, y, r))) *
     Real.exp (τ * Jy * spinSign (s (x, y, r)) * spinSign (s (x, finRotate ly y, r))) *
     kTime τ (s (x, y, r)) (s (x, y, finRotate M r)))

/-- Finite-`M` 3D classical Ising partition function `Z_M`. -/
noncomputable def Z_M (lx ly : ℕ) (Jx Jy a b : ℝ) (M : ℕ) : ℝ :=
  ∑ s : Hist lx ly M, W_3d lx ly M Jx Jy a (b / (M : ℝ)) s

/-- Exact coordinate-swap symmetry: `Z_M lx ly Jx Jy a b M = Z_M ly lx Jy Jx a b M`. -/
theorem Z_M_swap_xy (lx ly : ℕ) (Jx Jy a b : ℝ) (M : ℕ) :
    Z_M lx ly Jx Jy a b M = Z_M ly lx Jy Jx a b M := by
  unfold Z_M W_3d
  let eHist : Hist lx ly M ≃ Hist ly lx M :=
    { toFun := fun s p => s (p.2.1, p.1, p.2.2)
      invFun := fun s p => s (p.2.1, p.1, p.2.2)
      left_inv := fun s => by funext ⟨x, y, r⟩; rfl
      right_inv := fun s => by funext ⟨y, x, r⟩; rfl }
  refine Fintype.sum_equiv eHist _ _ fun s => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun y _ => Finset.prod_congr rfl fun x _ =>
    Finset.prod_congr rfl fun r _ => ?_
  dsimp only [eHist, Equiv.coe_fn_mk]
  ring

/-- Helper: currying `Hist lx ly M ≃ (Fin M → Cfg lx ly)`. -/
private def histEquivTime (lx ly M : ℕ) : Hist lx ly M ≃ (Fin M → Cfg lx ly) where
  toFun s r v := s (v.1, v.2, r)
  invFun β p := β p.2.2 (p.1, p.2.1)
  left_inv s := by funext ⟨x, y, r⟩; rfl
  right_inv β := by funext r ⟨x, y⟩; rfl

/-- Helper: currying `Hist lx ly M ≃ (Fin lx → (Fin ly × Fin M → Bool))`. -/
private def histEquivX (lx ly M : ℕ) : Hist lx ly M ≃ (Fin lx → (Fin ly × Fin M → Bool)) where
  toFun s x yr := s (x, yr.1, yr.2)
  invFun β p := β p.1 (p.2.1, p.2.2)
  left_inv s := by funext ⟨x, y, r⟩; rfl
  right_inv β := by funext x ⟨y, r⟩; rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Cut 1 (Time)**: for `M ≥ 1`, `Z_M` equals the Lie–Trotter trace
`Tr((exp(-τ • (H_Z + a N • 1)) * exp(-τ • H_X)) ^ M)`. -/
theorem Z_M_eq_trace_time (lx ly : ℕ) (Jx Jy a b : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    letI := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
    letI := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
    let τ := b / (M : ℝ)
    Z_M lx ly Jx Jy a b M =
      Matrix.trace
        ((NormedSpace.exp ((-τ) • (H_Z lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ))) *
          NormedSpace.exp ((-τ) • H_X lx ly)) ^ M) := by
  let _ := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℚ) (α := ℝ)
  let _ : CompleteSpace (Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := FiniteDimensional.completeSpace ℝ _
  dsimp only
  set τ := b / (M : ℝ)
  set D_diag : Cfg lx ly → ℝ := fun u =>
    -τ * (potZ lx ly Jx Jy u + a * (lx * ly : ℝ))
  have hD_eq : (-τ) • (H_Z lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) =
      Matrix.diagonal D_diag := by
    ext u v
    simp only [H_Z, Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul, D_diag]
    split_ifs <;> ring
  have hexpD : NormedSpace.exp (Matrix.diagonal D_diag) =
      Matrix.diagonal (fun u => Real.exp (D_diag u)) := by
    rw [Matrix.exp_diagonal]
    ext u v
    simp only [Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      have hpi : ∀ (f : Cfg lx ly → ℝ), NormedSpace.exp f u = Real.exp (f u) := fun f => by
        rw [Real.exp_eq_exp_ℝ]
        have heval := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) f).map
          (Pi.evalAddMonoidHom (fun _ : Cfg lx ly => ℝ) u) (continuous_apply u)
        have hterm : ((Pi.evalAddMonoidHom (fun _ : Cfg lx ly => ℝ) u) ∘
            fun k => NormedSpace.expSeries ℝ (Cfg lx ly → ℝ) k fun _ => f) =
            fun k => NormedSpace.expSeries ℝ ℝ k fun _ => f u := by
          funext k
          change (NormedSpace.expSeries ℝ (Cfg lx ly → ℝ) k fun _ => f) u =
            NormedSpace.expSeries ℝ ℝ k fun _ => f u
          rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq]
          simp
        rw [hterm] at heval
        exact heval.unique (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (f u))
      exact hpi D_diag
    · rfl
  rw [hD_eq, hexpD, trace_pow_eq_sum_cycle_rot _ hM]
  unfold Z_M W_3d
  refine Fintype.sum_equiv (histEquivTime lx ly M) _ _ fun s => ?_
  -- Swap product order: ∏ x, ∏ y, ∏ r = ∏ r, ∏ (x, y)
  have hprod_swap : (∏ x : Fin lx, ∏ y : Fin ly, ∏ r : Fin M,
      (Real.exp (-τ * a) *
       Real.exp (τ * Jx * spinSign (s (x, y, r)) * spinSign (s (finRotate lx x, y, r))) *
       Real.exp (τ * Jy * spinSign (s (x, y, r)) * spinSign (s (x, finRotate ly y, r))) *
       kTime τ (s (x, y, r)) (s (x, y, finRotate M r)))) =
      ∏ r : Fin M, ∏ v : Site lx ly,
        (Real.exp (-τ * a) *
         Real.exp (τ * Jx * spinSign (s (v.1, v.2, r)) * spinSign (s (finRotate lx v.1, v.2, r))) *
         Real.exp (τ * Jy * spinSign (s (v.1, v.2, r)) * spinSign (s (v.1, finRotate ly v.2, r))) *
         kTime τ (s (v.1, v.2, r)) (s (v.1, v.2, finRotate M r))) := by
    have h1 : ∀ x : Fin lx, (∏ y : Fin ly, ∏ r : Fin M,
        (Real.exp (-τ * a) *
         Real.exp (τ * Jx * spinSign (s (x, y, r)) * spinSign (s (finRotate lx x, y, r))) *
         Real.exp (τ * Jy * spinSign (s (x, y, r)) * spinSign (s (x, finRotate ly y, r))) *
         kTime τ (s (x, y, r)) (s (x, y, finRotate M r)))) =
        ∏ r : Fin M, ∏ y : Fin ly,
          (Real.exp (-τ * a) *
           Real.exp (τ * Jx * spinSign (s (x, y, r)) * spinSign (s (finRotate lx x, y, r))) *
           Real.exp (τ * Jy * spinSign (s (x, y, r)) * spinSign (s (x, finRotate ly y, r))) *
           kTime τ (s (x, y, r)) (s (x, y, finRotate M r))) := fun x => Finset.prod_comm
    simp_rw [h1]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Fintype.prod_prod_type]
  rw [hprod_swap]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Matrix.diagonal_mul, exp_neg_H_X_apply lx ly τ]
  have hexp_prod : Real.exp (D_diag (histEquivTime lx ly M s r)) =
      ∏ v : Site lx ly,
        (Real.exp (-τ * a) *
         Real.exp (τ * Jx * spinSign (s (v.1, v.2, r)) * spinSign (s (finRotate lx v.1, v.2, r))) *
         Real.exp (τ * Jy * spinSign (s (v.1, v.2, r)) * spinSign (s (v.1, finRotate ly v.2, r)))) := by
    dsimp [D_diag, potZ, histEquivTime]
    have hsum_eq : -τ * (-(∑ v : Site lx ly,
        (Jx * spinSign (s (v.1, v.2, r)) * spinSign (s (finRotate lx v.1, v.2, r)) +
         Jy * spinSign (s (v.1, v.2, r)) * spinSign (s (v.1, finRotate ly v.2, r)))) +
        a * (lx * ly : ℝ)) =
      ∑ v : Site lx ly,
        ((-τ * a) +
         (τ * Jx * spinSign (s (v.1, v.2, r)) * spinSign (s (finRotate lx v.1, v.2, r))) +
         (τ * Jy * spinSign (s (v.1, v.2, r)) * spinSign (s (v.1, finRotate ly v.2, r)))) := by
      have hcard : (∑ _v : Site lx ly, (-τ * a)) = -τ * (a * (lx * ly : ℝ)) := by
        simp [Fintype.card_prod, Fintype.card_fin]
        ring
      simp only [Finset.sum_add_distrib, hcard]
      rw [mul_add, mul_neg, neg_mul, neg_neg, mul_add, Finset.mul_sum, Finset.mul_sum]
      have h1 : (∑ v : Site lx ly, τ * (Jx * spinSign (s (v.1, v.2, r)) * spinSign (s (finRotate lx v.1, v.2, r)))) =
          ∑ v : Site lx ly, τ * Jx * spinSign (s (v.1, v.2, r)) * spinSign (s (finRotate lx v.1, v.2, r)) :=
        Finset.sum_congr rfl fun v _ => by ring
      have h2 : (∑ v : Site lx ly, τ * (Jy * spinSign (s (v.1, v.2, r)) * spinSign (s (v.1, finRotate ly v.2, r)))) =
          ∑ v : Site lx ly, τ * Jy * spinSign (s (v.1, v.2, r)) * spinSign (s (v.1, finRotate ly v.2, r)) :=
        Finset.sum_congr rfl fun v _ => by ring
      linarith
    rw [hsum_eq, Real.exp_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Real.exp_add, Real.exp_add]
  rw [hexp_prod, ← Finset.prod_mul_distrib]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Trotter Limit**: `Z_M lx ly Jx Jy a b M → Z_2d lx ly Jx Jy a b` as `M → ∞`. -/
theorem tendsto_Z_M (lx ly : ℕ) (Jx Jy a b : ℝ) :
    Tendsto (Z_M lx ly Jx Jy a b) atTop (nhds (Z_2d lx ly Jx Jy a b)) := by
  let _ := Matrix.linftyOpNormedRing (n := Cfg lx ly) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℝ) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Cfg lx ly) (R := ℚ) (α := ℝ)
  let _ : CompleteSpace (Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := FiniteDimensional.completeSpace ℝ _
  let A : Matrix (Cfg lx ly) (Cfg lx ly) ℝ :=
    (-b) • (H_Z lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ))
  let B : Matrix (Cfg lx ly) (Cfg lx ly) ℝ := (-b) • H_X lx ly
  have hlim := tendsto_trotter3 A B 0
  have htr_cont : Continuous (Matrix.trace : Matrix (Cfg lx ly) (Cfg lx ly) ℝ → ℝ) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.traceLinearMap (Cfg lx ly) ℝ ℝ)
  have htr_lim : Tendsto (fun M : ℕ => Matrix.trace
      ((NormedSpace.exp (((M : ℝ)⁻¹) • A) * NormedSpace.exp (((M : ℝ)⁻¹) • B) *
        NormedSpace.exp (((M : ℝ)⁻¹) • (0 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ))) ^ M))
      atTop (nhds (Matrix.trace (NormedSpace.exp (A + B + 0)))) :=
    (htr_cont.tendsto _).comp hlim
  have hlim_val : Matrix.trace (NormedSpace.exp (A + B + 0)) = Z_2d lx ly Jx Jy a b := by
    have hsum : A + B + 0 =
        (-b) • H_2d lx ly Jx Jy + (-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := by
      ext u v
      simp only [A, B, H_2d, Matrix.add_apply, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hcomm : Commute ((-b) • H_2d lx ly Jx Jy)
        ((-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) :=
      Commute.smul_left (Commute.smul_right (Commute.one_right _) _) _
    rw [hsum, NormedSpace.exp_add_of_commute hcomm]
    have hexp1 : NormedSpace.exp ((-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) =
        Real.exp (-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ) := by
      have hdiag : ((-b * a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) =
          Matrix.diagonal (fun _ : Cfg lx ly => -b * a * (lx * ly : ℝ)) := by
        ext u v; simp [Matrix.diagonal_apply, Matrix.one_apply]
      rw [hdiag, Matrix.exp_diagonal]
      ext u v; simp [Matrix.diagonal_apply, Matrix.one_apply, Real.exp_eq_exp_ℝ]
    rw [hexp1, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
      trace_exp_eq_matZ (H_2d lx ly Jx Jy) (H_2d_isHermitian lx ly Jx Jy) b]
    rfl
  rw [hlim_val] at htr_lim
  refine htr_lim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  rw [Z_M_eq_trace_time lx ly Jx Jy a b hM]
  have h0 : NormedSpace.exp (((M : ℝ)⁻¹) • (0 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) = 1 := by
    simp
  rw [h0, Matrix.mul_one]
  have hA : ((M : ℝ)⁻¹) • A =
      (-(b / (M : ℝ))) • (H_Z lx ly Jx Jy + (a * (lx * ly : ℝ)) • (1 : Matrix (Cfg lx ly) (Cfg lx ly) ℝ)) := by
    dsimp [A]; rw [smul_smul]; congr 1; ring
  have hB : ((M : ℝ)⁻¹) • B = (-(b / (M : ℝ))) • H_X lx ly := by
    dsimp [B]; rw [smul_smul]; congr 1; ring
  rw [hA, hB]

/-! ## 5. Exact Real Symmetric Spatial Transfer Matrices `T_x` and `T_y` -/

abbrev ColCfg (ly M : ℕ) := Fin ly × Fin M → Bool

/-- Intra-column weight `U_x(u)` of an `x`-column `u : Fin ly × Fin M → Bool`. -/
noncomputable def U_x (ly M : ℕ) (Jy a τ : ℝ) (u : ColCfg ly M) : ℝ :=
  ∏ y : Fin ly, ∏ r : Fin M,
    (Real.exp (-τ * a) *
     Real.exp (τ * Jy * spinSign (u (y, r)) * spinSign (u (finRotate ly y, r))) *
     kTime τ (u (y, r)) (u (y, finRotate M r)))

lemma U_x_nonneg (ly M : ℕ) (Jy a : ℝ) {τ : ℝ} (hτ : 0 < τ) (u : ColCfg ly M) :
    0 ≤ U_x ly M Jy a τ u :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (kTime_pos hτ _ _).le

/-- Inter-column coupling `C_x(u, v) = ∏_{y, r} exp(τ Jx u_{y,r} v_{y,r})`. -/
noncomputable def C_x (ly M : ℕ) (Jx τ : ℝ) (u v : ColCfg ly M) : ℝ :=
  ∏ y : Fin ly, ∏ r : Fin M,
    Real.exp (τ * Jx * spinSign (u (y, r)) * spinSign (v (y, r)))

lemma C_x_symm (ly M : ℕ) (Jx τ : ℝ) (u v : ColCfg ly M) :
    C_x ly M Jx τ u v = C_x ly M Jx τ v u := by
  unfold C_x
  refine Finset.prod_congr rfl fun y _ => Finset.prod_congr rfl fun r _ => ?_
  congr 1; ring

/-- Real symmetric `x`-direction transfer matrix `T_x(u, v) = √U_x(u) * C_x(u, v) * √U_x(v)`. -/
noncomputable def T_x (ly M : ℕ) (Jx Jy a τ : ℝ) : Matrix (ColCfg ly M) (ColCfg ly M) ℝ :=
  Matrix.of fun u v =>
    Real.sqrt (U_x ly M Jy a τ u) * C_x ly M Jx τ u v * Real.sqrt (U_x ly M Jy a τ v)

lemma T_x_transpose (ly M : ℕ) (Jx Jy a τ : ℝ) :
    (T_x ly M Jx Jy a τ)ᵀ = T_x ly M Jx Jy a τ := by
  ext u v
  simp only [Matrix.transpose_apply, T_x, Matrix.of_apply, C_x_symm ly M Jx τ v u]
  ring

/-- **Cut 2 (Space `x`)**: for `lx ≥ 1`, `M ≥ 1`, `b > 0`, `Z_M = Tr(T_x ^ lx)`. -/
theorem Z_M_eq_trace_Tx (lx ly : ℕ) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hlx : 1 ≤ lx) (hM : 1 ≤ M) :
    Z_M lx ly Jx Jy a b M = Matrix.trace ((T_x ly M Jx Jy a (b / (M : ℝ))) ^ lx) := by
  set τ := b / (M : ℝ)
  have hτ : 0 < τ := div_pos hb (Nat.cast_pos.mpr hM)
  rw [trace_pow_eq_sum_cycle_rot _ hlx]
  unfold Z_M W_3d
  refine Fintype.sum_equiv (histEquivX lx ly M) _ _ fun s => ?_
  let β : Fin lx → ColCfg ly M := histEquivX lx ly M s
  have hRHS : (∏ x : Fin lx, T_x ly M Jx Jy a τ (β x) (β (finRotate lx x))) =
      (∏ x : Fin lx, Real.sqrt (U_x ly M Jy a τ (β x))) *
      (∏ x : Fin lx, C_x ly M Jx τ (β x) (β (finRotate lx x))) *
      (∏ x : Fin lx, Real.sqrt (U_x ly M Jy a τ (β (finRotate lx x)))) := by
    simp only [T_x, Matrix.of_apply, Finset.prod_mul_distrib]
  have hrot_prod : (∏ x : Fin lx, Real.sqrt (U_x ly M Jy a τ (β (finRotate lx x)))) =
      ∏ x : Fin lx, Real.sqrt (U_x ly M Jy a τ (β x)) :=
    Fintype.prod_equiv (finRotate lx) _ _ fun _ => rfl
  rw [hRHS, hrot_prod, mul_right_comm, ← Finset.prod_mul_distrib]
  have hsq : ∀ x : Fin lx,
      Real.sqrt (U_x ly M Jy a τ (β x)) * Real.sqrt (U_x ly M Jy a τ (β x)) =
        U_x ly M Jy a τ (β x) := fun x => Real.mul_self_sqrt (U_x_nonneg ly M Jy a hτ (β x))
  simp_rw [hsq]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  dsimp [U_x, C_x, β, histEquivX]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  ring

/-- **Cut 3 (Space `y`)**: for `ly ≥ 1`, `M ≥ 1`, `b > 0`, `Z_M = Tr(T_y ^ ly)` where
`T_y = T_x lx M Jy Jx a (b / M)` is real symmetric. -/
theorem Z_M_eq_trace_Ty (lx ly : ℕ) (Jx Jy a : ℝ) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hly : 1 ≤ ly) (hM : 1 ≤ M) :
    Z_M lx ly Jx Jy a b M = Matrix.trace ((T_x lx M Jy Jx a (b / (M : ℝ))) ^ ly) := by
  rw [Z_M_swap_xy]
  exact Z_M_eq_trace_Tx ly lx Jy Jx a hb hly hM

end PurityBootstrap.Ising2DTrotter
