import PurityBootstrap.LieTrotter
import PurityBootstrap.IsingHamiltonian
import PurityBootstrap.IsingMPS
import PurityBootstrap.CandidateE.RectangleTheorem
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# Unconditional Checkerboard Trotter Instantiation & Candidate E Rectangle Theorem

Proves **unconditionally** (zero transfer hypotheses, zero infinite-dimensional operators,
zero `sorry`, zero `native_decide`, strictly standard axioms) that the interacting transverse-field
Ising chain `H_ising L g h` (`g ≥ 0, h ≥ 0`) instantiates `TrotterIsingSystem` via the exact
positive-semidefinite checkerboard Trotter transfer pair `(V₀^{(M)}, V₁^{(M)})`:
  `Z_+^{(M)}(2m, b) = Tr((V₀ V₀ᵀ)^m) + Tr((V₁ V₁ᵀ)^m) → Z_+(2m, b)` as `M → ∞`,
  `Z_-^{(M)}(2m, b) = Tr((V₀ V₀ᵀ)^m) - Tr((V₁ V₁ᵀ)^m) → Z_-(2m, b)` as `M → ∞`.

Combining this with `candidate_e_rectangle_Qplus_ge` and `candidate_e_three_rounds_to_64` yields
`candidate_e_unconditional_rectangle_theorem`: for every `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]`
and every even `ℓ ≥ 64`, sorting the full untwisted spectrum of `H_ising ℓ g h` (`2^ℓ` eigenvalues)
satisfies:
- `0 ≤ E_1(ℓ) - E_0(ℓ) ≤ (1 / 20) * exp (-(log 20) * ℓ / 128)`,
- `E_i(ℓ) - E_1(ℓ) > log 8 / 48` for every excited level `i ≥ 2`.
-/

namespace PurityBootstrap.IsingTrotter

open scoped BigOperators Matrix Matrix.Norms.Operator
open Filter Matrix NormedSpace
open PurityBootstrap PurityBootstrap.MatrixTools PurityBootstrap.IsingHamiltonian
open PurityBootstrap.IsingMPS PurityBootstrap.LieTrotter PurityBootstrap.CandidateE

/-! ## Section 1: Single-Qubit Pauli Algebra & Parity Selection Rule -/

/-- Spin eigenvalue `+1` (`false`) or `-1` (`true`) in the `X`-basis. -/
def spinB (x : Bool) : ℝ := if x then (-1 : ℝ) else (1 : ℝ)

def matI : Matrix Bool Bool ℝ := 1
def matZ1 : Matrix Bool Bool ℝ := Matrix.of fun a b => if b = !a then (1 : ℝ) else 0
def matX1 : Matrix Bool Bool ℝ := Matrix.diagonal spinB
def matZX1 : Matrix Bool Bool ℝ := matZ1 * matX1

def op4 : Fin 4 → Matrix Bool Bool ℝ
  | ⟨0, _⟩ => matI
  | ⟨1, _⟩ => matZ1
  | ⟨2, _⟩ => matX1
  | ⟨3, _⟩ => matZX1

def isFlip : Fin 4 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => true

def twistSign (tw : Bool) (α : Fin 4) : ℝ :=
  if tw && isFlip α then (-1 : ℝ) else (1 : ℝ)

noncomputable def bondCoeff (τ g : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => Real.cosh τ * Real.cosh (τ * g)
  | ⟨1, _⟩ => Real.sinh τ * Real.cosh (τ * g)
  | ⟨2, _⟩ => Real.cosh τ * Real.sinh (τ * g)
  | ⟨3, _⟩ => Real.sinh τ * Real.sinh (τ * g)

noncomputable def EX (τ h : ℝ) : Matrix Bool Bool ℝ :=
  Matrix.diagonal fun s => Real.exp (τ * h * spinB s)

lemma bondCoeff_nonneg {τ g : ℝ} (hτ : 0 ≤ τ) (hg : 0 ≤ g) (α : Fin 4) :
    0 ≤ bondCoeff τ g α := by
  have hsinh_nn : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sinh x := fun x hx => by
    rw [Real.sinh_eq]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h1 : 0 ≤ Real.cosh τ := (Real.cosh_pos τ).le
  have h2 : 0 ≤ Real.cosh (τ * g) := (Real.cosh_pos (τ * g)).le
  have h3 : 0 ≤ Real.sinh τ := hsinh_nn τ hτ
  have h4 : 0 ≤ Real.sinh (τ * g) := hsinh_nn (τ * g) (mul_nonneg hτ hg)
  fin_cases α <;> dsimp [bondCoeff] <;> positivity

lemma matZ1_sq : matZ1 * matZ1 = 1 := by
  ext a b; cases a <;> cases b <;>
    simp [matZ1, Matrix.mul_apply, Fintype.sum_bool]

lemma matX1_sq : matX1 * matX1 = 1 := by
  ext a b; cases a <;> cases b <;>
    simp [matX1, spinB, Matrix.mul_apply, Fintype.sum_bool]

lemma matX1_mul_matZ1 : matX1 * matZ1 = -matZX1 := by
  ext a b; cases a <;> cases b <;>
    simp [matX1, matZ1, matZX1, spinB, Matrix.mul_apply, Fintype.sum_bool]

lemma op4_apply_eq_zero {α : Fin 4} {a b : Bool} (h : b ≠ xor a (isFlip α)) :
    op4 α a b = 0 := by
  fin_cases α <;> cases a <;> cases b <;>
    simp [op4, matI, matZ1, matX1, matZX1, isFlip, spinB, Matrix.mul_apply, Fintype.sum_bool] at h ⊢

/-- Product of `M` Trotter slices on a single site `(α, β : Fin M → Fin 4)`. -/
noncomputable def sliceProd (τ h : ℝ) {M : ℕ} (α β : Fin M → Fin 4) : Matrix Bool Bool ℝ :=
  matProd (fun r : Fin M => EX τ h * op4 (α r) * op4 (β r))

/-- Total bit-flip parity of a `Fin M → Fin 4` time history. -/
def flipParity {M : ℕ} (α : Fin M → Fin 4) : Bool :=
  tupleParity (fun r : Fin M => isFlip (α r))

lemma prod_twistSign_true : ∀ {M : ℕ} (α : Fin M → Fin 4),
    (∏ r : Fin M, twistSign true (α r)) = if flipParity α then (-1 : ℝ) else (1 : ℝ)
  | 0, _ => by simp [flipParity, tupleParity]
  | M + 1, α => by
    rw [Fin.prod_univ_castSucc, prod_twistSign_true (fun r : Fin M => α r.castSucc)]
    simp only [flipParity, tupleParity, twistSign, Bool.true_and]
    rcases Bool.eq_false_or_eq_true (isFlip (α (Fin.last M))) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (tupleParity (fun r : Fin M => isFlip (α r.castSucc))) with h2 | h2 <;>
      simp [h1, h2]

lemma sliceProd_apply_eq_zero (τ h : ℝ) : ∀ {M : ℕ} (α β : Fin M → Fin 4) {a b : Bool},
    b ≠ xor a (xor (flipParity α) (flipParity β)) →
    sliceProd τ h α β a b = 0
  | 0, α, β, a, b, hne => by
    simp only [sliceProd, matProd, flipParity, tupleParity, Bool.xor_false] at hne ⊢
    simp [Matrix.one_apply, Ne.symm hne]
  | M + 1, α, β, a, b, hne => by
    have hsplit : sliceProd τ h α β =
        (EX τ h * op4 (α 0) * op4 (β 0)) *
        sliceProd τ h (fun r : Fin M => α r.succ) (fun r : Fin M => β r.succ) := rfl
    have hpar_succ : ∀ (γ : Fin (M + 1) → Fin 4),
        flipParity γ = xor (isFlip (γ 0)) (flipParity (fun r : Fin M => γ r.succ)) := by
      intro γ
      have hprod : (if flipParity γ then (-1 : ℝ) else 1) =
          (if isFlip (γ 0) then (-1 : ℝ) else 1) *
          (if flipParity (fun r : Fin M => γ r.succ) then (-1 : ℝ) else 1) := by
        rw [← prod_twistSign_true γ, Fin.prod_univ_succ, prod_twistSign_true]
        simp [twistSign]
      rcases Bool.eq_false_or_eq_true (flipParity γ) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (isFlip (γ 0)) with h2 | h2 <;>
        rcases Bool.eq_false_or_eq_true (flipParity (fun r : Fin M => γ r.succ)) with h3 | h3 <;>
        simp [h1, h2, h3] at hprod ⊢ <;> norm_num at hprod
    rw [hsplit, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = xor a (xor (isFlip (α 0)) (isFlip (β 0)))
    · have hne2 : b ≠ xor c (xor (flipParity (fun r : Fin M => α r.succ))
          (flipParity (fun r : Fin M => β r.succ))) := by
        rw [hc]; intro heq; apply hne
        rw [heq, hpar_succ α, hpar_succ β]
        cases a <;> cases isFlip (α 0) <;> cases isFlip (β 0) <;>
          cases flipParity (fun r : Fin M => α r.succ) <;>
          cases flipParity (fun r : Fin M => β r.succ) <;> rfl
      rw [sliceProd_apply_eq_zero τ h _ _ hne2, mul_zero]
    · have hleft : (EX τ h * op4 (α 0) * op4 (β 0)) a c = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun d _ => ?_
        by_cases hd : d = xor a (isFlip (α 0))
        · have hne_b : c ≠ xor d (isFlip (β 0)) := by
            rw [hd]; intro heq; apply hc; rw [heq, Bool.xor_assoc]
          rw [op4_apply_eq_zero hne_b, mul_zero]
        · have hEA : (EX τ h * op4 (α 0)) a d = 0 := by
            simp only [EX, Matrix.diagonal_mul]
            rw [op4_apply_eq_zero hd, mul_zero]
          rw [hEA, zero_mul]
      rw [hleft, zero_mul]

lemma trace_sliceProd_eq_zero (τ h : ℝ) {M : ℕ} (Q : Matrix Bool Bool ℝ)
    (hQdiag : ∀ a b, a ≠ b → Q a b = 0)
    {α β : Fin M → Fin 4} (hne : flipParity α ≠ flipParity β) :
    Matrix.trace (Q * sliceProd τ h α β) = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : a = c
  · subst hac
    have hneq : a ≠ xor a (xor (flipParity α) (flipParity β)) := by
      cases a <;> cases h1 : flipParity α <;> cases h2 : flipParity β <;>
        simp [h1, h2] at hne ⊢
    rw [sliceProd_apply_eq_zero τ h α β hneq, mul_zero]
  · rw [hQdiag a c hac, zero_mul]

/-! ## Section 2: `L`-Qubit Tensor Product `kronVec` & Multi-Site Algebra -/

/-- Tensor product of `L` single-qubit matrices `U i : Matrix Bool Bool ℝ` on `Fin L → Bool`. -/
def kronVec {L : ℕ} (U : Fin L → Matrix Bool Bool ℝ) :
    Matrix (Fin L → Bool) (Fin L → Bool) ℝ :=
  Matrix.of fun a b => ∏ i : Fin L, U i (a i) (b i)

lemma kronVec_one (L : ℕ) :
    kronVec (fun _ : Fin L => (1 : Matrix Bool Bool ℝ)) = 1 := by
  ext a b
  simp only [kronVec, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]
    have hex : ∃ i : Fin L, a i ≠ b i := by
      by_contra hall; push Not at hall; exact h (funext hall)
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma kronVec_mul {L : ℕ} (U V : Fin L → Matrix Bool Bool ℝ) :
    kronVec U * kronVec V = kronVec (fun i => U i * V i) := by
  ext a b
  simp only [kronVec, Matrix.mul_apply, Matrix.of_apply]
  have h1 : ∀ c : Fin L → Bool,
      (∏ i : Fin L, U i (a i) (c i)) * (∏ i : Fin L, V i (c i) (b i)) =
      ∏ i : Fin L, U i (a i) (c i) * V i (c i) (b i) := fun c =>
    (Finset.prod_mul_distrib).symm
  simp_rw [h1]
  exact (Fintype.prod_sum (fun i s => U i (a i) s * V i s (b i))).symm

lemma trace_kronVec {L : ℕ} (U : Fin L → Matrix Bool Bool ℝ) :
    Matrix.trace (kronVec U) = ∏ i : Fin L, Matrix.trace (U i) := by
  simp only [Matrix.trace, Matrix.diag, kronVec, Matrix.of_apply]
  exact (Fintype.prod_sum (fun i s => U i s s)).symm

/-- Two-site operator placing `P` at `i`, `Q` at `j`, and `1` elsewhere. -/
def twoSite {L : ℕ} (i j : Fin L) (P Q : Matrix Bool Bool ℝ) :
    Matrix (Fin L → Bool) (Fin L → Bool) ℝ :=
  kronVec (fun k => if k = i then P else if k = j then Q else 1)

lemma twoSite_mul_same {L : ℕ} {i j : Fin L} (hij : i ≠ j)
    (P₁ Q₁ P₂ Q₂ : Matrix Bool Bool ℝ) :
    twoSite i j P₁ Q₁ * twoSite i j P₂ Q₂ = twoSite i j (P₁ * P₂) (Q₁ * Q₂) := by
  unfold twoSite
  rw [kronVec_mul]
  congr 1; funext k
  by_cases h1 : k = i
  · subst h1; simp
  · by_cases h2 : k = j
    · subst h2; simp [hij.symm]
    · simp [h1, h2]

lemma twoSite_comm_disjoint {L : ℕ} {i₁ j₁ i₂ j₂ : Fin L}
    (h1 : i₁ ≠ i₂) (h2 : i₁ ≠ j₂) (h3 : j₁ ≠ i₂) (h4 : j₁ ≠ j₂)
    (P₁ Q₁ P₂ Q₂ : Matrix Bool Bool ℝ) :
    Commute (twoSite i₁ j₁ P₁ Q₁) (twoSite i₂ j₂ P₂ Q₂) := by
  change twoSite i₁ j₁ P₁ Q₁ * twoSite i₂ j₂ P₂ Q₂ = twoSite i₂ j₂ P₂ Q₂ * twoSite i₁ j₁ P₁ Q₁
  unfold twoSite
  rw [kronVec_mul, kronVec_mul]
  congr 1; funext k
  by_cases hi1 : k = i₁
  · subst hi1; simp [h1, h2]
  · by_cases hj1 : k = j₁
    · subst hj1; simp [hi1, h3, h4]
    · by_cases hi2 : k = i₂
      · subst hi2; simp [hi1, hj1]
      · by_cases hj2 : k = j₂
        · subst hj2; simp [hi1, hj1, hi2, h2.symm, h4.symm]
        · simp [hi1, hj1, hi2, hj2]

lemma twoSite_neg_neg {L : ℕ} {i j : Fin L} (hij : i ≠ j) (P Q : Matrix Bool Bool ℝ) :
    twoSite i j (-P) (-Q) = twoSite i j P Q := by
  ext a b
  unfold twoSite kronVec
  simp only [Matrix.of_apply]
  have hsplit : ∀ (R S : Matrix Bool Bool ℝ),
      (∏ k : Fin L, (if k = i then R else if k = j then S else 1) (a k) (b k)) =
      R (a i) (b i) * S (a j) (b j) *
      ∏ k ∈ (Finset.univ.erase i).erase j, (1 : Matrix Bool Bool ℝ) (a k) (b k) := by
    intro R S
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ hj_mem]
    simp only [↓reduceIte, hij.symm, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk1 : k ≠ j := (Finset.mem_erase.mp hk).1
    have hk2 : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp [hk1, hk2]
  rw [hsplit (-P) (-Q), hsplit P Q]
  simp [Matrix.neg_apply]

lemma twoSite_ZZ_XX_comm {L : ℕ} {i j : Fin L} (hij : i ≠ j) :
    Commute (twoSite i j matZ1 matZ1) (twoSite i j matX1 matX1) := by
  change twoSite i j matZ1 matZ1 * twoSite i j matX1 matX1 =
    twoSite i j matX1 matX1 * twoSite i j matZ1 matZ1
  rw [twoSite_mul_same hij, twoSite_mul_same hij, matX1_mul_matZ1, twoSite_neg_neg hij]
  rfl

lemma twoSite_ZZ_sq {L : ℕ} {i j : Fin L} (hij : i ≠ j) :
    twoSite i j matZ1 matZ1 * twoSite i j matZ1 matZ1 = 1 := by
  rw [twoSite_mul_same hij, matZ1_sq]
  simpa [twoSite] using kronVec_one L

lemma twoSite_XX_sq {L : ℕ} {i j : Fin L} (hij : i ≠ j) :
    twoSite i j matX1 matX1 * twoSite i j matX1 matX1 = 1 := by
  rw [twoSite_mul_same hij, matX1_sq]
  simpa [twoSite] using kronVec_one L

set_option backward.isDefEq.respectTransparency false in
/-- Single-bond exponential expands as a 4-term sum of `twoSite i j (op4 α) (op4 α)`! -/
lemma exp_bond_eq_sum4 {L : ℕ} {i j : Fin L} (hij : i ≠ j) (τ g : ℝ) (tw : Bool) :
    let t : ℝ := if tw then (-1 : ℝ) else 1
    NormedSpace.exp (τ • (t • twoSite i j matZ1 matZ1 + g • twoSite i j matX1 matX1)) =
      ∑ α : Fin 4, (twistSign tw α * bondCoeff τ g α) • twoSite i j (op4 α) (op4 α) := by
  intro t
  have hcomm : Commute ((τ * t) • twoSite i j matZ1 matZ1) ((τ * g) • twoSite i j matX1 matX1) :=
    (twoSite_ZZ_XX_comm hij).smul_left (τ * t) |>.smul_right (τ * g)
  have harg : τ • (t • twoSite i j matZ1 matZ1 + g • twoSite i j matX1 matX1) =
      (τ * t) • twoSite i j matZ1 matZ1 + (τ * g) • twoSite i j matX1 matX1 := by
    rw [smul_add, smul_smul, smul_smul]
  rw [harg, NormedSpace.exp_add_of_commute hcomm,
    exp_involutive (twoSite_ZZ_sq hij), exp_involutive (twoSite_XX_sq hij)]
  have hcosh_t : Real.cosh (τ * t) = Real.cosh τ := by
    dsimp [t]; cases tw <;> simp
  have hsinh_t : Real.sinh (τ * t) = t * Real.sinh τ := by
    dsimp [t]; cases tw <;> simp
  rw [hcosh_t, hsinh_t]
  have h1 : twoSite i j (op4 0) (op4 0) = 1 := by
    simpa [op4, matI, twoSite] using kronVec_one L
  have h2 : twoSite i j (op4 1) (op4 1) = twoSite i j matZ1 matZ1 := rfl
  have h3 : twoSite i j (op4 2) (op4 2) = twoSite i j matX1 matX1 := rfl
  have h4 : twoSite i j (op4 3) (op4 3) = twoSite i j matZ1 matZ1 * twoSite i j matX1 matX1 :=
    (twoSite_mul_same hij matZ1 matZ1 matX1 matX1).symm
  rw [Fin.sum_univ_four, h1, h2, h3, h4]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [twistSign, isFlip, bondCoeff, Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  dsimp [t]
  cases tw <;> simp [smul_smul, sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] <;> abel

set_option backward.isDefEq.respectTransparency false in
private lemma commute_exp_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (h : Commute A B) :
    Commute (NormedSpace.exp A) (NormedSpace.exp B) := by
  change NormedSpace.exp A * NormedSpace.exp B = NormedSpace.exp B * NormedSpace.exp A
  rw [← NormedSpace.exp_add_of_commute h, ← NormedSpace.exp_add_of_commute h.symm, add_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Exponential of a commuting finite sum of matrices equals the product of exponentials. -/
lemma exp_finset_sum_of_commute {n ι : Type*} [Fintype n] [DecidableEq n] [DecidableEq ι]
    (s : Finset ι) (f : ι → Matrix n n ℝ)
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, Commute (f a) (f b)) :
    NormedSpace.exp (∑ x ∈ s, f x) = s.noncommProd (fun x => NormedSpace.exp (f x))
      (fun a ha b hb _ => commute_exp_of_commute (hcomm a ha b hb)) := by
  induction s using Finset.induction_on with
  | empty => simp [NormedSpace.exp_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hcomm_sum : Commute (f a) (∑ x ∈ s, f x) :=
      Commute.sum_right s _ _ fun x hx =>
        hcomm a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx)
    rw [NormedSpace.exp_add_of_commute hcomm_sum,
      Finset.noncommProd_insert_of_notMem s a (fun x => NormedSpace.exp (f x)) _ ha]
    congr 1
    exact ih fun x hx y hy =>
      hcomm x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)

/-! ## Section 3: Full `2^(2m)`-Dim Ising Hamiltonian & Exact Block-Diagonal Equivalence -/

/-- Even bond index `(2j, 2j+1)` for `j : Fin m`. -/
def evenL {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨2 * j.val, by omega⟩
def evenR {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨2 * j.val + 1, by omega⟩

/-- Odd bond index `(2j+1, (2j+2) % (2m))` for `j : Fin m`. -/
def oddL {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨2 * j.val + 1, by omega⟩
def oddR {m : ℕ} (hm : 0 < m) (j : Fin m) : Fin (2 * m) :=
  ⟨(2 * j.val + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩

/-- Previous cell index `(j - 1) mod m` on the `m`-cell ring. -/
def prevCell {m : ℕ} (hm : 0 < m) (j : Fin m) : Fin m :=
  ⟨(j.val + m - 1) % m, Nat.mod_lt _ hm⟩

/-- Last cell index `m - 1` on the `m`-cell ring (`0 < m`). -/
def lastCell {m : ℕ} (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩

lemma evenL_ne_evenR {m : ℕ} (j : Fin m) : evenL j ≠ evenR j := by
  intro h; have := congrArg Fin.val h; dsimp [evenL, evenR] at this; omega

lemma oddL_ne_oddR {m : ℕ} (hm : 2 ≤ m) (j : Fin m) : oddL j ≠ oddR (by omega) j := by
  intro h; have := congrArg Fin.val h; dsimp [oddL, oddR] at this
  by_cases hlt : 2 * j.val + 2 < 2 * m
  · rw [Nat.mod_eq_of_lt hlt] at this; omega
  · have heq : 2 * j.val + 2 = 2 * m := by omega
    rw [heq, Nat.mod_self] at this; omega

/-- Full `2^(2m)`-dim transverse field piece `A_X = h ∑_i X_i` (sign `-H_X`). -/
def A_X (L : ℕ) (h : ℝ) : Matrix (Fin L → Bool) (Fin L → Bool) ℝ :=
  Matrix.diagonal fun a => h * ∑ k : Fin L, spinB (a k)

/-- Full `2^(2m)`-dim even-bond piece `A_even = ∑_j (Z_{2j} Z_{2j+1} + g X_{2j} X_{2j+1})`. -/
def A_even (m : ℕ) (g : ℝ) : Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ :=
  ∑ j : Fin m, (twoSite (evenL j) (evenR j) matZ1 matZ1 +
    g • twoSite (evenL j) (evenR j) matX1 matX1)

/-- Full `2^(2m)`-dim odd-bond piece `A_odd` (closing bond `j = m - 1` gets sign `-1` when `tw = true`). -/
def A_odd (m : ℕ) (hm : 0 < m) (g : ℝ) (tw : Bool) :
    Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ :=
  ∑ j : Fin m,
    ((if tw && decide (j.val = m - 1) then (-1 : ℝ) else 1) •
      twoSite (oddL j) (oddR hm j) matZ1 matZ1 +
     g • twoSite (oddL j) (oddR hm j) matX1 matX1)

/-- Global `X`-parity operator `P_full = ⊗_i X_i`. -/
def P_full (L : ℕ) : Matrix (Fin L → Bool) (Fin L → Bool) ℝ :=
  kronVec (fun _ : Fin L => matX1)

lemma P_full_eq_diagonal (L : ℕ) :
    P_full L = Matrix.diagonal (fun a : Fin L → Bool => if tupleParity a then (-1 : ℝ) else 1) := by
  ext a b
  simp only [P_full, kronVec, Matrix.of_apply, matX1, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    simpa [spinB] using spinBool_prod_eq a
  · rw [if_neg h]
    have hex : ∃ i : Fin L, a i ≠ b i := by
      by_contra hall; push Not at hall; exact h (funext hall)
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Equivalence `(Fin (2 * m) → Bool) ≃ Fin (2 ^ (2 * m - 1)) × Bool` aligning full space with `Matrix.blockDiagonal`. -/
def fullSectorEquiv (m : ℕ) (hm : 1 ≤ m) :
    (Fin (2 * m) → Bool) ≃ Fin (2 ^ (2 * m - 1)) × Bool :=
  ((Equiv.arrowCongr (finCongr (show 2 * m = (2 * m - 1) + 1 by omega)) (Equiv.refl Bool)).trans
    (sectorEquiv (2 * m - 1))).trans (Equiv.prodComm Bool (Fin (2 ^ (2 * m - 1))))

lemma fullSectorEquiv_symm_apply {m : ℕ} (hm : 1 ≤ m) (sec : Bool)
    (i : Fin (2 ^ (2 * m - 1))) (k : Fin (2 * m)) :
    (fullSectorEquiv m hm).symm (i, sec) k = (sectorState (2 * m) sec i).testBit k.val := by
  simp only [fullSectorEquiv, Equiv.symm_trans_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm,
    sectorEquiv, Equiv.coe_fn_symm_mk]
  have hst : sectorState (2 * m - 1 + 1) sec i = sectorState (2 * m) sec i := by
    simp only [sectorState, Nat.add_sub_cancel]
  simp [hst]

lemma flipPair_eq_twoSite_ZZ {L : ℕ} {i j : Fin L} (hij : i ≠ j) (a b : Fin L → Bool) :
    twoSite i j matZ1 matZ1 a b =
      if (∀ k : Fin L, b k = if k = i ∨ k = j then !(a k) else a k) then (1 : ℝ) else 0 := by
  unfold twoSite kronVec
  simp only [Matrix.of_apply]
  by_cases h : ∀ k : Fin L, b k = if k = i ∨ k = j then !(a k) else a k
  · rw [if_pos h]
    refine Finset.prod_eq_one fun k _ => ?_
    have hk := h k
    by_cases h1 : k = i
    · subst h1; simp [matZ1, hk]
    · by_cases h2 : k = j
      · subst h2; simp [h1, matZ1, hk]
      · simp [h1, h2] at hk
        simp [h1, h2, Matrix.one_apply, hk]
  · rw [if_neg h]
    push Not at h
    rcases h with ⟨k, hk⟩
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    by_cases h1 : k = i
    · subst h1; simp [matZ1] at hk ⊢; exact hk
    · by_cases h2 : k = j
      · subst h2; simp [h1, matZ1] at hk ⊢; exact hk
      · simp [h1, h2] at hk
        simp [h1, h2, Matrix.one_apply]
        exact fun (heq : a k = b k) => hk heq.symm

lemma twoSite_XX_apply {L : ℕ} {i j : Fin L} (hij : i ≠ j) (a b : Fin L → Bool) :
    twoSite i j matX1 matX1 a b = if a = b then spinB (a i) * spinB (a j) else 0 := by
  unfold twoSite kronVec
  simp only [Matrix.of_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ hj_mem]
    have hrest : ∏ k ∈ (Finset.univ.erase i).erase j,
        (if k = i then matX1 else if k = j then matX1 else 1) (a k) (a k) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hk1 : k ≠ j := (Finset.mem_erase.mp hk).1
      have hk2 : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp [hk1, hk2]
    rw [hrest, mul_one]
    simp [hij.symm, matX1]
  · rw [if_neg h]
    have hex : ∃ k : Fin L, a k ≠ b k := by
      by_contra hall; push Not at hall; exact h (funext hall)
    rcases hex with ⟨k, hk⟩
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    by_cases h1 : k = i
    · subst h1; simp [matX1, hk]
    · by_cases h2 : k = j
      · subst h2; simp [h1, matX1, hk]
      · simp [h1, h2, hk]

/-- Testbit characterization of `sectorState (2*m)` vs `flipBond (2*m)`. -/
private lemma sectorState_flipBond_iff {L : ℕ} (hL : 2 ≤ L)
    (sec₁ sec₂ : Bool) (i₁ i₂ : Fin (2 ^ (L - 1))) (k : ℕ) (hk : k < L) :
    (∀ r : Fin L, (sectorState L sec₂ i₂).testBit r.val =
      if r.val = k ∨ r.val = (k + 1) % L then !((sectorState L sec₁ i₁).testBit r.val)
      else (sectorState L sec₁ i₁).testBit r.val) ↔
    (sec₂ = sec₁ ∧ i₂ = flipBond L k i₁) := by
  have hk_ne : k ≠ (k + 1) % L := by
    by_cases hlt : k + 1 < L
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have : k + 1 = L := by omega
      rw [this, Nat.mod_self]; omega
  have hbit_flip : ∀ r : ℕ, r < L - 1 →
      (flipBond L k i₁).val.testBit r =
        if r = k ∨ r = (k + 1) % L then !(i₁.val.testBit r) else i₁.val.testBit r := by
    intro r hr
    simp only [flipBond]
    rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and, Nat.testBit_xor,
      Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and, Nat.testBit_xor]
    have htb : ∀ c : ℕ, (1 <<< c).testBit r = decide (r = c) := fun c => by
      rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
      by_cases hrc : r = c
      · subst hrc; simp
      · simp [hrc, Ne.symm hrc]
    rw [htb k, htb ((k + 1) % L)]
    by_cases h1 : r = k
    · subst h1; simp [hk_ne]
    · by_cases h2 : r = (k + 1) % L
      · subst h2; simp [h1]
      · simp [h1, h2]
  have hlow_eq : ∀ sec (i : Fin (2 ^ (L - 1))) (r : ℕ), r < L - 1 →
      (sectorState L sec i).testBit r = i.val.testBit r := fun sec i r hr => by
    unfold sectorState
    rw [testBit_add_two_pow i.isLt, if_neg (by omega), if_pos hr]
  have hpar_state : ∀ sec (i : Fin (2 ^ (L - 1))),
      tupleParity (fun r : Fin L => (sectorState L sec i).testBit r.val) = sec := by
    intro sec i
    have hgen : ∀ (m : ℕ) (hLm : L = m + 1) (j : Fin (2 ^ (L - 1))),
        tupleParity (fun r : Fin L => (sectorState L sec j).testBit r.val) = sec := by
      intro m hLm; subst hLm; intro j
      exact congrArg Prod.fst ((sectorEquiv m).right_inv (sec, j))
    exact hgen (L - 1) (by omega) i
  have hflip_par : ∀ (b : Fin L → Bool),
      tupleParity (fun r : Fin L => if r.val = k ∨ r.val = (k + 1) % L then !(b r) else b r) =
      tupleParity b := by
    intro b
    have hprod :
        (if tupleParity (fun r : Fin L => if r.val = k ∨ r.val = (k + 1) % L then !(b r) else b r)
          then (-1 : ℝ) else 1) =
        if tupleParity b then (-1 : ℝ) else 1 := by
      rw [← spinBool_prod_eq, ← spinBool_prod_eq]
      let r1 : Fin L := ⟨k, hk⟩
      let r2 : Fin L := ⟨(k + 1) % L, Nat.mod_lt _ (by omega)⟩
      have hr12 : r1 ≠ r2 := fun h => hk_ne (congrArg Fin.val h)
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r1),
        ← Finset.mul_prod_erase (Finset.univ.erase r1) _ (Finset.mem_erase.mpr ⟨hr12.symm, Finset.mem_univ r2⟩)]
      symm
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r1),
        ← Finset.mul_prod_erase (Finset.univ.erase r1) _ (Finset.mem_erase.mpr ⟨hr12.symm, Finset.mem_univ r2⟩)]
      have hrest : ∏ r ∈ (Finset.univ.erase r1).erase r2,
          (if (if r.val = k ∨ r.val = (k + 1) % L then !b r else b r) then (-1 : ℝ) else 1) =
          ∏ r ∈ (Finset.univ.erase r1).erase r2, (if b r then (-1 : ℝ) else 1) := by
        refine Finset.prod_congr rfl fun r hr => ?_
        have hnr2 : r ≠ r2 := (Finset.mem_erase.mp hr).1
        have hnr1 : r ≠ r1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
        have hv1 : r.val ≠ k := fun h => hnr1 (Fin.ext h)
        have hv2 : r.val ≠ (k + 1) % L := fun h => hnr2 (Fin.ext h)
        simp [hv1, hv2]
      rw [hrest]
      simp only [r1, r2, true_or, or_true, ↓reduceIte]
      rcases Bool.eq_false_or_eq_true (b ⟨k, hk⟩) with hb1 | hb1 <;>
        rcases Bool.eq_false_or_eq_true (b ⟨(k + 1) % L, Nat.mod_lt _ (by omega)⟩) with hb2 | hb2 <;>
        simp [hb1, hb2] <;> ring
    rcases Bool.eq_false_or_eq_true
      (tupleParity (fun r : Fin L => if r.val = k ∨ r.val = (k + 1) % L then !(b r) else b r)) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (tupleParity b) with h2 | h2 <;>
      simp [h1, h2] at hprod ⊢ <;> norm_num at hprod
  constructor
  · intro hall
    have hsec : sec₂ = sec₁ := by
      rw [← hpar_state sec₂ i₂, ← hpar_state sec₁ i₁]
      have hfn : (fun r : Fin L => (sectorState L sec₂ i₂).testBit r.val) =
          (fun r : Fin L => if r.val = k ∨ r.val = (k + 1) % L
            then !((sectorState L sec₁ i₁).testBit r.val)
            else (sectorState L sec₁ i₁).testBit r.val) := funext hall
      rw [hfn, hflip_par]
    refine ⟨hsec, ?_⟩
    ext
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < L - 1
    · rw [hbit_flip r hr, ← hlow_eq sec₂ i₂ r hr, ← hlow_eq sec₁ i₁ r hr]
      exact hall ⟨r, by omega⟩
    · have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le i₂.isLt
        (Nat.pow_le_pow_right (by norm_num) (by omega : L - 1 ≤ r)))
      have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (flipBond L k i₁).isLt
        (Nat.pow_le_pow_right (by norm_num) (by omega : L - 1 ≤ r)))
      rw [h1, h2]
  · rintro ⟨hsec, hi2⟩ r
    rw [hsec, hi2]
    by_cases hr : r.val < L - 1
    · rw [hlow_eq sec₁ (flipBond L k i₁) r.val hr, hlow_eq sec₁ i₁ r.val hr, hbit_flip r.val hr]
    · have htop : r.val = L - 1 := by omega
      have hpar_eq : tupleParity (fun s : Fin L => (sectorState L sec₁ (flipBond L k i₁)).testBit s.val) =
          tupleParity (fun s : Fin L => if s.val = k ∨ s.val = (k + 1) % L
            then !((sectorState L sec₁ i₁).testBit s.val)
            else (sectorState L sec₁ i₁).testBit s.val) := by
        rw [hpar_state, hflip_par, hpar_state]
      have hprod_eq :
          (∏ s : Fin L, if (sectorState L sec₁ (flipBond L k i₁)).testBit s.val then (-1 : ℝ) else 1) =
          (∏ s : Fin L, if (if s.val = k ∨ s.val = (k + 1) % L
            then !((sectorState L sec₁ i₁).testBit s.val)
            else (sectorState L sec₁ i₁).testBit s.val) then (-1 : ℝ) else 1) := by
        rw [spinBool_prod_eq, spinBool_prod_eq, hpar_eq]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)] at hprod_eq
      conv_rhs at hprod_eq => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
      have hlow_prod :
          (∏ s ∈ Finset.univ.erase r,
            if (sectorState L sec₁ (flipBond L k i₁)).testBit s.val then (-1 : ℝ) else 1) =
          (∏ s ∈ Finset.univ.erase r,
            if (if s.val = k ∨ s.val = (k + 1) % L
              then !((sectorState L sec₁ i₁).testBit s.val)
              else (sectorState L sec₁ i₁).testBit s.val) then (-1 : ℝ) else 1) := by
        refine Finset.prod_congr rfl fun s hs => ?_
        have hsne : s ≠ r := (Finset.mem_erase.mp hs).1
        have hslt : s.val < L - 1 := by
          have : s.val ≠ r.val := fun h => hsne (Fin.ext h)
          omega
        rw [hlow_eq sec₁ (flipBond L k i₁) s.val hslt, hlow_eq sec₁ i₁ s.val hslt, hbit_flip s.val hslt]
      have hlow_ne : (∏ s ∈ Finset.univ.erase r,
          if (if s.val = k ∨ s.val = (k + 1) % L
            then !((sectorState L sec₁ i₁).testBit s.val)
            else (sectorState L sec₁ i₁).testBit s.val) then (-1 : ℝ) else 1) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun s _ => ?_
        split_ifs <;> norm_num
      rw [hlow_prod] at hprod_eq
      have htop_val := mul_right_cancel₀ hlow_ne hprod_eq
      rcases Bool.eq_false_or_eq_true ((sectorState L sec₁ (flipBond L k i₁)).testBit r.val) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (if r.val = k ∨ r.val = (k + 1) % L
          then !((sectorState L sec₁ i₁).testBit r.val)
          else (sectorState L sec₁ i₁).testBit r.val) with h2 | h2 <;>
        simp [h1, h2] at htop_val ⊢ <;> norm_num at htop_val

/-- Reindexing `b • (A_X + A_even + A_odd)` by `fullSectorEquiv` produces the exact block-diagonal
matrix `blockDiagonal (fun sec => (-b) • H_ising (2 * m) g h tw sec)`! -/
theorem reindex_Afull_eq_blockDiagonal {m : ℕ} (hm : 2 ≤ m) (b g h : ℝ) (tw : Bool) :
    let e := fullSectorEquiv m (by omega)
    (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw)).reindex e e =
      Matrix.blockDiagonal (fun sec : Bool => (-b) • H_ising (2 * m) g h tw sec) := by
  intro e
  ext ⟨i₁, sec₁⟩ ⟨i₂, sec₂⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.blockDiagonal_apply, smul_eq_mul]
  -- Split `H_ising` into `H_ZZ + g • H_XX + h • H_X` and compare entry by entry!
  have hsum_even_odd : ∀ (F : ℕ → ℝ),
      (∑ j : Fin m, F (2 * j.val)) + (∑ j : Fin m, F (2 * j.val + 1)) =
      ∑ k ∈ Finset.range (2 * m), F k := by
    intro F
    have hsplit : ∑ k ∈ Finset.range (2 * m), F k =
        ∑ j ∈ Finset.range m, (F (2 * j) + F (2 * j + 1)) := by
      clear hm b g h tw e sec₁ sec₂ i₁ i₂
      induction m with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
        ring
    rw [hsplit, Finset.sum_add_distrib, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  -- 1. Evaluate `A_X` entry
  have hAX : A_X (2 * m) h (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
      if sec₁ = sec₂ then (-h) * H_X (2 * m) sec₁ i₁ i₂ else 0 := by
    simp only [A_X, H_X, Matrix.diagonal_apply]
    by_cases hpair : (i₁, sec₁) = (i₂, sec₂)
    · rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [← Fin.sum_univ_eq_sum_range]
      have hterm : ∑ k : Fin (2 * m), spinB (e.symm (i₁, sec₁) k) =
          -(∑ k : Fin (2 * m), -spinVal (sectorState (2 * m) sec₁ i₁) k.val) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [fullSectorEquiv_symm_apply]
        simp [spinB, spinVal]
      rw [hterm]; ring
    · have hne : e.symm (i₁, sec₁) ≠ e.symm (i₂, sec₂) := fun h => hpair (e.symm.injective h)
      rw [if_neg hne]
      by_cases hs : sec₁ = sec₂
      · subst hs
        have hi : i₁ ≠ i₂ := fun h => hpair (by rw [h])
        simp [hi]
      · simp [hs]
  -- 2. Evaluate `XX` part of `A_even + A_odd`
  have hXX : (∑ j : Fin m, (g • twoSite (evenL j) (evenR j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) +
      (∑ j : Fin m, (g • twoSite (oddL j) (oddR (by omega) j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) =
      if sec₁ = sec₂ then (-g) * H_XX (2 * m) sec₁ i₁ i₂ else 0 := by
    have heven : ∀ j : Fin m,
        (g • twoSite (evenL j) (evenR j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
        if (i₁, sec₁) = (i₂, sec₂) then
          g * (spinVal (sectorState (2 * m) sec₁ i₁) (2 * j.val) *
               spinVal (sectorState (2 * m) sec₁ i₁) ((2 * j.val + 1) % (2 * m)))
        else 0 := fun j => by
      simp only [Matrix.smul_apply, smul_eq_mul, twoSite_XX_apply (evenL_ne_evenR j)]
      by_cases hp : (i₁, sec₁) = (i₂, sec₂)
      · rw [if_pos hp, if_pos (congrArg e.symm hp)]
        rw [fullSectorEquiv_symm_apply, fullSectorEquiv_symm_apply]
        have hmod : (2 * j.val + 1) % (2 * m) = 2 * j.val + 1 := Nat.mod_eq_of_lt (by omega)
        simp only [evenL, evenR, hmod, spinB, spinVal]; rfl
      · rw [if_neg hp, if_neg (fun h => hp (e.symm.injective h)), mul_zero]
    have hodd : ∀ j : Fin m,
        (g • twoSite (oddL j) (oddR (by omega) j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
        if (i₁, sec₁) = (i₂, sec₂) then
          g * (spinVal (sectorState (2 * m) sec₁ i₁) (2 * j.val + 1) *
               spinVal (sectorState (2 * m) sec₁ i₁) ((2 * j.val + 1 + 1) % (2 * m)))
        else 0 := fun j => by
      simp only [Matrix.smul_apply, smul_eq_mul, twoSite_XX_apply (oddL_ne_oddR hm j)]
      by_cases hp : (i₁, sec₁) = (i₂, sec₂)
      · rw [if_pos hp, if_pos (congrArg e.symm hp)]
        rw [fullSectorEquiv_symm_apply, fullSectorEquiv_symm_apply]
        simp only [oddL, oddR, spinB, spinVal, show 2 * j.val + 2 = 2 * j.val + 1 + 1 by omega]; rfl
      · rw [if_neg hp, if_neg (fun h => hp (e.symm.injective h)), mul_zero]
    simp_rw [heven, hodd]
    by_cases hp : (i₁, sec₁) = (i₂, sec₂)
    · rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
      simp only [↓reduceIte, H_XX, Matrix.diagonal_apply]
      rw [hsum_even_odd (fun k => g * (spinVal (sectorState (2 * m) sec₁ i₁) k *
          spinVal (sectorState (2 * m) sec₁ i₁) ((k + 1) % (2 * m)))),
        ← Finset.mul_sum, Finset.sum_neg_distrib]
      ring
    · simp only [hp, ↓reduceIte, Finset.sum_const_zero, add_zero, H_XX, Matrix.diagonal_apply]
      by_cases hs : sec₁ = sec₂
      · subst hs; have hi : i₁ ≠ i₂ := fun h => hp (by rw [h]); simp [hi]
      · simp [hs]
  -- 3. Evaluate `ZZ` part of `A_even + A_odd`
  have hZZ : (∑ j : Fin m, (twoSite (evenL j) (evenR j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) +
      (∑ j : Fin m, ((if tw && decide (j.val = m - 1) then (-1 : ℝ) else 1) •
        twoSite (oddL j) (oddR (by omega) j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) =
      if sec₁ = sec₂ then (-1 : ℝ) * H_ZZ (2 * m) tw i₁ i₂ else 0 := by
    have heven : ∀ j : Fin m,
        (twoSite (evenL j) (evenR j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
        if sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) (2 * j.val) i₁ then
          if tw && decide (2 * j.val = 2 * m - 1) then (-1 : ℝ) else (1 : ℝ)
        else 0 := fun j => by
      rw [flipPair_eq_twoSite_ZZ (evenL_ne_evenR j)]
      have hne_last : ¬ (2 * j.val = 2 * m - 1) := by omega
      simp only [hne_last, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      have hmod : (2 * j.val + 1) % (2 * m) = 2 * j.val + 1 := Nat.mod_eq_of_lt (by omega)
      have hiff := sectorState_flipBond_iff (L := 2 * m) (by omega) sec₁ sec₂ i₁ i₂ (2 * j.val) (by omega)
      have hcond : (∀ r : Fin (2 * m), e.symm (i₂, sec₂) r =
          if r = evenL j ∨ r = evenR j then !(e.symm (i₁, sec₁) r) else e.symm (i₁, sec₁) r) ↔
          (sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) (2 * j.val) i₁) := by
        rw [← hiff]
        refine forall_congr' fun r => ?_
        rw [fullSectorEquiv_symm_apply, fullSectorEquiv_symm_apply]
        have heq1 : (r = evenL j) ↔ r.val = 2 * j.val := by
          constructor <;> intro h; · exact congrArg Fin.val h
          · exact Fin.ext h
        have heq2 : (r = evenR j) ↔ r.val = (2 * j.val + 1) % (2 * m) := by
          rw [hmod]; constructor <;> intro h; · exact congrArg Fin.val h
          · exact Fin.ext h
        simp [heq1, heq2]
      by_cases h : sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) (2 * j.val) i₁
      · rw [if_pos h, if_pos (hcond.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hcond.mp h'))]
    have hodd : ∀ j : Fin m,
        ((if tw && decide (j.val = m - 1) then (-1 : ℝ) else 1) •
          twoSite (oddL j) (oddR (by omega) j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
        if sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) (2 * j.val + 1) i₁ then
          if tw && decide (2 * j.val + 1 = 2 * m - 1) then (-1 : ℝ) else (1 : ℝ)
        else 0 := fun j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [flipPair_eq_twoSite_ZZ (oddL_ne_oddR hm j)]
      have hlast_iff : (j.val = m - 1) ↔ (2 * j.val + 1 = 2 * m - 1) := by omega
      have hiff := sectorState_flipBond_iff (L := 2 * m) (by omega) sec₁ sec₂ i₁ i₂ (2 * j.val + 1) (by omega)
      have hcond : (∀ r : Fin (2 * m), e.symm (i₂, sec₂) r =
          if r = oddL j ∨ r = oddR (by omega) j then !(e.symm (i₁, sec₁) r) else e.symm (i₁, sec₁) r) ↔
          (sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) (2 * j.val + 1) i₁) := by
        rw [← hiff]
        refine forall_congr' fun r => ?_
        rw [fullSectorEquiv_symm_apply, fullSectorEquiv_symm_apply]
        have heq1 : (r = oddL j) ↔ r.val = 2 * j.val + 1 := by
          constructor <;> intro h; · exact congrArg Fin.val h
          · exact Fin.ext h
        have heq2 : (r = oddR (by omega) j) ↔ r.val = (2 * j.val + 1 + 1) % (2 * m) := by
          simp only [oddR, show 2 * j.val + 2 = 2 * j.val + 1 + 1 by omega]
          constructor <;> intro h; · exact congrArg Fin.val h
          · exact Fin.ext h
        simp [heq1, heq2]
      by_cases h : sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) (2 * j.val + 1) i₁
      · rw [if_pos h, if_pos (hcond.mpr h), mul_one]
        simp [hlast_iff]
      · rw [if_neg h, if_neg (fun h' => h (hcond.mp h')), mul_zero]
    simp_rw [heven, hodd]
    rw [hsum_even_odd (fun k =>
      if sec₂ = sec₁ ∧ i₂ = flipBond (2 * m) k i₁ then
        if tw && decide (k = 2 * m - 1) then (-1 : ℝ) else (1 : ℝ)
      else 0)]
    by_cases hs : sec₁ = sec₂
    · subst hs
      simp only [↓reduceIte, true_and, H_ZZ, Matrix.of_apply, neg_mul, one_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> norm_num
    · have hs' : sec₂ ≠ sec₁ := Ne.symm hs
      simp [hs, hs']
  -- Combine `A_X + A_even + A_odd`
  have hAe_app : A_even m g (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
      (∑ j : Fin m, (twoSite (evenL j) (evenR j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) +
      (∑ j : Fin m, (g • twoSite (evenL j) (evenR j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) := by
    simp [A_even, Matrix.sum_apply, Finset.sum_add_distrib]
  have hAo_app : A_odd m (by omega) g tw (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) =
      (∑ j : Fin m, ((if tw && decide (j.val = m - 1) then (-1 : ℝ) else 1) •
        twoSite (oddL j) (oddR (by omega) j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) +
      (∑ j : Fin m, (g • twoSite (oddL j) (oddR (by omega) j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) := by
    simp only [A_odd, Matrix.sum_apply, Matrix.add_apply, Finset.sum_add_distrib]
  rw [hAe_app, hAo_app]
  have hcomb : A_X (2 * m) h (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)) +
      ((∑ j : Fin m, (twoSite (evenL j) (evenR j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) +
       (∑ j : Fin m, (g • twoSite (evenL j) (evenR j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)))) +
      ((∑ j : Fin m, ((if tw && decide (j.val = m - 1) then (-1 : ℝ) else 1) •
        twoSite (oddL j) (oddR (by omega) j) matZ1 matZ1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂))) +
       (∑ j : Fin m, (g • twoSite (oddL j) (oddR (by omega) j) matX1 matX1) (e.symm (i₁, sec₁)) (e.symm (i₂, sec₂)))) =
      (if sec₁ = sec₂ then (-h) * H_X (2 * m) sec₁ i₁ i₂ else 0) +
      (if sec₁ = sec₂ then (-1 : ℝ) * H_ZZ (2 * m) tw i₁ i₂ else 0) +
      (if sec₁ = sec₂ then (-g) * H_XX (2 * m) sec₁ i₁ i₂ else 0) := by
    rw [← hAX, ← hZZ, ← hXX]; ring
  rw [hcomb]
  by_cases hs : sec₁ = sec₂
  · subst hs
    simp only [↓reduceIte, H_ising, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · simp [hs]

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing commutes with `NormedSpace.exp` on finite real matrices. -/
private lemma exp_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (M : Matrix α α ℝ) :
    NormedSpace.exp (M.reindex e e) = (NormedSpace.exp M).reindex e e := by
  let φ : Matrix α α ℝ ≃ₐ[ℝ] Matrix β β ℝ := Matrix.reindexAlgEquiv ℝ ℝ e
  have hcont : Continuous φ := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous (fun X : Matrix α α ℝ => X (e.symm i) (e.symm j))
    exact (continuous_apply (e.symm j)).comp (continuous_apply (e.symm i))
  have hhas := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) M).map φ.toAddMonoidHom hcont
  have hcomp : (φ.toAddMonoidHom ∘ fun k => NormedSpace.expSeries ℝ (Matrix α α ℝ) k fun _ => M) =
      fun k => NormedSpace.expSeries ℝ (Matrix β β ℝ) k fun _ => φ M := by
    funext k
    change φ (NormedSpace.expSeries ℝ (Matrix α α ℝ) k fun _ => M) =
      NormedSpace.expSeries ℝ (Matrix β β ℝ) k fun _ => φ M
    rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq]
    simp [map_smul, map_pow]
  rw [hcomp] at hhas
  exact (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (φ M)).unique hhas

set_option backward.isDefEq.respectTransparency false in
/-- Exact traces of `exp(b • A_full)` and `P_full * exp(b • A_full)` in terms of `matZ`! -/
theorem trace_exp_Afull_eq_matZ {m : ℕ} (hm : 2 ≤ m) (b g h : ℝ) (tw : Bool) :
    let A := A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw
    Matrix.trace (NormedSpace.exp (b • A)) =
      matZ (H_ising (2 * m) g h tw false) (H_ising_isHermitian (2 * m) g h tw false) b +
      matZ (H_ising (2 * m) g h tw true) (H_ising_isHermitian (2 * m) g h tw true) b ∧
    Matrix.trace (P_full (2 * m) * NormedSpace.exp (b • A)) =
      matZ (H_ising (2 * m) g h tw false) (H_ising_isHermitian (2 * m) g h tw false) b -
      matZ (H_ising (2 * m) g h tw true) (H_ising_isHermitian (2 * m) g h tw true) b := by
  intro A
  let e := fullSectorEquiv m (by omega)
  have hre : (NormedSpace.exp (b • A)).reindex e e =
      Matrix.blockDiagonal (fun sec : Bool =>
        NormedSpace.exp ((-b) • H_ising (2 * m) g h tw sec)) := by
    rw [← exp_reindex e (b • A), reindex_Afull_eq_blockDiagonal hm b g h tw,
      Matrix.exp_blockDiagonal]
    congr 1; funext sec
    have heval := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ)
      (fun s : Bool => (-b) • H_ising (2 * m) g h tw s)).map
      (Pi.evalAddMonoidHom (fun _ : Bool => Matrix (Fin (2 ^ (2 * m - 1))) (Fin (2 ^ (2 * m - 1))) ℝ) sec)
      (continuous_apply sec)
    have hcomp : ((Pi.evalAddMonoidHom (fun _ : Bool => Matrix (Fin (2 ^ (2 * m - 1))) (Fin (2 ^ (2 * m - 1))) ℝ) sec) ∘
        fun k => NormedSpace.expSeries ℝ (Bool → Matrix (Fin (2 ^ (2 * m - 1))) (Fin (2 ^ (2 * m - 1))) ℝ) k
          fun _ => fun s => (-b) • H_ising (2 * m) g h tw s) =
        fun k => NormedSpace.expSeries ℝ (Matrix (Fin (2 ^ (2 * m - 1))) (Fin (2 ^ (2 * m - 1))) ℝ) k
          fun _ => (-b) • H_ising (2 * m) g h tw sec := by
      funext k
      change (NormedSpace.expSeries ℝ (Bool → Matrix (Fin (2 ^ (2 * m - 1))) (Fin (2 ^ (2 * m - 1))) ℝ) k
        fun _ => fun s => (-b) • H_ising (2 * m) g h tw s) sec = _
      rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq]
      simp
    rw [hcomp] at heval
    exact heval.unique (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ((-b) • H_ising (2 * m) g h tw sec))
  have hPre : (P_full (2 * m)).reindex e e =
      Matrix.blockDiagonal (fun sec : Bool =>
        (if sec then (-1 : ℝ) else 1) • (1 : Matrix (Fin (2 ^ (2 * m - 1))) (Fin (2 ^ (2 * m - 1))) ℝ)) := by
    rw [P_full_eq_diagonal]
    ext ⟨i₁, s₁⟩ ⟨i₂, s₂⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
      Matrix.blockDiagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hpar : tupleParity (e.symm (i₁, s₁)) = s₁ := by
      have hfn : ∀ k : Fin (2 * m), e.symm (i₁, s₁) k = (sectorState (2 * m) s₁ i₁).testBit k.val :=
        fullSectorEquiv_symm_apply (by omega) s₁ i₁
      rw [funext hfn]
      have hgen : ∀ (L r : ℕ) (hr : L = r + 1) (j : Fin (2 ^ (L - 1))),
          tupleParity (fun k : Fin L => (sectorState L s₁ j).testBit k.val) = s₁ := by
        intro L r hr; subst hr; intro j
        exact congrArg Prod.fst ((sectorEquiv r).right_inv (s₁, j))
      exact hgen (2 * m) (2 * m - 1) (by omega) i₁
    by_cases hs : s₁ = s₂
    · subst hs
      by_cases hi : i₁ = i₂
      · subst hi; simp [hpar]
      · have hne : e.symm (i₁, s₁) ≠ e.symm (i₂, s₁) := fun h => hi (Prod.mk.inj (e.symm.injective h)).1
        simp [hi, hne]
    · have hne : e.symm (i₁, s₁) ≠ e.symm (i₂, s₂) := fun h => hs (Prod.mk.inj (e.symm.injective h)).2
      simp [hs, hne]
  have htr_re : ∀ X : Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ,
      Matrix.trace X = Matrix.trace (X.reindex e e) := fun X => by
    simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact (Equiv.sum_comp e.symm (fun x => X x x)).symm
  constructor
  · rw [htr_re, hre, Matrix.trace_blockDiagonal, Fintype.sum_bool, add_comm,
      trace_exp_eq_matZ (hH := H_ising_isHermitian _ _ _ _ _),
      trace_exp_eq_matZ (hH := H_ising_isHermitian _ _ _ _ _)]
  · rw [htr_re]
    have hmul_re : (P_full (2 * m) * NormedSpace.exp (b • A)).reindex e e =
        (P_full (2 * m)).reindex e e * (NormedSpace.exp (b • A)).reindex e e := by
      exact (Matrix.reindexAlgEquiv ℝ ℝ e).map_mul (P_full (2 * m)) (NormedSpace.exp (b • A))
    rw [hmul_re, hPre, hre, ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal,
      Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, one_smul, neg_one_smul, Matrix.one_mul,
      Matrix.neg_mul, Matrix.trace_neg]
    rw [trace_exp_eq_matZ (hH := H_ising_isHermitian _ _ _ _ _),
      trace_exp_eq_matZ (hH := H_ising_isHermitian _ _ _ _ _)]
    ring

/-! ## Section 4: Exact Checkerboard Trotter Expansion & PSD Gram Contraction -/

/-- `M`-th power of a weighted sum of `kronVec` matrices expands into time histories `Fin M → ι`. -/
lemma pow_sum_kronVec {L : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (U : ι → Fin L → Matrix Bool Bool ℝ) :
    ∀ M : ℕ, (∑ x : ι, w x • kronVec (U x)) ^ M =
      ∑ xs : Fin M → ι, (∏ r : Fin M, w (xs r)) •
        kronVec (fun i : Fin L => matProd (fun r : Fin M => U (xs r) i))
  | 0 => by
    have h1 : (1 : Matrix (Fin L → Bool) (Fin L → Bool) ℝ) = kronVec (fun _ => 1) := (kronVec_one L).symm
    simp only [pow_zero, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    exact h1
  | M + 1 => by
    rw [pow_succ', pow_sum_kronVec w U M, Finset.sum_mul]
    simp_rw [Finset.mul_sum, smul_mul_smul_comm, kronVec_mul]
    rw [← Fintype.sum_prod_type']
    let e : ι × (Fin M → ι) ≃ (Fin (M + 1) → ι) :=
      { toFun := fun ⟨x, f⟩ => Fin.cons x f
        invFun := fun xs => (xs 0, fun r : Fin M => xs r.succ)
        left_inv := fun ⟨x, f⟩ => by ext <;> simp
        right_inv := fun xs => by
          funext r
          refine Fin.cases ?_ ?_ r <;> simp }
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun xs _ => ?_
    have he0 : (e.symm xs).1 = xs 0 := rfl
    have he1 : (e.symm xs).2 = fun r : Fin M => xs r.succ := rfl
    rw [he0, he1, Fin.prod_univ_succ]
    rfl

/-- Cyclic trace of a matrix power `Tr(A^m) = ∑ β : Fin m → ι, ∏ j : Fin m, A (β (prevCell j)) (β j)`. -/
lemma trace_pow_eq_sum_cycle {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    ∀ {m : ℕ} (hm : 1 ≤ m),
      Matrix.trace (A ^ m) = ∑ β : Fin m → ι, ∏ j : Fin m, A (β (prevCell (by omega) j)) (β j) := by
  -- Prove path-entry formula `(A ^ k) u v = ∑ mid : Fin (k - 1) → ι, ...` by induction
  have hpow_entry : ∀ (k : ℕ) (u v : ι),
      (A ^ (k + 1)) u v =
        ∑ p : Fin k → ι,
          (∏ r : Fin k, A (if h : r.val = 0 then u else p ⟨r.val - 1, by omega⟩) (p r)) *
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
      have hpull : ∀ x : ι,
          (∑ p : Fin k → ι,
            (∏ r : Fin k, A (if h : r.val = 0 then u else p ⟨r.val - 1, by omega⟩) (p r)) *
            A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) x) * A x v =
          ∑ p : Fin k → ι,
            ((∏ r : Fin k, A (if h : r.val = 0 then u else p ⟨r.val - 1, by omega⟩) (p r)) *
             A (if h : k = 0 then u else p ⟨k - 1, by omega⟩) x) * A x v := fun x => Finset.sum_mul _ _ _
      simp_rw [hpull]
      rw [← Fintype.sum_prod_type']
      let e : ι × (Fin k → ι) ≃ (Fin (k + 1) → ι) :=
        { toFun := fun ⟨x, p⟩ => Fin.snoc p x
          invFun := fun q => (q (Fin.last k), Fin.init q)
          left_inv := fun ⟨x, p⟩ => by ext <;> simp [Fin.snoc, Fin.init]
          right_inv := fun q => by
            funext r
            by_cases hr : r.val < k
            · have hr' : r = (⟨r.val, hr⟩ : Fin k).castSucc := Fin.ext rfl
              rw [hr']; simp [Fin.snoc_castSucc, Fin.init]
            · have hr' : r = Fin.last k := Fin.ext (by simp [Fin.last]; omega)
              rw [hr']; simp [Fin.snoc_last] }
      rw [← Equiv.sum_comp e.symm]
      refine Finset.sum_congr rfl fun q _ => ?_
      change ((∏ r : Fin k, A (if h : r.val = 0 then u else q ⟨r.val - 1, by omega⟩) (q r.castSucc)) *
          A (if h : k = 0 then u else q ⟨k - 1, by omega⟩) (q (Fin.last k))) * A (q (Fin.last k)) v = _
      rw [Fin.prod_univ_castSucc]
      congr 1
  intro m hm
  rcases Nat.exists_eq_add_of_le' hm with ⟨k, rfl⟩
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [hpow_entry k]
  rw [← Fintype.sum_prod_type']
  let e : ι × (Fin k → ι) ≃ (Fin (k + 1) → ι) :=
    { toFun := fun ⟨u, p⟩ => Fin.snoc p u
      invFun := fun β => (β (Fin.last k), Fin.init β)
      left_inv := fun ⟨u, p⟩ => by ext <;> simp [Fin.snoc, Fin.init]
      right_inv := fun β => by
        funext r
        by_cases hr : r.val < k
        · have hr' : r = (⟨r.val, hr⟩ : Fin k).castSucc := Fin.ext rfl
          rw [hr']; simp [Fin.snoc_castSucc, Fin.init]
        · have hr' : r = Fin.last k := Fin.ext (by simp [Fin.last]; omega)
          rw [hr']; simp [Fin.snoc_last] }
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun β _ => ?_
  change (∏ r : Fin k, A (if h : r.val = 0 then β (Fin.last k) else β ⟨r.val - 1, by omega⟩) (β r.castSucc)) *
      A (if h : k = 0 then β (Fin.last k) else β ⟨k - 1, by omega⟩) (β (Fin.last k)) =
    ∏ j : Fin (k + 1), A (β (prevCell (by omega) j)) (β j)
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    by_cases h0 : r.val = 0
    · rw [dif_pos h0]
      have hprev : prevCell (by omega) r.castSucc = Fin.last k := by
        ext; simp [prevCell, h0, Fin.last]
      rw [hprev]
    · rw [dif_neg h0]
      have hprev : prevCell (by omega) r.castSucc = ⟨r.val - 1, by omega⟩ := by
        ext; simp only [prevCell, Fin.val_castSucc]
        have : r.val + (k + 1) - 1 = (r.val - 1) + (k + 1) := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hprev]
  · by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceDIte]
      have hprev : prevCell (by omega) (Fin.last 0) = Fin.last 0 := by ext; simp [prevCell, Fin.last]
      rw [hprev]
    · rw [dif_neg hk0]
      have hprev : prevCell (by omega) (Fin.last k) = ⟨k - 1, by omega⟩ := by
        ext; simp only [prevCell, Fin.val_last]
        have : k + (k + 1) - 1 = (k - 1) + (k + 1) := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hprev]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Exact 1-slice Trotter operator `exp(τ A_X) * exp(τ A_even) * exp(τ A_odd)` expanded as a sum of `kronVec`! -/
lemma single_slice_trotter_eq {m : ℕ} (hm : 2 ≤ m) (τ g h : ℝ) (tw : Bool) :
    NormedSpace.exp (τ • A_X (2 * m) h) *
    NormedSpace.exp (τ • A_even m g) *
    NormedSpace.exp (τ • A_odd m (by omega) g tw) =
      ∑ p : (Fin m → Fin 4) × (Fin m → Fin 4),
        (twistSign tw (p.2 (lastCell (by omega))) *
          (∏ j : Fin m, bondCoeff τ g (p.1 j)) *
          (∏ j : Fin m, bondCoeff τ g (p.2 j))) •
        kronVec (fun i : Fin (2 * m) =>
          EX τ h * op4 (p.1 ⟨i.val / 2, by omega⟩) *
            op4 (if i.val % 2 = 0
                 then p.2 (prevCell (by omega) ⟨i.val / 2, by omega⟩)
                 else p.2 ⟨i.val / 2, by omega⟩)) := by
  -- 1. `exp(τ • A_X) = kronVec (fun _ => EX τ h)`
  have hEX : NormedSpace.exp (τ • A_X (2 * m) h) = kronVec (fun _ : Fin (2 * m) => EX τ h) := by
    have hdiag : τ • A_X (2 * m) h =
        Matrix.diagonal fun a : Fin (2 * m) → Bool => ∑ k : Fin (2 * m), τ * h * spinB (a k) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [A_X, Finset.mul_sum, mul_assoc]
      · simp [A_X, hab]
    rw [hdiag, Matrix.exp_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq, kronVec, Matrix.of_apply, EX]
      have hpi : ∀ (f : (Fin (2 * m) → Bool) → ℝ), NormedSpace.exp f a = Real.exp (f a) := fun f => by
        rw [Real.exp_eq_exp_ℝ]
        have heval := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) f).map
          (Pi.evalAddMonoidHom (fun _ => ℝ) a) (continuous_apply a)
        have hcomp : ((Pi.evalAddMonoidHom (fun _ => ℝ) a) ∘
            fun k => NormedSpace.expSeries ℝ ((Fin (2 * m) → Bool) → ℝ) k fun _ => f) =
            fun k => NormedSpace.expSeries ℝ ℝ k fun _ => f a := by
          funext k
          change (NormedSpace.expSeries ℝ ((Fin (2 * m) → Bool) → ℝ) k fun _ => f) a =
            NormedSpace.expSeries ℝ ℝ k fun _ => f a
          rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq]; simp
        rw [hcomp] at heval
        exact heval.unique (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (f a))
      rw [hpi, Real.exp_sum]
    · simp only [Matrix.diagonal_apply_ne _ hab, kronVec, Matrix.of_apply, EX]
      have hex : ∃ i : Fin (2 * m), a i ≠ b i := by
        by_contra hall; push Not at hall; exact hab (funext hall)
      rcases hex with ⟨i, hi⟩
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  -- 2. `exp(τ • A_even)` via `exp_finset_sum_of_commute` + `exp_bond_eq_sum4`
  have hEven : NormedSpace.exp (τ • A_even m g) =
      ∑ α : Fin m → Fin 4, (∏ j : Fin m, bondCoeff τ g (α j)) •
        kronVec (fun i : Fin (2 * m) => op4 (α ⟨i.val / 2, by omega⟩)) := by
    let B : Fin m → Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ := fun j =>
      τ • (twoSite (evenL j) (evenR j) matZ1 matZ1 + g • twoSite (evenL j) (evenR j) matX1 matX1)
    have hcomm : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
        Commute (B a) (B b) := fun a _ b _ => by
      by_cases hab : a = b
      · subst hab; exact Commute.refl _
      · have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
        have h1 : evenL a ≠ evenL b := fun h => hne (by have := congrArg Fin.val h; dsimp [evenL] at this; omega)
        have h2 : evenL a ≠ evenR b := fun h => by have := congrArg Fin.val h; dsimp [evenL, evenR] at this; omega
        have h3 : evenR a ≠ evenL b := fun h => by have := congrArg Fin.val h; dsimp [evenL, evenR] at this; omega
        have h4 : evenR a ≠ evenR b := fun h => hne (by have := congrArg Fin.val h; dsimp [evenR] at this; omega)
        dsimp [B]
        refine ((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).add_right
            ((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_right g)).add_left
          (((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_left g).add_right
            (((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_left g).smul_right g))
          |>.smul_left τ |>.smul_right τ
    have harg : τ • A_even m g = ∑ j : Fin m, B j := by
      simp [A_even, B, Finset.smul_sum]
    rw [harg, exp_finset_sum_of_commute Finset.univ B hcomm]
    -- Expand product of sums over `Fin m` into sum over `α : Fin m → Fin 4`
    have hexp_B : ∀ j : Fin m, NormedSpace.exp (B j) =
        ∑ c : Fin 4, bondCoeff τ g c • twoSite (evenL j) (evenR j) (op4 c) (op4 c) := fun j => by
      have h1 := exp_bond_eq_sum4 (evenL_ne_evenR j) τ g false
      simpa [B, twistSign] using h1
    -- General commuting noncommProd of sums of `twoSite` equals `∑ α, ...`
    have hprod_expand : ∀ (s : Finset (Fin m))
        (hc : Set.Pairwise (↑s) fun a b => Commute (NormedSpace.exp (B a)) (NormedSpace.exp (B b))),
        s.noncommProd (fun j => NormedSpace.exp (B j)) hc =
        ∑ α : Fin m → Fin 4,
          (if ∀ j, j ∉ s → α j = 0 then (∏ j ∈ s, bondCoeff τ g (α j)) else 0) •
          kronVec (fun i : Fin (2 * m) =>
            if ⟨i.val / 2, by omega⟩ ∈ s then op4 (α ⟨i.val / 2, by omega⟩) else 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        rw [Finset.noncommProd_empty, Finset.sum_eq_single (fun _ => (0 : Fin 4))]
        · simp [kronVec_one]
        · intro α _ hne
          have hex : ∃ j, α j ≠ 0 := by by_contra hall; push Not at hall; exact hne (funext hall)
          rcases hex with ⟨j, hj⟩
          simp only [Finset.notMem_empty, not_false_eq_true, forall_const]
          rw [if_neg (fun h => hj (h j)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      | insert a s ha ih =>
        intro hc
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
          ih (hc.mono (Finset.subset_insert a s)), hexp_B a, Finset.sum_mul]
        simp_rw [Finset.mul_sum, smul_mul_smul_comm]
        -- Combine `c : Fin 4` and `α` (zero outside `s`) into `α' = Function.update α a c`
        have hstep : ∀ (c : Fin 4) (α : Fin m → Fin 4),
            twoSite (evenL a) (evenR a) (op4 c) (op4 c) *
            kronVec (fun i : Fin (2 * m) =>
              if ⟨i.val / 2, by omega⟩ ∈ s then op4 (α ⟨i.val / 2, by omega⟩) else 1) =
            kronVec (fun i : Fin (2 * m) =>
              if ⟨i.val / 2, by omega⟩ ∈ insert a s
              then op4 (Function.update α a c ⟨i.val / 2, by omega⟩) else 1) := by
          intro c α
          unfold twoSite; rw [kronVec_mul]; congr 1; funext i
          by_cases hi : (⟨i.val / 2, by omega⟩ : Fin m) = a
          · have hcases : i = evenL a ∨ i = evenR a := by
              have hval : i.val / 2 = a.val := congrArg Fin.val hi
              by_cases hpar : i.val % 2 = 0
              · left; ext; dsimp [evenL]; omega
              · right; ext; dsimp [evenR]; omega
            rcases hcases with rfl | rfl
            · simp [hi, ha, Function.update_self]
            · simp [hi, ha, (evenL_ne_evenR a).symm, Function.update_self]
          · have hne1 : i ≠ evenL a := fun h => hi (by ext; rw [h]; dsimp [evenL]; omega)
            have hne2 : i ≠ evenR a := fun h => hi (by ext; rw [h]; dsimp [evenR]; omega)
            by_cases hmem : (⟨i.val / 2, by omega⟩ : Fin m) ∈ s
            · simp [hne1, hne2, hi, hmem]
            · simp [hne1, hne2, hi, hmem]
        simp_rw [hstep]
        -- Reindex `Fin 4 × {α | α a = 0}` ↔ `Fin m → Fin 4`
        rw [Finset.sum_comm]
        have hreidx :
            ∑ α : Fin m → Fin 4, ∑ c : Fin 4,
              (bondCoeff τ g c * if ∀ j, j ∉ s → α j = 0 then ∏ j ∈ s, bondCoeff τ g (α j) else 0) •
              kronVec (fun i : Fin (2 * m) =>
                if ⟨i.val / 2, by omega⟩ ∈ insert a s
                then op4 (Function.update α a c ⟨i.val / 2, by omega⟩) else 1) =
            ∑ γ : Fin m → Fin 4,
              (if ∀ j, j ∉ insert a s → γ j = 0 then ∏ j ∈ insert a s, bondCoeff τ g (γ j) else 0) •
              kronVec (fun i : Fin (2 * m) =>
                if ⟨i.val / 2, by omega⟩ ∈ insert a s then op4 (γ ⟨i.val / 2, by omega⟩) else 1) := by
          -- Collapse inner sum over `c` and outer sum over `α` via `γ = update α a c`
          have hzero : ∀ α : Fin m → Fin 4, α a ≠ 0 →
              ∑ c : Fin 4,
                (bondCoeff τ g c * if ∀ j, j ∉ s → α j = 0 then ∏ j ∈ s, bondCoeff τ g (α j) else 0) •
                kronVec (fun i : Fin (2 * m) =>
                  if ⟨i.val / 2, by omega⟩ ∈ insert a s
                  then op4 (Function.update α a c ⟨i.val / 2, by omega⟩) else 1) = 0 := fun α hne => by
            have hnot : ¬ (∀ j, j ∉ s → α j = 0) := fun h => hne (h a ha)
            simp [hnot]
          rw [← Finset.sum_filter_of_ne (p := fun α : Fin m → Fin 4 => α a = 0) (by
            intro α _ hne; by_contra h0; exact hne (hzero α h0))]
          rw [Finset.sum_sigma']
          refine Finset.sum_nbij (fun x => Function.update x.1 a x.2) ?_ ?_ ?_ ?_
          · intro x _; exact Finset.mem_univ _
          · intro x hx y hy hEq
            have hxa : x.1 a = 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
            have hya : y.1 a = 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).1).2
            have h2 : x.2 = y.2 := by
              have := congrFun hEq a; simpa using this
            have h1 : x.1 = y.1 := by
              funext j
              by_cases hja : j = a
              · subst hja; rw [hxa, hya]
              · have := congrFun hEq j; simpa [hja] using this
            exact Sigma.ext h1 (heq_of_eq h2)
          · intro γ _
            refine ⟨⟨Function.update γ a 0, γ a⟩, ?_, ?_⟩
            · simp
            · funext j; by_cases hja : j = a <;> simp [hja]
          · intro x hx
            have hxa : x.1 a = 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
            have hiff : (∀ j, j ∉ s → x.1 j = 0) ↔ (∀ j, j ∉ insert a s → Function.update x.1 a x.2 j = 0) := by
              constructor
              · intro h j hj
                have hja : j ≠ a := fun heq => hj (heq ▸ Finset.mem_insert_self a s)
                have hjs : j ∉ s := fun hmem => hj (Finset.mem_insert_of_mem hmem)
                simp [hja, h j hjs]
              · intro h j hjs
                by_cases hja : j = a
                · subst hja; exact hxa
                · have hj : j ∉ insert a s := by simp [hja, hjs]
                  have := h j hj; simpa [hja] using this
            congr 1
            by_cases hcond : ∀ j, j ∉ s → x.1 j = 0
            · rw [if_pos hcond, if_pos (hiff.mp hcond), Finset.prod_insert ha, Function.update_self]
              congr 1
              refine Finset.prod_congr rfl fun j hj => ?_
              have hja : j ≠ a := fun heq => ha (heq ▸ hj)
              simp [hja]
            · rw [if_neg hcond, if_neg (fun h => hcond (hiff.mpr h)), mul_zero]
        exact hreidx
    simpa using hprod_expand Finset.univ (fun a ha b hb _ => commute_exp_of_commute (hcomm a ha b hb))
  -- 3. `exp(τ • A_odd)` via the exact same argument!
  have hOdd : NormedSpace.exp (τ • A_odd m (by omega) g tw) =
      ∑ β : Fin m → Fin 4,
        (twistSign tw (β (lastCell (by omega))) * ∏ j : Fin m, bondCoeff τ g (β j)) •
        kronVec (fun i : Fin (2 * m) =>
          op4 (if i.val % 2 = 0
               then β (prevCell (by omega) ⟨i.val / 2, by omega⟩)
               else β ⟨i.val / 2, by omega⟩)) := by
    let B : Fin m → Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ := fun j =>
      τ • ((if tw && decide (j.val = m - 1) then (-1 : ℝ) else 1) •
        twoSite (oddL j) (oddR (by omega) j) matZ1 matZ1 +
        g • twoSite (oddL j) (oddR (by omega) j) matX1 matX1)
    have hsite_owner : ∀ i : Fin (2 * m),
        let o : Fin m := if i.val % 2 = 0
          then prevCell (by omega) ⟨i.val / 2, by omega⟩
          else ⟨i.val / 2, by omega⟩
        (i = oddL o ∨ i = oddR (by omega) o) ∧
        (∀ j : Fin m, j ≠ o → i ≠ oddL j ∧ i ≠ oddR (by omega) j) := by
      intro i o
      have h1 : i = oddL o ∨ i = oddR (by omega) o := by
        by_cases hpar : i.val % 2 = 0
        · right; ext
          simp only [o, hpar, ↓reduceIte, oddR, prevCell]
          by_cases hi0 : i.val = 0
          · have hmod : (0 / 2 + m - 1) % m = m - 1 := by
              rw [Nat.zero_div, zero_add, Nat.mod_eq_of_lt (by omega)]
            rw [hi0, hmod, show 2 * (m - 1) + 2 = 2 * m by omega, Nat.mod_self]
          · have hmod : (i.val / 2 + m - 1) % m = i.val / 2 - 1 := by
              have heq : i.val / 2 + m - 1 = (i.val / 2 - 1) + m := by omega
              rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hmod, show 2 * (i.val / 2 - 1) + 2 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
        · left; ext; simp only [o, hpar, ↓reduceIte, oddL]; omega
      refine ⟨h1, fun j hjo => ?_⟩
      constructor
      · intro h
        have hv : i.val = 2 * j.val + 1 := congrArg Fin.val h
        have hpar : ¬ (i.val % 2 = 0) := by omega
        apply hjo; ext; simp only [o, hpar, ↓reduceIte]; omega
      · intro h
        have hv : i.val = (2 * j.val + 2) % (2 * m) := congrArg Fin.val h
        have hpar : i.val % 2 = 0 := by
          by_cases hlt : 2 * j.val + 2 < 2 * m
          · rw [Nat.mod_eq_of_lt hlt] at hv; omega
          · have : 2 * j.val + 2 = 2 * m := by omega
            rw [this, Nat.mod_self] at hv; omega
        apply hjo; ext; simp only [o, hpar, ↓reduceIte, prevCell]
        by_cases hlt : 2 * j.val + 2 < 2 * m
        · rw [Nat.mod_eq_of_lt hlt] at hv
          have heq : i.val / 2 + m - 1 = j.val + m := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
        · have hjlast : j.val = m - 1 := by omega
          have : 2 * j.val + 2 = 2 * m := by omega
          rw [this, Nat.mod_self] at hv
          rw [hv, Nat.zero_div, zero_add, Nat.mod_eq_of_lt (by omega), hjlast]
    have hcomm : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
        Commute (B a) (B b) := fun a _ b _ => by
      by_cases hab : a = b
      · subst hab; exact Commute.refl _
      · have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
        have h1 : oddL a ≠ oddL b := fun h => hne (by have := congrArg Fin.val h; dsimp [oddL] at this; omega)
        have h2 : oddL a ≠ oddR (by omega) b := fun h => by
          have hv := congrArg Fin.val h; dsimp [oddL, oddR] at hv
          by_cases hlt : 2 * b.val + 2 < 2 * m
          · rw [Nat.mod_eq_of_lt hlt] at hv; omega
          · have heq_b : 2 * b.val + 2 = 2 * m := by omega
            rw [heq_b, Nat.mod_self] at hv; omega
        have h3 : oddR (by omega) a ≠ oddL b := fun h => by
          have hv := congrArg Fin.val h; dsimp [oddL, oddR] at hv
          by_cases hlt : 2 * a.val + 2 < 2 * m
          · rw [Nat.mod_eq_of_lt hlt] at hv; omega
          · have heq_a : 2 * a.val + 2 = 2 * m := by omega
            rw [heq_a, Nat.mod_self] at hv; omega
        have h4 : oddR (by omega) a ≠ oddR (by omega) b := fun h => by
          have hv := congrArg Fin.val h; dsimp [oddR] at hv
          by_cases ha' : 2 * a.val + 2 < 2 * m <;> by_cases hb' : 2 * b.val + 2 < 2 * m
          · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hv; omega
          · have heq_b : 2 * b.val + 2 = 2 * m := by omega
            rw [Nat.mod_eq_of_lt ha', heq_b, Nat.mod_self] at hv; omega
          · have heq_a : 2 * a.val + 2 = 2 * m := by omega
            rw [heq_a, Nat.mod_self, Nat.mod_eq_of_lt hb'] at hv; omega
          · omega
        dsimp [B]
        refine (((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_left _).smul_right _ |>.add_right
            (((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_left _).smul_right g)).add_left
          ((((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_left g).smul_right _).add_right
            (((twoSite_comm_disjoint h1 h2 h3 h4 _ _ _ _).smul_left g).smul_right g))
          |>.smul_left τ |>.smul_right τ
    have harg : τ • A_odd m (by omega) g tw = ∑ j : Fin m, B j := by
      simp [A_odd, B, Finset.smul_sum]
    rw [harg, exp_finset_sum_of_commute Finset.univ B hcomm]
    let wOdd : Fin m → Fin 4 → ℝ := fun j c =>
      twistSign (tw && decide (j.val = m - 1)) c * bondCoeff τ g c
    have hexp_B : ∀ j : Fin m, NormedSpace.exp (B j) =
        ∑ c : Fin 4, wOdd j c • twoSite (oddL j) (oddR (by omega) j) (op4 c) (op4 c) := fun j =>
      exp_bond_eq_sum4 (oddL_ne_oddR hm j) τ g (tw && decide (j.val = m - 1))
    let owner : Fin (2 * m) → Fin m := fun i =>
      if i.val % 2 = 0 then prevCell (by omega) ⟨i.val / 2, by omega⟩ else ⟨i.val / 2, by omega⟩
    have hprod_expand : ∀ (s : Finset (Fin m))
        (hc : Set.Pairwise (↑s) fun a b => Commute (NormedSpace.exp (B a)) (NormedSpace.exp (B b))),
        s.noncommProd (fun j => NormedSpace.exp (B j)) hc =
        ∑ β : Fin m → Fin 4,
          (if ∀ j, j ∉ s → β j = 0 then (∏ j ∈ s, wOdd j (β j)) else 0) •
          kronVec (fun i : Fin (2 * m) => if owner i ∈ s then op4 (β (owner i)) else 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        rw [Finset.noncommProd_empty, Finset.sum_eq_single (fun _ => (0 : Fin 4))]
        · simp [kronVec_one]
        · intro β _ hne
          have hex : ∃ j, β j ≠ 0 := by by_contra hall; push Not at hall; exact hne (funext hall)
          rcases hex with ⟨j, hj⟩
          simp only [Finset.notMem_empty, not_false_eq_true, forall_const]
          rw [if_neg (fun h => hj (h j)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      | insert a s ha ih =>
        intro hc
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
          ih (hc.mono (Finset.subset_insert a s)), hexp_B a, Finset.sum_mul]
        simp_rw [Finset.mul_sum, smul_mul_smul_comm]
        have hstep : ∀ (c : Fin 4) (β : Fin m → Fin 4),
            twoSite (oddL a) (oddR (by omega) a) (op4 c) (op4 c) *
            kronVec (fun i : Fin (2 * m) => if owner i ∈ s then op4 (β (owner i)) else 1) =
            kronVec (fun i : Fin (2 * m) =>
              if owner i ∈ insert a s then op4 (Function.update β a c (owner i)) else 1) := by
          intro c β
          unfold twoSite; rw [kronVec_mul]; congr 1; funext i
          by_cases hi : owner i = a
          · have hcases := (hsite_owner i).1
            rw [show (if i.val % 2 = 0 then prevCell (by omega) ⟨i.val / 2, by omega⟩
              else ⟨i.val / 2, by omega⟩) = owner i from rfl, hi] at hcases
            rcases hcases with rfl | rfl
            · simp [hi, ha, Function.update_self]
            · simp [hi, ha, (oddL_ne_oddR hm a).symm, Function.update_self]
          · have hne := (hsite_owner i).2 a (Ne.symm hi)
            by_cases hmem : owner i ∈ s
            · simp [hne.1, hne.2, hi, hmem]
            · simp [hne.1, hne.2, hi, hmem]
        simp_rw [hstep]
        rw [Finset.sum_comm]
        have hzero : ∀ β : Fin m → Fin 4, β a ≠ 0 →
            ∑ c : Fin 4,
              (wOdd a c * if ∀ j, j ∉ s → β j = 0 then ∏ j ∈ s, wOdd j (β j) else 0) •
              kronVec (fun i : Fin (2 * m) =>
                if owner i ∈ insert a s then op4 (Function.update β a c (owner i)) else 1) = 0 := fun β hne => by
          have hnot : ¬ (∀ j, j ∉ s → β j = 0) := fun h => hne (h a ha)
          simp [hnot]
        rw [← Finset.sum_filter_of_ne (p := fun β : Fin m → Fin 4 => β a = 0) (by
          intro β _ hne; by_contra h0; exact hne (hzero β h0))]
        rw [Finset.sum_sigma']
        refine Finset.sum_nbij (fun x => Function.update x.1 a x.2) ?_ ?_ ?_ ?_
        · intro x _; exact Finset.mem_univ _
        · intro x hx y hy hEq
          have hxa : x.1 a = 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
          have hya : y.1 a = 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).1).2
          have h2 : x.2 = y.2 := by have := congrFun hEq a; simpa using this
          have h1 : x.1 = y.1 := by
            funext j; by_cases hja : j = a
            · subst hja; rw [hxa, hya]
            · have := congrFun hEq j; simpa [hja] using this
          exact Sigma.ext h1 (heq_of_eq h2)
        · intro γ _
          refine ⟨⟨Function.update γ a 0, γ a⟩, by simp, ?_⟩
          funext j; by_cases hja : j = a <;> simp [hja]
        · intro x hx
          have hxa : x.1 a = 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
          have hiff : (∀ j, j ∉ s → x.1 j = 0) ↔
              (∀ j, j ∉ insert a s → Function.update x.1 a x.2 j = 0) := by
            constructor
            · intro h j hj
              have hja : j ≠ a := fun heq => hj (heq ▸ Finset.mem_insert_self a s)
              have hjs : j ∉ s := fun hmem => hj (Finset.mem_insert_of_mem hmem)
              simp [hja, h j hjs]
            · intro h j hjs
              by_cases hja : j = a
              · subst hja; exact hxa
              · have hj : j ∉ insert a s := by simp [hja, hjs]
                have := h j hj; simpa [hja] using this
          congr 1
          by_cases hcond : ∀ j, j ∉ s → x.1 j = 0
          · rw [if_pos hcond, if_pos (hiff.mp hcond), Finset.prod_insert ha, Function.update_self]
            congr 1
            refine Finset.prod_congr rfl fun j hj => ?_
            have hja : j ≠ a := fun heq => ha (heq ▸ hj)
            simp [hja]
          · rw [if_neg hcond, if_neg (fun h => hcond (hiff.mpr h)), mul_zero]
    rw [hprod_expand Finset.univ (fun a ha b hb _ => commute_exp_of_commute (hcomm a ha b hb))]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true, ↓reduceIte]
    congr 1
    · dsimp [wOdd]
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single (lastCell (by omega))]
      · have hv : (lastCell (m := m) (by omega)).val = m - 1 := rfl
        simp [hv]
      · intro j _ hne
        have hv : j.val ≠ m - 1 := fun h => hne (Fin.ext (by simpa [lastCell] using h))
        simp [hv, twistSign]
      · intro h; exact absurd (Finset.mem_univ _) h
    · congr 1; funext i; dsimp [owner]; split_ifs <;> rfl
  -- 4. Multiply `hEX * hEven * hOdd`
  rw [hEX, hEven, hOdd]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    Finset.smul_sum, smul_smul, kronVec_mul]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
  congr 1
  ring

/-! ## Section 5: PSD Transfer Matrices `(V₀, V₁)` and Exact Finite-`M` Trace Identity -/

/-- Product of bond weights along a `Fin M → Fin 4` time history. -/
noncomputable def cProd (τ g : ℝ) {M : ℕ} (α : Fin M → Fin 4) : ℝ :=
  ∏ r : Fin M, bondCoeff τ g (α r)

lemma cProd_nonneg {τ g : ℝ} (hτ : 0 ≤ τ) (hg : 0 ≤ g) {M : ℕ} (α : Fin M → Fin 4) :
    0 ≤ cProd τ g α :=
  Finset.prod_nonneg fun r _ => bondCoeff_nonneg hτ hg (α r)

/-- Raw checkerboard vertex matrix `W(Q)(α, β) = √(c(α) c(β)) * Tr(Q * sliceProd α β)`. -/
noncomputable def rawVertex (g h b : ℝ) (M : ℕ) (Q : Matrix Bool Bool ℝ) :
    Matrix (Fin M → Fin 4) (Fin M → Fin 4) ℝ :=
  Matrix.of fun α β =>
    let τ := b / (M : ℝ)
    Real.sqrt (cProd τ g α * cProd τ g β) * Matrix.trace (Q * sliceProd τ h α β)

/-- Parity-projected transfer factor `V_raw(Q)(β, α) = 1_{flipParity β = false} * rawVertex(α, β)`. -/
noncomputable def projFactor (g h b : ℝ) (M : ℕ) (Q : Matrix Bool Bool ℝ) :
    Matrix (Fin M → Fin 4) (Fin M → Fin 4) ℝ :=
  Matrix.of fun β α =>
    if flipParity β then 0 else rawVertex g h b M Q α β

set_option maxHeartbeats 800000 in
/-- Exact finite-`M` trace identity for both `Q = 1` (`V₀`) and `Q = matX1` (`V₁`)! -/
theorem finite_M_trace_identity {m M : ℕ} (hm : 2 ≤ m) (hM : 1 ≤ M)
    {g h b : ℝ} (hg : 0 ≤ g) (hb : 0 < b)
    (Q : Matrix Bool Bool ℝ) (hQdiag : ∀ a b, a ≠ b → Q a b = 0) :
    let τ := b / (M : ℝ)
    let T : Bool → Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ := fun tw =>
      (NormedSpace.exp (τ • A_X (2 * m) h) *
       NormedSpace.exp (τ • A_even m g) *
       NormedSpace.exp (τ • A_odd m (by omega) g tw)) ^ M
    let V := projFactor g h b M Q
    (Matrix.trace (kronVec (fun _ : Fin (2 * m) => Q) * T false) +
     Matrix.trace (kronVec (fun _ : Fin (2 * m) => Q) * T true)) / 2 =
      Matrix.trace ((V * Vᵀ) ^ m) := by
  intro τ T V
  have hτ_nn : 0 ≤ τ := div_nonneg hb.le (by positivity)
  let W := rawVertex g h b M Q
  -- Step 1: Expand `Tr(kronVec Q * T tw)` using `single_slice_trotter_eq` and `pow_sum_kronVec`
  have hT_trace : ∀ tw : Bool,
      Matrix.trace (kronVec (fun _ : Fin (2 * m) => Q) * T tw) =
      ∑ β : Fin m → (Fin M → Fin 4),
        (if tw then (if flipParity (β (lastCell (by omega))) then (-1 : ℝ) else 1) else 1) *
        ∏ j : Fin m, (Wᵀ * W) (β (prevCell (by omega) j)) (β j) := by
    intro tw
    dsimp [T]
    rw [single_slice_trotter_eq hm τ g h tw, pow_sum_kronVec]
    rw [Finset.mul_sum, Matrix.trace_sum]
    simp_rw [Matrix.mul_smul, kronVec_mul, Matrix.trace_smul, smul_eq_mul, trace_kronVec]
    -- Reindex `xs : Fin M → (Fin m → Fin 4) × (Fin m → Fin 4)` to `(α, β) : (Fin m → Fin M → Fin 4) × (Fin m → Fin M → Fin 4)`
    let eIdx : (Fin M → (Fin m → Fin 4) × (Fin m → Fin 4)) ≃
        (Fin m → Fin M → Fin 4) × (Fin m → Fin M → Fin 4) :=
      { toFun := fun xs => (fun j r => (xs r).1 j, fun j r => (xs r).2 j)
        invFun := fun ⟨α, β⟩ r => (fun j => α j r, fun j => β j r)
        left_inv := fun _ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [← Equiv.sum_comp eIdx.symm, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun β _ => ?_
    -- Pull twist sign out of sum over `α`, then split `∏ i : Fin (2*m)` into `∏ j : Fin m`
    have hpull : ∀ α : Fin m → Fin M → Fin 4,
        (∏ r : Fin M,
          twistSign tw (β (lastCell (by omega)) r) *
          (∏ j : Fin m, bondCoeff τ g (α j r)) *
          (∏ j : Fin m, bondCoeff τ g (β j r))) *
        (∏ i : Fin (2 * m), Matrix.trace (Q * matProd (fun r : Fin M =>
          EX τ h * op4 (α ⟨i.val / 2, by omega⟩ r) *
            op4 (if i.val % 2 = 0
                 then β (prevCell (by omega) ⟨i.val / 2, by omega⟩) r
                 else β ⟨i.val / 2, by omega⟩ r)))) =
        (if tw then (if flipParity (β (lastCell (by omega))) then (-1 : ℝ) else 1) else 1) *
        ∏ j : Fin m, (W (α j) (β (prevCell (by omega) j)) * W (α j) (β j)) := by
      intro α
      -- Factor the `r`-product on the LHS only
      conv_lhs => simp only [Finset.prod_mul_distrib]
      have htw_prod : (∏ r : Fin M, twistSign tw (β (lastCell (by omega)) r)) =
          if tw then (if flipParity (β (lastCell (by omega))) then (-1 : ℝ) else 1) else 1 := by
        cases tw
        · simp [twistSign]
        · simpa using prod_twistSign_true (β (lastCell (by omega)))
      rw [htw_prod]
      -- Swap `∏ r ∏ j` to `∏ j ∏ r`
      have hswapA : (∏ r : Fin M, ∏ j : Fin m, bondCoeff τ g (α j r)) = ∏ j : Fin m, cProd τ g (α j) :=
        Finset.prod_comm
      have hswapB : (∏ r : Fin M, ∏ j : Fin m, bondCoeff τ g (β j r)) = ∏ j : Fin m, cProd τ g (β j) :=
        Finset.prod_comm
      rw [hswapA, hswapB]
      -- Split `∏ i : Fin (2*m)` into `∏ j : Fin m, (site 2j) * (site 2j+1)`
      have h2m_prod : ∀ F : Fin (2 * m) → ℝ,
          (∏ i : Fin (2 * m), F i) = ∏ j : Fin m, F (evenL j) * F (evenR j) := fun F => by
        let e2 : Fin m × Fin 2 ≃ Fin (2 * m) :=
          { toFun := fun ⟨j, c⟩ => ⟨2 * j.val + c.val, by omega⟩
            invFun := fun i => (⟨i.val / 2, by omega⟩, ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩)
            left_inv := fun ⟨j, c⟩ => by ext <;> simp <;> omega
            right_inv := fun i => by ext; simp; omega }
        rw [← Equiv.prod_comp e2, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Fin.prod_univ_two]; rfl
      rw [h2m_prod]
      -- Cyclic shift of `∏ j, √(cProd (β j))` equals `∏ j, √(cProd (β (prevCell j)))`
      have hprev_bij : Function.Bijective (prevCell (m := m) (by omega)) := by
        refine ⟨?_, ?_⟩
        · intro j₁ j₂ h
          have hv : (j₁.val + m - 1) % m = (j₂.val + m - 1) % m := congrArg Fin.val h
          have hj1 : j₁.val < m := j₁.isLt
          have hj2 : j₂.val < m := j₂.isLt
          ext
          by_cases h1 : j₁.val = 0 <;> by_cases h2 : j₂.val = 0
          · omega
          · rw [h1, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)] at hv
            have heq2 : j₂.val + m - 1 = (j₂.val - 1) + m := by omega
            rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j₂.val - 1 < m)] at hv; omega
          · rw [h2, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)] at hv
            have heq1 : j₁.val + m - 1 = (j₁.val - 1) + m := by omega
            rw [heq1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j₁.val - 1 < m)] at hv; omega
          · have e1 : j₁.val + m - 1 = (j₁.val - 1) + m := by omega
            have e2 : j₂.val + m - 1 = (j₂.val - 1) + m := by omega
            rw [e1, e2, Nat.add_mod_right, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega : j₁.val - 1 < m), Nat.mod_eq_of_lt (by omega : j₂.val - 1 < m)] at hv; omega
        · intro k
          refine ⟨⟨(k.val + 1) % m, Nat.mod_lt _ (by omega)⟩, ?_⟩
          ext; simp only [prevCell]
          by_cases hlt : k.val + 1 < m
          · rw [Nat.mod_eq_of_lt hlt, show k.val + 1 + m - 1 = k.val + m by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
          · have hk : k.val = m - 1 := by omega
            rw [show k.val + 1 = m by omega, Nat.mod_self, zero_add,
              Nat.mod_eq_of_lt (by omega : m - 1 < m), hk]
      have hshift_sqrt : (∏ j : Fin m, Real.sqrt (cProd τ g (β (prevCell (by omega) j)))) =
          ∏ j : Fin m, Real.sqrt (cProd τ g (β j)) :=
        Equiv.prod_comp (Equiv.ofBijective _ hprev_bij) (fun j => Real.sqrt (cProd τ g (β j)))
      have hsqA : (∏ j : Fin m, cProd τ g (α j)) =
          (∏ j : Fin m, Real.sqrt (cProd τ g (α j))) * (∏ j : Fin m, Real.sqrt (cProd τ g (α j))) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun j _ => (Real.mul_self_sqrt (cProd_nonneg hτ_nn hg (α j))).symm
      have hsqB : (∏ j : Fin m, cProd τ g (β j)) =
          (∏ j : Fin m, Real.sqrt (cProd τ g (β (prevCell (by omega) j)))) *
          (∏ j : Fin m, Real.sqrt (cProd τ g (β j))) := by
        rw [hshift_sqrt, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun j _ => (Real.mul_self_sqrt (cProd_nonneg hτ_nn hg (β j))).symm
      rw [hsqA, hsqB]
      simp only [mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      have heL_div : (⟨(evenL j).val / 2, by omega⟩ : Fin m) = j := by ext; simp [evenL]
      have heR_div : (⟨(evenR j).val / 2, by omega⟩ : Fin m) = j := by ext; simp [evenR]; omega
      have heL_mod : (evenL j).val % 2 = 0 := by simp [evenL]
      have heR_mod : (evenR j).val % 2 ≠ 0 := by simp [evenR]
      dsimp [W, rawVertex, sliceProd, τ]
      rw [Real.sqrt_mul (cProd_nonneg hτ_nn hg (α j)), Real.sqrt_mul (cProd_nonneg hτ_nn hg (α j))]
      simp only [heL_div, heR_div, heL_mod, heR_mod, ↓reduceIte, Matrix.mul_assoc]
      ring
    have hpull_symm : ∀ x : Fin m → Fin M → Fin 4,
        (∏ r : Fin M,
          (twistSign tw ((eIdx.symm (x, β) r).2 (lastCell (by omega))) *
            ∏ j : Fin m, bondCoeff τ g ((eIdx.symm (x, β) r).1 j)) *
          ∏ j : Fin m, bondCoeff τ g ((eIdx.symm (x, β) r).2 j)) *
        (∏ i : Fin (2 * m), Matrix.trace (Q * matProd fun r : Fin M =>
          EX τ h * op4 ((eIdx.symm (x, β) r).1 ⟨i.val / 2, by omega⟩) *
            op4 (if i.val % 2 = 0
                 then (eIdx.symm (x, β) r).2 (prevCell (by omega) ⟨i.val / 2, by omega⟩)
                 else (eIdx.symm (x, β) r).2 ⟨i.val / 2, by omega⟩))) =
        (if tw then (if flipParity (β (lastCell (by omega))) then (-1 : ℝ) else 1) else 1) *
        ∏ j : Fin m, (W (x j) (β (prevCell (by omega) j)) * W (x j) (β j)) := fun x => hpull x
    rw [Finset.sum_congr rfl fun x _ => hpull_symm x, ← Finset.mul_sum]
    congr 1
    have hWTW : ∏ j : Fin m, (Wᵀ * W) (β (prevCell (by omega) j)) (β j) =
        ∏ j : Fin m, ∑ a : Fin M → Fin 4, W a (β (prevCell (by omega) j)) * W a (β j) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Matrix.mul_apply]; rfl
    rw [hWTW, Fintype.prod_sum]
  -- Step 2: Average `tw = false` and `tw = true`
  rw [hT_trace false, hT_trace true, ← Finset.sum_add_distrib, Finset.sum_div]
  rw [trace_pow_eq_sum_cycle (V * Vᵀ) (by omega)]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  have havg : ((1 : ℝ) * (∏ j : Fin m, (Wᵀ * W) (β (prevCell (by omega) j)) (β j)) +
      (if flipParity (β (lastCell (by omega))) then (-1 : ℝ) else 1) *
      (∏ j : Fin m, (Wᵀ * W) (β (prevCell (by omega) j)) (β j))) / 2 =
      (if flipParity (β (lastCell (by omega))) then (0 : ℝ) else 1) *
      (∏ j : Fin m, (Wᵀ * W) (β (prevCell (by omega) j)) (β j)) := by
    cases flipParity (β (lastCell (by omega))) <;> simp <;> ring
  rw [havg]
  have hW_block : ∀ a c : Fin M → Fin 4, flipParity a ≠ flipParity c → W a c = 0 := fun a c hne => by
    dsimp [W, rawVertex]
    rw [trace_sliceProd_eq_zero τ h Q hQdiag hne, mul_zero]
  have hWTW_block : ∀ c₁ c₂ : Fin M → Fin 4, flipParity c₁ ≠ flipParity c₂ →
      (Wᵀ * W) c₁ c₂ = 0 := fun c₁ c₂ hne => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : flipParity a = flipParity c₁
    · rw [hW_block a c₂ (ha ▸ hne), mul_zero]
    · rw [hW_block a c₁ ha, zero_mul]
  have hVVT_eq : ∀ c₁ c₂ : Fin M → Fin 4,
      (V * Vᵀ) c₁ c₂ = if !flipParity c₁ ∧ !flipParity c₂ then (Wᵀ * W) c₁ c₂ else 0 := fun c₁ c₂ => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, V, projFactor, Matrix.of_apply]
    cases flipParity c₁ <;> cases flipParity c₂ <;> simp <;> rfl
  by_cases hall_even : ∀ j : Fin m, flipParity (β j) = false
  · rw [hall_even (lastCell (by omega))]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hVVT_eq, hall_even (prevCell (by omega) j), hall_even j]
    simp
  · push Not at hall_even
    rcases hall_even with ⟨j₀, hj₀⟩
    have hj₀_t : flipParity (β j₀) = true := Bool.eq_true_of_not_eq_false hj₀
    have hRHS0 : (∏ j : Fin m, (V * Vᵀ) (β (prevCell (by omega) j)) (β j)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
      rw [hVVT_eq, hj₀_t]; simp
    rw [hRHS0]
    by_cases hlast : flipParity (β (lastCell (by omega))) = true
    · simp [hlast]
    · have hlast_f : flipParity (β (lastCell (by omega))) = false := Bool.eq_false_iff.mpr hlast
      -- Since `flipParity (β last) = false` and `flipParity (β j₀) = true`, some adjacent pair differs!
      have hex_diff : ∃ j : Fin m, flipParity (β (prevCell (by omega) j)) ≠ flipParity (β j) := by
        by_contra hall_same; push Not at hall_same
        have hconst : ∀ k : ℕ, (hk : k < m) → flipParity (β ⟨k, hk⟩) = flipParity (β (lastCell (by omega))) := by
          intro k
          induction k with
          | zero =>
            intro hk
            have h0 := hall_same ⟨0, hk⟩
            have hprev0 : prevCell (by omega) ⟨0, hk⟩ = lastCell (by omega) := by
              ext; simp [prevCell, lastCell, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
            rw [hprev0] at h0; exact h0.symm
          | succ k ih =>
            intro hk
            have hs := hall_same ⟨k + 1, hk⟩
            have hprevs : prevCell (by omega) ⟨k + 1, hk⟩ = ⟨k, by omega⟩ := by
              ext; simp only [prevCell]
              rw [show k + 1 + m - 1 = k + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hprevs] at hs
            rw [← hs, ih (by omega)]
        have := hconst j₀.val j₀.isLt
        rw [hj₀_t, hlast_f] at this; exact Bool.noConfusion this
      rcases hex_diff with ⟨j, hj⟩
      have hprod0 : (∏ i : Fin m, (Wᵀ * W) (β (prevCell (by omega) i)) (β i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (hWTW_block _ _ hj)
      rw [hprod0, mul_zero]

/-! ## Section 6: Unconditional `TrotterIsingSystem` Instantiation & Boxed Candidate E Theorem -/

/-- Canonical index equivalence `(Fin M → Fin 4) ≃ Fin (4 ^ M)`. -/
noncomputable def equivFin4Pow (M : ℕ) : (Fin M → Fin 4) ≃ Fin (4 ^ M) :=
  Fintype.equivFinOfCardEq (by simp)

private lemma continuous_matrix_trace {n : Type*} [Fintype n] [DecidableEq n] :
    Continuous (Matrix.trace : Matrix n n ℝ → ℝ) := by
  have hsum : ∀ s : Finset n, Continuous (fun X : Matrix n n ℝ => ∑ i ∈ s, X i i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : Matrix n n ℝ => (0 : ℝ)))
    | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      have hpt : Continuous (fun X : Matrix n n ℝ => X a a) :=
        (continuous_apply a).comp (continuous_apply a)
      exact hpt.add ih
  exact hsum Finset.univ

/-- **Unconditional `TrotterIsingSystem` for the interacting Ising chain `H_ising L g h`**
valid for **every** `g ≥ 0, h ≥ 0` with ZERO transfer hypotheses! -/
noncomputable def isingTrotterSystem (g h : ℝ) (hg : 0 ≤ g) : TrotterIsingSystem where
  d_pu L := 2 ^ (L - 1)
  d_pt L := 2 ^ (L - 1)
  d_mu L := 2 ^ (L - 1)
  d_mt L := 2 ^ (L - 1)
  d_pu_pos _ _ _ := by positivity
  d_mu_pos _ _ _ := by positivity
  E_pu L := (H_ising_isHermitian L g h false false).eigenvalues
  E_pt L := (H_ising_isHermitian L g h true false).eigenvalues
  E_mu L := (H_ising_isHermitian L g h false true).eigenvalues
  E_mt L := (H_ising_isHermitian L g h true true).eigenvalues
  seam_order_p L _ _ := ising_seam_ordering L g h false
  seam_order_m L _ _ := ising_seam_ordering L g h true
  trotDim M := 4 ^ M
  V0 b M := (projFactor g h b M (1 : Matrix Bool Bool ℝ)).reindex (equivFin4Pow M) (equivFin4Pow M)
  V1 b M := (projFactor g h b M matX1).reindex (equivFin4Pow M) (equivFin4Pow M)
  trot_tendsto_Zplus := by
    intro m hm b hb
    -- Trace of reindexed Gram power equals trace of original Gram power
    have hre_tr : ∀ (Q : Matrix Bool Bool ℝ) (M : ℕ),
        Matrix.trace (((projFactor g h b M Q).reindex (equivFin4Pow M) (equivFin4Pow M) *
          ((projFactor g h b M Q).reindex (equivFin4Pow M) (equivFin4Pow M))ᵀ) ^ m) =
        Matrix.trace ((projFactor g h b M Q * (projFactor g h b M Q)ᵀ) ^ m) := fun Q M => by
      let e := equivFin4Pow M
      let V := projFactor g h b M Q
      have hT : (V.reindex e e)ᵀ = Vᵀ.reindex e e := by ext i j; rfl
      have hG : V.reindex e e * (V.reindex e e)ᵀ = (V * Vᵀ).reindex e e := by
        rw [hT]; exact ((Matrix.reindexAlgEquiv ℝ ℝ e).map_mul V Vᵀ).symm
      have hP : ∀ r : ℕ, ((V * Vᵀ).reindex e e) ^ r = ((V * Vᵀ) ^ r).reindex e e := fun r => by
        exact ((Matrix.reindexAlgEquiv ℝ ℝ e).map_pow (V * Vᵀ) r).symm
      rw [hG, hP m]
      simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact Equiv.sum_comp e.symm (fun x => ((V * Vᵀ) ^ m) x x)
    -- Apply `tendsto_trotter3` to `b • A_X`, `b • A_even`, `b • A_odd` for both `tw = false, true`
    have ht_tw : ∀ tw : Bool,
        Tendsto (fun M : ℕ =>
          (NormedSpace.exp ((b / (M : ℝ)) • A_X (2 * m) h) *
           NormedSpace.exp ((b / (M : ℝ)) • A_even m g) *
           NormedSpace.exp ((b / (M : ℝ)) • A_odd m (by omega) g tw)) ^ M)
          atTop (nhds (NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw)))) := fun tw => by
      have h3 := tendsto_trotter3 (b • A_X (2 * m) h) (b • A_even m g) (b • A_odd m (by omega) g tw)
      have harg : b • A_X (2 * m) h + b • A_even m g + b • A_odd m (by omega) g tw =
          b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw) := by simp [smul_add]
      rw [harg] at h3
      refine h3.congr fun M => ?_
      simp only [smul_smul, div_eq_inv_mul]
    have hcont_tr : Continuous (Matrix.trace : Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ → ℝ) :=
      continuous_matrix_trace
    have hcont_mulP : Continuous (fun X : Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ =>
        Matrix.trace (P_full (2 * m) * X)) :=
      hcont_tr.comp (continuous_const.mul continuous_id)
    have hlim_0 := ((hcont_tr.continuousAt.tendsto.comp (ht_tw false)).add
        (hcont_tr.continuousAt.tendsto.comp (ht_tw true))).div_const 2
    have hlim_1 := ((hcont_mulP.continuousAt.tendsto.comp (ht_tw false)).add
        (hcont_mulP.continuousAt.tendsto.comp (ht_tw true))).div_const 2
    have hlim_sum := hlim_0.add hlim_1
    have htarget :
        (Matrix.trace (NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g false))) +
         Matrix.trace (NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g true)))) / 2 +
        (Matrix.trace (P_full (2 * m) * NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g false))) +
         Matrix.trace (P_full (2 * m) * NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g true)))) / 2 =
        (∑ k : Fin (2 ^ (2 * m - 1)), Real.exp (-b * (H_ising_isHermitian (2 * m) g h false false).eigenvalues k)) +
        (∑ k : Fin (2 ^ (2 * m - 1)), Real.exp (-b * (H_ising_isHermitian (2 * m) g h true false).eigenvalues k)) := by
      have hf := trace_exp_Afull_eq_matZ hm b g h false
      have ht := trace_exp_Afull_eq_matZ hm b g h true
      rw [hf.1, hf.2, ht.1, ht.2]
      unfold matZ; ring
    rw [htarget] at hlim_sum
    refine hlim_sum.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    rw [hre_tr 1 M, hre_tr matX1 M]
    have hQ1 : ∀ a c : Bool, a ≠ c → (1 : Matrix Bool Bool ℝ) a c = 0 := fun a c h => by simp [h]
    have hQX : ∀ a c : Bool, a ≠ c → matX1 a c = 0 := fun a c h => by simp [matX1, h]
    have hid0 := finite_M_trace_identity hm hM hg hb (h := h) (1 : Matrix Bool Bool ℝ) hQ1
    have hid1 := finite_M_trace_identity hm hM hg hb (h := h) matX1 hQX
    dsimp only at hid0 hid1
    rw [kronVec_one, Matrix.one_mul, Matrix.one_mul] at hid0
    simp only [Function.comp_apply]
    change _ = _
    rw [← hid0, ← hid1]
    rfl
  trot_tendsto_Zminus := by
    intro m hm b hb
    have hre_tr : ∀ (Q : Matrix Bool Bool ℝ) (M : ℕ),
        Matrix.trace (((projFactor g h b M Q).reindex (equivFin4Pow M) (equivFin4Pow M) *
          ((projFactor g h b M Q).reindex (equivFin4Pow M) (equivFin4Pow M))ᵀ) ^ m) =
        Matrix.trace ((projFactor g h b M Q * (projFactor g h b M Q)ᵀ) ^ m) := fun Q M => by
      let e := equivFin4Pow M
      let V := projFactor g h b M Q
      have hT : (V.reindex e e)ᵀ = Vᵀ.reindex e e := by ext i j; rfl
      have hG : V.reindex e e * (V.reindex e e)ᵀ = (V * Vᵀ).reindex e e := by
        rw [hT]; exact ((Matrix.reindexAlgEquiv ℝ ℝ e).map_mul V Vᵀ).symm
      have hP : ∀ r : ℕ, ((V * Vᵀ).reindex e e) ^ r = ((V * Vᵀ) ^ r).reindex e e := fun r => by
        exact ((Matrix.reindexAlgEquiv ℝ ℝ e).map_pow (V * Vᵀ) r).symm
      rw [hG, hP m]
      simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact Equiv.sum_comp e.symm (fun x => ((V * Vᵀ) ^ m) x x)
    have ht_tw : ∀ tw : Bool,
        Tendsto (fun M : ℕ =>
          (NormedSpace.exp ((b / (M : ℝ)) • A_X (2 * m) h) *
           NormedSpace.exp ((b / (M : ℝ)) • A_even m g) *
           NormedSpace.exp ((b / (M : ℝ)) • A_odd m (by omega) g tw)) ^ M)
          atTop (nhds (NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw)))) := fun tw => by
      have h3 := tendsto_trotter3 (b • A_X (2 * m) h) (b • A_even m g) (b • A_odd m (by omega) g tw)
      have harg : b • A_X (2 * m) h + b • A_even m g + b • A_odd m (by omega) g tw =
          b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw) := by simp [smul_add]
      rw [harg] at h3
      refine h3.congr fun M => ?_
      simp only [smul_smul, div_eq_inv_mul]
    have hcont_tr : Continuous (Matrix.trace : Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ → ℝ) :=
      continuous_matrix_trace
    have hcont_mulP : Continuous (fun X : Matrix (Fin (2 * m) → Bool) (Fin (2 * m) → Bool) ℝ =>
        Matrix.trace (P_full (2 * m) * X)) :=
      hcont_tr.comp (continuous_const.mul continuous_id)
    have hlim_0 := ((hcont_tr.continuousAt.tendsto.comp (ht_tw false)).add
        (hcont_tr.continuousAt.tendsto.comp (ht_tw true))).div_const 2
    have hlim_1 := ((hcont_mulP.continuousAt.tendsto.comp (ht_tw false)).add
        (hcont_mulP.continuousAt.tendsto.comp (ht_tw true))).div_const 2
    have hlim_diff := hlim_0.sub hlim_1
    have htarget :
        (Matrix.trace (NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g false))) +
         Matrix.trace (NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g true)))) / 2 -
        (Matrix.trace (P_full (2 * m) * NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g false))) +
         Matrix.trace (P_full (2 * m) * NormedSpace.exp (b • (A_X (2 * m) h + A_even m g + A_odd m (by omega) g true)))) / 2 =
        (∑ k : Fin (2 ^ (2 * m - 1)), Real.exp (-b * (H_ising_isHermitian (2 * m) g h false true).eigenvalues k)) +
        (∑ k : Fin (2 ^ (2 * m - 1)), Real.exp (-b * (H_ising_isHermitian (2 * m) g h true true).eigenvalues k)) := by
      have hf := trace_exp_Afull_eq_matZ hm b g h false
      have ht := trace_exp_Afull_eq_matZ hm b g h true
      rw [hf.1, hf.2, ht.1, ht.2]
      unfold matZ; ring
    rw [htarget] at hlim_diff
    refine hlim_diff.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    rw [hre_tr 1 M, hre_tr matX1 M]
    have hQ1 : ∀ a c : Bool, a ≠ c → (1 : Matrix Bool Bool ℝ) a c = 0 := fun a c h => by simp [h]
    have hQX : ∀ a c : Bool, a ≠ c → matX1 a c = 0 := fun a c h => by simp [matX1, h]
    have hid0 := finite_M_trace_identity hm hM hg hb (h := h) (1 : Matrix Bool Bool ℝ) hQ1
    have hid1 := finite_M_trace_identity hm hM hg hb (h := h) matX1 hQX
    dsimp only at hid0 hid1
    rw [kronVec_one, Matrix.one_mul, Matrix.one_mul] at hid0
    simp only [Function.comp_apply]
    change _ = _
    rw [← hid0, ← hid1]
    rfl

/-- **100% UNCONDITIONAL CANDIDATE E 2D COUPLING-RECTANGLE MULTIPLET THEOREM**
(Pure Lean 4 Kernel, Zero `sorry`, Zero `native_decide`, Zero Transfer Hypotheses,
Strictly Standard Axioms `[propext, Classical.choice, Quot.sound]`):

For **every** coupling pair `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]` and **every**
even chain length `ℓ ≥ 64`, sorting all `2^ℓ` untwisted eigenvalues of the interacting
transverse-field Ising chain
  `H_ℓ(g, h) = -∑ Z_i Z_{i+1} - g ∑ X_i X_{i+1} - h ∑ X_i`
yields an exponentially degenerate ground doublet `(E_0(ℓ), E_1(ℓ))` separated from the
rest of the spectrum by a uniform spectral gap `> log 8 / 48`:
- `0 ≤ E_1(ℓ) - E_0(ℓ) ≤ (1 / 20) * exp (-(log 20) * ℓ / 128)`,
- `E_i(ℓ) - E_1(ℓ) > log 8 / 48` for every excited level `i ≥ 2`. -/
theorem candidate_e_unconditional_rectangle_theorem {g h : ℝ}
    (hg0 : (15 / 128 : ℝ) ≤ g) (hg1 : g ≤ 16 / 128)
    (hh0 : (47 / 128 : ℝ) ≤ h) (hh1 : h ≤ 48 / 128)
    {ℓ : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : 64 ≤ ℓ) :
    let raw := List.ofFn (H_ising_isHermitian ℓ g h false false).eigenvalues ++
               List.ofFn (H_ising_isHermitian ℓ g h false true).eigenvalues
    let sorted := raw.mergeSort (· ≤ ·)
    2 ≤ sorted.length ∧
    (∀ h0 h1, (0 : ℝ) ≤ sorted[1]'h1 - sorted[0]'h0 ∧
      sorted[1]'h1 - sorted[0]'h0 ≤
        (1 / 20 : ℝ) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / 128)) ∧
    (∀ i (hi : i < sorted.length) (h1 : 1 < sorted.length), 2 ≤ i →
      Real.log 8 / 48 < sorted[i]'hi - sorted[1]'h1) := by
  have hg_nn : 0 ≤ g := by linarith
  let sys := isingTrotterSystem g h hg_nn
  let psys := sys.toPuritySystem1D
  have hQ_ising : (877 / 1000 : ℝ) * (psys.Z 8 6) ^ 4 ≤ psys.Z 16 12 :=
    candidate_e_rectangle_Qplus_ge hg0 hg1 hh0 hh1
  have h64 := candidate_e_three_rounds_to_64 psys hQ_ising
  have hS64 : 1 - sys.Splus 64 48 ≤ 1 / 100 := h64.1
  have hT128 : 1 - sys.Tplus 128 48 ≤ 1 / 100 := h64.2
  have hres := sys.ising_multiplet_sorted ⟨32, by omega⟩ (by omega) (by norm_num : (0 : ℝ) < 48)
    hS64 hT128 hℓ_even hℓ_ge
  have hc1 : (12 : ℝ) / (5 * 48) = 1 / 20 := by norm_num
  have hc2 : (2 : ℝ) * ((64 : ℕ) : ℝ) = 128 := by norm_num
  rw [hc1, hc2] at hres
  exact hres

/-- Characteristic polynomial of a two-block `Matrix.blockDiagonal` over `Bool`. -/
theorem charpoly_blockDiagonal_bool {n : Type*} [Fintype n] [DecidableEq n]
    (B : Bool → Matrix n n ℝ) :
    (Matrix.blockDiagonal B).charpoly = (B false).charpoly * (B true).charpoly := by
  have hc : (Matrix.blockDiagonal B).charmatrix =
      Matrix.blockDiagonal (fun s => (B s).charmatrix) := by
    ext ⟨i, s⟩ ⟨j, t⟩ : 1
    by_cases h : s = t
    · subst t; simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
    · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply, h]
  rw [Matrix.charpoly, hc, Matrix.det_blockDiagonal, Fintype.prod_bool, mul_comm]
  rfl

/-- Exact multiset identity connecting the characteristic polynomial roots of the full
`2^(2*m) × 2^(2*m)` Pauli Hamiltonian `-(A_X + A_even + A_odd)` to the concatenation of the
`+1` (`sec = false`) and `-1` (`sec = true`) spin-flip parity block eigenvalues. -/
theorem charpoly_full_hamiltonian_roots {m : ℕ} (hm : 2 ≤ m) (g h : ℝ) (tw : Bool) :
    (-(A_X (2 * m) h + A_even m g + A_odd m (by omega) g tw)).charpoly.roots =
    (↑(List.ofFn (H_ising_isHermitian (2 * m) g h tw false).eigenvalues ++
       List.ofFn (H_ising_isHermitian (2 * m) g h tw true).eigenvalues) : Multiset ℝ) := by
  have br := reindex_Afull_eq_blockDiagonal hm (-1) g h tw
  simp only [neg_smul, one_smul, neg_neg] at br
  rw [← Matrix.charpoly_reindex (fullSectorEquiv m (by omega)), br, charpoly_blockDiagonal_bool,
    Polynomial.roots_mul
      (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero),
    (H_ising_isHermitian (2 * m) g h tw false).roots_charpoly_eq_eigenvalues,
    (H_ising_isHermitian (2 * m) g h tw true).roots_charpoly_eq_eigenvalues]
  simp [Fin.univ_val_map, Function.comp_def]

/-- **Full-Hamiltonian Unconditional Candidate E 2D Rectangle Theorem (Characteristic Polynomial +
Exact Length `2^(2*m)` + Explicit Spin-Flip Parity Labels on the Ground Doublet)**:
for every `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]` and every `m ≥ 32` (`ℓ = 2*m ≥ 64`),
let `H_full := -(A_X (2*m) h + A_even m g + A_odd m _ g false)` be the full `2^(2*m) × 2^(2*m)`
untwisted Pauli Hamiltonian. Then sorting the combined eigenvalues yields a list `sorted` with:
1. `sorted.length = 2 ^ (2 * m)`,
2. `(sorted : Multiset ℝ) = H_full.charpoly.roots` (full spectrum with multiplicity),
3. `sorted[0]` is the minimum eigenvalue of the `+1` parity block (`sec = false`) and
   `sorted[1]` is the minimum eigenvalue of the `-1` parity block (`sec = true`),
4. `0 ≤ sorted[1] - sorted[0] ≤ (1 / 20) * exp (-(log 20) * (2*m) / 128)`,
5. `log 8 / 48 < sorted[i] - sorted[1]` for every `2 ≤ i < 2 ^ (2 * m)`. -/
theorem candidate_e_unconditional_full_hamiltonian_theorem {g h : ℝ}
    (hg0 : (15 / 128 : ℝ) ≤ g) (hg1 : g ≤ 16 / 128)
    (hh0 : (47 / 128 : ℝ) ≤ h) (hh1 : h ≤ 48 / 128)
    {m : ℕ} (hm : 32 ≤ m) :
    let H_full := -(A_X (2 * m) h + A_even m g + A_odd m (by omega) g false)
    let raw := List.ofFn (H_ising_isHermitian (2 * m) g h false false).eigenvalues ++
               List.ofFn (H_ising_isHermitian (2 * m) g h false true).eigenvalues
    let sorted := raw.mergeSort (· ≤ ·)
    sorted.length = 2 ^ (2 * m) ∧
    (sorted : Multiset ℝ) = H_full.charpoly.roots ∧
    (∀ h0, ∃ k₀ : Fin (2 ^ (2 * m - 1)),
      sorted[0]'h0 = (H_ising_isHermitian (2 * m) g h false false).eigenvalues k₀ ∧
      ∀ k, (H_ising_isHermitian (2 * m) g h false false).eigenvalues k₀ ≤
        (H_ising_isHermitian (2 * m) g h false false).eigenvalues k) ∧
    (∀ h1, ∃ k₁ : Fin (2 ^ (2 * m - 1)),
      sorted[1]'h1 = (H_ising_isHermitian (2 * m) g h false true).eigenvalues k₁ ∧
      ∀ k, (H_ising_isHermitian (2 * m) g h false true).eigenvalues k₁ ≤
        (H_ising_isHermitian (2 * m) g h false true).eigenvalues k) ∧
    (∀ h0 h1, (0 : ℝ) ≤ sorted[1]'h1 - sorted[0]'h0 ∧
      sorted[1]'h1 - sorted[0]'h0 ≤
        (1 / 20 : ℝ) * Real.exp (-(Real.log 20) * ((2 * m : ℕ) : ℝ) / 128)) ∧
    (∀ i (hi : i < sorted.length) (h1 : 1 < sorted.length), 2 ≤ i →
      Real.log 8 / 48 < sorted[i]'hi - sorted[1]'h1) := by
  have hg_nn : 0 ≤ g := by linarith
  let sys := isingTrotterSystem g h hg_nn
  let psys := sys.toPuritySystem1D
  have hQ_ising : (877 / 1000 : ℝ) * (psys.Z 8 6) ^ 4 ≤ psys.Z 16 12 :=
    candidate_e_rectangle_Qplus_ge hg0 hg1 hh0 hh1
  have h64 := candidate_e_three_rounds_to_64 psys hQ_ising
  have hres := sys.ising_multiplet_sorted_labeled ⟨32, by omega⟩ (by omega) (by norm_num : (0 : ℝ) < 48)
    h64.1 h64.2 (ℓ := 2 * m) ⟨m, by omega⟩ (by omega)
  have hc1 : (12 : ℝ) / (5 * 48) = 1 / 20 := by norm_num
  have hc2 : (2 : ℝ) * ((64 : ℕ) : ℝ) = 128 := by norm_num
  rw [hc1, hc2] at hres
  intro H_full raw sorted
  have hlen : sorted.length = 2 ^ (2 * m) := by
    have h1 := hres.1
    dsimp [sys, isingTrotterSystem] at h1
    have hpow : 2 ^ (2 * m - 1) + 2 ^ (2 * m - 1) = 2 ^ (2 * m) := by
      have hk : 2 * m = (2 * m - 1) + 1 := by omega
      conv_rhs => rw [hk, pow_succ, mul_two]
    exact h1.trans hpow
  have hroots : (sorted : Multiset ℝ) = H_full.charpoly.roots := by
    have hperm : sorted.Perm raw := List.mergeSort_perm raw (· ≤ ·)
    rw [Multiset.coe_eq_coe.mpr hperm, charpoly_full_hamiltonian_roots (by omega) g h false]
  exact ⟨hlen, hroots, hres.2.2.1, hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2⟩

end PurityBootstrap.IsingTrotter
