import PurityBootstrap.IsingHamiltonian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Exact Periodic Matrix Product State (MPS) Contraction for the Interacting Ising Chain

Proves the exact transfer-matrix contraction identity for a bond-dimension `D = 2`
periodic MPS `ψ(b) = Tr(∏_{k=0}^{L-1} A_{b_k})` projected onto the even-`X` parity sector
of `H_ising L g h false false`.

For `L = 16`, this reduces the 32,768-dimensional exact Rayleigh quotient
`⟨v_MPS, H_ising 16 g h false false *ᵥ v_MPS⟩ / ⟨v_MPS, v_MPS⟩`
to traces of `4 × 4` integer matrix powers (`Ep^16, Em^16, ...`), verifiable in milliseconds
inside Lean 4's kernel with zero external numerical premises.
-/

namespace PurityBootstrap.IsingMPS

open scoped BigOperators Matrix Kronecker
open Matrix PurityBootstrap.IsingHamiltonian

/-- Ordered matrix product `∏_{k=0}^{n-1} M k` (`M 0 * M 1 * ... * M (n - 1)`). -/
def matProd {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ {n : ℕ}, (Fin n → Matrix α α ℝ) → Matrix α α ℝ
  | 0, _ => 1
  | _ + 1, M => M 0 * matProd (fun k => M k.succ)

lemma matProd_congr {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ {n : ℕ} {F G : Fin n → Matrix α α ℝ}, (∀ k, F k = G k) → matProd F = matProd G
  | 0, _, _, _ => rfl
  | _ + 1, _, _, h => by simp only [matProd, h 0, matProd_congr (fun k => h k.succ)]

lemma matProd_const {γ : Type*} [Fintype γ] [DecidableEq γ] (M : Matrix γ γ ℝ) :
    ∀ n : ℕ, matProd (fun _ : Fin n => M) = M ^ n
  | 0 => rfl
  | n + 1 => by simp only [matProd, matProd_const M n, pow_succ']

lemma matProd_kronecker {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    ∀ {n : ℕ} (F : Fin n → Matrix α α ℝ) (G : Fin n → Matrix β β ℝ),
      (matProd F) ⊗ₖ (matProd G) = matProd (fun k => (F k) ⊗ₖ (G k))
  | 0, _, _ => by simp [matProd]
  | _ + 1, F, G => by
    simp only [matProd]
    rw [Matrix.mul_kronecker_mul, matProd_kronecker]

lemma matProd_cast {γ : Type*} [Fintype γ] [DecidableEq γ]
    {m n : ℕ} (h : m = n) (M : Fin n → Matrix γ γ ℝ) :
    matProd M = matProd (fun k : Fin m => M (finCongr h k)) := by
  subst h; rfl

lemma matProd_smul {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Matrix α α ℝ),
      matProd (fun k => c k • M k) = (∏ k : Fin n, c k) • matProd M
  | 0, _, _ => by simp [matProd]
  | _ + 1, c, M => by
    simp only [matProd, Fin.prod_univ_succ, matProd_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_comm]

lemma matProd_append {γ : Type*} [Fintype γ] [DecidableEq γ] :
    ∀ {a b : ℕ} (M : Fin (a + b) → Matrix γ γ ℝ),
      matProd M =
        matProd (fun i : Fin a => M (Fin.castAdd b i)) *
        matProd (fun j : Fin b => M (Fin.natAdd a j))
  | 0, b, M => by
    have h0 : 0 + b = b := Nat.zero_add b
    rw [matProd_cast h0.symm M]
    simp only [matProd, one_mul]
    exact matProd_congr fun j => by congr 1; ext; simp
  | a + 1, b, M => by
    have hadd : (a + b) + 1 = (a + 1) + b := by omega
    rw [matProd_cast hadd M]
    simp only [matProd]
    have hsplit := matProd_append (a := a) (b := b) (fun k : Fin (a + b) => M (finCongr hadd k.succ))
    rw [hsplit, ← Matrix.mul_assoc]
    have h1 : M (finCongr hadd 0) = M (Fin.castAdd b 0) := by congr 1
    have h2 : matProd (fun i : Fin a => M (finCongr hadd (Fin.castAdd b i).succ)) =
        matProd (fun i : Fin a => M (Fin.castAdd b i.succ)) :=
      matProd_congr fun i => by congr 1
    have h3 : matProd (fun j : Fin b => M (finCongr hadd (Fin.natAdd a j).succ)) =
        matProd (fun j : Fin b => M (Fin.natAdd (a + 1) j)) :=
      matProd_congr fun j => by congr 1; ext; simp; omega
    rw [h1, h2, h3]

/-- Distributing a finite sum over `Fin n → Bool` through an ordered matrix product. -/
lemma sum_matProd_bool {γ : Type*} [Fintype γ] [DecidableEq γ] :
    ∀ {n : ℕ} (T : Fin n → Bool → Matrix γ γ ℝ),
      ∑ b : Fin n → Bool, matProd (fun k => T k (b k)) =
        matProd (fun k => T k false + T k true)
  | 0, _ => by simp [matProd]
  | n + 1, T => by
    let e : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) :=
      { toFun := fun b => (b 0, fun k => b k.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun b => by funext k; refine Fin.cases ?_ ?_ k <;> simp
        right_inv := fun ⟨b0, br⟩ => by ext <;> simp }
    rw [← Equiv.sum_comp e.symm]
    simp only [e, Equiv.coe_fn_symm_mk, matProd, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    simp_rw [← Matrix.mul_sum, sum_matProd_bool]
    rw [Fintype.sum_bool, ← Matrix.add_mul, add_comm (T 0 true)]

/-- **Master periodic MPS contraction identity**:
for any `n` and site-dependent matrix pairs `F, G : Fin n → Bool → Matrix (Fin 2) (Fin 2) ℝ`,
`∑ b : Fin n → Bool, Tr(∏ F_k(b_k)) * Tr(∏ G_k(b_k)) = Tr(∏ (F_k false ⊗ G_k false + F_k true ⊗ G_k true))`. -/
theorem sum_trace_matProd_mul {n : ℕ}
    (F G : Fin n → Bool → Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ b : Fin n → Bool,
        Matrix.trace (matProd (fun k => F k (b k))) *
        Matrix.trace (matProd (fun k => G k (b k))) =
      Matrix.trace (matProd (fun k => (F k false) ⊗ₖ (G k false) + (F k true) ⊗ₖ (G k true))) := by
  have h1 : ∀ b : Fin n → Bool,
      Matrix.trace (matProd (fun k => F k (b k))) *
      Matrix.trace (matProd (fun k => G k (b k))) =
      Matrix.trace (matProd (fun k => (F k (b k)) ⊗ₖ (G k (b k)))) := fun b => by
    rw [← Matrix.trace_kronecker, matProd_kronecker]
  simp_rw [h1]
  rw [← Matrix.trace_sum, sum_matProd_bool (T := fun k s => (F k s) ⊗ₖ (G k s))]

/-- Trace of a single-site insertion `X` at position `j` inside `M^(n-1)`. -/
lemma trace_matProd_single {γ : Type*} [Fintype γ] [DecidableEq γ]
    {n : ℕ} (M X : Matrix γ γ ℝ) (j : Fin n) :
    Matrix.trace (matProd (fun k : Fin n => if k = j then X else M)) =
      Matrix.trace (X * M ^ (n - 1)) := by
  have hn : j.val + (1 + (n - 1 - j.val)) = n := by omega
  let e : Fin (j.val + (1 + (n - 1 - j.val))) ≃ Fin n := finCongr hn
  rw [matProd_cast hn (fun k : Fin n => if k = j then X else M), matProd_append, matProd_append]
  have hL : matProd (fun i : Fin j.val => if e (Fin.castAdd _ i) = j then X else M) = M ^ j.val := by
    rw [← matProd_const]
    refine matProd_congr fun i => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h; simp [e] at this; try omega
  have hMid : matProd (fun i : Fin 1 => if e (Fin.natAdd j.val (Fin.castAdd _ i)) = j then X else M) = X := by
    simp only [matProd, mul_one]
    rw [if_pos]; ext; simp [e]
  have hR : matProd (fun i : Fin (n - 1 - j.val) =>
      if e (Fin.natAdd j.val (Fin.natAdd 1 i)) = j then X else M) = M ^ (n - 1 - j.val) := by
    rw [← matProd_const]
    refine matProd_congr fun i => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h; simp [e] at this; try omega
  change Matrix.trace (matProd (fun i : Fin j.val => if e (Fin.castAdd _ i) = j then X else M) *
    (matProd (fun i : Fin 1 => if e (Fin.natAdd j.val (Fin.castAdd _ i)) = j then X else M) *
     matProd (fun i : Fin (n - 1 - j.val) => if e (Fin.natAdd j.val (Fin.natAdd 1 i)) = j then X else M))) = _
  rw [hL, hMid, hR, Matrix.trace_mul_comm (M ^ j.val), Matrix.mul_assoc, ← pow_add]
  rw [show n - 1 - j.val + j.val = n - 1 by omega]

/-- Trace of an adjacent-bond insertion `(X, X)` at `(j, (j+1) % n)` inside `M^(n-2)` (`2 ≤ n`). -/
lemma trace_matProd_adj {γ : Type*} [Fintype γ] [DecidableEq γ]
    {n : ℕ} (hn2 : 2 ≤ n) (M X : Matrix γ γ ℝ) (j : Fin n) :
    Matrix.trace (matProd (fun k : Fin n =>
        if k = j ∨ k.val = (j.val + 1) % n then X else M)) =
      Matrix.trace (X * X * M ^ (n - 2)) := by
  by_cases hlast : j.val + 1 < n
  · have hmod : (j.val + 1) % n = j.val + 1 := Nat.mod_eq_of_lt hlast
    have hn : j.val + (2 + (n - 2 - j.val)) = n := by omega
    let e : Fin (j.val + (2 + (n - 2 - j.val))) ≃ Fin n := finCongr hn
    rw [matProd_cast hn (fun k : Fin n => if k = j ∨ k.val = (j.val + 1) % n then X else M),
      matProd_append, matProd_append]
    have hL : matProd (fun i : Fin j.val =>
        if e (Fin.castAdd _ i) = j ∨ (e (Fin.castAdd _ i)).val = (j.val + 1) % n then X else M) = M ^ j.val := by
      rw [← matProd_const]; refine matProd_congr fun i => ?_
      rw [if_neg]; rintro (h | h)
      · have := congrArg Fin.val h; simp [e] at this; try omega
      · simp [e, hmod] at h; omega
    have hMid : matProd (fun i : Fin 2 =>
        if e (Fin.natAdd j.val (Fin.castAdd _ i)) = j ∨
          (e (Fin.natAdd j.val (Fin.castAdd _ i))).val = (j.val + 1) % n then X else M) = X * X := by
      simp only [matProd, mul_one]
      congr 1
      · rw [if_pos]; left; ext; simp [e]
      · rw [if_pos]; right; simp [e, hmod]
    have hR : matProd (fun i : Fin (n - 2 - j.val) =>
        if e (Fin.natAdd j.val (Fin.natAdd 2 i)) = j ∨
          (e (Fin.natAdd j.val (Fin.natAdd 2 i))).val = (j.val + 1) % n then X else M) = M ^ (n - 2 - j.val) := by
      rw [← matProd_const]; refine matProd_congr fun i => ?_
      rw [if_neg]; rintro (h | h)
      · have := congrArg Fin.val h; simp [e] at this; try omega
      · simp [e, hmod] at h; omega
    change Matrix.trace (matProd (fun i : Fin j.val =>
        if e (Fin.castAdd _ i) = j ∨ (e (Fin.castAdd _ i)).val = (j.val + 1) % n then X else M) *
      (matProd (fun i : Fin 2 =>
        if e (Fin.natAdd j.val (Fin.castAdd _ i)) = j ∨
          (e (Fin.natAdd j.val (Fin.castAdd _ i))).val = (j.val + 1) % n then X else M) *
       matProd (fun i : Fin (n - 2 - j.val) =>
        if e (Fin.natAdd j.val (Fin.natAdd 2 i)) = j ∨
          (e (Fin.natAdd j.val (Fin.natAdd 2 i))).val = (j.val + 1) % n then X else M))) = _
    rw [hL, hMid, hR, Matrix.trace_mul_comm (M ^ j.val), Matrix.mul_assoc, ← pow_add]
    rw [show n - 2 - j.val + j.val = n - 2 by omega]
  · have hj_eq : j.val = n - 1 := by omega
    have hmod : (j.val + 1) % n = 0 := by rw [show j.val + 1 = n by omega, Nat.mod_self]
    have hn : 1 + ((n - 2) + 1) = n := by omega
    let e : Fin (1 + ((n - 2) + 1)) ≃ Fin n := finCongr hn
    rw [matProd_cast hn (fun k : Fin n => if k = j ∨ k.val = (j.val + 1) % n then X else M),
      matProd_append, matProd_append]
    have hL : matProd (fun i : Fin 1 =>
        if e (Fin.castAdd _ i) = j ∨ (e (Fin.castAdd _ i)).val = (j.val + 1) % n then X else M) = X := by
      simp only [matProd, mul_one]
      rw [if_pos]; right; simp [e, hmod]
    have hMid : matProd (fun i : Fin (n - 2) =>
        if e (Fin.natAdd 1 (Fin.castAdd _ i)) = j ∨
          (e (Fin.natAdd 1 (Fin.castAdd _ i))).val = (j.val + 1) % n then X else M) = M ^ (n - 2) := by
      rw [← matProd_const]; refine matProd_congr fun i => ?_
      rw [if_neg]; rintro (h | h)
      · have := congrArg Fin.val h; simp [e, hj_eq] at this; omega
      · simp [e, hmod] at h
    have hR : matProd (fun i : Fin 1 =>
        if e (Fin.natAdd 1 (Fin.natAdd (n - 2) i)) = j ∨
          (e (Fin.natAdd 1 (Fin.natAdd (n - 2) i))).val = (j.val + 1) % n then X else M) = X := by
      simp only [matProd, mul_one]
      rw [if_pos]; left; ext; simp [e, hj_eq]; omega
    change Matrix.trace (matProd (fun i : Fin 1 =>
        if e (Fin.castAdd _ i) = j ∨ (e (Fin.castAdd _ i)).val = (j.val + 1) % n then X else M) *
      (matProd (fun i : Fin (n - 2) =>
        if e (Fin.natAdd 1 (Fin.castAdd _ i)) = j ∨
          (e (Fin.natAdd 1 (Fin.castAdd _ i))).val = (j.val + 1) % n then X else M) *
       matProd (fun i : Fin 1 =>
        if e (Fin.natAdd 1 (Fin.natAdd (n - 2) i)) = j ∨
          (e (Fin.natAdd 1 (Fin.natAdd (n - 2) i))).val = (j.val + 1) % n then X else M))) = _
    rw [hL, hMid, hR, ← Matrix.mul_assoc, Matrix.trace_mul_comm (X * M ^ (n - 2)), ← Matrix.mul_assoc]

/-! ## Bitstring Parity Bijection `(Fin L → Bool) ≃ Bool × Fin (2 ^ (L - 1))` -/

/-- Recursive parity of a boolean tuple `b : Fin m → Bool`. -/
def tupleParity : ∀ {m : ℕ}, (Fin m → Bool) → Bool
  | 0, _ => false
  | m + 1, b => xor (b (Fin.last m)) (tupleParity (fun k : Fin m => b k.castSucc))

/-- Convert a boolean tuple `b : Fin m → Bool` to its little-endian natural number `< 2^m`. -/
def tupleToNat : ∀ {m : ℕ}, (Fin m → Bool) → ℕ
  | 0, _ => 0
  | m + 1, b => tupleToNat (fun k : Fin m => b k.castSucc) +
      if b (Fin.last m) then 2 ^ m else 0

lemma tupleToNat_lt : ∀ {m : ℕ} (b : Fin m → Bool), tupleToNat b < 2 ^ m
  | 0, _ => by simp [tupleToNat]
  | m + 1, b => by
    simp only [tupleToNat]
    have ih := tupleToNat_lt (fun k : Fin m => b k.castSucc)
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    split_ifs <;> omega

lemma testBit_add_two_pow {a m k : ℕ} (ha : a < 2 ^ m) (bit : Bool) :
    (a + if bit then 2 ^ m else 0).testBit k =
      if k = m then bit else if k < m then a.testBit k else false := by
  have hhi : ∀ j, m ≤ j → a.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hj))
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    split_ifs with h1 h2
    · subst h1; exact hhi k le_rfl
    · rfl
    · exact hhi k (by omega)
  · simp only [↓reduceIte]
    split_ifs with h1 h2
    · subst h1
      rw [add_comm, Nat.testBit_two_pow_add_eq, hhi k le_rfl]; rfl
    · have hdiv : (a + 2 ^ m) / 2 ^ k = a / 2 ^ k + 2 ^ (m - k) := by
        have hm : 2 ^ m = 2 ^ (m - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
        rw [hm, Nat.add_mul_div_right _ _ (by positivity)]
      have heven : 2 ^ (m - k) % 2 = 0 := by
        have h1' : m - k = (m - k - 1) + 1 := by omega
        rw [h1', pow_succ]; omega
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
      have hmod : (a / 2 ^ k + 2 ^ (m - k)) % 2 = (a / 2 ^ k) % 2 := by omega
      simp [Nat.and_one_is_mod, hmod]
    · have hlt : a + 2 ^ m < 2 ^ k := by
        have hpow : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by ring
        have hle : 2 ^ (m + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact Nat.testBit_lt_two_pow hlt

lemma tupleToNat_testBit : ∀ {m : ℕ} (b : Fin m → Bool) (k : ℕ),
    (tupleToNat b).testBit k = if h : k < m then b ⟨k, h⟩ else false
  | 0, _, _ => by simp [tupleToNat]
  | m + 1, b, k => by
    simp only [tupleToNat]
    rw [testBit_add_two_pow (tupleToNat_lt _), tupleToNat_testBit]
    split_ifs with h1 h2 h3 h4 <;> try omega
    · subst h1; rfl
    · rfl
    · rfl

lemma bitParity_eq_tupleParity : ∀ {m : ℕ} (b : Fin m → Bool),
    bitParity m (tupleToNat b) = tupleParity b
  | 0, _ => rfl
  | m + 1, b => by
    simp only [bitParity, tupleParity, tupleToNat_testBit, Nat.lt_succ_self, ↓reduceDIte]
    congr 1
    have hlow : bitParity m (tupleToNat b) = bitParity m (tupleToNat (fun k : Fin m => b k.castSucc)) := by
      have hgen : ∀ r (hr : r ≤ m) (x y : ℕ), (∀ j < r, x.testBit j = y.testBit j) →
          bitParity r x = bitParity r y := by
        intro r
        induction r with
        | zero => intros; rfl
        | succ r ih =>
          intro hr x y hxy
          simp only [bitParity]
          rw [hxy r (Nat.lt_succ_self r), ih (by omega) x y (fun j hj => hxy j (by omega))]
      refine hgen m le_rfl _ _ fun j hj => ?_
      rw [tupleToNat_testBit, tupleToNat_testBit, dif_pos (by omega), dif_pos hj]
      rfl
    rw [hlow, bitParity_eq_tupleParity]

lemma bitParity_eq_tupleParity_of_lt {m : ℕ} (i : Fin (2 ^ m)) :
    bitParity m i.val = tupleParity (fun k : Fin m => i.val.testBit k.val) := by
  have heq : tupleToNat (fun k : Fin m => i.val.testBit k.val) = i.val := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [tupleToNat_testBit]
    split_ifs with hk
    · rfl
    · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  conv_lhs => rw [← heq]
  exact bitParity_eq_tupleParity _

lemma spinBool_prod_eq : ∀ {m : ℕ} (b : Fin m → Bool),
    (∏ k : Fin m, if b k then (-1 : ℝ) else (1 : ℝ)) =
      if tupleParity b then (-1 : ℝ) else (1 : ℝ)
  | 0, _ => by simp [tupleParity]
  | m + 1, b => by
    rw [Fin.prod_univ_castSucc, spinBool_prod_eq]
    simp only [tupleParity]
    rcases Bool.eq_false_or_eq_true (b (Fin.last m)) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (tupleParity (fun k : Fin m => b k.castSucc)) with h2 | h2 <;>
      simp [h1, h2]

/-- Bijection between `Fin (m + 1) → Bool` and `Bool × Fin (2 ^ m)` matching `sectorState (m + 1)`. -/
def sectorEquiv (m : ℕ) : (Fin (m + 1) → Bool) ≃ Bool × Fin (2 ^ m) where
  toFun b := (tupleParity b, ⟨tupleToNat (fun k : Fin m => b k.castSucc), tupleToNat_lt _⟩)
  invFun p := fun k => (sectorState (m + 1) p.1 p.2).testBit k.val
  left_inv b := by
    funext k
    simp only [sectorState, Nat.add_sub_cancel]
    rw [testBit_add_two_pow (tupleToNat_lt _), bitParity_eq_tupleParity]
    split_ifs with h1 h2
    · simp only [tupleParity]
      have hk : k = Fin.last m := Fin.ext h1
      subst hk
      cases b (Fin.last m) <;> cases tupleParity (fun j : Fin m => b j.castSucc) <;> rfl
    · rw [tupleToNat_testBit, dif_pos h2]; rfl
    · omega
  right_inv p := by
    rcases p with ⟨sec, i⟩
    ext
    · simp only [tupleParity, sectorState, Nat.add_sub_cancel, Fin.val_last]
      rw [testBit_add_two_pow i.isLt, if_pos rfl]
      have hlow : tupleParity (fun k : Fin m =>
          (i.val + if xor sec (bitParity m i.val) then 2 ^ m else 0).testBit k.val) =
          bitParity m i.val := by
        rw [bitParity_eq_tupleParity_of_lt i]
        congr 1; funext k
        rw [testBit_add_two_pow i.isLt, if_neg (by omega), if_pos k.isLt]
      simp only [Fin.val_castSucc]
      rw [hlow]
      cases sec <;> cases bitParity m i.val <;> rfl
    · apply Nat.eq_of_testBit_eq; intro k
      rw [tupleToNat_testBit]
      split_ifs with hk
      · simp only [sectorState, Nat.add_sub_cancel, Fin.val_castSucc]
        rw [testBit_add_two_pow i.isLt, if_neg (by omega), if_pos hk]
      · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-- Even-`X` sector sum rewritten as `(1/2) * (sum + parity-weighted sum)` over `Fin (m + 1) → Bool`. -/
lemma sum_even_sector {m : ℕ} (F : (Fin (m + 1) → Bool) → ℝ) :
    ∑ i : Fin (2 ^ m), F (fun k => (sectorState (m + 1) false i).testBit k.val) =
      ((∑ b : Fin (m + 1) → Bool, F b) +
       (∑ b : Fin (m + 1) → Bool,
         (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else (1 : ℝ)) * F b)) / 2 := by
  have hcomb :
      (∑ b : Fin (m + 1) → Bool, F b) +
      (∑ b : Fin (m + 1) → Bool, (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else (1 : ℝ)) * F b) =
      ∑ b : Fin (m + 1) → Bool, (if tupleParity b then (0 : ℝ) else 2) * F b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [spinBool_prod_eq]
    cases tupleParity b <;> simp <;> ring
  rw [hcomb, ← Equiv.sum_comp (sectorEquiv m).symm, Fintype.sum_prod_type, Fintype.sum_bool]
  have hpar : ∀ sec (i : Fin (2 ^ m)), tupleParity ((sectorEquiv m).symm (sec, i)) = sec := fun sec i => by
    have := congrArg Prod.fst ((sectorEquiv m).right_inv (sec, i))
    exact this
  simp_rw [hpar]
  simp only [↓reduceIte, Bool.false_eq_true, zero_mul, Finset.sum_const_zero, zero_add,
    ← Finset.mul_sum]
  ring_nf
  rfl

/-! ## Exact `D = 2` Periodic MPS Vector and Rayleigh Quotient Contraction -/

/-- Periodic `D = 2` MPS wavefunction on the even-`X` sector of length `m + 1`. -/
def mpsVec (m : ℕ) (A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin (2 ^ m)) : ℝ :=
  Matrix.trace (matProd (fun k : Fin (m + 1) =>
    if (sectorState (m + 1) false i).testBit k.val then A₁ else A₀))

/-- Exact norm-squared of the `D = 2` even-`X` periodic MPS via `4 × 4` transfer traces. -/
theorem mpsVec_norm_sq (m : ℕ) (A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ) :
    let E₀ := A₀ ⊗ₖ A₀
    let E₁ := A₁ ⊗ₖ A₁
    dotProduct (mpsVec m A₀ A₁) (mpsVec m A₀ A₁) =
      (Matrix.trace ((E₀ + E₁) ^ (m + 1)) + Matrix.trace ((E₀ - E₁) ^ (m + 1))) / 2 := by
  intro E₀ E₁
  have hdot : dotProduct (mpsVec m A₀ A₁) (mpsVec m A₀ A₁) =
      ∑ i : Fin (2 ^ m),
        (fun b : Fin (m + 1) → Bool =>
          Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
          Matrix.trace (matProd (fun k => if b k then A₁ else A₀)))
        (fun k => (sectorState (m + 1) false i).testBit k.val) := rfl
  rw [hdot, sum_even_sector (F := fun b : Fin (m + 1) → Bool =>
    Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
    Matrix.trace (matProd (fun k => if b k then A₁ else A₀)))]
  congr 1; congr 1
  · rw [sum_trace_matProd_mul (F := fun _ s => if s then A₁ else A₀) (G := fun _ s => if s then A₁ else A₀)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg Matrix.trace (matProd_const (E₀ + E₁) (m + 1))
  · have hmul : ∀ b : Fin (m + 1) → Bool,
        (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else (1 : ℝ)) *
          (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
           Matrix.trace (matProd (fun k => if b k then A₁ else A₀))) =
        Matrix.trace (matProd (fun k => (if b k then (-1 : ℝ) else (1 : ℝ)) • (if b k then A₁ else A₀))) *
        Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) := fun b => by
      rw [matProd_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]
    simp_rw [hmul]
    rw [sum_trace_matProd_mul
      (F := fun _ s => (if s then (-1 : ℝ) else (1 : ℝ)) • (if s then A₁ else A₀))
      (G := fun _ s => if s then A₁ else A₀)]
    have hstep : ((1 : ℝ) • A₀) ⊗ₖ A₀ + ((-1 : ℝ) • A₁) ⊗ₖ A₁ = E₀ - E₁ := by
      ext ⟨a, b⟩ ⟨c, d⟩; simp [E₀, E₁, sub_eq_add_neg]
    simp only [Bool.false_eq_true, ↓reduceIte, hstep, matProd_const]

/-- Exact `H_X` expectation value of the `D = 2` even-`X` periodic MPS. -/
theorem mpsVec_H_X (m : ℕ) (A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ) :
    let E₀ := A₀ ⊗ₖ A₀
    let E₁ := A₁ ⊗ₖ A₁
    dotProduct (mpsVec m A₀ A₁) ((H_X (m + 1) false).mulVec (mpsVec m A₀ A₁)) =
      -((m + 1 : ℝ) *
        (Matrix.trace ((E₀ - E₁) * (E₀ + E₁) ^ m) +
         Matrix.trace ((E₀ + E₁) * (E₀ - E₁) ^ m)) / 2) := by
  intro E₀ E₁
  have hdiag : dotProduct (mpsVec m A₀ A₁) ((H_X (m + 1) false).mulVec (mpsVec m A₀ A₁)) =
      -(∑ j : Fin (m + 1), ∑ i : Fin (2 ^ m),
        (if (sectorState (m + 1) false i).testBit j.val then (-1 : ℝ) else (1 : ℝ)) *
          (mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ i)) := by
    simp only [dotProduct, H_X, Matrix.mulVec_diagonal, spinVal]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hdiag]
  have hsite : ∀ j : Fin (m + 1),
      ∑ i : Fin (2 ^ m),
        (if (sectorState (m + 1) false i).testBit j.val then (-1 : ℝ) else (1 : ℝ)) *
          (mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ i) =
      (Matrix.trace ((E₀ - E₁) * (E₀ + E₁) ^ m) +
       Matrix.trace ((E₀ + E₁) * (E₀ - E₁) ^ m)) / 2 := by
    intro j
    have hrew : (∑ i : Fin (2 ^ m),
        (if (sectorState (m + 1) false i).testBit j.val then (-1 : ℝ) else (1 : ℝ)) *
          (mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ i)) =
        ∑ i : Fin (2 ^ m),
          (fun b : Fin (m + 1) → Bool =>
            (if b j then (-1 : ℝ) else (1 : ℝ)) *
              (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
               Matrix.trace (matProd (fun k => if b k then A₁ else A₀))))
          (fun k => (sectorState (m + 1) false i).testBit k.val) := rfl
    rw [hrew, sum_even_sector (F := fun b : Fin (m + 1) → Bool =>
      (if b j then (-1 : ℝ) else (1 : ℝ)) *
        (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
         Matrix.trace (matProd (fun k => if b k then A₁ else A₀))))]
    congr 1; congr 1
    · have h1 : ∀ b : Fin (m + 1) → Bool,
          (if b j then (-1 : ℝ) else (1 : ℝ)) *
            (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
             Matrix.trace (matProd (fun k => if b k then A₁ else A₀))) =
          Matrix.trace (matProd (fun k => (if k = j then (if b k then (-1 : ℝ) else 1) else 1) • (if b k then A₁ else A₀))) *
          Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) := fun b => by
        rw [matProd_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]
        have hp : (∏ k : Fin (m + 1), if k = j then (if b k then (-1 : ℝ) else 1) else 1) =
            if b j then (-1 : ℝ) else 1 := by simp
        rw [hp]
      simp_rw [h1]
      rw [sum_trace_matProd_mul
        (F := fun k s => (if k = j then (if s then (-1 : ℝ) else 1) else 1) • (if s then A₁ else A₀))
        (G := fun _ s => if s then A₁ else A₀)]
      have harg : (fun k : Fin (m + 1) =>
          ((if k = j then (1 : ℝ) else 1) • A₀) ⊗ₖ A₀ +
          ((if k = j then (-1 : ℝ) else 1) • A₁) ⊗ₖ A₁) =
          fun k => if k = j then (E₀ - E₁) else (E₀ + E₁) := by
        funext k; split_ifs <;> (ext ⟨a, b⟩ ⟨c, d⟩; simp [E₀, E₁, sub_eq_add_neg])
      simp only [Bool.false_eq_true, ↓reduceIte, harg]
      simpa using trace_matProd_single (E₀ + E₁) (E₀ - E₁) j
    · have h2 : ∀ b : Fin (m + 1) → Bool,
          (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else 1) *
            ((if b j then (-1 : ℝ) else 1) *
              (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
               Matrix.trace (matProd (fun k => if b k then A₁ else A₀)))) =
          Matrix.trace (matProd (fun k =>
            (if k = j then (1 : ℝ) else (if b k then (-1 : ℝ) else 1)) • (if b k then A₁ else A₀))) *
          Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) := fun b => by
        rw [matProd_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]
        rw [← mul_assoc (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else 1)]
        congr 1
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
            ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [↓reduceIte, one_mul]
        have hsq : (if b j then (-1 : ℝ) else 1) * (if b j then (-1 : ℝ) else 1) = 1 := by
          cases b j <;> norm_num
        have hrest : ∏ x ∈ Finset.univ.erase j, (if b x then (-1 : ℝ) else 1) =
            ∏ x ∈ Finset.univ.erase j, if x = j then (1 : ℝ) else (if b x then (-1 : ℝ) else 1) :=
          Finset.prod_congr rfl fun x hx => (if_neg (Finset.ne_of_mem_erase hx)).symm
        rw [← hrest]; calc
          (if b j then (-1 : ℝ) else 1) * (∏ x ∈ Finset.univ.erase j, if b x then (-1 : ℝ) else 1) *
            (if b j then (-1 : ℝ) else 1)
              = ((if b j then (-1 : ℝ) else 1) * (if b j then (-1 : ℝ) else 1)) *
                (∏ x ∈ Finset.univ.erase j, if b x then (-1 : ℝ) else 1) := by ring
          _ = _ := by rw [hsq, one_mul]
      simp_rw [h2]
      rw [sum_trace_matProd_mul
        (F := fun k s => (if k = j then (1 : ℝ) else (if s then (-1 : ℝ) else 1)) • (if s then A₁ else A₀))
        (G := fun _ s => if s then A₁ else A₀)]
      have harg : (fun k : Fin (m + 1) =>
          ((if k = j then (1 : ℝ) else 1) • A₀) ⊗ₖ A₀ +
          ((if k = j then (1 : ℝ) else -1) • A₁) ⊗ₖ A₁) =
          fun k => if k = j then (E₀ + E₁) else (E₀ - E₁) := by
        funext k; split_ifs <;> (ext ⟨a, b⟩ ⟨c, d⟩; simp [E₀, E₁, sub_eq_add_neg])
      simp only [Bool.false_eq_true, ↓reduceIte, harg]
      simpa using trace_matProd_single (E₀ - E₁) (E₀ + E₁) j
  simp_rw [hsite]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  ring

/-- Exact `H_XX` expectation value of the `D = 2` even-`X` periodic MPS (`2 ≤ m + 1`). -/
theorem mpsVec_H_XX {m : ℕ} (hm : 1 ≤ m) (A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ) :
    let E₀ := A₀ ⊗ₖ A₀
    let E₁ := A₁ ⊗ₖ A₁
    dotProduct (mpsVec m A₀ A₁) ((H_XX (m + 1) false).mulVec (mpsVec m A₀ A₁)) =
      -((m + 1 : ℝ) *
        (Matrix.trace ((E₀ - E₁) * (E₀ - E₁) * (E₀ + E₁) ^ (m - 1)) +
         Matrix.trace ((E₀ + E₁) * (E₀ + E₁) * (E₀ - E₁) ^ (m - 1))) / 2) := by
  intro E₀ E₁
  have hdiag : dotProduct (mpsVec m A₀ A₁) ((H_XX (m + 1) false).mulVec (mpsVec m A₀ A₁)) =
      -(∑ j : Fin (m + 1), ∑ i : Fin (2 ^ m),
        ((if (sectorState (m + 1) false i).testBit j.val then (-1 : ℝ) else 1) *
         (if (sectorState (m + 1) false i).testBit ((j.val + 1) % (m + 1)) then (-1 : ℝ) else 1)) *
          (mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ i)) := by
    simp only [dotProduct, H_XX, Matrix.mulVec_diagonal, spinVal]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hdiag]
  have hbond : ∀ j : Fin (m + 1),
      ∑ i : Fin (2 ^ m),
        ((if (sectorState (m + 1) false i).testBit j.val then (-1 : ℝ) else 1) *
         (if (sectorState (m + 1) false i).testBit ((j.val + 1) % (m + 1)) then (-1 : ℝ) else 1)) *
          (mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ i) =
      (Matrix.trace ((E₀ - E₁) * (E₀ - E₁) * (E₀ + E₁) ^ (m - 1)) +
       Matrix.trace ((E₀ + E₁) * (E₀ + E₁) * (E₀ - E₁) ^ (m - 1))) / 2 := by
    intro j
    let j1 : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
    have hj_ne : j ≠ j1 := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [j1] at hv
      by_cases h : j.val + 1 < m + 1
      · rw [Nat.mod_eq_of_lt h] at hv; omega
      · have h0 : j.val + 1 = m + 1 := by omega
        rw [h0, Nat.mod_self] at hv; omega
    have hrew : (∑ i : Fin (2 ^ m),
        ((if (sectorState (m + 1) false i).testBit j.val then (-1 : ℝ) else 1) *
         (if (sectorState (m + 1) false i).testBit ((j.val + 1) % (m + 1)) then (-1 : ℝ) else 1)) *
          (mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ i)) =
        ∑ i : Fin (2 ^ m),
          (fun b : Fin (m + 1) → Bool =>
            ((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1)) *
              (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
               Matrix.trace (matProd (fun k => if b k then A₁ else A₀))))
          (fun k => (sectorState (m + 1) false i).testBit k.val) := rfl
    rw [hrew, sum_even_sector (F := fun b : Fin (m + 1) → Bool =>
      ((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1)) *
        (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
         Matrix.trace (matProd (fun k => if b k then A₁ else A₀))))]
    congr 1; congr 1
    · have h1 : ∀ b : Fin (m + 1) → Bool,
          ((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1)) *
            (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
             Matrix.trace (matProd (fun k => if b k then A₁ else A₀))) =
          Matrix.trace (matProd (fun k =>
            (if k = j ∨ k.val = (j.val + 1) % (m + 1) then (if b k then (-1 : ℝ) else 1) else 1) •
              (if b k then A₁ else A₀))) *
          Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) := fun b => by
        rw [matProd_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]
        have hp : (∏ k : Fin (m + 1),
            if k = j ∨ k.val = (j.val + 1) % (m + 1) then (if b k then (-1 : ℝ) else 1) else 1) =
            (if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
          have hj1_mem : j1 ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hj_ne.symm, Finset.mem_univ _⟩
          rw [← Finset.mul_prod_erase _ _ hj1_mem]
          have hj1_cond : j1 = j ∨ j1.val = (j.val + 1) % (m + 1) := Or.inr rfl
          simp only [↓reduceIte, true_or, hj1_cond]
          have hrest : ∏ x ∈ (Finset.univ.erase j).erase j1,
              (if x = j ∨ x.val = (j.val + 1) % (m + 1) then (if b x then (-1 : ℝ) else 1) else 1) = 1 := by
            refine Finset.prod_eq_one fun x hx => ?_
            have hx1 : x ≠ j1 := Finset.ne_of_mem_erase hx
            have hx0 : x ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
            rw [if_neg]; rintro (h | h)
            · exact hx0 h
            · exact hx1 (Fin.ext h)
          rw [hrest, mul_one]
        rw [hp]; ring
      simp_rw [h1]
      rw [sum_trace_matProd_mul
        (F := fun k s => (if k = j ∨ k.val = (j.val + 1) % (m + 1) then (if s then (-1 : ℝ) else 1) else 1) • (if s then A₁ else A₀))
        (G := fun _ s => if s then A₁ else A₀)]
      have harg : (fun k : Fin (m + 1) =>
          ((if k = j ∨ k.val = (j.val + 1) % (m + 1) then (1 : ℝ) else 1) • A₀) ⊗ₖ A₀ +
          ((if k = j ∨ k.val = (j.val + 1) % (m + 1) then (-1 : ℝ) else 1) • A₁) ⊗ₖ A₁) =
          fun k => if k = j ∨ k.val = (j.val + 1) % (m + 1) then (E₀ - E₁) else (E₀ + E₁) := by
        funext k; split_ifs <;> (ext ⟨a, b⟩ ⟨c, d⟩; simp [E₀, E₁, sub_eq_add_neg])
      simp only [Bool.false_eq_true, ↓reduceIte, harg]
      simpa using trace_matProd_adj (by omega : 2 ≤ m + 1) (E₀ + E₁) (E₀ - E₁) j
    · have h2 : ∀ b : Fin (m + 1) → Bool,
          (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else 1) *
            (((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1)) *
              (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
               Matrix.trace (matProd (fun k => if b k then A₁ else A₀)))) =
          Matrix.trace (matProd (fun k =>
            (if k = j ∨ k.val = (j.val + 1) % (m + 1) then (1 : ℝ) else (if b k then (-1 : ℝ) else 1)) •
              (if b k then A₁ else A₀))) *
          Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) := fun b => by
        rw [matProd_smul, Matrix.trace_smul, smul_eq_mul]
        have hre : (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else 1) *
            (((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1)) *
              (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
               Matrix.trace (matProd (fun k => if b k then A₁ else A₀)))) =
            ((∏ k : Fin (m + 1), if b k then (-1 : ℝ) else 1) *
              ((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1))) *
              Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
              Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) := by ring
        rw [hre]
        congr 1; congr 1
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        have hj1_mem : j1 ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hj_ne.symm, Finset.mem_univ _⟩
        rw [← Finset.mul_prod_erase _ _ hj1_mem]
        conv_rhs =>
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
              ← Finset.mul_prod_erase _ _ hj1_mem]
        have hsqj : (if b j then (-1 : ℝ) else 1) * (if b j then (-1 : ℝ) else 1) = 1 := by
          cases b j <;> norm_num
        have hsqj1 : (if b j1 then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1) = 1 := by
          cases b j1 <;> norm_num
        have hrest : ∏ x ∈ (Finset.univ.erase j).erase j1, (if b x then (-1 : ℝ) else 1) =
            ∏ x ∈ (Finset.univ.erase j).erase j1,
              (if x = j ∨ x.val = (j.val + 1) % (m + 1) then (1 : ℝ) else (if b x then (-1 : ℝ) else 1)) := by
          refine Finset.prod_congr rfl fun x hx => ?_
          have hx1 : x ≠ j1 := Finset.ne_of_mem_erase hx
          have hx0 : x ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
          symm; rw [if_neg]; rintro (h | h)
          · exact hx0 h
          · exact hx1 (Fin.ext h)
        have hj1_cond : j1 = j ∨ j1.val = (j.val + 1) % (m + 1) := Or.inr rfl
        simp only [↓reduceIte, true_or, hj1_cond, one_mul, ← hrest]
        calc (if b j then (-1 : ℝ) else 1) * ((if b j1 then (-1 : ℝ) else 1) *
              (∏ x ∈ (Finset.univ.erase j).erase j1, if b x then (-1 : ℝ) else 1)) *
              ((if b j then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1))
            = ((if b j then (-1 : ℝ) else 1) * (if b j then (-1 : ℝ) else 1)) *
              ((if b j1 then (-1 : ℝ) else 1) * (if b j1 then (-1 : ℝ) else 1)) *
              (∏ x ∈ (Finset.univ.erase j).erase j1, if b x then (-1 : ℝ) else 1) := by ring
          _ = _ := by rw [hsqj, hsqj1, one_mul, one_mul]
      simp_rw [h2]
      rw [sum_trace_matProd_mul
        (F := fun k s => (if k = j ∨ k.val = (j.val + 1) % (m + 1) then (1 : ℝ) else (if s then (-1 : ℝ) else 1)) • (if s then A₁ else A₀))
        (G := fun _ s => if s then A₁ else A₀)]
      have harg : (fun k : Fin (m + 1) =>
          ((if k = j ∨ k.val = (j.val + 1) % (m + 1) then (1 : ℝ) else 1) • A₀) ⊗ₖ A₀ +
          ((if k = j ∨ k.val = (j.val + 1) % (m + 1) then (1 : ℝ) else -1) • A₁) ⊗ₖ A₁) =
          fun k => if k = j ∨ k.val = (j.val + 1) % (m + 1) then (E₀ + E₁) else (E₀ - E₁) := by
        funext k; split_ifs <;> (ext ⟨a, b⟩ ⟨c, d⟩; simp [E₀, E₁, sub_eq_add_neg])
      simp only [Bool.false_eq_true, ↓reduceIte, harg]
      simpa using trace_matProd_adj (by omega : 2 ≤ m + 1) (E₀ - E₁) (E₀ + E₁) j
  simp_rw [hbond]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  ring

/-- Helper: bitstring of `sectorState (m + 1) false (flipBond (m + 1) j i)` equals flipping bits
`j` and `(j + 1) % (m + 1)` of `sectorState (m + 1) false i` (`1 ≤ m`). -/
lemma testBit_sectorState_flipBond {m : ℕ} (hm : 1 ≤ m) (j : Fin (m + 1))
    (i : Fin (2 ^ m)) (k : Fin (m + 1)) :
    (sectorState (m + 1) false (flipBond (m + 1) j.val i)).testBit k.val =
      if k = j ∨ k.val = (j.val + 1) % (m + 1) then
        !((sectorState (m + 1) false i).testBit k.val)
      else (sectorState (m + 1) false i).testBit k.val := by
  let b : Fin (m + 1) → Bool := fun r => (sectorState (m + 1) false i).testBit r.val
  let b' : Fin (m + 1) → Bool := fun r =>
    if r = j ∨ r.val = (j.val + 1) % (m + 1) then !(b r) else b r
  have hj1_ne : j ≠ ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ := by
    intro heq; have hv := congrArg Fin.val heq; dsimp at hv
    by_cases h : j.val + 1 < m + 1
    · rw [Nat.mod_eq_of_lt h] at hv; omega
    · have h0 : j.val + 1 = m + 1 := by omega
      rw [h0, Nat.mod_self] at hv; omega
  have hpar_b : tupleParity b = false := by
    have := congrArg Prod.fst ((sectorEquiv m).right_inv (false, i))
    exact this
  have hpar_b' : tupleParity b' = false := by
    have hprod : (∏ r : Fin (m + 1), if b' r then (-1 : ℝ) else 1) =
        (∏ r : Fin (m + 1), if b r then (-1 : ℝ) else 1) := by
      let j1 : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
      have hj1_mem : j1 ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hj1_ne.symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
          ← Finset.mul_prod_erase _ _ hj1_mem]
      conv_rhs =>
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
            ← Finset.mul_prod_erase _ _ hj1_mem]
      have hrest : ∏ x ∈ (Finset.univ.erase j).erase j1, (if b' x then (-1 : ℝ) else 1) =
          ∏ x ∈ (Finset.univ.erase j).erase j1, (if b x then (-1 : ℝ) else 1) := by
        refine Finset.prod_congr rfl fun x hx => ?_
        have hx1 : x ≠ j1 := Finset.ne_of_mem_erase hx
        have hx0 : x ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
        have hnot : ¬ (x = j ∨ x.val = (j.val + 1) % (m + 1)) := by
          rintro (h | h); exact hx0 h; exact hx1 (Fin.ext h)
        simp [b', hnot]
      have hbj : b' j = !(b j) := by simp [b']
      have hbj1 : b' j1 = !(b j1) := by simp [b', j1]
      rw [hrest, hbj, hbj1]
      cases b j <;> cases b j1 <;> simp <;> ring
    rw [spinBool_prod_eq, spinBool_prod_eq, hpar_b] at hprod
    cases h : tupleParity b'
    · rfl
    · rw [h] at hprod; norm_num at hprod
  have hlow_eq : (⟨tupleToNat (fun r : Fin m => b' r.castSucc), tupleToNat_lt _⟩ : Fin (2 ^ m)) =
      flipBond (m + 1) j.val i := by
    ext
    apply Nat.eq_of_testBit_eq; intro r
    simp only [flipBond, Nat.add_sub_cancel]
    have hmask_lt : ((1 <<< j.val) ^^^ (1 <<< ((j.val + 1) % (m + 1)))) % (2 ^ m) < 2 ^ m :=
      Nat.mod_lt _ (by positivity)
    rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow i.isLt hmask_lt), Nat.testBit_xor,
      Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      tupleToNat_testBit]
    by_cases hr : r < m
    · rw [dif_pos hr, decide_eq_true hr, Bool.true_and]
      have hb_r : b ⟨r, by omega⟩ = i.val.testBit r := by
        simp only [b, sectorState, Nat.add_sub_cancel]
        rw [testBit_add_two_pow i.isLt, if_neg (by omega), if_pos hr]
      have hshift : ∀ a : ℕ, (decide (a ≤ r) && (1 : ℕ).testBit (r - a)) = decide (r = a) := fun a => by
        by_cases h : r = a
        · subst h; simp
        · by_cases hle : a ≤ r
          · have hgt : 1 < 2 ^ (r - a) := by
              have h1 : 1 ≤ r - a := by omega
              have h2 : 2 ^ 1 ≤ 2 ^ (r - a) := Nat.pow_le_pow_right (by norm_num) h1
              omega
            rw [Nat.testBit_lt_two_pow hgt]; simp [h]
          · simp [hle, h]
      rw [hshift j.val, hshift ((j.val + 1) % (m + 1))]
      have hcond : ((⟨r, by omega⟩ : Fin (m + 1)) = j ∨ r = (j.val + 1) % (m + 1)) ↔
          (r = j.val ∨ r = (j.val + 1) % (m + 1)) := by
        constructor
        · rintro (h | h); left; exact congrArg Fin.val h; right; exact h
        · rintro (h | h); left; exact Fin.ext h; right; exact h
      dsimp only [b', Fin.castSucc_mk]
      rw [hb_r]
      by_cases hjr : r = j.val
      · have hne2 : j.val ≠ (j.val + 1) % (m + 1) := by
          intro h2; exact hj1_ne (Fin.ext (by dsimp; omega))
        rw [if_pos (hcond.mpr (Or.inl hjr))]
        subst hjr; simp [hne2]
      · by_cases hj1r : r = (j.val + 1) % (m + 1)
        · have hne1 : (j.val + 1) % (m + 1) ≠ j.val := by
            intro h2; exact hj1_ne (Fin.ext (by dsimp; omega))
          rw [if_pos (hcond.mpr (Or.inr hj1r))]
          subst hj1r; simp [hne1]
        · rw [if_neg (by intro h; rcases hcond.mp h with h1 | h2 <;> contradiction)]
          simp [hjr, hj1r]
    · rw [dif_neg hr, decide_eq_false hr, Bool.false_and, Bool.xor_false]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  have hinv := congrFun ((sectorEquiv m).left_inv b') k
  simp only [sectorEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, hpar_b', hlow_eq] at hinv
  exact hinv

/-- Exact `H_ZZ` expectation value of the `D = 2` even-`X` periodic MPS (`2 ≤ m + 1`). -/
theorem mpsVec_H_ZZ {m : ℕ} (hm : 1 ≤ m) (A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ) :
    let E₀ := A₀ ⊗ₖ A₀
    let E₁ := A₁ ⊗ₖ A₁
    let Kp := A₀ ⊗ₖ A₁ + A₁ ⊗ₖ A₀
    let Km := A₀ ⊗ₖ A₁ - A₁ ⊗ₖ A₀
    dotProduct (mpsVec m A₀ A₁) ((H_ZZ (m + 1) false).mulVec (mpsVec m A₀ A₁)) =
      -((m + 1 : ℝ) *
        (Matrix.trace (Kp * Kp * (E₀ + E₁) ^ (m - 1)) +
         Matrix.trace (Km * Km * (E₀ - E₁) ^ (m - 1))) / 2) := by
  intro E₀ E₁ Kp Km
  have hquad : dotProduct (mpsVec m A₀ A₁) ((H_ZZ (m + 1) false).mulVec (mpsVec m A₀ A₁)) =
      -(∑ j : Fin (m + 1), ∑ i : Fin (2 ^ m),
        mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ (flipBond (m + 1) j.val i)) := by
    simp only [dotProduct, Matrix.mulVec, H_ZZ, Matrix.of_apply, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    calc ∑ x : Fin (2 ^ m), mpsVec m A₀ A₁ i *
            ((∑ k ∈ Finset.range (m + 1), if x = flipBond (m + 1) k i then (-1 : ℝ) else 0) *
              mpsVec m A₀ A₁ x)
        = ∑ x : Fin (2 ^ m), ∑ k : Fin (m + 1),
            if x = flipBond (m + 1) k.val i then -(mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ x) else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_range, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
      _ = ∑ k : Fin (m + 1), ∑ x : Fin (2 ^ m),
            if x = flipBond (m + 1) k.val i then -(mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ x) else 0 :=
          Finset.sum_comm
      _ = ∑ k : Fin (m + 1), -(mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ (flipBond (m + 1) k.val i)) := by
          refine Finset.sum_congr rfl fun k _ => by simp
  rw [hquad]
  have hbond : ∀ j : Fin (m + 1),
      ∑ i : Fin (2 ^ m), mpsVec m A₀ A₁ i * mpsVec m A₀ A₁ (flipBond (m + 1) j.val i) =
      (Matrix.trace (Kp * Kp * (E₀ + E₁) ^ (m - 1)) +
       Matrix.trace (Km * Km * (E₀ - E₁) ^ (m - 1))) / 2 := by
    intro j
    have hflip : ∀ i : Fin (2 ^ m),
        mpsVec m A₀ A₁ (flipBond (m + 1) j.val i) =
          Matrix.trace (matProd (fun k : Fin (m + 1) =>
            if k = j ∨ k.val = (j.val + 1) % (m + 1) then
              if !((sectorState (m + 1) false i).testBit k.val) then A₁ else A₀
            else if (sectorState (m + 1) false i).testBit k.val then A₁ else A₀)) := fun i => by
      unfold mpsVec
      congr 1; refine matProd_congr fun k => ?_
      rw [testBit_sectorState_flipBond hm j i k]
      split_ifs <;> rfl
    simp_rw [hflip]
    have hrew : (∑ i : Fin (2 ^ m),
        mpsVec m A₀ A₁ i *
          Matrix.trace (matProd (fun k : Fin (m + 1) =>
            if k = j ∨ k.val = (j.val + 1) % (m + 1) then
              if !((sectorState (m + 1) false i).testBit k.val) then A₁ else A₀
            else if (sectorState (m + 1) false i).testBit k.val then A₁ else A₀))) =
        ∑ i : Fin (2 ^ m),
          (fun b : Fin (m + 1) → Bool =>
            Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
            Matrix.trace (matProd (fun k =>
              if k = j ∨ k.val = (j.val + 1) % (m + 1) then
                if !(b k) then A₁ else A₀
              else if b k then A₁ else A₀)))
          (fun k => (sectorState (m + 1) false i).testBit k.val) := rfl
    rw [hrew]
    rw [sum_even_sector (F := fun b : Fin (m + 1) → Bool =>
      Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
      Matrix.trace (matProd (fun k =>
        if k = j ∨ k.val = (j.val + 1) % (m + 1) then
          if !(b k) then A₁ else A₀
        else if b k then A₁ else A₀)))]
    congr 1; congr 1
    · rw [sum_trace_matProd_mul
        (F := fun _ s => if s then A₁ else A₀)
        (G := fun k s => if k = j ∨ k.val = (j.val + 1) % (m + 1) then
          if !s then A₁ else A₀ else if s then A₁ else A₀)]
      have harg : (fun k : Fin (m + 1) =>
          A₀ ⊗ₖ (if k = j ∨ k.val = (j.val + 1) % (m + 1) then A₁ else A₀) +
          A₁ ⊗ₖ (if k = j ∨ k.val = (j.val + 1) % (m + 1) then A₀ else A₁)) =
          fun k => if k = j ∨ k.val = (j.val + 1) % (m + 1) then Kp else (E₀ + E₁) := by
        funext k; split_ifs <;> rfl
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, harg]
      simpa using trace_matProd_adj (by omega : 2 ≤ m + 1) (E₀ + E₁) Kp j
    · have h2 : ∀ b : Fin (m + 1) → Bool,
          (∏ k : Fin (m + 1), if b k then (-1 : ℝ) else 1) *
            (Matrix.trace (matProd (fun k => if b k then A₁ else A₀)) *
             Matrix.trace (matProd (fun k =>
               if k = j ∨ k.val = (j.val + 1) % (m + 1) then
                 if !(b k) then A₁ else A₀
               else if b k then A₁ else A₀))) =
          Matrix.trace (matProd (fun k => (if b k then (-1 : ℝ) else 1) • (if b k then A₁ else A₀))) *
          Matrix.trace (matProd (fun k =>
            if k = j ∨ k.val = (j.val + 1) % (m + 1) then
              if !(b k) then A₁ else A₀
            else if b k then A₁ else A₀)) := fun b => by
        rw [matProd_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]
      simp_rw [h2]
      rw [sum_trace_matProd_mul
        (F := fun _ s => (if s then (-1 : ℝ) else 1) • (if s then A₁ else A₀))
        (G := fun k s => if k = j ∨ k.val = (j.val + 1) % (m + 1) then
          if !s then A₁ else A₀ else if s then A₁ else A₀)]
      have harg : (fun k : Fin (m + 1) =>
          ((1 : ℝ) • A₀) ⊗ₖ (if k = j ∨ k.val = (j.val + 1) % (m + 1) then A₁ else A₀) +
          ((-1 : ℝ) • A₁) ⊗ₖ (if k = j ∨ k.val = (j.val + 1) % (m + 1) then A₀ else A₁)) =
          fun k => if k = j ∨ k.val = (j.val + 1) % (m + 1) then Km else (E₀ - E₁) := by
        funext k; split_ifs <;> (ext ⟨a, b⟩ ⟨c, d⟩; simp [E₀, E₁, Km, sub_eq_add_neg])
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, harg]
      simpa using trace_matProd_adj (by omega : 2 ≤ m + 1) (E₀ - E₁) Km j
  simp_rw [hbond]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  ring

end PurityBootstrap.IsingMPS
