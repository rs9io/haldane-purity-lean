import PurityBootstrap.MatrixTools
import PurityBootstrap.IsingHamiltonian
import Mathlib.Tactic

/-!
# Computable Block-Diagonal Gershgorin Certificate Verifier for `L = 8` Ising Blocks

Connects fast pure-kernel `List Int` / `ℚ` verification (`decide +kernel`, zero `native_decide`)
to `PurityBootstrap.MatrixTools.gershgorin_matZ_le` for the 128-dimensional even-`X` blocks
of `H_ising 8 (g_num / 128) (h_num / 128) twist false`.

Architecture:
1. Sparse integer symmetry basis `Bcols` (6 orthogonal `{-1, 0, +1}` blocks of sizes `≤ 32`).
2. Soundness lemma `sum_mul_lookup` reducing `Fin 128` sums against sparse columns to `List` folds.
3. Computable block-diagonal Gershgorin checker `checkBlockGershgorin` using linear-time `dotList`.
4. Rational argument-reduced `exp(-x)` upper bound `ratExpNegUpper` via `exp_neg_div_pow2_upper`.
5. End-to-end soundness theorem `certify_H8_matZ_upper`:
   `verifyH8Cert ... = true → matZ (H_ising 8 (g_num/128) (h_num/128) twist false) _ 6 ≤ exp 72 * U`.
-/

namespace PurityBootstrap.BlockGershgorin

open scoped BigOperators Matrix
open Matrix PurityBootstrap.MatrixTools PurityBootstrap.IsingHamiltonian

/-! ## Exact Integer Representation of `128 * (H_ising 8 + 12 • 1)` -/

/-- Exact integer matrix `128 * (H_ising 8 (g_num/128) (h_num/128) twist false + 12 • 1)`
on `Fin 128`. -/
def H8ShiftInt (g_num h_num : ℤ) (twist : Bool) (i j : Fin 128) : ℤ :=
  let diag : ℤ :=
    if i = j then
      let s := sectorState 8 false i
      1536 +
      g_num * (∑ k ∈ Finset.range 8, -(spinValInt s k * spinValInt s ((k + 1) % 8))) +
      h_num * (∑ k ∈ Finset.range 8, -(spinValInt s k))
    else 0
  let off : ℤ :=
    ∑ k ∈ Finset.range 8,
      if j = flipBond 8 k i then
        if twist && decide (k = 7) then (128 : ℤ) else (-128 : ℤ)
      else 0
  diag + off

/-- Fast computable integer version of `H8ShiftInt` on `Nat` indices `< 128`. -/
def H8ShiftIntFast (g_num h_num : ℤ) (twist : Bool) (i j : ℕ) : ℤ :=
  if hi : i < 128 then
    let fi : Fin 128 := ⟨i, hi⟩
    let diag : ℤ :=
      if i = j then
        let s := sectorState 8 false fi
        let sxx := (List.range 8).foldl (fun acc k => acc - spinValInt s k * spinValInt s ((k + 1) % 8)) 0
        let sx := (List.range 8).foldl (fun acc k => acc - spinValInt s k) 0
        1536 + g_num * sxx + h_num * sx
      else 0
    let off : ℤ :=
      (List.range 8).foldl (fun acc k =>
        if j = (flipBond 8 k fi).val then
          acc + (if twist && decide (k = 7) then (128 : ℤ) else (-128 : ℤ))
        else acc) 0
    diag + off
  else 0

lemma foldl_add_eq_sum_range (f : ℕ → ℤ) :
    ∀ n (init : ℤ), (List.range n).foldl (fun acc k => acc + f k) init =
      init + ∑ k ∈ Finset.range n, f k
  | 0, init => by simp
  | n + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_add_eq_sum_range f n init, Finset.sum_range_succ]
    ring

lemma foldl_sub_eq_sum_range (f : ℕ → ℤ) :
    ∀ n (init : ℤ), (List.range n).foldl (fun acc k => acc - f k) init =
      init + ∑ k ∈ Finset.range n, -(f k)
  | 0, init => by simp
  | n + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_sub_eq_sum_range f n init, Finset.sum_range_succ]
    ring

lemma H8ShiftIntFast_eq (g_num h_num : ℤ) (twist : Bool) (i j : Fin 128) :
    H8ShiftIntFast g_num h_num twist i.val j.val = H8ShiftInt g_num h_num twist i j := by
  unfold H8ShiftIntFast H8ShiftInt
  rw [dif_pos i.isLt]
  have hfi : (⟨i.val, i.isLt⟩ : Fin 128) = i := Fin.eta i i.isLt
  rw [hfi]
  dsimp only
  congr 1
  · by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      rw [foldl_sub_eq_sum_range, foldl_sub_eq_sum_range, zero_add, zero_add]
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp only [hij, hval, ↓reduceIte]
  · have hfold := foldl_add_eq_sum_range
      (fun k => if j.val = (flipBond 8 k i).val then
        (if twist && decide (k = 7) then (128 : ℤ) else (-128 : ℤ)) else 0) 8 0
    have hlhs : (List.range 8).foldl (fun acc k =>
        if j.val = (flipBond 8 k i).val then
          acc + (if twist && decide (k = 7) then (128 : ℤ) else (-128 : ℤ))
        else acc) 0 =
      (List.range 8).foldl (fun acc k =>
        acc + (if j.val = (flipBond 8 k i).val then
          (if twist && decide (k = 7) then (128 : ℤ) else (-128 : ℤ))
        else 0)) 0 := by
      congr 1; funext acc k; split_ifs <;> ring
    rw [hlhs, hfold, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hiff : j.val = (flipBond 8 k i).val ↔ j = flipBond 8 k i :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    by_cases h : j = flipBond 8 k i
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma H8ShiftInt_cast (g_num h_num : ℤ) (twist : Bool) (i j : Fin 128) :
    (H8ShiftInt g_num h_num twist i j : ℝ) =
      128 * (H_ising 8 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) twist false +
        (12 : ℝ) • (1 : Matrix (Fin 128) (Fin 128) ℝ)) i j := by
  unfold H8ShiftInt H_ising H_ZZ H_XX H_X
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_ite,
    Int.cast_zero, Int.cast_ofNat, Int.cast_neg]
  have hspin : ∀ s k, spinVal s k = (spinValInt s k : ℝ) := spinVal_eq_cast
  simp_rw [hspin]
  have h128 : (128 : ℝ) ≠ 0 := by norm_num
  have hoff : (∑ x ∈ Finset.range 8,
      if j = flipBond 8 x i then if (twist && decide (x = 7)) = true then (128 : ℝ) else (-128 : ℝ) else 0) =
      128 * ∑ x ∈ Finset.range 8,
        if j = flipBond 8 x i then if (twist && decide (x = 7)) = true then (1 : ℝ) else (-1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> norm_num
  rw [hoff]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_neg, Int.cast_ofNat]
    field_simp [h128]
    ring
  · simp only [hij, ↓reduceIte, mul_zero, add_zero, zero_add]

/-! ## Sparse Column Representation & Linear-Time `List Int` Arithmetic -/

/-- Linear-time dot product of two `List Int` vectors. -/
def dotList : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dotList as bs

/-- Componentwise product of two `List Int` vectors. -/
def mulList : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => (a * b) :: mulList as bs

/-- Lookup entry `r` in a sparse column `List (Nat × Int)` (summing duplicates if any,
which makes linearity unconditional without even requiring `Nodup`!). -/
def sparseLookup (r : ℕ) : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (idx, val) :: rest => (if r = idx then val else 0) + sparseLookup r rest

/-- Check all row indices in a sparse column are `< n`. -/
def sparseInBounds (n : ℕ) (col : List (ℕ × ℤ)) : Bool :=
  col.all fun p => decide (p.1 < n)

/-- Sparse dot product between two sparse columns (when both are in bounds `< n`). -/
def sparseDot (c₁ c₂ : List (ℕ × ℤ)) : ℤ :=
  c₁.foldl (fun acc p => acc + p.2 * sparseLookup p.1 c₂) 0

/-- Sparse bilinear form `c₁ᵀ * M * c₂` for a general function `M : ℕ → ℕ → ℤ`. -/
def sparseBilinear (M : ℕ → ℕ → ℤ) (c₁ c₂ : List (ℕ × ℤ)) : ℤ :=
  c₁.foldl (fun acc p => acc + p.2 * c₂.foldl (fun acc2 q => acc2 + M p.1 q.1 * q.2) 0) 0

lemma sparseLookup_sum_mul {n : ℕ} (f : Fin n → ℤ) :
    ∀ (c : List (ℕ × ℤ)), sparseInBounds n c = true →
      ∑ i : Fin n, f i * sparseLookup i.val c =
        c.foldl (fun acc p => acc + (if h : p.1 < n then f ⟨p.1, h⟩ * p.2 else 0)) 0
  | [], _ => by simp [sparseLookup]
  | (r, v) :: rest, hb => by
    simp only [sparseInBounds, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨hr, hrest⟩
    have hfold_shift : ∀ (l : List (ℕ × ℤ)) (g : ℕ × ℤ → ℤ) (init : ℤ),
        l.foldl (fun acc p => acc + g p) init = init + l.foldl (fun acc p => acc + g p) 0 := by
      intro l g
      induction l with
      | nil => intro init; simp
      | cons a tl ih =>
        intro init
        simp only [List.foldl_cons, zero_add]
        rw [ih (init + g a), ih (g a)]; ring
    simp only [List.foldl_cons, zero_add, dif_pos hr]
    rw [hfold_shift rest _ (f ⟨r, hr⟩ * v), ← sparseLookup_sum_mul f rest hrest]
    simp only [sparseLookup, mul_add, Finset.sum_add_distrib]
    congr 1
    have hsingle : ∑ i : Fin n, f i * (if i.val = r then v else 0) = f ⟨r, hr⟩ * v := by
      have hrew : ∀ i : Fin n, f i * (if i.val = r then v else 0) =
          if i = ⟨r, hr⟩ then f i * v else 0 := fun i => by
        by_cases h : i = ⟨r, hr⟩
        · subst h; simp
        · have hv : i.val ≠ r := fun h' => h (Fin.ext h')
          simp [h, hv]
      simp_rw [hrew]
      simp
    exact hsingle

lemma sparseDot_eq_sum {n : ℕ} (c₁ c₂ : List (ℕ × ℤ))
    (h1 : sparseInBounds n c₁ = true) :
    ∑ i : Fin n, sparseLookup i.val c₁ * sparseLookup i.val c₂ = sparseDot c₁ c₂ := by
  have h := sparseLookup_sum_mul (fun i : Fin n => sparseLookup i.val c₂) c₁ h1
  have hcomm : ∑ i : Fin n, sparseLookup i.val c₁ * sparseLookup i.val c₂ =
      ∑ i : Fin n, sparseLookup i.val c₂ * sparseLookup i.val c₁ :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm, h]
  unfold sparseDot
  have hfold : ∀ (l : List (ℕ × ℤ)) (init : ℤ),
      sparseInBounds n l = true →
      l.foldl (fun acc p => acc + if h : p.1 < n then sparseLookup p.1 c₂ * p.2 else 0) init =
      l.foldl (fun acc p => acc + p.2 * sparseLookup p.1 c₂) init := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons a tl ih =>
      intro init hb
      simp only [sparseInBounds, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [List.foldl_cons, dif_pos hb.1, mul_comm (sparseLookup a.1 c₂) a.2]
      exact ih _ hb.2
  exact hfold c₁ 0 h1

lemma sparseBilinear_eq_sum {n : ℕ} (M : ℕ → ℕ → ℤ) (c₁ c₂ : List (ℕ × ℤ))
    (h1 : sparseInBounds n c₁ = true) (h2 : sparseInBounds n c₂ = true) :
    ∑ i : Fin n, ∑ j : Fin n, sparseLookup i.val c₁ * M i.val j.val * sparseLookup j.val c₂ =
      sparseBilinear M c₁ c₂ := by
  have hinner : ∀ i : Fin n,
      ∑ j : Fin n, sparseLookup i.val c₁ * M i.val j.val * sparseLookup j.val c₂ =
        sparseLookup i.val c₁ * c₂.foldl (fun acc q => acc + M i.val q.1 * q.2) 0 := fun i => by
    have hmul : ∑ j : Fin n, sparseLookup i.val c₁ * M i.val j.val * sparseLookup j.val c₂ =
        sparseLookup i.val c₁ * ∑ j : Fin n, M i.val j.val * sparseLookup j.val c₂ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [hmul, sparseLookup_sum_mul (fun j : Fin n => M i.val j.val) c₂ h2]
    congr 1
    have hfold : ∀ (l : List (ℕ × ℤ)) (init : ℤ),
        sparseInBounds n l = true →
        l.foldl (fun acc q => acc + if h : q.1 < n then M i.val q.1 * q.2 else 0) init =
        l.foldl (fun acc q => acc + M i.val q.1 * q.2) init := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons a tl ih =>
        intro init hb
        simp only [sparseInBounds, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [List.foldl_cons, dif_pos hb.1]
        exact ih _ hb.2
    exact hfold c₂ 0 h2
  simp_rw [hinner]
  have hcomm : ∑ i : Fin n, sparseLookup i.val c₁ * c₂.foldl (fun acc q => acc + M i.val q.1 * q.2) 0 =
      ∑ i : Fin n, c₂.foldl (fun acc q => acc + M i.val q.1 * q.2) 0 * sparseLookup i.val c₁ :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm, sparseLookup_sum_mul _ c₁ h1]
  unfold sparseBilinear
  have hfold : ∀ (l : List (ℕ × ℤ)) (init : ℤ),
      sparseInBounds n l = true →
      l.foldl (fun acc p => acc + if h : p.1 < n then
        c₂.foldl (fun acc2 q => acc2 + M p.1 q.1 * q.2) 0 * p.2 else 0) init =
      l.foldl (fun acc p => acc + p.2 * c₂.foldl (fun acc2 q => acc2 + M p.1 q.1 * q.2) 0) init := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons a tl ih =>
      intro init hb
      simp only [sparseInBounds, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [List.foldl_cons, dif_pos hb.1, mul_comm _ a.2]
      exact ih _ hb.2
  exact hfold c₁ 0 h1

lemma dotList_eq_sum {m : ℕ} (a b : List ℤ) (ha : a.length = m) (hb : b.length = m) :
    dotList a b = ∑ k : Fin m, a.getD k.val 0 * b.getD k.val 0 := by
  induction m generalizing a b with
  | zero =>
    cases a with
    | nil => cases b <;> simp [dotList] at *
    | cons => simp at ha
  | succ m ih =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hb
        rw [dotList, ih xs ys ha hb, Fin.sum_univ_succ]
        simp [List.getD]

lemma mulList_length (a b : List ℤ) (h : a.length = b.length) :
    (mulList a b).length = a.length := by
  induction a generalizing b with
  | nil => cases b <;> simp [mulList] at *
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys => simp [mulList, ih ys (by simpa using h)]

lemma mulList_getD (a b : List ℤ) (k : ℕ) (hk : k < a.length) (h : a.length = b.length) :
    (mulList a b).getD k 0 = a.getD k 0 * b.getD k 0 := by
  induction a generalizing b k with
  | nil => simp at hk
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      cases k with
      | zero => simp [mulList, List.getD]
      | succ k' =>
        simp only [mulList, List.getD_cons_succ]
        exact ih ys k' (by simpa using hk) (by simpa using h)

/-! ## Rational Argument-Reduced `exp (-x)` Upper Bound -/

/-- Exact rational Taylor sum `∑_{i=0}^{N-1} (x / 2^k)^i / i!`. -/
def taylorExpQ (x : ℚ) (k N : ℕ) : ℚ :=
  let y := x / (2 ^ k : ℚ)
  let rec go : ℕ → ℚ → ℚ → ℚ
    | 0, _, acc => acc
    | n + 1, term, acc =>
      let idx := N - (n + 1)
      let nextTerm := if idx = 0 then 1 else term * y / (idx : ℚ)
      go n nextTerm (acc + nextTerm)
  go N 1 0

/-- Simpler direct recursive definition of `∑_{i=0}^{N-1} (x / 2^k)^i / i!` for trivial casting. -/
def taylorSumQ (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => taylorSumQ y n + y ^ n / (n.factorial : ℚ)

lemma taylorSumQ_cast (y : ℚ) : ∀ N : ℕ,
    ((taylorSumQ y N : ℚ) : ℝ) = ∑ i ∈ Finset.range N, (y : ℝ) ^ i / (i.factorial : ℝ)
  | 0 => by simp [taylorSumQ]
  | n + 1 => by
    simp only [taylorSumQ, Finset.sum_range_succ, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, taylorSumQ_cast y n]

/-- Exact rational upper bound on `exp (-x)` (`x ≥ 0`) using argument reduction `2^k` and `N` terms:
`((taylorSumQ (x / 2^k) N) ^ (2^k))⁻¹`. -/
def ratExpNegUpper (x : ℚ) (k N : ℕ) : ℚ :=
  ((taylorSumQ (x / (2 ^ k : ℚ)) N) ^ (2 ^ k))⁻¹

lemma exp_neg_le_ratExpNegUpper {x : ℚ} (hx : 0 ≤ x) (k N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-(x : ℝ)) ≤ (ratExpNegUpper x k N : ℝ) := by
  have h1 := exp_neg_div_pow2_upper (by exact_mod_cast hx : (0 : ℝ) ≤ (x : ℝ)) k N hN
  unfold ratExpNegUpper
  push_cast
  rw [taylorSumQ_cast]
  simpa using h1

/-- Exact rational lower bound on `exp (-x)` (`0 ≤ x ≤ 2^k`, `0 < N`) via `Real.exp_bound'`:
`((taylorSumQ (x/2^k) N + (x/2^k)^N * (N + 1) / (N! * N)) ^ (2^k))⁻¹`. -/
def ratExpNegLower (x : ℚ) (k N : ℕ) : ℚ :=
  let y := x / (2 ^ k : ℚ)
  ((taylorSumQ y N + y ^ N * ((N : ℚ) + 1) / ((N.factorial : ℚ) * (N : ℚ))) ^ (2 ^ k))⁻¹

lemma ratExpNegLower_le_exp_neg {x : ℚ} (hx : 0 ≤ x) (k N : ℕ) (hN : 0 < N)
    (hle1 : x / (2 ^ k : ℚ) ≤ 1) :
    (ratExpNegLower x k N : ℝ) ≤ Real.exp (-(x : ℝ)) := by
  have h1 := exp_neg_div_pow2_lower (by exact_mod_cast hx : (0 : ℝ) ≤ (x : ℝ)) k N hN
    (by exact_mod_cast hle1)
  unfold ratExpNegLower
  push_cast
  rw [taylorSumQ_cast]
  simpa using h1

/-! ## General 6-Block Gershgorin Certificate Structure & Soundness -/

/-- A single verified symmetry block of size `m`:
- `offset`: starting column index in `Fin 128`
- `dim`: block dimension `m`
- `diagD`: integer diagonal norms `D_b` (`length = m`)
- `Hb`: integer rows of `B_bᵀ * H8ShiftInt * B_b` (`m × m`)
- `Ccols`: integer columns of approximate generalized eigenvectors `C_b` (`m × m`, scaled by `S`)
- `xlo`: rational lower bounds on `6 * (λ + 12)` for this block (`length = m`, all `≥ 0`). -/
structure BlockCert where
  offset : ℕ
  dim : ℕ
  diagD : List ℤ
  Hb : List (List ℤ)
  Ccols : List (List ℤ)
  xlo : List ℚ

/-- Check that a list of `BlockCert`s cleanly partitions `0..127`. -/
def checkPartition (blocks : List BlockCert) : Bool :=
  let rec go (pos : ℕ) : List BlockCert → Bool
    | [] => decide (pos = 128)
    | b :: rest => decide (b.offset = pos) && go (pos + b.dim) rest
  go 0 blocks

/-- Check that sparse basis `Bcols` (length 128) satisfies `Bᵀ B = diag(D)` and
`Bᵀ * H8ShiftInt * B = blockdiag(Hb)`. -/
def checkBasisAndBlocks (g_num h_num : ℤ) (twist : Bool)
    (Bcols : List (List (ℕ × ℤ))) (blocks : List BlockCert) : Bool :=
  decide (Bcols.length = 128) &&
  Bcols.all (sparseInBounds 128) &&
  checkPartition blocks &&
  -- Check Bᵀ B = diag(D)
  let Dfull : List ℤ := blocks.flatMap (·.diagD)
  decide (Dfull.length = 128) &&
  (List.range 128).all (fun i =>
    let ci := Bcols.getD i []
    (List.range 128).all fun j =>
      let cj := Bcols.getD j []
      let expected : ℤ := if i = j then Dfull.getD i 0 else 0
      decide (sparseDot ci cj = expected)) &&
  -- Check Bᵀ * H8ShiftInt * B = blockdiag(Hb)
  let M := H8ShiftIntFast g_num h_num twist
  (List.range 128).all (fun i =>
    let ci := Bcols.getD i []
    (List.range 128).all fun j =>
      let cj := Bcols.getD j []
      let expected : ℤ :=
        (match blocks.find? (fun b => decide (b.offset ≤ i) && decide (i < b.offset + b.dim)) with
        | some b =>
          if b.offset ≤ j ∧ j < b.offset + b.dim then
            (b.Hb.getD (i - b.offset) ([] : List ℤ)).getD (j - b.offset) (0 : ℤ)
          else (0 : ℤ)
        | none => (0 : ℤ))
      @decide (sparseBilinear M ci cj = expected) (Int.decEq _ _))

/-- Check a single block's Gershgorin inequalities for `G1 = Cᵀ D C` and `G2 = Cᵀ Hb C`
against global Gram defect bound `e1_max < S^2` and rational lower bounds `xlo`. -/
def checkSingleBlockGershgorin (S2 e1_max : ℤ) (b : BlockCert) : Bool :=
  decide (b.diagD.length = b.dim) &&
  decide (b.Hb.length = b.dim) &&
  b.Hb.all (fun row => decide (row.length = b.dim)) &&
  decide (b.Ccols.length = b.dim) &&
  b.Ccols.all (fun col => decide (col.length = b.dim)) &&
  decide (b.xlo.length = b.dim) &&
  -- Precompute D * C_j and Hb * C_j for each column j
  let DC : List (List ℤ) := b.Ccols.map (mulList b.diagD)
  let HC : List (List ℤ) := b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))
  -- Check G1 row-sum defect ≤ e1_max and G2 row lower bound ≥ xlo
  (List.range b.dim).all fun i =>
    let ci := b.Ccols.getD i []
    let g1_err : ℤ :=
      (List.range b.dim).foldl (fun acc j =>
        let entry := dotList ci (DC.getD j [])
        if i = j then acc + |entry - S2| else acc + |entry|) 0
    let g2_diag : ℤ := dotList ci (HC.getD i [])
    let g2_off : ℤ :=
      (List.range b.dim).foldl (fun acc j =>
        if i = j then acc else acc + |dotList ci (HC.getD j [])|) 0
    let xi : ℚ := b.xlo.getD i 0
    decide (g1_err ≤ e1_max) &&
    decide (0 ≤ g2_diag - g2_off) &&
    decide (0 ≤ xi) &&
    decide (xi * ((128 * (S2 + e1_max) : ℤ) : ℚ) ≤ ((6 * (g2_diag - g2_off) : ℤ) : ℚ))

/-- Sum rational upper bounds on `exp (-xlo_i)` across all blocks (with cutoff `45`). -/
def sumBlockExpUpper (blocks : List BlockCert) : ℚ :=
  let tailVal : ℚ := ratExpNegUpper 45 6 10
  blocks.foldl (fun acc b =>
    b.xlo.foldl (fun acc2 x =>
      acc2 + if (45 : ℚ) ≤ x then tailVal else ratExpNegUpper x 6 10) acc) 0

/-- Complete computable certificate check for one 128-dim `L = 8` Ising block. -/
def verifyH8Cert (g_num h_num : ℤ) (twist : Bool)
    (S e1_max : ℤ) (Bcols : List (List (ℕ × ℤ))) (blocks : List BlockCert) (U : ℚ) : Bool :=
  decide (0 < S) &&
  decide (0 ≤ e1_max) &&
  decide (e1_max < S * S) &&
  checkBasisAndBlocks g_num h_num twist Bcols blocks &&
  blocks.all (checkSingleBlockGershgorin (S * S) e1_max) &&
  decide (sumBlockExpUpper blocks ≤ U)

/-! ## Soundness Theorem Connecting `verifyH8Cert = true` to `matZ` -/

/-- Helper: extract the unique block containing index `i < 128` from a valid partition. -/
private lemma partition_block_props {blocks : List BlockCert} (hp : checkPartition blocks = true) :
    (∀ b ∈ blocks, b.offset + b.dim ≤ 128) ∧
    (∀ i : Fin 128, ∃ b ∈ blocks, b.offset ≤ i.val ∧ i.val < b.offset + b.dim) ∧
    (∀ b₁ ∈ blocks, ∀ b₂ ∈ blocks, ∀ i : ℕ,
      b₁.offset ≤ i → i < b₁.offset + b₁.dim →
      b₂.offset ≤ i → i < b₂.offset + b₂.dim → b₁ = b₂) := by
  have hgo : ∀ (pos : ℕ) (bs : List BlockCert),
      checkPartition.go pos bs = true →
      (∀ b ∈ bs, pos ≤ b.offset ∧ b.offset + b.dim ≤ 128) ∧
      (∀ i : ℕ, pos ≤ i → i < 128 → ∃ b ∈ bs, b.offset ≤ i ∧ i < b.offset + b.dim) ∧
      (∀ b₁ ∈ bs, ∀ b₂ ∈ bs, ∀ i : ℕ,
        b₁.offset ≤ i → i < b₁.offset + b₁.dim →
        b₂.offset ≤ i → i < b₂.offset + b₂.dim → b₁ = b₂) := by
    intro pos bs
    induction bs generalizing pos with
    | nil =>
      intro h
      simp only [checkPartition.go, decide_eq_true_eq] at h
      refine ⟨fun _ hb => absurd hb List.not_mem_nil, fun i hi1 hi2 => by omega,
        fun _ hb => absurd hb List.not_mem_nil⟩
    | cons hd tl ih =>
      intro h
      simp only [checkPartition.go, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hoff, htl⟩
      rcases ih (pos + hd.dim) htl with ⟨hbound, hcov, hdisj⟩
      have hhd_le : pos + hd.dim ≤ 128 := by
        cases tl with
        | nil => simp [checkPartition.go] at htl; omega
        | cons nxt _ =>
          have := (hbound nxt List.mem_cons_self).1
          have := (hbound nxt List.mem_cons_self).2
          omega
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hmem
        · exact ⟨by omega, by omega⟩
        · have := hbound b hmem; exact ⟨by omega, this.2⟩
      · intro i hi1 hi2
        by_cases hlt : i < pos + hd.dim
        · exact ⟨hd, List.mem_cons_self, by omega, by omega⟩
        · rcases hcov i (by omega) hi2 with ⟨b, hb, h1, h2⟩
          exact ⟨b, List.mem_cons_of_mem hd hb, h1, h2⟩
      · intro b₁ hb₁ b₂ hb₂ i h1a h1b h2a h2b
        rcases List.mem_cons.mp hb₁ with rfl | h1m <;> rcases List.mem_cons.mp hb₂ with rfl | h2m
        · rfl
        · exfalso; have := (hbound b₂ h2m).1; omega
        · exfalso; have := (hbound b₁ h1m).1; omega
        · exact hdisj b₁ h1m b₂ h2m i h1a h1b h2a h2b
  rcases hgo 0 blocks hp with ⟨h1, h2, h3⟩
  exact ⟨fun b hb => (h1 b hb).2, fun i => h2 i.val (Nat.zero_le _) i.isLt, h3⟩

/-- Construct the full `128 × 128` block-diagonal integer eigenvector matrix `C_mat` from `blocks`. -/
def blockDiagC (blocks : List BlockCert) (i j : Fin 128) : ℤ :=
  match blocks.find? (fun b => decide (b.offset ≤ i.val) && decide (i.val < b.offset + b.dim)) with
  | some b =>
    if b.offset ≤ j.val ∧ j.val < b.offset + b.dim then
      (b.Ccols.getD (j.val - b.offset) []).getD (i.val - b.offset) 0
    else 0
  | none => 0

/-- Construct the full `128`-vector of `xlo` values from `blocks`. -/
def blocksXlo (blocks : List BlockCert) (i : Fin 128) : ℚ :=
  match blocks.find? (fun b => decide (b.offset ≤ i.val) && decide (i.val < b.offset + b.dim)) with
  | some b => b.xlo.getD (i.val - b.offset) 0
  | none => 0

lemma find_block_eq {blocks : List BlockCert} (hp : checkPartition blocks = true)
    {b : BlockCert} (hb : b ∈ blocks) {i : ℕ} (hi1 : b.offset ≤ i) (hi2 : i < b.offset + b.dim) :
    blocks.find? (fun b' => decide (b'.offset ≤ i) && decide (i < b'.offset + b'.dim)) = some b := by
  rcases partition_block_props hp with ⟨_, _, hdisj⟩
  cases h : blocks.find? (fun b' => decide (b'.offset ≤ i) && decide (i < b'.offset + b'.dim)) with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp h b hb
    simp [hi1, hi2] at hnone
  | some b' =>
    have hmem : b' ∈ blocks := List.mem_of_find?_eq_some h
    have hpred := List.find?_some h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
    congr 1
    exact hdisj b' hmem b hb i hpred.1 hpred.2 hi1 hi2

lemma list_getD_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i]'hi := by
  simp [List.getD, List.getElem?_eq_getElem hi]

lemma list_getD_of_ge {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

lemma foldl_sum_range_int (f : ℕ → ℤ) :
    ∀ n (init : ℤ), (List.range n).foldl (fun acc k => acc + f k) init =
      init + ∑ k : Fin n, f k.val := fun n init => by
  rw [foldl_add_eq_sum_range, Finset.sum_range]

lemma foldl_list_add_rat (f : ℚ → ℚ) :
    ∀ (l : List ℚ) (init : ℚ),
      l.foldl (fun acc x => acc + f x) init = init + ∑ k : Fin l.length, f (l.getD k.val 0)
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [foldl_list_add_rat f xs (init + f x)]
    ring

lemma sumBlockExpUpper_eq {blocks : List BlockCert} (hp : checkPartition blocks = true)
    (hlen : ∀ b ∈ blocks, b.xlo.length = b.dim) :
    sumBlockExpUpper blocks =
      ∑ i : Fin 128,
        if (45 : ℚ) ≤ blocksXlo blocks i then ratExpNegUpper 45 6 10
        else ratExpNegUpper (blocksXlo blocks i) 6 10 := by
  let g : ℚ → ℚ := fun x => if (45 : ℚ) ≤ x then ratExpNegUpper 45 6 10 else ratExpNegUpper x 6 10
  let fNat : ℕ → ℚ := fun k =>
    if hk : k < 128 then g (blocksXlo blocks ⟨k, hk⟩) else 0
  have hgo : ∀ (pos : ℕ) (bs : List BlockCert) (init : ℚ),
      checkPartition.go pos bs = true →
      (∀ b ∈ bs, b ∈ blocks) →
      (∀ b ∈ bs, b.xlo.length = b.dim) →
      bs.foldl (fun acc b => b.xlo.foldl (fun acc2 x => acc2 + g x) acc) init =
        init + ∑ k ∈ Finset.Ico pos 128, fNat k := by
    intro pos bs
    induction bs generalizing pos with
    | nil =>
      intro init hgo_nil _ _
      simp only [checkPartition.go, decide_eq_true_eq] at hgo_nil
      subst hgo_nil
      simp
    | cons hd tl ih =>
      intro init hgo_cons hsub hlen_bs
      simp only [checkPartition.go, Bool.and_eq_true, decide_eq_true_eq] at hgo_cons
      rcases hgo_cons with ⟨hoff, htl⟩
      have hhd_mem : hd ∈ blocks := hsub hd List.mem_cons_self
      have hhd_le : pos + hd.dim ≤ 128 := by
        have := (partition_block_props hp).1 hd hhd_mem; omega
      have hhd_len : hd.xlo.length = hd.dim := hlen_bs hd List.mem_cons_self
      simp only [List.foldl_cons]
      rw [ih (pos + hd.dim) _ htl (fun b hb => hsub b (List.mem_cons_of_mem hd hb))
        (fun b hb => hlen_bs b (List.mem_cons_of_mem hd hb))]
      rw [foldl_list_add_rat g hd.xlo init]
      have hsplit : ∑ k ∈ Finset.Ico pos 128, fNat k =
          (∑ k ∈ Finset.Ico pos (pos + hd.dim), fNat k) +
          (∑ k ∈ Finset.Ico (pos + hd.dim) 128, fNat k) :=
        (Finset.sum_Ico_consecutive fNat (Nat.le_add_right pos hd.dim) hhd_le).symm
      rw [hsplit]
      have hseg : ∑ k : Fin hd.xlo.length, g (hd.xlo.getD k.val 0) =
          ∑ k ∈ Finset.Ico pos (pos + hd.dim), fNat k := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
          ← Finset.sum_range (f := fun k => g (hd.xlo.getD k 0)), hhd_len]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjlt : j < hd.dim := Finset.mem_range.mp hj
        have hlt : pos + j < 128 := by omega
        simp only [fNat, dif_pos hlt]
        congr 1
        unfold blocksXlo
        dsimp only
        rw [find_block_eq hp hhd_mem (by omega) (by omega)]
        congr 1; omega
      rw [hseg]; ring
  have hmain := hgo 0 blocks 0 hp (fun _ hb => hb) hlen
  unfold sumBlockExpUpper
  change blocks.foldl (fun acc b => b.xlo.foldl (fun acc2 x => acc2 + g x) acc) 0 = _
  rw [hmain, zero_add, Nat.Ico_zero_eq_range, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [fNat, i.isLt, g]

lemma flatMap_diagD_getD {blocks : List BlockCert} (hp : checkPartition blocks = true)
    (hlen : ∀ b ∈ blocks, b.diagD.length = b.dim)
    {b : BlockCert} (hb : b ∈ blocks) {i : ℕ} (hi1 : b.offset ≤ i) (hi2 : i < b.offset + b.dim) :
    (blocks.flatMap (·.diagD)).getD i 0 = b.diagD.getD (i - b.offset) 0 := by
  have hgo : ∀ (pos : ℕ) (bs : List BlockCert),
      checkPartition.go pos bs = true →
      (∀ b' ∈ bs, b'.diagD.length = b'.dim) →
      ∀ b' ∈ bs, ∀ i, b'.offset ≤ i → i < b'.offset + b'.dim →
        (bs.flatMap (·.diagD)).getD (i - pos) 0 = b'.diagD.getD (i - b'.offset) 0 := by
    intro pos bs
    induction bs generalizing pos with
    | nil => intro _ _ _ hb'; exact absurd hb' List.not_mem_nil
    | cons hd tl ih =>
      intro hgo_c hlen_c b' hb' i h1 h2
      simp only [checkPartition.go, Bool.and_eq_true, decide_eq_true_eq] at hgo_c
      rcases hgo_c with ⟨hoff, htl⟩
      have hhd_len : hd.diagD.length = hd.dim := hlen_c hd List.mem_cons_self
      simp only [List.flatMap_cons]
      rcases List.mem_cons.mp hb' with rfl | hmem
      · have hlt : i - pos < b'.diagD.length := by omega
        rw [list_getD_of_lt _ _ (by rw [List.length_append]; omega), List.getElem_append_left hlt,
          ← list_getD_of_lt _ _ hlt, hoff]
      · have hge_pos : pos + hd.dim ≤ b'.offset := by
          have hge : ∀ p (l : List BlockCert), checkPartition.go p l = true → ∀ x ∈ l, p ≤ x.offset := by
            intro p l; induction l generalizing p with
            | nil => intro _ _ hx; exact absurd hx List.not_mem_nil
            | cons a as iha =>
              intro h x hx
              simp only [checkPartition.go, Bool.and_eq_true, decide_eq_true_eq] at h
              rcases List.mem_cons.mp hx with rfl | hxm
              · omega
              · have := iha (p + a.dim) h.2 x hxm; omega
          exact hge (pos + hd.dim) tl htl b' hmem
        have hge_len : hd.diagD.length ≤ i - pos := by omega
        have hsub : i - pos - hd.diagD.length = i - (pos + hd.dim) := by omega
        have htl_res := ih (pos + hd.dim) htl (fun x hx => hlen_c x (List.mem_cons_of_mem hd hx))
          b' hmem i h1 h2
        by_cases hlt_tot : i - pos < (hd.diagD ++ tl.flatMap (·.diagD)).length
        · have hlt_tl : i - pos - hd.diagD.length < (tl.flatMap (·.diagD)).length := by
            rw [List.length_append] at hlt_tot; omega
          rw [list_getD_of_lt _ _ hlt_tot, List.getElem_append_right hge_len,
            ← list_getD_of_lt _ _ hlt_tl, hsub]
          exact htl_res
        · have hge_tl : (tl.flatMap (·.diagD)).length ≤ i - (pos + hd.dim) := by
            rw [List.length_append] at hlt_tot; omega
          rw [list_getD_of_ge _ _ (by omega)]
          have hdef : (tl.flatMap (·.diagD)).getD (i - (pos + hd.dim)) 0 = 0 :=
            list_getD_of_ge _ _ hge_tl
          rw [← htl_res, hdef]
  have := hgo 0 blocks hp hlen b hb i hi1 hi2
  simpa using this

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- **Master Soundness Theorem for 6-Block Gershgorin `L = 8` Certificates**:
if `verifyH8Cert g_num h_num twist S e1_max Bcols blocks U = true`, then
`matZ (H_ising 8 (g_num/128) (h_num/128) twist false) _ 6 ≤ exp 72 * U`. -/
theorem certify_H8_matZ_upper (g_num h_num : ℤ) (twist : Bool)
    (S e1_max : ℤ) (Bcols : List (List (ℕ × ℤ))) (blocks : List BlockCert) (U : ℚ)
    (hcert : verifyH8Cert g_num h_num twist S e1_max Bcols blocks U = true) :
    matZ (H_ising 8 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) twist false)
      (H_ising_isHermitian 8 _ _ twist false) 6 ≤
      Real.exp 72 * (U : ℝ) := by
  -- Unpack all boolean checks from `verifyH8Cert`
  unfold verifyH8Cert at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨hS_pos, he1_nn⟩, he1_lt⟩, hbasis⟩, hblocks_all⟩, hsumU⟩
  unfold checkBasisAndBlocks at hbasis
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbasis
  rcases hbasis with ⟨⟨⟨hBlen, hBin⟩, hpart⟩, ⟨hDlen, hBTB⟩, hBHB⟩
  have hblock_ok : ∀ b ∈ blocks, checkSingleBlockGershgorin (S * S) e1_max b = true :=
    fun b hb => List.all_eq_true.mp hblocks_all b hb
  have hBcol_in : ∀ j : Fin 128, sparseInBounds 128 (Bcols.getD j.val []) = true := fun j => by
    have hj : j.val < Bcols.length := by omega
    rw [list_getD_of_lt _ _ hj]
    exact List.all_eq_true.mp hBin _ (List.getElem_mem hj)
  have hdiag_len : ∀ b ∈ blocks, b.diagD.length = b.dim := fun b hb => by
    have h := hblock_ok b hb; unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1.1.1.1
  have hxlo_len : ∀ b ∈ blocks, b.xlo.length = b.dim := fun b hb => by
    have h := hblock_ok b hb; unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
  have hC_len : ∀ b ∈ blocks, b.Ccols.length = b.dim := fun b hb => by
    have h := hblock_ok b hb; unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1.2
  have hCcol_len : ∀ b ∈ blocks, ∀ j : Fin b.dim, (b.Ccols.getD j.val []).length = b.dim := fun b hb j => by
    have h := hblock_ok b hb; unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hj : j.val < b.Ccols.length := by rw [hC_len b hb]; exact j.isLt
    rw [list_getD_of_lt _ _ hj]
    have := List.all_eq_true.mp h.1.1.2 _ (List.getElem_mem hj)
    simpa using this
  have hHb_len : ∀ b ∈ blocks, b.Hb.length = b.dim := fun b hb => by
    have h := hblock_ok b hb; unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1.1.1.2
  have hHbrow_len : ∀ b ∈ blocks, ∀ i : Fin b.dim, (b.Hb.getD i.val []).length = b.dim := fun b hb i => by
    have h := hblock_ok b hb; unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hi : i.val < b.Hb.length := by rw [hHb_len b hb]; exact i.isLt
    rw [list_getD_of_lt _ _ hi]
    have := List.all_eq_true.mp h.1.1.1.1.2 _ (List.getElem_mem hi)
    simpa using this
  -- Build integer & real matrices B, C, Q = (1 / S) • (B * C)
  let B_int : Matrix (Fin 128) (Fin 128) ℤ :=
    Matrix.of fun i j => sparseLookup i.val (Bcols.getD j.val [])
  let C_int : Matrix (Fin 128) (Fin 128) ℤ :=
    Matrix.of fun i j => blockDiagC blocks i j
  let B_R : Matrix (Fin 128) (Fin 128) ℝ := B_int.map Int.cast
  let C_R : Matrix (Fin 128) (Fin 128) ℝ := C_int.map Int.cast
  let Q : Matrix (Fin 128) (Fin 128) ℝ := ((S : ℝ)⁻¹) • (B_R * C_R)
  let H := H_ising 8 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) twist false
  let hH := H_ising_isHermitian 8 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) twist false
  let Hs := H + (12 : ℝ) • (1 : Matrix (Fin 128) (Fin 128) ℝ)
  have hS_R_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS_pos
  have hS2_R_pos : (0 : ℝ) < ((S * S : ℤ) : ℝ) := by push_cast; positivity
  -- B_intᵀ * B_int = diag(Dfull)
  have hBTB_eq : ∀ r s : Fin 128,
      ∑ i : Fin 128, B_int i r * B_int i s =
        if r = s then (blocks.flatMap (·.diagD)).getD r.val 0 else 0 := by
    intro r s
    have h1 := sparseDot_eq_sum (Bcols.getD r.val []) (Bcols.getD s.val []) (hBcol_in r)
    have hr_mem : r.val ∈ List.range 128 := List.mem_range.mpr r.isLt
    have hs_mem : s.val ∈ List.range 128 := List.mem_range.mpr s.isLt
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp hBTB r.val hr_mem) s.val hs_mem
    simp only [decide_eq_true_eq] at hchk
    change ∑ i : Fin 128, sparseLookup i.val (Bcols.getD r.val []) *
        sparseLookup i.val (Bcols.getD s.val []) = _
    rw [h1, hchk]
    by_cases hrs : r = s
    · subst hrs; simp
    · have hne : r.val ≠ s.val := fun h => hrs (Fin.ext h)
      simp [hrs, hne]
  -- B_intᵀ * H8ShiftInt * B_int = blockdiag(Hb)
  have hBHB_eq : ∀ r s : Fin 128,
      ∑ i : Fin 128, ∑ j : Fin 128, B_int i r * H8ShiftInt g_num h_num twist i j * B_int j s =
        match blocks.find? (fun b => decide (b.offset ≤ r.val) && decide (r.val < b.offset + b.dim)) with
        | some b =>
          if b.offset ≤ s.val ∧ s.val < b.offset + b.dim then
            (b.Hb.getD (r.val - b.offset) []).getD (s.val - b.offset) 0
          else 0
        | none => 0 := by
    intro r s
    have hr_mem : r.val ∈ List.range 128 := List.mem_range.mpr r.isLt
    have hs_mem : s.val ∈ List.range 128 := List.mem_range.mpr s.isLt
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp hBHB r.val hr_mem) s.val hs_mem
    simp only [decide_eq_true_eq] at hchk
    have h1 := sparseBilinear_eq_sum (H8ShiftIntFast g_num h_num twist)
      (Bcols.getD r.val []) (Bcols.getD s.val []) (hBcol_in r) (hBcol_in s)
    have heq : ∑ i : Fin 128, ∑ j : Fin 128, B_int i r * H8ShiftInt g_num h_num twist i j * B_int j s =
        ∑ i : Fin 128, ∑ j : Fin 128,
          sparseLookup i.val (Bcols.getD r.val []) *
            H8ShiftIntFast g_num h_num twist i.val j.val *
            sparseLookup j.val (Bcols.getD s.val []) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [H8ShiftIntFast_eq]; rfl
    rw [heq, h1, hchk]
  -- Evaluate entries of Qᵀ * Q and Qᵀ * Hs * Q block by block!
  rcases partition_block_props hpart with ⟨hble, hbcov, hbdisj⟩
  have hQTQ_entry : ∀ i j : Fin 128, ∀ b ∈ blocks,
      b.offset ≤ i.val → i.val < b.offset + b.dim →
      (Qᵀ * Q) i j =
        if b.offset ≤ j.val ∧ j.val < b.offset + b.dim then
          (dotList (b.Ccols.getD (i.val - b.offset) [])
            (mulList b.diagD (b.Ccols.getD (j.val - b.offset) [])) : ℝ) / ((S * S : ℤ) : ℝ)
        else 0 := by
    intro i j b hb hi1 hi2
    have hQTQ_expand : (Qᵀ * Q) i j =
        ((∑ r : Fin 128, ∑ s : Fin 128,
          C_int r i * (∑ k : Fin 128, B_int k r * B_int k s) * C_int s j : ℤ) : ℝ) / ((S * S : ℤ) : ℝ) := by
      dsimp only [Q, B_R, C_R]
      simp only [Matrix.transpose_smul, Matrix.smul_apply,
        smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      rw [div_eq_mul_inv, Int.cast_mul, mul_inv]
      have hpull :
          (∑ x : Fin 128,
            ((S : ℝ)⁻¹ * ∑ r : Fin 128, (B_int x r : ℝ) * (C_int r i : ℝ)) *
            ((S : ℝ)⁻¹ * ∑ s : Fin 128, (B_int x s : ℝ) * (C_int s j : ℝ))) =
          (S : ℝ)⁻¹ * ((S : ℝ)⁻¹ * ∑ x : Fin 128,
            (∑ r : Fin 128, (B_int x r : ℝ) * (C_int r i : ℝ)) *
            (∑ s : Fin 128, (B_int x s : ℝ) * (C_int s j : ℝ))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [hpull]
      have hrearr :
          (S : ℝ)⁻¹ * ((S : ℝ)⁻¹ * ∑ x : Fin 128,
            (∑ r : Fin 128, (B_int x r : ℝ) * (C_int r i : ℝ)) *
            (∑ s : Fin 128, (B_int x s : ℝ) * (C_int s j : ℝ))) =
          (∑ r : Fin 128, ∑ s : Fin 128,
            (C_int r i : ℝ) * (∑ x : Fin 128, (B_int x r : ℝ) * (B_int x s : ℝ)) * (C_int s j : ℝ)) *
            ((S : ℝ)⁻¹ * (S : ℝ)⁻¹) := by
        have hsum_eq :
            ∑ x : Fin 128,
              (∑ r : Fin 128, (B_int x r : ℝ) * (C_int r i : ℝ)) *
              (∑ s : Fin 128, (B_int x s : ℝ) * (C_int s j : ℝ)) =
            ∑ r : Fin 128, ∑ s : Fin 128,
              (C_int r i : ℝ) * (∑ x : Fin 128, (B_int x r : ℝ) * (B_int x s : ℝ)) * (C_int s j : ℝ) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [hsum_eq]; ring
      push_cast
      exact hrearr
    rw [hQTQ_expand]
    simp_rw [hBTB_eq]
    have hdiag_sum :
        (∑ r : Fin 128, ∑ s : Fin 128,
          C_int r i * (if r = s then (blocks.flatMap (·.diagD)).getD r.val 0 else 0) * C_int s j) =
        ∑ r : Fin 128, C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int r j) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have h1 : ∀ s : Fin 128,
          C_int r i * (if r = s then (blocks.flatMap (·.diagD)).getD r.val 0 else 0) * C_int s j =
            if s = r then C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int s j) else 0 := fun s => by
        by_cases h : s = r
        · subst h; simp; ring
        · simp [h, Ne.symm h]
      simp_rw [h1]
      simp
    rw [hdiag_sum]
    have hCi_zero : ∀ r : Fin 128, ¬ (b.offset ≤ r.val ∧ r.val < b.offset + b.dim) → C_int r i = 0 := by
      intro r hr
      rcases hbcov r with ⟨b', hb', hr1, hr2⟩
      have hne : b' ≠ b := fun heq => hr (heq ▸ ⟨hr1, hr2⟩)
      simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb' hr1 hr2]
      have hnoti : ¬ (b'.offset ≤ i.val ∧ i.val < b'.offset + b'.dim) := fun ⟨h1, h2⟩ =>
        hne (hbdisj b' hb' b hb i.val h1 h2 hi1 hi2)
      simp [hnoti]
    by_cases hj : b.offset ≤ j.val ∧ j.val < b.offset + b.dim
    · rw [if_pos hj]
      congr 1; refine congrArg (Int.cast : ℤ → ℝ) ?_
      have hrestrict :
          (∑ r : Fin 128, C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int r j)) =
          ∑ k : Fin b.dim,
            (b.Ccols.getD (i.val - b.offset) []).getD k.val 0 *
              (b.diagD.getD k.val 0 * (b.Ccols.getD (j.val - b.offset) []).getD k.val 0) := by
        have h1 : (∑ r : Fin 128, C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int r j)) =
            ∑ r ∈ Finset.univ.filter (fun r : Fin 128 => b.offset ≤ r.val ∧ r.val < b.offset + b.dim),
              C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int r j) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun r : Fin 128 => b.offset ≤ r.val ∧ r.val < b.offset + b.dim)]
          have h0 : ∑ r ∈ Finset.univ.filter (fun r : Fin 128 => ¬ (b.offset ≤ r.val ∧ r.val < b.offset + b.dim)),
              C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int r j) = 0 :=
            Finset.sum_eq_zero fun r hr => by rw [hCi_zero r (Finset.mem_filter.mp hr).2, zero_mul]
          rw [h0, add_zero]
        rw [h1]
        refine Finset.sum_bij (fun (r : Fin 128) hr =>
            (⟨r.val - b.offset, by have := (Finset.mem_filter.mp hr).2; omega⟩ : Fin b.dim))
          (fun _ _ => Finset.mem_univ _)
          (fun r₁ hr₁ r₂ hr₂ heq => by
            have h1' := (Finset.mem_filter.mp hr₁).2
            have h2' := (Finset.mem_filter.mp hr₂).2
            have hv := congrArg Fin.val heq; dsimp at hv
            exact Fin.ext (by omega))
          (fun k _ => ⟨⟨b.offset + k.val, by have := hble b hb; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩,
            Fin.ext (by simp)⟩)
          (fun r hr => by
            rcases (Finset.mem_filter.mp hr).2 with ⟨hr1, hr2⟩
            simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb hr1 hr2,
              hi1, hi2, hj.1, hj.2, and_self, ↓reduceIte,
              flatMap_diagD_getD hpart hdiag_len hb hr1 hr2])
      rw [hrestrict, dotList_eq_sum (m := b.dim) _ _
        (hCcol_len b hb ⟨i.val - b.offset, by omega⟩)
        (by rw [mulList_length _ _ (by rw [hdiag_len b hb, hCcol_len b hb ⟨j.val - b.offset, by omega⟩])]; exact hdiag_len b hb)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulList_getD _ _ k.val (by rw [hdiag_len b hb]; exact k.isLt)
        (by rw [hdiag_len b hb, hCcol_len b hb ⟨j.val - b.offset, by omega⟩])]
    · rw [if_neg hj]
      have h0 : (∑ r : Fin 128, C_int r i * ((blocks.flatMap (·.diagD)).getD r.val 0 * C_int r j)) = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        by_cases hr : b.offset ≤ r.val ∧ r.val < b.offset + b.dim
        · have hCj : C_int r j = 0 := by
            simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb hr.1 hr.2]
            simp [hj]
          rw [hCj, mul_zero, mul_zero]
        · rw [hCi_zero r hr, zero_mul]
      rw [h0]; simp
  -- Similarly evaluate entries of Qᵀ * Hs * Q block by block!
  have hQHQ_entry : ∀ i j : Fin 128, ∀ b ∈ blocks,
      b.offset ≤ i.val → i.val < b.offset + b.dim →
      (Qᵀ * Hs * Q) i j =
        if b.offset ≤ j.val ∧ j.val < b.offset + b.dim then
          (dotList (b.Ccols.getD (i.val - b.offset) [])
            (b.Hb.map (fun row => dotList row (b.Ccols.getD (j.val - b.offset) []))) : ℝ) /
            ((128 * (S * S) : ℤ) : ℝ)
        else 0 := by
    intro i j b hb hi1 hi2
    have hQHQ_expand : (Qᵀ * Hs * Q) i j =
        ((∑ r : Fin 128, ∑ s : Fin 128,
          C_int r i * (∑ p : Fin 128, ∑ q : Fin 128,
            B_int p r * H8ShiftInt g_num h_num twist p q * B_int q s) * C_int s j : ℤ) : ℝ) /
          ((128 * (S * S) : ℤ) : ℝ) := by
      have hHs_entry : ∀ p q : Fin 128, Hs p q = (H8ShiftInt g_num h_num twist p q : ℝ) / 128 := fun p q => by
        dsimp only [Hs, H]
        rw [H8ShiftInt_cast]; field_simp [(by norm_num : (128 : ℝ) ≠ 0)]
      dsimp only [Q, B_R, C_R]
      simp only [Matrix.transpose_smul, Matrix.smul_apply,
        smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp_rw [hHs_entry]
      have h128 : (128 : ℝ) ≠ 0 := by norm_num
      have hS_ne : (S : ℝ) ≠ 0 := hS_R_pos.ne'
      have hpull :
          (∑ q : Fin 128,
            (∑ p : Fin 128, ((S : ℝ)⁻¹ * ∑ r : Fin 128, (B_int p r : ℝ) * (C_int r i : ℝ)) *
              ((H8ShiftInt g_num h_num twist p q : ℝ) / 128)) *
            ((S : ℝ)⁻¹ * ∑ s : Fin 128, (B_int q s : ℝ) * (C_int s j : ℝ))) =
          ((S : ℝ)⁻¹ * (S : ℝ)⁻¹) *
            ∑ q : Fin 128,
              (∑ p : Fin 128, (∑ r : Fin 128, (B_int p r : ℝ) * (C_int r i : ℝ)) *
                ((H8ShiftInt g_num h_num twist p q : ℝ) / 128)) *
              (∑ s : Fin 128, (B_int q s : ℝ) * (C_int s j : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        have hp :
            (∑ p : Fin 128, ((S : ℝ)⁻¹ * ∑ r : Fin 128, (B_int p r : ℝ) * (C_int r i : ℝ)) *
              ((H8ShiftInt g_num h_num twist p q : ℝ) / 128)) =
            (S : ℝ)⁻¹ * ∑ p : Fin 128, (∑ r : Fin 128, (B_int p r : ℝ) * (C_int r i : ℝ)) *
              ((H8ShiftInt g_num h_num twist p q : ℝ) / 128) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
        rw [hp]; ring
      refine hpull.trans ?_
      push_cast
      have hsum_eq :
          (∑ q : Fin 128,
            (∑ p : Fin 128, (∑ r : Fin 128, (B_int p r : ℝ) * (C_int r i : ℝ)) *
              ((H8ShiftInt g_num h_num twist p q : ℝ) / 128)) *
            (∑ s : Fin 128, (B_int q s : ℝ) * (C_int s j : ℝ))) =
          (∑ r : Fin 128, ∑ s : Fin 128,
            (C_int r i : ℝ) * (∑ p : Fin 128, ∑ q : Fin 128,
              (B_int p r : ℝ) * (H8ShiftInt g_num h_num twist p q : ℝ) * (B_int q s : ℝ)) *
            (C_int s j : ℝ)) / 128 := by
        rw [Finset.sum_div]
        simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        rw [Finset.sum_comm]
        -- Reorder 4 nested sums (q, p, r, s) -> (r, s, p, q)
        have hre : ∀ (F : Fin 128 → Fin 128 → Fin 128 → Fin 128 → ℝ),
            (∑ p : Fin 128, ∑ q : Fin 128, ∑ r : Fin 128, ∑ s : Fin 128, F p q r s) =
            ∑ r : Fin 128, ∑ s : Fin 128, ∑ p : Fin 128, ∑ q : Fin 128, F p q r s := fun F => by
          calc ∑ p, ∑ q, ∑ r, ∑ s, F p q r s
              = ∑ p, ∑ r, ∑ q, ∑ s, F p q r s := Finset.sum_congr rfl fun p _ => Finset.sum_comm
            _ = ∑ r, ∑ p, ∑ q, ∑ s, F p q r s := Finset.sum_comm
            _ = ∑ r, ∑ p, ∑ s, ∑ q, F p q r s := Finset.sum_congr rfl fun r _ =>
                  Finset.sum_congr rfl fun p _ => Finset.sum_comm
            _ = ∑ r, ∑ s, ∑ p, ∑ q, F p q r s := Finset.sum_congr rfl fun r _ => Finset.sum_comm
        calc ∑ p : Fin 128, ∑ q : Fin 128, ∑ r : Fin 128, ∑ s : Fin 128,
                (B_int p r : ℝ) * (C_int r i : ℝ) * ((H8ShiftInt g_num h_num twist p q : ℝ) / 128) *
                  ((B_int q s : ℝ) * (C_int s j : ℝ))
            = ∑ r : Fin 128, ∑ s : Fin 128, ∑ p : Fin 128, ∑ q : Fin 128,
                (B_int p r : ℝ) * (C_int r i : ℝ) * ((H8ShiftInt g_num h_num twist p q : ℝ) / 128) *
                  ((B_int q s : ℝ) * (C_int s j : ℝ)) := hre _
          _ = _ := by
            refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
              Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
      rw [hsum_eq]; field_simp [h128, hS_ne]
    rw [hQHQ_expand]
    simp_rw [hBHB_eq]
    have hCi_zero : ∀ r : Fin 128, ¬ (b.offset ≤ r.val ∧ r.val < b.offset + b.dim) → C_int r i = 0 := by
      intro r hr
      rcases hbcov r with ⟨b', hb', hr1, hr2⟩
      have hne : b' ≠ b := fun heq => hr (heq ▸ ⟨hr1, hr2⟩)
      simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb' hr1 hr2]
      have hnoti : ¬ (b'.offset ≤ i.val ∧ i.val < b'.offset + b'.dim) := fun ⟨h1, h2⟩ =>
        hne (hbdisj b' hb' b hb i.val h1 h2 hi1 hi2)
      simp [hnoti]
    by_cases hj : b.offset ≤ j.val ∧ j.val < b.offset + b.dim
    · rw [if_pos hj]
      congr 1; refine congrArg (Int.cast : ℤ → ℝ) ?_
      have hCj_zero : ∀ s : Fin 128, ¬ (b.offset ≤ s.val ∧ s.val < b.offset + b.dim) → C_int s j = 0 := by
        intro s hs
        rcases hbcov s with ⟨b', hb', hs1, hs2⟩
        have hne : b' ≠ b := fun heq => hs (heq ▸ ⟨hs1, hs2⟩)
        simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb' hs1 hs2]
        have hnotj : ¬ (b'.offset ≤ j.val ∧ j.val < b'.offset + b'.dim) := fun ⟨h1, h2⟩ =>
          hne (hbdisj b' hb' b hb j.val h1 h2 hj.1 hj.2)
        simp [hnotj]
      have hrestrict :
          (∑ r : Fin 128, ∑ s : Fin 128,
            C_int r i *
              (match blocks.find? (fun b' => decide (b'.offset ≤ r.val) && decide (r.val < b'.offset + b'.dim)) with
               | some b' => if b'.offset ≤ s.val ∧ s.val < b'.offset + b'.dim then
                   (b'.Hb.getD (r.val - b'.offset) []).getD (s.val - b'.offset) 0 else 0
               | none => 0) * C_int s j) =
          ∑ kr : Fin b.dim,
            (b.Ccols.getD (i.val - b.offset) []).getD kr.val 0 *
              ∑ ks : Fin b.dim,
                (b.Hb.getD kr.val []).getD ks.val 0 *
                  (b.Ccols.getD (j.val - b.offset) []).getD ks.val 0 := by
        have hfilt_sum : ∀ (f : Fin 128 → ℤ),
            (∀ x : Fin 128, ¬ (b.offset ≤ x.val ∧ x.val < b.offset + b.dim) → f x = 0) →
            (∑ x : Fin 128, f x) = ∑ k : Fin b.dim, f ⟨b.offset + k.val, by have := hble b hb; omega⟩ := by
          intro f hf
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun x : Fin 128 => b.offset ≤ x.val ∧ x.val < b.offset + b.dim)]
          have h0 : ∑ x ∈ Finset.univ.filter (fun x : Fin 128 => ¬ (b.offset ≤ x.val ∧ x.val < b.offset + b.dim)), f x = 0 :=
            Finset.sum_eq_zero fun x hx => hf x (Finset.mem_filter.mp hx).2
          rw [h0, add_zero]
          refine Finset.sum_bij (fun (x : Fin 128) hx =>
              (⟨x.val - b.offset, by have := (Finset.mem_filter.mp hx).2; omega⟩ : Fin b.dim))
            (fun _ _ => Finset.mem_univ _)
            (fun x₁ hx₁ x₂ hx₂ heq => by
              have h1 := (Finset.mem_filter.mp hx₁).2; have h2 := (Finset.mem_filter.mp hx₂).2
              have hv := congrArg Fin.val heq; dsimp at hv; exact Fin.ext (by omega))
            (fun k _ => ⟨⟨b.offset + k.val, by have := hble b hb; omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩, Fin.ext (by simp)⟩)
            (fun x hx => by
              have h := (Finset.mem_filter.mp hx).2
              congr 1; exact Fin.ext (by dsimp; omega))
        rw [hfilt_sum _ (fun r hr => Finset.sum_eq_zero fun s _ => by rw [hCi_zero r hr, zero_mul, zero_mul])]
        refine Finset.sum_congr rfl fun kr _ => ?_
        rw [hfilt_sum _ (fun s hs => by rw [hCj_zero s hs, mul_zero])]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ks _ => ?_
        have hkr1 : b.offset ≤ b.offset + kr.val := by omega
        have hkr2 : b.offset + kr.val < b.offset + b.dim := by omega
        have hks1 : b.offset ≤ b.offset + ks.val := by omega
        have hks2 : b.offset + ks.val < b.offset + b.dim := by omega
        simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb hkr1 hkr2,
          find_block_eq hpart hb hks1 hks2, hi1, hi2, hj.1, hj.2, hks1, hks2,
          and_self, ↓reduceIte, Nat.add_sub_cancel_left]
        ring
      rw [hrestrict, dotList_eq_sum (m := b.dim) _ _
        (hCcol_len b hb ⟨i.val - b.offset, by omega⟩)
        (by rw [List.length_map, hHb_len b hb])]
      refine Finset.sum_congr rfl fun kr _ => ?_
      congr 1
      have hkr_lt : kr.val < b.Hb.length := by rw [hHb_len b hb]; exact kr.isLt
      rw [list_getD_of_lt (b.Hb.map (fun row => dotList row (b.Ccols.getD (j.val - b.offset) []))) 0
          (by rw [List.length_map]; exact hkr_lt),
        List.getElem_map, ← list_getD_of_lt b.Hb [] hkr_lt,
        dotList_eq_sum (m := b.dim) _ _ (hHbrow_len b hb kr) (hCcol_len b hb ⟨j.val - b.offset, by omega⟩)]
    · rw [if_neg hj]
      have h0 : (∑ r : Fin 128, ∑ s : Fin 128,
            C_int r i *
              (match blocks.find? (fun b' => decide (b'.offset ≤ r.val) && decide (r.val < b'.offset + b'.dim)) with
               | some b' => if b'.offset ≤ s.val ∧ s.val < b'.offset + b'.dim then
                   (b'.Hb.getD (r.val - b'.offset) []).getD (s.val - b'.offset) 0 else 0
               | none => 0) * C_int s j) = 0 := by
        refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
        by_cases hr : b.offset ≤ r.val ∧ r.val < b.offset + b.dim
        · simp only [find_block_eq hpart hb hr.1 hr.2]
          by_cases hs : b.offset ≤ s.val ∧ s.val < b.offset + b.dim
          · have hCj : C_int s j = 0 := by
              simp only [C_int, Matrix.of_apply, blockDiagC, find_block_eq hpart hb hs.1 hs.2]
              simp [hj]
            rw [hCj, mul_zero]
          · simp [hs]
        · rw [hCi_zero r hr, zero_mul, zero_mul]
      rw [h0]; simp
  -- Now verify the two Gershgorin hypotheses of `gershgorin_matZ_le`!
  set ε₁ : ℝ := (e1_max : ℝ) / ((S * S : ℤ) : ℝ)
  have hε0 : 0 ≤ ε₁ := div_nonneg (by exact_mod_cast he1_nn) hS2_R_pos.le
  have hε1 : ε₁ < 1 := (div_lt_one hS2_R_pos).mpr (by exact_mod_cast he1_lt)
  let μ : Fin 128 → ℝ := fun i => (blocksXlo blocks i : ℝ) * (1 + ε₁) / 6
  -- Helper: extract per-row check from `checkSingleBlockGershgorin`
  have hrow_chk : ∀ b ∈ blocks, ∀ i : Fin 128, b.offset ≤ i.val → i.val < b.offset + b.dim →
      let ci := b.Ccols.getD (i.val - b.offset) []
      let DC := b.Ccols.map (mulList b.diagD)
      let HC := b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))
      let g1_err := (List.range b.dim).foldl (fun acc j =>
        let entry := dotList ci (DC.getD j [])
        if i.val - b.offset = j then acc + |entry - S * S| else acc + |entry|) 0
      let g2_diag := dotList ci (HC.getD (i.val - b.offset) [])
      let g2_off := (List.range b.dim).foldl (fun acc j =>
        if i.val - b.offset = j then acc else acc + |dotList ci (HC.getD j [])|) 0
      let xi := b.xlo.getD (i.val - b.offset) 0
      g1_err ≤ e1_max ∧ 0 ≤ g2_diag - g2_off ∧ 0 ≤ xi ∧
        xi * ((128 * (S * S + e1_max) : ℤ) : ℚ) ≤ ((6 * (g2_diag - g2_off) : ℤ) : ℚ) := by
    intro b hb i hi1 hi2
    have h := hblock_ok b hb
    unfold checkSingleBlockGershgorin at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hi_mem : i.val - b.offset ∈ List.range b.dim := List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp h.2 (i.val - b.offset) hi_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    exact ⟨hrow.1.1.1, hrow.1.1.2, hrow.1.2, hrow.2⟩
  have hμ_nn : ∀ i : Fin 128, 0 ≤ μ i := fun i => by
    rcases hbcov i with ⟨b, hb, hi1, hi2⟩
    have hrc := hrow_chk b hb i hi1 hi2
    have hx_eq : blocksXlo blocks i = b.xlo.getD (i.val - b.offset) 0 := by
      unfold blocksXlo; rw [find_block_eq hpart hb hi1 hi2]
    dsimp [μ]; rw [hx_eq]
    have hxi : (0 : ℝ) ≤ (b.xlo.getD (i.val - b.offset) 0 : ℝ) := by exact_mod_cast hrc.2.2.1
    positivity
  have hG1 : ∀ i : Fin 128, |(Qᵀ * Q) i i - 1| + ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j| ≤ ε₁ := by
    intro i
    rcases hbcov i with ⟨b, hb, hi1, hi2⟩
    have hrc := hrow_chk b hb i hi1 hi2
    have hsum_eq : |(Qᵀ * Q) i i - 1| + ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j| =
        (((List.range b.dim).foldl (fun acc j =>
          let entry := dotList (b.Ccols.getD (i.val - b.offset) [])
            ((b.Ccols.map (mulList b.diagD)).getD j [])
          if i.val - b.offset = j then acc + |entry - S * S| else acc + |entry|) 0 : ℤ) : ℝ) /
          ((S * S : ℤ) : ℝ) := by
      -- Rewrite foldl as sum over Fin b.dim
      have hfold : (List.range b.dim).foldl (fun acc j =>
          let entry := dotList (b.Ccols.getD (i.val - b.offset) [])
            ((b.Ccols.map (mulList b.diagD)).getD j [])
          if i.val - b.offset = j then acc + |entry - S * S| else acc + |entry|) 0 =
        ∑ k : Fin b.dim,
          if i.val - b.offset = k.val then
            |dotList (b.Ccols.getD (i.val - b.offset) [])
              (mulList b.diagD (b.Ccols.getD k.val [])) - S * S|
          else
            |dotList (b.Ccols.getD (i.val - b.offset) [])
              (mulList b.diagD (b.Ccols.getD k.val []))| := by
        have hstep : (List.range b.dim).foldl (fun acc j =>
            let entry := dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (mulList b.diagD)).getD j [])
            if i.val - b.offset = j then acc + |entry - S * S| else acc + |entry|) 0 =
          (List.range b.dim).foldl (fun acc j =>
            let entry := dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (mulList b.diagD)).getD j [])
            acc + (if i.val - b.offset = j then |entry - S * S| else |entry|)) 0 := by
          congr 1; funext acc j; split_ifs <;> rfl
        rw [hstep, foldl_sum_range_int, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk_lt : k.val < b.Ccols.length := by rw [hC_len b hb]; exact k.isLt
        rw [list_getD_of_lt (b.Ccols.map (mulList b.diagD)) [] (by rw [List.length_map]; exact hk_lt),
          List.getElem_map, ← list_getD_of_lt b.Ccols [] hk_lt]
      rw [hfold, Int.cast_sum, Finset.sum_div]
      -- Match LHS (sum over Fin 128) with sum over Fin b.dim
      have hlhs : |(Qᵀ * Q) i i - 1| + ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j| =
          ∑ j : Fin 128, if j = i then |(Qᵀ * Q) i i - 1| else |(Qᵀ * Q) i j| := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
        exact congrArg (|(Qᵀ * Q) i i - 1| + ·)
          (Finset.sum_congr rfl fun j hj => (if_neg (Finset.ne_of_mem_erase hj)).symm)
      rw [hlhs]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin 128 => b.offset ≤ j.val ∧ j.val < b.offset + b.dim)]
      have h0 : ∑ j ∈ Finset.univ.filter (fun j : Fin 128 => ¬ (b.offset ≤ j.val ∧ j.val < b.offset + b.dim)),
          (if j = i then |(Qᵀ * Q) i i - 1| else |(Qᵀ * Q) i j|) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hnot := (Finset.mem_filter.mp hj).2
        have hne : j ≠ i := fun heq => hnot (heq ▸ ⟨hi1, hi2⟩)
        rw [if_neg hne, hQTQ_entry i j b hb hi1 hi2, if_neg hnot, abs_zero]
      rw [h0, add_zero]
      refine Finset.sum_bij (fun (j : Fin 128) hj =>
          (⟨j.val - b.offset, by have := (Finset.mem_filter.mp hj).2; omega⟩ : Fin b.dim))
        (fun _ _ => Finset.mem_univ _)
        (fun j₁ hj₁ j₂ hj₂ heq => by
          have h1 := (Finset.mem_filter.mp hj₁).2; have h2 := (Finset.mem_filter.mp hj₂).2
          have hv := congrArg Fin.val heq; dsimp at hv; exact Fin.ext (by omega))
        (fun k _ => ⟨⟨b.offset + k.val, by have := hble b hb; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩, Fin.ext (by simp)⟩)
        (fun j hj => by
          rcases (Finset.mem_filter.mp hj).2 with ⟨hj1, hj2⟩
          by_cases hji : j = i
          · rw [if_pos hji, if_pos (by dsimp; rw [hji]), hQTQ_entry i i b hb hi1 hi2, if_pos ⟨hi1, hi2⟩]
            dsimp only
            rw [hji, Int.cast_abs, Int.cast_sub]
            have h1 : ∀ a : ℝ, |a / ((S * S : ℤ) : ℝ) - 1| = |a - ((S * S : ℤ) : ℝ)| / ((S * S : ℤ) : ℝ) := fun a => by
              rw [show a / ((S * S : ℤ) : ℝ) - 1 = (a - ((S * S : ℤ) : ℝ)) / ((S * S : ℤ) : ℝ) by
                rw [sub_div, div_self hS2_R_pos.ne'], abs_div, abs_of_pos hS2_R_pos]
            exact h1 _
          · have hne : i.val - b.offset ≠ j.val - b.offset := by
              intro h; exact hji (Fin.ext (by omega))
            rw [if_neg hji, if_neg hne, hQTQ_entry i j b hb hi1 hi2, if_pos ⟨hj1, hj2⟩]
            rw [Int.cast_abs, abs_div, abs_of_pos hS2_R_pos])
    rw [hsum_eq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hrc.1) hS2_R_pos.le
  have hG2 : ∀ i : Fin 128, μ i ≤ (Qᵀ * Hs * Q) i i - ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Hs * Q) i j| := by
    intro i
    rcases hbcov i with ⟨b, hb, hi1, hi2⟩
    have hrc := hrow_chk b hb i hi1 hi2
    have h128S2_pos : (0 : ℝ) < ((128 * (S * S) : ℤ) : ℝ) := by push_cast; positivity
    have hdiff_eq : (Qᵀ * Hs * Q) i i - ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Hs * Q) i j| =
        (((dotList (b.Ccols.getD (i.val - b.offset) [])
            ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD (i.val - b.offset) []) -
          (List.range b.dim).foldl (fun acc j =>
            if i.val - b.offset = j then acc
            else acc + |dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD j [])|) 0) : ℤ) : ℝ) /
          ((128 * (S * S) : ℤ) : ℝ) := by
      have hi_lt : i.val - b.offset < b.Ccols.length := by rw [hC_len b hb]; omega
      have hdiag : (Qᵀ * Hs * Q) i i =
          ((dotList (b.Ccols.getD (i.val - b.offset) [])
            ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD (i.val - b.offset) []) : ℤ) : ℝ) /
            ((128 * (S * S) : ℤ) : ℝ) := by
        rw [hQHQ_entry i i b hb hi1 hi2, if_pos ⟨hi1, hi2⟩,
          list_getD_of_lt (b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))) []
            (by rw [List.length_map]; exact hi_lt),
          List.getElem_map, ← list_getD_of_lt b.Ccols [] hi_lt]
      have hoff : ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Hs * Q) i j| =
          (((List.range b.dim).foldl (fun acc j =>
            if i.val - b.offset = j then acc
            else acc + |dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD j [])|) 0 : ℤ) : ℝ) /
            ((128 * (S * S) : ℤ) : ℝ) := by
        have hstep : (List.range b.dim).foldl (fun acc j =>
            if i.val - b.offset = j then acc
            else acc + |dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD j [])|) 0 =
          (List.range b.dim).foldl (fun acc j =>
            acc + (if i.val - b.offset = j then 0
            else |dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD j [])|)) 0 := by
          congr 1; funext acc j; split_ifs <;> ring
        rw [hstep, foldl_sum_range_int, zero_add, Int.cast_sum, Finset.sum_div]
        have hlhs : ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Hs * Q) i j| =
            ∑ j : Fin 128, if j = i then 0 else |(Qᵀ * Hs * Q) i j| := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add]
          refine Finset.sum_congr rfl fun j hj => (if_neg (Finset.ne_of_mem_erase hj)).symm
        rw [hlhs]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j : Fin 128 => b.offset ≤ j.val ∧ j.val < b.offset + b.dim)]
        have h0 : ∑ j ∈ Finset.univ.filter (fun j : Fin 128 => ¬ (b.offset ≤ j.val ∧ j.val < b.offset + b.dim)),
            (if j = i then 0 else |(Qᵀ * Hs * Q) i j|) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hnot := (Finset.mem_filter.mp hj).2
          by_cases hji : j = i
          · simp [hji]
          · rw [if_neg hji, hQHQ_entry i j b hb hi1 hi2, if_neg hnot, abs_zero]
        rw [h0, add_zero]
        refine Finset.sum_bij (fun (j : Fin 128) hj =>
            (⟨j.val - b.offset, by have := (Finset.mem_filter.mp hj).2; omega⟩ : Fin b.dim))
          (fun _ _ => Finset.mem_univ _)
          (fun j₁ hj₁ j₂ hj₂ heq => by
            have h1 := (Finset.mem_filter.mp hj₁).2; have h2 := (Finset.mem_filter.mp hj₂).2
            have hv := congrArg Fin.val heq; dsimp at hv; exact Fin.ext (by omega))
          (fun k _ => ⟨⟨b.offset + k.val, by have := hble b hb; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩, Fin.ext (by simp)⟩)
          (fun j hj => by
            rcases (Finset.mem_filter.mp hj).2 with ⟨hj1, hj2⟩
            by_cases hji : j = i
            · subst hji; simp
            · have hne : i.val - b.offset ≠ j.val - b.offset := fun h => hji (Fin.ext (by omega))
              have hj_lt : j.val - b.offset < b.Ccols.length := by rw [hC_len b hb]; omega
              rw [if_neg hji, if_neg hne, hQHQ_entry i j b hb hi1 hi2, if_pos ⟨hj1, hj2⟩,
                list_getD_of_lt (b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))) []
                  (by rw [List.length_map]; exact hj_lt),
                List.getElem_map, ← list_getD_of_lt b.Ccols [] hj_lt,
                abs_div, abs_of_pos h128S2_pos, Int.cast_abs])
      rw [hdiag, hoff, ← sub_div, Int.cast_sub]
    rw [hdiff_eq]
    have hx_eq : blocksXlo blocks i = b.xlo.getD (i.val - b.offset) 0 := by
      unfold blocksXlo; rw [find_block_eq hpart hb hi1 hi2]
    dsimp [μ]; rw [hx_eq]
    have hineq_R : (b.xlo.getD (i.val - b.offset) 0 : ℝ) * ((128 * (S * S + e1_max) : ℤ) : ℝ) ≤
        ((6 * (dotList (b.Ccols.getD (i.val - b.offset) [])
            ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD (i.val - b.offset) []) -
          (List.range b.dim).foldl (fun acc j =>
            if i.val - b.offset = j then acc
            else acc + |dotList (b.Ccols.getD (i.val - b.offset) [])
              ((b.Ccols.map (fun col => b.Hb.map (fun row => dotList row col))).getD j [])|) 0) : ℤ) : ℝ) := by
      exact_mod_cast hrc.2.2.2
    have h1pe : 1 + ε₁ = ((S * S + e1_max : ℤ) : ℝ) / ((S * S : ℤ) : ℝ) := by
      dsimp [ε₁]; push_cast; field_simp [hS2_R_pos.ne']
    rw [h1pe]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) h128S2_pos]
    push_cast at hineq_R ⊢
    field_simp [hS2_R_pos.ne'] at hineq_R ⊢
    linarith
  -- Apply `gershgorin_matZ_le`!
  have hmain : matZ H hH 6 ≤ ∑ i : Fin 128, Real.exp (-6 * (μ i / (1 + ε₁) - 12)) :=
    gershgorin_matZ_le H hH 12 Q hε0 hε1 μ hμ_nn hG1 hG2 (by norm_num : (0 : ℝ) < 6)
  have hexp_split : ∑ i : Fin 128, Real.exp (-6 * (μ i / (1 + ε₁) - 12)) =
      Real.exp 72 * ∑ i : Fin 128, Real.exp (-(blocksXlo blocks i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.exp_add]
    congr 1
    dsimp [μ]
    have h1pe_ne : 1 + ε₁ ≠ 0 := by linarith
    field_simp [h1pe_ne]; ring
  rw [hexp_split] at hmain
  have hterm_ub : ∑ i : Fin 128, Real.exp (-(blocksXlo blocks i : ℝ)) ≤
      ((sumBlockExpUpper blocks : ℚ) : ℝ) := by
    rw [sumBlockExpUpper_eq hpart hxlo_len, Rat.cast_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases hbcov i with ⟨b, hb, hi1, hi2⟩
    have hx_nn : (0 : ℚ) ≤ blocksXlo blocks i := by
      unfold blocksXlo; rw [find_block_eq hpart hb hi1 hi2]
      exact (hrow_chk b hb i hi1 hi2).2.2.1
    split_ifs with h45
    · have h1 : Real.exp (-(blocksXlo blocks i : ℝ)) ≤ Real.exp (-(45 : ℝ)) :=
        Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast h45))
      exact h1.trans (exp_neg_le_ratExpNegUpper (by norm_num : (0 : ℚ) ≤ 45) 6 10 (by omega))
    · exact exp_neg_le_ratExpNegUpper hx_nn 6 10 (by omega)
  have hsumU_R : ((sumBlockExpUpper blocks : ℚ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast hsumU
  exact hmain.trans (mul_le_mul_of_nonneg_left (hterm_ub.trans hsumU_R) (Real.exp_pos 72).le)

end PurityBootstrap.BlockGershgorin
