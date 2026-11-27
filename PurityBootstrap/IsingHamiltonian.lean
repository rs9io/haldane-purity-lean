import PurityBootstrap.MatrixTools
import Mathlib.Tactic

/-!
# Explicit Interacting Ising Chain Hamiltonian (`arXiv:2611.07400`, Eq. `eq:ising-interacting-chain`)

Defines the exact finite-volume interacting transverse-field Ising Hamiltonian
  `H_L^{(t)}(g, h) = -∑_{i=0}^{L-1} Z_i Z_{i+1}^{(t)} - g ∑_{i=0}^{L-1} X_i X_{i+1} - h ∑_{i=0}^{L-1} X_i`
in the product-`X` basis on the even-`X` (`sector = false`) and odd-`X` (`sector = true`)
symmetry sectors of dimension `2^(L - 1)`, for both untwisted (`twist = false`, `t = +1`)
and twisted (`twist = true`, `t = -1`, closing bond `+Z_{L-1} Z_0`) boundary conditions.

Proves from first principles (pure standard axioms):
1. `H_ising_isHermitian`: real symmetry of `H_L^{(t)}(g, h)` for all `L ≥ 1, g, h, twist, sector`.
2. `H_ising_affine`: exact affine decomposition `H_ZZ + g • H_XX + h • H_X` in `(g, h)`.
3. `ising_seam_ordering`: Grover's Eq. `eq:sectors` absolute-value variational proof that
   `E_{0, k, t=+1}(L) ≤ E_{0, k, t=-1}(L)` for every `L ≥ 2`, `g, h ∈ ℝ`, and sector `k = ±1`.
-/

namespace PurityBootstrap.IsingHamiltonian

open scoped BigOperators Matrix
open Matrix PurityBootstrap.MatrixTools

/-- Parity (XOR) of the lowest `m` bits of a natural number `n`. -/
def bitParity : ℕ → ℕ → Bool
  | 0, _ => false
  | m + 1, n => xor (n.testBit m) (bitParity m n)

/-- Lift an index `i : Fin (2 ^ (L - 1))` into an `L`-bit string with prescribed total
`X`-parity `sector` (`false` = even popcount, `true` = odd popcount) by setting bit `L - 1`
to `xor sector (bitParity (L - 1) i.val)`. -/
def sectorState (L : ℕ) (sector : Bool) (i : Fin (2 ^ (L - 1))) : ℕ :=
  let topBit := xor sector (bitParity (L - 1) i.val)
  i.val + if topBit then 2 ^ (L - 1) else 0

/-- Spin eigenvalue `σ_k ∈ {+1, -1}` of `X_k` on bitstring `s`: `+1` if bit `k` is `0`, `-1` if `1`. -/
def spinVal (s k : ℕ) : ℝ :=
  if s.testBit k then (-1 : ℝ) else (1 : ℝ)

/-- Integer spin eigenvalue `±1` for exact integer matrix checks. -/
def spinValInt (s k : ℕ) : ℤ :=
  if s.testBit k then (-1 : ℤ) else (1 : ℤ)

lemma spinVal_eq_cast (s k : ℕ) : spinVal s k = (spinValInt s k : ℝ) := by
  unfold spinVal spinValInt
  split_ifs <;> norm_num

/-- Flip bits `k` and `(k + 1) % L` on the low `L - 1` bits (preserves total parity,
so it acts as an involution on `Fin (2 ^ (L - 1))`!). -/
def flipBond (L k : ℕ) (i : Fin (2 ^ (L - 1))) : Fin (2 ^ (L - 1)) :=
  let mask := ((1 <<< k) ^^^ (1 <<< ((k + 1) % L))) % (2 ^ (L - 1))
  ⟨(i.val ^^^ mask) % (2 ^ (L - 1)), Nat.mod_lt _ (by positivity)⟩

lemma flipBond_involutive (L k : ℕ) (i : Fin (2 ^ (L - 1))) :
    flipBond L k (flipBond L k i) = i := by
  ext
  simp only [flipBond]
  let M := 2 ^ (L - 1)
  have hM : 0 < M := by positivity
  let mask := ((1 <<< k) ^^^ (1 <<< ((k + 1) % L))) % M
  have hi_lt : i.val < M := i.isLt
  have hmask_lt : mask < M := Nat.mod_lt _ hM
  have h1 : (i.val ^^^ mask) % M = i.val ^^^ mask :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hi_lt hmask_lt)
  change ((i.val ^^^ mask) % M ^^^ mask) % M = i.val
  rw [h1]
  have h2 : (i.val ^^^ mask) ^^^ mask = i.val := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [h2, Nat.mod_eq_of_lt hi_lt]

/-- `ZZ` bond term `-∑_{k=0}^{L-1} t_k Z_k Z_{k+1}` on `Fin (2^(L-1))`,
where `t_k = 1` for `k < L - 1` and `t_{L-1} = -1` if `twist = true`. -/
def H_ZZ (L : ℕ) (twist : Bool) : Matrix (Fin (2 ^ (L - 1))) (Fin (2 ^ (L - 1))) ℝ :=
  Matrix.of fun i j =>
    ∑ k ∈ Finset.range L,
      if j = flipBond L k i then
        if twist && decide (k = L - 1) then (1 : ℝ) else (-1 : ℝ)
      else 0

/-- Diagonal `XX` bond term `-∑_{k=0}^{L-1} X_k X_{k+1}` on `Fin (2^(L-1))`. -/
def H_XX (L : ℕ) (sector : Bool) : Matrix (Fin (2 ^ (L - 1))) (Fin (2 ^ (L - 1))) ℝ :=
  Matrix.diagonal fun i =>
    let s := sectorState L sector i
    ∑ k ∈ Finset.range L, -(spinVal s k * spinVal s ((k + 1) % L))

/-- Diagonal transverse-field `X` term `-∑_{k=0}^{L-1} X_k` on `Fin (2^(L-1))`. -/
def H_X (L : ℕ) (sector : Bool) : Matrix (Fin (2 ^ (L - 1))) (Fin (2 ^ (L - 1))) ℝ :=
  Matrix.diagonal fun i =>
    let s := sectorState L sector i
    ∑ k ∈ Finset.range L, -(spinVal s k)

/-- Full interacting Ising Hamiltonian `H_L^{(t)}(g, h)` in symmetry sector `sector`
and boundary condition `twist`. -/
def H_ising (L : ℕ) (g h : ℝ) (twist sector : Bool) :
    Matrix (Fin (2 ^ (L - 1))) (Fin (2 ^ (L - 1))) ℝ :=
  H_ZZ L twist + g • H_XX L sector + h • H_X L sector

lemma H_ZZ_isHermitian (L : ℕ) (twist : Bool) : (H_ZZ L twist).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, H_ZZ, Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hiff : (i = flipBond L k j) ↔ (j = flipBond L k i) := by
    constructor
    · intro h; rw [h, flipBond_involutive]
    · intro h; rw [h, flipBond_involutive]
  by_cases h : j = flipBond L k i
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma H_XX_isHermitian (L : ℕ) (sector : Bool) : (H_XX L sector).IsHermitian := by
  unfold H_XX
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

lemma H_X_isHermitian (L : ℕ) (sector : Bool) : (H_X L sector).IsHermitian := by
  unfold H_X
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

lemma H_ising_isHermitian (L : ℕ) (g h : ℝ) (twist sector : Bool) :
    (H_ising L g h twist sector).IsHermitian := by
  unfold H_ising
  have h1 : (g • H_XX L sector).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, (H_XX_isHermitian L sector).eq]
  have h2 : (h • H_X L sector).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, (H_X_isHermitian L sector).eq]
  exact ((H_ZZ_isHermitian L twist).add h1).add h2

/-- Affine interpolation identity for `H_ising` in `g`. -/
lemma H_ising_affine_g (L : ℕ) (g₁ g₂ h θ : ℝ) (twist sector : Bool) :
    H_ising L ((1 - θ) * g₁ + θ * g₂) h twist sector =
      (1 - θ) • H_ising L g₁ h twist sector + θ • H_ising L g₂ h twist sector := by
  ext i j
  simp [H_ising]
  ring

/-- Affine interpolation identity for `H_ising` in `h`. -/
lemma H_ising_affine_h (L : ℕ) (g h₁ h₂ θ : ℝ) (twist sector : Bool) :
    H_ising L g ((1 - θ) * h₁ + θ * h₂) twist sector =
      (1 - θ) • H_ising L g h₁ twist sector + θ • H_ising L g h₂ twist sector := by
  ext i j
  simp [H_ising]
  ring

/-- Quadratic-form dominance for the `ZZ` bond term (Grover Eq. `eq:sectors`):
replacing `v` by `|v|` in the untwisted Hamiltonian can only lower the expectation value
relative to either boundary condition `twist`. -/
lemma H_ZZ_abs_quad_le (L : ℕ) (twist : Bool) (v : Fin (2 ^ (L - 1)) → ℝ) :
    dotProduct (fun i => |v i|) ((H_ZZ L false).mulVec (fun i => |v i|)) ≤
      dotProduct v ((H_ZZ L twist).mulVec v) := by
  have hquad : ∀ (tw : Bool) (u : Fin (2 ^ (L - 1)) → ℝ),
      dotProduct u ((H_ZZ L tw).mulVec u) =
        ∑ i : Fin (2 ^ (L - 1)), ∑ k ∈ Finset.range L,
          (if tw && decide (k = L - 1) then (1 : ℝ) else (-1 : ℝ)) *
            u i * u (flipBond L k i) := fun tw u => by
    simp only [dotProduct, Matrix.mulVec, H_ZZ, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    calc ∑ x : Fin (2 ^ (L - 1)), u i *
            ((∑ k ∈ Finset.range L,
              if x = flipBond L k i then
                if tw && decide (k = L - 1) then (1 : ℝ) else (-1 : ℝ)
              else 0) * u x)
        = ∑ x : Fin (2 ^ (L - 1)), ∑ k ∈ Finset.range L,
            if x = flipBond L k i then
              (if tw && decide (k = L - 1) then (1 : ℝ) else (-1 : ℝ)) * u i * u x
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
      _ = ∑ k ∈ Finset.range L, ∑ x : Fin (2 ^ (L - 1)),
            if x = flipBond L k i then
              (if tw && decide (k = L - 1) then (1 : ℝ) else (-1 : ℝ)) * u i * u x
            else 0 := Finset.sum_comm
      _ = ∑ k ∈ Finset.range L,
            (if tw && decide (k = L - 1) then (1 : ℝ) else (-1 : ℝ)) *
              u i * u (flipBond L k i) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp
  rw [hquad false (fun i => |v i|), hquad twist v]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have habs : -(|v i| * |v (flipBond L k i)|) ≤ v i * v (flipBond L k i) ∧
      v i * v (flipBond L k i) ≤ |v i| * |v (flipBond L k i)| := by
    rw [← abs_mul]
    exact ⟨neg_abs_le _, le_abs_self _⟩
  split_ifs <;> linarith

/-- **Within-sector seam ordering (`arXiv:2611.07400`, Eq. `eq:sectors`)**:
for every `L`, couplings `g, h : ℝ`, and symmetry sector `sector : Bool`,
every twisted eigenvalue `E_{k, t=-1}` lies at or above some untwisted eigenvalue `E_{k', t=+1}`
in the same sector! -/
theorem ising_seam_ordering (L : ℕ) (g h : ℝ) (sector : Bool) :
    ∀ kt : Fin (2 ^ (L - 1)), ∃ ku : Fin (2 ^ (L - 1)),
      (H_ising_isHermitian L g h false sector).eigenvalues ku ≤
        (H_ising_isHermitian L g h true sector).eigenvalues kt := by
  intro kt
  let hU := H_ising_isHermitian L g h false sector
  let hT := H_ising_isHermitian L g h true sector
  let v : Fin (2 ^ (L - 1)) → ℝ := (hT.eigenvectorBasis kt).ofLp
  let vabs : Fin (2 ^ (L - 1)) → ℝ := fun i => |v i|
  have hv_unit : dotProduct v v = 1 := by
    have h1 := hT.eigenvectorBasis.orthonormal.1 kt
    have hsq : ‖hT.eigenvectorBasis kt‖ ^ 2 = 1 := by rw [h1, one_pow]
    rw [EuclideanSpace.norm_sq_eq] at hsq
    simpa [v, dotProduct, Real.norm_eq_abs, sq_abs, sq] using hsq
  have hvabs_unit : dotProduct vabs vabs = 1 := by
    have heq : dotProduct vabs vabs = dotProduct v v := by
      simp only [dotProduct, vabs]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sq, sq_abs, sq]
    rw [heq, hv_unit]
  have hdiag_eq : ∀ (d : Fin (2 ^ (L - 1)) → ℝ),
      dotProduct vabs ((Matrix.diagonal d).mulVec vabs) =
        dotProduct v ((Matrix.diagonal d).mulVec v) := fun d => by
    simp only [dotProduct, Matrix.mulVec_diagonal, vabs]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsq : |v i| * (d i * |v i|) = d i * |v i| ^ 2 := by ring
    have hsq' : v i * (d i * v i) = d i * v i ^ 2 := by ring
    rw [hsq, hsq', sq_abs]
  have hquad_le :
      dotProduct vabs ((H_ising L g h false sector).mulVec vabs) ≤
        hT.eigenvalues kt := by
    have hT_eq : dotProduct v ((H_ising L g h true sector).mulVec v) = hT.eigenvalues kt := by
      rw [hT.mulVec_eigenvectorBasis kt, dotProduct_smul, smul_eq_mul, hv_unit, mul_one]
    rw [← hT_eq]
    simp only [H_ising, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    have hzz := H_ZZ_abs_quad_le L true v
    have hxx := hdiag_eq (fun i =>
      ∑ k ∈ Finset.range L, -(spinVal (sectorState L sector i) k *
        spinVal (sectorState L sector i) ((k + 1) % L)))
    have hx := hdiag_eq (fun i =>
      ∑ k ∈ Finset.range L, -(spinVal (sectorState L sector i) k))
    change dotProduct vabs ((H_ZZ L false).mulVec vabs) +
        g * dotProduct vabs ((H_XX L sector).mulVec vabs) +
        h * dotProduct vabs ((H_X L sector).mulVec vabs) ≤
      dotProduct v ((H_ZZ L true).mulVec v) +
        g * dotProduct v ((H_XX L sector).mulVec v) +
        h * dotProduct v ((H_X L sector).mulVec v)
    unfold H_XX H_X
    rw [hxx, hx]
    linarith
  rcases Finset.exists_min_image Finset.univ hU.eigenvalues Finset.univ_nonempty with
    ⟨ku, _, hku⟩
  refine ⟨ku, ?_⟩
  have hray : hU.eigenvalues ku ≤ dotProduct vabs ((H_ising L g h false sector).mulVec vabs) := by
    rw [dotProduct_mulVec_eq_sum_eigenvalues _ hU vabs]
    have hsum1 : ∑ k : Fin (2 ^ (L - 1)), (dotProduct (hU.eigenvectorBasis k).ofLp vabs) ^ 2 = 1 := by
      rw [← dotProduct_self_eq_sum_sq _ hU vabs, hvabs_unit]
    calc hU.eigenvalues ku
        = hU.eigenvalues ku * ∑ k, (dotProduct (hU.eigenvectorBasis k).ofLp vabs) ^ 2 := by
          rw [hsum1, mul_one]
      _ = ∑ k, hU.eigenvalues ku * (dotProduct (hU.eigenvectorBasis k).ofLp vabs) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ∑ k, hU.eigenvalues k * (dotProduct (hU.eigenvectorBasis k).ofLp vabs) ^ 2 :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hku k (Finset.mem_univ k)) (sq_nonneg _)
  exact hray.trans hquad_le

end PurityBootstrap.IsingHamiltonian
