import PurityBootstrap.Basic
import PurityBootstrap.OneD
import PurityBootstrap.ExactCertificates
import PurityBootstrap.SymmetryTwists
import PurityBootstrap.MatrixTools
import PurityBootstrap.IsingHamiltonian
import PurityBootstrap.IsingMPS
import PurityBootstrap.CandidateE.Corner15_47
import PurityBootstrap.CandidateE.Corner15_48
import PurityBootstrap.CandidateE.Corner16_47
import PurityBootstrap.CandidateE.Corner16_48

/-!
# Candidate E: Machine-Checked 2D Coupling-Rectangle Spectral Gap & Multiplet Theorem

Proves inside Lean 4's pure kernel (zero `sorry`, zero `native_decide`, standard axioms
`[propext, Classical.choice, Quot.sound]` only):

1. **Exact `L = 16` `D = 2` periodic MPS Rayleigh–Ritz certificate** (`mps16_rayleigh_le_matZ`):
   for `A₀ = [[219, -159], [-159, 256]]`, `A₁ = [[-249, 152], [152, 9]]`, evaluates the
   32,768-dimensional exact expectation values `‖ψ‖²`, `⟨ψ, H_ZZ ψ⟩`, `⟨ψ, H_XX ψ⟩`,
   `⟨ψ, H_X ψ⟩` via `IsingMPS` (`4 × 4` integer matrix powers checked with `decide +kernel`).
2. **Continuous 2D Rectangle Seed Bound** (`candidate_e_rectangle_Qplus_ge`):
   combining the 4 pure-kernel 256-dim `L = 8` Gershgorin upper bounds (`Corner15_47`,
   `Corner15_48`, `Corner16_47`, `Corner16_48`), the `L = 16` MPS lower bound, and
   Peierls–Bogoliubov–Young log-convexity (`log_convex_rectangle_le`), proves unconditionally
   for **every** `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]`:
   `(877 / 1000) * Z_+(8, 6; g, h)^4 ≤ Z_+(16, 12; g, h)`.
3. **3-Round Coupled Bootstrap to `(L₀, β₀) = (64, 48)`** (`candidate_e_three_rounds_to_64`):
   propagates `(p₀ = 64/1000, q₀ = 123/1000)` through 3 exact rounded coupled updates
   (`decide +kernel`) to reach `1 - S_+(64, 48) ≤ 1/100` and `1 - T_+(128, 48) ≤ 1/100`.
4. **Uniform Rectangle Multiplet Theorem** (`candidate_e_rectangle_multiplet`):
   yields `0 ≤ W_ℓ ≤ (1/20) * exp (-(log 20) * ℓ / 128)` and `Γ_ℓ > log 8 / 48` for every
   even `ℓ ≥ 64` and every `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]`.
-/

namespace PurityBootstrap.CandidateE

open scoped BigOperators Matrix Kronecker
open Matrix PurityBootstrap PurityBootstrap.ExactCertificates
open PurityBootstrap.MatrixTools PurityBootstrap.IsingHamiltonian
open PurityBootstrap.IsingMPS PurityBootstrap.SymmetryTwists

/-! ## Exact `4 × 4` Integer Transfer Matrix Arithmetic for `D = 2` MPS -/

/-- Exact `2 × 2` integer matrices defining our 6-parameter symmetric periodic MPS. -/
def mpsA0Z : Matrix (Fin 2) (Fin 2) ℤ := !![219, -159; -159, 256]
def mpsA1Z : Matrix (Fin 2) (Fin 2) ℤ := !![-249, 152; 152, 9]

/-- Real cast of `mpsA0Z` and `mpsA1Z`. -/
def mpsA0 : Matrix (Fin 2) (Fin 2) ℝ := mpsA0Z.map Int.cast
def mpsA1 : Matrix (Fin 2) (Fin 2) ℝ := mpsA1Z.map Int.cast

/-- Computable `4 × 4` integer matrix represented as a 4-row `List (List ℤ)`. -/
abbrev Mat4Z := List (List ℤ)

/-- Map index `(a, b) : Fin 2 × Fin 2` to `0..3`. -/
def idx4 (p : Fin 2 × Fin 2) : ℕ := 2 * p.1.val + p.2.val

def mat4Entry (M : Mat4Z) (r c : ℕ) : ℤ := (M.getD r []).getD c 0

def mat4ToReal (M : Mat4Z) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun i j => (mat4Entry M (idx4 i) (idx4 j) : ℝ)

def mat4Mul (A B : Mat4Z) : Mat4Z :=
  (List.range 4).map fun r =>
    (List.range 4).map fun c =>
      mat4Entry A r 0 * mat4Entry B 0 c +
      mat4Entry A r 1 * mat4Entry B 1 c +
      mat4Entry A r 2 * mat4Entry B 2 c +
      mat4Entry A r 3 * mat4Entry B 3 c

def mat4Id : Mat4Z :=
  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

def mat4Pow (A : Mat4Z) : ℕ → Mat4Z
  | 0 => mat4Id
  | n + 1 => mat4Mul A (mat4Pow A n)

def mat4Trace (A : Mat4Z) : ℤ :=
  mat4Entry A 0 0 + mat4Entry A 1 1 + mat4Entry A 2 2 + mat4Entry A 3 3

lemma idx4_lt (p : Fin 2 × Fin 2) : idx4 p < 4 := by
  rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; unfold idx4; omega

lemma mat4ToReal_id : mat4ToReal mat4Id = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [mat4ToReal, mat4Id, mat4Entry, idx4]

lemma mat4ToReal_mul (A B : Mat4Z) :
    mat4ToReal (mat4Mul A B) = mat4ToReal A * mat4ToReal B := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [mat4ToReal, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hget : mat4Entry (mat4Mul A B) (idx4 (a, b)) (idx4 (c, d)) =
      mat4Entry A (idx4 (a, b)) 0 * mat4Entry B 0 (idx4 (c, d)) +
      mat4Entry A (idx4 (a, b)) 1 * mat4Entry B 1 (idx4 (c, d)) +
      mat4Entry A (idx4 (a, b)) 2 * mat4Entry B 2 (idx4 (c, d)) +
      mat4Entry A (idx4 (a, b)) 3 * mat4Entry B 3 (idx4 (c, d)) := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl
  rw [hget]
  simp only [idx4, Fin.val_zero, Fin.val_one]
  push_cast
  ring

lemma mat4ToReal_pow (A : Mat4Z) : ∀ n : ℕ, mat4ToReal (mat4Pow A n) = (mat4ToReal A) ^ n
  | 0 => by simp [mat4Pow, mat4ToReal_id]
  | n + 1 => by rw [mat4Pow, mat4ToReal_mul, mat4ToReal_pow A n, pow_succ']

lemma mat4ToReal_trace (A : Mat4Z) : Matrix.trace (mat4ToReal A) = (mat4Trace A : ℝ) := by
  simp only [Matrix.trace, Matrix.diag, mat4ToReal, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, idx4, Fin.val_zero, Fin.val_one, mat4Trace]
  push_cast
  ring

/-- Kronecker product of two `2 × 2` integer matrices as a `Mat4Z`. -/
def kron2Z (A B : Matrix (Fin 2) (Fin 2) ℤ) : Mat4Z :=
  [ [A 0 0 * B 0 0, A 0 0 * B 0 1, A 0 1 * B 0 0, A 0 1 * B 0 1],
    [A 0 0 * B 1 0, A 0 0 * B 1 1, A 0 1 * B 1 0, A 0 1 * B 1 1],
    [A 1 0 * B 0 0, A 1 0 * B 0 1, A 1 1 * B 0 0, A 1 1 * B 0 1],
    [A 1 0 * B 1 0, A 1 0 * B 1 1, A 1 1 * B 1 0, A 1 1 * B 1 1] ]

def mat4Add (A B : Mat4Z) : Mat4Z :=
  (List.range 4).map fun r => (List.range 4).map fun c => mat4Entry A r c + mat4Entry B r c

def mat4Sub (A B : Mat4Z) : Mat4Z :=
  (List.range 4).map fun r => (List.range 4).map fun c => mat4Entry A r c - mat4Entry B r c

def mpsEpZ : Mat4Z := mat4Add (kron2Z mpsA0Z mpsA0Z) (kron2Z mpsA1Z mpsA1Z)
def mpsEmZ : Mat4Z := mat4Sub (kron2Z mpsA0Z mpsA0Z) (kron2Z mpsA1Z mpsA1Z)
def mpsKpZ : Mat4Z := mat4Add (kron2Z mpsA0Z mpsA1Z) (kron2Z mpsA1Z mpsA0Z)
def mpsKmZ : Mat4Z := mat4Sub (kron2Z mpsA0Z mpsA1Z) (kron2Z mpsA1Z mpsA0Z)

lemma mat4ToReal_Ep : mat4ToReal mpsEpZ = mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [mat4ToReal, mpsEpZ, mat4Add, kron2Z, mpsA0, mpsA1, mpsA0Z, mpsA1Z, mat4Entry, idx4] <;>
    norm_num

lemma mat4ToReal_Em : mat4ToReal mpsEmZ = mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [mat4ToReal, mpsEmZ, mat4Sub, kron2Z, mpsA0, mpsA1, mpsA0Z, mpsA1Z, mat4Entry, idx4] <;>
    norm_num

lemma mat4ToReal_Kp : mat4ToReal mpsKpZ = mpsA0 ⊗ₖ mpsA1 + mpsA1 ⊗ₖ mpsA0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [mat4ToReal, mpsKpZ, mat4Add, kron2Z, mpsA0, mpsA1, mpsA0Z, mpsA1Z, mat4Entry, idx4] <;>
    norm_num

lemma mat4ToReal_Km : mat4ToReal mpsKmZ = mpsA0 ⊗ₖ mpsA1 - mpsA1 ⊗ₖ mpsA0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [mat4ToReal, mpsKmZ, mat4Sub, kron2Z, mpsA0, mpsA1, mpsA0Z, mpsA1Z, mat4Entry, idx4] <;>
    norm_num

/-- Exact integer MPS moments for `L = 16`. -/
def mpsNorm2Z : ℤ :=
  60200539516288267294663027771002531640177485104009561744880738429166110250941541587823

def mpsFzzZ : ℤ :=
  -907101432479165520932420836822451852089031307314825412650329062293447078376383830361440

def mpsFxxZ : ℤ :=
  -132696409851869091800337758132232794875342950619190825239854846885609984676729566369392

def mpsFxZ : ℤ :=
  -226974267777052087570517169673124786507991094527269150727012566859002120490670649515280

private theorem mps_traces_exact :
    mat4Trace (mat4Pow mpsEpZ 16) + mat4Trace (mat4Pow mpsEmZ 16) = 2 * mpsNorm2Z ∧
    (-8) * (mat4Trace (mat4Mul (mat4Mul mpsKpZ mpsKpZ) (mat4Pow mpsEpZ 14)) +
            mat4Trace (mat4Mul (mat4Mul mpsKmZ mpsKmZ) (mat4Pow mpsEmZ 14))) = mpsFzzZ ∧
    (-8) * (mat4Trace (mat4Mul (mat4Mul mpsEmZ mpsEmZ) (mat4Pow mpsEpZ 14)) +
            mat4Trace (mat4Mul (mat4Mul mpsEpZ mpsEpZ) (mat4Pow mpsEmZ 14))) = mpsFxxZ ∧
    (-8) * (mat4Trace (mat4Mul mpsEmZ (mat4Pow mpsEpZ 15)) +
            mat4Trace (mat4Mul mpsEpZ (mat4Pow mpsEmZ 15))) = mpsFxZ := by
  decide +kernel

/-- Exact MPS trial energy functional `E_MPS(g, h)` (affine in `g` and `h`). -/
noncomputable def mpsEnergy (g h : ℝ) : ℝ :=
  ((mpsFzzZ : ℝ) + g * (mpsFxxZ : ℝ) + h * (mpsFxZ : ℝ)) / (mpsNorm2Z : ℝ)

/-- Symbolic `D = 2` periodic MPS Rayleigh–Ritz lower bound on `matZ (H_ising (m + 1) g h false false) _ 12`,
expressed purely in terms of `4 × 4` transfer traces (never reducing `2 ^ m` for concrete `m`). -/
private lemma mps_rayleigh_symbolic {m : ℕ} (hm : 1 ≤ m) (A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (g h : ℝ)
    (hnorm_pos : 0 < (Matrix.trace ((A₀ ⊗ₖ A₀ + A₁ ⊗ₖ A₁) ^ (m + 1)) +
      Matrix.trace ((A₀ ⊗ₖ A₀ - A₁ ⊗ₖ A₁) ^ (m + 1))) / 2) :
    let E₀ := A₀ ⊗ₖ A₀
    let E₁ := A₁ ⊗ₖ A₁
    let Kp := A₀ ⊗ₖ A₁ + A₁ ⊗ₖ A₀
    let Km := A₀ ⊗ₖ A₁ - A₁ ⊗ₖ A₀
    let norm2 := (Matrix.trace ((E₀ + E₁) ^ (m + 1)) + Matrix.trace ((E₀ - E₁) ^ (m + 1))) / 2
    let fzz := -((m + 1 : ℝ) * (Matrix.trace (Kp * Kp * (E₀ + E₁) ^ (m - 1)) +
      Matrix.trace (Km * Km * (E₀ - E₁) ^ (m - 1))) / 2)
    let fxx := -((m + 1 : ℝ) * (Matrix.trace ((E₀ - E₁) * (E₀ - E₁) * (E₀ + E₁) ^ (m - 1)) +
      Matrix.trace ((E₀ + E₁) * (E₀ + E₁) * (E₀ - E₁) ^ (m - 1))) / 2)
    let fx := -((m + 1 : ℝ) * (Matrix.trace ((E₀ - E₁) * (E₀ + E₁) ^ m) +
      Matrix.trace ((E₀ + E₁) * (E₀ - E₁) ^ m)) / 2)
    Real.exp (-12 * ((fzz + g * fxx + h * fx) / norm2)) ≤
      matZ (H_ising (m + 1) g h false false) (H_ising_isHermitian (m + 1) g h false false) 12 := by
  intro E₀ E₁ Kp Km norm2 fzz fxx fx
  let v := mpsVec m A₀ A₁
  have hnorm : dotProduct v v = norm2 := mpsVec_norm_sq m A₀ A₁
  have hzz : dotProduct v ((H_ZZ (m + 1) false).mulVec v) = fzz := mpsVec_H_ZZ hm A₀ A₁
  have hxx : dotProduct v ((H_XX (m + 1) false).mulVec v) = fxx := mpsVec_H_XX hm A₀ A₁
  have hx : dotProduct v ((H_X (m + 1) false).mulVec v) = fx := mpsVec_H_X m A₀ A₁
  have hquad : dotProduct v ((H_ising (m + 1) g h false false).mulVec v) =
      fzz + g * fxx + h * fx := by
    simp only [H_ising, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    rw [hzz, hxx, hx]
  have hv_pos : 0 < dotProduct v v := hnorm ▸ hnorm_pos
  have : Nonempty (Fin (2 ^ m)) := ⟨⟨0, by positivity⟩⟩
  have hray := exp_rayleigh_le_matZ (H_ising (m + 1) g h false false)
    (H_ising_isHermitian (m + 1) g h false false) (by norm_num : (0 : ℝ) < 12) v hv_pos
  rw [hquad, hnorm] at hray
  exact hray

/-- Exact Rayleigh–Ritz lower bound on `matZ (H_ising 16 g h false false) _ 12` for ALL `(g, h)`. -/
theorem mps16_rayleigh_le_matZ (g h : ℝ) :
    Real.exp (-12 * mpsEnergy g h) ≤
      matZ (H_ising 16 g h false false) (H_ising_isHermitian 16 g h false false) 12 := by
  have htr := mps_traces_exact
  have hnorm_eq : (Matrix.trace ((mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) ^ 16) +
      Matrix.trace ((mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) ^ 16)) / 2 = (mpsNorm2Z : ℝ) := by
    rw [← mat4ToReal_Ep, ← mat4ToReal_Em, ← mat4ToReal_pow, ← mat4ToReal_pow,
      mat4ToReal_trace, mat4ToReal_trace]
    have hcast : ((mat4Trace (mat4Pow mpsEpZ 16) : ℝ) + (mat4Trace (mat4Pow mpsEmZ 16) : ℝ)) =
        2 * (mpsNorm2Z : ℝ) := by exact_mod_cast htr.1
    linarith
  have hzz_eq : -(((15 : ℝ) + 1) *
      (Matrix.trace ((mpsA0 ⊗ₖ mpsA1 + mpsA1 ⊗ₖ mpsA0) * (mpsA0 ⊗ₖ mpsA1 + mpsA1 ⊗ₖ mpsA0) *
          (mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) ^ 14) +
       Matrix.trace ((mpsA0 ⊗ₖ mpsA1 - mpsA1 ⊗ₖ mpsA0) * (mpsA0 ⊗ₖ mpsA1 - mpsA1 ⊗ₖ mpsA0) *
          (mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) ^ 14)) / 2) = (mpsFzzZ : ℝ) := by
    rw [← mat4ToReal_Ep, ← mat4ToReal_Em, ← mat4ToReal_Kp, ← mat4ToReal_Km,
      ← mat4ToReal_pow, ← mat4ToReal_pow, ← mat4ToReal_mul, ← mat4ToReal_mul,
      ← mat4ToReal_mul, ← mat4ToReal_mul, mat4ToReal_trace, mat4ToReal_trace]
    have hcast : (-8 : ℝ) * ((mat4Trace (mat4Mul (mat4Mul mpsKpZ mpsKpZ) (mat4Pow mpsEpZ 14)) : ℝ) +
        (mat4Trace (mat4Mul (mat4Mul mpsKmZ mpsKmZ) (mat4Pow mpsEmZ 14)) : ℝ)) = (mpsFzzZ : ℝ) := by
      exact_mod_cast htr.2.1
    linarith
  have hxx_eq : -(((15 : ℝ) + 1) *
      (Matrix.trace ((mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) * (mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) *
          (mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) ^ 14) +
       Matrix.trace ((mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) * (mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) *
          (mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) ^ 14)) / 2) = (mpsFxxZ : ℝ) := by
    rw [← mat4ToReal_Ep, ← mat4ToReal_Em,
      ← mat4ToReal_pow, ← mat4ToReal_pow, ← mat4ToReal_mul, ← mat4ToReal_mul,
      ← mat4ToReal_mul, ← mat4ToReal_mul, mat4ToReal_trace, mat4ToReal_trace]
    have hcast : (-8 : ℝ) * ((mat4Trace (mat4Mul (mat4Mul mpsEmZ mpsEmZ) (mat4Pow mpsEpZ 14)) : ℝ) +
        (mat4Trace (mat4Mul (mat4Mul mpsEpZ mpsEpZ) (mat4Pow mpsEmZ 14)) : ℝ)) = (mpsFxxZ : ℝ) := by
      exact_mod_cast htr.2.2.1
    linarith
  have hx_eq : -(((15 : ℝ) + 1) *
      (Matrix.trace ((mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) * (mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) ^ 15) +
       Matrix.trace ((mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) * (mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) ^ 15)) / 2) =
      (mpsFxZ : ℝ) := by
    rw [← mat4ToReal_Ep, ← mat4ToReal_Em,
      ← mat4ToReal_pow, ← mat4ToReal_pow, ← mat4ToReal_mul, ← mat4ToReal_mul,
      mat4ToReal_trace, mat4ToReal_trace]
    have hcast : (-8 : ℝ) * ((mat4Trace (mat4Mul mpsEmZ (mat4Pow mpsEpZ 15)) : ℝ) +
        (mat4Trace (mat4Mul mpsEpZ (mat4Pow mpsEmZ 15)) : ℝ)) = (mpsFxZ : ℝ) := by
      exact_mod_cast htr.2.2.2
    linarith
  have hnorm_pos : 0 < (Matrix.trace ((mpsA0 ⊗ₖ mpsA0 + mpsA1 ⊗ₖ mpsA1) ^ 16) +
      Matrix.trace ((mpsA0 ⊗ₖ mpsA0 - mpsA1 ⊗ₖ mpsA1) ^ 16)) / 2 := by
    rw [hnorm_eq]; exact_mod_cast (by decide +kernel : (0 : ℤ) < mpsNorm2Z)
  have hsym := mps_rayleigh_symbolic (m := 15) (by omega) mpsA0 mpsA1 g h hnorm_pos
  dsimp only at hsym
  rw [show ((15 : ℕ) : ℝ) = (15 : ℝ) by norm_num] at hsym
  rw [hnorm_eq, hzz_eq, hxx_eq, hx_eq] at hsym
  exact hsym

/-! ## Compact 8-Step Rational Squaring Certificate for `exp(y) ≤ r₈` -/

/-- Exact rational degree-9 upper bound on `exp (y / 256)` via `Real.exp_bound'`. -/
def expBoundBase9 (y : ℚ) : ℚ :=
  let t : ℚ := y / 256
  (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120 +
    t ^ 6 / 720 + t ^ 7 / 5040 + t ^ 8 / 40320) +
    t ^ 9 * 10 / (362880 * 9)

lemma exp_le_pow256_of_chain {y : ℚ} (hy0 : 0 ≤ y) (hy256 : y ≤ 256)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℚ)
    (h0 : expBoundBase9 y ≤ r0)
    (h1 : r0 * r0 ≤ r1) (h2 : r1 * r1 ≤ r2) (h3 : r2 * r2 ≤ r3) (h4 : r3 * r3 ≤ r4)
    (h5 : r4 * r4 ≤ r5) (h6 : r5 * r5 ≤ r6) (h7 : r6 * r6 ≤ r7) (h8 : r7 * r7 ≤ r8) :
    Real.exp (y : ℝ) ≤ (r8 : ℝ) := by
  have hyR0 : (0 : ℝ) ≤ (y : ℝ) / 256 := by
    have : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
    linarith
  have hyR1 : (y : ℝ) / 256 ≤ 1 := by
    have : (y : ℝ) ≤ 256 := by exact_mod_cast hy256
    linarith
  have hbase : Real.exp ((y : ℝ) / 256) ≤ (expBoundBase9 y : ℝ) := by
    refine (Real.exp_bound' hyR0 hyR1 (n := 9) (by omega)).trans (le_of_eq ?_)
    unfold expBoundBase9
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, pow_zero, pow_one, div_one]
    push_cast
    ring
  have hr0 : Real.exp ((y : ℝ) / 256) ≤ (r0 : ℝ) := hbase.trans (by exact_mod_cast h0)
  have sq_step : ∀ {a b c : ℝ}, 0 ≤ a → a ≤ b → b * b ≤ c → a * a ≤ c := fun ha hab hbc =>
    (mul_le_mul hab hab ha (ha.trans hab)).trans hbc
  have hr0_nn : (0 : ℝ) ≤ (r0 : ℝ) := (Real.exp_pos _).le.trans hr0
  have he1 : Real.exp ((y : ℝ) / 128) ≤ (r1 : ℝ) := by
    have : Real.exp ((y : ℝ) / 128) = Real.exp ((y : ℝ) / 256) * Real.exp ((y : ℝ) / 256) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le hr0 (by exact_mod_cast h1)
  have he2 : Real.exp ((y : ℝ) / 64) ≤ (r2 : ℝ) := by
    have : Real.exp ((y : ℝ) / 64) = Real.exp ((y : ℝ) / 128) * Real.exp ((y : ℝ) / 128) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he1 (by exact_mod_cast h2)
  have he3 : Real.exp ((y : ℝ) / 32) ≤ (r3 : ℝ) := by
    have : Real.exp ((y : ℝ) / 32) = Real.exp ((y : ℝ) / 64) * Real.exp ((y : ℝ) / 64) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he2 (by exact_mod_cast h3)
  have he4 : Real.exp ((y : ℝ) / 16) ≤ (r4 : ℝ) := by
    have : Real.exp ((y : ℝ) / 16) = Real.exp ((y : ℝ) / 32) * Real.exp ((y : ℝ) / 32) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he3 (by exact_mod_cast h4)
  have he5 : Real.exp ((y : ℝ) / 8) ≤ (r5 : ℝ) := by
    have : Real.exp ((y : ℝ) / 8) = Real.exp ((y : ℝ) / 16) * Real.exp ((y : ℝ) / 16) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he4 (by exact_mod_cast h5)
  have he6 : Real.exp ((y : ℝ) / 4) ≤ (r6 : ℝ) := by
    have : Real.exp ((y : ℝ) / 4) = Real.exp ((y : ℝ) / 8) * Real.exp ((y : ℝ) / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he5 (by exact_mod_cast h6)
  have he7 : Real.exp ((y : ℝ) / 2) ≤ (r7 : ℝ) := by
    have : Real.exp ((y : ℝ) / 2) = Real.exp ((y : ℝ) / 4) * Real.exp ((y : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he6 (by exact_mod_cast h7)
  have he8 : Real.exp (y : ℝ) ≤ (r8 : ℝ) := by
    have : Real.exp (y : ℝ) = Real.exp ((y : ℝ) / 2) * Real.exp ((y : ℝ) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; exact sq_step (Real.exp_pos _).le he7 (by exact_mod_cast h8)
  exact he8

/-- Exact rational check for one corner `(g_num, h_num)` against `U_plus` and squaring chain. -/
def checkCornerChain (g_num h_num : ℤ) (U y_hi r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℚ) : Bool :=
  decide (0 ≤ y_hi) &&
  decide (y_hi ≤ 256) &&
  decide (288 * ((128 * mpsNorm2Z : ℤ) : ℚ) +
      12 * ((128 * mpsFzzZ + g_num * mpsFxxZ + h_num * mpsFxZ : ℤ) : ℚ) ≤
    y_hi * ((128 * mpsNorm2Z : ℤ) : ℚ)) &&
  decide (expBoundBase9 y_hi ≤ r0) &&
  decide (r0 * r0 ≤ r1) &&
  decide (r1 * r1 ≤ r2) &&
  decide (r2 * r2 ≤ r3) &&
  decide (r3 * r3 ≤ r4) &&
  decide (r4 * r4 ≤ r5) &&
  decide (r5 * r5 ≤ r6) &&
  decide (r6 * r6 ≤ r7) &&
  decide (r7 * r7 ≤ r8) &&
  decide (877 * U ^ 4 * r8 ≤ 1000)

/-- Combined even-`X` partition function `Z_+(L, b; g, h) = Z_untw + Z_tw` for `H_ising`. -/
noncomputable def ZplusIsing (L : ℕ) (b g h : ℝ) : ℝ :=
  matZ (H_ising L g h false false) (H_ising_isHermitian L g h false false) b +
  matZ (H_ising L g h true false) (H_ising_isHermitian L g h true false) b

lemma ZplusIsing_pos (L : ℕ) (b g h : ℝ) : 0 < ZplusIsing L b g h := by
  haveI : Nonempty (Fin (2 ^ (L - 1))) := ⟨⟨0, by positivity⟩⟩
  exact add_pos (matZ_pos _ _ _) (matZ_pos _ _ _)

/-- Log-convexity target `F(g, h) = Z_+(8, 6; g, h)^4 * exp (12 * E_MPS(g, h))`. -/
noncomputable def rectTarget (g h : ℝ) : ℝ :=
  (ZplusIsing 8 6 g h) ^ 4 * Real.exp (12 * mpsEnergy g h)

set_option maxRecDepth 2000 in
lemma rectTarget_corner_le (g_num h_num : ℤ) (U y_hi r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℚ)
    (hZ : ZplusIsing 8 6 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) ≤ Real.exp 72 * (U : ℝ))
    (hchk : checkCornerChain g_num h_num U y_hi r0 r1 r2 r3 r4 r5 r6 r7 r8 = true) :
    rectTarget ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) ≤ (1000 / 877 : ℝ) := by
  unfold checkCornerChain at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy0, hy256⟩, hE_le⟩, hr0⟩, hr1⟩, hr2⟩, hr3⟩, hr4⟩, hr5⟩, hr6⟩, hr7⟩, hr8⟩, hprod⟩
  have hnorm_pos : (0 : ℝ) < (mpsNorm2Z : ℝ) := by unfold mpsNorm2Z; norm_num
  have h128norm_pos : (0 : ℝ) < ((128 * mpsNorm2Z : ℤ) : ℝ) := by push_cast; positivity
  have h288E : 288 + 12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128) ≤ (y_hi : ℝ) := by
    have hE_R : 288 * ((128 * mpsNorm2Z : ℤ) : ℝ) +
        12 * ((128 * mpsFzzZ + g_num * mpsFxxZ + h_num * mpsFxZ : ℤ) : ℝ) ≤
        (y_hi : ℝ) * ((128 * mpsNorm2Z : ℤ) : ℝ) := by exact_mod_cast hE_le
    unfold mpsEnergy
    rw [show 288 + 12 * (((mpsFzzZ : ℝ) + (g_num : ℝ) / 128 * (mpsFxxZ : ℝ) +
        (h_num : ℝ) / 128 * (mpsFxZ : ℝ)) / (mpsNorm2Z : ℝ)) =
        (288 * ((128 * mpsNorm2Z : ℤ) : ℝ) +
          12 * ((128 * mpsFzzZ + g_num * mpsFxxZ + h_num * mpsFxZ : ℤ) : ℝ)) /
        ((128 * mpsNorm2Z : ℤ) : ℝ) by
      push_cast; field_simp [hnorm_pos.ne']]
    exact (div_le_iff₀ h128norm_pos).mpr hE_R
  have hexp_le : Real.exp (288 + 12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) ≤ (r8 : ℝ) :=
    (Real.exp_le_exp.mpr h288E).trans
      (exp_le_pow256_of_chain hy0 hy256 r0 r1 r2 r3 r4 r5 r6 r7 r8 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8)
  have hZ_pow : (ZplusIsing 8 6 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) ^ 4 ≤
      Real.exp 288 * (U : ℝ) ^ 4 := by
    have h1 := pow_le_pow_left₀ (ZplusIsing_pos 8 6 _ _).le hZ 4
    rw [mul_pow, ← Real.exp_nat_mul] at h1
    simpa [show (4 : ℝ) * 72 = 288 by norm_num] using h1
  have hU4_nn : (0 : ℝ) ≤ (U : ℝ) ^ 4 := by positivity
  have hr8_nn : (0 : ℝ) ≤ (r8 : ℝ) := (Real.exp_pos _).le.trans hexp_le
  have hprod_R : (877 : ℝ) * (U : ℝ) ^ 4 * (r8 : ℝ) ≤ 1000 := by exact_mod_cast hprod
  unfold rectTarget
  have hsplit : Real.exp 288 * Real.exp (12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) =
      Real.exp (288 + 12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) :=
    (Real.exp_add _ _).symm
  calc (ZplusIsing 8 6 ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) ^ 4 *
          Real.exp (12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128))
      ≤ (Real.exp 288 * (U : ℝ) ^ 4) *
          Real.exp (12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) :=
        mul_le_mul_of_nonneg_right hZ_pow (Real.exp_pos _).le
    _ = (U : ℝ) ^ 4 * Real.exp (288 + 12 * mpsEnergy ((g_num : ℝ) / 128) ((h_num : ℝ) / 128)) := by
        rw [← hsplit]; ring
    _ ≤ (U : ℝ) ^ 4 * (r8 : ℝ) := mul_le_mul_of_nonneg_left hexp_le hU4_nn
    _ ≤ 1000 / 877 := by linarith

private theorem all_four_corner_chains_ok :
    checkCornerChain 15 47 U_15_47_plus (4373573 / 50000)
      (1407317473 / 1000000000) (198054247 / 100000000) (980637119 / 250000000)
      (307727731 / 20000000) (2367408911 / 10000000) (700578119 / 12500)
      3141182086 9867024898000000000 97358180340000000000000000000000000000 = true ∧
    checkCornerChain 15 48 U_15_48_plus (8711799 / 100000)
      (1405375671 / 1000000000) (1975080777 / 1000000000) (975236019 / 250000000)
      (1521736469 / 100000000) (1157840941 / 5000000) (5362382579 / 100000)
      2875514693 8268584750000000000 68369493770000000000000000000000000000 = true ∧
    checkCornerChain 16 47 U_16_47_plus (8726481 / 100000)
      (1406181907 / 1000000000) (494336889 / 250000000) (1954951679 / 500000000)
      (1528734427 / 100000000) (2337028949 / 10000000) (5461704309 / 100000)
      2983021396 8898416649000000000 79181818860000000000000000000000000000 = true ∧
    checkCornerChain 16 48 U_16_48_plus (4345567 / 50000)
      (1404241673 / 1000000000) (1971894677 / 1000000000) (1944184309 / 500000000)
      (1511941051 / 100000000) (1142982871 / 5000000) (2612819687 / 50000)
      2730730687 7456890085000000000 55605209740000000000000000000000000000 = true := by
  decide +kernel

set_option maxRecDepth 2000 in
/-- **Unconditional 2D Coupling-Rectangle Seed Theorem (Pure Kernel, Zero External Premises)**:
for **every** `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]`,
`(877 / 1000) * Z_+(8, 6; g, h)^4 ≤ Z_+(16, 12; g, h)`. -/
theorem candidate_e_rectangle_Qplus_ge {g h : ℝ}
    (hg0 : (15 / 128 : ℝ) ≤ g) (hg1 : g ≤ 16 / 128)
    (hh0 : (47 / 128 : ℝ) ≤ h) (hh1 : h ≤ 48 / 128) :
    (877 / 1000 : ℝ) * (ZplusIsing 8 6 g h) ^ 4 ≤ ZplusIsing 16 12 g h := by
  haveI : Nonempty (Fin (2 ^ (8 - 1))) := ⟨⟨0, by positivity⟩⟩
  haveI : Nonempty (Fin (2 ^ (16 - 1))) := ⟨⟨0, by positivity⟩⟩
  have hchains := all_four_corner_chains_ok
  have h00 : rectTarget (15 / 128) (47 / 128) ≤ 1000 / 877 :=
    rectTarget_corner_le 15 47 _ _ _ _ _ _ _ _ _ _ _ corner_15_47_Zplus_le hchains.1
  have h01 : rectTarget (15 / 128) (48 / 128) ≤ 1000 / 877 :=
    rectTarget_corner_le 15 48 _ _ _ _ _ _ _ _ _ _ _ corner_15_48_Zplus_le hchains.2.1
  have h10 : rectTarget (16 / 128) (47 / 128) ≤ 1000 / 877 :=
    rectTarget_corner_le 16 47 _ _ _ _ _ _ _ _ _ _ _ corner_16_47_Zplus_le hchains.2.2.1
  have h11 : rectTarget (16 / 128) (48 / 128) ≤ 1000 / 877 :=
    rectTarget_corner_le 16 48 _ _ _ _ _ _ _ _ _ _ _ corner_16_48_Zplus_le hchains.2.2.2
  have hpos : ∀ x y : ℝ, 0 < rectTarget x y := fun x y =>
    mul_pos (pow_pos (ZplusIsing_pos 8 6 x y) 4) (Real.exp_pos _)
  have hlog_pow4 : ∀ {z z₁ z₂ θ : ℝ}, 0 < z → 0 < z₁ → 0 < z₂ → 0 ≤ θ → θ ≤ 1 →
      z ≤ z₁ ^ (1 - θ) * z₂ ^ θ →
      z ^ 4 ≤ (z₁ ^ 4) ^ (1 - θ) * (z₂ ^ 4) ^ θ := by
    intro z z₁ z₂ θ hz hz₁ hz₂ hθ0 hθ1 hle
    have h4 := pow_le_pow_left₀ hz.le hle 4
    rw [mul_pow] at h4
    have hp : ∀ {a r : ℝ}, 0 ≤ a → (a ^ r) ^ (4 : ℕ) = (a ^ (4 : ℕ)) ^ r := fun {a r} ha => by
      rw [← Real.rpow_natCast (a ^ r) 4, ← Real.rpow_natCast a 4,
        ← Real.rpow_mul ha, ← Real.rpow_mul ha, mul_comm]
    rwa [hp hz₁.le, hp hz₂.le] at h4
  have hcx : ∀ a b y θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      rectTarget ((1 - θ) * a + θ * b) y ≤
        (rectTarget a y) ^ (1 - θ) * (rectTarget b y) ^ θ := by
    intro a b y θ hθ0 hθ1
    have hu : matZ (H_ising 8 ((1 - θ) * a + θ * b) y false false)
        (H_ising_isHermitian 8 _ y false false) 6 ≤
        (matZ (H_ising 8 a y false false) (H_ising_isHermitian 8 a y false false) 6) ^ (1 - θ) *
        (matZ (H_ising 8 b y false false) (H_ising_isHermitian 8 b y false false) 6) ^ θ := by
      have haff := H_ising_affine_g 8 a b y θ false false
      have hH := H_ising_isHermitian 8 ((1 - θ) * a + θ * b) y false false
      have hconv := matZ_convex_combo_le (H_ising 8 a y false false) (H_ising 8 b y false false)
        (H_ising_isHermitian 8 a y false false) (H_ising_isHermitian 8 b y false false)
        hθ0 hθ1 (haff ▸ hH) 6
      convert hconv using 1
      simp only [haff]
    have ht : matZ (H_ising 8 ((1 - θ) * a + θ * b) y true false)
        (H_ising_isHermitian 8 _ y true false) 6 ≤
        (matZ (H_ising 8 a y true false) (H_ising_isHermitian 8 a y true false) 6) ^ (1 - θ) *
        (matZ (H_ising 8 b y true false) (H_ising_isHermitian 8 b y true false) 6) ^ θ := by
      have haff := H_ising_affine_g 8 a b y θ true false
      have hH := H_ising_isHermitian 8 ((1 - θ) * a + θ * b) y true false
      have hconv := matZ_convex_combo_le (H_ising 8 a y true false) (H_ising 8 b y true false)
        (H_ising_isHermitian 8 a y true false) (H_ising_isHermitian 8 b y true false)
        hθ0 hθ1 (haff ▸ hH) 6
      convert hconv using 1
      simp only [haff]
    have hZ_lc : ZplusIsing 8 6 ((1 - θ) * a + θ * b) y ≤
        (ZplusIsing 8 6 a y) ^ (1 - θ) * (ZplusIsing 8 6 b y) ^ θ :=
      (add_le_add hu ht).trans (add_rpow_mul_rpow_le (matZ_pos _ _ _) (matZ_pos _ _ _)
        (matZ_pos _ _ _) (matZ_pos _ _ _) hθ0 hθ1)
    have hZ4_lc := hlog_pow4 (ZplusIsing_pos 8 6 _ _) (ZplusIsing_pos 8 6 a y)
      (ZplusIsing_pos 8 6 b y) hθ0 hθ1 hZ_lc
    have hE_aff : mpsEnergy ((1 - θ) * a + θ * b) y =
        (1 - θ) * mpsEnergy a y + θ * mpsEnergy b y := by
      unfold mpsEnergy; ring
    have hexp_eq : Real.exp (12 * mpsEnergy ((1 - θ) * a + θ * b) y) =
        (Real.exp (12 * mpsEnergy a y)) ^ (1 - θ) * (Real.exp (12 * mpsEnergy b y)) ^ θ := by
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, hE_aff]; congr 1; ring
    unfold rectTarget
    rw [hexp_eq, Real.mul_rpow (pow_nonneg (ZplusIsing_pos 8 6 a y).le 4) (Real.exp_pos _).le,
      Real.mul_rpow (pow_nonneg (ZplusIsing_pos 8 6 b y).le 4) (Real.exp_pos _).le]
    have hmul := mul_le_mul_of_nonneg_right hZ4_lc
      (mul_nonneg (Real.rpow_nonneg (Real.exp_pos (12 * mpsEnergy a y)).le (1 - θ))
        (Real.rpow_nonneg (Real.exp_pos (12 * mpsEnergy b y)).le θ))
    linarith
  have hcy : ∀ x a b θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      rectTarget x ((1 - θ) * a + θ * b) ≤
        (rectTarget x a) ^ (1 - θ) * (rectTarget x b) ^ θ := by
    intro x a b θ hθ0 hθ1
    have hu : matZ (H_ising 8 x ((1 - θ) * a + θ * b) false false)
        (H_ising_isHermitian 8 x _ false false) 6 ≤
        (matZ (H_ising 8 x a false false) (H_ising_isHermitian 8 x a false false) 6) ^ (1 - θ) *
        (matZ (H_ising 8 x b false false) (H_ising_isHermitian 8 x b false false) 6) ^ θ := by
      have haff := H_ising_affine_h 8 x a b θ false false
      have hH := H_ising_isHermitian 8 x ((1 - θ) * a + θ * b) false false
      have hconv := matZ_convex_combo_le (H_ising 8 x a false false) (H_ising 8 x b false false)
        (H_ising_isHermitian 8 x a false false) (H_ising_isHermitian 8 x b false false)
        hθ0 hθ1 (haff ▸ hH) 6
      convert hconv using 1
      simp only [haff]
    have ht : matZ (H_ising 8 x ((1 - θ) * a + θ * b) true false)
        (H_ising_isHermitian 8 x _ true false) 6 ≤
        (matZ (H_ising 8 x a true false) (H_ising_isHermitian 8 x a true false) 6) ^ (1 - θ) *
        (matZ (H_ising 8 x b true false) (H_ising_isHermitian 8 x b true false) 6) ^ θ := by
      have haff := H_ising_affine_h 8 x a b θ true false
      have hH := H_ising_isHermitian 8 x ((1 - θ) * a + θ * b) true false
      have hconv := matZ_convex_combo_le (H_ising 8 x a true false) (H_ising 8 x b true false)
        (H_ising_isHermitian 8 x a true false) (H_ising_isHermitian 8 x b true false)
        hθ0 hθ1 (haff ▸ hH) 6
      convert hconv using 1
      simp only [haff]
    have hZ_lc : ZplusIsing 8 6 x ((1 - θ) * a + θ * b) ≤
        (ZplusIsing 8 6 x a) ^ (1 - θ) * (ZplusIsing 8 6 x b) ^ θ :=
      (add_le_add hu ht).trans (add_rpow_mul_rpow_le (matZ_pos _ _ _) (matZ_pos _ _ _)
        (matZ_pos _ _ _) (matZ_pos _ _ _) hθ0 hθ1)
    have hZ4_lc := hlog_pow4 (ZplusIsing_pos 8 6 _ _) (ZplusIsing_pos 8 6 x a)
      (ZplusIsing_pos 8 6 x b) hθ0 hθ1 hZ_lc
    have hE_aff : mpsEnergy x ((1 - θ) * a + θ * b) =
        (1 - θ) * mpsEnergy x a + θ * mpsEnergy x b := by
      unfold mpsEnergy; ring
    have hexp_eq : Real.exp (12 * mpsEnergy x ((1 - θ) * a + θ * b)) =
        (Real.exp (12 * mpsEnergy x a)) ^ (1 - θ) * (Real.exp (12 * mpsEnergy x b)) ^ θ := by
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, hE_aff]; congr 1; ring
    unfold rectTarget
    rw [hexp_eq, Real.mul_rpow (pow_nonneg (ZplusIsing_pos 8 6 x a).le 4) (Real.exp_pos _).le,
      Real.mul_rpow (pow_nonneg (ZplusIsing_pos 8 6 x b).le 4) (Real.exp_pos _).le]
    have hmul := mul_le_mul_of_nonneg_right hZ4_lc
      (mul_nonneg (Real.rpow_nonneg (Real.exp_pos (12 * mpsEnergy x a)).le (1 - θ))
        (Real.rpow_nonneg (Real.exp_pos (12 * mpsEnergy x b)).le θ))
    linarith
  have hrect := log_convex_rectangle_le (by norm_num : (15 / 128 : ℝ) ≤ 16 / 128)
    (by norm_num : (47 / 128 : ℝ) ≤ 48 / 128) hpos hcx hcy h00 h01 h10 h11 hg0 hg1 hh0 hh1
  have hray_le : (877 / 1000 : ℝ) * (ZplusIsing 8 6 g h) ^ 4 ≤ Real.exp (-12 * mpsEnergy g h) := by
    unfold rectTarget at hrect
    have hinv : Real.exp (-12 * mpsEnergy g h) = (Real.exp (12 * mpsEnergy g h))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hinv]
    have h1 := mul_le_mul_of_nonneg_right hrect (Real.exp_pos (-12 * mpsEnergy g h)).le
    have hcancel : Real.exp (12 * mpsEnergy g h) * Real.exp (-12 * mpsEnergy g h) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hlhs : (ZplusIsing 8 6 g h) ^ 4 * Real.exp (12 * mpsEnergy g h) *
        Real.exp (-12 * mpsEnergy g h) = (ZplusIsing 8 6 g h) ^ 4 := by
      rw [mul_assoc, hcancel, mul_one]
    rw [hlhs] at h1
    rw [← hinv]
    linarith
  have hZ16 : Real.exp (-12 * mpsEnergy g h) ≤ ZplusIsing 16 12 g h := by
    unfold ZplusIsing
    linarith [mps16_rayleigh_le_matZ g h,
      matZ_pos (H_ising 16 g h true false) (H_ising_isHermitian 16 g h true false) 12]
  exact hray_le.trans hZ16

/-! ## Exact 3-Round Coupled Bootstrap `(8, 6) → (64, 48)` -/

def ceP0 : ℚ := 64 / 1000
def ceQ0 : ℚ := 123 / 1000
def ceP1 : ℚ := 454553 / 10 ^ 7
def ceQ1 : ℚ := 655532 / 10 ^ 7
def ceP2 : ℚ := 152251 / 10 ^ 7
def ceQ2 : ℚ := 132733 / 10 ^ 7
def ceP3 : ℚ := 10139 / 10 ^ 7
def ceQ3 : ℚ := 3956 / 10 ^ 7

theorem candidate_e_three_rounded_updates_exact :
    (1 - ceP0) ^ 2 ≤ 877 / 1000 ∧
    1 - ceQ0 ≤ 877 / 1000 ∧
    ceilGrid7 (fQ (1 - (1 - ceP0) ^ 2 * (1 - ceQ0))) = ceP1 ∧
    ceilGrid7 (fQ (1 - (1 - ceQ0) ^ 2 * (1 - ceP1))) = ceQ1 ∧
    ceilGrid7 (fQ (1 - (1 - ceP1) ^ 2 * (1 - ceQ1))) = ceP2 ∧
    ceilGrid7 (fQ (1 - (1 - ceQ1) ^ 2 * (1 - ceP2))) = ceQ2 ∧
    ceilGrid7 (fQ (1 - (1 - ceP2) ^ 2 * (1 - ceQ2))) = ceP3 ∧
    ceilGrid7 (fQ (1 - (1 - ceQ2) ^ 2 * (1 - ceP3))) = ceQ3 ∧
    ceP3 < 1 / 100 ∧ ceQ3 < 1 / 100 := by
  decide +kernel

/-- Propagate `Q_+(8, 6) = Z_+(16, 12) / Z_+(8, 6)^4 ≥ 877/1000` through 3 coupled bootstrap rounds
in any `PuritySystem1D` to reach `1 - S(64, 48) ≤ 1/100` and `1 - T(128, 48) ≤ 1/100`. -/
theorem candidate_e_three_rounds_to_64 (sys : PuritySystem1D)
    (hQ : (877 / 1000 : ℝ) * (sys.Z 8 6) ^ 4 ≤ sys.Z 16 12) :
    1 - sys.S 64 48 ≤ (1 / 100 : ℝ) ∧
    1 - sys.T 128 48 ≤ (1 / 100 : ℝ) := by
  have hex := candidate_e_three_rounded_updates_exact
  have hZ8_pos : 0 < sys.Z 8 6 := sys.Z_pos 8 6 ⟨4, by omega⟩ (by omega) (by norm_num)
  have hZ16_pos : 0 < sys.Z 16 6 := sys.Z_pos 16 6 ⟨8, by omega⟩ (by omega) (by norm_num)
  have hS_le1 : sys.S 8 6 ≤ 1 := sys.S_le_one 8 6 ⟨4, by omega⟩ (by omega) (by norm_num)
  have hS_pos : 0 < sys.S 8 6 := sys.S_pos ⟨4, by omega⟩ (by omega) (by norm_num)
  have hT_le1 : sys.T 16 6 ≤ 1 := sys.T_le_one 16 6 ⟨8, by omega⟩ (by omega) (by norm_num)
  have hT_pos : 0 < sys.T 16 6 := sys.T_pos ⟨8, by omega⟩ (by omega) (by norm_num)
  have hprod : (sys.S 8 6) ^ 2 * sys.T 16 6 = sys.Z 16 12 / (sys.Z 8 6) ^ 4 := by
    unfold PuritySystem1D.S PuritySystem1D.T
    have h16 : 2 * 8 = 16 := rfl
    have h12 : 2 * (6 : ℝ) = 12 := by norm_num
    rw [h16, h12]
    field_simp [hZ8_pos.ne', hZ16_pos.ne']
  have hQ_div : (877 / 1000 : ℝ) ≤ (sys.S 8 6) ^ 2 * sys.T 16 6 := by
    rw [hprod, le_div_iff₀ (pow_pos hZ8_pos 4)]
    exact hQ
  have hS0 : 1 - sys.S 8 6 ≤ (ceP0 : ℝ) := by
    have hsq : (1 - (ceP0 : ℝ)) ^ 2 ≤ (sys.S 8 6) ^ 2 := by
      have h1 : (1 - (ceP0 : ℝ)) ^ 2 ≤ 877 / 1000 := by unfold ceP0; norm_num
      have h2 : (sys.S 8 6) ^ 2 * sys.T 16 6 ≤ (sys.S 8 6) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hT_le1 (sq_nonneg _)
      linarith
    have hle : 1 - (ceP0 : ℝ) ≤ sys.S 8 6 := by
      have hnn : 0 ≤ 1 - (ceP0 : ℝ) := by unfold ceP0; norm_num
      nlinarith
    linarith
  have hT0 : 1 - sys.T 16 6 ≤ (ceQ0 : ℝ) := by
    have hS2_le1 : (sys.S 8 6) ^ 2 ≤ 1 := by nlinarith
    have h2 : (sys.S 8 6) ^ 2 * sys.T 16 6 ≤ 1 * sys.T 16 6 :=
      mul_le_mul_of_nonneg_right hS2_le1 hT_pos.le
    have h1 : 1 - (ceQ0 : ℝ) ≤ 877 / 1000 := by unfold ceQ0; norm_num
    linarith
  have step : ∀ {n : ℕ} {b : ℝ} {p q p' q' : ℚ},
      Even n → 4 ≤ n → 0 < b →
      0 ≤ p → p < 1 → 0 ≤ q → q < 1 → p' < 1 →
      ceilGrid7 (fQ (1 - (1 - p) ^ 2 * (1 - q))) = p' →
      ceilGrid7 (fQ (1 - (1 - q) ^ 2 * (1 - p'))) = q' →
      1 - sys.S n b ≤ (p : ℝ) → 1 - sys.T (2 * n) b ≤ (q : ℝ) →
      1 - sys.S (2 * n) (2 * b) ≤ (p' : ℝ) ∧ 1 - sys.T (4 * n) (2 * b) ≤ (q' : ℝ) := by
    intro n b p q p' q' hn h4 hb hp0 hp1 hq0 hq1 hp'1 hp'eq hq'eq hS hT
    have hp'_R : purityUpdate (1 - (1 - (p : ℝ)) ^ 2 * (1 - (q : ℝ))) ≤ (p' : ℝ) := by
      have hcast : ((fQ (1 - (1 - p) ^ 2 * (1 - q)) : ℚ) : ℝ) ≤ (p' : ℝ) := by
        exact_mod_cast (hp'eq ▸ le_ceilGrid7 _)
      rw [fQ_cast] at hcast; push_cast at hcast; exact hcast
    have hq'_R : purityUpdate (1 - (1 - (q : ℝ)) ^ 2 * (1 - (p' : ℝ))) ≤ (q' : ℝ) := by
      have hcast : ((fQ (1 - (1 - q) ^ 2 * (1 - p')) : ℚ) : ℝ) ≤ (q' : ℝ) := by
        exact_mod_cast (hq'eq ▸ le_ceilGrid7 _)
      rw [fQ_cast] at hcast; push_cast at hcast; exact hcast
    exact sys.rounded_coupled_update hn h4 hb
      (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq0) (by exact_mod_cast hq1)
      (by exact_mod_cast hp'1) hS hT hp'_R hq'_R
  have r1 := step (n := 8) (b := 6) ⟨4, by omega⟩ (by omega) (by norm_num)
    (by unfold ceP0; norm_num) (by unfold ceP0; norm_num)
    (by unfold ceQ0; norm_num) (by unfold ceQ0; norm_num)
    (by unfold ceP1; norm_num) hex.2.2.1 hex.2.2.2.1 hS0 hT0
  have r2 := step (n := 16) (b := 12) ⟨8, by omega⟩ (by omega) (by norm_num)
    (by unfold ceP1; norm_num) (by unfold ceP1; norm_num)
    (by unfold ceQ1; norm_num) (by unfold ceQ1; norm_num)
    (by unfold ceP2; norm_num) hex.2.2.2.2.1 hex.2.2.2.2.2.1
    (by convert r1.1 using 2 <;> norm_num) (by convert r1.2 using 2 <;> norm_num)
  have r3 := step (n := 32) (b := 24) ⟨16, by omega⟩ (by omega) (by norm_num)
    (by unfold ceP2; norm_num) (by unfold ceP2; norm_num)
    (by unfold ceQ2; norm_num) (by unfold ceQ2; norm_num)
    (by unfold ceP3; norm_num) hex.2.2.2.2.2.2.1 hex.2.2.2.2.2.2.2.1
    (by convert r2.1 using 2 <;> norm_num) (by convert r2.2 using 2 <;> norm_num)
  have hp3 : (ceP3 : ℝ) < (1 / 100 : ℝ) := by unfold ceP3; norm_num
  have hq3 : (ceQ3 : ℝ) < (1 / 100 : ℝ) := by unfold ceQ3; norm_num
  constructor
  · have h1 : 1 - sys.S 64 48 ≤ (ceP3 : ℝ) := by convert r3.1 using 2 <;> norm_num
    linarith
  · have h2 : 1 - sys.T 128 48 ≤ (ceQ3 : ℝ) := by convert r3.2 using 2 <;> norm_num
    linarith

/-- **Boxed Candidate E 2D Rectangle Multiplet Theorem**:
for any `(g, h) ∈ [15/128, 16/128] × [47/128, 48/128]` and any `IsingTwistSystem` matching the
finite-size partition functions `ZplusIsing` at `(8, 6)` and `(16, 12)` (instantiated
unconditionally in `IsingTrotter`), for **every even `ℓ ≥ 64`**:
- `0 ≤ W_ℓ = E_1(ℓ) - E_0(ℓ) ≤ (1 / 20) * exp (-(log 20) * ℓ / 128)`,
- `Γ_ℓ = E_i(ℓ) - E_1(ℓ) > log 8 / 48` for every excited level `i ≥ 2`. -/
theorem candidate_e_rectangle_multiplet {g h : ℝ}
    (hg0 : (15 / 128 : ℝ) ≤ g) (hg1 : g ≤ 16 / 128)
    (hh0 : (47 / 128 : ℝ) ≤ h) (hh1 : h ≤ 48 / 128)
    (sys : IsingTwistSystem)
    (hZ8 : sys.Zplus 8 6 = Real.exp (-6 * sys.a * 8) * ZplusIsing 8 6 g h)
    (hZ16 : sys.Zplus 16 12 = Real.exp (-12 * sys.a * 16) * ZplusIsing 16 12 g h)
    {ℓ : ℕ} (hℓ_even : Even ℓ) (hℓ_ge : 64 ≤ ℓ) :
    let raw := List.ofFn (sys.E_pu ℓ) ++ List.ofFn (sys.E_mu ℓ)
    let sorted := raw.mergeSort (· ≤ ·)
    2 ≤ sorted.length ∧
    (∀ h0 h1, 0 ≤ sorted[1]'h1 - sorted[0]'h0 ∧
      sorted[1]'h1 - sorted[0]'h0 ≤
        (1 / 20 : ℝ) * Real.exp (-(Real.log 20) * (ℓ : ℝ) / 128)) ∧
    (∀ i (hi : i < sorted.length) (h1 : 1 < sorted.length), 2 ≤ i →
      Real.log 8 / 48 < sorted[i]'hi - sorted[1]'h1) := by
  have hQ_ising := candidate_e_rectangle_Qplus_ge hg0 hg1 hh0 hh1
  let psys := sys.toSpectralSystem1D.toPuritySystem1D
  have hZ_eq : ∀ L b, Even L → 4 ≤ L → 0 < b → psys.Z L b = sys.Zplus L b := fun L b _ h4 hb =>
    sys.toSpectralSystem1D_Z h4 hb
  have hQ_sys : (877 / 1000 : ℝ) * (psys.Z 8 6) ^ 4 ≤ psys.Z 16 12 := by
    have h1 : psys.Z 8 6 = sys.Zplus 8 6 := hZ_eq 8 6 ⟨4, by omega⟩ (by omega) (by norm_num)
    have h2 : psys.Z 16 12 = sys.Zplus 16 12 := hZ_eq 16 12 ⟨8, by omega⟩ (by omega) (by norm_num)
    rw [h1, h2, hZ8, hZ16, mul_pow, ← Real.exp_nat_mul]
    have hexp_eq : (4 : ℕ) * (-6 * sys.a * 8) = -12 * sys.a * 16 := by push_cast; ring
    rw [hexp_eq]
    have hmul := mul_le_mul_of_nonneg_left hQ_ising (Real.exp_pos (-12 * sys.a * 16)).le
    linarith
  have h64 := candidate_e_three_rounds_to_64 psys hQ_sys
  have hS64 : 1 - sys.Splus 64 48 ≤ 1 / 100 := by
    have heq : psys.S 64 48 = sys.Splus 64 48 := by
      unfold PuritySystem1D.S IsingTwistSystem.Splus
      rw [hZ_eq (2 * 64) 48 ⟨64, by omega⟩ (by omega) (by norm_num),
        hZ_eq 64 48 ⟨32, by omega⟩ (by omega) (by norm_num)]
    have h1 := h64.1
    rw [heq] at h1
    exact h1
  have hT128 : 1 - sys.Tplus 128 48 ≤ 1 / 100 := by
    have heq : psys.T 128 48 = sys.Tplus 128 48 := by
      unfold PuritySystem1D.T IsingTwistSystem.Tplus
      rw [hZ_eq 128 (2 * 48) ⟨64, by omega⟩ (by omega) (by norm_num),
        hZ_eq 128 48 ⟨64, by omega⟩ (by omega) (by norm_num)]
    have h2 := h64.2
    rw [heq] at h2
    exact h2
  have hres := sys.ising_multiplet_sorted ⟨32, by omega⟩ (by omega) (by norm_num : (0 : ℝ) < 48)
    hS64 hT128 hℓ_even hℓ_ge
  have hc1 : (12 : ℝ) / (5 * 48) = 1 / 20 := by norm_num
  have hc2 : (2 : ℝ) * ((64 : ℕ) : ℝ) = 128 := by norm_num
  rw [hc1, hc2] at hres
  exact hres

end PurityBootstrap.CandidateE
