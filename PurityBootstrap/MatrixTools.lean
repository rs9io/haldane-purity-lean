import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Finite-Dimensional Matrix Spectral Tools for Certified Purity-Bootstrap Witnesses

Provides pure-kernel (standard axioms only) linear algebra theorems used to certify
finite-size Hamiltonian partition functions directly inside Lean 4:
1. **`matZ H hH b`**: thermal trace `∑ k, exp (-b * λ_k(H))` of a real symmetric matrix.
2. **Rayleigh–Ritz lower bound (`exp_rayleigh_le_matZ`)**: for any nonzero vector `v`,
   `exp (-b * ⟨v, H v⟩ / ⟨v, v⟩) ≤ matZ H hH b`.
3. **Peierls–Bogoliubov–Young log-convexity (`matZ_convex_combo_le`, `matZ_add_convex_combo_le`)**:
   proves `Z((1-θ)H₁ + θ H₂) ≤ Z(H₁)^(1-θ) Z(H₂)^θ` directly from `IsHermitian.eigenvectorBasis`,
   scalar `convexOn_exp`, and weighted AM–GM — enabling continuous coupling-rectangle certificates
   from the 4 corners alone.
4. **Gershgorin + Courant–Fischer eigenvalue enclosure (`gershgorin_matZ_le`)**:
   given an approximate eigenvector matrix `Q` whose Gram matrix `Qᵀ Q ≈ I` (row-sum defect `≤ ε₁ < 1`)
   and shifted congruence `Qᵀ (H + s I) Q` have row-wise Gershgorin lower bounds `μ_i ≥ 0`,
   proves `matZ H hH b ≤ ∑ i, exp (-b * (μ_i / (1 + ε₁) - s))`.
5. **Argument-reduced rational bounds on `Real.exp`** (`exp_div_pow2_lower`, `exp_neg_div_pow2_upper`).
-/

namespace PurityBootstrap.MatrixTools

open scoped BigOperators Matrix
open Matrix

/-- Thermal partition function `Z(H, b) = ∑ k, exp (-b * λ_k(H))` of a real symmetric matrix. -/
noncomputable def matZ {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) (b : ℝ) : ℝ :=
  ∑ k : n, Real.exp (-b * hH.eigenvalues k)

lemma matZ_pos {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) (b : ℝ) : 0 < matZ H hH b := by
  unfold matZ
  exact Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty

/-- Express the real quadratic form `v ⬝ᵥ H *ᵥ v` in the orthonormal eigenbasis of `H`. -/
lemma dotProduct_mulVec_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) (v : n → ℝ) :
    dotProduct v (H.mulVec v) =
      ∑ k : n, hH.eigenvalues k *
        (dotProduct (hH.eigenvectorBasis k).ofLp v) ^ 2 := by
  let b := hH.eigenvectorBasis
  let x : EuclideanSpace ℝ n := WithLp.toLp 2 v
  have hcoord : ∀ k, (b.repr x) k = dotProduct (b k).ofLp v := fun k => by
    rw [OrthonormalBasis.repr_apply_apply]
    simp [x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hx_eq : v = ∑ k : n, (dotProduct (b k).ofLp v) • (b k).ofLp := by
    have h1 := b.sum_repr x
    have h2 : (∑ k : n, (b.repr x) k • b k).ofLp = x.ofLp := congrArg WithLp.ofLp h1
    rw [WithLp.ofLp_sum] at h2
    simpa [x, hcoord] using h2.symm
  have hHx : H.mulVec v =
      ∑ k : n, (hH.eigenvalues k * dotProduct (b k).ofLp v) • (b k).ofLp := by
    conv_lhs => rw [hx_eq]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul, hH.mulVec_eigenvectorBasis k, smul_smul, mul_comm]
  rw [hHx, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-- Parseval identity for `dotProduct v v` in `hH.eigenvectorBasis`. -/
lemma dotProduct_self_eq_sum_sq {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) (v : n → ℝ) :
    dotProduct v v = ∑ k : n, (dotProduct (hH.eigenvectorBasis k).ofLp v) ^ 2 := by
  let b := hH.eigenvectorBasis
  let x : EuclideanSpace ℝ n := WithLp.toLp 2 v
  have hcoord : ∀ k, (b.repr x) k = dotProduct (b k).ofLp v := fun k => by
    rw [OrthonormalBasis.repr_apply_apply]
    simp [x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hnorm := b.repr.norm_map x
  have hsq : ‖b.repr x‖ ^ 2 = ‖x‖ ^ 2 := by rw [hnorm]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hsq
  have hL : ∑ k : n, ‖(b.repr x) k‖ ^ 2 = ∑ k : n, (dotProduct (b k).ofLp v) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [hcoord k, Real.norm_eq_abs, sq_abs]
  have hR : ∑ i : n, ‖x i‖ ^ 2 = dotProduct v v := by
    simp [x, dotProduct, Real.norm_eq_abs, sq_abs, sq]
  linarith

/-- **Rayleigh–Ritz lower bound on `matZ`**:
for any real symmetric `H`, nonzero `v`, and `b > 0`,
`exp (-b * (v ⬝ᵥ H *ᵥ v) / (v ⬝ᵥ v)) ≤ matZ H hH b`. -/
theorem exp_rayleigh_le_matZ {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) {b : ℝ} (hb : 0 < b)
    (v : n → ℝ) (hv : 0 < dotProduct v v) :
    Real.exp (-b * (dotProduct v (H.mulVec v) / dotProduct v v)) ≤ matZ H hH b := by
  rcases Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty with
    ⟨k₀, _, hk₀⟩
  have hmin : hH.eigenvalues k₀ ≤ dotProduct v (H.mulVec v) / dotProduct v v := by
    rw [le_div_iff₀ hv, dotProduct_mulVec_eq_sum_eigenvalues H hH v,
      dotProduct_self_eq_sum_sq H hH v, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (hk₀ k (Finset.mem_univ k)) (sq_nonneg _)
  have hexp_le :
      Real.exp (-b * (dotProduct v (H.mulVec v) / dotProduct v v)) ≤
        Real.exp (-b * hH.eigenvalues k₀) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsingle : Real.exp (-b * hH.eigenvalues k₀) ≤ matZ H hH b :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ k₀)
  exact hexp_le.trans hsingle

/-- Scalar Jensen inequality in the eigenbasis of `H`: for any unit vector `u` (`u ⬝ᵥ u = 1`),
`exp (-b * (u ⬝ᵥ H *ᵥ u)) ≤ ∑ j, (u_j)^2 * exp (-b * λ_j(H))`
where `u_j = (hH.eigenvectorBasis j).ofLp ⬝ᵥ u`. -/
lemma exp_quad_le_sum_sq_exp {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) (b : ℝ) (u : n → ℝ) (hu : dotProduct u u = 1) :
    Real.exp (-b * dotProduct u (H.mulVec u)) ≤
      ∑ j : n, (dotProduct (hH.eigenvectorBasis j).ofLp u) ^ 2 *
        Real.exp (-b * hH.eigenvalues j) := by
  let w : n → ℝ := fun j => (dotProduct (hH.eigenvectorBasis j).ofLp u) ^ 2
  have hw_nn : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ w j := fun j _ => sq_nonneg _
  have hw_sum : ∑ j : n, w j = 1 := by
    rw [← dotProduct_self_eq_sum_sq H hH u, hu]
  have hquad : -b * dotProduct u (H.mulVec u) = ∑ j : n, w j • (-b * hH.eigenvalues j) := by
    rw [dotProduct_mulVec_eq_sum_eigenvalues H hH u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp [w]; ring
  rw [hquad]
  have hj := convexOn_exp.map_sum_le (p := fun j => -b * hH.eigenvalues j)
    hw_nn hw_sum (fun j _ => Set.mem_univ _)
  simpa [w, smul_eq_mul] using hj

/-- Double-sum completeness of two orthonormal bases:
`∑ k, ∑ j, ((b₁ j) ⬝ᵥ (b₂ k))^2 * f j = ∑ j, f j`. -/
lemma sum_orthonormal_overlap_sq {n : Type*} [Fintype n] [DecidableEq n]
    (b₁ b₂ : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (f : n → ℝ) :
    ∑ k : n, ∑ j : n, (dotProduct (b₁ j).ofLp (b₂ k).ofLp) ^ 2 * f j = ∑ j : n, f j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  have hnorm : ∑ k : n, (dotProduct (b₁ j).ofLp (b₂ k).ofLp) ^ 2 = 1 := by
    have hcoord : ∀ k, (b₂.repr (b₁ j)) k = dotProduct (b₁ j).ofLp (b₂ k).ofLp := fun k => by
      rw [OrthonormalBasis.repr_apply_apply]
      simp [EuclideanSpace.inner_eq_star_dotProduct]
    have hsq : ‖b₂.repr (b₁ j)‖ ^ 2 = ‖b₁ j‖ ^ 2 := by rw [b₂.repr.norm_map]
    rw [b₁.orthonormal.1, one_pow, EuclideanSpace.norm_sq_eq] at hsq
    have hL : ∑ k : n, ‖(b₂.repr (b₁ j)) k‖ ^ 2 =
        ∑ k : n, (dotProduct (b₁ j).ofLp (b₂ k).ofLp) ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hcoord k, Real.norm_eq_abs, sq_abs]
    linarith
  rw [hnorm, one_mul]

/-- **Peierls–Bogoliubov–Young Log-Convexity of `matZ`**:
for any real symmetric `H₁, H₂`, `b : ℝ`, and `0 ≤ θ ≤ 1`,
`matZ ((1 - θ) • H₁ + θ • H₂) hH b ≤ (matZ H₁ hH₁ b) ^ (1 - θ) * (matZ H₂ hH₂ b) ^ θ`. -/
theorem matZ_convex_combo_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H₁ H₂ : Matrix n n ℝ) (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hH : ((1 - θ) • H₁ + θ • H₂).IsHermitian) (b : ℝ) :
    matZ ((1 - θ) • H₁ + θ • H₂) hH b ≤
      (matZ H₁ hH₁ b) ^ (1 - θ) * (matZ H₂ hH₂ b) ^ θ := by
  set Z₁ := matZ H₁ hH₁ b
  set Z₂ := matZ H₂ hH₂ b
  have hZ₁_pos : 0 < Z₁ := matZ_pos H₁ hH₁ b
  have hZ₂_pos : 0 < Z₂ := matZ_pos H₂ hH₂ b
  have hden_pos : 0 < Z₁ ^ (1 - θ) * Z₂ ^ θ :=
    mul_pos (Real.rpow_pos_of_pos hZ₁_pos _) (Real.rpow_pos_of_pos hZ₂_pos _)
  let u : n → (n → ℝ) := fun k => (hH.eigenvectorBasis k).ofLp
  let a : n → ℝ := fun k =>
    ∑ j : n, (dotProduct (hH₁.eigenvectorBasis j).ofLp (u k)) ^ 2 *
      Real.exp (-b * hH₁.eigenvalues j)
  let c : n → ℝ := fun k =>
    ∑ j : n, (dotProduct (hH₂.eigenvectorBasis j).ofLp (u k)) ^ 2 *
      Real.exp (-b * hH₂.eigenvalues j)
  have hu_unit : ∀ k, dotProduct (u k) (u k) = 1 := fun k => by
    have h := hH.eigenvectorBasis.orthonormal.1 k
    have hsq : ‖hH.eigenvectorBasis k‖ ^ 2 = 1 := by rw [h, one_pow]
    rw [EuclideanSpace.norm_sq_eq] at hsq
    simpa [u, dotProduct, Real.norm_eq_abs, sq_abs, sq] using hsq
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hc_nn : ∀ k, 0 ≤ c k := fun k =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have ha_sum : ∑ k : n, a k = Z₁ :=
    sum_orthonormal_overlap_sq hH₁.eigenvectorBasis hH.eigenvectorBasis
      (fun j => Real.exp (-b * hH₁.eigenvalues j))
  have hc_sum : ∑ k : n, c k = Z₂ :=
    sum_orthonormal_overlap_sq hH₂.eigenvectorBasis hH.eigenvectorBasis
      (fun j => Real.exp (-b * hH₂.eigenvalues j))
  have hterm : ∀ k : n,
      Real.exp (-b * hH.eigenvalues k) / (Z₁ ^ (1 - θ) * Z₂ ^ θ) ≤
        (1 - θ) * (a k / Z₁) + θ * (c k / Z₂) := fun k => by
    have heig : hH.eigenvalues k =
        (1 - θ) * dotProduct (u k) (H₁.mulVec (u k)) +
        θ * dotProduct (u k) (H₂.mulVec (u k)) := by
      have h1 : dotProduct (u k) (((1 - θ) • H₁ + θ • H₂).mulVec (u k)) = hH.eigenvalues k := by
        rw [hH.mulVec_eigenvectorBasis k, dotProduct_smul, smul_eq_mul, hu_unit k, mul_one]
      rw [← h1, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hexp_split :
        Real.exp (-b * hH.eigenvalues k) =
          (Real.exp (-b * dotProduct (u k) (H₁.mulVec (u k)))) ^ (1 - θ) *
          (Real.exp (-b * dotProduct (u k) (H₂.mulVec (u k)))) ^ θ := by
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, heig]
      congr 1; ring
    have hj1 : Real.exp (-b * dotProduct (u k) (H₁.mulVec (u k))) ≤ a k :=
      exp_quad_le_sum_sq_exp H₁ hH₁ b (u k) (hu_unit k)
    have hj2 : Real.exp (-b * dotProduct (u k) (H₂.mulVec (u k))) ≤ c k :=
      exp_quad_le_sum_sq_exp H₂ hH₂ b (u k) (hu_unit k)
    have hprod : Real.exp (-b * hH.eigenvalues k) ≤ a k ^ (1 - θ) * c k ^ θ := by
      rw [hexp_split]
      exact mul_le_mul
        (Real.rpow_le_rpow (Real.exp_pos _).le hj1 (by linarith))
        (Real.rpow_le_rpow (Real.exp_pos _).le hj2 hθ0)
        (Real.rpow_nonneg (Real.exp_pos _).le _)
        (Real.rpow_nonneg (ha_nn k) _)
    have hdiv : Real.exp (-b * hH.eigenvalues k) / (Z₁ ^ (1 - θ) * Z₂ ^ θ) ≤
        (a k / Z₁) ^ (1 - θ) * (c k / Z₂) ^ θ := by
      rw [Real.div_rpow (ha_nn k) hZ₁_pos.le, Real.div_rpow (hc_nn k) hZ₂_pos.le, div_mul_div_comm]
      exact div_le_div_of_nonneg_right hprod hden_pos.le
    exact hdiv.trans (Real.geom_mean_le_arith_mean2_weighted (by linarith) hθ0
      (div_nonneg (ha_nn k) hZ₁_pos.le) (div_nonneg (hc_nn k) hZ₂_pos.le) (by ring))
  have hsum_le : matZ ((1 - θ) • H₁ + θ • H₂) hH b / (Z₁ ^ (1 - θ) * Z₂ ^ θ) ≤ 1 := by
    unfold matZ
    rw [Finset.sum_div]
    calc ∑ k : n, Real.exp (-b * hH.eigenvalues k) / (Z₁ ^ (1 - θ) * Z₂ ^ θ)
        ≤ ∑ k : n, ((1 - θ) * (a k / Z₁) + θ * (c k / Z₂)) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (1 - θ) * ((∑ k : n, a k) / Z₁) + θ * ((∑ k : n, c k) / Z₂) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_div, ← Finset.sum_div]
      _ = 1 := by rw [ha_sum, hc_sum, div_self hZ₁_pos.ne', div_self hZ₂_pos.ne']; ring
  exact (div_le_one hden_pos).mp hsum_le

/-- Two-term weighted Hölder inequality:
`a₁^(1-θ) b₁^θ + a₂^(1-θ) b₂^θ ≤ (a₁ + a₂)^(1-θ) (b₁ + b₂)^θ` for nonnegative reals and `θ ∈ [0,1]`. -/
lemma add_rpow_mul_rpow_le {a₁ a₂ b₁ b₂ θ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    a₁ ^ (1 - θ) * b₁ ^ θ + a₂ ^ (1 - θ) * b₂ ^ θ ≤
      (a₁ + a₂) ^ (1 - θ) * (b₁ + b₂) ^ θ := by
  have ha : 0 < a₁ + a₂ := by linarith
  have hb : 0 < b₁ + b₂ := by linarith
  have hden : 0 < (a₁ + a₂) ^ (1 - θ) * (b₁ + b₂) ^ θ :=
    mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  rw [← div_le_one hden, add_div]
  have h1 : a₁ ^ (1 - θ) * b₁ ^ θ / ((a₁ + a₂) ^ (1 - θ) * (b₁ + b₂) ^ θ) ≤
      (1 - θ) * (a₁ / (a₁ + a₂)) + θ * (b₁ / (b₁ + b₂)) := by
    rw [← div_mul_div_comm, ← Real.div_rpow ha₁.le ha.le, ← Real.div_rpow hb₁.le hb.le]
    exact Real.geom_mean_le_arith_mean2_weighted (by linarith) hθ0
      (div_nonneg ha₁.le ha.le) (div_nonneg hb₁.le hb.le) (by ring)
  have h2 : a₂ ^ (1 - θ) * b₂ ^ θ / ((a₁ + a₂) ^ (1 - θ) * (b₁ + b₂) ^ θ) ≤
      (1 - θ) * (a₂ / (a₁ + a₂)) + θ * (b₂ / (b₁ + b₂)) := by
    rw [← div_mul_div_comm, ← Real.div_rpow ha₂.le ha.le, ← Real.div_rpow hb₂.le hb.le]
    exact Real.geom_mean_le_arith_mean2_weighted (by linarith) hθ0
      (div_nonneg ha₂.le ha.le) (div_nonneg hb₂.le hb.le) (by ring)
  have hsum : (1 - θ) * (a₁ / (a₁ + a₂)) + θ * (b₁ / (b₁ + b₂)) +
      ((1 - θ) * (a₂ / (a₁ + a₂)) + θ * (b₂ / (b₁ + b₂))) = 1 := by
    have ha1 : a₁ / (a₁ + a₂) + a₂ / (a₁ + a₂) = 1 := by rw [← add_div, div_self ha.ne']
    have hb1 : b₁ / (b₁ + b₂) + b₂ / (b₁ + b₂) = 1 := by rw [← add_div, div_self hb.ne']
    calc (1 - θ) * (a₁ / (a₁ + a₂)) + θ * (b₁ / (b₁ + b₂)) +
          ((1 - θ) * (a₂ / (a₁ + a₂)) + θ * (b₂ / (b₁ + b₂)))
        = (1 - θ) * (a₁ / (a₁ + a₂) + a₂ / (a₁ + a₂)) +
          θ * (b₁ / (b₁ + b₂) + b₂ / (b₁ + b₂)) := by ring
      _ = 1 := by rw [ha1, hb1]; ring
  linarith

/-- Log-convexity on a 2D rectangle: if `F : ℝ × ℝ → ℝ` is positive and satisfies
`F ((1-θ)x₁ + θ x₂, y) ≤ F(x₁, y)^(1-θ) F(x₂, y)^θ` (and likewise in `y`),
then for all `(x, y) ∈ [x₀, x₁] × [y₀, y₁]`,
`F(x, y) ≤ max (max (F(x₀, y₀)) (F(x₀, y₁))) (max (F(x₁, y₀)) (F(x₁, y₁)))`. -/
theorem log_convex_rectangle_le {F : ℝ → ℝ → ℝ} {x₀ x₁ y₀ y₁ M : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hpos : ∀ x y, 0 < F x y)
    (hcx : ∀ a b y θ, 0 ≤ θ → θ ≤ 1 →
      F ((1 - θ) * a + θ * b) y ≤ F a y ^ (1 - θ) * F b y ^ θ)
    (hcy : ∀ x a b θ, 0 ≤ θ → θ ≤ 1 →
      F x ((1 - θ) * a + θ * b) ≤ F x a ^ (1 - θ) * F x b ^ θ)
    (h00 : F x₀ y₀ ≤ M) (h01 : F x₀ y₁ ≤ M) (h10 : F x₁ y₀ ≤ M) (h11 : F x₁ y₁ ≤ M)
    {x y : ℝ} (hx0 : x₀ ≤ x) (hx1 : x ≤ x₁) (hy0 : y₀ ≤ y) (hy1 : y ≤ y₁) :
    F x y ≤ M := by
  have hseg : ∀ {u a b : ℝ} (hab : a ≤ b) (hu : a ≤ u) (hv : u ≤ b)
      (f : ℝ → ℝ), (∀ t, 0 < f t) →
      (∀ θ, 0 ≤ θ → θ ≤ 1 → f ((1 - θ) * a + θ * b) ≤ f a ^ (1 - θ) * f b ^ θ) →
      f a ≤ M → f b ≤ M → f u ≤ M := by
    intro u a b hab hu hv f hfpos hfc hfa hfb
    by_cases heq : a = b
    · have : u = a := le_antisymm (heq ▸ hv) hu; rwa [this]
    · have hlt : a < b := lt_of_le_of_ne hab heq
      set θ := (u - a) / (b - a)
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
      have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have hu_eq : (1 - θ) * a + θ * b = u := by
        dsimp [θ]; field_simp [(by linarith : b - a ≠ 0)]; ring
      have h1 := hfc θ hθ0 hθ1
      rw [hu_eq] at h1
      have hMpos : 0 < M := lt_of_lt_of_le (hfpos a) hfa
      have h2 : f a ^ (1 - θ) * f b ^ θ ≤ M ^ (1 - θ) * M ^ θ :=
        mul_le_mul (Real.rpow_le_rpow (hfpos a).le hfa (by linarith))
          (Real.rpow_le_rpow (hfpos b).le hfb hθ0)
          (Real.rpow_nonneg (hfpos b).le _) (Real.rpow_nonneg hMpos.le _)
      have h3 : M ^ (1 - θ) * M ^ θ = M := by
        rw [← Real.rpow_add hMpos]; simp
      linarith
  have hFx0 : F x y₀ ≤ M := hseg hx hx0 hx1 (fun t => F t y₀) (fun t => hpos t y₀)
    (fun θ h0 h1 => hcx x₀ x₁ y₀ θ h0 h1) h00 h10
  have hFx1 : F x y₁ ≤ M := hseg hx hx0 hx1 (fun t => F t y₁) (fun t => hpos t y₁)
    (fun θ h0 h1 => hcx x₀ x₁ y₁ θ h0 h1) h01 h11
  exact hseg hy hy0 hy1 (fun t => F x t) (fun t => hpos x t)
    (fun θ h0 h1 => hcy x y₀ y₁ θ h0 h1) hFx0 hFx1

/-! ## Gershgorin + Courant–Fischer Eigenvalue Enclosure -/

/-- Elementary Gershgorin quadratic-form bound for any symmetric matrix `M`:
`∑ i, (M i i - ∑ j ≠ i, |M i j|) * w_i^2 ≤ w ⬝ᵥ M *ᵥ w ≤ ∑ i, (M i i + ∑ j ≠ i, |M i j|) * w_i^2`. -/
lemma gershgorin_quad_bounds {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsHermitian) (w : n → ℝ) :
    ∑ i : n, (M i i - ∑ j ∈ Finset.univ.erase i, |M i j|) * (w i) ^ 2 ≤
      dotProduct w (M.mulVec w) ∧
    dotProduct w (M.mulVec w) ≤
      ∑ i : n, (M i i + ∑ j ∈ Finset.univ.erase i, |M i j|) * (w i) ^ 2 := by
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [conjTranspose_apply] using this
  have hquad : dotProduct w (M.mulVec w) =
      (∑ i : n, M i i * w i ^ 2) +
      (∑ i : n, ∑ j ∈ Finset.univ.erase i, M i j * w i * w j) := by
    simp only [dotProduct, mulVec]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => by ring
  have hoff_abs :
      |∑ i : n, ∑ j ∈ Finset.univ.erase i, M i j * w i * w j| ≤
        ∑ i : n, (∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 := by
    calc |∑ i : n, ∑ j ∈ Finset.univ.erase i, M i j * w i * w j|
        ≤ ∑ i : n, ∑ j ∈ Finset.univ.erase i, |M i j * w i * w j| := by
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : n, ∑ j ∈ Finset.univ.erase i, |M i j| * ((w i ^ 2 + w j ^ 2) / 2) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have h2 : |w i| * |w j| ≤ (w i ^ 2 + w j ^ 2) / 2 := by
            have := sq_nonneg (|w i| - |w j|)
            nlinarith [sq_abs (w i), sq_abs (w j)]
          nlinarith [abs_nonneg (M i j)]
      _ = (∑ i : n, ∑ j ∈ Finset.univ.erase i, |M i j| * w i ^ 2 / 2) +
          (∑ i : n, ∑ j ∈ Finset.univ.erase i, |M i j| * w j ^ 2 / 2) := by
          simp_rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : n, (∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 := by
          have hswap :
              ∑ i : n, ∑ j ∈ Finset.univ.erase i, |M i j| * w j ^ 2 / 2 =
              ∑ i : n, ∑ j ∈ Finset.univ.erase i, |M i j| * w i ^ 2 / 2 := by
            have h1 : ∀ (f : n → n → ℝ),
                ∑ i : n, ∑ j ∈ Finset.univ.erase i, f i j =
                  ∑ i : n, ∑ j : n, if j = i then 0 else f i j := fun f => by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add]
              refine Finset.sum_congr rfl fun j hj => (if_neg (Finset.ne_of_mem_erase hj)).symm
            rw [h1, h1, Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            by_cases hij : i = j
            · subst hij; simp
            · rw [if_neg hij, if_neg (Ne.symm hij), hsym i j]
          rw [hswap, ← two_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
  have h1 : -(∑ i : n, (∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2) ≤
      ∑ i : n, ∑ j ∈ Finset.univ.erase i, M i j * w i * w j := (abs_le.mp hoff_abs).1
  have h2 : ∑ i : n, ∑ j ∈ Finset.univ.erase i, M i j * w i * w j ≤
      ∑ i : n, (∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 := (abs_le.mp hoff_abs).2
  have hsub : ∑ i : n, (M i i - ∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 =
      (∑ i : n, M i i * w i ^ 2) - ∑ i : n, (∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
  have hadd : ∑ i : n, (M i i + ∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 =
      (∑ i : n, M i i * w i ^ 2) + ∑ i : n, (∑ j ∈ Finset.univ.erase i, |M i j|) * w i ^ 2 := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
  constructor <;> linarith

/-- **Gershgorin + Courant–Fischer Eigenvalue Enclosure for `matZ`**:
given any real symmetric `H : Matrix (Fin n) (Fin n) ℝ`, shift `s : ℝ`, matrix `Q`,
Gram row-sum defect `ε₁ ∈ [0, 1)`, and nonnegative row lower bounds `μ : Fin n → ℝ`:
- if `∀ i, |((Qᵀ * Q) i i) - 1| + ∑_{j ≠ i} |(Qᵀ * Q) i j| ≤ ε₁`, and
- `∀ i, μ i ≤ (Qᵀ * (H + s • 1) * Q) i i - ∑_{j ≠ i} |(Qᵀ * (H + s • 1) * Q) i j|`,
then for every `b > 0`, `matZ H hH b ≤ ∑ i : Fin n, Real.exp (-b * (μ i / (1 + ε₁) - s))`. -/
theorem gershgorin_matZ_le {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    {ε₁ : ℝ} (hε0 : 0 ≤ ε₁) (hε1 : ε₁ < 1)
    (μ : Fin n → ℝ) (hμ_nn : ∀ i, 0 ≤ μ i)
    (hG1 : ∀ i : Fin n, |(Qᵀ * Q) i i - 1| + ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j| ≤ ε₁)
    (hG2 : ∀ i : Fin n,
      μ i ≤ (Qᵀ * (H + s • (1 : Matrix (Fin n) (Fin n) ℝ)) * Q) i i -
        ∑ j ∈ Finset.univ.erase i, |(Qᵀ * (H + s • (1 : Matrix (Fin n) (Fin n) ℝ)) * Q) i j|)
    {b : ℝ} (hb : 0 < b) :
    matZ H hH b ≤ ∑ i : Fin n, Real.exp (-b * (μ i / (1 + ε₁) - s)) := by
  let Hs := H + s • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hG1_herm : (Qᵀ * Q).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  have hHs_herm : Hs.IsHermitian := by
    dsimp [Hs]
    have h1 : (s • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    exact hH.add h1
  have hG2_herm : (Qᵀ * Hs * Q).IsHermitian := by
    have hHsT : Hsᵀ = Hs := by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hHs_herm.eq
    simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.mul_assoc, hHsT]
  -- Quadratic-form bounds from Gershgorin
  have hQ_norm : ∀ w : Fin n → ℝ,
      (1 - ε₁) * dotProduct w w ≤ dotProduct (Q.mulVec w) (Q.mulVec w) ∧
      dotProduct (Q.mulVec w) (Q.mulVec w) ≤ (1 + ε₁) * dotProduct w w := fun w => by
    have hdot : dotProduct (Q.mulVec w) (Q.mulVec w) = dotProduct w ((Qᵀ * Q).mulVec w) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, dotProduct_comm w _,
        ← Matrix.dotProduct_mulVec]
    rw [hdot]
    rcases gershgorin_quad_bounds (Qᵀ * Q) hG1_herm w with ⟨hL, hU⟩
    constructor
    · calc (1 - ε₁) * dotProduct w w
          = ∑ i : Fin n, (1 - ε₁) * w i ^ 2 := by
            simp only [dotProduct, Finset.mul_sum, sq]
        _ ≤ ∑ i : Fin n, ((Qᵀ * Q) i i - ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j|) * w i ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              have hi := hG1 i
              have : 1 - ε₁ ≤ (Qᵀ * Q) i i - ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j| := by
                have h1 : -((Qᵀ * Q) i i - 1) ≤ |(Qᵀ * Q) i i - 1| := neg_le_abs _
                linarith
              exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ ≤ dotProduct w ((Qᵀ * Q).mulVec w) := hL
    · calc dotProduct w ((Qᵀ * Q).mulVec w)
          ≤ ∑ i : Fin n, ((Qᵀ * Q) i i + ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j|) * w i ^ 2 := hU
        _ ≤ ∑ i : Fin n, (1 + ε₁) * w i ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              have hi := hG1 i
              have : (Qᵀ * Q) i i + ∑ j ∈ Finset.univ.erase i, |(Qᵀ * Q) i j| ≤ 1 + ε₁ := by
                have h1 : (Qᵀ * Q) i i - 1 ≤ |(Qᵀ * Q) i i - 1| := le_abs_self _
                linarith
              exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = (1 + ε₁) * dotProduct w w := by simp only [dotProduct, Finset.mul_sum, sq]
  have hQ_inj : Function.Injective Q.mulVec := by
    intro w₁ w₂ heq
    have hdiff : Q.mulVec (w₁ - w₂) = 0 := by rw [Matrix.mulVec_sub, heq, sub_self]
    have h0 := (hQ_norm (w₁ - w₂)).1
    rw [hdiff, dotProduct_zero] at h0
    have hdot0 : dotProduct (w₁ - w₂) (w₁ - w₂) ≤ 0 := by nlinarith
    have hsq : ∀ i, (w₁ i - w₂ i) ^ 2 = 0 := fun i => by
      have hle : (w₁ i - w₂ i) ^ 2 ≤ dotProduct (w₁ - w₂) (w₁ - w₂) := by
        simpa [dotProduct, sq] using
          Finset.single_le_sum (f := fun j => (w₁ j - w₂ j) * (w₁ j - w₂ j))
            (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      exact le_antisymm (by linarith) (sq_nonneg _)
    funext i
    have := sq_eq_zero_iff.mp (hsq i)
    linarith
  have hG2_lb : ∀ w : Fin n → ℝ,
      ∑ i : Fin n, μ i * w i ^ 2 ≤ dotProduct (Q.mulVec w) (Hs.mulVec (Q.mulVec w)) := fun w => by
    have hdot : dotProduct (Q.mulVec w) (Hs.mulVec (Q.mulVec w)) =
        dotProduct w ((Qᵀ * Hs * Q).mulVec w) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_transpose, dotProduct_comm w _, ← Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [hdot]
    exact (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hG2 i) (sq_nonneg _)).trans
        (gershgorin_quad_bounds (Qᵀ * Hs * Q) hG2_herm w).1
  -- Sort both `hH.eigenvalues` and `μ` ascending via `Tuple.sort`
  let σ : Equiv.Perm (Fin n) := Tuple.sort hH.eigenvalues
  let τ : Equiv.Perm (Fin n) := Tuple.sort μ
  have hσ_mono : Monotone (hH.eigenvalues ∘ σ) := Tuple.monotone_sort hH.eigenvalues
  have hτ_mono : Monotone (μ ∘ τ) := Tuple.monotone_sort μ
  -- Courant–Fischer subspace-intersection comparison for every rank `k : Fin n`
  have hrank : ∀ k : Fin n, μ (τ k) / (1 + ε₁) - s ≤ hH.eigenvalues (σ k) := by
    intro k
    -- Subspace U = span { eigenvectorBasis (σ i) | i ≤ k }, dim = k + 1
    -- Subspace V = span { Q *ᵥ e_{τ j} | k ≤ j }, dim = n - k
    let uVec : Fin n → (Fin n → ℝ) := fun i => (hH.eigenvectorBasis (σ i)).ofLp
    let vVec : Fin n → (Fin n → ℝ) := fun j => Q.mulVec (Pi.single (M := fun _ => ℝ) (τ j) (1 : ℝ))
    let U : Submodule ℝ (Fin n → ℝ) :=
      Submodule.span ℝ (uVec '' {i : Fin n | i ≤ k})
    let V : Submodule ℝ (Fin n → ℝ) :=
      Submodule.span ℝ (vVec '' {j : Fin n | k ≤ j})
    have hu_li : LinearIndependent ℝ uVec := by
      have h1 : LinearIndependent ℝ (fun i : Fin n => hH.eigenvectorBasis (σ i)) :=
        (hH.eigenvectorBasis.orthonormal.linearIndependent).comp σ σ.injective
      let e := (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv
      exact h1.map' e.toLinearMap e.ker
    have hv_li : LinearIndependent ℝ vVec := by
      have hstd : LinearIndependent ℝ (fun j : Fin n => Pi.single (M := fun _ => ℝ) (τ j) (1 : ℝ)) := by
        have hb := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp τ τ.injective
        convert hb using 1
        funext j; simp [Pi.basisFun_apply]
      have hQlin : LinearMap.ker (Matrix.mulVecLin Q) = ⊥ :=
        LinearMap.ker_eq_bot.mpr hQ_inj
      exact hstd.map' (Matrix.mulVecLin Q) hQlin
    have hdimU : Module.finrank ℝ U = k.val + 1 := by
      have hcard : Fintype.card {i : Fin n // i ≤ k} = k.val + 1 := by
        have h1 : (Finset.univ.filter fun i : Fin n => i ≤ k) = Finset.Iic k := by
          ext i; simp
        rw [Fintype.card_subtype, h1, Fin.card_Iic]
      have himg : uVec '' {i : Fin n | i ≤ k} = Set.range (uVec ∘ (Subtype.val : {i : Fin n // i ≤ k} → Fin n)) := by
        ext x; simp
      rw [show U = Submodule.span ℝ (Set.range (uVec ∘ (Subtype.val : {i : Fin n // i ≤ k} → Fin n))) by
        dsimp [U]; rw [himg]]
      rw [finrank_span_eq_card (hu_li.comp Subtype.val Subtype.val_injective), hcard]
    have hdimV : Module.finrank ℝ V = n - k.val := by
      have hcard : Fintype.card {j : Fin n // k ≤ j} = n - k.val := by
        have h1 : (Finset.univ.filter fun j : Fin n => k ≤ j) = Finset.Ici k := by
          ext j; simp
        rw [Fintype.card_subtype, h1, Fin.card_Ici]
      have himg : vVec '' {j : Fin n | k ≤ j} = Set.range (vVec ∘ (Subtype.val : {j : Fin n // k ≤ j} → Fin n)) := by
        ext x; simp
      rw [show V = Submodule.span ℝ (Set.range (vVec ∘ (Subtype.val : {j : Fin n // k ≤ j} → Fin n))) by
        dsimp [V]; rw [himg]]
      rw [finrank_span_eq_card (hv_li.comp Subtype.val Subtype.val_injective), hcard]
    have hdim_tot : Module.finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
    have hinf_pos : 0 < Module.finrank ℝ (U ⊓ V : Submodule ℝ (Fin n → ℝ)) := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq U V
      have hle : Module.finrank ℝ (U ⊔ V : Submodule ℝ (Fin n → ℝ)) ≤ n := by
        simpa [hdim_tot] using Submodule.finrank_le (U ⊔ V)
      omega
    have hinf_ne : (U ⊓ V : Submodule ℝ (Fin n → ℝ)) ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hinf_pos; omega
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hinf_ne with ⟨x, hxUV, hx0⟩
    rcases Submodule.mem_inf.mp hxUV with ⟨hxU, hxV⟩
    -- 1. Since `x ∈ U`, `x ⬝ᵥ Hs *ᵥ x ≤ (λ_{σ k} + s) * (x ⬝ᵥ x)`
    have hU_ub : dotProduct x (Hs.mulVec x) ≤ (hH.eigenvalues (σ k) + s) * dotProduct x x := by
      have hx_orth : ∀ i : Fin n, k < i → dotProduct (hH.eigenvectorBasis (σ i)).ofLp x = 0 := by
        intro i hi
        let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
          { toFun := fun y => dotProduct (hH.eigenvectorBasis (σ i)).ofLp y
            map_add' := fun y z => dotProduct_add _ _ _
            map_smul' := fun c y => by simp [dotProduct_smul] }
        have hker : U ≤ LinearMap.ker f := by
          rw [Submodule.span_le]
          rintro y ⟨j, hj, rfl⟩
          simp only [SetLike.mem_coe, LinearMap.mem_ker, f, uVec]
          have hne : σ i ≠ σ j := fun heq => by
            have := σ.injective heq
            exact not_le.mpr hi (this ▸ hj)
          have h0 := hH.eigenvectorBasis.orthonormal.2 hne
          simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h0
        exact hker hxU
      have hHs_quad : dotProduct x (Hs.mulVec x) =
          dotProduct x (H.mulVec x) + s * dotProduct x x := by
        dsimp [Hs]
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [hHs_quad, dotProduct_mulVec_eq_sum_eigenvalues H hH x,
        dotProduct_self_eq_sum_sq H hH x]
      have hsum_eq :
          ∑ m : Fin n, hH.eigenvalues m * (dotProduct (hH.eigenvectorBasis m).ofLp x) ^ 2 ≤
          hH.eigenvalues (σ k) * ∑ m : Fin n, (dotProduct (hH.eigenvectorBasis m).ofLp x) ^ 2 := by
        rw [Finset.mul_sum]
        conv_lhs => rw [← Equiv.sum_comp σ]
        conv_rhs => rw [← Equiv.sum_comp σ]
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hik : i ≤ k
        · exact mul_le_mul_of_nonneg_right (hσ_mono hik) (sq_nonneg _)
        · have h0 : dotProduct (hH.eigenvectorBasis (σ i)).ofLp x = 0 :=
            hx_orth i (lt_of_not_ge hik)
          rw [h0, zero_pow (by norm_num), mul_zero, mul_zero]
      linarith
    -- 2. Since `x ∈ V`, `x = Q *ᵥ w` with `w (τ j) = 0` for `j < k`
    have hxV_rep : ∃ w : Fin n → ℝ, x = Q.mulVec w ∧ ∀ j : Fin n, j < k → w (τ j) = 0 := by
      have himg : V = Submodule.map (Matrix.mulVecLin Q)
          (Submodule.span ℝ ((fun j : Fin n => Pi.single (M := fun _ => ℝ) (τ j) (1 : ℝ)) '' {j : Fin n | k ≤ j})) := by
        dsimp [V, vVec]
        rw [Submodule.map_span, Set.image_image]
        rfl
      rw [himg] at hxV
      rcases Submodule.mem_map.mp hxV with ⟨w, hw, hQw⟩
      refine ⟨w, hQw.symm, fun j hj => ?_⟩
      let g : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (τ j)
      have hker : Submodule.span ℝ ((fun m : Fin n => Pi.single (M := fun _ => ℝ) (τ m) (1 : ℝ)) '' {m : Fin n | k ≤ m}) ≤
          LinearMap.ker g := by
        rw [Submodule.span_le]
        rintro y ⟨m, hm, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, g, LinearMap.proj_apply]
        have hne : τ j ≠ τ m := fun heq => by
          have := τ.injective heq
          exact not_le.mpr hj (this ▸ hm)
        exact Pi.single_eq_of_ne hne 1
      exact hker hw
    rcases hxV_rep with ⟨w, rfl, hw_supp⟩
    have hw_pos : 0 < dotProduct w w := by
      by_contra hle
      push_neg at hle
      have h0 : w = 0 := by
        funext i
        have hsq : w i ^ 2 ≤ dotProduct w w := by
          simpa [dotProduct, sq] using
            Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
        exact sq_eq_zero_iff.mp (le_antisymm (by linarith) (sq_nonneg _))
      exact hx0 (by rw [h0, Matrix.mulVec_zero])
    have hV_lb : μ (τ k) * dotProduct w w ≤ dotProduct (Q.mulVec w) (Hs.mulVec (Q.mulVec w)) := by
      refine le_trans ?_ (hG2_lb w)
      have hsum : μ (τ k) * dotProduct w w = ∑ i : Fin n, μ (τ k) * w i ^ 2 := by
        simp only [dotProduct, Finset.mul_sum, sq]
      rw [hsum]
      conv_lhs => rw [← Equiv.sum_comp τ]
      conv_rhs => rw [← Equiv.sum_comp τ]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hkj : k ≤ j
      · exact mul_le_mul_of_nonneg_right (hτ_mono hkj) (sq_nonneg _)
      · have h0 := hw_supp j (lt_of_not_ge hkj)
        rw [h0, zero_pow (by norm_num), mul_zero, mul_zero]
    -- 3. Combine: μ(τ k) * ‖w‖² ≤ (λ_{σ k} + s) * ‖Q w‖² ≤ (λ_{σ k} + s) * (1 + ε₁) * ‖w‖²
    have hQw_pos : 0 < dotProduct (Q.mulVec w) (Q.mulVec w) := by
      have := (hQ_norm w).1
      nlinarith
    have hlam_s_nn : 0 ≤ hH.eigenvalues (σ k) + s := by
      have h1 : 0 ≤ μ (τ k) * dotProduct w w := mul_nonneg (hμ_nn (τ k)) hw_pos.le
      nlinarith
    have hcomb : μ (τ k) * dotProduct w w ≤ (hH.eigenvalues (σ k) + s) * ((1 + ε₁) * dotProduct w w) :=
      hV_lb.trans (hU_ub.trans (mul_le_mul_of_nonneg_left (hQ_norm w).2 hlam_s_nn))
    have hdiv : μ (τ k) ≤ (hH.eigenvalues (σ k) + s) * (1 + ε₁) := by
      have hmul : μ (τ k) * dotProduct w w ≤ ((hH.eigenvalues (σ k) + s) * (1 + ε₁)) * dotProduct w w := by
        linarith
      exact le_of_mul_le_mul_right hmul hw_pos
    have h1pe : 0 < 1 + ε₁ := by linarith
    have hstep : μ (τ k) / (1 + ε₁) ≤ hH.eigenvalues (σ k) + s := (div_le_iff₀ h1pe).mpr hdiv
    linarith
  -- Sum over all `k : Fin n` using permutations `σ` and `τ`
  unfold matZ
  conv_lhs => rw [← Equiv.sum_comp σ]
  conv_rhs => rw [← Equiv.sum_comp τ]
  refine Finset.sum_le_sum fun k _ => ?_
  exact Real.exp_le_exp.mpr (by nlinarith [hrank k])

/-! ## Argument-Reduced Rational Bounds on `Real.exp` -/

/-- Lower bound on `exp x` for `x ≥ 0` via argument reduction `x / 2^k` and degree `N` Taylor sum. -/
theorem exp_div_pow2_lower {x : ℝ} (hx : 0 ≤ x) (k N : ℕ) :
    (∑ i ∈ Finset.range N, (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ)) ^ (2 ^ k) ≤ Real.exp x := by
  have hx' : 0 ≤ x / (2 : ℝ) ^ k := div_nonneg hx (by positivity)
  have h1 := Real.sum_le_exp_of_nonneg hx' N
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range N, (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hx' i) (Nat.cast_nonneg _)
  have hpow := pow_le_pow_left₀ hsum_nn h1 (2 ^ k)
  rw [← Real.exp_nat_mul] at hpow
  have hcancel : ((2 ^ k : ℕ) : ℝ) * (x / (2 : ℝ) ^ k) = x := by
    push_cast; field_simp [(by positivity : (2 : ℝ) ^ k ≠ 0)]
  rwa [hcancel] at hpow

/-- Upper bound on `exp (-x)` for `x ≥ 0` via argument reduction `x / 2^k` and degree `N` Taylor sum. -/
theorem exp_neg_div_pow2_upper {x : ℝ} (hx : 0 ≤ x) (k N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-x) ≤
      ((∑ i ∈ Finset.range N, (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ)) ^ (2 ^ k))⁻¹ := by
  have hpos_sum : 0 < ∑ i ∈ Finset.range N, (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ) := by
    have h0 : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have h1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range N, (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ) := by
      have := Finset.single_le_sum
        (f := fun i => (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ))
        (fun i _ => div_nonneg (pow_nonneg (div_nonneg hx (by positivity)) i) (Nat.cast_nonneg _)) h0
      simpa using this
    linarith
  rw [Real.exp_neg]
  exact inv_anti₀ (pow_pos hpos_sum _) (exp_div_pow2_lower hx k N)

/-- Argument-reduced lower bound on `exp (-x)` (`x ≥ 0`) using `Real.exp_bound'`:
if `x / 2^k ≤ 1` and `0 < N`, then
`((∑ i < N, (x/2^k)^i / i! + (x/2^k)^N * (N + 1) / (N! * N)) ^ (2^k))⁻¹ ≤ Real.exp (-x)`. -/
theorem exp_neg_div_pow2_lower {x : ℝ} (hx : 0 ≤ x) (k N : ℕ) (hN : 0 < N)
    (hle1 : x / (2 : ℝ) ^ k ≤ 1) :
    (((∑ i ∈ Finset.range N, (x / (2 : ℝ) ^ k) ^ i / (i.factorial : ℝ)) +
      (x / (2 : ℝ) ^ k) ^ N * ((N : ℝ) + 1) / ((N.factorial : ℝ) * (N : ℝ))) ^ (2 ^ k))⁻¹ ≤
      Real.exp (-x) := by
  have hx' : 0 ≤ x / (2 : ℝ) ^ k := div_nonneg hx (by positivity)
  have hub := Real.exp_bound' hx' hle1 hN
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hub (2 ^ k)
  rw [← Real.exp_nat_mul] at hpow
  have hcancel : ((2 ^ k : ℕ) : ℝ) * (x / (2 : ℝ) ^ k) = x := by
    push_cast; field_simp [(by positivity : (2 : ℝ) ^ k ≠ 0)]
  rw [hcancel] at hpow
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos x) hpow

end PurityBootstrap.MatrixTools
