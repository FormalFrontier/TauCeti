/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.SmulSub
public import TauCeti.Analysis.Normed.Operator.LinearPMap.SmulSub

/-!
# Formally self-adjoint partial linear maps and their shifts

For a formally self-adjoint partial linear map `A` on a complex inner-product space (Mathlib's
`LinearPMap.IsFormalAdjoint A A`, the symmetric operators), the quadratic form `⟪x, A x⟫` is real,
so for a complex scalar `c` the shift `x ↦ c • x - A x` satisfies

`‖c • x - A x‖² = c.im² ‖x‖² + ‖c.re • x - A x‖²`.

For `c.im ≠ 0` the shift is therefore bounded below with respect to the graph norm of `A`; if `A` is
closed, its range is closed (`LinearPMap.isClosed_range_smul_sub_of_graph_norm_le`).  When `A` is
self-adjoint the range is also dense, because a vector orthogonal to it is an eigenvector of `A†`
for the eigenvalue `conj c` (`LinearPMap.exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero`), and a
symmetric operator has no nonreal eigenvalue
(`LinearPMap.IsFormalAdjoint.eq_zero_of_apply_eq_smul`).  Hence every nonreal shift of a
self-adjoint operator is surjective (`IsSelfAdjoint.smul_sub_surjective`), and with the lower bound
it is bijective with bounded inverse (`IsSelfAdjoint.smul_sub_bijective`): the resolvent set
contains every nonreal point.  The shifts `± i - A` are the classical deficiency operators, and
their surjectivity is the range condition that makes `± i • A` m-dissipative.

The file also provides the formal-adjointness and quadratic-form API of self-adjoint partial
linear maps used by the semigroup development.

## Main results

* `IsSelfAdjoint.isFormalAdjoint`: a self-adjoint partial linear map is formally self-adjoint.
* `LinearPMap.IsFormalAdjoint.im_inner_self_apply`: the quadratic form of a formally self-adjoint
  map is real.
* `LinearPMap.IsFormalAdjoint.norm_smul_sub_sq`: the square-sum identity for a shift, and the
  graph-norm lower bounds `abs_im_mul_norm_le_norm_smul_sub` (equivalently the resolvent bound
  `norm_le_inv_abs_im_mul_norm_smul_sub`) and `norm_apply_le_mul_norm_smul_sub`.
* `LinearPMap.IsFormalAdjoint.eq_zero_of_apply_eq_smul`: a formally self-adjoint map has no
  eigenvector for a nonreal eigenvalue.
* `LinearPMap.exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero`: a vector orthogonal to the range
  of the shift `c • x - A x` is an eigenvector of the adjoint `A†` for the eigenvalue `conj c`.
* `LinearPMap.IsFormalAdjoint.isClosed_range_smul_sub`, `IsSelfAdjoint.denseRange_smul_sub` and
  `IsSelfAdjoint.smul_sub_surjective`: the range of a nonreal shift is closed (closed symmetric
  operator), dense and the whole space (self-adjoint operator).
* `LinearPMap.IsFormalAdjoint.smul_sub_injective` and `IsSelfAdjoint.smul_sub_bijective`: a
  nonreal shift is injective, and bijective for a self-adjoint operator.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem VIII.3 (the basic criterion for self-adjointness).
* J. Weidmann, *Linear Operators in Hilbert Spaces*, Chapter 5.
-/

public section

noncomputable section

open scoped NNReal

namespace LinearPMap

section General

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A self-adjoint partial linear map is formally self-adjoint on its domain. -/
theorem _root_.IsSelfAdjoint.isFormalAdjoint [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  have h := adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h

/-- The quadratic form of a formally self-adjoint partial linear map is real. -/
theorem IsFormalAdjoint.im_inner_self_apply {A : E →ₗ.[𝕜] E} (hA : A.IsFormalAdjoint A)
    (x : A.domain) : RCLike.im (inner 𝕜 (x : E) (A x)) = 0 := by
  apply RCLike.conj_eq_iff_im.mp
  calc
    (starRingEnd 𝕜) (inner 𝕜 (x : E) (A x)) = inner 𝕜 (A x) (x : E) :=
      inner_conj_symm (A x) (x : E)
    _ = inner 𝕜 (x : E) (A x) := hA x x

/-- **Deficiency vectors are adjoint eigenvectors.** A vector orthogonal to the range of the shift
`c • x - A x` of a densely defined partial linear map lies in the domain of the adjoint `A†`, which
acts on it as multiplication by `conj c`. -/
theorem exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hdense : Dense (A.domain : Set E)) {c : 𝕜} {y : E}
    (h : ∀ x : A.domain, inner 𝕜 y (c • (x : E) - A x) = 0) :
    ∃ hy : y ∈ A†.domain, A† ⟨y, hy⟩ = (starRingEnd 𝕜) c • y := by
  have hpair : ∀ x : A.domain, inner 𝕜 ((starRingEnd 𝕜) c • y) (x : E) = inner 𝕜 y (A x) := by
    intro x
    have hx := h x
    rw [inner_sub_right, sub_eq_zero] at hx
    rw [inner_smul_left, RCLike.conj_conj, ← hx, inner_smul_right]
  have hy : y ∈ A†.domain := mem_adjoint_domain_of_exists y ⟨_, hpair⟩
  exact ⟨hy, hdense.eq_of_inner_left 𝕜 fun x hx =>
    (adjoint_isFormalAdjoint hdense ⟨y, hy⟩ ⟨x, hx⟩).trans (hpair ⟨x, hx⟩).symm⟩

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a formally self-adjoint partial linear map, the real cross term between `c • x` and `A x`
is `c.re` times the (real) quadratic form.  The complex inner product is conjugate-linear in its
first argument. -/
theorem IsFormalAdjoint.re_inner_smul_self_apply {A : E →ₗ.[ℂ] E} (hA : A.IsFormalAdjoint A)
    (c : ℂ) (x : A.domain) :
    (inner ℂ (c • (x : E)) (A x)).re = c.re * (inner ℂ (x : E) (A x)).re := by
  have him := hA.im_inner_self_apply x
  rw [RCLike.im_to_complex] at him
  rw [inner_smul_left, Complex.mul_re, Complex.conj_re, Complex.conj_im, him]
  ring

/-- The mirror image of `re_inner_smul_self_apply`: the real cross term between `c • A x` and `x`
is `c.re` times the quadratic form. -/
theorem IsFormalAdjoint.re_inner_smul_apply_self {A : E →ₗ.[ℂ] E} (hA : A.IsFormalAdjoint A)
    (c : ℂ) (x : A.domain) :
    (inner ℂ (c • A x) (x : E)).re = c.re * (inner ℂ (x : E) (A x)).re := by
  rw [inner_smul_left, hA x x, ← inner_smul_left]
  exact hA.re_inner_smul_self_apply c x

/-- **Square-sum identity for shifts.** For a formally self-adjoint partial linear map and a complex
scalar `c`, `‖c • x - A x‖² = c.im² ‖x‖² + ‖c.re • x - A x‖²`. -/
theorem IsFormalAdjoint.norm_smul_sub_sq {A : E →ₗ.[ℂ] E} (hA : A.IsFormalAdjoint A) (c : ℂ)
    (x : A.domain) :
    ‖c • (x : E) - A x‖ ^ 2 =
      c.im ^ 2 * ‖(x : E)‖ ^ 2 + ‖(c.re : ℂ) • (x : E) - A x‖ ^ 2 := by
  have hc : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [@norm_sub_sq ℂ, @norm_sub_sq ℂ, RCLike.re_to_complex, RCLike.re_to_complex,
    hA.re_inner_smul_self_apply c x, hA.re_inner_smul_self_apply (c.re : ℂ) x]
  simp only [norm_smul, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    hc]
  ring

/-- A shift dominates the imaginary part of the scalar times the input. -/
theorem IsFormalAdjoint.abs_im_mul_norm_le_norm_smul_sub {A : E →ₗ.[ℂ] E}
    (hA : A.IsFormalAdjoint A) (c : ℂ) (x : A.domain) :
    |c.im| * ‖(x : E)‖ ≤ ‖c • (x : E) - A x‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [hA.norm_smul_sub_sq c x, mul_pow, sq_abs]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The resolvent bound: a nonreal shift of a formally self-adjoint partial linear map dominates
`|c.im|` times the input, so its inverse (where defined) has norm at most `|c.im|⁻¹`. -/
theorem IsFormalAdjoint.norm_le_inv_abs_im_mul_norm_smul_sub {A : E →ₗ.[ℂ] E}
    (hA : A.IsFormalAdjoint A) {c : ℂ} (hc : c.im ≠ 0) (x : A.domain) :
    ‖(x : E)‖ ≤ |c.im|⁻¹ * ‖c • (x : E) - A x‖ := by
  rw [le_inv_mul_iff₀ (abs_pos.mpr hc)]
  exact hA.abs_im_mul_norm_le_norm_smul_sub c x

/-- A nonreal shift of a formally self-adjoint partial linear map is injective. -/
theorem IsFormalAdjoint.smul_sub_injective {A : E →ₗ.[ℂ] E} (hA : A.IsFormalAdjoint A) {c : ℂ}
    (hc : c.im ≠ 0) : Function.Injective (fun x : A.domain => c • (x : E) - A x) :=
  smul_sub_injective_of_norm_le (K := (|c.im|⁻¹).toNNReal) fun x => by
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg _))]
    exact hA.norm_le_inv_abs_im_mul_norm_smul_sub hc x

/-- A shift dominates the shift by the real part of the scalar. -/
theorem IsFormalAdjoint.norm_re_smul_sub_le_norm_smul_sub {A : E →ₗ.[ℂ] E}
    (hA : A.IsFormalAdjoint A) (c : ℂ) (x : A.domain) :
    ‖(c.re : ℂ) • (x : E) - A x‖ ≤ ‖c • (x : E) - A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hA.norm_smul_sub_sq c x]
  exact le_add_of_nonneg_left (by positivity)

/-- A nonreal shift dominates the image, up to the constant `1 + |c.re| / |c.im|`: together with
`abs_im_mul_norm_le_norm_smul_sub` this bounds the graph norm `max ‖x‖ ‖A x‖` by the shift. -/
theorem IsFormalAdjoint.norm_apply_le_mul_norm_smul_sub {A : E →ₗ.[ℂ] E}
    (hA : A.IsFormalAdjoint A) {c : ℂ} (hc : c.im ≠ 0) (x : A.domain) :
    ‖A x‖ ≤ (1 + |c.re| * |c.im|⁻¹) * ‖c • (x : E) - A x‖ := by
  have hxN := hA.norm_le_inv_abs_im_mul_norm_smul_sub hc x
  calc
    ‖A x‖ = ‖(c.re : ℂ) • (x : E) - ((c.re : ℂ) • (x : E) - A x)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖(c.re : ℂ) • (x : E)‖ + ‖(c.re : ℂ) • (x : E) - A x‖ := norm_sub_le _ _
    _ ≤ |c.re| * (|c.im|⁻¹ * ‖c • (x : E) - A x‖) + ‖c • (x : E) - A x‖ := by
      gcongr
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hxN (abs_nonneg _)
      · exact hA.norm_re_smul_sub_le_norm_smul_sub c x
    _ = (1 + |c.re| * |c.im|⁻¹) * ‖c • (x : E) - A x‖ := by ring

/-- The range of a nonreal shift of a closed, formally self-adjoint partial linear map is closed:
the shift is bounded below with respect to the graph norm
(`LinearPMap.isClosed_range_smul_sub_of_graph_norm_le`). -/
theorem IsFormalAdjoint.isClosed_range_smul_sub [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : A.IsFormalAdjoint A) (hcl : A.IsClosed) {c : ℂ} (hc : c.im ≠ 0) :
    _root_.IsClosed (Set.range (fun x : A.domain => c • (x : E) - A x)) := by
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  let K : ℝ≥0 := ⟨1 + (1 + |c.re|) * |c.im|⁻¹, by positivity⟩
  have hK : (K : ℝ) = 1 + (1 + |c.re|) * |c.im|⁻¹ := NNReal.coe_mk _ _
  have hinv0 : 0 ≤ |c.re| * |c.im|⁻¹ := mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hpos.le)
  have hK1 : |c.im|⁻¹ ≤ K := by rw [hK]; linarith
  have hK2 : 1 + |c.re| * |c.im|⁻¹ ≤ K := by rw [hK]; linarith [inv_nonneg.mpr hpos.le]
  refine isClosed_range_smul_sub_of_graph_norm_le hcl (K := K) fun x => ?_
  have hN0 : 0 ≤ ‖c • (x : E) - A x‖ := norm_nonneg _
  exact max_le ((hA.norm_le_inv_abs_im_mul_norm_smul_sub hc x).trans
    (mul_le_mul_of_nonneg_right hK1 hN0))
    ((hA.norm_apply_le_mul_norm_smul_sub hc x).trans (mul_le_mul_of_nonneg_right hK2 hN0))

/-- **A symmetric operator has no nonreal eigenvalue**: the quadratic form at an eigenvector for
`c` is `c * ‖x‖²`, whose imaginary part vanishes only if `x = 0`. -/
theorem IsFormalAdjoint.eq_zero_of_apply_eq_smul {A : E →ₗ.[ℂ] E} (hA : A.IsFormalAdjoint A)
    {c : ℂ} (hc : c.im ≠ 0) {x : A.domain} (h : A x = c • (x : E)) : (x : E) = 0 := by
  have him := hA.im_inner_self_apply x
  rw [h, inner_smul_right] at him
  simp only [RCLike.mul_im, inner_self_im, inner_self_eq_norm_sq, RCLike.im_to_complex, mul_zero,
    zero_add] at him
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp him).resolve_left hc))

/-- The range of a nonreal shift of a self-adjoint partial linear map is dense. -/
theorem _root_.IsSelfAdjoint.denseRange_smul_sub [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.im ≠ 0) :
    DenseRange (fun x : A.domain => c • (x : E) - A x) := by
  rw [DenseRange, ← A.coe_range_smulSub c]
  refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
  have hortho : ∀ x : A.domain, inner ℂ y (c • (x : E) - A x) = 0 := fun x =>
    (Submodule.mem_orthogonal' _ y).mp hy _ (LinearMap.mem_range.mpr ⟨x, A.smulSub_apply c x⟩)
  have hc' : ((starRingEnd ℂ) c).im ≠ 0 := by
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr hc
  obtain ⟨hy, hAy⟩ := exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero hA.dense_domain hortho
  have hAA : A† = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hyA : y ∈ A.domain := (LinearPMap.ext_iff.mp hAA).1 ▸ hy
  exact hA.isFormalAdjoint.eq_zero_of_apply_eq_smul hc' (x := ⟨y, hyA⟩)
    (((@(LinearPMap.ext_iff.mp hAA).2 y hy hyA).symm).trans hAy)

/-- **Nonreal shifts of a self-adjoint partial linear map are surjective**: their ranges are
closed and dense. -/
theorem _root_.IsSelfAdjoint.smul_sub_surjective [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.im ≠ 0) :
    Function.Surjective (fun x : A.domain => c • (x : E) - A x) := by
  intro y
  have hrange : Set.range (fun x : A.domain => c • (x : E) - A x) = Set.univ := by
    rw [← (hA.isFormalAdjoint.isClosed_range_smul_sub hA.isClosed hc).closure_eq,
      (hA.denseRange_smul_sub hc).closure_range]
  rw [← Set.mem_range, hrange]
  exact Set.mem_univ y

/-- **Nonreal shifts of a self-adjoint partial linear map are bijective.** Together with the lower
bound `IsFormalAdjoint.abs_im_mul_norm_le_norm_smul_sub`, which bounds the inverse by
`|c.im|⁻¹`, this says that the resolvent set of a self-adjoint operator contains every nonreal
point. -/
theorem _root_.IsSelfAdjoint.smul_sub_bijective [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.im ≠ 0) :
    Function.Bijective (fun x : A.domain => c • (x : E) - A x) :=
  ⟨hA.isFormalAdjoint.smul_sub_injective hc, hA.smul_sub_surjective hc⟩

end LinearPMap

end
