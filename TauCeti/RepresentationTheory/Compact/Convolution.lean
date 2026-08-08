/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Convolution operators on `L²` of a compact group

For a continuous kernel `k : C(G, 𝕜)` on a compact group `G` and an `L²` function `f`, the
convolution

`(k * f) x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G)`

makes sense at *every* point `x`, not merely almost everywhere: the integral is the `L²` pairing of
`f` against the continuous function `y ↦ conj (k (x * y⁻¹))`, and that function varies continuously
with `x` in the uniform norm. Convolution therefore smooths `L²(G)` into `C(G)`, and the resulting
map `convolutionCLM k : L²(G) →L[𝕜] C(G)` is bounded by the uniform norm of the kernel.

Composing with `ContinuousMap.toLp` gives the convolution operator `convolutionOperator k` on
`L²(G)`. Two of its properties are proved here: it is self-adjoint when the kernel is symmetric
(`k g⁻¹ = conj (k g)`), and it commutes with right translation. Together these say that the
nonzero eigenspaces of a symmetric convolution operator are right-translation-invariant subspaces
of `L²(G)` whose elements admit continuous representatives, which is how the Peter-Weyl theorem
manufactures finite-dimensional representations of `G` without presupposing that any exist.

## Main definitions

* `TauCeti.convolutionCLM`: convolution against a continuous kernel, as a bounded linear map
  `Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜)`.
* `TauCeti.convolutionOperator`: the convolution operator `f ↦ k * f` on `Lp 𝕜 2 (haarProb G)`.

## Main statements

* `TauCeti.convolutionCLM_apply_apply`: the pointwise formula
  `(k * f) x = ∫ y, k (x * y⁻¹) * f y`.
* `TauCeti.norm_convolutionCLM_apply_le`: `‖k * f‖_∞ ≤ ‖k‖_∞ * ‖f‖₂`, so convolution against a
  continuous kernel is bounded from `L²(G)` into the uniform norm of `C(G)`.
* `TauCeti.isSelfAdjoint_convolutionOperator`: a symmetric kernel gives a self-adjoint operator.
* `TauCeti.convolutionCLM_compMeasurePreserving_mul_right`: convolution commutes with right
  translation.

## Implementation notes

Mathlib's `convolution` (`Mathlib/Analysis/Convolution.lean`) is the convolution of two functions
on an *additive* group against a bilinear pairing, and does not apply here: `G` is multiplicative,
and one of the two arguments is an `L²` class rather than a function. The kernel sections
`y ↦ conj (k (x * y⁻¹))` are assembled with `ContinuousMap.curry`, whose continuity is exactly the
statement that they depend continuously on `x`, so no uniform-continuity argument is needed.

Self-adjointness is proved by writing `convolutionOperator k H`, for a *continuous* `H`, as the
Bochner integral of the kernel sections weighted by `H`, and then extending to all of `L²(G)` by
density (`ContinuousMap.toLp_denseRange`). The more direct Fubini argument on `G × G` is not
available: the product of two Borel spaces is Borel only under a second-countability hypothesis,
which a compact group need not satisfy, whereas a continuous function on a compact space is
integrable with no such hypothesis (`TauCeti.integrable_continuousMap`).

The conjugation in the kernel sections is bookkeeping for Mathlib's convention that the inner
product is conjugate linear in its first argument; it is invisible in the pointwise formula
`convolutionCLM_apply_apply`.

## References

This is the opening of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), which names
`convolutionOperator` and its self-adjointness for a symmetric kernel (there spelled
`convolutionOperator_isSelfAdjoint`, renamed here to `isSelfAdjoint_convolutionOperator` for the
predicate-prefix convention) as milestones on the non-circular route to the Peter-Weyl theorem.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), Chapter 5.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### Preliminaries on `L²` against normalized Haar measure -/

/-- Normalized Haar measure is a probability measure, so passing from the uniform norm to the `L²`
norm is a contraction. -/
private theorem norm_toLp_le (F : C(G, 𝕜)) :
    ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖ ≤ ‖F‖ := by
  have hmass : measureUnivNNReal (haarProb G) = 1 :=
    ENNReal.coe_inj.1 (by simp [coe_measureUnivNNReal])
  have hop : ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ ≤ 1 := by
    simpa [hmass] using ContinuousMap.toLp_norm_le (E := 𝕜) (p := 2) (𝕜 := 𝕜) (haarProb G)
  calc ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖
      ≤ ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ * ‖F‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg F)
    _ = ‖F‖ := one_mul _

/-- Mathlib's `L2.inner_def` computes an inner product in `L²` as the integral of the pointwise
inner products `⟪a, b⟫ = conj a * b`. This is its specialization to a first argument coming from a
continuous function. -/
private theorem inner_toLp_left (F : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F, f⟫_𝕜
      = ∫ x, (starRingEnd 𝕜) (F x) * f x ∂(haarProb G) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) F] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-! ### The kernel sections

The section of the kernel `k` at `x` is `y ↦ conj (k (x * y⁻¹))`. Currying the continuous function
`(x, y) ↦ conj (k (x * y⁻¹))` on `G × G` is exactly the statement that the section depends
continuously on `x` in the uniform norm. -/

/-- The conjugated kernel sections `x ↦ (y ↦ conj (k (x * y⁻¹)))`, as a continuous map into
`C(G, 𝕜)`. -/
private noncomputable def convSectionCM (k : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ContinuousMap.curry
    (star (k.comp ⟨fun p : G × G => p.1 * p.2⁻¹, continuous_fst.mul continuous_snd.inv⟩))

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem convSectionCM_apply (k : C(G, 𝕜)) (x y : G) :
    convSectionCM k x y = (starRingEnd 𝕜) (k (x * y⁻¹)) :=
  (rfl)

omit [MeasurableSpace G] [BorelSpace G] in
private theorem norm_convSectionCM_le (k : C(G, 𝕜)) (x : G) : ‖convSectionCM k x‖ ≤ ‖k‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg k)).2 fun y => by
    rw [convSectionCM_apply, RCLike.norm_conj]
    exact k.norm_coe_le_norm _

/-- The conjugated kernel sections, read in `L²(G)`. -/
private noncomputable def convSection (k : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x),
    (ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜).continuous.comp (convSectionCM k).continuous⟩

private theorem convSection_apply (k : C(G, 𝕜)) (x : G) :
    convSection k x = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x) :=
  (rfl)

private theorem norm_convSection_le (k : C(G, 𝕜)) (x : G) : ‖convSection k x‖ ≤ ‖k‖ :=
  (norm_toLp_le _).trans (norm_convSectionCM_le k x)

/-! ### Convolution as a map into continuous functions -/

private noncomputable def convolutionₗ (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →ₗ[𝕜] C(G, 𝕜) where
  toFun f := ⟨fun x => ⟪convSection k x, f⟫_𝕜, (convSection k).continuous.inner continuous_const⟩
  map_add' f₁ f₂ := by ext x; exact inner_add_right (convSection k x) f₁ f₂
  map_smul' c f := by ext x; exact inner_smul_right (convSection k x) f c

private theorem norm_convolutionₗ_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionₗ k f‖ ≤ ‖k‖ * ‖f‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_convSection_le k x) (norm_nonneg f))

/-- **Convolution against a continuous kernel**, as a bounded linear map from `L²(G)` into `C(G)`.

The value at `x` is the `L²` pairing of `f` against the kernel section at `x`, so it is defined at
every point of `G` and depends continuously on that point: convolving an `L²` class against a
continuous kernel produces a genuine continuous function, not another almost-everywhere class. -/
noncomputable def convolutionCLM (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜) :=
  LinearMap.mkContinuous (convolutionₗ k) ‖k‖ (norm_convolutionₗ_le k)

private theorem convolutionCLM_apply_apply' (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ⟪convSection k x, f⟫_𝕜 :=
  (rfl)

/-- **The pointwise formula for convolution against a continuous kernel.** -/
theorem convolutionCLM_apply_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G) := by
  rw [convolutionCLM_apply_apply', convSection_apply, inner_toLp_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [convSectionCM_apply, RCLike.conj_conj]

private theorem integrable_convolution_integrand (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    Integrable (fun y => k (x * y⁻¹) * f y) (haarProb G) := by
  refine (L2.integrable_inner (convSection k x) f).congr ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜)
    (convSectionCM k x)] with y hy
  rw [convSection_apply, hy, RCLike.inner_apply, convSectionCM_apply, RCLike.conj_conj,
    mul_comm]

/-- Convolution is zero when its kernel is zero. -/
@[simp]
theorem convolutionCLM_zero :
    convolutionCLM (G := G) (0 : C(G, 𝕜)) = 0 := by
  ext f x
  simp [convolutionCLM_apply_apply]

/-- Convolution is additive in its kernel. -/
@[simp]
theorem convolutionCLM_add (k₁ k₂ : C(G, 𝕜)) :
    convolutionCLM (k₁ + k₂) = convolutionCLM k₁ + convolutionCLM k₂ := by
  ext f x
  simp only [add_apply, ContinuousMap.add_apply, convolutionCLM_apply_apply]
  rw [← integral_add (integrable_convolution_integrand k₁ f x)
    (integrable_convolution_integrand k₂ f x)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => add_mul _ _ _)

/-- Convolution is compatible with scalar multiplication of its kernel. -/
@[simp]
theorem convolutionCLM_smul (c : 𝕜) (k : C(G, 𝕜)) :
    convolutionCLM (c • k) = c • convolutionCLM k := by
  ext f x
  simp only [smul_apply, ContinuousMap.smul_apply, smul_eq_mul, convolutionCLM_apply_apply]
  rw [← integral_const_mul c]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)

/-- **Convolution is bounded from `L²(G)` into `C(G)`:** the uniform norm of `k * f` is at most the
product of the uniform norm of the kernel and the `L²` norm of `f`. Normalized Haar measure is a
probability measure, so no measure-dependent constant appears. -/
theorem norm_convolutionCLM_apply_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionCLM k f‖ ≤ ‖k‖ * ‖f‖ :=
  norm_convolutionₗ_le k f

/-- The operator norm of convolution against `k`, as a map into the uniform norm of `C(G)`, is at
most the uniform norm of `k`. -/
theorem norm_convolutionCLM_le (k : C(G, 𝕜)) : ‖convolutionCLM (G := G) k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg k) _

/-! ### The convolution operator on `L²(G)` -/

/-- **The convolution operator** `f ↦ k * f` on `L²(G)`, for a continuous kernel `k`.

It factors through `C(G)`: `convolutionCLM` produces a continuous function, and
`ContinuousMap.toLp` reads that function back into `L²(G)`. -/
noncomputable def convolutionOperator (k : C(G, 𝕜)) :
    Lp 𝕜 2 (haarProb G) →L[𝕜] Lp 𝕜 2 (haarProb G) :=
  (ContinuousMap.toLp 2 (haarProb G) 𝕜).comp (convolutionCLM k)

/-- The convolution operator is `convolutionCLM` followed by `ContinuousMap.toLp`. -/
theorem convolutionOperator_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convolutionCLM k f) :=
  (rfl)

/-- The convolution operator is zero when its kernel is zero. -/
@[simp]
theorem convolutionOperator_zero :
    convolutionOperator (G := G) (0 : C(G, 𝕜)) = 0 := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is additive in its kernel. -/
@[simp]
theorem convolutionOperator_add (k₁ k₂ : C(G, 𝕜)) :
    convolutionOperator (k₁ + k₂) = convolutionOperator k₁ + convolutionOperator k₂ := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is compatible with scalar multiplication of its kernel. -/
@[simp]
theorem convolutionOperator_smul (c : 𝕜) (k : C(G, 𝕜)) :
    convolutionOperator (c • k) = c • convolutionOperator k := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is represented, almost everywhere, by the continuous function
`convolutionCLM k f`. -/
theorem coeFn_convolutionOperator (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f =ᵐ[haarProb G] convolutionCLM k f :=
  ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) _

/-- The convolution operator on `L²(G)` has operator norm at most the uniform norm of its
kernel. -/
theorem norm_convolutionOperator_le (k : C(G, 𝕜)) : ‖convolutionOperator (G := G) k‖ ≤ ‖k‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg k) fun f => by
    rw [convolutionOperator_apply]
    exact (norm_toLp_le _).trans (norm_convolutionCLM_apply_le k f)

/-! ### Self-adjointness for a symmetric kernel

For a *continuous* weight `H` the kernel sections may be averaged against `H`, giving a Bochner
integral in `C(G)` and, after `ContinuousMap.toLp`, one in `L²(G)`. Symmetry of the kernel
identifies that average with `k * H`, which is the adjoint relation on the dense subspace of
continuous functions; the general case follows because both sides of the relation are continuous in
their second argument. -/

/-- The kernel sections weighted by a continuous function `H`. -/
private noncomputable def weightedSectionsCM (k H : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ⟨fun x => H x • convSectionCM k x, H.continuous.smul (convSectionCM k).continuous⟩

/-- The kernel sections weighted by a continuous function `H`, read in `L²(G)`. -/
private noncomputable def weightedSections (k H : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => H x • convSection k x, H.continuous.smul (convSection k).continuous⟩

private theorem integrable_weightedSectionsCM (k H : C(G, 𝕜)) :
    Integrable (fun x => H x • convSectionCM k x) (haarProb G) :=
  integrable_continuousMap G (weightedSectionsCM k H)

private theorem integrable_weightedSections (k H : C(G, 𝕜)) :
    Integrable (fun x => H x • convSection k x) (haarProb G) :=
  integrable_continuousMap G (weightedSections k H)

/-- The `L²`-valued average of the weighted kernel sections is the image under
`ContinuousMap.toLp` of their `C(G)`-valued average. -/
private theorem integral_weightedSections (k H : C(G, 𝕜)) :
    ∫ x, H x • convSection k x ∂(haarProb G)
      = ContinuousMap.toLp 2 (haarProb G) 𝕜
          (∫ x, H x • convSectionCM k x ∂(haarProb G)) := by
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_weightedSectionsCM k H)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_smul, convSection_apply]

/-- The `C(G)`-valued average of the weighted kernel sections, evaluated at a point. -/
private theorem integral_weightedSectionsCM_apply (k H : C(G, 𝕜)) (y : G) :
    (∫ x, H x • convSectionCM k x ∂(haarProb G)) y
      = ∫ x, H x * (starRingEnd 𝕜) (k (x * y⁻¹)) ∂(haarProb G) := by
  have hcomm := (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) y).integral_comp_comm
    (integrable_weightedSectionsCM k H)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, convSectionCM_apply,
    smul_eq_mul] at hcomm
  exact hcomm.symm

/-- The pairing of `convolutionOperator k f` against a continuous function is the pairing of `f`
against the average of the weighted kernel sections. -/
private theorem inner_convolutionOperator_toLp (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G))
    (H : C(G, 𝕜)) :
    ⟪convolutionOperator k f, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
      = ⟪f, ∫ x, H x • convSection k x ∂(haarProb G)⟫_𝕜 := by
  rw [convolutionOperator_apply, inner_toLp_left,
    ← integral_inner (integrable_weightedSections k H) f]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) H] with x hx
  rw [hx, convolutionCLM_apply_apply', inner_smul_right, ← inner_conj_symm f (convSection k x),
    mul_comm]

/-- **Self-adjointness of the convolution operator for a symmetric kernel.** A kernel is symmetric
when `k g⁻¹ = conj (k g)`; the pointwise identity `conj (k (x * y⁻¹)) = k (y * x⁻¹)` it supplies is
what turns the average of the kernel sections weighted by `H` back into `k * H`. -/
theorem isSelfAdjoint_convolutionOperator (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) :
    IsSelfAdjoint (convolutionOperator k) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  have key : ∀ H : C(G, 𝕜),
      ⟪convolutionOperator k f, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
        = ⟪f, convolutionOperator k (ContinuousMap.toLp 2 (haarProb G) 𝕜 H)⟫_𝕜 := by
    intro H
    rw [inner_convolutionOperator_toLp, integral_weightedSections, convolutionOperator_apply]
    congr 2
    ext y
    rw [integral_weightedSectionsCM_apply, convolutionCLM_apply_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) H] with x hx
    have hsym : (starRingEnd 𝕜) (k (x * y⁻¹)) = k (y * x⁻¹) := by
      rw [← hk (x * y⁻¹), mul_inv_rev, inv_inv]
    rw [hx, hsym, mul_comm]
  have hcont₁ : Continuous fun u : Lp 𝕜 2 (haarProb G) => ⟪convolutionOperator k f, u⟫_𝕜 :=
    continuous_const.inner continuous_id
  have hcont₂ : Continuous fun u : Lp 𝕜 2 (haarProb G) => ⟪f, convolutionOperator k u⟫_𝕜 :=
    continuous_const.inner (convolutionOperator k).continuous
  exact congrFun
    ((ContinuousMap.toLp_denseRange (E := 𝕜) (p := 2) (haarProb G) 𝕜
      (by simp)).equalizer hcont₁ hcont₂ (funext key)) h

/-! ### Equivariance under right translation -/

/-- **Convolution commutes with right translation.** Translating `f` on the right by `g₀` and then
convolving is the same as convolving and then translating the result, because the kernel
`(x, y) ↦ k (x * y⁻¹)` is unchanged by right translation of both variables.

This is what makes every eigenspace of a convolution operator a right-translation-invariant
subspace of `L²(G)`, hence, once the eigenspace is known to be finite-dimensional, the carrier of a
finite-dimensional representation of `G`. -/
theorem convolutionCLM_compMeasurePreserving_mul_right (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (g₀ x : G) :
    convolutionCLM k
        (Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f) x
      = convolutionCLM k f (x * g₀) := by
  have hg : ∀ y : G, x * g₀ * (y * g₀)⁻¹ = x * y⁻¹ := fun y => by group
  rw [convolutionCLM_apply_apply, convolutionCLM_apply_apply,
    ← integral_mul_right_eq_self (fun y => k (x * g₀ * y⁻¹) * (f : G → 𝕜) y) g₀]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (E := 𝕜) (p := 2) f
    (measurePreserving_mul_right (haarProb G) g₀)] with y hy
  rw [hy, hg y]
  rfl

/-- **The convolution operator commutes with right translation on `L²(G)`.** This is
`convolutionCLM_compMeasurePreserving_mul_right` read in `L²(G)`; it is the form in which the
eigenspaces of `convolutionOperator k` are seen to be right-translation-invariant. -/
theorem convolutionOperator_compMeasurePreserving_mul_right (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (g₀ : G) :
    convolutionOperator k
        (Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f)
      = Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀)
          (convolutionOperator k f) := by
  have hqmp := (measurePreserving_mul_right (haarProb G) g₀).quasiMeasurePreserving
  rw [Lp.ext_iff]
  refine (coeFn_convolutionOperator k _).trans ?_
  refine Filter.EventuallyEq.symm (((Lp.coeFn_compMeasurePreserving (E := 𝕜) (p := 2)
    (convolutionOperator k f) (measurePreserving_mul_right (haarProb G) g₀)).trans
      (hqmp.ae_eq_comp (coeFn_convolutionOperator k f))).trans ?_)
  exact Filter.Eventually.of_forall fun y =>
    (convolutionCLM_compMeasurePreserving_mul_right k f g₀ y).symm

end CompactGroup

end TauCeti
