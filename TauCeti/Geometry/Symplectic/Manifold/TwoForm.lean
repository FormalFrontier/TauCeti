/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Geometry.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex

/-!
# Nondegenerate, tame, and compatible two-forms on manifolds

This file supplies the fiberwise part of a symplectic structure on a smooth manifold. A smooth
two-form is nondegenerate when its value on every tangent space is a nondegenerate alternating
bilinear form. Such a value is therefore a `TauCeti.SymplecticForm`, so the pointwise linear theory
can be reused without restating it.

Tameness and compatibility with a smooth almost complex structure are kept as unbundled
predicates. They are pointwise exactly `SymplecticForm.Tames` and `SymplecticForm.Compatible`.
In particular, tameness already forces fiberwise nondegeneracy. The constant construction shows
that every finite-dimensional symplectic vector space, and especially the standard doubled model,
gives a non-vacuous manifold-level example.

Closedness is not included: the pinned Mathlib has no exterior derivative of manifold differential
forms. A symplectic manifold will be a smooth two-form satisfying both the nondegeneracy predicate
defined here and the separate closedness predicate once that exterior-calculus layer exists.

## Main declarations

* `TauCeti.SmoothTwoForm.IsNondegenerate`: fiberwise nondegeneracy of a smooth two-form.
* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt`: the symplectic form on a tangent fiber.
* `TauCeti.SmoothTwoForm.Tames` and `TauCeti.SmoothTwoForm.Compatible`: the unbundled pointwise
  relations to a smooth almost complex structure.
* `TauCeti.SmoothTwoForm.IsNondegenerate.tames_iff`, `invariant_iff`, and `compatible_iff`: these
  relations characterized fiber by fiber through the linear theory.
* `TauCeti.SymplecticForm.constSmooth`: a symplectic form as a constant smooth two-form.

The definitions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.2.
-/

public section

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- A smooth two-form is fiberwise nondegenerate when its algebraic bilinear form on every tangent
space is nondegenerate. Closedness is a separate condition. -/
def IsNondegenerate (form : SmoothTwoForm I M) : Prop :=
  ∀ x, (form.bilinFormAt x).Nondegenerate

/-- Fiberwise nondegeneracy in terms of vectors annihilating every vector on the right. For an
alternating form this one-sided condition implies the corresponding condition on the other side. -/
lemma isNondegenerate_iff_separatingLeft :
    form.IsNondegenerate ↔
      ∀ (x : M) (v : TangentSpace I x),
        (∀ w, form x v w = 0) → v = 0 := by
  constructor
  · intro h x v hv
    apply (h x).1 v
    intro w
    simpa only [bilinFormAt_apply] using hv w
  · intro h x
    have hrefl := (form.isAlt_bilinFormAt x).isRefl
    apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr
    intro v hv
    apply h x v
    intro w
    simpa only [bilinFormAt_apply] using hv w

/-- A fiberwise nondegenerate smooth two-form gives a symplectic form on each tangent space. -/
def IsNondegenerate.symplecticFormAt (h : form.IsNondegenerate) (x : M) :
    SymplecticForm (TangentSpace I x) where
  toBilinForm := form.bilinFormAt x
  isAlt := form.isAlt_bilinFormAt x
  nondegenerate := h x

/-- The tangent-space symplectic form evaluates as the original smooth two-form. -/
@[simp]
lemma IsNondegenerate.symplecticFormAt_apply (h : form.IsNondegenerate) (x : M)
    (v w : TangentSpace I x) :
    h.symplecticFormAt x v w = form x v w :=
  form.bilinFormAt_apply x v w

/-- A smooth two-form tames a smooth almost complex structure when
`form_x(v, J_x v) > 0` for every nonzero tangent vector. -/
def Tames (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < form x v (J x v)

/-- Manifold-level tameness is the pointwise linear tameness condition once nondegeneracy has
identified each tangent-space form as a `SymplecticForm`. -/
lemma IsNondegenerate.tames_iff (h : form.IsNondegenerate) :
    form.Tames J ↔ ∀ x, (h.symplecticFormAt x).Tames (J.almostComplexStructureAt x) := by
  constructor <;> intro htame x v hv
  · simpa only [IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using htame x v hv
  · simpa only [IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using htame x v hv

/-- A tame smooth two-form is fiberwise nondegenerate. -/
lemma Tames.isNondegenerate (h : form.Tames J) : form.IsNondegenerate := by
  rw [isNondegenerate_iff_separatingLeft]
  intro x v hv
  by_contra hv0
  exact (h x v hv0).ne' (hv (J x v))

/-- A smooth two-form is invariant under a smooth almost complex structure when applying the
structure in both tangent arguments leaves the form unchanged. -/
def Invariant (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x), form x (J x v) (J x w) = form x v w

/-- Apply invariance at a point and two tangent vectors. -/
lemma Invariant.apply (h : form.Invariant J) (x : M) (v w : TangentSpace I x) :
    form x (J x v) (J x w) = form x v w :=
  h x v w

/-- Manifold-level invariance is the pointwise linear invariance condition once nondegeneracy has
identified each tangent-space form as a `SymplecticForm`. -/
lemma IsNondegenerate.invariant_iff (h : form.IsNondegenerate) :
    form.Invariant J ↔ ∀ x, (h.symplecticFormAt x).Invariant (J.almostComplexStructureAt x) := by
  simp only [SymplecticForm.invariant_iff]
  constructor <;> intro hinv x v w
  · simpa only [IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hinv x v w
  · simpa only [IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hinv x v w

/-- Compatibility is the conjunction of invariance and tameness. Neither relation is stored in
the smooth two-form or almost complex structure. -/
structure Compatible (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M) : Prop where
  /-- Applying the almost complex structure in both entries preserves the two-form. -/
  invariant : form.Invariant J
  /-- The two-form is positive on every complex line. -/
  tames : form.Tames J

/-- Compatibility implies fiberwise nondegeneracy. -/
lemma Compatible.isNondegenerate (h : form.Compatible J) : form.IsNondegenerate :=
  h.tames.isNondegenerate

/-- Manifold-level compatibility is compatibility of the induced linear pair on every tangent
space. -/
lemma IsNondegenerate.compatible_iff (h : form.IsNondegenerate) :
    form.Compatible J ↔ ∀ x, (h.symplecticFormAt x).Compatible (J.almostComplexStructureAt x) := by
  simp only [SymplecticForm.compatible_iff, forall_and]
  constructor
  · intro hcompat
    exact ⟨h.invariant_iff.mp hcompat.invariant, h.tames_iff.mp hcompat.tames⟩
  · rintro ⟨hinv, htame⟩
    exact ⟨h.invariant_iff.mpr hinv, h.tames_iff.mpr htame⟩

/-- Manifold-level compatibility gives the existing compatible-pair structure on each tangent
space. -/
lemma Compatible.compatibleAt (h : form.Compatible J) (x : M) :
    (h.isNondegenerate.symplecticFormAt x).Compatible (J.almostComplexStructureAt x) :=
  h.isNondegenerate.compatible_iff.mp h x

end SmoothTwoForm

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A symplectic form on a finite-dimensional normed vector space, regarded as a constant smooth
two-form on the corresponding model manifold. -/
def constSmooth (omegaForm : SymplecticForm V) :
    SmoothTwoForm (modelWithCornersSelf ℝ V) V :=
  SmoothTwoForm.const omegaForm.toBilinForm.toContinuousBilinearMap omegaForm.isAlt

/-- A constant smooth symplectic form evaluates as its defining algebraic form. -/
@[simp]
lemma constSmooth_apply (omegaForm : SymplecticForm V) (x v w : V) :
    omegaForm.constSmooth x v w = omegaForm v w := by
  simp only [constSmooth]
  -- The two sides of `SmoothTwoForm.const_toContMDiffSection_apply` live in the fiber type
  -- `TangentSpace 𝓘(ℝ, V) x →L[ℝ] _` and in `V →L[ℝ] _`, so `rw` cannot rewrite underneath the
  -- application; the equality is transported by `congrArg` instead.
  exact (congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ ↦ B v w)
    (SmoothTwoForm.const_toContMDiffSection_apply _ _ x)).trans
      (LinearMap.toContinuousBilinearMap_apply _ v w)

/-- Under the canonical identification of a self-model tangent fiber with the model space,
evaluating a constant smooth symplectic form is evaluating its defining bilinear form. -/
@[simp]
lemma fromTangentSpace_constSmooth_apply (omegaForm : SymplecticForm V) (x : V)
    (v w : TangentSpace 𝓘(ℝ, V) x) :
    omegaForm.constSmooth x v w =
      omegaForm (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := by
  exact (congrArg
    (fun B : V →L[ℝ] V →L[ℝ] ℝ ↦
      B (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w))
    (SmoothTwoForm.const_toContMDiffSection_apply _ _ x)).trans
      (LinearMap.toContinuousBilinearMap_apply _ _ _)

/-- A constant smooth symplectic form is fiberwise nondegenerate. -/
@[simp]
lemma isNondegenerate_constSmooth (omegaForm : SymplecticForm V) :
    omegaForm.constSmooth.IsNondegenerate := fun x => by
  have hx : omegaForm.constSmooth.bilinFormAt x = omegaForm.toBilinForm :=
    SmoothTwoForm.const_bilinFormAt _ _ x
  rw [hx]
  exact omegaForm.nondegenerate

/-- Tameness of a pair of constant smooth structures is exactly tameness of the underlying linear
pair. -/
@[simp]
lemma tames_constSmooth_iff {omegaForm : SymplecticForm V} {J : AlmostComplexStructure V} :
    omegaForm.constSmooth.Tames J.constSmooth ↔ omegaForm.Tames J := by
  constructor
  · intro h v hv
    simpa only [constSmooth_apply, AlmostComplexStructure.constSmooth_apply] using h 0 v hv
  · intro h x v hv
    -- Use Mathlib's explicit canonical identification of a self-model tangent fiber with `V`.
    let e : TangentSpace 𝓘(ℝ, V) x ≃L[ℝ] V := NormedSpace.fromTangentSpace x
    have hev : e v ≠ 0 := fun hev ↦ hv (e.injective (hev.trans e.map_zero.symm))
    simpa only [e, fromTangentSpace_constSmooth_apply,
      AlmostComplexStructure.fromTangentSpace_constSmooth_apply] using h (e v) hev

/-- Invariance of a pair of constant smooth structures is exactly invariance of the underlying
linear pair. -/
@[simp]
lemma invariant_constSmooth_iff {omegaForm : SymplecticForm V} {J : AlmostComplexStructure V} :
    omegaForm.constSmooth.Invariant J.constSmooth ↔ omegaForm.Invariant J := by
  rw [SymplecticForm.invariant_iff]
  constructor
  · intro h v w
    simpa only [constSmooth_apply, AlmostComplexStructure.constSmooth_apply] using h 0 v w
  · intro h x v w
    -- Use the same canonical identification for both tangent vectors.
    let e : TangentSpace 𝓘(ℝ, V) x ≃L[ℝ] V := NormedSpace.fromTangentSpace x
    simpa only [e, fromTangentSpace_constSmooth_apply,
      AlmostComplexStructure.fromTangentSpace_constSmooth_apply] using h (e v) (e w)

/-- Compatibility of a pair of constant smooth structures is exactly compatibility of the
underlying linear pair. -/
@[simp]
lemma compatible_constSmooth_iff {omegaForm : SymplecticForm V} {J : AlmostComplexStructure V} :
    omegaForm.constSmooth.Compatible J.constSmooth ↔ omegaForm.Compatible J := by
  rw [SymplecticForm.compatible_iff]
  constructor
  · intro h
    exact ⟨invariant_constSmooth_iff.mp h.invariant, tames_constSmooth_iff.mp h.tames⟩
  · rintro ⟨hinv, htame⟩
    exact ⟨invariant_constSmooth_iff.mpr hinv, tames_constSmooth_iff.mpr htame⟩

end SymplecticForm

end TauCeti

end
