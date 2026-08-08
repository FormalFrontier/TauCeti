/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Smooth almost complex structures on manifolds

This file lifts the pointwise linear algebra of `TauCeti.AlmostComplexStructure` to smooth
manifolds. A smooth almost complex structure is a smooth section of the endomorphism bundle of
the tangent bundle whose square is fiberwise minus the identity. Its value at each point is the
existing pointwise almost complex structure on that tangent space.

The smoothness is part of the structure itself, while relations to a symplectic form such as
tameness and compatibility remain separate hypotheses. This is the manifold-level definition
needed in Lane F2.1 of the analytic Heegaard Floer roadmap before manifold-valued
`J`-holomorphic maps can be stated.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure`: a smooth tangent-bundle endomorphism squaring to `-1`.
* `TauCeti.SmoothAlmostComplexStructure.atPoint`: the pointwise almost complex structure on a
  tangent space.
* `TauCeti.SmoothAlmostComplexStructure.contMDiff_apply`: applying the structure to a smooth
  vector field gives a smooth vector field.
* `TauCeti.AlmostComplexStructure.toSmoothModelSpace`: a constant pointwise structure gives a
  smooth almost complex structure on its model vector space.

The definition follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.2.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth almost complex structure on a manifold is a smooth tangent-bundle endomorphism
whose square is fiberwise minus the identity.

The endomorphism is bundled as a smooth section of `End(TM)`. Tameness, compatibility with a
symplectic form, and integrability are deliberately not fields of this structure. -/
structure SmoothAlmostComplexStructure (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The underlying smooth section of the tangent endomorphism bundle. -/
  toEndomorphism :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
  /-- The defining identity `J² = -1` on every tangent fiber. -/
  square_neg : ∀ x, (toEndomorphism x).comp (toEndomorphism x) = -ContinuousLinearMap.id ℝ _

namespace SmoothAlmostComplexStructure

variable {J K : SmoothAlmostComplexStructure I M}

/-- The underlying smooth endomorphism section determines a smooth almost complex structure. -/
theorem toEndomorphism_injective :
    Function.Injective
      (toEndomorphism : SmoothAlmostComplexStructure I M →
        ContMDiffSection I (E →L[ℝ] E) ∞
          (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)) := by
  rintro ⟨J, hJ⟩ ⟨K, hK⟩ h
  subst h
  rfl

/-- A smooth almost complex structure is applied as `J x v`, evaluating its endomorphism of the
tangent space at `x` on the tangent vector `v`. -/
instance : CoeFun (SmoothAlmostComplexStructure I M) fun _ =>
    (x : M) → TangentSpace I x → TangentSpace I x :=
  ⟨fun J x ↦ J.toEndomorphism x⟩

/-- The value of a smooth almost complex structure at a point, as the existing pointwise
`AlmostComplexStructure` on that tangent space. -/
def atPoint (J : SmoothAlmostComplexStructure I M) (x : M) :
    AlmostComplexStructure (TangentSpace I x) where
  toLinearMap := (J.toEndomorphism x).toLinearMap
  square_neg := by
    ext v
    have h := congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦ A v)
      (J.square_neg x)
    simpa using h

@[simp]
lemma atPoint_toLinearMap (J : SmoothAlmostComplexStructure I M) (x : M) :
    (J.atPoint x).toLinearMap = (J.toEndomorphism x).toLinearMap :=
  (rfl)

/-- Evaluating the pointwise almost complex structure agrees with evaluating the smooth one. -/
-- This is not a `simp` lemma: `simp` already rewrites the left-hand side through
-- `atPoint_toLinearMap`.
lemma atPoint_apply (J : SmoothAlmostComplexStructure I M) (x : M) (v : TangentSpace I x) :
    J.atPoint x v = J x v :=
  (rfl)

/-- Applying a smooth almost complex structure twice gives the negative tangent vector. -/
@[simp]
lemma apply_apply (J : SmoothAlmostComplexStructure I M) (x : M) (v : TangentSpace I x) :
    J x (J x v) = -v :=
  (J.atPoint x).apply_apply v

/-- A smooth almost complex structure is fiberwise injective. -/
lemma injective (J : SmoothAlmostComplexStructure I M) (x : M) : Function.Injective (J x) :=
  (J.atPoint x).injective

/-- A smooth almost complex structure is fiberwise surjective. -/
lemma surjective (J : SmoothAlmostComplexStructure I M) (x : M) : Function.Surjective (J x) :=
  (J.atPoint x).surjective

/-- Two smooth almost complex structures agreeing on every tangent vector are equal. -/
@[ext]
lemma ext (h : ∀ (x : M) (v : TangentSpace I x), J x v = K x v) : J = K := by
  apply toEndomorphism_injective
  ext x v
  exact h x v

/-- The underlying endomorphism field of a smooth almost complex structure is smooth. -/
lemma contMDiff_toEndomorphism (J : SmoothAlmostComplexStructure I M) :
    ContMDiff I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) x (J.toEndomorphism x)) :=
  J.toEndomorphism.contMDiff

/-- Applying a smooth almost complex structure to a smooth vector field gives a smooth vector
field. -/
lemma contMDiff_apply (J : SmoothAlmostComplexStructure I M)
    {V : ∀ x : M, TangentSpace I x}
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (V x))) :
    ContMDiff I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (J x (V x))) :=
  J.contMDiff_toEndomorphism.clm_bundle_apply hV

/-- Negating a smooth almost complex structure gives another smooth almost complex structure. -/
def neg (J : SmoothAlmostComplexStructure I M) : SmoothAlmostComplexStructure I M where
  toEndomorphism := -J.toEndomorphism
  square_neg := by
    intro x
    ext v
    simp

instance : Neg (SmoothAlmostComplexStructure I M) :=
  ⟨neg⟩

@[simp]
lemma neg_toEndomorphism (J : SmoothAlmostComplexStructure I M) :
    (-J).toEndomorphism = -J.toEndomorphism :=
  (rfl)

/-- Evaluating a negated smooth almost complex structure negates its value. -/
-- This is not a `simp` lemma: `simp` already rewrites the left-hand side through
-- `neg_toEndomorphism`.
lemma neg_apply (J : SmoothAlmostComplexStructure I M) (x : M) (v : TangentSpace I x) :
    (-J) x v = -J x v :=
  (rfl)

@[simp]
lemma neg_neg (J : SmoothAlmostComplexStructure I M) : -(-J) = J := by
  ext x v
  simp

/-- A continuous endomorphism of a normed space squaring to `-1` defines a constant smooth almost
complex structure on the corresponding model manifold. -/
private def constantModelSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v) :
    SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V where
  toEndomorphism :=
    ⟨fun _ ↦ Jc, by
      intro x
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, ?_⟩
      simpa [inCoordinates_tangent_bundle_core_model_space] using
        (contMDiffAt_const (x := x) (c := Jc))⟩
  square_neg := by
    intro x
    ext v
    -- For the self model with identity corners, `TangentSpace` reduces definitionally to `V`;
    -- Mathlib has no separate conversion lemma for this identification.
    change Jc (Jc v) = -v
    exact hJc v

private lemma constantModelSpace_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v) (x v : V) :
    constantModelSpace Jc hJc x v = Jc v :=
  (rfl)

end SmoothAlmostComplexStructure

namespace AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A pointwise almost complex structure on a finite-dimensional normed vector space defines a
constant smooth almost complex structure on the corresponding model manifold. -/
def toSmoothModelSpace (J : AlmostComplexStructure V) :
    SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V :=
  SmoothAlmostComplexStructure.constantModelSpace (LinearMap.toContinuousLinearMap J.toLinearMap)
    J.apply_apply

@[simp]
lemma toSmoothModelSpace_apply (J : AlmostComplexStructure V) (x v : V) :
    J.toSmoothModelSpace x v = J v :=
  SmoothAlmostComplexStructure.constantModelSpace_apply _ _ x v

@[simp]
lemma toSmoothModelSpace_atPoint (J : AlmostComplexStructure V) (x : V) :
    J.toSmoothModelSpace.atPoint x = J := by
  ext v
  exact toSmoothModelSpace_apply J x v

end AlmostComplexStructure

namespace SmoothAlmostComplexStructure

/-- The standard smooth almost complex structure on `V × V`, sending `(v, w)` to `(-w, v)`. -/
noncomputable def product (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    SmoothAlmostComplexStructure (modelWithCornersSelf ℝ (V × V)) (V × V) :=
  constantModelSpace ((-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V))
    fun _ ↦ rfl

@[simp]
lemma product_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x v : V × V) :
    product V x v = (-v.2, v.1) :=
  constantModelSpace_apply _ _ x v

@[simp]
lemma product_atPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V × V) :
    (product V).atPoint x = AlmostComplexStructure.product V := by
  ext v
  exact product_apply x v

end SmoothAlmostComplexStructure

end TauCeti

end
