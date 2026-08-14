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

The smoothness is part of the structure itself, while relations to a symplectic form are not
fields of it. Tameness and compatibility are currently available only pointwise, as
`TauCeti.SymplecticForm.Tames` and `TauCeti.SymplecticForm.Compatible` on a real module, so they
can only be stated for the tangent-fiber structures produced by `almostComplexStructureAt`. This
is the manifold-level definition needed in Lane F2.1 of the analytic Heegaard Floer roadmap
before manifold-valued `J`-holomorphic maps can be stated.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure`: a smooth tangent-bundle endomorphism squaring to `-1`.
* `TauCeti.SmoothAlmostComplexStructure.almostComplexStructureAt`: the pointwise almost complex
  structure on a tangent space.
* `TauCeti.SmoothAlmostComplexStructure.contMDiff_apply`: applying the structure to a `C^n` vector
  field along a `C^n` map gives a `C^n` vector field along that map.
* `TauCeti.SmoothAlmostComplexStructure.neg`: the negative of a smooth almost complex structure.
* `TauCeti.SmoothAlmostComplexStructure.const`: a continuous endomorphism of a real normed space
  squaring to `-1` gives the constant smooth almost complex structure on that model manifold.
* `TauCeti.AlmostComplexStructure.constSmooth`: a pointwise almost complex structure on a
  finite-dimensional real normed space gives the constant smooth almost complex structure on that
  model manifold.
* `TauCeti.SmoothAlmostComplexStructure.product`: the standard smooth almost complex structure on
  `V × V`, sending `(v, w)` to `(-w, v)`.

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
def almostComplexStructureAt (J : SmoothAlmostComplexStructure I M) (x : M) :
    AlmostComplexStructure (TangentSpace I x) where
  toLinearMap := (J.toEndomorphism x).toLinearMap
  square_neg := by
    ext v
    have h := congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦ A v)
      (J.square_neg x)
    simpa using h

@[simp]
lemma almostComplexStructureAt_toLinearMap (J : SmoothAlmostComplexStructure I M) (x : M) :
    (J.almostComplexStructureAt x).toLinearMap = (J.toEndomorphism x).toLinearMap :=
  (rfl)

/-- Evaluating the pointwise almost complex structure agrees with evaluating the smooth one. -/
-- This is not a `simp` lemma: `simp` already rewrites the left-hand side through
-- `almostComplexStructureAt_toLinearMap`.
lemma almostComplexStructureAt_apply (J : SmoothAlmostComplexStructure I M) (x : M)
    (v : TangentSpace I x) :
    J.almostComplexStructureAt x v = J x v :=
  (rfl)

/-- Applying a smooth almost complex structure twice gives the negative tangent vector. -/
@[simp]
lemma apply_apply (J : SmoothAlmostComplexStructure I M) (x : M) (v : TangentSpace I x) :
    J x (J x v) = -v :=
  (J.almostComplexStructureAt x).apply_apply v

/-- A smooth almost complex structure is fiberwise injective. -/
lemma injective (J : SmoothAlmostComplexStructure I M) (x : M) : Function.Injective (J x) :=
  (J.almostComplexStructureAt x).injective

/-- A smooth almost complex structure is fiberwise surjective. -/
lemma surjective (J : SmoothAlmostComplexStructure I M) (x : M) : Function.Surjective (J x) :=
  (J.almostComplexStructureAt x).surjective

/-- Two smooth almost complex structures agreeing on every tangent vector are equal. -/
@[ext]
lemma ext (h : ∀ (x : M) (v : TangentSpace I x), J x v = K x v) : J = K := by
  apply toEndomorphism_injective
  ext x v
  exact h x v

section ContMDiffApply

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Applying a smooth almost complex structure along a `C^n` map `b` to a `C^n` vector field along
`b` gives a `C^n` vector field along `b`. Taking `b = id` this says that `J` preserves `C^n`
vector fields on `M`. -/
lemma contMDiff_apply {n : ℕ∞ω} [ENat.LEInfty n] (J : SmoothAlmostComplexStructure I M)
    {b : N → M} (hb : ContMDiff I' I n b) {V : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (V y))) :
    ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (J (b y) (V y))) :=
  ((J.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).comp hb).clm_bundle_apply hV

end ContMDiffApply

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

/-- The pointwise structure of a negated smooth almost complex structure is the negation of the
pointwise structure. -/
@[simp]
lemma neg_almostComplexStructureAt (J : SmoothAlmostComplexStructure I M) (x : M) :
    (-J).almostComplexStructureAt x = -J.almostComplexStructureAt x := by
  ext v
  simp

/-- A continuous endomorphism of a normed space squaring to `-1` defines a constant smooth almost
complex structure on the corresponding model manifold. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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
    -- After the composition and the negated identity are unfolded, the goal is `hJc v`: the
    -- additive group instance on `TangentSpace 𝓘(ℝ, V) x` is the one of `V` itself.
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.neg_apply,
      ContinuousLinearMap.coe_id', id_eq]
    exact hJc v

/-- The endomorphism section of a constant smooth almost complex structure has its defining value
in every fiber. -/
@[simp]
lemma const_toEndomorphism_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v) (x : V) :
    (const Jc hJc).toEndomorphism x = Jc :=
  (rfl)

end SmoothAlmostComplexStructure

namespace AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A pointwise almost complex structure on a finite-dimensional normed vector space defines a
constant smooth almost complex structure on the corresponding model manifold. -/
def constSmooth (J : AlmostComplexStructure V) :
    SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V :=
  SmoothAlmostComplexStructure.const (LinearMap.toContinuousLinearMap J.toLinearMap)
    J.apply_apply

@[simp]
lemma constSmooth_apply (J : AlmostComplexStructure V) (x v : V) :
    J.constSmooth x v = J v :=
  congrArg (fun A : V →L[ℝ] V ↦ A v)
    (SmoothAlmostComplexStructure.const_toEndomorphism_apply _ _ x)

/-- Under the canonical identification of a self-model tangent fiber with the model space,
evaluating a constant smooth almost complex structure is evaluating its defining linear map. -/
@[simp]
lemma fromTangentSpace_constSmooth_apply (J : AlmostComplexStructure V) (x : V)
    (v : TangentSpace 𝓘(ℝ, V) x) :
    NormedSpace.fromTangentSpace x (J.constSmooth x v) =
      J (NormedSpace.fromTangentSpace x v) := by
  exact congrArg
    (fun A : V →L[ℝ] V ↦ A (NormedSpace.fromTangentSpace x v))
    (SmoothAlmostComplexStructure.const_toEndomorphism_apply _ _ x)

@[simp]
lemma constSmooth_almostComplexStructureAt (J : AlmostComplexStructure V) (x : V) :
    J.constSmooth.almostComplexStructureAt x = J := by
  ext v
  exact constSmooth_apply J x v

end AlmostComplexStructure

namespace SmoothAlmostComplexStructure

/-- The standard smooth almost complex structure on `V × V`, sending `(v, w)` to `(-w, v)`. -/
noncomputable def product (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    SmoothAlmostComplexStructure (modelWithCornersSelf ℝ (V × V)) (V × V) :=
  const ((-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V))
    fun v => by ext <;> simp

@[simp]
lemma product_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x v : V × V) :
    product V x v = (-v.2, v.1) :=
  congrArg (fun A : (V × V) →L[ℝ] (V × V) ↦ A v)
    (const_toEndomorphism_apply _ _ x)

@[simp]
lemma product_almostComplexStructureAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V × V) :
    (product V).almostComplexStructureAt x = AlmostComplexStructure.product V := by
  ext v
  exact product_apply x v

end SmoothAlmostComplexStructure

end TauCeti

end
