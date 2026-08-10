/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Smooth affine group schemes

This file restricts the anti-equivalence between commutative Hopf algebras and affine group
schemes to the smooth objects. On the coordinate side, smoothness is `Algebra.Smooth R H`. On
the scheme side, it is smoothness of the structural morphism `G ⟶ Spec R`.

The key comparison is `TauCeti.algebraSmooth_iff_smooth_hopfSpec`: a commutative Hopf algebra is
smooth over its base exactly when the structural morphism of its Hopf spectrum is smooth. It
restricts the existing affine anti-equivalence to

`(SmoothCommHopfAlgCat R)ᵒᵖ ≌ SmoothAffineGroupSchemeCat (CommRingCat.of R)`.

Smoothness remains a separate object property in both models. In particular it is not built into
the definition of an affine group scheme, so finite-type group schemes that are non-smooth over a
characteristic-`p` base, such as `μₚ` and `αₚ`, remain in the ambient category.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty`: the smooth object property on commutative Hopf algebras.
* `TauCeti.smoothAffineGroupSchemeProperty`: the smooth structural-morphism property on affine
  group schemes.
* `TauCeti.algebraSmooth_iff_smooth_hopfSpec`: compatibility of the algebraic and
  scheme-theoretic smoothness conditions.
* `TauCeti.smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat`: the restricted
  anti-equivalence.

## References

The affine anti-equivalence is `TauCeti.commHopfAlgCatOpEquivAffineGroupSchemeCat`, assembled
from Mathlib's `AlgebraicGeometry.hopfSpec`. The smoothness comparison uses Mathlib's
`AlgebraicGeometry.HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap`. The organization
mirrors the companion finite-type restriction in Tau Ceti PR #2556. This is the smoothness
predicate synchronization requested in Layer 0 of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

private instance smooth_respectsIso :
    MorphismProperty.RespectsIso (@Smooth) := by
  rw [HasRingHomProperty.eq_affineLocally @Smooth]
  exact affineLocally_respectsIso (@RingHom.Smooth) RingHom.Smooth.respectsIso

/-- The object property on commutative Hopf algebras selecting coordinate algebras smooth over
the base ring. -/
def smoothCommHopfAlgProperty (R : Type u) [CommRing R] :
    ObjectProperty (CommHopfAlgCat.{u} R) :=
  fun H => Algebra.Smooth R H

/-- Membership in the smooth commutative-Hopf-algebra object property. -/
@[simp]
lemma smoothCommHopfAlgProperty_iff {R : Type u} [CommRing R]
    (H : CommHopfAlgCat.{u} R) :
    smoothCommHopfAlgProperty R H ↔ Algebra.Smooth R H :=
  Iff.rfl

/-- The category of commutative Hopf algebras smooth over a commutative ring `R`.

Smoothness is kept as an object property rather than included in the Hopf algebra typeclass. -/
abbrev SmoothCommHopfAlgCat (R : Type u) [CommRing R] :=
  (smoothCommHopfAlgProperty R).FullSubcategory

namespace SmoothCommHopfAlgCat

variable {R : Type u} [CommRing R]

instance : CoeSort (SmoothCommHopfAlgCat R) (Type u) :=
  ⟨fun H => H.obj⟩

instance commRing (H : SmoothCommHopfAlgCat R) : CommRing H :=
  inferInstanceAs (CommRing H.obj)

instance hopfAlgebra (H : SmoothCommHopfAlgCat R) : HopfAlgebra R H :=
  inferInstanceAs (HopfAlgebra R H.obj)

instance smooth (H : SmoothCommHopfAlgCat R) : Algebra.Smooth R H :=
  (smoothCommHopfAlgProperty_iff H.obj).mp H.property

variable (R) in
/-- Construct a bundled smooth commutative Hopf algebra from the usual unbundled typeclasses. -/
abbrev of (H : Type u) [CommRing H] [HopfAlgebra R H] [Algebra.Smooth R H] :
    SmoothCommHopfAlgCat R :=
  ⟨CommHopfAlgCat.of R H,
    (smoothCommHopfAlgProperty_iff _).mpr (inferInstanceAs (Algebra.Smooth R H))⟩

/-- Turn a morphism in `SmoothCommHopfAlgCat` back into a bialgebra morphism. -/
abbrev toBialgHom {H K : SmoothCommHopfAlgCat R} (φ : H ⟶ K) :
    H →ₐc[R] K :=
  φ.hom.hom

/-- Typecheck a bialgebra morphism between smooth commutative Hopf algebras as a morphism in
`SmoothCommHopfAlgCat`. -/
abbrev ofHom {H K : Type u} [CommRing H] [CommRing K]
    [HopfAlgebra R H] [HopfAlgebra R K]
    [Algebra.Smooth R H] [Algebra.Smooth R K] (φ : H →ₐc[R] K) :
    of R H ⟶ of R K :=
  ObjectProperty.homMk (CommHopfAlgCat.ofHom φ)

/-- Two morphisms of smooth commutative Hopf algebras are equal when their underlying bialgebra
morphisms are equal. -/
@[ext]
lemma hom_ext {H K : SmoothCommHopfAlgCat R} {φ ψ : H ⟶ K}
    (h : toBialgHom φ = toBialgHom ψ) : φ = ψ :=
  ObjectProperty.hom_ext (P := smoothCommHopfAlgProperty R)
    (CommHopfAlgCat.hom_ext h)

@[simp]
lemma toBialgHom_id {H : SmoothCommHopfAlgCat R} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id R H :=
  rfl

@[simp]
lemma toBialgHom_comp {H K L : SmoothCommHopfAlgCat R}
    (φ : H ⟶ K) (ψ : K ⟶ L) :
    toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ) :=
  rfl

@[simp]
lemma ofHom_toBialgHom {H K : SmoothCommHopfAlgCat R} (φ : H ⟶ K) :
    ofHom (toBialgHom φ) = φ :=
  rfl

@[simp]
lemma toBialgHom_ofHom {H K : Type u} [CommRing H] [CommRing K]
    [HopfAlgebra R H] [HopfAlgebra R K]
    [Algebra.Smooth R H] [Algebra.Smooth R K] (φ : H →ₐc[R] K) :
    toBialgHom (ofHom (R := R) φ) = φ :=
  rfl

end SmoothCommHopfAlgCat

/-- The object property on affine group schemes over `Spec S` selecting those whose structural
morphism is smooth. -/
def smoothAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  (MorphismProperty.overObj (@Smooth)).inverseImage
    ((affineGroupSchemeProperty S).ι ⋙ Grp.forget _)

/-- Membership in the smooth affine-group-scheme object property. -/
@[simp]
lemma smoothAffineGroupSchemeProperty_iff (S : CommRingCat.{u})
    (G : AffineGroupSchemeCat S) :
    smoothAffineGroupSchemeProperty S G ↔ Smooth G.obj.X.hom :=
  Iff.rfl

instance (S : CommRingCat.{u}) :
    (smoothAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms := by
  unfold smoothAffineGroupSchemeProperty
  let _ : (MorphismProperty.overObj (@Smooth)
      (X := Spec S)).IsClosedUnderIsomorphisms :=
    MorphismProperty.instIsClosedUnderIsomorphismsOverOverObjOfRespectsIso
  infer_instance

/-- The category of smooth affine group schemes over the affine base `Spec S`.

Smoothness is kept as an object property rather than included in the definition of an affine
group scheme. -/
abbrev SmoothAffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (smoothAffineGroupSchemeProperty S).FullSubcategory

/-- An object of `SmoothAffineGroupSchemeCat S` has a smooth structural morphism by
construction. -/
instance (G : SmoothAffineGroupSchemeCat S) : Smooth G.obj.obj.X.hom :=
  (smoothAffineGroupSchemeProperty_iff S G.obj).mp G.property

/-- A commutative Hopf algebra is smooth over its base exactly when the structural morphism of
its Hopf spectrum is smooth.

This is the predicate-level compatibility needed to restrict the affine Hopf/group-scheme
anti-equivalence to smooth objects. -/
@[simp]
theorem algebraSmooth_iff_smooth_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Algebra.Smooth R H ↔
      Smooth (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @Smooth) (eqToHom (hopfSpec_obj_X_left R H))]
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.symm

/-- Under the affine Hopf/group-scheme anti-equivalence, the inverse image of the smooth scheme
property is the smooth coordinate-algebra property. -/
theorem smoothAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (smoothAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (smoothCommHopfAlgProperty R).op := by
  ext H
  let G : AffineGroupSchemeCat (CommRingCat.of R) :=
    ⟨(hopfSpec (CommRingCat.of R)).obj H, by
      apply (affineGroupSchemeProperty_iff _).mpr
      rw [← essImage_hopfSpec]
      exact ⟨H, ⟨Iso.refl _⟩⟩⟩
  let e : (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).functor.obj H ≅ G :=
    (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of R)).app H)
  rw [ObjectProperty.prop_inverseImage_iff,
    smoothAffineGroupSchemeProperty_iff, ObjectProperty.op_iff,
    smoothCommHopfAlgProperty_iff]
  constructor
  · intro h
    have hG : smoothAffineGroupSchemeProperty (CommRingCat.of R) G :=
      (smoothAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e h
    exact (algebraSmooth_iff_smooth_hopfSpec R H.unop).mpr hG
  · intro h
    apply (smoothAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e.symm
    exact (algebraSmooth_iff_smooth_hopfSpec R H.unop).mp h

/-- `Spec` as an anti-equivalence from smooth commutative `R`-Hopf algebras to smooth affine
group schemes over `Spec R`.

This is the restriction of `commHopfAlgCatOpEquivAffineGroupSchemeCat` along
`smoothAffineGroupSchemeProperty_inverseImage`. -/
noncomputable def smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (SmoothCommHopfAlgCat R)ᵒᵖ ≌ SmoothAffineGroupSchemeCat (CommRingCat.of R) :=
  (ObjectProperty.opEquivalence (smoothCommHopfAlgProperty R)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).congrFullSubcategory
        (smoothAffineGroupSchemeProperty_inverseImage R)

/-- The forward restricted equivalence followed by the smooth inclusion is definitionally the
unrestricted equivalence applied after forgetting the smoothness proof. This private isomorphism
isolates the representation boundary of `opEquivalence`, `trans`, and `congrFullSubcategory` from
the public compatibility isomorphism below. -/
private noncomputable def
    smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCatFunctorCompιIso
    (R : Type u) [CommRing R] :
    (smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat R).functor ⋙
        (smoothAffineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (smoothCommHopfAlgProperty R).ι.op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor :=
  Iso.refl _

/-- The forward smooth anti-equivalence, followed by the inclusions into affine group schemes
and then all group schemes, is Mathlib's `hopfSpec` applied after forgetting the smoothness proof.
This is the computation interface for the restricted equivalence. -/
noncomputable def smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat.functorCompιIso
    (R : Type u) [CommRing R] :
    (smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat R).functor ⋙
          (smoothAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (smoothCommHopfAlgProperty R).ι.op ⋙ hopfSpec (CommRingCat.of R) :=
  Functor.isoWhiskerRight
      (smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCatFunctorCompιIso R)
      (affineGroupSchemeProperty (CommRingCat.of R)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (smoothCommHopfAlgProperty R).ι.op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of R))

end TauCeti
