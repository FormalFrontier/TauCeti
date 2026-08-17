/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda

/-!
# Scheme-valued points of affine Hopf spectra

For a commutative ring `R`, a same-universe commutative Hopf algebra `H`, and a
same-universe commutative `R`-algebra `A`, this file identifies the convolution group
`WithConv (H →ₐ[R] A)` with the group of morphisms over `Spec R` from `Spec A` into
`Spec H`.

The group law on the scheme side is the pointwise group law induced by the group object
represented by `H`; the source `Spec A` need not itself be a group object. No
cocommutativity assumption is made, so the resulting group of points need not be
commutative. The target `(Spec H).asOver (Spec R)` below is definitionally the underlying
object of `(AlgebraicGeometry.hopfSpec R).obj (Opposite.op H)`.

The equivalence and its multiplicativity are Mathlib's
`AlgebraicGeometry.Spec.mapMulEquiv`. This file provides its transport across named scheme
presentations and proves its covariance in the value algebra and contravariance in the coordinate
Hopf algebra.

## Main declarations

* `TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation`: Mathlib's spectrum-points equivalence with
  its target transported across a named presentation.
* `TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation_apply_left`: the underlying spectrum map of
  the transported equivalence.
* `TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue`: a value-algebra map becomes
  precomposition by the corresponding spectrum morphism.
* `TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation_mapValue`: the same covariance after
  transport across a named presentation.
* `TauCeti.CommHopfAlgCat.mapMulEquiv_mapDomain`: a coordinate Hopf morphism
  becomes postcomposition by its contravariant `hopfSpec` image.
* `TauCeti.CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain`: contravariance for arbitrary
  named point equivalences characterized by their underlying spectrum maps.
* `TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf`: the natural comparison between
  convolution points and relative-spectrum points.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R]

private lemma mapMulEquiv_left
    {S T : Type u} [CommRing S] [CommRing T] [Bialgebra R S] [Algebra R T]
    (f : WithConv (S →ₐ[R] T)) :
    (AlgebraicGeometry.Spec.mapMulEquiv f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) :=
  rfl

private lemma hopfSpec_map_left
    {H K : _root_.CommHopfAlgCat.{u} R} (φ : H ⟶ K) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom φ.hom.toAlgHom.toRingHom) :=
  rfl

/-- Mathlib's spectrum-points equivalence with its target transported to an equal named scheme
over `Spec R`.

The equality records the complete presentation as a group object over `Spec R`, so both the
structural morphism and the pointwise group law are preserved by the transport. -/
noncomputable def mapMulEquivOfPresentation
    (H : _root_.CommHopfAlgCat.{u} R) (A : Type u) [CommRing A] [Algebra R A]
    {G : Grp (Over (Spec (CommRingCat.of R)))}
    (hG : G = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) :
    WithConv (H →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.X) := by
  subst G
  exact AlgebraicGeometry.Spec.mapMulEquiv

private theorem mapMulEquivOfPresentation_apply_left_comp
    (H : _root_.CommHopfAlgCat.{u} R) (A : Type u) [CommRing A] [Algebra R A]
    {G : Grp (Over (Spec (CommRingCat.of R)))}
    (hG : G = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))
    (hX : G.X.left = Spec (CommRingCat.of H))
    (f : WithConv (H →ₐ[R] A)) :
    (mapMulEquivOfPresentation H A hG f).left ≫
        eqToHom hX =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) := by
  subst G
  rfl

/-- The underlying scheme map of the spectrum point transported across a named presentation.

The second equality names the presentation of the wrapped group's underlying scheme as `Spec H`;
it determines the `eqToHom` appearing in the formula. -/
theorem mapMulEquivOfPresentation_apply_left
    (H : _root_.CommHopfAlgCat.{u} R) (A : Type u) [CommRing A] [Algebra R A]
    {G : Grp (Over (Spec (CommRingCat.of R)))}
    (hG : G = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))
    (hX : G.X.left = Spec (CommRingCat.of H))
    (f : WithConv (H →ₐ[R] A)) :
    (mapMulEquivOfPresentation H A hG f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom hX.symm := by
  apply (cancel_mono (eqToHom hX)).1
  subst G
  rfl

/-- Mathlib's spectrum-points equivalence is natural in the value algebra. Postcomposing
an `A`-valued algebra point by `φ : A ⟶ B` corresponds on spectra to precomposing by
`Spec B ⟶ Spec A`. -/
theorem mapMulEquiv_mapValue
    (H : _root_.CommHopfAlgCat.{u} R) {A B : CommAlgCat.{u} R}
    (φ : A ⟶ B) (p : HopfAlgebra.points (R := R) (H := H) A) :
    AlgebraicGeometry.Spec.mapMulEquiv (HopfAlgebra.mapPoints (H := H) φ p) =
      (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫
        AlgebraicGeometry.Spec.mapMulEquiv p := by
  rw [HopfAlgebra.mapPoints_apply]
  apply Over.OverMorphism.ext
  erw [Over.comp_left]
  simp only [mapMulEquiv_left, OverClass.asOverHom_left]
  erw [← Spec.map_comp]
  rfl

/-- Naturality in the value algebra for spectrum points whose target is transported across a
named presentation. -/
theorem mapMulEquivOfPresentation_mapValue
    (H : _root_.CommHopfAlgCat.{u} R)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {G : Grp (Over (Spec (CommRingCat.of R)))}
    (hG : G = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.X) :
    (mapMulEquivOfPresentation H B hG).symm
        ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) =
      HopfAlgebra.mapPoints (H := H) (CommAlgCat.ofHom φ)
        ((mapMulEquivOfPresentation H A hG).symm p) := by
  let hX : G.X.left = Spec (CommRingCat.of H) :=
    congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hG
  let q : WithConv (H →ₐ[R] A) :=
    (mapMulEquivOfPresentation H A hG).symm p
  have hq :
      (mapMulEquivOfPresentation H B hG).symm
          ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
            (Spec (CommRingCat.of R)) ≫ p) =
        HopfAlgebra.mapPoints (H := H) (CommAlgCat.ofHom φ) q := by
    have hmap := mapMulEquiv_mapValue H (CommAlgCat.ofHom φ) q
    have hp : mapMulEquivOfPresentation H A hG q = p :=
      (mapMulEquivOfPresentation H A hG).apply_symm_apply p
    apply (mapMulEquivOfPresentation H B hG).injective
    rw [(mapMulEquivOfPresentation H B hG).apply_symm_apply, ← hp]
    apply Over.OverMorphism.ext
    apply (cancel_mono (eqToHom hX)).1
    erw [Over.comp_left]
    rw [Category.assoc, mapMulEquivOfPresentation_apply_left_comp H A hG hX,
      mapMulEquivOfPresentation_apply_left_comp H B hG hX]
    have hmapLeft := congrArg Over.Hom.left hmap.symm
    simp only [Over.comp_left, OverClass.asOverHom_left, mapMulEquiv_left] at hmapLeft
    exact hmapLeft
  simpa only [q] using hq

/-- Mathlib's spectrum-points equivalence is contravariantly natural in the coordinate
Hopf algebra. Precomposing a `K`-point by `φ : H ⟶ K` corresponds on spectra to
postcomposing by the group-scheme morphism `Spec K ⟶ Spec H` induced by `hopfSpec`. -/
theorem mapMulEquiv_mapDomain
    {H K : _root_.CommHopfAlgCat.{u} R} (A : CommAlgCat.{u} R)
    (φ : H ⟶ K) (p : HopfAlgebra.points (R := R) (H := K) A) :
    AlgebraicGeometry.Spec.mapMulEquiv ((mapPointsFunctor φ).app A p) =
      AlgebraicGeometry.Spec.mapMulEquiv p ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op).hom.hom := by
  rw [mapPointsFunctor_app_apply]
  apply Over.OverMorphism.ext
  erw [Over.comp_left]
  simp only [mapMulEquiv_left, hopfSpec_map_left]
  erw [← Spec.map_comp]
  rfl

private lemma transportedHopfSpecMap_left
    {H K : _root_.CommHopfAlgCat.{u} R}
    {G H' : Grp (Over (Spec (CommRingCat.of R)))}
    (hG : G = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))
    (hH' : H' = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K))
    (φ : H ⟶ K) :
    (eqToHom hH' ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op ≫
        eqToHom hG.symm).hom.hom.left =
      eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hH') ≫
        Spec.map (CommRingCat.ofHom φ.hom.toAlgHom.toRingHom) ≫
        eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hG).symm := by
  subst G
  subst H'
  rfl

/-- Contravariant naturality in the coordinate Hopf algebra for named point equivalences.

The two equivalences may be public wrappers around `mapMulEquivOfPresentation`; it is enough to
characterize their underlying scheme maps. This lets named affine group schemes reuse the
presentation compatibility without unfolding their definitions. -/
theorem pointMulEquivOfPresentation_mapDomain
    {H K : _root_.CommHopfAlgCat.{u} R} (A : Type u) [CommRing A] [Algebra R A]
    {G H' : Grp (Over (Spec (CommRingCat.of R)))}
    (hG : G = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))
    (hH' : H' = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K))
    (eG : WithConv (H →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.X))
    (eH' : WithConv (K →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ H'.X))
    (eG_apply_left : ∀ f, (eG f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hG).symm)
    (eH'_apply_left : ∀ f, (eH' f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hH').symm)
    (φ : H ⟶ K) (p : HopfAlgebra.points (R := R) (H := K) (CommAlgCat.of R A)) :
    eH' p ≫
        (eqToHom hH' ≫
          (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op ≫
          eqToHom hG.symm).hom.hom =
      eG ((mapPointsFunctor φ).app (CommAlgCat.of R A) p) := by
  let hGX : G.X.left = Spec (CommRingCat.of H) :=
    congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hG
  let hH'X : H'.X.left = Spec (CommRingCat.of K) :=
    congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) hH'
  apply Over.OverMorphism.ext
  -- `erw` matches across `.asOver.left` which is definitionally `Spec A`.
  erw [Over.comp_left, eH'_apply_left,
    transportedHopfSpecMap_left hG hH' φ, eG_apply_left]
  -- The public computations expose the same spectrum maps behind differently wrapped `Over`
  -- sources; restate them explicitly so the two presentation transports can cancel.
  change (Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫ eqToHom hH'X.symm) ≫
      eqToHom hH'X ≫ Spec.map (CommRingCat.ofHom φ.hom.toAlgHom.toRingHom) ≫
        eqToHom hGX.symm =
    Spec.map (CommRingCat.ofHom
      (((mapPointsFunctor φ).app (CommAlgCat.of R A) p).ofConv.toRingHom)) ≫
        eqToHom hGX.symm
  rw [mapPointsFunctor_app_apply, WithConv.ofConv_toConv]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Scheme-valued affine-group points, restricted along relative `Spec` and regarded as a
type-valued presheaf on opposite commutative algebras. -/
noncomputable abbrev schemePointsPresheaf (H : _root_.CommHopfAlgCat.{u} R) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type u :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙
    yoneda.obj
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X

/-- The scheme-points presheaf at `A` is the set of morphisms over `Spec R` from `Spec A` to
`Spec H`. -/
theorem schemePointsPresheaf_obj (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (schemePointsPresheaf H).obj A =
      ((Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X) :=
  rfl

/-- **Convolution points agree naturally with scheme-valued points.** This is Mathlib's
`Spec.mapMulEquiv`, assembled over all value algebras. -/
noncomputable def pointsPresheafIsoSchemePointsPresheaf
    (H : _root_.CommHopfAlgCat.{u} R) :
    HopfAlgebra.pointsPresheaf H ≅ schemePointsPresheaf H :=
  NatIso.ofComponents
    (fun A =>
      (AlgebraicGeometry.Spec.mapMulEquiv
        (R := R) (S := H) (T := A.unop.unop)).toEquiv.toIso)
    (by
      intro A B f
      ext p
      exact mapMulEquiv_mapValue H f.unop.unop p)

-- These component lemmas are deliberately not `@[simp]`: `simpNF` first unfolds the presheaf
-- object expressions in their left-hand sides through functor composition and Yoneda evaluation.

/-- The comparison from convolution points to scheme-valued points is Mathlib's spectrum-points
equivalence at every value algebra. -/
theorem pointsPresheafIsoSchemePointsPresheaf_hom_app_apply
    (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : WithConv (H →ₐ[R] A.unop.unop)) :
    (pointsPresheafIsoSchemePointsPresheaf H).hom.app A p =
      AlgebraicGeometry.Spec.mapMulEquiv p := by
  rw [pointsPresheafIsoSchemePointsPresheaf]
  rfl

/-- The inverse comparison recovers the convolution point represented by a relative spectrum
morphism. -/
theorem pointsPresheafIsoSchemePointsPresheaf_inv_app_apply
    (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : (schemePointsPresheaf H).obj A) :
    (pointsPresheafIsoSchemePointsPresheaf H).inv.app A p =
      AlgebraicGeometry.Spec.mapMulEquiv.symm p := by
  rw [pointsPresheafIsoSchemePointsPresheaf]
  rfl

end CommHopfAlgCat

end TauCeti
