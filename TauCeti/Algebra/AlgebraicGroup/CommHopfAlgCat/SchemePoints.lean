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
# Scheme-valued points of affine Hopf-algebra spectra

For a commutative ring `R` and a same-universe commutative bialgebra `H`, this file identifies
the convolution monoid of `H`-points with morphisms over `Spec R` into `Spec H`. It treats both
affine test schemes `Spec A` and arbitrary schemes `T`, whose points are valued in the relative
global sections of `T` through the relative `Γ-Spec` adjunction.

The monoid law on the scheme side is the pointwise law induced by the monoid object represented
by `H`; the source `Spec A` need not itself be a monoid object. No cocommutativity assumption is
made, so the resulting monoid of points need not be commutative. The target
`(Spec H).asOver (Spec R)` below is definitionally the underlying object of
`(AlgebraicGeometry.bialgSpec R).obj (Opposite.op (CommBialgCat.of R H))`.

The affine equivalence and its multiplicativity are Mathlib's
`AlgebraicGeometry.Spec.mapMulEquiv`. The comparison for arbitrary test schemes upgrades
Mathlib's `AlgebraicGeometry.algΓAlgSpecAdjunction` to a multiplicative equivalence. This file
proves this comparison at bialgebra/monoid generality. It additionally records the Hopf-algebra
case: transport across named `Grp`-presentations and the points-presheaf isomorphism for
`CommHopfAlgCat`, together with covariance in the value algebra and contravariance in the
coordinate algebra.

## Main declarations

* `TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv`: maps from an arbitrary relative scheme to
  an affine bialgebra spectrum are convolution points valued in its relative global sections.
* `TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_apply`: the forward comparison applies
  relative global sections and then the adjunction counit.
* `TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_symm_apply`: the inverse comparison is the
  adjunction unit followed by the spectrum map of the convolution point.
* `TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_precomp`: the comparison is natural in the
  test scheme.
* `TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_mapDomain`: the comparison is
  contravariantly natural in the coordinate bialgebra.
* `TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation`: Mathlib's spectrum-points equivalence with
  its target transported across a named presentation.
* `TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation_apply_left`: the underlying spectrum map of
  the transported equivalence.
* `TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue`: a value-algebra map becomes
  precomposition by the corresponding spectrum morphism.
* `TauCeti.CommHopfAlgCat.mapMulEquivOfPresentation_mapValue`: the same covariance after
  transport across a named presentation.
* `TauCeti.CommHopfAlgCat.mapMulEquiv_mapDomain`: a coordinate bialgebra morphism
  becomes postcomposition by the induced relative spectrum morphism `Spec K ⟶ Spec H`.
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

/-- The scheme morphism underlying the spectrum-points equivalence is induced by the underlying
ring homomorphism of the algebra point. -/
lemma mapMulEquiv_left
    {S T : Type u} [CommRing S] [CommRing T] [Bialgebra R S] [Algebra R T]
    (f : WithConv (S →ₐ[R] T)) :
    (AlgebraicGeometry.Spec.mapMulEquiv f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) :=
  rfl

/-- Mathlib's spectrum-points equivalence is contravariantly natural in the coordinate
bialgebra. Precomposing a `K`-point by `f : H →ₐc[R] K` corresponds on spectra to
postcomposing by the induced morphism `Spec K ⟶ Spec H`. -/
theorem mapMulEquiv_mapDomain
    {H K : Type u} [CommRing H] [CommRing K] [Bialgebra R H] [Bialgebra R K]
    (A : CommAlgCat.{u} R) (f : H →ₐc[R] K)
    (p : WithConv (K →ₐ[R] A)) :
    AlgebraicGeometry.Spec.mapMulEquiv (AlgHom.mapDomain f p) =
      AlgebraicGeometry.Spec.mapMulEquiv p ≫
        (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of R)) := by
  apply Over.OverMorphism.ext
  erw [Over.comp_left]
  simp only [mapMulEquiv_left, OverClass.asOverHom_left, AlgHom.mapDomain_apply]
  erw [← Spec.map_comp]
  rfl

/-! ### Points of affine spectra on arbitrary test schemes -/

private theorem algSpec_obj_eq_spec
    (H : Type u) [CommRing H] [Algebra R H] :
    (algSpec (CommRingCat.of R)).obj (Opposite.op (CommAlgCat.of R H)) =
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) :=
  rfl

/-- The relative `Γ-Spec` adjunction as an equivalence between scheme-valued points and
convolution points, before recording multiplicativity. -/
private noncomputable def schemePointsAlgΓEquiv
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) ≃
      WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop) := by
  let e₀ := (algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv T
    (Opposite.op (CommAlgCat.of R H))
  exact (Equiv.cast (congrArg (fun X ↦ T ⟶ X) (algSpec_obj_eq_spec H).symm)).trans
    (e₀.symm.trans
      ((opEquiv ((algΓ (CommRingCat.of R)).obj T) (Opposite.op (CommAlgCat.of R H))).trans
        (HopfAlgebra.pointsHomEquiv H ((algΓ (CommRingCat.of R)).obj T).unop)))

/-- A private elaboration bridge between the adjunction's composite-functor target and the
definitionally equal relative-spectrum presentation. Keeping this bridge opaque prevents
category-rewriting tactics from losing the latter presentation at `implicit` transparency. -/
private noncomputable def algΓUnitToSpec (T : Over (Spec (CommRingCat.of R))) :
    T ⟶ (Spec (CommRingCat.of ((algΓ (CommRingCat.of R)).obj T).unop)).asOver
      (Spec (CommRingCat.of R)) :=
  (algΓAlgSpecAdjunction (CommRingCat.of R)).unit.app T

/-- A convolution point over the global sections of `T`, regarded as a `T`-valued point through
the relative spectrum presentation. -/
private noncomputable def algΓPointSchemePoint
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    T ⟶ (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) :=
  algΓUnitToSpec T ≫ AlgebraicGeometry.Spec.mapMulEquiv p

private theorem schemePointsAlgΓEquiv_symm_apply
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    (schemePointsAlgΓEquiv H T).symm p =
      (algΓAlgSpecAdjunction (CommRingCat.of R)).unit.app T ≫
        (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom p.ofConv).op := by
  rw [schemePointsAlgΓEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    Equiv.symm_trans_apply,
    HopfAlgebra.pointsHomEquiv_symm_apply]
  -- The remaining `Equiv.cast` transports the relative-spectrum presentation, while
  -- `opEquiv` reverses the bundled algebra morphism. These wrappers are definitionally the
  -- displayed adjunction hom-equivalence application; there is no morphism-level rewrite for
  -- the cast through the three composed equivalences.
  change ((algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv T
      (Opposite.op (CommAlgCat.of R H))) (CommAlgCat.ofHom p.ofConv).op = _
  rw [Adjunction.homEquiv_unit]

private theorem mapMulEquiv_eq_algSpec_map
    (H : Type u) [CommRing H] [Bialgebra R H]
    (A : Type u) [CommRing A] [Algebra R A]
    (p : WithConv (H →ₐ[R] A)) :
    AlgebraicGeometry.Spec.mapMulEquiv p =
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom p.ofConv).op := by
  apply Over.OverMorphism.ext
  rw [mapMulEquiv_left, algSpec_map_left]
  rfl

private theorem algΓPointSchemePoint_eq_symm
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    algΓPointSchemePoint H T p = (schemePointsAlgΓEquiv H T).symm p := by
  rw [schemePointsAlgΓEquiv_symm_apply]
  exact congrArg (algΓUnitToSpec T ≫ ·) (mapMulEquiv_eq_algSpec_map H _ p)

private theorem algΓPointSchemePoint_mul
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (p q : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    algΓPointSchemePoint H T (p * q) =
      algΓPointSchemePoint H T p * algΓPointSchemePoint H T q := by
  unfold algΓPointSchemePoint
  rw [map_mul, MonObj.comp_mul]

/-- Maps from an arbitrary scheme `T` over `Spec R` to the affine monoid scheme represented by
`H` are the convolution monoid of `H`-points valued in the relative global sections of `T`.

Unlike `AlgebraicGeometry.Spec.mapMulEquiv`, the test scheme here need not be affine. The
equivalence is the relative `Γ-Spec` adjunction, with its target given the convolution product.
-/
noncomputable def schemePointsAlgΓMulEquiv
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) ≃*
      WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop) :=
  { schemePointsAlgΓEquiv H T with
    map_mul' := by
      intro g h
      apply (schemePointsAlgΓEquiv H T).symm.injective
      calc
        _ = g * h := (schemePointsAlgΓEquiv H T).symm_apply_apply (g * h)
        _ = algΓPointSchemePoint H T (schemePointsAlgΓEquiv H T g) *
            algΓPointSchemePoint H T (schemePointsAlgΓEquiv H T h) := by
          rw [algΓPointSchemePoint_eq_symm, algΓPointSchemePoint_eq_symm,
            Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        _ = algΓPointSchemePoint H T
            (schemePointsAlgΓEquiv H T g * schemePointsAlgΓEquiv H T h) :=
          (algΓPointSchemePoint_mul H T _ _).symm
        _ = (schemePointsAlgΓEquiv H T).symm
            (schemePointsAlgΓEquiv H T g * schemePointsAlgΓEquiv H T h) :=
          algΓPointSchemePoint_eq_symm H T _ }

/-- The forward relative `Γ-Spec` comparison applies relative global sections to the scheme
point and composes with the adjunction counit, then regards the resulting algebra morphism as a
convolution point. -/
@[simp]
theorem schemePointsAlgΓMulEquiv_apply
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (g : T ⟶ (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :
    schemePointsAlgΓMulEquiv H T g =
      WithConv.toConv (((algΓ (CommRingCat.of R)).map g ≫
        (algΓAlgSpecAdjunction (CommRingCat.of R)).counit.app
          (Opposite.op (CommAlgCat.of R H))).unop.hom) := by
  -- `schemePointsAlgΓMulEquiv` is a structure update of `schemePointsAlgΓEquiv` that only
  -- supplies `map_mul'`; expose their definitionally identical forward maps for simplification.
  change schemePointsAlgΓEquiv H T g = _
  unfold schemePointsAlgΓEquiv
  simp only [Equiv.trans_apply, HopfAlgebra.pointsHomEquiv_apply,
    Adjunction.homEquiv_counit]
  rfl

private theorem schemePointsAlgΓMulEquiv_symm_apply_spec
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    (schemePointsAlgΓMulEquiv H T).symm p = algΓPointSchemePoint H T p :=
  (algΓPointSchemePoint_eq_symm H T p).symm

/-- The inverse relative `Γ-Spec` comparison is the adjunction unit followed by the affine
spectrum point represented by `p`. -/
@[simp]
theorem schemePointsAlgΓMulEquiv_symm_apply
    (H : Type u) [CommRing H] [Bialgebra R H]
    (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    (schemePointsAlgΓMulEquiv H T).symm p =
      ((algΓAlgSpecAdjunction (CommRingCat.of R)).unit.app T :
          T ⟶ (Spec (CommRingCat.of ((algΓ (CommRingCat.of R)).obj T).unop)).asOver
            (Spec (CommRingCat.of R))) ≫
        AlgebraicGeometry.Spec.mapMulEquiv p :=
  schemePointsAlgΓMulEquiv_symm_apply_spec H T p

/-- The global-sections comparison is natural in the test scheme. Precomposing a `T`-valued
point by `φ : S ⟶ T` postcomposes its algebra point with the induced map `Γ(T) ⟶ Γ(S)`. -/
theorem schemePointsAlgΓMulEquiv_precomp
    (H : Type u) [CommRing H] [Bialgebra R H]
    {S T : Over (Spec (CommRingCat.of R))} (φ : S ⟶ T)
    (g : T ⟶ (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :
    schemePointsAlgΓMulEquiv H S (φ ≫ g) =
      AlgHom.mapValue ((algΓ (CommRingCat.of R)).map φ).unop.hom
        (schemePointsAlgΓMulEquiv H T g) := by
  rw [schemePointsAlgΓMulEquiv_apply, schemePointsAlgΓMulEquiv_apply,
    AlgHom.mapValue_apply]
  congr 1

/-- The global-sections comparison is contravariantly natural in the coordinate bialgebra.
Postcomposing a scheme-valued point with `Spec f` is precomposition of its algebra point by `f`.
-/
theorem schemePointsAlgΓMulEquiv_mapDomain
    {H K : Type u} [CommRing H] [CommRing K] [Bialgebra R H] [Bialgebra R K]
    (T : Over (Spec (CommRingCat.of R))) (f : H →ₐc[R] K)
    (g : T ⟶ (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of R))) :
    schemePointsAlgΓMulEquiv H T
        (g ≫ (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of R))) =
      AlgHom.mapDomain f (schemePointsAlgΓMulEquiv K T g) := by
  let eH := schemePointsAlgΓMulEquiv H T
  let eK := schemePointsAlgΓMulEquiv K T
  apply eH.symm.injective
  calc
    eH.symm (eH (g ≫ (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)).asOver
        (Spec (CommRingCat.of R)))) =
        g ≫ (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of R)) := eH.symm_apply_apply _
    _ = eH.symm (AlgHom.mapDomain f (eK g)) := by
      conv_lhs => rw [← eK.symm_apply_apply g]
      dsimp only [eH, eK]
      rw [schemePointsAlgΓMulEquiv_symm_apply_spec,
        schemePointsAlgΓMulEquiv_symm_apply_spec]
      unfold algΓPointSchemePoint
      rw [Category.assoc]
      congr 1
      exact (mapMulEquiv_mapDomain _ f (eK g)).symm

/-! ### Points on affine test schemes -/

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
