/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# The additive group scheme

For a commutative ring `R`, the one-dimensional additive group is represented by the symmetric
Hopf algebra

`R[x] = SymmetricAlgebra R R`, with `x = SymmetricAlgebra.ι R R 1`.

The generator is primitive, its counit is zero, and its antipode is `-x`. Applying relative
spectrum packages this Hopf algebra as a group object over `Spec R`. This file exposes the
underlying spectrum, structural morphism, multiplication source, and the three group operations
through Tau Ceti's generic Hopf-spectrum projection interface, which is otherwise out of reach:
the resulting group scheme is a `def` whose body is not exposed outside this module.

The singleton basis of `R` identifies the coordinate algebra with a polynomial algebra on the
same-universe singleton `ULift (Fin 1)`. Contravariant spectrum and Mathlib's affine-space
spectrum isomorphism then identify the underlying scheme with affine one-space over `Spec R`.
The identification is packaged in `Over (Spec R)`, so compatibility with the structural morphism
is part of the isomorphism. This uses only the algebra equivalence: the standard bialgebra instance
on `MvPolynomial` has group-like variables and is not the additive Hopf structure.

For a same-universe commutative `R`-algebra `A`, Mathlib's spectrum-points equivalence followed by
`AdditiveGroup.gaPointsMulEquiv` identifies scheme-valued points with `(A, +)`. The resulting
identification is natural in `A`. The construction includes the zero ring and zero value algebra.
The same-universe restriction comes from the current `hopfSpec`, `Spec.mapMulEquiv`, and
affine-space APIs.

## Main declarations

* `TauCeti.AdditiveGroup.coordinateHopfAlgebra`: the symmetric Hopf algebra representing `G_a`.
* `TauCeti.AdditiveGroup.coordinateAlgEquiv`: its rank-one polynomial presentation.
* `TauCeti.AdditiveGroup.groupScheme`: the additive group scheme over `Spec R`.
* `TauCeti.AdditiveGroup.groupSchemeAffineSpaceIso`: its canonical identification with affine
  one-space over the base.
* `TauCeti.AdditiveGroup.groupScheme_one_left`,
  `TauCeti.AdditiveGroup.groupScheme_mul_left`, and
  `TauCeti.AdditiveGroup.groupScheme_inv_left`: the underlying scheme maps of its operations.
* `TauCeti.AdditiveGroup.isAffine_groupScheme`,
  `TauCeti.AdditiveGroup.locallyOfFinitePresentation_groupScheme`, and
  `TauCeti.AdditiveGroup.locallyOfFiniteType_groupScheme`: affineness, local finite presentation,
  and local finite type.
* `TauCeti.AdditiveGroup.groupSchemePointMulEquiv`: the canonical passage between algebra points
  and scheme-valued points.
* `TauCeti.AdditiveGroup.schemePointsMulEquiv`: scheme-valued points are the additive group of
  the value algebra.
* `TauCeti.AdditiveGroup.schemePointsMulEquiv_mapValue`: covariance in the value algebra.

## References

The Hopf structure and algebra-valued point calculation are
`TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra` and
`TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic`. The operation formulas specialize
`TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec`. The affine coordinate presentation follows
the spectrum-transport pattern in `TauCetiProject/TauCeti`, revision
`90f7e09cf472553c4d268db39fcae6b84bd91e04`,
`TauCeti/Algebra/AlgebraicGroup/GeneralLinear/Scheme.lean` (Apache 2.0), specialized to Mathlib's
rank-one symmetric-algebra and affine-space equivalences. The scheme-valued-points interface follows
the “Functor of points is the notion of points” design note in
`TauCetiRoadmap/ReductiveGroups/README.md` and its cited Lean Zulip discussion
[#Is there code for X? > Algebraic groups](https://leanprover.zulipchat.com/#narrow/channel/217875-Is%20there%20code%20for%20X%3F/topic/Algebraic%20groups).
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AdditiveGroup

open AlgebraicGeometry Module MonObj MonoidalCategory WithConv

universe u

/-- A singleton coordinate index in the same universe as the base ring. -/
abbrev CoordinateIndex := ULift.{u} (Fin 1)

section CoordinateAlgebra

variable (R : Type u) [CommSemiring R]

/-- The singleton basis used to present the rank-one symmetric algebra as a polynomial algebra. -/
private noncomputable def coordinateBasis : Basis (CoordinateIndex.{u}) R R :=
  Basis.singleton _ _

/-- The rank-one symmetric algebra is the polynomial algebra on a same-universe singleton. -/
noncomputable def coordinateAlgEquiv :
    SymmetricAlgebra R R ≃ₐ[R] MvPolynomial (CoordinateIndex.{u}) R :=
  SymmetricAlgebra.equivMvPolynomial (coordinateBasis R)

/-- The polynomial presentation sends the additive coordinate `ι(1)` to the unique variable. -/
@[simp]
lemma coordinateAlgEquiv_ι_one :
    coordinateAlgEquiv R (SymmetricAlgebra.ι R R 1) =
      MvPolynomial.X (default : CoordinateIndex.{u}) := by
  simpa only [coordinateAlgEquiv, coordinateBasis, Basis.singleton_apply] using
    SymmetricAlgebra.equivMvPolynomial_ι_apply
      (Basis.singleton (CoordinateIndex.{u}) R) (default : CoordinateIndex.{u})

end CoordinateAlgebra

variable (R : Type u) [CommRing R]

/-- The commutative Hopf algebra representing the one-dimensional additive group. Its carrier is
`SymmetricAlgebra R R`, with primitive generator `SymmetricAlgebra.ι R R 1`. -/
noncomputable abbrev coordinateHopfAlgebra : CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.of R (SymmetricAlgebra R R)

/-- The coordinate algebra of `𝔾ₐ` is of finite type: it is the polynomial algebra on the single
generator `x`. -/
instance instFiniteTypeSymmetricAlgebra : Algebra.FiniteType R (SymmetricAlgebra R R) :=
  Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType R (MvPolynomial Unit R)))
    (SymmetricAlgebra.equivMvPolynomial (Basis.singleton Unit R)).symm

/-- The coordinate algebra of `𝔾ₐ` is smooth: it is the polynomial algebra on the single
generator `x`. -/
instance instSmoothSymmetricAlgebra : Algebra.Smooth R (SymmetricAlgebra R R) :=
  letI : Algebra.Smooth R (MvPolynomial Unit R) := ⟨inferInstance, inferInstance⟩
  Algebra.Smooth.of_equiv
    (SymmetricAlgebra.equivMvPolynomial (Basis.singleton Unit R)).symm

/-- The additive group scheme obtained by applying relative spectrum to the symmetric Hopf
algebra on one generator.

The same-universe restriction is imposed by Mathlib's current `hopfSpec` construction. -/
noncomputable def groupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (coordinateHopfAlgebra R))

/-- The additive group scheme is the relative spectrum of its coordinate Hopf algebra. -/
public lemma groupScheme_def :
    groupScheme R =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (coordinateHopfAlgebra R)) := by
  unfold groupScheme
  rfl

-- The generic `hopfSpec_obj_*` lemmas are stated for the literal functor object, whereas
-- `groupScheme` is a `def` whose body is not exposed outside this module. Downstream the generic
-- lemmas therefore cannot be applied to `(groupScheme R).X` at all, and `simp` cannot see through
-- the wrapper. The specializations below are the projection interface across it: each unfolds the
-- wrapper once and then defers to the corresponding generic lemma, so no spectrum or
-- group-operation computation is redone here.

/-- The scheme underlying the additive group scheme is the spectrum of its symmetric coordinate
algebra. -/
@[simp]
lemma groupScheme_X_left :
    (groupScheme R).X.left = Spec (CommRingCat.of (SymmetricAlgebra R R)) := by
  unfold groupScheme
  exact hopfSpec_obj_X_left R (coordinateHopfAlgebra R)

/-- The structural morphism of the additive group scheme is induced by the symmetric algebra's
`R`-algebra structure map. -/
@[simp]
lemma groupScheme_X_hom :
    (groupScheme R).X.hom =
      eqToHom (groupScheme_X_left R) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R R))) := by
  unfold groupScheme
  convert hopfSpec_obj_X_hom R (coordinateHopfAlgebra R) using 1

/-- The source of multiplication is the standard affine fibre product of two copies of the
coordinate spectrum over `Spec R`. -/
@[simp↓]
lemma groupScheme_tensor_X_left :
    ((groupScheme R).X ⊗ (groupScheme R).X).left =
      Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R R)))) := by
  unfold groupScheme
  convert hopfSpec_obj_tensor_X_left R (coordinateHopfAlgebra R) using 1

/-- The unit of the additive group scheme is induced contravariantly by the symmetric-algebra
counit. -/
@[simp]
lemma groupScheme_one_left :
    η[(groupScheme R).X].left =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R (SymmetricAlgebra R R))) ≫
      eqToHom (groupScheme_X_left R).symm := by
  unfold groupScheme
  convert hopfSpec_obj_one_left R (coordinateHopfAlgebra R) using 1

/-- Multiplication on the additive group scheme is induced contravariantly by the primitive
comultiplication. The first two maps identify its source with the spectrum of the tensor square. -/
@[simp]
lemma groupScheme_mul_left :
    μ[(groupScheme R).X].left =
      eqToHom (groupScheme_tensor_X_left R) ≫
        (pullbackSpecIso R (SymmetricAlgebra R R) (SymmetricAlgebra R R)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom R (SymmetricAlgebra R R))) ≫
        eqToHom (groupScheme_X_left R).symm := by
  unfold groupScheme
  convert hopfSpec_obj_mul_left R (coordinateHopfAlgebra R) using 1

/-- Inversion on the additive group scheme is induced contravariantly by the antipode
`x ↦ -x`. -/
@[simp]
lemma groupScheme_inv_left :
    ι[(groupScheme R).X].left =
      eqToHom (groupScheme_X_left R) ≫
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.antipodeAlgHom R (SymmetricAlgebra R R)).toRingHom) ≫
        eqToHom (groupScheme_X_left R).symm := by
  unfold groupScheme
  convert hopfSpec_obj_inv_left R (coordinateHopfAlgebra R) using 1

/-- The underlying scheme isomorphism from the additive group to affine one-space. -/
private noncomputable def groupSchemeAffineSpaceIsoLeft :
    (groupScheme R).X.left ≅
      𝔸(CoordinateIndex.{u}; Spec (CommRingCat.of R)) :=
  eqToIso (groupScheme_X_left R) ≪≫
    Scheme.Spec.mapIso (coordinateAlgEquiv R).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (CoordinateIndex.{u}) (CommRingCat.of R)).symm

private lemma groupSchemeAffineSpaceIsoLeft_over :
    (groupSchemeAffineSpaceIsoLeft R).hom ≫
        𝔸(CoordinateIndex.{u}; Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R) =
      (groupScheme R).X.hom := by
  rw [groupScheme_X_hom, groupSchemeAffineSpaceIsoLeft]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  rw [AffineSpace.SpecIso_inv_over]
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op, ← Spec.map_comp]
  congr 2
  ext r
  exact (coordinateAlgEquiv R).symm.commutes r

/-- The additive group scheme's underlying scheme is canonically affine one-space over `Spec R`.

This is an isomorphism in `Over (Spec R)`, not an isomorphism of Hopf algebras or group objects.
The polynomial presentation is used only as an algebra presentation. -/
noncomputable def groupSchemeAffineSpaceIso :
    (groupScheme R).X ≅
      (𝔸(CoordinateIndex.{u}; Spec (CommRingCat.of R))).asOver
        (Spec (CommRingCat.of R)) :=
  Over.isoMk (groupSchemeAffineSpaceIsoLeft R) (groupSchemeAffineSpaceIsoLeft_over R)

/-- The underlying scheme map of the affine-one-space identification is the contravariant
spectrum map from the rank-one polynomial presentation, followed by Mathlib's affine-space
spectrum isomorphism. -/
@[simp]
lemma groupSchemeAffineSpaceIso_hom_left :
    (groupSchemeAffineSpaceIso R).hom.left =
      (eqToIso (groupScheme_X_left R) ≪≫
        Scheme.Spec.mapIso
          (coordinateAlgEquiv R).symm.toRingEquiv.toCommRingCatIso.op ≪≫
        (AffineSpace.SpecIso (CoordinateIndex.{u}) (CommRingCat.of R)).symm).hom := by
  rfl

/-- The additive group scheme is affine. -/
instance isAffine_groupScheme : IsAffine (groupScheme R).X.left := by
  rw [groupScheme_X_left]
  exact AlgebraicGeometry.isAffine_Spec _

/-- The structural morphism of the additive group scheme is locally of finite presentation. -/
instance locallyOfFinitePresentation_groupScheme :
    LocallyOfFinitePresentation (groupScheme R).X.hom := by
  let : Algebra.FinitePresentation R (MvPolynomial (CoordinateIndex.{u}) R) := inferInstance
  let : Algebra.FinitePresentation R (SymmetricAlgebra R R) :=
    Algebra.FinitePresentation.equiv (coordinateAlgEquiv R).symm
  rw [groupScheme_X_hom]
  let : LocallyOfFinitePresentation (eqToHom (groupScheme_X_left R)) :=
    locallyOfFinitePresentation_of_isOpenImmersion _
  let : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R R)))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  exact locallyOfFinitePresentation_comp _ _

/-- The structural morphism of the additive group scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    LocallyOfFiniteType (groupScheme R).X.hom := inferInstance

section SchemePoints

variable {R} (A : Type u) [CommRing A] [Algebra R A]

/-- Mathlib's spectrum-points equivalence, with its target presented as the underlying object of
the additive group scheme. It sends an algebra point to its contravariant spectrum morphism.

The retyping is what makes the equivalence usable: `groupScheme` is not exposed outside this
module, so `AlgebraicGeometry.Spec.mapMulEquiv` cannot be applied to a point of `(groupScheme R).X`
downstream. -/
noncomputable def groupSchemePointMulEquiv :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
        (groupScheme R).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation
    (coordinateHopfAlgebra R) A (groupScheme_def R)

/-- The underlying map of the spectrum point associated to an algebra point. -/
@[simp]
lemma groupSchemePointMulEquiv_apply_left
    (f : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    (groupSchemePointMulEquiv A f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R).symm := by
  simpa only [groupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (coordinateHopfAlgebra R) A (groupScheme_def R)
        (groupScheme_X_left R) f

/-- The group of scheme-valued points of the additive group scheme is the additive group of the
value algebra.

The source consists of morphisms over `Spec R` from `Spec A` to the underlying object of
`groupScheme R`. It is written multiplicatively to match the group law on a hom-set into a group
object. -/
noncomputable def schemePointsMulEquiv :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R).X) ≃* Multiplicative A :=
  (groupSchemePointMulEquiv A).symm.trans
    (gaPointsMulEquiv (R := R) (A := A))

/-- A scheme-valued point corresponds to the value at the additive coordinate `ι(1)` of its
canonical algebra point. -/
@[simp]
lemma toAdd_schemePointsMulEquiv
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R).X) :
    Multiplicative.toAdd (schemePointsMulEquiv A p) =
      ((groupSchemePointMulEquiv A).symm p).ofConv
        (SymmetricAlgebra.ι R R 1) := by
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply]
  exact toAdd_gaPointsMulEquiv _

/-- Evaluating the scheme-points equivalence on a point presented by `groupSchemePointMulEquiv`
recovers the canonical algebra point. -/
@[simp]
theorem schemePointsMulEquiv_groupSchemePointMulEquiv
    (q : WithConv (coordinateHopfAlgebra R →ₐ[R] A)) :
    schemePointsMulEquiv A (groupSchemePointMulEquiv A q) =
      gaPointsMulEquiv (R := R) (A := A) q := by
  simp [schemePointsMulEquiv]

/-- Evaluating the scheme-points equivalence directly on a scheme morphism. -/
theorem schemePointsMulEquiv_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R).X) :
    schemePointsMulEquiv A p =
      gaPointsMulEquiv (R := R) (A := A)
        ((groupSchemePointMulEquiv A).symm p) := by
  unfold schemePointsMulEquiv
  rfl

/-- The inverse scheme-points equivalence sends an element of the value algebra to the spectrum
map induced by the corresponding symmetric-algebra point. -/
@[simp]
lemma schemePointsMulEquiv_symm_apply (a : Multiplicative A) :
    (schemePointsMulEquiv A).symm a =
      groupSchemePointMulEquiv A
        ((gaPointsMulEquiv (R := R) (A := A)).symm a) := by
  rfl

variable {B : Type u} [CommRing B] [Algebra R B]

/-- The scheme-valued point identification is covariantly natural in the value algebra. An
`R`-algebra map `A → B` becomes precomposition by the reversed spectrum map, and sends the
corresponding additive value `a` to its image in `B`. -/
theorem schemePointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R).X) :
    schemePointsMulEquiv B
        ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
            (Spec (CommRingCat.of R)) ≫ p) =
      Multiplicative.ofAdd
        (φ (Multiplicative.toAdd (schemePointsMulEquiv A p))) := by
  let q : WithConv (SymmetricAlgebra R R →ₐ[R] A) :=
    (groupSchemePointMulEquiv A).symm p
  have hpre :
      (groupSchemePointMulEquiv B).symm
          ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
            (Spec (CommRingCat.of R)) ≫ p) =
        HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R)
          (CommAlgCat.ofHom φ) q := by
    simpa only [q, groupSchemePointMulEquiv] using
      CommHopfAlgCat.mapMulEquivOfPresentation_mapValue
        (coordinateHopfAlgebra R) φ (groupScheme_def R) p
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply]
  rw [hpre, HopfAlgebra.mapPoints_apply, ← AlgHom.mapValue_apply]
  exact gaPointsMulEquiv_mapValue φ q

end SchemePoints

end AdditiveGroup

end TauCeti
