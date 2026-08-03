/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme

/-!
# Scheme-valued points and morphisms of diagonalizable group schemes

For a commutative ring `R` and a finitely generated commutative group `G`, the
diagonalizable group scheme `D(G)` is represented by the group algebra `R[G]`. This file
synchronizes its group-scheme and functor-of-points presentations. A scheme-valued point
`Spec A ⟶ D(G)` over `Spec R` is identified multiplicatively with a character `G →* Aˣ`.
Under this identification, the group-scheme morphism induced contravariantly by `G ⟶ H`
acts by precomposition on characters, and the equivalence is natural in `A`.

The same bridge realizes characters, cocharacters, and integer power maps as actual
group-scheme morphisms. Their composite is the power map whose exponent is the established
character--cocharacter pairing. No classification of arbitrary group-scheme morphisms is
asserted; such a classification requires additional hypotheses on the base.

The scheme-facing constructions are same-universe because Mathlib's current `hopfSpec` and
`Spec.mapMulEquiv` interfaces are same-universe. Consequently the character group used for
`𝔾ₘ` over `R : Type u` is the canonical same-universe copy
`ULift.{u} (Multiplicative ℤ)`. Mathlib's `uliftZPowersHom` identifies its characters with
units, while public exponents and cocharacters remain expressed using ordinary integers.

## Main declarations

* `TauCeti.DiagonalizableGroup.schemePointsMulEquiv`: scheme-valued points of `D(G)` are
  characters `G →* Aˣ`.
* `TauCeti.DiagonalizableGroup.schemePointsMulEquiv_mapValue`: this identification is natural
  in the value algebra.
* `TauCeti.DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap`: a diagonalizable
  group-scheme morphism acts on points by precomposition on characters.
* `TauCeti.DiagonalizableGroup.multiplicativeGroupScheme`: the same-universe presentation of
  `𝔾ₘ`.
* `TauCeti.DiagonalizableGroup.characterGroupSchemeMap` and
  `TauCeti.DiagonalizableGroup.cocharacterGroupSchemeMap`: scheme-level characters and
  cocharacters.
* `TauCeti.DiagonalizableGroup.powEndGroupSchemeMap`: the scheme-level integer power map of
  `𝔾ₘ`.
* `TauCeti.DiagonalizableGroup.cocharacterGroupSchemeMap_comp_characterGroupSchemeMap`: the
  character--cocharacter pairing as an equality of group-scheme morphisms.

## References

Milne, *Algebraic Groups*, Definition 12.7 and Theorems 12.8--12.9, describes the
contravariant diagonalizable-group construction. The scheme-points bridge combines Mathlib's
`AlgebraicGeometry.Spec.mapMulEquiv` with Tau Ceti's
`DiagonalizableGroup.pointsMulEquiv`, `CommHopfAlgCat.mapMulEquiv_mapValue`, and
`CommHopfAlgCat.mapMulEquiv_mapDomain`.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace DiagonalizableGroup

open AlgebraicGeometry

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Transport scheme-valued points of the packaged `groupScheme` wrapper to the canonical
generic `hopfSpec` presentation. The transport is multiplicative because the canonical
presentation is an isomorphism of group objects. -/
@[expose] noncomputable def schemePointPresentationMulEquiv (G : FGCommGrpCat.{u}) :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) ≃*
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (coordinateRing R G).obj)).X) where
  toFun p := p ≫ (groupSchemeIsoHopfSpec R G).hom.hom.hom
  invFun p := p ≫ (groupSchemeIsoHopfSpec R G).inv.hom.hom
  left_inv p := by
    dsimp
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
  right_inv p := by
    dsimp
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  map_mul' p q := by
    rw [MonObj.mul_comp]

/-- The presentation equivalence postcomposes a point by the canonical group-scheme
isomorphism to `hopfSpec`. -/
theorem schemePointPresentationMulEquiv_apply (G : FGCommGrpCat.{u})
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    schemePointPresentationMulEquiv (R := R) (A := A) G p =
      p ≫ (groupSchemeIsoHopfSpec R G).hom.hom.hom :=
  rfl

/-- Scheme-valued points of `D(G)` over `Spec R` are multiplicative characters `G →* Aˣ`.

The equivalence transports the packaged group scheme to its generic Hopf spectrum, reverses
the spectrum morphism into an algebra point through `Spec.mapMulEquiv`, then applies the
diagonalizable-group points equivalence. -/
@[expose] noncomputable def schemePointsMulEquiv (G : FGCommGrpCat.{u}) :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) ≃* (G →* Aˣ) :=
  (schemePointPresentationMulEquiv (R := R) (A := A) G).trans <|
    AlgebraicGeometry.Spec.mapMulEquiv.symm.trans pointsMulEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A scheme-valued point, viewed as a character, evaluates a group element on the
corresponding group-algebra basis monomial. -/
@[simp]
theorem schemePointsMulEquiv_apply_coe (G : FGCommGrpCat.{u})
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) (g : G) :
    (schemePointsMulEquiv (R := R) (A := A) G p g : A) =
      (AlgebraicGeometry.Spec.mapMulEquiv.symm
        (schemePointPresentationMulEquiv (R := R) (A := A) G p)).ofConv
          (MonoidAlgebra.single g 1) := by
  change (pointsMulEquiv
    (AlgebraicGeometry.Spec.mapMulEquiv.symm
      (schemePointPresentationMulEquiv (R := R) (A := A) G p)) g : A) = _
  rw [pointsMulEquiv_apply, charOfPoint_apply_coe]
  rfl

/-- The inverse scheme-points equivalence is the spectrum morphism associated to the algebra
point extending a character, transported back to the packaged group scheme. -/
theorem schemePointPresentationMulEquiv_symm_schemePointsMulEquiv_symm_apply
    (G : FGCommGrpCat.{u}) (chi : G →* Aˣ) :
    schemePointPresentationMulEquiv (R := R) (A := A) G
        ((schemePointsMulEquiv (R := R) (A := A) G).symm chi) =
      AlgebraicGeometry.Spec.mapMulEquiv
        ((pointsMulEquiv (R := R) (A := A) (G := G)).symm chi) := by
  change schemePointPresentationMulEquiv (R := R) (A := A) G
      ((schemePointPresentationMulEquiv (R := R) (A := A) G).symm
        (AlgebraicGeometry.Spec.mapMulEquiv
          ((pointsMulEquiv (R := R) (A := A) (G := G)).symm chi))) = _
  exact (schemePointPresentationMulEquiv (R := R) (A := A) G).apply_symm_apply _

private theorem pointsMap_eq_mapPointsFunctor_app
    {G H : FGCommGrpCat.{u}} (f : G ⟶ H)
    (p : WithConv (MonoidAlgebra R H →ₐ[R] A)) :
    pointsMap (R := R) (A := A) (FGCommGrpCat.toMonoidHom f) p =
      (CommHopfAlgCat.mapPointsFunctor (coordinateMap R f).hom).app
        (CommAlgCat.of R A) p := by
  rfl

private theorem mapMulEquiv_pointsMap
    {G H : FGCommGrpCat.{u}} (f : G ⟶ H)
    (p : WithConv (MonoidAlgebra R H →ₐ[R] A)) :
    AlgebraicGeometry.Spec.mapMulEquiv
        (pointsMap (R := R) (A := A) (FGCommGrpCat.toMonoidHom f) p) =
      AlgebraicGeometry.Spec.mapMulEquiv p ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (coordinateMap R f).hom.op).hom.hom := by
  rw [pointsMap_eq_mapPointsFunctor_app]
  exact CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of R A)
    (coordinateMap R f).hom p

private theorem groupSchemeMap_presentation
    {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    (groupSchemeMap R f).hom.hom ≫
        (groupSchemeIsoHopfSpec R G).hom.hom.hom =
      (groupSchemeIsoHopfSpec R H).hom.hom.hom ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (coordinateMap R f).hom.op).hom.hom := by
  exact congrArg (fun k => k.hom.hom)
    (groupSchemeMap_comp_groupSchemeIsoHopfSpec_hom R f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The scheme-points equivalence intertwines `groupSchemeMap f` with precomposition by the
underlying homomorphism `f` on characters. -/
theorem schemePointsMulEquiv_groupSchemeMap
    {G H : FGCommGrpCat.{u}} (f : G ⟶ H)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R H).X) :
    schemePointsMulEquiv (R := R) (A := A) G
        (p ≫ (groupSchemeMap R f).hom.hom) =
      (schemePointsMulEquiv (R := R) (A := A) H p).comp
        (FGCommGrpCat.toMonoidHom f) := by
  change pointsMulEquiv
      (AlgebraicGeometry.Spec.mapMulEquiv.symm
        ((p ≫ (groupSchemeMap R f).hom.hom) ≫
          (groupSchemeIsoHopfSpec R G).hom.hom.hom)) =
    (pointsMulEquiv
      (AlgebraicGeometry.Spec.mapMulEquiv.symm
        (p ≫ (groupSchemeIsoHopfSpec R H).hom.hom.hom))).comp
      (FGCommGrpCat.toMonoidHom f)
  rw [← pointsMulEquiv_pointsMap]
  congr 1
  apply AlgebraicGeometry.Spec.mapMulEquiv.injective
  calc
    _ = (p ≫ (groupSchemeMap R f).hom.hom) ≫
        (groupSchemeIsoHopfSpec R G).hom.hom.hom :=
      AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply _
    _ = (p ≫ (groupSchemeIsoHopfSpec R H).hom.hom.hom) ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (coordinateMap R f).hom.op).hom.hom := by
      simpa only [Category.assoc] using congrArg (fun k => p ≫ k)
        (groupSchemeMap_presentation (R := R) f)
    _ = AlgebraicGeometry.Spec.mapMulEquiv
          (AlgebraicGeometry.Spec.mapMulEquiv.symm
            (p ≫ (groupSchemeIsoHopfSpec R H).hom.hom.hom)) ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (coordinateMap R f).hom.op).hom.hom := by
      exact congrArg (fun q => q ≫
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
            (coordinateMap R f).hom.op).hom.hom)
        (AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply _).symm
    _ = AlgebraicGeometry.Spec.mapMulEquiv
        (pointsMap (R := R) (A := A) (FGCommGrpCat.toMonoidHom f)
          (AlgebraicGeometry.Spec.mapMulEquiv.symm
            (p ≫ (groupSchemeIsoHopfSpec R H).hom.hom.hom))) := by
      exact (mapMulEquiv_pointsMap (R := R) (A := A) f _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The scheme-points equivalence is natural in the value algebra. For `phi : A →ₐ[R] B`,
precomposing by `Spec B ⟶ Spec A` applies `phi` to the values of the corresponding
character. -/
theorem schemePointsMulEquiv_mapValue (G : FGCommGrpCat.{u}) (phi : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    schemePointsMulEquiv (R := R) (A := B) G
        ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) =
      (Units.map phi.toMonoidHom).comp
        (schemePointsMulEquiv (R := R) (A := A) G p) := by
  change pointsMulEquiv
      (AlgebraicGeometry.Spec.mapMulEquiv.symm
        (((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) ≫
            (groupSchemeIsoHopfSpec R G).hom.hom.hom)) =
    (Units.map phi.toMonoidHom).comp
      (pointsMulEquiv
        (AlgebraicGeometry.Spec.mapMulEquiv.symm
          (p ≫ (groupSchemeIsoHopfSpec R G).hom.hom.hom)))
  rw [← pointsMulEquiv_mapValue]
  congr 1
  apply AlgebraicGeometry.Spec.mapMulEquiv.injective
  calc
    _ = ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
        (Spec (CommRingCat.of R)) ≫ p) ≫
          (groupSchemeIsoHopfSpec R G).hom.hom.hom :=
      AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply _
    _ = (Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
        (Spec (CommRingCat.of R)) ≫
          (p ≫ (groupSchemeIsoHopfSpec R G).hom.hom.hom) := by
      rw [Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
        (Spec (CommRingCat.of R)) ≫
          AlgebraicGeometry.Spec.mapMulEquiv
            (AlgebraicGeometry.Spec.mapMulEquiv.symm
              (p ≫ (groupSchemeIsoHopfSpec R G).hom.hom.hom)) := by
      exact congrArg
        (fun q => (Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ q)
        (AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply _).symm
    _ = AlgebraicGeometry.Spec.mapMulEquiv
        (HopfAlgebra.mapPoints (H := (coordinateRing R G).obj)
          (CommAlgCat.ofHom phi)
          (AlgebraicGeometry.Spec.mapMulEquiv.symm
            (p ≫ (groupSchemeIsoHopfSpec R G).hom.hom.hom))) := by
      exact (CommHopfAlgCat.mapMulEquiv_mapValue
        (coordinateRing R G).obj (CommAlgCat.ofHom phi) _).symm

/-! ### The multiplicative group and scheme-level characters -/

/-- The same-universe copy of `Multiplicative ℤ` is finitely generated. -/
instance instFGULiftMultiplicativeInt :
    Group.FG (ULift.{u} (Multiplicative ℤ)) := by
  exact Group.fg_of_surjective
    (f := (MulEquiv.ulift.symm : Multiplicative ℤ ≃*
      ULift.{u} (Multiplicative ℤ)).toMonoidHom) MulEquiv.ulift.symm.surjective

/-- The character group of the multiplicative group scheme, in the universe of the base.
It is the canonical universe lift of `Multiplicative ℤ`. -/
noncomputable abbrev multiplicativeCharacterGroup : FGCommGrpCat.{u} :=
  FGCommGrpCat.of (ULift.{u} (Multiplicative ℤ))

/-- The multiplicative group scheme, presented in the base universe as
`D(ULift (Multiplicative ℤ))`. -/
noncomputable abbrev multiplicativeGroupScheme (R : Type u) [CommRing R] :
    Grp (Over (Spec (CommRingCat.of R))) :=
  groupScheme R multiplicativeCharacterGroup

/-- Evaluation at the lifted standard generator identifies characters of
`ULift (Multiplicative ℤ)` with elements of a commutative group. -/
@[expose] noncomputable def uliftZPowersMulEquiv (M : Type u) [CommGroup M] :
    M ≃* (ULift.{u} (Multiplicative ℤ) →* M) :=
  (zpowersMulHom M).trans MulEquiv.ulift.symm.monoidHomCongrLeft

/-- The character corresponding to `m` evaluates on a lifted integer `n` as `m ^ n`. -/
@[simp]
theorem uliftZPowersMulEquiv_apply (M : Type u) [CommGroup M]
    (m : M) (n : Multiplicative ℤ) :
    uliftZPowersMulEquiv M m (ULift.up n) = m ^ n.toAdd :=
  rfl

/-- The inverse equivalence evaluates a lifted-integer character at the standard generator. -/
@[simp]
theorem uliftZPowersMulEquiv_symm_apply (M : Type u) [CommGroup M]
    (f : ULift.{u} (Multiplicative ℤ) →* M) :
    (uliftZPowersMulEquiv M).symm f = f (ULift.up (Multiplicative.ofAdd 1)) :=
  rfl

/-- Scheme-valued points of the multiplicative group scheme are units of the value algebra,
read off on the lifted standard generator. -/
@[expose] noncomputable def multiplicativeGroupSchemePointsMulEquiv :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) ≃* Aˣ :=
  (schemePointsMulEquiv (R := R) (A := A) multiplicativeCharacterGroup).trans
    (uliftZPowersMulEquiv Aˣ).symm

/-- The scheme-points equivalence for `𝔾ₘ` evaluates the corresponding character on
the lifted generator `Multiplicative.ofAdd 1`. -/
@[simp]
theorem multiplicativeGroupSchemePointsMulEquiv_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) :
    multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p =
      schemePointsMulEquiv (R := R) (A := A) multiplicativeCharacterGroup p
        (ULift.up (Multiplicative.ofAdd 1)) := by
  change (uliftZPowersMulEquiv Aˣ).symm
      (schemePointsMulEquiv (R := R) (A := A) multiplicativeCharacterGroup p) = _
  exact uliftZPowersMulEquiv_symm_apply Aˣ _

/-- The multiplicative-group scheme-points equivalence is natural in the value algebra. -/
theorem multiplicativeGroupSchemePointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) :
    multiplicativeGroupSchemePointsMulEquiv (R := R) (A := B)
        ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) =
      Units.map phi.toMonoidHom
        (multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p) := by
  rw [multiplicativeGroupSchemePointsMulEquiv_apply,
    multiplicativeGroupSchemePointsMulEquiv_apply,
    schemePointsMulEquiv_mapValue, MonoidHom.comp_apply]

/-- A character of the lifted integer group evaluates at `ULift.up n` as the corresponding
unit raised to the ordinary integer exponent `n.toAdd`. -/
theorem schemePointsMulEquiv_multiplicativeCharacterGroup_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) (n : Multiplicative ℤ) :
    schemePointsMulEquiv (R := R) (A := A) multiplicativeCharacterGroup p (ULift.up n) =
      multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p ^ n.toAdd := by
  let f := schemePointsMulEquiv (R := R) (A := A) multiplicativeCharacterGroup p
  calc
    f (ULift.up n) = uliftZPowersMulEquiv Aˣ
        ((uliftZPowersMulEquiv Aˣ).symm f) (ULift.up n) := by
      exact congrArg (fun q : ULift.{u} (Multiplicative ℤ) →* Aˣ => q (ULift.up n))
        ((uliftZPowersMulEquiv Aˣ).apply_symm_apply f).symm
    _ = (uliftZPowersMulEquiv Aˣ).symm f ^ n.toAdd := by
      rw [uliftZPowersMulEquiv_apply]
    _ = f (ULift.up (Multiplicative.ofAdd 1)) ^ n.toAdd := by
      rw [uliftZPowersMulEquiv_symm_apply]
    _ = _ := by
      rw [multiplicativeGroupSchemePointsMulEquiv_apply]

/-! ### Scheme-level characters, cocharacters, and power maps -/

/-- A group element `g : G`, viewed as a character of `D(G)`, gives the group-scheme
morphism `D(G) ⟶ 𝔾ₘ` induced contravariantly by the homomorphism from the lifted
integer group that sends its standard generator to `g`. -/
@[expose] noncomputable def characterGroupSchemeMap (G : FGCommGrpCat.{u}) (g : G) :
    groupScheme R G ⟶ multiplicativeGroupScheme R :=
  groupSchemeMap R (FGCommGrpCat.ofHom (uliftZPowersMulEquiv G g))

/-- On scheme-valued points, the group-scheme character associated to `g` evaluates the
corresponding `G`-character at `g`. -/
theorem multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap
    (G : FGCommGrpCat.{u}) (g : G)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A)
        (p ≫ (characterGroupSchemeMap (R := R) G g).hom.hom) =
      schemePointsMulEquiv (R := R) (A := A) G p g := by
  rw [multiplicativeGroupSchemePointsMulEquiv_apply, characterGroupSchemeMap,
    schemePointsMulEquiv_groupSchemeMap, MonoidHom.comp_apply]
  change schemePointsMulEquiv (R := R) (A := A) G p
      (uliftZPowersMulEquiv G g (ULift.up (Multiplicative.ofAdd 1))) = _
  rw [uliftZPowersMulEquiv_apply, toAdd_ofAdd, zpow_one]

/-- A cocharacter `psi : G →* Multiplicative ℤ` gives a group-scheme morphism
`𝔾ₘ ⟶ D(G)`. The target character lattice is universe-lifted only at this scheme
boundary. -/
@[expose] noncomputable def cocharacterGroupSchemeMap (G : FGCommGrpCat.{u})
    (psi : G →* Multiplicative ℤ) :
    multiplicativeGroupScheme R ⟶ groupScheme R G :=
  groupSchemeMap R <| FGCommGrpCat.ofHom <|
    (MulEquiv.ulift.symm : Multiplicative ℤ ≃*
      ULift.{u} (Multiplicative ℤ)).toMonoidHom.comp psi

/-- On scheme-valued points, a cocharacter raises the multiplicative-group unit to the
ordinary integer obtained by evaluating the cocharacter. -/
theorem schemePointsMulEquiv_cocharacterGroupSchemeMap
    (G : FGCommGrpCat.{u}) (psi : G →* Multiplicative ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) (g : G) :
    schemePointsMulEquiv (R := R) (A := A) G
        (p ≫ (cocharacterGroupSchemeMap (R := R) G psi).hom.hom) g =
      multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p ^ (psi g).toAdd := by
  rw [cocharacterGroupSchemeMap, schemePointsMulEquiv_groupSchemeMap,
    MonoidHom.comp_apply]
  change schemePointsMulEquiv (R := R) (A := A) multiplicativeCharacterGroup p
      (ULift.up (psi g)) = _
  exact schemePointsMulEquiv_multiplicativeCharacterGroup_apply p (psi g)

/-- The `n`-th power endomorphism of the multiplicative group scheme. Its character-lattice
map sends the lifted standard generator to the lift of `Multiplicative.ofAdd n`. -/
@[expose] noncomputable def powEndGroupSchemeMap (n : ℤ) :
    multiplicativeGroupScheme R ⟶ multiplicativeGroupScheme R :=
  characterGroupSchemeMap (R := R) multiplicativeCharacterGroup
    (ULift.up (Multiplicative.ofAdd n))

/-- The scheme-level `n`-th power endomorphism raises every scheme-valued point to the
ordinary integer power `n`. -/
theorem multiplicativeGroupSchemePointsMulEquiv_powEndGroupSchemeMap (n : ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) :
    multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A)
        (p ≫ (powEndGroupSchemeMap (R := R) n).hom.hom) =
      multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p ^ n := by
  rw [powEndGroupSchemeMap,
    multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap]
  simpa using schemePointsMulEquiv_multiplicativeCharacterGroup_apply
    (R := R) (A := A) p (Multiplicative.ofAdd n)

/-- Composing a cocharacter with a character is the multiplicative-group power map whose
exponent is their established character--cocharacter pairing. -/
theorem cocharacterGroupSchemeMap_comp_characterGroupSchemeMap
    (G : FGCommGrpCat.{u}) (g : G) (psi : G →* Multiplicative ℤ) :
    cocharacterGroupSchemeMap (R := R) G psi ≫ characterGroupSchemeMap (R := R) G g =
      powEndGroupSchemeMap (R := R) (pairing g psi) := by
  rw [cocharacterGroupSchemeMap, characterGroupSchemeMap, powEndGroupSchemeMap,
    characterGroupSchemeMap, ← groupSchemeMap_comp]
  congr 1
  apply FGCommGrpCat.hom_ext
  change ((MulEquiv.ulift.symm : Multiplicative ℤ ≃*
      ULift.{u} (Multiplicative ℤ)).toMonoidHom.comp psi).comp
        (uliftZPowersMulEquiv G g) =
    uliftZPowersMulEquiv (ULift.{u} (Multiplicative ℤ))
      (ULift.up (Multiplicative.ofAdd (pairing g psi)))
  apply (uliftZPowersMulEquiv (ULift.{u} (Multiplicative ℤ))).symm.injective
  rw [uliftZPowersMulEquiv_symm_apply, uliftZPowersMulEquiv_symm_apply]
  change ULift.up (psi (g ^ (1 : ℤ))) =
    (ULift.up (Multiplicative.ofAdd (pairing g psi))) ^ (1 : ℤ)
  simp only [zpow_one, pairing_def, ofAdd_toAdd]

end DiagonalizableGroup

end TauCeti
