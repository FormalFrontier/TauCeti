/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic

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
`ULift.{u} (Multiplicative ℤ)`. The local character equivalence combines Mathlib's
`zpowersMulHom` with `MulEquiv.ulift`; public exponents and cocharacters remain expressed
using ordinary integers.

## Main declarations

* `TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv`: the typed comparison between
  scheme-valued points of `D(G)` and algebra points of `R[G]`.
* `TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_symm_apply_left`: the underlying
  spectrum map of the inverse comparison.
* `TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_mapValue` and
  `TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_groupSchemeMap`: its naturality in
  the value algebra and the character group.
* `TauCeti.DiagonalizableGroup.schemePointsMulEquiv`: scheme-valued points of `D(G)` are
  characters `G →* Aˣ`.
* `TauCeti.DiagonalizableGroup.schemePointsMulEquiv_eq_pointsMulEquiv_groupSchemePointsMulEquiv`:
  this character comparison factors through the convolution-point comparison.
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

/-- The underlying-object isomorphism induced by the named Hopf-spectrum presentation. -/
private noncomputable def groupSchemeIsoHopfSpec (G : FGCommGrpCat.{u}) :
    (groupScheme R G).X ≅
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (coordinateRing R G).obj)).X :=
  (Grp.forget _).mapIso (eqToIso (groupScheme_def R G))

/-- The underlying Hopf spectrum identified with the relative spectrum of its group algebra. -/
private noncomputable def hopfSpecIsoSpec (G : FGCommGrpCat.{u}) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op (coordinateRing R G).obj)).X ≅
      (Spec (CommRingCat.of (MonoidAlgebra R G))).asOver (Spec (CommRingCat.of R)) :=
  (Grp.forget _).mapIso
    (eqToIso (hopfSpec_obj_eq_asOver R (coordinateRing R G).obj))

/-- The composite identification of the named diagonalizable group with its relative spectrum. -/
private noncomputable def groupSchemeIsoSpec (G : FGCommGrpCat.{u}) :
    (groupScheme R G).X ≅
      (Spec (CommRingCat.of (MonoidAlgebra R G))).asOver (Spec (CommRingCat.of R)) :=
  groupSchemeIsoHopfSpec (R := R) G ≪≫ hopfSpecIsoSpec (R := R) G

private instance groupSchemeIsoSpec_isMonHom (G : FGCommGrpCat.{u}) :
    IsMonHom (groupSchemeIsoSpec (R := R) G).hom := by
  have h₁ : IsMonHom (groupSchemeIsoHopfSpec (R := R) G).hom := by
    unfold groupSchemeIsoHopfSpec
    rw [Functor.mapIso_hom, Grp.forget_map]
    infer_instance
  have h₂ : IsMonHom (hopfSpecIsoSpec (R := R) G).hom := by
    unfold hopfSpecIsoSpec
    rw [Functor.mapIso_hom, Grp.forget_map]
    infer_instance
  unfold groupSchemeIsoSpec
  exact @instIsMonHomComp _ _ _ _ _ _ _ _ _
    (groupSchemeIsoHopfSpec (R := R) G).hom
    (hopfSpecIsoSpec (R := R) G).hom h₁ h₂

/-- Scheme-valued points of `D(G)` are the convolution group of algebra maps out of its
coordinate ring. This typed wrapper keeps the defining identification of `groupScheme`
with `Spec R[G]` local to this module. -/
noncomputable def groupSchemePointsMulEquiv (G : FGCommGrpCat.{u}) :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) ≃* WithConv (MonoidAlgebra R G →ₐ[R] A) :=
  (Hom.mulEquivCongrRight (groupSchemeIsoSpec (R := R) G)
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)))).trans
      AlgebraicGeometry.Spec.mapMulEquiv.symm

/-- The underlying scheme morphism of an equality transport between group objects over
`Spec R` is the equality transport between their underlying schemes. -/
lemma eqToHom_hom_hom_left {G₁ G₂ : Grp (Over (Spec (CommRingCat.of R)))}
    (h : G₁ = G₂) :
    (eqToHom h).hom.hom.left =
      eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) h) := by
  subst h
  rfl

private lemma groupSchemeIsoHopfSpec_hom_left (G : FGCommGrpCat.{u}) :
    (groupSchemeIsoHopfSpec (R := R) G).hom.left =
      (eqToHom (groupScheme_def R G)).hom.hom.left :=
  rfl

private lemma hopfSpecIsoSpec_hom_left (G : FGCommGrpCat.{u}) :
    (hopfSpecIsoSpec (R := R) G).hom.left =
      (eqToHom (hopfSpec_obj_eq_asOver R (coordinateRing R G).obj)).hom.hom.left :=
  rfl

private lemma groupSchemeIsoSpec_hom_left (G : FGCommGrpCat.{u}) :
    (groupSchemeIsoSpec (R := R) G).hom.left = eqToHom (groupScheme_X_left R G) := by
  -- `groupSchemeIsoSpec` is the composite of `groupSchemeIsoHopfSpec` and `hopfSpecIsoSpec`,
  -- which are transport isomorphisms along `groupScheme_def` and `hopfSpec_obj_eq_asOver`.
  -- On the underlying scheme morphisms, both reduce to `eqToHom` on the scheme components.
  unfold groupSchemeIsoSpec
  rw [Iso.trans_hom, Over.comp_left]
  rw [groupSchemeIsoHopfSpec_hom_left, hopfSpecIsoSpec_hom_left]
  rw [eqToHom_hom_hom_left, eqToHom_hom_hom_left]
  rfl

/-- The underlying map of a scheme point under the typed comparison. -/
lemma groupSchemePointsMulEquiv_apply_left_comp (G : FGCommGrpCat.{u})
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    p.left ≫ eqToHom (groupScheme_X_left R G) =
      (AlgebraicGeometry.Spec.mapMulEquiv
        (groupSchemePointsMulEquiv (R := R) (A := A) G p)).left := by
  have hp := (AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply
    (p ≫ (groupSchemeIsoSpec (R := R) G).hom)).symm
  have hleft := congrArg Over.Hom.left hp
  rw [Over.comp_left, groupSchemeIsoSpec_hom_left] at hleft
  exact hleft

/-- The inverse typed point comparison is the spectrum morphism induced by the algebra point,
transported to the named diagonalizable group scheme. -/
lemma groupSchemePointsMulEquiv_symm_apply_left (G : FGCommGrpCat.{u})
    (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    ((groupSchemePointsMulEquiv (R := R) (A := A) G).symm f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R G).symm := by
  apply (cancel_mono (eqToHom (groupScheme_X_left R G))).1
  rw [groupSchemePointsMulEquiv_apply_left_comp, MulEquiv.apply_symm_apply,
    CommHopfAlgCat.mapMulEquiv_left]
  -- Normalize the `Over.left` source and the proof-irrelevant equality witnesses.
  change Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) =
    (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
      eqToHom (groupScheme_X_left R G).symm) ≫ eqToHom (groupScheme_X_left R G)
  simp

/-- The typed scheme-point comparison is natural in the value algebra. -/
theorem groupSchemePointsMulEquiv_mapValue (G : FGCommGrpCat.{u}) (phi : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    groupSchemePointsMulEquiv (R := R) (A := B) G
        ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) =
      AlgHom.mapValue (H := MonoidAlgebra R G) phi
        (groupSchemePointsMulEquiv (R := R) (A := A) G p) := by
  -- This crosses the local typed wrapper from the opaque `groupScheme` target to
  -- the public spectrum presentation of `D(G)`.
  change AlgebraicGeometry.Spec.mapMulEquiv.symm
      (((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver (Spec (CommRingCat.of R)) ≫
        p) ≫ (groupSchemeIsoSpec (R := R) G).hom) =
    HopfAlgebra.mapPoints (H := (coordinateRing R G).obj)
      (CommAlgCat.ofHom phi)
        (AlgebraicGeometry.Spec.mapMulEquiv.symm
          (p ≫ (groupSchemeIsoSpec (R := R) G).hom))
  rw [Category.assoc]
  apply AlgebraicGeometry.Spec.mapMulEquiv.injective
  have hcomp := AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply
    ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver (Spec (CommRingCat.of R)) ≫
      p ≫ (groupSchemeIsoSpec (R := R) G).hom)
  have hp := AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply
    (p ≫ (groupSchemeIsoSpec (R := R) G).hom)
  have hpcomp := congrArg
    (fun q => (Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
      (Spec (CommRingCat.of R)) ≫ q) hp.symm
  have hnat := (CommHopfAlgCat.mapMulEquiv_mapValue (coordinateRing R G).obj
    (CommAlgCat.ofHom phi)
    (AlgebraicGeometry.Spec.mapMulEquiv.symm
      (p ≫ (groupSchemeIsoSpec (R := R) G).hom))).symm
  exact hcomp.trans (hpcomp.trans hnat)

/-- The relative spectrum map induced contravariantly by a character-group homomorphism. -/
private noncomputable def hopfSpecMapAsOver {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    (Spec (CommRingCat.of (MonoidAlgebra R H))).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of (MonoidAlgebra R G))).asOver (Spec (CommRingCat.of R)) :=
  (hopfSpecIsoSpec (R := R) H).inv ≫
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (coordinateMap R f).hom.op).hom.hom ≫
    (hopfSpecIsoSpec (R := R) G).hom

private theorem groupSchemeIsoHopfSpec_naturality {G H : FGCommGrpCat.{u}}
    (f : G ⟶ H) :
    (groupSchemeMap R f).hom.hom ≫ (groupSchemeIsoHopfSpec (R := R) G).hom =
      (groupSchemeIsoHopfSpec (R := R) H).hom ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (coordinateMap R f).hom.op).hom.hom := by
  have h :
      groupSchemeMap R f ≫ eqToHom (groupScheme_def R G) =
        eqToHom (groupScheme_def R H) ≫
          (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
            (coordinateMap R f).hom.op := by
    rw [groupSchemeMap_def]
    simp [Category.assoc]
  exact congrArg (fun k => k.hom.hom) h

private theorem groupSchemeIsoSpec_naturality {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    (groupSchemeMap R f).hom.hom ≫ (groupSchemeIsoSpec (R := R) G).hom =
      (groupSchemeIsoSpec (R := R) H).hom ≫
        hopfSpecMapAsOver (R := R) f := by
  unfold groupSchemeIsoSpec hopfSpecMapAsOver
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
    groupSchemeIsoHopfSpec_naturality, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- The typed scheme-point comparison sends postcomposition by `groupSchemeMap f` to the
existing contravariant algebra-point map induced by the underlying homomorphism `f`. -/
theorem groupSchemePointsMulEquiv_groupSchemeMap {G H : FGCommGrpCat.{u}} (f : G ⟶ H)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R H).X) :
    groupSchemePointsMulEquiv (R := R) (A := A) G
        (p ≫ (groupSchemeMap R f).hom.hom) =
      pointsMap (R := R) (A := A) (FGCommGrpCat.toMonoidHom f)
        (groupSchemePointsMulEquiv (R := R) (A := A) H p) := by
  -- This crosses the local `groupSchemeMap` and typed-point wrappers to the existing
  -- coordinate-map action on convolution points; `coordinateMap` supplies the same map.
  change AlgebraicGeometry.Spec.mapMulEquiv.symm
      ((p ≫ (groupSchemeMap R f).hom.hom) ≫
        (groupSchemeIsoSpec (R := R) G).hom) =
    (CommHopfAlgCat.mapPointsFunctor (coordinateMap R f).hom).app
      (CommAlgCat.of R A)
        (AlgebraicGeometry.Spec.mapMulEquiv.symm
          (p ≫ (groupSchemeIsoSpec (R := R) H).hom))
  rw [Category.assoc, groupSchemeIsoSpec_naturality, ← Category.assoc]
  apply AlgebraicGeometry.Spec.mapMulEquiv.injective
  have hcomp := AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply
    ((p ≫ (groupSchemeIsoSpec (R := R) H).hom) ≫
      hopfSpecMapAsOver (R := R) f)
  have hp := AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply
    (p ≫ (groupSchemeIsoSpec (R := R) H).hom)
  have hpcomp := congrArg
    (fun q => q ≫ hopfSpecMapAsOver (R := R) f) hp.symm
  have hnat := (CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of R A)
    (coordinateMap R f).hom
    (AlgebraicGeometry.Spec.mapMulEquiv.symm
      (p ≫ (groupSchemeIsoSpec (R := R) H).hom))).symm
  exact hcomp.trans (hpcomp.trans hnat)

/-- Scheme-valued points of `D(G)` over `Spec R` are multiplicative characters `G →* Aˣ`.

The equivalence reverses the spectrum morphism into an algebra point through
`groupSchemePointsMulEquiv`, then applies the diagonalizable-group points equivalence. -/
noncomputable def schemePointsMulEquiv (G : FGCommGrpCat.{u}) :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) ≃* (G →* Aˣ) :=
  (groupSchemePointsMulEquiv (R := R) (A := A) G).trans pointsMulEquiv

/-- The diagonalizable-group scheme-points character is obtained by first passing to its
convolution point and then applying the algebra-valued points equivalence. -/
theorem schemePointsMulEquiv_eq_pointsMulEquiv_groupSchemePointsMulEquiv
    (G : FGCommGrpCat.{u})
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    schemePointsMulEquiv (R := R) (A := A) G p =
      pointsMulEquiv
        (groupSchemePointsMulEquiv (R := R) (A := A) G p) := by
  rw [schemePointsMulEquiv, MulEquiv.trans_apply]

/-- A scheme-valued point, viewed as a character, evaluates a group element on the
corresponding group-algebra basis monomial. -/
@[simp]
theorem schemePointsMulEquiv_apply_coe (G : FGCommGrpCat.{u})
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) (g : G) :
    (schemePointsMulEquiv (R := R) (A := A) G p g : A) =
      (groupSchemePointsMulEquiv (R := R) (A := A) G p).ofConv
        (MonoidAlgebra.single g 1) := by
  rw [schemePointsMulEquiv, MulEquiv.trans_apply, pointsMulEquiv_apply,
    charOfPoint_apply_coe]

/-- The inverse scheme-points equivalence is the spectrum morphism associated to the algebra
point extending a character. -/
theorem schemePointsMulEquiv_symm_apply
    (G : FGCommGrpCat.{u}) (chi : G →* Aˣ) :
    (schemePointsMulEquiv (R := R) (A := A) G).symm chi =
      (groupSchemePointsMulEquiv (R := R) (A := A) G).symm
        ((pointsMulEquiv (R := R) (A := A) (G := G)).symm chi) := by
  rw [schemePointsMulEquiv, MulEquiv.symm_trans_apply]

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
  rw [schemePointsMulEquiv, MulEquiv.trans_apply,
    groupSchemePointsMulEquiv_groupSchemeMap, pointsMulEquiv_pointsMap,
    schemePointsMulEquiv, MulEquiv.trans_apply]

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
  rw [schemePointsMulEquiv, MulEquiv.trans_apply,
    groupSchemePointsMulEquiv_mapValue, pointsMulEquiv_mapValue,
    schemePointsMulEquiv, MulEquiv.trans_apply]

/-! ### The multiplicative group and scheme-level characters -/

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
noncomputable def uliftZPowersMulEquiv (M : Type u) [CommGroup M] :
    M ≃* (ULift.{u} (Multiplicative ℤ) →* M) :=
  (zpowersMulHom M).trans MulEquiv.ulift.symm.monoidHomCongrLeft

/-- The character corresponding to `m` evaluates on a lifted integer `n` as `m ^ n`. -/
@[simp]
theorem uliftZPowersMulEquiv_apply (M : Type u) [CommGroup M]
    (m : M) (n : Multiplicative ℤ) :
    uliftZPowersMulEquiv M m (ULift.up n) = m ^ n.toAdd := by
  rw [uliftZPowersMulEquiv]
  rfl

/-- The inverse equivalence evaluates a lifted-integer character at the standard generator. -/
@[simp]
theorem uliftZPowersMulEquiv_symm_apply (M : Type u) [CommGroup M]
    (f : ULift.{u} (Multiplicative ℤ) →* M) :
    (uliftZPowersMulEquiv M).symm f = f (ULift.up (Multiplicative.ofAdd 1)) := by
  rw [uliftZPowersMulEquiv]
  rfl

/-- Scheme-valued points of the multiplicative group scheme are units of the value algebra,
read off on the lifted standard generator. -/
noncomputable def multiplicativeGroupSchemePointsMulEquiv :
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
  rw [multiplicativeGroupSchemePointsMulEquiv, MulEquiv.trans_apply,
    uliftZPowersMulEquiv_symm_apply]

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
noncomputable def characterGroupSchemeMap (G : FGCommGrpCat.{u}) (g : G) :
    groupScheme R G ⟶ multiplicativeGroupScheme R :=
  groupSchemeMap R (FGCommGrpCat.ofHom (uliftZPowersMulEquiv G g))

/-- A scheme-level character is the contravariant diagonalizable-group morphism induced by
the corresponding homomorphism from the lifted integer group. -/
theorem characterGroupSchemeMap_def (G : FGCommGrpCat.{u}) (g : G) :
    characterGroupSchemeMap (R := R) G g =
      groupSchemeMap R (FGCommGrpCat.ofHom (uliftZPowersMulEquiv G g)) := by
  rfl

/-- On scheme-valued points, the group-scheme character associated to `g` evaluates the
corresponding `G`-character at `g`. -/
@[simp high]
theorem multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap
    (G : FGCommGrpCat.{u}) (g : G)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R G).X) :
    multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A)
        (p ≫ (characterGroupSchemeMap (R := R) G g).hom.hom) =
      schemePointsMulEquiv (R := R) (A := A) G p g := by
  rw [multiplicativeGroupSchemePointsMulEquiv_apply, characterGroupSchemeMap_def,
    schemePointsMulEquiv_groupSchemeMap, MonoidHom.comp_apply,
    FGCommGrpCat.toMonoidHom_ofHom, uliftZPowersMulEquiv_apply, toAdd_ofAdd, zpow_one]

/-- A cocharacter `psi : G →* Multiplicative ℤ` gives a group-scheme morphism
`𝔾ₘ ⟶ D(G)`. The target character lattice is universe-lifted only at this scheme
boundary. -/
noncomputable def cocharacterGroupSchemeMap (G : FGCommGrpCat.{u})
    (psi : G →* Multiplicative ℤ) :
    multiplicativeGroupScheme R ⟶ groupScheme R G :=
  groupSchemeMap R <| FGCommGrpCat.ofHom <|
    (MulEquiv.ulift.symm : Multiplicative ℤ ≃*
      ULift.{u} (Multiplicative ℤ)).toMonoidHom.comp psi

/-- A scheme-level cocharacter is the contravariant diagonalizable-group morphism induced by
the universe-lifted cocharacter lattice homomorphism. -/
theorem cocharacterGroupSchemeMap_def (G : FGCommGrpCat.{u})
    (psi : G →* Multiplicative ℤ) :
    cocharacterGroupSchemeMap (R := R) G psi =
      groupSchemeMap R (FGCommGrpCat.ofHom
        ((MulEquiv.ulift.symm : Multiplicative ℤ ≃*
          ULift.{u} (Multiplicative ℤ)).toMonoidHom.comp psi)) := by
  rfl

/-- On scheme-valued points, a cocharacter raises the multiplicative-group unit to the
ordinary integer obtained by evaluating the cocharacter. -/
@[simp high]
theorem schemePointsMulEquiv_cocharacterGroupSchemeMap
    (G : FGCommGrpCat.{u}) (psi : G →* Multiplicative ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) (g : G) :
    schemePointsMulEquiv (R := R) (A := A) G
        (p ≫ (cocharacterGroupSchemeMap (R := R) G psi).hom.hom) g =
      multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p ^ (psi g).toAdd := by
  rw [cocharacterGroupSchemeMap_def, schemePointsMulEquiv_groupSchemeMap,
    MonoidHom.comp_apply, FGCommGrpCat.toMonoidHom_ofHom]
  exact schemePointsMulEquiv_multiplicativeCharacterGroup_apply p (psi g)

/-- The `n`-th power endomorphism of the multiplicative group scheme. Its character-lattice
map sends the lifted standard generator to the lift of `Multiplicative.ofAdd n`. -/
noncomputable def powEndGroupSchemeMap (n : ℤ) :
    multiplicativeGroupScheme R ⟶ multiplicativeGroupScheme R :=
  characterGroupSchemeMap (R := R) multiplicativeCharacterGroup
    (ULift.up (Multiplicative.ofAdd n))

/-- The scheme-level power endomorphism is the character associated to the lifted integer
exponent. -/
theorem powEndGroupSchemeMap_def (n : ℤ) :
    powEndGroupSchemeMap (R := R) n =
      characterGroupSchemeMap (R := R) multiplicativeCharacterGroup
        (ULift.up (Multiplicative.ofAdd n)) := by
  rfl

/-- The scheme-level `n`-th power endomorphism raises every scheme-valued point to the
ordinary integer power `n`. -/
@[simp high]
theorem multiplicativeGroupSchemePointsMulEquiv_powEndGroupSchemeMap (n : ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (multiplicativeGroupScheme R).X) :
    multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A)
        (p ≫ (powEndGroupSchemeMap (R := R) n).hom.hom) =
      multiplicativeGroupSchemePointsMulEquiv (R := R) (A := A) p ^ n := by
  rw [powEndGroupSchemeMap_def,
    multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap]
  simpa using schemePointsMulEquiv_multiplicativeCharacterGroup_apply
    (R := R) (A := A) p (Multiplicative.ofAdd n)

/-- Composing a cocharacter with a character is the multiplicative-group power map whose
exponent is their established character--cocharacter pairing. -/
theorem cocharacterGroupSchemeMap_comp_characterGroupSchemeMap
    (G : FGCommGrpCat.{u}) (g : G) (psi : G →* Multiplicative ℤ) :
    cocharacterGroupSchemeMap (R := R) G psi ≫ characterGroupSchemeMap (R := R) G g =
      powEndGroupSchemeMap (R := R) (pairing g psi) := by
  rw [cocharacterGroupSchemeMap_def, characterGroupSchemeMap_def,
    powEndGroupSchemeMap_def, characterGroupSchemeMap_def, ← groupSchemeMap_comp]
  congr 1
  apply FGCommGrpCat.hom_ext
  simp only [FGCommGrpCat.toMonoidHom_comp, FGCommGrpCat.toMonoidHom_ofHom]
  apply (uliftZPowersMulEquiv (ULift.{u} (Multiplicative ℤ))).symm.injective
  rw [uliftZPowersMulEquiv_symm_apply, uliftZPowersMulEquiv_symm_apply]
  simp only [MonoidHom.comp_apply, uliftZPowersMulEquiv_apply, toAdd_ofAdd,
    zpow_one, pairing_def, ofAdd_toAdd]
  rfl

end DiagonalizableGroup

end TauCeti
