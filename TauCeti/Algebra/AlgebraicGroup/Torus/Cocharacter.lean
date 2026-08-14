/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Cocharacter lattices of tori

For a torus `T` over a field `k`, a geometric cocharacter is a group-scheme morphism
`G_m → T` after extension to the chosen algebraic closure. Contravariantly, it is a morphism
of coordinate Hopf algebras

```text
O(T_bar) → O(G_m).
```

The canonical group-like evaluation equivalence reconstructs the geometric fibre of a torus from
its characters. Full faithfulness of the diagonalizable-group coordinate-ring functor then
identifies these geometric morphisms with the integral dual of the geometric character lattice.
This comparison, rather than the definition of cocharacters, supplies the perfect pairing. The dual
description is specific to tori: a semisimple group can have trivial character group and nontrivial
cocharacters.

The absolute Galois action on `X_*(T)` is the contragredient of its action on `X*(T)`. The
evaluation pairing is invariant under the diagonal action and is perfect over `ℤ`. For the
standard split torus, the dual comparison is related to the existing group of genuine
cocharacters, and the Galois representation is shown to be trivial.

## Main declarations

* `TauCeti.TorusCommHopfAlgCat.cocharacterLattice`: geometric group-scheme morphisms
  `G_m → T_bar`.
* `TauCeti.TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual`: the canonical comparison
  between geometric cocharacters and the integral character dual.
* `TauCeti.TorusCommHopfAlgCat.geometricCharacterGroupSchemeMap`: the group-scheme morphism
  attached to a geometric character.
* `TauCeti.TorusCommHopfAlgCat.cocharacterGaloisRepresentation`: its contragredient absolute
  Galois representation.
* `TauCeti.TorusCommHopfAlgCat.characterCocharacterPairing`: the evaluation pairing between
  characters and cocharacters, intrinsically characterized by composition of their group-scheme
  morphisms and equipped with a perfect-pairing instance.
* `TauCeti.TorusCommHopfAlgCat.cocharacterLattice_module_free` and
  `TauCeti.TorusCommHopfAlgCat.cocharacterLattice_module_finite`: the cocharacter lattice is
  finite free over `ℤ`.
* `TauCeti.SplitTorus.cocharacterLatticeEquiv`: for a standard split torus, the geometric
  morphism lattice is its existing explicit group of cocharacters.

## Roadmap

This completes the lattice-and-pairing part of Layer 4, "Tori: split and non-split; the
character lattice `X*(T)` and cocharacter lattice `X_*(T)` with their perfect pairing", in the
reductive-groups roadmap. Continuity of the Galois actions and the descent classification of
non-split tori remain separate steps.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric character group of a torus, bundled as a finitely generated commutative
group for use with the diagonalizable coordinate-ring functor. -/
private noncomputable def geometricCharacterFG (T : TorusCommHopfAlgCat k) :
    FGCommGrpCat.{u} := by
  let _ : Group.FG (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) :=
    CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType T.obj
      (torusCommHopfAlgProperty.multiplicativeType k T.obj T.property)
  exact FGCommGrpCat.of (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)

/-- The bundled geometric character group has the intrinsic geometric characters as its
underlying group. -/
private noncomputable def geometricCharacterFGEquiv (T : TorusCommHopfAlgCat k) :
    CommHopfAlgCat.geometricCharacterGroup T.obj.obj ≃* geometricCharacterFG T :=
  MulEquiv.refl _

private theorem baseChange_groupLike_span_eq_top (T : TorusCommHopfAlgCat k) :
    Submodule.span (AlgebraicClosure k)
        (Set.range (_root_.GroupLike.val (R := AlgebraicClosure k)
          (A := FiniteTypeCommHopfAlgCat.baseChange
            (K := AlgebraicClosure k) T.obj))) = ⊤ := by
  rw [← Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  exact (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).1 <|
    (multiplicativeTypeCommHopfAlgProperty_iff k T.obj).1
      (torusCommHopfAlgProperty.multiplicativeType k T.obj T.property)

/-- The canonical reconstruction of the geometric coordinate algebra of a torus from its
geometric characters. -/
private noncomputable def geometricCoordinateIso (T : TorusCommHopfAlgCat k) :
    DiagonalizableGroup.coordinateRing (AlgebraicClosure k) (geometricCharacterFG T) ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj :=
  ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    TauCeti.GroupLike.evaluationBialgEquiv (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)
      (baseChange_groupLike_span_eq_top T)

@[simp]
private theorem geometricCoordinateIso_hom_single (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.geometricCharacterGroup T.obj.obj) :
    (geometricCoordinateIso T).hom.hom
        (_root_.MonoidAlgebra.single (geometricCharacterFGEquiv T x) 1) = x.val := by
  change TauCeti.GroupLike.evaluationBialgEquiv (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)
        (baseChange_groupLike_span_eq_top T)
          (_root_.MonoidAlgebra.single x 1) = x.val
  rw [TauCeti.GroupLike.evaluationBialgEquiv_apply,
    TauCeti.GroupLike.evaluationBialgHom_single, one_smul]

@[simp]
private theorem geometricCoordinateIso_hom_single' (T : TorusCommHopfAlgCat k)
    (x : geometricCharacterFG T) :
    (geometricCoordinateIso T).hom.hom (_root_.MonoidAlgebra.single x 1) =
      ((geometricCharacterFGEquiv T).symm x).val := by
  simpa using geometricCoordinateIso_hom_single T ((geometricCharacterFGEquiv T).symm x)

/-- The coordinate Hopf-algebra morphism of a geometric character. It sends the standard
generator of the multiplicative group's coordinate algebra to the character's underlying
group-like element. -/
private noncomputable def geometricCharacterCoordinateMap (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
        DiagonalizableGroup.multiplicativeCharacterGroup ⟶
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj :=
  FiniteTypeCommHopfAlgCat.ofHom <|
    (TauCeti.GroupLike.evaluationBialgHom (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)).comp <|
        _root_.MonoidAlgebra.mapDomainBialgHom (AlgebraicClosure k)
          (DiagonalizableGroup.uliftZPowersMulEquiv
            (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) x.toMul)

private theorem coordinateMap_comp_geometricCoordinateIso
    (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    DiagonalizableGroup.coordinateMap (AlgebraicClosure k)
        (FGCommGrpCat.ofHom
          (DiagonalizableGroup.uliftZPowersMulEquiv (geometricCharacterFG T)
            (geometricCharacterFGEquiv T x.toMul))) ≫
      (geometricCoordinateIso T).hom = geometricCharacterCoordinateMap T x := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  ext z
  rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp]
  change (geometricCoordinateIso T).hom.hom
      ((DiagonalizableGroup.coordinateMap (AlgebraicClosure k)
        (FGCommGrpCat.ofHom
          (DiagonalizableGroup.uliftZPowersMulEquiv (geometricCharacterFG T)
            (geometricCharacterFGEquiv T x.toMul)))).hom.hom
              (_root_.MonoidAlgebra.single z 1)) =
    ((TauCeti.GroupLike.evaluationBialgHom (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)).comp
        (_root_.MonoidAlgebra.mapDomainBialgHom (AlgebraicClosure k)
          (DiagonalizableGroup.uliftZPowersMulEquiv
            (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) x.toMul)))
              (_root_.MonoidAlgebra.single z 1)
  rw [DiagonalizableGroup.coordinateMap_single, geometricCoordinateIso_hom_single',
    BialgHom.comp_apply, _root_.MonoidAlgebra.mapDomainBialgHom_single,
    TauCeti.GroupLike.evaluationBialgHom_single, one_smul]
  rw [geometricCharacterFGEquiv]
  rfl

/-- The geometric fibre of a torus as an affine group scheme over the chosen algebraic closure. -/
noncomputable abbrev geometricFiberGroupScheme (T : TorusCommHopfAlgCat k) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).obj <|
    Opposite.op (FiniteTypeCommHopfAlgCat.baseChange
      (K := AlgebraicClosure k) T.obj).obj

/-- The canonical coordinate reconstruction, viewed as an isomorphism from the geometric fibre to
the diagonalizable group scheme on its intrinsic character group. -/
private noncomputable def geometricFiberGroupSchemeIso (T : TorusCommHopfAlgCat k) :
    geometricFiberGroupScheme T ≅
      (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).obj
        (Opposite.op
          (DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
            (geometricCharacterFG T)).obj) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).mapIso
    (((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (_root_.CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso
        (geometricCoordinateIso T)).op)

/-- The geometric cocharacter lattice of a torus: group-scheme morphisms `G_m → T_bar` over
the chosen algebraic closure. -/
abbrev cocharacterLattice (T : TorusCommHopfAlgCat k) :=
  DiagonalizableGroup.multiplicativeGroupScheme (AlgebraicClosure k) ⟶
    geometricFiberGroupScheme T

/-- A geometric character, as the corresponding group-scheme morphism from the geometric fibre
of the torus to the multiplicative group. -/
noncomputable def geometricCharacterGroupSchemeMap (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    geometricFiberGroupScheme T ⟶
      DiagonalizableGroup.multiplicativeGroupScheme (AlgebraicClosure k) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).map
      (geometricCharacterCoordinateMap T x).hom.op ≫
    eqToHom (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
      DiagonalizableGroup.multiplicativeCharacterGroup).symm

/-- The intrinsic character map agrees with the diagonalizable-group character map after the
canonical coordinate reconstruction. -/
private theorem geometricCharacterGroupSchemeMap_eq (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    geometricCharacterGroupSchemeMap T x =
      (geometricFiberGroupSchemeIso T).hom ≫
        eqToHom (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
          (geometricCharacterFG T)).symm ≫
          DiagonalizableGroup.characterGroupSchemeMap (geometricCharacterFG T)
            (geometricCharacterFGEquiv T x.toMul) := by
  let hG := DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
    (geometricCharacterFG T)
  let hZ := DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
    DiagonalizableGroup.multiplicativeCharacterGroup
  rw [DiagonalizableGroup.characterGroupSchemeMap_def,
    DiagonalizableGroup.groupSchemeMap_def]
  simp only [geometricCharacterGroupSchemeMap, geometricFiberGroupSchemeIso,
    Functor.mapIso_hom, Iso.op_hom]
  rw [← Category.assoc (eqToHom hG.symm) (eqToHom hG), eqToHom_trans,
    eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, cancel_mono, ← Functor.map_comp]
  apply congrArg (AlgebraicGeometry.hopfSpec
    (CommRingCat.of (AlgebraicClosure k))).map
  exact congrArg (fun q => q.hom.op) (coordinateMap_comp_geometricCoordinateIso T x).symm

/-- Character-group morphisms to the lifted integer group are integral linear functionals on
the additive character group. -/
private noncomputable def characterHomDualEquiv (T : TorusCommHopfAlgCat k) :
    (geometricCharacterFG T ⟶ DiagonalizableGroup.multiplicativeCharacterGroup) ≃
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  ((ConcreteCategory.homEquiv (X := geometricCharacterFG T)
      (Y := DiagonalizableGroup.multiplicativeCharacterGroup)).trans
    (MulEquiv.monoidHomCongrRightEquiv
      (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ))).trans
    (MonoidHom.toAdditiveLeft.trans (addMonoidHomLequivInt ℤ).toEquiv)

/-- Full faithfulness identifies homomorphisms of character groups with the corresponding
contravariant morphisms of diagonalizable group schemes. -/
private noncomputable def diagonalizableGroupSchemeHomEquiv
    (G H : FGCommGrpCat.{u}) :
    (G ⟶ H) ≃
      (DiagonalizableGroup.groupScheme (AlgebraicClosure k) H ⟶
        DiagonalizableGroup.groupScheme (AlgebraicClosure k) G) :=
  (Quiver.Hom.opEquiv.trans
    (DiagonalizableGroup.fullyFaithfulSchemeFunctor
      (AlgebraicClosure k)).homEquiv).trans <|
        (eqToIso (DiagonalizableGroup.schemeFunctor_obj
          (AlgebraicClosure k) (Opposite.op H))).homCongr
            (eqToIso (DiagonalizableGroup.schemeFunctor_obj
              (AlgebraicClosure k) (Opposite.op G)))

private theorem diagonalizableGroupSchemeHomEquiv_apply
    (G H : FGCommGrpCat.{u}) (f : G ⟶ H) :
    diagonalizableGroupSchemeHomEquiv (k := k) G H f =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) f := by
  simp [diagonalizableGroupSchemeHomEquiv,
    DiagonalizableGroup.schemeFunctor_map]

/-- The geometric fibre reconstructed from its intrinsic characters, now with the public
diagonalizable-group-scheme presentation as target. -/
private noncomputable def geometricFiberDiagonalizableIso (T : TorusCommHopfAlgCat k) :
    geometricFiberGroupScheme T ≅
      DiagonalizableGroup.groupScheme (AlgebraicClosure k) (geometricCharacterFG T) :=
  (geometricFiberGroupSchemeIso T).trans <|
    eqToIso (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
      (geometricCharacterFG T)).symm

/-- Canonical reconstruction identifies a geometric cocharacter with the corresponding
homomorphism from the intrinsic character group to the character group of `G_m`. -/
private noncomputable def cocharacterLatticeEquivFG (T : TorusCommHopfAlgCat k) :
    cocharacterLattice T ≃
      (geometricCharacterFG T ⟶ DiagonalizableGroup.multiplicativeCharacterGroup) :=
  ((Iso.refl _).homCongr (geometricFiberDiagonalizableIso T)).trans
    (diagonalizableGroupSchemeHomEquiv (k := k) (geometricCharacterFG T)
      DiagonalizableGroup.multiplicativeCharacterGroup).symm

/-- The character-group homomorphism canonically recovered from a geometric cocharacter. -/
private noncomputable def cocharacterFGMap (T : TorusCommHopfAlgCat k)
    (f : cocharacterLattice T) :
    geometricCharacterFG T ⟶ DiagonalizableGroup.multiplicativeCharacterGroup :=
  cocharacterLatticeEquivFG T f

private theorem cocharacter_comp_geometricFiberGroupSchemeIso
    (T : TorusCommHopfAlgCat k) (f : cocharacterLattice T) :
    (f ≫ (geometricFiberGroupSchemeIso T).hom) ≫
        eqToHom (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
          (geometricCharacterFG T)).symm =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) (cocharacterFGMap T f) := by
  change f ≫ (geometricFiberDiagonalizableIso T).hom = _
  rw [← diagonalizableGroupSchemeHomEquiv_apply]
  exact (diagonalizableGroupSchemeHomEquiv (k := k) (geometricCharacterFG T)
    DiagonalizableGroup.multiplicativeCharacterGroup).apply_symm_apply _ |>.symm

/-- The ordinary-integer-valued homomorphism underlying the lifted character-group map of a
geometric cocharacter. -/
private noncomputable def cocharacterMonoidHom (T : TorusCommHopfAlgCat k)
    (f : cocharacterLattice T) : geometricCharacterFG T →* Multiplicative ℤ :=
  (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom.comp
    (FGCommGrpCat.toMonoidHom (cocharacterFGMap T f))

private theorem cocharacterGroupSchemeMap_eq (T : TorusCommHopfAlgCat k)
    (f : cocharacterLattice T) :
    DiagonalizableGroup.cocharacterGroupSchemeMap (R := AlgebraicClosure k)
        (geometricCharacterFG T) (cocharacterMonoidHom T f) =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) (cocharacterFGMap T f) := by
  rw [DiagonalizableGroup.cocharacterGroupSchemeMap_def]
  unfold cocharacterMonoidHom
  congr 1

/-- The canonical group-like reconstruction identifies geometric cocharacters with the integral
dual of geometric characters. This comparison is not the definition of `cocharacterLattice`. -/
noncomputable def cocharacterLatticeEquivDual (T : TorusCommHopfAlgCat k) :
    cocharacterLattice T ≃
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  (cocharacterLatticeEquivFG T).trans (characterHomDualEquiv T)

noncomputable instance instCocharacterLatticeAddCommGroup (T : TorusCommHopfAlgCat k) :
    AddCommGroup (cocharacterLattice T) :=
  (cocharacterLatticeEquivDual T).addCommGroup

noncomputable instance instCocharacterLatticeModule (T : TorusCommHopfAlgCat k) :
    Module ℤ (cocharacterLattice T) :=
  (cocharacterLatticeEquivDual T).addEquiv.module ℤ

/-- The canonical equivalence from geometric cocharacters to the character dual, as a linear
equivalence. -/
noncomputable def cocharacterLatticeLinearEquivDual (T : TorusCommHopfAlgCat k) :
    cocharacterLattice T ≃ₗ[ℤ]
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  (cocharacterLatticeEquivDual T).addEquiv.linearEquiv ℤ

private theorem pairing_cocharacterMonoidHom (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    DiagonalizableGroup.pairing (geometricCharacterFGEquiv T x.toMul)
        (cocharacterMonoidHom T f) =
      cocharacterLatticeLinearEquivDual T f x := by
  -- Both sides evaluate the same character-group homomorphism, with the left side passing
  -- through multiplicative notation and the right side through the transported integral dual.
  rw [DiagonalizableGroup.pairing_def]
  rfl

/-- The contragredient absolute-Galois representation on the cocharacter lattice. Thus a
Galois element `σ` sends a cocharacter functional `f` to `x ↦ f (σ⁻¹ • x)`. -/
noncomputable def cocharacterGaloisRepresentation (T : TorusCommHopfAlgCat k) :
    Representation ℤ (Field.absoluteGaloisGroup k) (cocharacterLattice T) :=
  (cocharacterLatticeLinearEquivDual T).symm.conjRingEquiv.toMonoidHom.comp <|
    (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual

/-- The contragredient Galois representation evaluates by applying the inverse Galois element
to the character. -/
@[simp]
theorem cocharacterGaloisRepresentation_apply_apply (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (f : cocharacterLattice T) (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    cocharacterLatticeLinearEquivDual T (cocharacterGaloisRepresentation T σ f) x =
      cocharacterLatticeLinearEquivDual T f (σ⁻¹ • x) := by
  -- The representation is packaged as a composite monoid hom, whereas
  -- `LinearEquiv.conj_apply_apply` rewrites a bare conjugation. This definitional step exposes
  -- that single representation-wrapper boundary before applying the public conjugation lemma.
  rw [show cocharacterGaloisRepresentation T σ f =
      (cocharacterLatticeLinearEquivDual T).symm.conj
        ((Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
          (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual σ) f by
    rfl]
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The character--cocharacter pairing transported through the canonical dual comparison. It is
evaluation of a functional in `X_*(T) = Hom_ℤ(X*(T), ℤ)` on a character. -/
noncomputable def characterCocharacterPairing (T : TorusCommHopfAlgCat k) :
    CommHopfAlgCat.additiveCharacterGroup T.obj.obj →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ :=
  (cocharacterLatticeLinearEquivDual T).toLinearMap.flip

/-- The character--cocharacter pairing is evaluation. -/
@[simp]
theorem characterCocharacterPairing_apply (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T x f = cocharacterLatticeLinearEquivDual T f x := by
  unfold characterCocharacterPairing
  rfl

/-- Composing an intrinsic geometric cocharacter with an intrinsic geometric character is the
multiplicative-group power map whose exponent is their character--cocharacter pairing. -/
theorem cocharacter_comp_geometricCharacterGroupSchemeMap (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    f ≫ geometricCharacterGroupSchemeMap T x =
      DiagonalizableGroup.powEndGroupSchemeMap (R := AlgebraicClosure k)
        (characterCocharacterPairing T x f) := by
  rw [geometricCharacterGroupSchemeMap_eq]
  simp only [← Category.assoc]
  rw [
    cocharacter_comp_geometricFiberGroupSchemeIso,
    ← cocharacterGroupSchemeMap_eq,
    DiagonalizableGroup.cocharacterGroupSchemeMap_comp_characterGroupSchemeMap,
    characterCocharacterPairing_apply, pairing_cocharacterMonoidHom]

private theorem powEndGroupSchemeMap_injective :
    Function.Injective
      (DiagonalizableGroup.powEndGroupSchemeMap (R := AlgebraicClosure k)) := by
  intro m n h
  let q (z : ℤ) : DiagonalizableGroup.multiplicativeCharacterGroup ⟶
      DiagonalizableGroup.multiplicativeCharacterGroup :=
    FGCommGrpCat.ofHom (DiagonalizableGroup.uliftZPowersMulEquiv
      DiagonalizableGroup.multiplicativeCharacterGroup
        (ULift.up (Multiplicative.ofAdd z)))
  have hmap :
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) (q m) =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) (q n) := by
    rw [DiagonalizableGroup.powEndGroupSchemeMap_def,
      DiagonalizableGroup.powEndGroupSchemeMap_def,
      DiagonalizableGroup.characterGroupSchemeMap_def,
      DiagonalizableGroup.characterGroupSchemeMap_def] at h
    exact h
  have hopmap :
      (DiagonalizableGroup.schemeFunctor (AlgebraicClosure k)).map (q m).op =
        (DiagonalizableGroup.schemeFunctor (AlgebraicClosure k)).map (q n).op := by
    rw [DiagonalizableGroup.schemeFunctor_map, DiagonalizableGroup.schemeFunctor_map]
    simp only [Quiver.Hom.unop_op]
    rw [hmap]
  have hop := (DiagonalizableGroup.schemeFunctor (AlgebraicClosure k)).map_injective hopmap
  have hq : q m = q n := by
    simpa using congrArg Quiver.Hom.unop hop
  have heval := DFunLike.congr_fun
    (congrArg FGCommGrpCat.toMonoidHom hq)
      (ULift.up (Multiplicative.ofAdd (1 : ℤ)))
  change (DiagonalizableGroup.uliftZPowersMulEquiv
      DiagonalizableGroup.multiplicativeCharacterGroup
        (ULift.up (Multiplicative.ofAdd m)))
          (ULift.up (Multiplicative.ofAdd (1 : ℤ))) =
    (DiagonalizableGroup.uliftZPowersMulEquiv
      DiagonalizableGroup.multiplicativeCharacterGroup
        (ULift.up (Multiplicative.ofAdd n)))
          (ULift.up (Multiplicative.ofAdd (1 : ℤ))) at heval
  rw [DiagonalizableGroup.uliftZPowersMulEquiv_apply,
    DiagonalizableGroup.uliftZPowersMulEquiv_apply] at heval
  have := congrArg (fun z : ULift.{u} (Multiplicative ℤ) => z.down.toAdd) heval
  simpa using this

/-- The pairing is the unique exponent whose power map is the composite of the corresponding
geometric cocharacter and character. -/
theorem characterCocharacterPairing_eq_iff_comp_eq_powEndGroupSchemeMap
    (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) (n : ℤ) :
    characterCocharacterPairing T x f = n ↔
      f ≫ geometricCharacterGroupSchemeMap T x =
        DiagonalizableGroup.powEndGroupSchemeMap (R := AlgebraicClosure k) n := by
  constructor
  · intro h
    rw [cocharacter_comp_geometricCharacterGroupSchemeMap, h]
  · intro h
    apply powEndGroupSchemeMap_injective (k := k)
    rw [← cocharacter_comp_geometricCharacterGroupSchemeMap]
    exact h

/-- The character--cocharacter pairing is invariant under the diagonal absolute-Galois action. -/
theorem characterCocharacterPairing_galois (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T (σ • x) (cocharacterGaloisRepresentation T σ f) =
      characterCocharacterPairing T x f := by
  rw [characterCocharacterPairing_apply, cocharacterGaloisRepresentation_apply_apply,
    inv_smul_smul, characterCocharacterPairing_apply]

/-- The character--cocharacter pairing of a torus is perfect. -/
noncomputable instance instCharacterCocharacterPairingIsPerfPair (T : TorusCommHopfAlgCat k) :
    (characterCocharacterPairing T).IsPerfPair := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  unfold characterCocharacterPairing
  infer_instance

/-- The cocharacter lattice of a torus is free over the integers. -/
theorem cocharacterLattice_module_free (T : TorusCommHopfAlgCat k) :
    Module.Free ℤ (cocharacterLattice T) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact Module.Free.of_equiv (cocharacterLatticeLinearEquivDual T).symm

/-- The cocharacter lattice of a torus is finitely generated over the integers. -/
theorem cocharacterLattice_module_finite (T : TorusCommHopfAlgCat k) :
    Module.Finite ℤ (cocharacterLattice T) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact Module.Finite.equiv (cocharacterLatticeLinearEquivDual T).symm

/-- The character and cocharacter lattices of a torus have the same rank. -/
theorem finrank_cocharacterLattice_eq_characterLattice (T : TorusCommHopfAlgCat k) :
    Module.finrank ℤ (cocharacterLattice T) =
      Module.finrank ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact (Module.finrank_of_isPerfPair (characterCocharacterPairing T)).symm

/-- A torus cocharacter lattice is noncanonically a finite-rank free abelian group. -/
theorem exists_cocharacterLattice_linearEquiv (T : TorusCommHopfAlgCat k) :
    ∃ n : ℕ, Nonempty (cocharacterLattice T ≃ₗ[ℤ] (Fin n → ℤ)) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_characterLattice_addEquiv_of_torus k T.obj T.property
  exact ⟨n, ⟨(cocharacterLatticeLinearEquivDual T).trans
    (e.toIntLinearEquiv.symm.dualMap.trans (Finsupp.llift ℤ ℤ ℤ (Fin n)).symm)⟩⟩

end TorusCommHopfAlgCat

namespace SplitTorus

/-- The standard rank-`σ` split torus, regarded as an object of the category of tori. -/
noncomputable abbrev toTorusCommHopfAlgCat
    (k : Type u) [Field k] (σ : Type u) [Finite σ] : TorusCommHopfAlgCat k :=
  ⟨DiagonalizableGroup.coordinateRing k (characterGroup σ),
    (splitTorus_coordinateRing k σ).torus k _⟩

/-- The transported additive group instance specialized to a standard split torus. -/
noncomputable local instance cocharacterLatticeAddCommGroup
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    AddCommGroup
      (TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) :=
  TorusCommHopfAlgCat.instCocharacterLatticeAddCommGroup _

/-- The transported integer-module instance specialized to a standard split torus. -/
noncomputable local instance cocharacterLatticeModule
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    Module ℤ (TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) :=
  TorusCommHopfAlgCat.instCocharacterLatticeModule _

/-- The chosen dual comparison for a standard split torus, expressed in coordinates `σ → ℤ`. -/
noncomputable def cocharacterLatticeCoordEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ) ≃ₗ[ℤ]
      (σ → ℤ) :=
  (TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toTorusCommHopfAlgCat k σ)).trans <|
    (characterLatticeEquiv k σ).toIntLinearEquiv.symm.dualMap |>.trans
      (Finsupp.llift ℤ ℤ ℤ σ).symm

/-- The chosen dual comparison for a standard split torus, expressed in its existing group of
genuine cocharacters `Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ`. -/
noncomputable def cocharacterLatticeEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ) ≃ₗ[ℤ]
      Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :=
  (cocharacterLatticeCoordEquiv k σ).trans cocharAddEquiv.toIntLinearEquiv.symm

/-- Under the chosen split-torus cocharacter equivalence, the usual cocharacter coordinates are
obtained by applying the functional to the corresponding standard characters. -/
@[simp]
theorem cocharAddEquiv_cocharacterLatticeEquiv_apply
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (f : TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) (i : σ) :
    cocharAddEquiv (cocharacterLatticeEquiv k σ f) i =
      TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual
        (toTorusCommHopfAlgCat k σ) f
          ((characterLatticeEquiv k σ).symm (Finsupp.single i 1)) := by
  simp [cocharacterLatticeEquiv, cocharacterLatticeCoordEquiv, Finsupp.llift_symm_apply]

/-- For a standard split torus, the pairing transported through the chosen comparison agrees with
the existing pairing on the explicit character and cocharacter lattices. -/
theorem characterCocharacterPairing_eq_latticePairing
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (x : CommHopfAlgCat.additiveCharacterGroup
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj)
    (f : TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) :
    TorusCommHopfAlgCat.characterCocharacterPairing
        (toTorusCommHopfAlgCat k σ) x f =
      latticePairing (characterLatticeEquiv k σ x) (cocharacterLatticeEquiv k σ f) := by
  rw [TorusCommHopfAlgCat.characterCocharacterPairing_apply,
    ← ofMul_toMul (cocharacterLatticeEquiv k σ f), latticePairing_ofMul,
    pairing_eq_dotPairing, dotPairing_apply]
  simp_rw [← cocharAddEquiv_apply]
  simp only [ofMul_toMul, ← smul_eq_mul]
  rw [← Finsupp.lift_apply,
    ← Finsupp.llift_apply (M := ℤ) (R := ℤ) (X := σ) (S := ℤ)]
  simp [cocharacterLatticeEquiv, cocharacterLatticeCoordEquiv]

/-- The absolute-Galois representation on the geometric cocharacter lattice of a standard split
torus is trivial. -/
@[simp]
theorem cocharacterGaloisRepresentation_apply_eq_self
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (γ : Field.absoluteGaloisGroup k)
    (f : TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) :
    TorusCommHopfAlgCat.cocharacterGaloisRepresentation
      (toTorusCommHopfAlgCat k σ) γ f = f := by
  apply (TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual
    (toTorusCommHopfAlgCat k σ)).injective
  ext x
  rw [TorusCommHopfAlgCat.cocharacterGaloisRepresentation_apply_apply,
    smul_characterLattice_eq_self]

end SplitTorus

end TauCeti
