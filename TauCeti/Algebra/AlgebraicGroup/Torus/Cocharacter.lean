/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Cocharacter lattices of tori

For a torus `T` over a field `k`, a geometric cocharacter is a group-scheme morphism
`G_m → T` after extension to the chosen algebraic closure. Contravariantly, it is a morphism
of coordinate Hopf algebras

```text
O(T_bar) → O(G_m).
```

The geometric fibre of a torus is canonically reconstructed from its group-like characters.
Full faithfulness of the diagonalizable-group coordinate-ring functor therefore identifies these
geometric morphisms with the integral dual of the geometric character lattice. This comparison,
rather than the definition of cocharacters, supplies the perfect pairing. The dual description is
specific to tori: a semisimple group can have trivial character group and nontrivial cocharacters.

The absolute Galois action on `X_*(T)` is the contragredient of its action on `X*(T)`. The
evaluation pairing is invariant under the diagonal action and is perfect over `ℤ`. For the
standard split torus, the intrinsic dual is identified with the existing group of genuine
cocharacters, and the Galois representation is shown to be trivial.

## Main declarations

* `TauCeti.TorusCommHopfAlgCat.cocharacterLattice`: geometric group-scheme morphisms
  `G_m → T_bar`.
* `TauCeti.TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual`: the canonical comparison
  between geometric cocharacters and the integral character dual.
* `TauCeti.TorusCommHopfAlgCat.cocharacterGaloisRepresentation`: its contragredient absolute
  Galois representation.
* `TauCeti.TorusCommHopfAlgCat.characterCocharacterPairing`: the evaluation pairing between
  characters and cocharacters, with a perfect-pairing instance.
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

private theorem baseChange_groupLikeSpanned (T : TorusCommHopfAlgCat k) :
    DiagonalizableGroup.groupLikeSpannedProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj) := by
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor]
  have hT := (torusCommHopfAlgProperty_iff k T.obj).1 T.property
  obtain ⟨n, ⟨i⟩⟩ := hT
  exact ⟨SplitTorus.characterGroup (ULift.{u} (Fin n)), ⟨i⟩⟩

private theorem baseChange_groupLike_span_eq_top (T : TorusCommHopfAlgCat k) :
    Submodule.span (AlgebraicClosure k)
        (Set.range (_root_.GroupLike.val (R := AlgebraicClosure k)
          (A := FiniteTypeCommHopfAlgCat.baseChange
            (K := AlgebraicClosure k) T.obj))) = ⊤ := by
  rw [← Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  exact (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).1
    (baseChange_groupLikeSpanned T)

/-- The geometric character group of a torus, bundled as a finitely generated commutative
group for use with the diagonalizable coordinate-ring functor. -/
private noncomputable def geometricCharacterFG (T : TorusCommHopfAlgCat k) :
    FGCommGrpCat.{u} := by
  let _ : Group.FG (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) :=
    CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType T.obj
      (torusCommHopfAlgProperty.multiplicativeType k T.obj T.property)
  exact FGCommGrpCat.of (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)

/-- The canonical reconstruction of the geometric coordinate algebra of a torus from its
geometric characters. -/
private noncomputable def geometricCoordinateIso (T : TorusCommHopfAlgCat k) :
    DiagonalizableGroup.coordinateRing (AlgebraicClosure k) (geometricCharacterFG T) ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj :=
  ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    TauCeti.GroupLike.evaluationBialgEquiv (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)
      (baseChange_groupLike_span_eq_top T)

/-- The geometric fibre of a torus as an affine group scheme over the chosen algebraic closure. -/
noncomputable abbrev geometricFiberGroupScheme (T : TorusCommHopfAlgCat k) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).obj <|
    Opposite.op (FiniteTypeCommHopfAlgCat.baseChange
      (K := AlgebraicClosure k) T.obj).obj

/-- The multiplicative group over the chosen algebraic closure, in the relative-spectrum
presentation used for geometric cocharacters. -/
noncomputable abbrev geometricMultiplicativeGroupScheme :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).obj <|
    Opposite.op
      (DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
        DiagonalizableGroup.multiplicativeCharacterGroup).obj

/-- The geometric cocharacter lattice of a torus: group-scheme morphisms `G_m → T_bar` over
the chosen algebraic closure. -/
abbrev cocharacterLattice (T : TorusCommHopfAlgCat k) :=
  geometricMultiplicativeGroupScheme (k := k) ⟶ geometricFiberGroupScheme T

/-- Under the fully faithful relative-spectrum functor, a geometric cocharacter is equivalently
the contravariant morphism from the geometric coordinate algebra of the torus to that of `G_m`. -/
private noncomputable def cocharacterLatticeEquivCoordinate (T : TorusCommHopfAlgCat k) :
    cocharacterLattice T ≃
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj ⟶
        DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
          DiagonalizableGroup.multiplicativeCharacterGroup) :=
  (Quiver.Hom.opEquiv.trans <| by
    let hF : ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
        (_root_.CommHopfAlgCat.{u} (AlgebraicClosure k))).op ⋙
        AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).FullyFaithful :=
      (finiteTypeCommHopfAlgProperty
        (R := AlgebraicClosure k)).fullyFaithfulι.op.comp
          (AlgebraicGeometry.hopfSpec.fullyFaithful
            (R := CommRingCat.of (AlgebraicClosure k)))
    exact hF.homEquiv).symm

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

/-- Geometric cocharacters are canonically the integral dual of geometric characters. The
equivalence comes from the canonical group-like reconstruction of the split geometric fibre,
not from the definition of `cocharacterLattice`. -/
noncomputable def cocharacterLatticeEquivDual (T : TorusCommHopfAlgCat k) :
    cocharacterLattice T ≃
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  (cocharacterLatticeEquivCoordinate T).trans <|
    ((geometricCoordinateIso T).homCongr (Iso.refl _)).symm |>.trans
      ((Functor.FullyFaithful.ofFullyFaithful
        (DiagonalizableGroup.coordinateRingFunctor
          (AlgebraicClosure k))).homEquiv.symm) |>.trans
      (characterHomDualEquiv T)

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

/-- The contragredient absolute-Galois representation on the cocharacter lattice. Thus a
Galois element `σ` sends a cocharacter functional `f` to `x ↦ f (σ⁻¹ • x)`. -/
noncomputable abbrev cocharacterGaloisRepresentation (T : TorusCommHopfAlgCat k) :
    Representation ℤ (Field.absoluteGaloisGroup k) (cocharacterLattice T) :=
  (cocharacterLatticeLinearEquivDual T).symm.conjRingEquiv.toMonoidHom.comp <|
    (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual

/-- The contragredient Galois representation evaluates by applying the inverse Galois element
to the character. -/
theorem cocharacterGaloisRepresentation_apply_apply (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (f : cocharacterLattice T) (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    cocharacterLatticeLinearEquivDual T (cocharacterGaloisRepresentation T σ f) x =
      cocharacterLatticeLinearEquivDual T f (σ⁻¹ • x) := by
  change cocharacterLatticeLinearEquivDual T
      ((cocharacterLatticeLinearEquivDual T).symm.conj
        ((Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
          (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual σ) f) x = _
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The canonical character--cocharacter pairing of a torus. It is evaluation of a functional
in `X_*(T) = Hom_ℤ(X*(T), ℤ)` on a character. -/
noncomputable abbrev characterCocharacterPairing (T : TorusCommHopfAlgCat k) :
    CommHopfAlgCat.additiveCharacterGroup T.obj.obj →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ :=
  (cocharacterLatticeLinearEquivDual T).toLinearMap.flip

/-- The character--cocharacter pairing is evaluation. -/
@[simp]
theorem characterCocharacterPairing_apply (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T x f = cocharacterLatticeLinearEquivDual T f x := by
  rfl

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

/-- A torus cocharacter lattice is noncanonically a finite-rank free abelian group, of the same
rank as its character lattice. -/
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

/-- The intrinsic cocharacter lattice of a standard split torus in the coordinates `σ → ℤ`. -/
noncomputable def cocharacterLatticeCoordEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ) ≃ₗ[ℤ]
      (σ → ℤ) :=
  (TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toTorusCommHopfAlgCat k σ)).trans <|
    (characterLatticeEquiv k σ).toIntLinearEquiv.symm.dualMap |>.trans
      (Finsupp.llift ℤ ℤ ℤ σ).symm

/-- The intrinsic cocharacter lattice of a standard split torus is its existing group of genuine
cocharacters `Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ`. -/
noncomputable def cocharacterLatticeEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ) ≃ₗ[ℤ]
      Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :=
  (cocharacterLatticeCoordEquiv k σ).trans cocharAddEquiv.toIntLinearEquiv.symm

/-- Under the intrinsic split-torus cocharacter equivalence, the usual cocharacter coordinates
are obtained by applying the functional to the corresponding standard characters. -/
@[simp]
theorem cocharAddEquiv_cocharacterLatticeEquiv_apply
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (f : TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) (i : σ) :
    cocharAddEquiv (cocharacterLatticeEquiv k σ f) i =
      TorusCommHopfAlgCat.cocharacterLatticeLinearEquivDual
        (toTorusCommHopfAlgCat k σ) f
          ((characterLatticeEquiv k σ).symm (Finsupp.single i 1)) := by
  simp [cocharacterLatticeEquiv, cocharacterLatticeCoordEquiv, Finsupp.llift_symm_apply]

/-- The absolute-Galois representation on the intrinsic cocharacter lattice of a standard split
torus is trivial. -/
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
