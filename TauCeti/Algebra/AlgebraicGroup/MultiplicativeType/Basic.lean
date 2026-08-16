/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage

/-!
# Groups of multiplicative type

A finite-type affine group over a field is of multiplicative type when it becomes diagonalizable
after extending scalars to an algebraic closure. On coordinate Hopf algebras, diagonalizability is
the intrinsic condition that the group-like elements span the algebra. Thus a finite-type
commutative Hopf algebra `H` over `k` is of multiplicative type exactly when the group-like
elements span `AlgebraicClosure k ⊗[k] H`.

The essential-image characterization of diagonalizable coordinate rings identifies this intrinsic
definition with the usual one: after base change, the Hopf algebra is isomorphic to `k̄[M]` for a
finitely generated commutative group `M`. In particular, every coordinate ring arising from
`FGCommGrpCat` is of multiplicative type.

## Main declarations

* `TauCeti.multiplicativeTypeCommHopfAlgProperty`: the multiplicative-type object property on
  finite-type commutative Hopf algebras over a field.
* `TauCeti.multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing`: the
  characterization by becoming a diagonalizable coordinate ring over an algebraic closure.
* `TauCeti.DiagonalizableGroup.multiplicativeType_coordinateRing`: every finite-type
  diagonalizable coordinate Hopf algebra is of multiplicative type.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat`: the full subcategory of coordinate Hopf algebras of
  multiplicative-type groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This is the coordinate-algebra foundation for Layer 4, "Diagonalizable groups and groups of
multiplicative type", of the ReductiveGroups roadmap. Non-split tori will add smoothness and
geometric connectedness to this property and equip the resulting character lattice with its
Galois action.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The object property selecting finite-type commutative Hopf algebras that become
diagonalizable after base change to an algebraic closure.

Diagonalizability is expressed intrinsically by the group-like elements spanning the base-changed
coordinate algebra. -/
def multiplicativeTypeCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  (DiagonalizableGroup.groupLikeSpannedProperty (AlgebraicClosure k)).inverseImage
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k))

/-- Membership in the multiplicative-type property means that the base-changed Hopf algebra is
spanned by its group-like elements. -/
@[simp]
theorem multiplicativeTypeCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    multiplicativeTypeCommHopfAlgProperty k H ↔
      DiagonalizableGroup.groupLikeSpannedProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  Iff.rfl

/-- Being of multiplicative type is invariant under isomorphisms of finite-type commutative Hopf
algebras. -/
instance (k : Type u) [Field k] :
    (multiplicativeTypeCommHopfAlgProperty k).IsClosedUnderIsomorphisms :=
  by
    unfold multiplicativeTypeCommHopfAlgProperty
    infer_instance

/-- **A finite-type commutative Hopf algebra is of multiplicative type exactly when its base
change to an algebraic closure is the coordinate Hopf algebra of a diagonalizable group.** -/
theorem multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    multiplicativeTypeCommHopfAlgProperty k H ↔
      ∃ G : FGCommGrpCat.{u}, Nonempty
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
          FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [multiplicativeTypeCommHopfAlgProperty, ObjectProperty.prop_inverseImage_iff,
    ← DiagonalizableGroup.essImage_coordinateRingFunctor]
  simp only [Functor.essImage, DiagonalizableGroup.coordinateRingFunctor_obj]

namespace DiagonalizableGroup

/-- Every finite-type diagonalizable coordinate Hopf algebra is of multiplicative type. -/
theorem multiplicativeType_coordinateRing
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    multiplicativeTypeCommHopfAlgProperty k (coordinateRing k G) := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing]
  exact ⟨G, ⟨(baseChangeCoordinateRingIso k (AlgebraicClosure k) G).symm⟩⟩

end DiagonalizableGroup

/-- The category of finite-type commutative Hopf algebras of multiplicative type over a field.

Objects are not required to be split over the base field; they become diagonalizable after base
change to an algebraic closure. -/
abbrev MultiplicativeTypeCommHopfAlgCat (k : Type u) [Field k] :=
  (multiplicativeTypeCommHopfAlgProperty k).FullSubcategory

end TauCeti
