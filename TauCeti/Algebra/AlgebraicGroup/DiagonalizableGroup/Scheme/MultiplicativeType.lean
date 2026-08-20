/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.MultiplicativeType

/-!
# Multiplicative type of diagonalizable group schemes

Every finite-type diagonalizable group scheme over a field is of multiplicative type. The result
is first stated for an arbitrary finite-type affine group scheme satisfying the scheme-side
diagonalizable property, and then specialized to the canonical object `D(G) = Spec k[G]`.

## Main declarations

* `multiplicativeTypeAffineGroupSchemeProperty_of_diagonalizableGroupSchemeProperty`:
  every finite-type affine group scheme satisfying the diagonalizable property is of
  multiplicative type.
* `TauCeti.DiagonalizableGroup.multiplicativeTypeAffineGroupSchemeProperty_groupScheme`: the
  canonical finite-type diagonalizable group scheme `D(G)` is of multiplicative type.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.7 and 12.14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

The proof structure follows
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.LinearlyReductive`, replacing linear
reductivity by the coordinate-side multiplicative-type property. This supplies a Layer 4 example
from the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace DiagonalizableGroup

/-- Every finite-type affine group scheme satisfying the diagonalizable-group property is of
multiplicative type. -/
@[grind →]
theorem multiplicativeTypeAffineGroupSchemeProperty_of_diagonalizableGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : diagonalizableGroupSchemeProperty k G.obj.obj) :
    multiplicativeTypeAffineGroupSchemeProperty k G := by
  have hEssImage : (schemeFunctor k).essImage G.obj.obj := by
    rw [essImage_schemeFunctor]
    exact hG
  obtain ⟨M, ⟨e⟩⟩ := hEssImage
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k
  let H : FiniteTypeCommHopfAlgCat.{u, u} k := coordinateRing k M.unop
  have hE : multiplicativeTypeAffineGroupSchemeProperty k (E.functor.obj (op H)) := by
    rw [← ObjectProperty.prop_inverseImage_iff
        (multiplicativeTypeAffineGroupSchemeProperty k) E.functor (op H),
      multiplicativeTypeAffineGroupSchemeProperty_inverseImage, ObjectProperty.op_iff]
    exact multiplicativeType_coordinateRing k M.unop
  have hD : multiplicativeTypeAffineGroupSchemeProperty k
      (finiteTypeGroupScheme k M.unop) :=
    (multiplicativeTypeAffineGroupSchemeProperty k).prop_of_iso
      (finiteTypeGroupSchemeIso k M.unop) hE
  let e' : finiteTypeGroupScheme k M.unop ≅ G :=
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      ((affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
        (eqToIso (finiteTypeGroupScheme_obj_obj k M.unop) ≪≫
          eqToIso (schemeFunctor_obj k M).symm ≪≫ e))
  exact (multiplicativeTypeAffineGroupSchemeProperty k).prop_of_iso e' hD

/-- The canonical finite-type diagonalizable group scheme `D(G)` is of multiplicative type. -/
theorem multiplicativeTypeAffineGroupSchemeProperty_groupScheme
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    multiplicativeTypeAffineGroupSchemeProperty k (finiteTypeGroupScheme k G) := by
  apply multiplicativeTypeAffineGroupSchemeProperty_of_diagonalizableGroupSchemeProperty
  rw [← essImage_schemeFunctor]
  exact ⟨op G, ⟨eqToIso (schemeFunctor_obj k (op G)) ≪≫
    eqToIso (finiteTypeGroupScheme_obj_obj k G).symm⟩⟩

end DiagonalizableGroup

end TauCeti
