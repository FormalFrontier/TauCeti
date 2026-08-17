/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.LinearlyReductive

/-!
# Linear reductivity of diagonalizable group schemes

Every finite-type diagonalizable group scheme over a field is linearly reductive. On the
canonical object `D(G) = Spec k[G]`, this follows from complete reducibility of comodules over a
monoid-algebra coalgebra. Isomorphism invariance then extends the result to the full
diagonalizable-group-scheme property.

## Main declarations

* `TauCeti.DiagonalizableGroup.linearlyReductiveAffineGroupSchemeProperty_groupScheme`: the
  canonical diagonalizable group scheme `D(G)` is linearly reductive.
* `TauCeti.DiagonalizableGroup.linearlyReductive_of_diagonalizableGroupSchemeProperty`: every
  affine group scheme satisfying the diagonalizable property is linearly reductive.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.

This is the diagonalizable-group example for the complete-reducibility characterization in
Layer 6 of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace DiagonalizableGroup

/-- The canonical finite-type diagonalizable group scheme `D(G)` is linearly reductive. -/
theorem linearlyReductiveAffineGroupSchemeProperty_groupScheme
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    linearlyReductiveAffineGroupSchemeProperty k
      ⟨groupScheme k G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩ := by
  let S : AffineGroupSchemeCat (CommRingCat.of k) :=
    ⟨(hopfSpec (CommRingCat.of k)).obj (op (coordinateRing k G).obj), by
      rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
      infer_instance⟩
  let D : AffineGroupSchemeCat (CommRingCat.of k) :=
    ⟨groupScheme k G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩
  have hS : linearlyReductiveAffineGroupSchemeProperty k S :=
    (linearlyReductiveAffineGroupSchemeProperty_hopfSpec k (coordinateRing k G).obj).2
      (Coalgebra.isLinearlyReductive_monoidAlgebra k G)
  let e : S ≅ D :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      (eqToIso (groupScheme_def k G).symm)
  simpa only [D] using
    (linearlyReductiveAffineGroupSchemeProperty k).prop_of_iso e hS

/-- Every affine group scheme satisfying the finite-type diagonalizable-group property is
linearly reductive. -/
theorem linearlyReductive_of_diagonalizableGroupSchemeProperty
    (k : Type u) [Field k] (G : AffineGroupSchemeCat (CommRingCat.of k))
    (hG : diagonalizableGroupSchemeProperty k G.obj) :
    linearlyReductiveAffineGroupSchemeProperty k G := by
  have hEssImage : (schemeFunctor k).essImage G.obj := by
    rw [essImage_schemeFunctor]
    exact hG
  obtain ⟨M, ⟨e⟩⟩ := hEssImage
  let D : AffineGroupSchemeCat (CommRingCat.of k) :=
    ⟨groupScheme k M.unop, (affineGroupSchemeProperty_iff _).2 inferInstance⟩
  let e' : D ≅ G :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      (eqToIso (schemeFunctor_obj k M).symm ≪≫ e)
  exact (linearlyReductiveAffineGroupSchemeProperty k).prop_of_iso e'
    (linearlyReductiveAffineGroupSchemeProperty_groupScheme k M.unop)

end DiagonalizableGroup

end TauCeti
