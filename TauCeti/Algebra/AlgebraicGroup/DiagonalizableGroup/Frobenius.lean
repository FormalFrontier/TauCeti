/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.Frobenius.Points

/-!
# Frobenius on diagonalizable groups

Let `A` be a commutative ring of exponential characteristic `p`. For any finitely generated
commutative group `G`, applying the `n`-fold Frobenius of `A` to an `A`-valued point of the
diagonalizable group `D(G)` agrees, under the coordinate-algebra comparison, with the existing
Frobenius endomorphism on convolution points.

## Main result

* `TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_mapValue_iterateFrobenius`: the
  scheme-point and convolution-point descriptions of iterated Frobenius agree.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 12 and 13.
-/

public section

open CategoryTheory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.DiagonalizableGroup

variable {A : Type} [CommRing A]
variable (p n : ℕ) [ExpChar A p]

/-- Under the coordinate-algebra comparison for a diagonalizable group, applying the iterated
Frobenius of the value ring is the existing Frobenius endomorphism on convolution points. -/
theorem groupSchemePointsMulEquiv_mapValue_iterateFrobenius (G : FGCommGrpCat)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (groupScheme ℤ G).X) :
    groupSchemePointsMulEquiv (R := ℤ) (A := A) G
        ((Spec.map (CommRingCat.ofHom (iterateFrobenius A p n).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q) =
      Bialgebra.iterateFrobeniusPoints p n
        (groupSchemePointsMulEquiv (R := ℤ) (A := A) G q) := by
  rw [groupSchemePointsMulEquiv_mapValue,
    Bialgebra.iterateFrobeniusPoints_apply, AlgHom.mapValue_apply]

end TauCeti.DiagonalizableGroup
