/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.Points
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.LinearMap

/-!
# Frobenius on split tori

Let `A` be a commutative ring of exponential characteristic `p`. On the `A`-valued points of an
integral split torus, post-composition with the `n`-fold Frobenius of `A` agrees with the
group-scheme power endomorphism of exponent `p ^ n`. Thus the coordinate-free Frobenius on
convolution points, the functorial action on scheme-valued points, and coordinatewise powering
all describe the same endomorphism.

This comparison is the bridge needed to read the square of a special isogeny on a split maximal
torus as Frobenius rather than merely as an abstract power map.

## Main results

* `TauCeti.SplitTorus.groupSchemePointsMulEquiv_mapValue_iterateFrobenius`: under the
  coordinate-algebra comparison, functoriality along Frobenius is the existing convolution-point
  Frobenius.
* `TauCeti.SplitTorus.mapValue_iterateFrobenius_eq_comp_powEnd`: on scheme-valued points, the
  `n`-fold Frobenius is composition with the power endomorphism of exponent `p ^ n`.
* `TauCeti.SplitTorus.mapValue_iterateFrobenius_eq_self_iff`: a point is fixed by the iterated
  Frobenius exactly when each torus coordinate is fixed by the corresponding power map.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 12 and 13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), Section 11.
-/

public section

open CategoryTheory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.SplitTorus

variable {A sigma : Type} [CommRing A] [Finite sigma]
variable (p n : ℕ) [ExpChar A p]

/-- Under the coordinate-algebra comparison for an integral split torus, applying the iterated
Frobenius of the value ring is the existing Frobenius endomorphism on convolution points. -/
theorem groupSchemePointsMulEquiv_mapValue_iterateFrobenius
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (groupScheme ℤ sigma).X) :
    DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := ℤ) (A := A) (characterGroup sigma)
        ((Spec.map (CommRingCat.ofHom (iterateFrobenius A p n).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q) =
      Bialgebra.iterateFrobeniusPoints p n
        (DiagonalizableGroup.groupSchemePointsMulEquiv
          (R := ℤ) (A := A) (characterGroup sigma) q) := by
  rw [DiagonalizableGroup.groupSchemePointsMulEquiv_mapValue,
    Bialgebra.iterateFrobeniusPoints_apply, AlgHom.mapValue_apply]

/-- **The iterated Frobenius on the points of an integral split torus is its power
endomorphism.** Precomposing an `A`-valued point by the `n`-fold Frobenius of `A` agrees with
postcomposing it by the split-torus power map of exponent `p ^ n`. -/
theorem mapValue_iterateFrobenius_eq_comp_powEnd
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (groupScheme ℤ sigma).X) :
    (Spec.map (CommRingCat.ofHom (iterateFrobenius A p n).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q =
      q ≫ (powEnd ℤ sigma ((p ^ n : ℕ) : ℤ)).hom.hom := by
  refine (schemePointsMulEquiv (R := ℤ) (A := A) (sigma := sigma)).injective ?_
  funext i
  apply Units.ext
  rw [schemePointsMulEquiv_mapValue, schemePointsMulEquiv_powEnd]
  change iterateFrobenius A p n
      (schemePointsMulEquiv (R := ℤ) (A := A) q i : A) =
    ((schemePointsMulEquiv (R := ℤ) (A := A) q i) ^ ((p ^ n : ℕ) : ℤ) : Aˣ)
  rw [iterateFrobenius_def]
  exact congrArg (fun x : Aˣ => (x : A))
    (zpow_natCast (schemePointsMulEquiv (R := ℤ) (A := A) q i) (p ^ n)).symm

/-- The ordinary Frobenius on the points of an integral split torus is its power endomorphism
of exponent `p`. -/
theorem mapValue_frobenius_eq_comp_powEnd
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (groupScheme ℤ sigma).X) :
    (Spec.map (CommRingCat.ofHom (frobenius A p).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q =
      q ≫ (powEnd ℤ sigma (p : ℤ)).hom.hom := by
  rw [← iterateFrobenius_one]
  simpa using mapValue_iterateFrobenius_eq_comp_powEnd p 1 q

/-- An `A`-valued point of an integral split torus is fixed by the `n`-fold Frobenius exactly
when each of its coordinates is fixed by the power map of exponent `p ^ n`. -/
theorem mapValue_iterateFrobenius_eq_self_iff
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (groupScheme ℤ sigma).X) :
    (Spec.map (CommRingCat.ofHom (iterateFrobenius A p n).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q = q ↔
      ∀ i, schemePointsMulEquiv (R := ℤ) (A := A) q i ^ ((p ^ n : ℕ) : ℤ) =
        schemePointsMulEquiv (R := ℤ) (A := A) q i := by
  rw [mapValue_iterateFrobenius_eq_comp_powEnd]
  constructor
  · intro h i
    have hi := congrArg (fun r => schemePointsMulEquiv (R := ℤ) (A := A) r i) h
    simpa using hi
  · intro h
    refine (schemePointsMulEquiv (R := ℤ) (A := A) (sigma := sigma)).injective ?_
    funext i
    rw [schemePointsMulEquiv_powEnd]
    exact h i

end TauCeti.SplitTorus
