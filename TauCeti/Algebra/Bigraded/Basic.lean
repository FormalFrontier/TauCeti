/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Bigraded Poincaré series

This file defines the Poincaré series of a finite-dimensional bigraded vector space, together
with its total dimension and Alexander-graded Euler characteristic.

## Main definitions

* `TauCeti.Bigraded.Series`: the Poincaré series of a finite-dimensional bigraded vector space.
* `TauCeti.Bigraded.totalDim`: the total dimension, as a ring homomorphism.
* `TauCeti.Bigraded.euler`: the Alexander-graded Euler characteristic.
-/

public section

namespace TauCeti

namespace Bigraded

open AddMonoidAlgebra

/-- The Poincaré series of a finite-dimensional bigraded vector space: the dimension of the
summand in each bidegree `(Maslov, Alexander)`, all but finitely many of them zero.

Over a field, a bigraded vector space with only finitely many nonzero finite-dimensional summands
is determined up to bigraded isomorphism by this function, and the product is the Poincaré series
of the tensor product. -/
abbrev Series : Type := AddMonoidAlgebra ℕ (ℤ × ℤ)

section TotalDim

/-- The total dimension of a finite-dimensional bigraded vector space, as a ring homomorphism:
the tensor product multiplies total dimensions. -/
noncomputable def totalDim : Series →+* ℕ :=
  liftNCRingHom (RingHom.id ℕ) (1 : Multiplicative (ℤ × ℤ) →* ℕ) fun _ _ => Commute.all _ _

/-- The total dimension is the sum of the dimensions of all the bigraded summands. -/
theorem totalDim_apply (P : Series) : totalDim P = P.coeff.sum fun _ c => c := by
  simp [totalDim, liftNCRingHom, AddMonoidAlgebra.liftNC]

/-- The total dimension of a series concentrated in one bidegree. -/
@[simp]
theorem totalDim_single (g : ℤ × ℤ) (r : ℕ) : totalDim (single g r) = r := by
  simp [totalDim]

/-- Only the zero series has total dimension zero. -/
@[simp]
theorem totalDim_eq_zero_iff (P : Series) : totalDim P = 0 ↔ P = 0 := by
  rw [totalDim_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext g
    by_cases hg : g ∈ P.coeff.support
    · simpa using h g hg
    · simpa using Finsupp.notMem_support_iff.mp hg
  · rintro rfl
    simp

end TotalDim

section Euler

open LaurentPolynomial

/-- The Alexander-graded Euler characteristic of a bigraded vector space, as a monoid
homomorphism on bidegrees: bidegree `(m, a)` contributes `(-1)^m T^a`. -/
noncomputable def eulerMonoidHom : Multiplicative (ℤ × ℤ) →* ℤ[T;T⁻¹] where
  toFun g := single g.toAdd.2 (g.toAdd.1.negOnePow : ℤ)
  map_one' := rfl
  map_mul' g h := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Int.negOnePow_add, Units.val_mul,
      single_mul_single]

/-- The Alexander-graded Euler characteristic of a finite-dimensional bigraded vector space: the
Laurent polynomial whose `T^a` coefficient is the alternating sum, over the Maslov grading, of
the dimensions in Alexander grading `a`.

This is a ring homomorphism, so it turns the tensor product into a product of Laurent
polynomials. -/
noncomputable def euler : Series →+* ℤ[T;T⁻¹] :=
  liftNCRingHom (Nat.castRingHom _) eulerMonoidHom fun _ _ => Commute.all _ _

/-- The Euler characteristic of a series concentrated in one bidegree. -/
@[simp]
theorem euler_single (m a : ℤ) (r : ℕ) :
    euler (single (m, a) r) = (r : ℤ[T;T⁻¹]) * single a (m.negOnePow : ℤ) :=
  liftNCRingHom_single _ _ _ _ _

end Euler

end Bigraded

end TauCeti
