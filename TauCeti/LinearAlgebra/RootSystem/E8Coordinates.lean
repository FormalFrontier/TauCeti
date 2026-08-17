/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# The Bourbaki coordinate model of type `E₈`

The simple roots of type `E₈` have half-integral coordinates in the orthonormal basis
`ε₁, ..., ε₈` of Bourbaki's Plate VII, so the table recorded here is twice them: row `i` of
`TauCeti.DynkinType.e8DoubledSimpleRoot` is twice the `i`-th simple root, which makes all entries
integers. `E₈` being simply laced, the same rows are twice the simple coroots.

This is the single coordinate model of type `E₈` in the library, and it is integral so that both
of its consumers can read what they need off it: the finite-type proof
`TauCeti.DynkinType.isFiniteType_cartanMatrix_E8` scales it back by one half over `ℚ`, and the
completeness of the coroot enumeration in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice` uses it as it stands, the
doubling being exactly what makes the Euclidean lattice `2 · Γ₈` there integral.

Three properties of the table are recorded, all checked by `decide`: the Gram matrix of the rows is
four times the `E₈` Cartan matrix, the factor four coming from the doubling, and the rows satisfy
the two congruences describing `2 · Γ₈`, namely that the entries of a row agree modulo two and that
its coordinate sum is divisible by four.

## Main definitions

* `TauCeti.DynkinType.e8DoubledSimpleRoot`

## References

The coordinates and the node numbering are Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VII. See also Humphreys, *Introduction to Lie Algebras and Representation Theory*,
Chapter 11.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-- The doubled Bourbaki simple roots of type `E₈`: row `i` is twice the `i`-th simple root of
Plate VII, in the orthonormal coordinates of the model, so that all entries are integers. -/
def e8DoubledSimpleRoot : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 1, -1, -1, -1, -1, -1, -1,  1;
      2,  2,  0,  0,  0,  0,  0,  0;
     -2,  2,  0,  0,  0,  0,  0,  0;
      0, -2,  2,  0,  0,  0,  0,  0;
      0,  0, -2,  2,  0,  0,  0,  0;
      0,  0,  0, -2,  2,  0,  0,  0;
      0,  0,  0,  0, -2,  2,  0,  0;
      0,  0,  0,  0,  0, -2,  2,  0]

/-- The doubled simple roots have the `E₈` Cartan matrix as their Gram matrix, up to the factor
four that doubling introduces. -/
lemma e8DoubledSimpleRoot_mul_transpose :
    e8DoubledSimpleRoot * e8DoubledSimpleRootᵀ = (4 : ℤ) • CartanMatrix.E₈ := by decide

private lemma e8DoubledSimpleRoot_sub_emod :
    ∀ i j : Fin 8, (e8DoubledSimpleRoot i j - e8DoubledSimpleRoot i 0) % 2 = 0 := by decide

private lemma e8DoubledSimpleRoot_sum_emod :
    ∀ i : Fin 8, (∑ j, e8DoubledSimpleRoot i j) % 4 = 0 := by decide

/-- Two entries in the same row of the doubled simple roots are congruent modulo two. -/
theorem e8DoubledSimpleRoot_two_dvd_sub (i j : Fin 8) :
    (2 : ℤ) ∣ e8DoubledSimpleRoot i j - e8DoubledSimpleRoot i 0 :=
  Int.dvd_of_emod_eq_zero (e8DoubledSimpleRoot_sub_emod i j)

/-- Every doubled simple root has coordinate sum divisible by four. -/
theorem e8DoubledSimpleRoot_four_dvd_sum (i : Fin 8) :
    (4 : ℤ) ∣ ∑ j, e8DoubledSimpleRoot i j :=
  Int.dvd_of_emod_eq_zero (e8DoubledSimpleRoot_sum_emod i)

end DynkinType

end TauCeti
