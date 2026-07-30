/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
public import TauCeti.RepresentationTheory.ExteriorPower
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Exterior powers of the standard representation

This file specializes exterior powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure wedge.

## Main definitions

* `TauCeti.extPowerRep` is the exterior-power representation of `GL n k`.
* `TauCeti.extPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.char_extPowerRep_diagonal` identifies its character on diagonal matrices with an
  elementary symmetric polynomial.

Importing this file also makes `exteriorPower.eq_zero_of_finrank_lt` available, which says that
`⋀[k]^d (Fin n → k)`, and hence `extPowerRep k n d`, is zero once `n < d`. The degree-zero and
degree-one identifications of `extPowerRep k n` are the generic
`(stdRep k n).exteriorPowerZeroEquiv` and `(stdRep k n).exteriorPowerOneEquiv`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th exterior power of the standard representation of `GL n k`. -/
noncomputable abbrev extPowerRep :
    Representation k (GL (Fin n) k) (⋀[k]^d (Fin n → k)) :=
  (stdRep k n).exteriorPower d

/-- The exterior power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev extPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (extPowerRep k n d)

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th exterior power on a diagonal matrix is the `d`th elementary
symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_extPowerRep_diagonal (t : Fin n → kˣ) :
    (extPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.esymm (Fin n) k d) := by
  rw [Representation.character, Representation.exteriorPower_apply]
  rw [exteriorPower.trace_map_of_apply_basis (Pi.basisFun k (Fin n))
    (stdRep k n (diagGL t)) (fun i => (t i : k)) d
    (stdRep_diagGL_apply_basisFun t)]
  simp only [MvPolynomial.esymm, MvPolynomial.eval_sum, MvPolynomial.eval_prod,
    MvPolynomial.eval_X]
  -- Both sides sum the same products over the `d`-element subsets of `Fin n`, indexed by
  -- `Set.powersetCard` on the left and by `Finset.powersetCard` on the right.
  exact (Finset.sum_subtype (Finset.powersetCard d Finset.univ)
    (fun _ => Finset.mem_powersetCard_univ) fun s => ∏ i ∈ s, (t i : k)).symm

end Field

end TauCeti
