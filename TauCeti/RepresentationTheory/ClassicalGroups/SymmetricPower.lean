/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
public import TauCeti.RepresentationTheory.SymmetricPower
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete

/-!
# Symmetric powers of the standard representation

This file specializes symmetric powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure symmetric
tensor.

A diagonal matrix acts diagonally on the basis of `Sym[k]^d (Fin n → k)` given by the unordered
`d`-tuples of standard basis vectors, with eigenvalue the product of the corresponding diagonal
entries. Summing those eigenvalues, the character of the `d`th symmetric power at a diagonal
matrix is the `d`th complete homogeneous symmetric polynomial in its diagonal entries, dual to the
elementary symmetric polynomial the exterior power gives.

## Main definitions

* `TauCeti.symPowerRep` is the symmetric-power representation of `GL n k`.
* `TauCeti.symPowerFDRep` is its bundled finite-dimensional form.

## Main results

* `TauCeti.char_symPowerRep_diagonal` identifies the character on diagonal matrices with a
  complete homogeneous symmetric polynomial.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* The standard-representation specialization is adapted from the formal template in
  `TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower`.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

variable (k : Type) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th symmetric power of the standard representation of `GL n k`. -/
noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  (stdRep k n).symmetricPower d

/-- The symmetric power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev symPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (symPowerRep k n d)

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerRep_diagonal (t : Fin n → kˣ) : (symPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  rw [Representation.character, Representation.symmetricPower_apply,
    SymmetricPower.trace_map_of_apply_basis (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) d (stdRep_diagGL_apply_basisFun t)]
  -- both sides sum, over the unordered `d`-tuples of indices, the product of the entries listed
  rw [eval_hsymm]

/-- The character of the bundled `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerFDRep_diagonal (t : Fin n → kˣ) : (symPowerFDRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_symPowerRep_diagonal k n d t

end Field

end TauCeti
