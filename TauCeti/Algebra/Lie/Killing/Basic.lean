/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing

/-!
# The Killing property as nondegeneracy of the Killing form

`LieAlgebra.IsKilling R L` is stated as the vanishing of the Killing orthogonal complement of the
whole algebra. Mathlib turns that into nondegeneracy of the Killing form in
`LieAlgebra.IsKilling.killingForm_nondegenerate`; this file supplies the converse, so that the two
together say that `LieAlgebra.IsKilling` is exactly nondegeneracy of the Killing form. That is the
form in which the property is recognised when it is produced by a computation with the form itself,
as under base change.

## Main declarations

* `TauCeti.isKilling_of_killingForm_nondegenerate`: a Lie algebra whose Killing form is
  nondegenerate is Killing.

## Roadmap

This supports `TauCeti/Algebra/Lie/Killing/BaseChange.lean`, a prerequisite for Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, the Chevalley--Demazure construction.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.1, for the Killing
  form and Cartan's criterion.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra whose Killing form is nondegenerate is Killing.

This is the converse of `LieAlgebra.IsKilling.killingForm_nondegenerate`, and the two together say
that `LieAlgebra.IsKilling` is exactly nondegeneracy of the Killing form. -/
theorem isKilling_of_killingForm_nondegenerate (h : (killingForm R L).Nondegenerate) :
    IsKilling R L :=
  ⟨(LieSubmodule.toSubmodule_eq_bot _).mp <|
    (LieIdeal.coe_killingCompl_top R L).trans h.ker_eq_bot⟩

end TauCeti
