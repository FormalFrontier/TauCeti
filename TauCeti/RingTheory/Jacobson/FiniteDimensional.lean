/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Ring

/-!
# The Jacobson radical of a finite-dimensional algebra

This file packages the standard Artinian-ring API for finite-dimensional algebras over a field.
For such an algebra `A`, its Jacobson radical is nilpotent, the quotient by the radical is
semisimple, and `A` itself is semisimple exactly when the radical vanishes.

Mathlib proves all three statements for an arbitrary left Artinian ring. The only bridge supplied
here is the standard implication from finite-dimensionality over a field to the Artinian condition,
via `IsArtinianRing.of_finite`. The mathematical inputs are:

* `IsArtinianRing.isSemisimpleRing_iff_jacobson`, the semisimplicity criterion;
* `IsArtinianRing.isNilpotent_jacobson_bot`, nilpotence of the radical; and
* `Ring.jacobson_quotient_jacobson`, vanishing of the radical after quotienting by it.

## Main results

* `TauCeti.isSemisimpleRing_iff_jacobson_eq_bot`: a finite-dimensional algebra is semisimple if
  and only if its Jacobson radical is zero.
* `TauCeti.isNilpotent_jacobson`: the Jacobson radical of a finite-dimensional algebra is
  nilpotent.
* `TauCeti.isSemisimpleRing_quotient_jacobson`: the quotient of a finite-dimensional algebra by
  its Jacobson radical is semisimple.
-/

public section

namespace TauCeti

universe u v

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

include K

/-- A finite-dimensional algebra over a field is semisimple if and only if its Jacobson radical
vanishes. This is the Artinian semisimplicity criterion, with Artinianity supplied by finite
dimensionality. -/
theorem isSemisimpleRing_iff_jacobson_eq_bot :
    IsSemisimpleRing A ↔ Ring.jacobson A = ⊥ := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact IsArtinianRing.isSemisimpleRing_iff_jacobson

/-- The Jacobson radical of a finite-dimensional algebra over a field is nilpotent. -/
theorem isNilpotent_jacobson : IsNilpotent (Ring.jacobson A) := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  simpa only [Ideal.jacobson_bot] using
    (IsArtinianRing.isNilpotent_jacobson_bot (R := A))

/-- The quotient of a finite-dimensional algebra by its Jacobson radical is semisimple. -/
theorem isSemisimpleRing_quotient_jacobson :
    IsSemisimpleRing (A ⧸ Ring.jacobson A) := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
    (Ring.jacobson_quotient_jacobson A)

end TauCeti
