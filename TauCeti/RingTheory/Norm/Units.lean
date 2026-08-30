/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs

/-!
# The norm on unit groups

The norm `Algebra.norm R : S →* R` of an `R`-algebra is multiplicative, so it sends units to
units. `TauCeti.Algebra.normUnits` packages that as a homomorphism `Sˣ →* Rˣ`. This is the form a
statement about the norm of an invertible element wants: the value is a unit by construction, so
no choice of proof that it is nonzero has to be carried alongside it.

No finiteness hypothesis is needed here, because `Algebra.norm` itself has none: it is the
determinant of multiplication, which is `1` when `S` is not module-finite over `R`
(`Algebra.norm_eq_one_of_not_module_finite`). A consumer that cares about the value — for instance
the non-split torus of `GL₂` in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NonSplitTorus.lean` — supplies its own
finiteness where the value is computed.

## Main definitions

* `TauCeti.Algebra.normUnits`: the algebra norm read as a homomorphism `Sˣ →* Rˣ`.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R] {S : Type*} [Ring S] [Algebra R S]

/-- **The norm as a homomorphism of unit groups.** The norm of a unit is a unit, because the norm
is multiplicative; this is `Algebra.norm R` read as a map `Sˣ →* Rˣ`. -/
noncomputable def Algebra.normUnits : Sˣ →* Rˣ :=
  Units.map (Algebra.norm R : S →* R)

/-- The value underlying `TauCeti.Algebra.normUnits` is the ordinary norm. -/
@[simp]
theorem Algebra.coe_normUnits (x : Sˣ) : (Algebra.normUnits R x : R) = Algebra.norm R (x : S) := by
  simp [Algebra.normUnits]

end TauCeti
