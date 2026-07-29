/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.ExteriorPower

/-!
# Exterior powers of the standard representation

This file specializes exterior powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure wedge.

## Main definitions

* `TauCeti.extPowerRep` is the exterior-power representation of `GL n k`.
* `TauCeti.extPowerFDRep` is its bundled finite-dimensional form.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
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

/-- A matrix acts on a pure wedge by acting on every factor. -/
@[simp]
theorem extPowerRep_apply_ιMulti (g : GL (Fin n) k) (m : Fin d → Fin n → k) :
    extPowerRep k n d g (_root_.exteriorPower.ιMulti k d m) =
      _root_.exteriorPower.ιMulti k d (stdRep k n g ∘ m) :=
  Representation.exteriorPower_apply_ιMulti (stdRep k n) d g m

/-- The zeroth exterior power of the standard representation is trivial. -/
noncomputable abbrev extPowerRepZeroEquiv :
    (extPowerRep k n 0).Equiv (Representation.trivial k (GL (Fin n) k) k) :=
  (stdRep k n).exteriorPowerZeroEquiv

/-- The first exterior power of the standard representation is the standard representation. -/
noncomputable abbrev extPowerRepOneEquiv :
    (extPowerRep k n 1).Equiv (stdRep k n) :=
  (stdRep k n).exteriorPowerOneEquiv

end CommRing

section Field

variable [Field k]

/-- The exterior power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev extPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (extPowerRep k n d)

/-- An exterior power above the dimension of the standard representation is zero. -/
theorem extPowerRep_eq_zero_of_lt (h : n < d) (x : ⋀[k]^d (Fin n → k)) :
    x = 0 := by
  apply _root_.exteriorPower.eq_zero_of_finrank_lt d
  simpa using h

end Field

end TauCeti
