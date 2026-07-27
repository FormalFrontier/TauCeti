/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.TensorPower

/-!
# Tensor powers of the standard representation

This file specializes the diagonal tensor-power construction to the standard representation of
the general linear group. It supplies the tensor powers that underpin the Weyl construction for
polynomial representations.

## Main definitions

* `TauCeti.tensorPowerRep` is the `d`-fold tensor power of `stdRep`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md), Layer 1, “The tensor power representation”.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The diagonal action of `GL n k` on the `d`-fold tensor power of its standard representation. -/
noncomputable abbrev tensorPowerRep :
    Representation k (GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (stdRep k n).tensorPower d

end CommRing

section Field

variable [Field k]

/-- The character of the tensor power is the corresponding power of the standard character. -/
@[simp]
theorem char_tensorPowerRep (g : GL (Fin n) k) :
    (tensorPowerRep k n d).character g = ((stdRep k n).character g) ^ d := by
  exact Representation.char_tensorPower (stdRep k n) d g

end Field

end TauCeti
