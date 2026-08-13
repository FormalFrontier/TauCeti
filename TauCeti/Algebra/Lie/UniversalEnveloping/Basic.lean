/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# Basic properties of universal enveloping algebras

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ι_mul_sub_mul`: canonical Lie generators satisfy their
  defining commutator relation.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type*) [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical map to the universal enveloping algebra turns a Lie bracket into an associative
ring commutator. -/
theorem ι_mul_sub_mul (x y : L) :
    _root_.UniversalEnvelopingAlgebra.ι R x * _root_.UniversalEnvelopingAlgebra.ι R y -
      _root_.UniversalEnvelopingAlgebra.ι R y * _root_.UniversalEnvelopingAlgebra.ι R x =
        _root_.UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ := by
  rw [(_root_.UniversalEnvelopingAlgebra.ι R).map_lie x y,
    LieRing.of_associative_ring_bracket]

end TauCeti.UniversalEnvelopingAlgebra
