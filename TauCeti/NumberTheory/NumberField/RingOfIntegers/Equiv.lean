/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Equivalences of rings of integers

An algebra equivalence between fields restricts to an algebra equivalence between their rings of
integers. This file records the compatibility of that induced equivalence with the ambient map and
its inverse.

## Main results

* `NumberField.RingOfIntegers.mapAlgEquiv_apply`: the induced equivalence agrees with the ambient
  algebra equivalence after coercion to the field.
* `NumberField.RingOfIntegers.mapAlgEquiv_symm_apply`: the inverse induced equivalence agrees with
  the ambient inverse after coercion to the field.
* `NumberField.RingOfIntegers.mapAlgEquiv_symm`: the induced equivalence of an inverse is the
  inverse induced equivalence.
-/

public section

open scoped NumberField

namespace NumberField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

namespace RingOfIntegers

/-- The induced ring-of-integers equivalence agrees with the ambient algebra equivalence. -/
@[simp]
theorem mapAlgEquiv_apply (e : L ≃ₐ[K] L') (x : 𝓞 L) :
    (mapAlgEquiv e x : L') = e (x : L) := rfl

/-- The inverse induced ring-of-integers equivalence agrees with the ambient inverse. -/
@[simp]
theorem mapAlgEquiv_symm_apply (e : L ≃ₐ[K] L') (x : 𝓞 L') :
    ((mapAlgEquiv e).symm x : L) = e.symm (x : L') := rfl

/-- The induced ring-of-integers equivalence for an inverse is the inverse equivalence. -/
@[simp]
theorem mapAlgEquiv_symm (e : L ≃ₐ[K] L') :
    (mapAlgEquiv e).symm = mapAlgEquiv e.symm := by
  apply AlgEquiv.ext
  intro x
  apply RingOfIntegers.ext
  rfl

end RingOfIntegers

end NumberField
