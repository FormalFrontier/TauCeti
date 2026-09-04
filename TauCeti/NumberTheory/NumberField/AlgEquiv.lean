/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.Unramified.AlgEquiv

/-!
# Transport between isomorphic number-field extensions

This file records how properties of primes of rings of integers transport along an isomorphism
of field extensions.

## Main results

* `AlgEquiv.forall_isUnramifiedAt_iff`: unramifiedness above a base prime is invariant under an
  isomorphism of extensions.
-/

public section

open scoped NumberField

namespace AlgEquiv

variable {K L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']

/-- **Unramifiedness above `𝔭` does not depend on the model of the extension.** -/
theorem forall_isUnramifiedAt_iff (e : L ≃ₐ[K] L') (𝔭 : Ideal (𝓞 K)) :
    (∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q) ↔
      ∀ (Q : Ideal (𝓞 L')) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q := by
  constructor
  · intro h Q _ _
    have hQ : (Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e)).comap
        (NumberField.RingOfIntegers.mapAlgEquiv e).symm = Q :=
      Ideal.comap_of_equiv (NumberField.RingOfIntegers.mapAlgEquiv e).symm.toRingEquiv
    have _ : Algebra.IsUnramifiedAt (𝓞 K)
        (Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e)) := h _
    exact (NumberField.RingOfIntegers.mapAlgEquiv e).symm.isUnramifiedAt_of_eq_comap hQ.symm
  · intro h Q _ _
    have hQ : (Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e).symm).comap
        (NumberField.RingOfIntegers.mapAlgEquiv e) = Q :=
      Ideal.comap_of_equiv (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv
    have _ : Algebra.IsUnramifiedAt (𝓞 K)
        (Q.comap (NumberField.RingOfIntegers.mapAlgEquiv e).symm) := h _
    exact (NumberField.RingOfIntegers.mapAlgEquiv e).isUnramifiedAt_of_eq_comap hQ.symm

end AlgEquiv
