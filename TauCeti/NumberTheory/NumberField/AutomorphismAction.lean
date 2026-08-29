/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Automorphisms acting on the ring of integers

A ring automorphism of a field restricts to its ring of integers, because it preserves
integrality. This file records how that restricted action relates to the ambient one: the
structure map `𝓞 K → K` is equivariant, carrying `σ • z` to `σ` applied to the image of `z`.

`𝓞 K` is the integral closure of `ℤ`, and any ring automorphism of `K` preserves `ℤ`-integrality,
so the base ring `R` over which `σ` is linear is irrelevant to both statement and proof; it is a
free parameter, specialized to `ℚ` by the callers. Nothing here needs `K` to be finite-dimensional
either, so `[NumberField K]` is not assumed.

This is the `AlgEquiv` specialization of Mathlib's `integralClosure.coe_smul`, which is stated
for an arbitrary `[Group G] [MulSemiringAction G K]` and therefore cannot phrase the right-hand
side as function application. Callers want exactly that applied form, so the specialization is
recorded once here rather than reconstructed at each use site.

## Main results

* `NumberField.algebraMap_smul_eq_apply`: `algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z)`.
-/

public section

open scoped NumberField

namespace NumberField

variable {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]

/-- **`algebraMap` intertwines the automorphism actions on `𝓞 K` and on `K`.** The action on the
ring of integers is the restriction of the action on `K` (`integralClosure.coe_smul`), so the
structure map sends `σ • z` to `σ` applied to the image of `z`.

Not named `algebraMap_smul`: that is Mathlib's unrelated `algebraMap R A r • m = r • m`. -/
@[simp] theorem algebraMap_smul_eq_apply (σ : K ≃ₐ[R] K) (z : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z) :=
  -- `integralClosure.coe_smul` proves this up to two definitional identifications:
  -- `RingOfIntegers.val` is an `abbrev` for `algebraMap`, and `AlgEquiv.smul_def` is `rfl`.
  integralClosure.coe_smul σ z

end NumberField
