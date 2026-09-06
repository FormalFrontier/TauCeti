/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius

/-!
# Restriction of arithmetic Frobenius

An arithmetic Frobenius in a field extension remains an arithmetic Frobenius after restriction
to a normal intermediate extension. More precisely, if `L/M/K` is a tower with `M/K` normal and
`σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, then `σ|_M` is an arithmetic Frobenius at the
contracted prime `Q ∩ 𝓞 M`.

This is the unpowered restriction law: both Frobenius elements are relative to the same base
field `K`, so both act on residue fields by the cardinality of the residue field of the same base
prime. The distinct tower law obtained by raising the base from `K` to `M` involves the inertia
degree as an exponent and is not proved here.

The argument follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9.

## Main result

* `IsArithFrobAt.restrictNormal`: restriction to a normal intermediate extension preserves the
  arithmetic-Frobenius property at the contracted prime.
-/

public section

open Ideal
open scoped NumberField

namespace IsArithFrobAt

variable {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L]
  [Algebra K L] [IsScalarTower K M L] [Normal K M]

/-- **Arithmetic Frobenius restricts without a power along a normal subextension.**

If `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, its restriction to a normal intermediate
extension `M/K` is an arithmetic Frobenius at `Q ∩ 𝓞 M`. The exponent on both sides is the
cardinality of `𝓞 K` modulo the contraction of `Q`; `Ideal.under_under` identifies the two
contractions. -/
theorem restrictNormal {Q : Ideal (𝓞 L)} {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal M) (Q.under (𝓞 M)) := by
  intro x
  rw [Ideal.mem_under, MulSemiringAction.toAlgHom_apply, map_sub,
    NumberField.algebraMap_restrictNormal_smul, map_pow, Ideal.under_under]
  exact hσ (algebraMap (𝓞 M) (𝓞 L) x)

end IsArithFrobAt
