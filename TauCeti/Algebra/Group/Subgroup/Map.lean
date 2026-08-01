/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Injectivity of the comparison map to a preimage subgroup

Mathlib's `MonoidHom.subgroupComap` sends the preimage `K.comap f` of a subgroup `K` to `K`.
Mathlib records that this map is surjective when `f` is
(`MonoidHom.subgroupComap_surjective_of_surjective`); this file records the companion fact for
injectivity.

## Main results

* `TauCeti.MonoidHom.subgroupComap_injective_of_injective`: `f.subgroupComap K` is injective when
  `f` is.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- The comparison map from the preimage of a subgroup to that subgroup is injective as soon as the
underlying homomorphism is. Companion to Mathlib's
`MonoidHom.subgroupComap_surjective_of_surjective`. -/
theorem MonoidHom.subgroupComap_injective_of_injective {f : H →* G} (hf : Function.Injective f)
    (K : Subgroup G) : Function.Injective (f.subgroupComap K) :=
  fun _ _ hxy => Subtype.ext (hf (congrArg Subtype.val hxy))

end TauCeti
