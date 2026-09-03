/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowMonoidHom

/-!
# The group of `n`th power classes `G ⧸ Gⁿ`

For a commutative group `G` the subgroup `Gⁿ` of `n`th powers is the range of `powMonoidHom n`,
and this file names it together with the quotient `G ⧸ Gⁿ` and the class of an element. At `n = 2`
the subgroup is Mathlib's `Subgroup.square G`, by `TauCeti.square_eq_powMonoidHom_two_range`.

## Main definitions

* `TauCeti.powerSubgroup`: the subgroup `Gⁿ ≤ G`, whose elements are characterised as the `n`th
  powers by `TauCeti.mem_powerSubgroup_iff`.
* `TauCeti.powerClassQuotient`, `TauCeti.powerClassHom`: the quotient `G ⧸ Gⁿ` and the map taking
  an element to its power class. It is surjective (`TauCeti.powerClassHom_surjective`) with kernel
  `Gⁿ` (`TauCeti.ker_powerClassHom`), so it presents `G ⧸ Gⁿ` as the quotient of `G` by the `n`th
  powers.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] (n : ℕ)

/-- **The subgroup of `n`th powers** `Gⁿ ≤ G`. -/
def powerSubgroup : Subgroup G :=
  (powMonoidHom n : G →* G).range

/-- **The group of `n`th power classes** `G ⧸ Gⁿ`. -/
abbrev powerClassQuotient : Type _ :=
  G ⧸ powerSubgroup G n

/-- The quotient homomorphism `G → G ⧸ Gⁿ`. -/
def powerClassHom : G →* powerClassQuotient G n :=
  QuotientGroup.mk' (powerSubgroup G n)

/-- The kernel of the power-class homomorphism is the subgroup `Gⁿ` of `n`th powers. -/
@[simp]
theorem ker_powerClassHom : (powerClassHom G n).ker = powerSubgroup G n :=
  QuotientGroup.ker_mk' (powerSubgroup G n)

/-- Every power class is the class of an element: `powerClassHom` is surjective. -/
theorem powerClassHom_surjective : Function.Surjective (powerClassHom G n) :=
  QuotientGroup.mk'_surjective (powerSubgroup G n)

variable {G}

/-- The power-class homomorphism sends `g` to its quotient class. -/
@[simp]
theorem powerClassHom_apply (g : G) : powerClassHom G n g = QuotientGroup.mk g := by
  exact QuotientGroup.mk'_apply (powerSubgroup G n) g

/-- An element belongs to `Gⁿ` exactly when it is an `n`th power. -/
@[simp]
theorem mem_powerSubgroup_iff {g : G} : g ∈ powerSubgroup G n ↔ ∃ h : G, h ^ n = g := by
  rw [powerSubgroup, MonoidHom.mem_range]
  exact exists_congr fun h => by rw [powMonoidHom_apply]

end TauCeti
