/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum
public import TauCeti.RepresentationTheory.AsAlgebraHom

/-!
# Character sums over a subgroup as operators

The character sum `∑_{h ∈ H} χ(h) h` of `TauCeti.subgroupCharSum` lives in the group algebra
`k[G]`, so it acts on any representation of `G` through `Representation.asAlgebraHom`.  This file
records the two facts every computation with that operator starts from.

Expanding it is immediate from the definition: it acts as the `χ`-weighted sum of the operators
`ρ h` over `h ∈ H` (`TauCeti.asAlgebraHom_subgroupCharSum_apply`).  Its vanishing is the
mechanism behind every antisymmetrizer argument: if some `p ∈ H` has `χ(p⁻¹) = -1`, the sum
absorbs `p` at the cost of a sign, so its value on a vector `p` fixes is its own negative, and
doubling being injective forces that value to be zero
(`TauCeti.asAlgebraHom_subgroupCharSum_apply_eq_zero`).  Injective doubling is the hypothesis of
`Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg`, taken as an assumption rather than
read off the scalars, so no invertibility of `2` in `k` is needed.

## Main results

* `TauCeti.asAlgebraHom_subgroupCharSum_apply`: the character sum acts as `∑_{h ∈ H} χ(h) ρ(h)`;
* `TauCeti.asAlgebraHom_subgroupCharSum_apply_eq_zero`: the character sum annihilates every vector
  fixed by an element of `H` whose inverse has character `-1`.
-/

public section

namespace TauCeti

section Semiring

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- The character sum of `χ` over `H`, acting on a representation, is the `χ`-weighted sum of the
actions of the elements of `H`. -/
theorem asAlgebraHom_subgroupCharSum_apply (ρ : Representation k G V) (v : V) :
    ρ.asAlgebraHom (subgroupCharSum χ H) v = ∑ h : H, χ (h : G) • ρ (h : G) v := by
  rw [subgroupCharSum_def, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun h _ => by
    rw [map_smul, LinearMap.smul_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one]

end Semiring

section Ring

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- **A character sum annihilates whatever an element of character `-1` fixes.**  Right
multiplication by `p ∈ H` rescales the sum by `χ(p⁻¹) = -1`, so the value of the sum on a vector
fixed by `p` is its own negative; with doubling injective it vanishes. -/
theorem asAlgebraHom_subgroupCharSum_apply_eq_zero
    (h2inj : Function.Injective fun w : V => (2 : ℕ) • w) (ρ : Representation k G V) {p : G}
    (hp : p ∈ H) (hχ : χ p⁻¹ = -1) {v : V} (hfix : ρ p v = v) :
    ρ.asAlgebraHom (subgroupCharSum χ H) v = 0 :=
  Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg h2inj ρ hfix
    (by rw [subgroupCharSum_mul_single χ H ⟨p, hp⟩, hχ, neg_one_smul])

end Ring

end TauCeti
