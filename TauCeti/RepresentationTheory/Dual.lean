/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character

/-!
# Invariants of the dual representation

The dual `ρ.dual` of a representation acts on functionals by `ψ ↦ ψ ∘ ρ g⁻¹`, so a functional
invariant for it is exactly one that the action of `G` on the space leaves unchanged:
`ψ (ρ g u) = ψ u`.  That characterization of membership in `ρ.dual.invariants` is all a
construction out of an invariant functional, or of one, ever needs.

Counting those invariants needs the character machinery.  The character of the dual is the
character of `ρ` read along `g⁻¹`, and summing over the group is unchanged by inversion, so the two
averages agree: the dual has as many invariants as the representation itself.  Averaging characters
produces identities in `k` and nothing more, so that count is stated first in `k`, needing only an
invertible `|G|`; in characteristic `p` it is an identity of residues, and it is the injectivity of
`ℕ → k` in characteristic zero that turns it into an equality of dimensions.

## Main results

* `TauCeti.Representation.mem_invariants_dual_iff`: a functional is invariant for `ρ.dual` exactly
  when the action of `G` leaves it unchanged, with
  `TauCeti.Representation.apply_of_mem_invariants_dual` the elimination direction.
* `TauCeti.Representation.finrank_invariants_dual`: **the dual of a representation has as many
  invariants as the representation**, as an identity in `k` whenever `|G|` is invertible
  (`TauCeti.Representation.finrank_invariants_dual_cast`) and as natural numbers in characteristic
  zero.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7, “Invariant bilinear forms”: the invariant forms of `ρ` are the intertwiners into
  `ρ.dual`, so counting them is counting invariants of a dual.
-/

public section

namespace TauCeti

open Module (finrank)

namespace Representation

/-! ### Invariant functionals -/

section Group

variable {k G V : Type*} [CommRing k] [Group G] [AddCommMonoid V] [Module k V]

/-- **A functional is invariant for the dual of a representation exactly when the action of `G`
leaves it unchanged.** -/
theorem mem_invariants_dual_iff {ρ : Representation k G V} {ψ : Module.Dual k V} :
    ψ ∈ ρ.dual.invariants ↔ ∀ (g : G) (u : V), ψ (ρ g u) = ψ u := by
  constructor
  · intro hψ g u
    have h := DFunLike.congr_fun (hψ g⁻¹) u
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h
  · refine fun h g => LinearMap.ext fun u => ?_
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h g⁻¹ u

/-- A functional invariant for the dual of a representation is unchanged by the action. -/
@[grind =]
theorem apply_of_mem_invariants_dual {ρ : Representation k G V} {ψ : Module.Dual k V}
    (hψ : ψ ∈ ρ.dual.invariants) (g : G) (u : V) : ψ (ρ g u) = ψ u :=
  mem_invariants_dual_iff.mp hψ g u

end Group

/-! ### Counting the invariants of a dual -/

section Finite

variable {k G V : Type*} [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **The dual of a representation has as many invariants as the representation**, as an identity
in `k`: both counts average the same character, one along `g` and the other along `g⁻¹`.

Averaging characters only ever produces identities in `k`.  In characteristic `p` this is one of
residues; see `TauCeti.Representation.finrank_invariants_dual` for the characteristic-zero form,
where the two counts agree as natural numbers. -/
theorem finrank_invariants_dual_cast [Invertible (Nat.card G : k)] (ρ : Representation k G V) :
    (finrank k ρ.dual.invariants : k) = (finrank k ρ.invariants : k) := by
  have : Fintype G := Fintype.ofFinite G
  rw [← Representation.card_inv_mul_sum_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank]
  refine congrArg _ ?_
  simp only [Representation.char_dual]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl

/-- **The dual of a representation has as many invariants as the representation**, as natural
numbers.  Characteristic zero is what lifts
`TauCeti.Representation.finrank_invariants_dual_cast` from an identity in `k`. -/
theorem finrank_invariants_dual [CharZero k] (ρ : Representation k G V) :
    finrank k ρ.dual.invariants = finrank k ρ.invariants := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact_mod_cast finrank_invariants_dual_cast ρ

end Finite

end Representation

end TauCeti
