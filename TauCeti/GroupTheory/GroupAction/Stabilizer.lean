/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of stabilisers under the two standard transports

A count defined through a point stabiliser is useful only alongside the rules for moving it.
Two such rules are recorded here, both consequences of Mathlib machinery rather than new
mathematics, and both stated for `Nat.card` because that is the form a numerical invariant of
an orbit is wanted in.

*Along an orbit* the stabiliser order does not change: related points have conjugate
stabilisers, by `MulAction.stabilizerEquivStabilizerOfOrbitRel`.

*Along a surjection* it divides: if `f : G →* H` is onto and the two actions agree at the point
in question, then the `G`-order of that point's stabiliser is `Nat.card f.ker` times its
`H`-order. Taking `f` to be a quotient map gives the projective case, where the divisor is the
subgroup quotiented out.

## Main results

* `TauCeti.card_stabilizer_of_orbitRel`: the stabiliser order is an invariant of the orbit,
  with `TauCeti.card_stabilizer_smul` the translate-presented corollary.
* `TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer`: the stabiliser order divides by
  `Nat.card f.ker` along a surjection `f`, with
  `TauCeti.card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient` the quotient-map
  corollary.
-/

public section

namespace TauCeti

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The order of a stabiliser is constant along an orbit**: points related by the orbit
relation have conjugate stabilisers, hence stabilisers of equal cardinality.

This is what lets a count defined through a point stabiliser — the order `e_P` of an elliptic
point of a Fuchsian group, say — be read as an invariant of the orbit. It holds with no
finiteness hypothesis: for an infinite stabiliser both sides are `0`, by `Nat.card`'s
convention. -/
theorem card_stabilizer_of_orbitRel {a b : α} (h : MulAction.orbitRel G α a b) :
    Nat.card (MulAction.stabilizer G a) = Nat.card (MulAction.stabilizer G b) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

/-- The orbit invariance of `card_stabilizer_of_orbitRel` in the form wanted when the second
point is presented as a translate of the first.

Not `@[simp]`: whether `Nat.card (MulAction.stabilizer G (g • a))` is in normal form depends on
the action, since a `simp` lemma for the particular `•` can rewrite inside it. -/
theorem card_stabilizer_smul (g : G) (a : α) :
    Nat.card (MulAction.stabilizer G (g • a)) = Nat.card (MulAction.stabilizer G a) :=
  card_stabilizer_of_orbitRel (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit a g))

/-- **A surjection of acting groups divides stabiliser orders by its kernel**: if `f : G →* H`
is surjective and the `H`-action agrees with the `G`-action along `f` *at the point `a`*, then
the stabiliser of `a` in `G` is `Nat.card f.ker` times its stabiliser in `H`.

Compatibility is asked for only at `a`, not globally, since that is all the count needs; a
caller holding the global statement supplies `fun g ↦ h g a`. -/
theorem card_stabilizer_eq_card_ker_mul_card_stabilizer {H : Type*} [Group H] [MulAction H α]
    (f : G →* H) (hf : Function.Surjective f) (a : α) (hcompat : ∀ g : G, f g • a = g • a) :
    Nat.card (MulAction.stabilizer G a) =
      Nat.card f.ker * Nat.card (MulAction.stabilizer H a) := by
  -- `QuotientGroup.preimageMkEquivSubgroupProdSet` would shorten this, but it is stated only
  -- for `QuotientGroup.mk`; at this generality the kernel-and-Lagrange chain is the route, and
  -- the whole of it rests on this one transport, used in both directions.
  have hmem : ∀ g : G, g ∈ MulAction.stabilizer G a ↔ f g ∈ MulAction.stabilizer H a :=
    fun g ↦ by simp [MulAction.mem_stabilizer_iff, hcompat g]
  have hle : f.ker ≤ MulAction.stabilizer G a := fun n hn ↦
    (hmem n).mpr (by simp [MonoidHom.mem_ker.mp hn])
  let φ : MulAction.stabilizer G a →* MulAction.stabilizer H a :=
    (f.comp (MulAction.stabilizer G a).subtype).codRestrict _ fun g ↦ (hmem _).mp g.2
  have hsurj : Function.Surjective φ := fun ⟨q, hq⟩ ↦ by
    obtain ⟨g, rfl⟩ := hf q
    -- `rfl` here is the `codRestrict`/`Subtype.val` unfolding of `φ`
    exact ⟨⟨g, (hmem g).mpr hq⟩, rfl⟩
  have hker : φ.ker = f.ker.subgroupOf (MulAction.stabilizer G a) :=
    MonoidHom.ker_codRestrict _ _ _
  rw [← φ.ker.card_mul_index, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  simp

/-- **Passing to a quotient group divides stabiliser orders by the subgroup**: the case of
`card_stabilizer_eq_card_ker_mul_card_stabilizer` for the quotient map, whose kernel is `N`.

This is the step from a matrix-group stabiliser order to the projective one. The divisor is
`Nat.card N` in general; for `SL(2, ℤ) ↠ PSL(2, ℤ)` that is the centre `±1`, so there the
elliptic orders `e_P` are the matrix counts halved. For a Fuchsian `Γ` with `-I ∉ Γ` the two
counts coincide. -/
theorem card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient (N : Subgroup G) [N.Normal]
    [MulAction (G ⧸ N) α] (a : α)
    (hcompat : ∀ g : G, (QuotientGroup.mk g : G ⧸ N) • a = g • a) :
    Nat.card (MulAction.stabilizer G a) =
      Nat.card N * Nat.card (MulAction.stabilizer (G ⧸ N) a) := by
  have h := card_stabilizer_eq_card_ker_mul_card_stabilizer (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) a hcompat
  rwa [QuotientGroup.ker_mk'] at h

end TauCeti

end
