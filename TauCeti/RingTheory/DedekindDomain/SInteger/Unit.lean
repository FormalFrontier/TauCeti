/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import TauCeti.Algebra.Algebra.Subalgebra.Lattice
public import TauCeti.GroupTheory.Finiteness

/-!
# Finite generation of the `S`-units

Mathlib defines the group `Set.unit S K` of `S`-units — the `x : Kˣ` with `v x = 1` for every
`v ∉ S` — and identifies it with the units of the ring of `S`-integers, but says nothing about its
size. Its own module docstring records the gap: `Mathlib/RingTheory/DedekindDomain/SInteger.lean`
lists as future work *"finite generation of `S`-units and Dirichlet's `S`-unit theorem"*, and
`Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` likewise carries *"TODO: proofs of finiteness
for global fields"*. This file supplies the finite-generation half.

## Main results

* `Set.unit_fg`: **if `S` is finite and the `∅`-units are finitely generated, so are the
  `S`-units.**
* `Set.unit_fg_of_units`: the same with the hypothesis over the base ring, `[Monoid.FG Rˣ]` —
  the form the arithmetic actually applies, since a caller holds `Rˣ` and not the `∅`-units. An
  `instance`; the hypothesis is the `Monoid` form because that is the one Mathlib registers for
  `𝒪 K`.
* `Set.unitValuation_ker`: the kernel of the `S`-valuation map is the `∅`-units, which is the
  left-exactness `1 → Rˣ → (S.integer K)ˣ → ∏_{v∈S} ℤ`. This is in the same spirit as the TODO
  `RingTheory/DedekindDomain/SInteger.lean` records — "proof that `S`-units is the kernel of a map
  to a product" — but is not that statement: the map here is defined *on* the `S`-units and its
  kernel is the `∅`-units.

The argument is one application of `Group.fg_of_fg_ker_of_fg_range`. Sending an `S`-unit to its
tuple of valuations at the primes *in* `S` gives `Set.unitValuation`, a homomorphism to `ℤ^S`; its
image is a subgroup of a finitely generated commutative group and so is finitely generated, and its
kernel is the group of `∅`-units (`Set.unitValuation_ker`), which is `Rˣ`
(`Set.unitEmptyEquivUnits`). An extension of finitely generated groups is finitely generated.

`Set.unit_mono` — the `S`-units grow with `S` — is what lets `unit_fg` identify the kernel
subgroup with the `∅`-units along `Subgroup.subgroupOfEquivOfLe`; it is not in Mathlib.

The rank refinement — that the rank is exactly `rank Rˣ + |S|` when the class group is finite — is
a separate topic and is not here.

This is the second of the two finiteness inputs that
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names for the weak Mordell–Weil theorem:
"`A(S, 2)` is finite because the `S`-class group is finite and **the `S`-units are finitely
generated** (AEC VIII.1)."

Throughout, `R` is an *arbitrary* Dedekind domain and `K` its fraction field; `Rˣ` and
`(S.integer K)ˣ` are the unit groups in play. The motivating case is `R = 𝒪_K` for a number
field, but nothing here assumes it, so the ring-of-integers notation is deliberately avoided.

## Relation to mathlib4#40791

**The names, statements and proofs here are taken from the open Mathlib pull request
[mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791), "feat(RingTheory/
DedekindDomain): dirichlet's s-unit theorem", by `vvvv-ops`, open since 2026-06-19**, which adds
`Mathlib/RingTheory/DedekindDomain/SUnit.lean` and proves exactly this (and more: the rank formula
and its number-field specialisation). Following that PR rather than inventing a parallel API is
deliberate — when Mathlib bumps past it, almost all of this file is deleted outright instead of
being reconciled name by name. **`unit_fg_of_units` and
`algebraMap_unitEmptyEquivUnits_apply` are the exceptions: they have no #40791 analogue, so at
bump time they must be re-homed onto Mathlib's `Set.unit_fg`, not dropped with the rest.**

**Four declarations here are not that PR's**, and are marked as such where they occur:

* `mem_unit_iff` is the membership lemma for `Set.unit`, which neither #40791 nor Mathlib states;
  it is the companion of `Set.mem_integer_iff` next door, and `@[simp]` for the same reason.
* `unit_mono` is stated for an arbitrary `S ⊆ S'`, of which #40791's `unit_empty_le` is the
  `S = ∅` case.
* **`unit_fg_of_units` is new here**, with no counterpart in #40791: upstream gives
  `unitEmptyEquivUnits` its consumer in the rank formula, which is not ported, so without this
  form the theorem is awkward to apply — a caller holds `Rˣ`, not the `∅`-units.
* **`algebraMap_unitEmptyEquivUnits_apply` is new here**, with no counterpart in #40791: it is the
  element-level characterisation of the three-fold composite `unitEmptyEquivUnits`, so that a
  future user of that equiv need not unfold it.

The valuation lemma these proofs run on,
`IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_one_iff`, is not here: it mentions no
`S` and no `Set.unit`, so it lives in `TauCeti/RingTheory/DedekindDomain/SelmerGroup.lean`
beside the `valuationOfNeZero` API it belongs to.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at
the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), and then restated to match
mathlib4#40791 as described above. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Set

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `S`-valuation map on `S`-units: `u ↦ (v(u))_{v ∈ S}`, valued in `↥S → Multiplicative ℤ`. -/
noncomputable def unitValuation : S.unit K →* (↥S → Multiplicative ℤ) :=
  MonoidHom.pi fun v ↦ (v : HeightOneSpectrum R).valuationOfNeZero.comp (S.unit K).subtype

@[simp]
theorem unitValuation_apply (u : S.unit K) (v : ↥S) :
    unitValuation S K u v = (v : HeightOneSpectrum R).valuationOfNeZero ((u : Kˣ)) := by
  rfl

/-- Membership in the `S`-units is the valuation condition defining it. Mathlib defines
`Set.unit` as a `Subgroup.copy` of exactly this set-builder but provides no membership lemma, so
this is `Iff.rfl`; naming it means the proofs below go through a characterisation rather than
that definitional unfolding. The companion of `Set.mem_integer_iff` for the other half of the
same API. -/
@[simp] theorem mem_unit_iff {x : Kˣ} :
    x ∈ S.unit K ↔ ∀ v ∉ S, (v : HeightOneSpectrum R).valuation K (x : K) = 1 := Iff.rfl

/-- The `S`-units grow with `S`: enlarging the set of allowed primes only weakens the condition
`v x = 1` for `v ∉ S`. mathlib4#40791's `unit_empty_le` is the case `S = ∅`. -/
theorem unit_mono {S S' : Set (HeightOneSpectrum R)} (h : S ⊆ S') : S.unit K ≤ S'.unit K :=
  fun _ hx ↦ (mem_unit_iff ..).mpr fun v hv ↦ (mem_unit_iff ..).mp hx v fun hvS ↦ hv (h hvS)

/-- **The kernel of the `S`-valuation map is the `∅`-units.** Equivalently, an `S`-unit lies in the
kernel iff it has trivial valuation at every prime — i.e. it comes from a unit of `R`. This is the
exact `1 → Rˣ → (S.integer K)ˣ → ∏_{v∈S} ℤ` left-exactness. The codomain is the product `↥S →
Multiplicative ℤ`; this theorem does not assume `S` finite, so it is not the direct sum. -/
theorem unitValuation_ker :
    (unitValuation S K).ker = ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, funext_iff]
  constructor
  · intro h
    refine (mem_unit_iff ..).mpr fun v _ ↦ ?_
    by_cases hvS : v ∈ S
    · have := h ⟨v, hvS⟩
      rwa [unitValuation_apply, Pi.one_apply, valuationOfNeZero_eq_one_iff] at this
    · exact Set.unit_valuation_eq_one _ _ u hvS
  · intro h v
    rw [unitValuation_apply, Pi.one_apply, valuationOfNeZero_eq_one_iff]
    exact (mem_unit_iff ..).mp h v (Set.notMem_empty v)

/-- **Finite generation of the `S`-units, relative to the `∅`-units.** If `S` is finite and the
`∅`-units are finitely generated — for `R = 𝒪_K` a ring of integers that is Dirichlet's unit
theorem — then so are the `S`-units. `unit_fg_of_units` is the form stated over `Rˣ`, which is
what a caller normally has. -/
theorem unit_fg [Finite S] (hu : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K)) :
    Group.FG (S.unit K) := by
  -- `Group.FG (↥S → Multiplicative ℤ)` is Mathlib's `Pi.instGroupFG` composed with
  -- `Group.fg_of_mul_group_fg` and `AddGroup.FG ℤ`; instance search finds it from `[Finite S]`
  -- and the range side from `Subgroup.fg_of_commGroup`, the only instance that can discharge it
  have : Group.FG (unitValuation S K).ker := by
    rw [unitValuation_ker]
    exact Group.fg_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (unit_mono K S.empty_subset)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (unit_mono K S.empty_subset)).symm.surjective
  exact Group.fg_of_fg_ker_of_fg_range (unitValuation S K)

/-- The `∅`-units are exactly the units of the base ring: `Set.unit ∅ K ≃* Rˣ`. The `∅`-integers
are the base ring `R` (`IsDedekindDomain.integer_empty`), and `S`-units are the units of the
`S`-integers (`Set.unitEquivUnitsInteger`).

It is a three-fold composite, so `algebraMap_unitEmptyEquivUnits_apply` below records what it
does to the underlying element. -/
noncomputable def unitEmptyEquivUnits : (∅ : Set (HeightOneSpectrum R)).unit K ≃* Rˣ :=
  (unitEquivUnitsInteger (∅ : Set (HeightOneSpectrum R)) K).trans
    (Units.mapEquiv
      ((Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K)).trans
        (Algebra.botEquivOfInjective (IsFractionRing.injective R K))).toRingEquiv.toMulEquiv)

/-- **What `unitEmptyEquivUnits` does to the underlying element:** it sends an `∅`-unit to the
unit of `R` with the same image in `K`.

**New here**, with no counterpart in mathlib4#40791: `unitEmptyEquivUnits` is a three-fold
composite whose value on an element is not readable off the definition, and this is that value,
so a future user of the equiv need not unfold it. -/
@[simp]
theorem algebraMap_unitEmptyEquivUnits_apply (u : (∅ : Set (HeightOneSpectrum R)).unit K) :
    algebraMap R K ((unitEmptyEquivUnits K u : Rˣ) : R) = ((u : Kˣ) : K) := by
  -- unfold the three-fold composite through its own equations rather than through defeq:
  -- `unitEquivUnitsInteger` and `Units.mapEquiv` down to the underlying element of `K`, then
  -- `Algebra.algebraMap_botEquivOfInjective` for the identification of `⊥` with `R`
  simp only [unitEmptyEquivUnits, RingEquiv.toMulEquiv_eq_coe, MulEquiv.trans_apply,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    val_unitEquivUnitsInteger_apply_coe, Algebra.algebraMap_botEquivOfInjective]

/-- **Finite generation of the `S`-units, over the base ring.** If `Rˣ` is finitely generated and
`S` is finite, then so is the group of `S`-units. This is `unit_fg` with its hypothesis
transported along `unitEmptyEquivUnits`, and it is the form the arithmetic uses — the `∅`-units
are not what a caller has in hand, `Rˣ` is.

This is *not* Dirichlet's `S`-unit theorem: finite generation of `Rˣ` is assumed, not proved (for
`R = 𝒪_K` that assumption is Dirichlet's unit theorem itself), no rank is computed, and `R` is an
arbitrary Dedekind domain rather than the ring of integers of a global field.

The hypothesis is `[Monoid.FG Rˣ]`, not `[Group.FG Rˣ]`: they are equivalent
(`Group.fg_iff_monoid_fg`), but the instance Mathlib actually registers for the motivating case is
`Monoid.FG (𝓞 K)ˣ` (`NumberField/Units/DirichletTheorem.lean`), and the only bridge that is an
instance runs the other way, so taking `Group.FG` would leave this instance unable to fire where
it is meant to.

**New here**, with no counterpart in mathlib4#40791: upstream gives `unitEmptyEquivUnits` its
consumer in the rank formula, which is not ported. -/
instance unit_fg_of_units [Finite S] [Monoid.FG Rˣ] : Group.FG (S.unit K) :=
  have : Group.FG Rˣ := Group.fg_iff_monoid_fg.mpr ‹_›
  unit_fg S K <| Group.fg_of_surjective (f := (unitEmptyEquivUnits K).symm.toMonoidHom)
    (unitEmptyEquivUnits K).symm.surjective

end Set

end
