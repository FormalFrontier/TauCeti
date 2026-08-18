/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic

/-!
# The underlying set of the adic spectrum `Spa (A, A⁺)`

**The set-level construction beneath Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
Definition 7.23.**

For a subring `A⁺` of a commutative ring `A` with a topology, `spa A⁺` is the set of continuous
points of `Spv A` that are sub-unit on `A⁺`:

```text
spa A⁺ = {v ∈ cont A | v(a) ≤ 1 for every a ∈ A⁺}.
```

This is stated for arbitrary data — the file assumes `[TopologicalSpace A]` and nothing
relating the topology to the ring operations, and asks nothing of the subring. It **is**
Wedhorn's adic spectrum `Spa (A, A⁺)` under the hypotheses his Definition 7.23 carries: `A` a
Huber ring (so in particular a topological ring, which is also what makes membership in
`cont A` Wedhorn's Definition 7.7) and `A⁺` a ring of integral elements. Those hypotheses
enter only where theorems need them — spectrality (Wedhorn Theorem 7.35) is the first such
theorem, and it lives with the `Spv (A, I)` machinery it consumes, not in this file. This
mirrors how `cont` itself is defined below its Wedhorn hypotheses.

Following the roadmap's conventions, the plus ring is an explicit `Subring A` argument and the
spectrum is a `Set (Spv A)`, so a point is a valuation up to equivalence with no chosen value
group, and the subspace topology is the one the coercion `↥(spa Aplus)` carries. (Mathlib's
in-flight `SpaPoint` of mathlib4#42315 instead bundles a representative valuation with a chosen
value group — the representation the roadmap warns must be compared before later layers may use
it; the subspace form here needs no such comparison.)

## Main definitions

* `TauCeti.ValuationSpectrum.spa` : the adic spectrum of `(A, A⁺)`, as a `Set (Spv A)`.

## Main results

* `TauCeti.ValuationSpectrum.spa_def` and `TauCeti.ValuationSpectrum.mem_spa_iff` : the
  set-level and membership-level characterizations — the definition is not exposed across the
  module boundary, so these two are the exported interface.
* `TauCeti.ValuationSpectrum.spa_antitone` : the spectrum shrinks as the plus ring grows. Its
  inclusion into `Cont A` is `spa_def ▸ Set.inter_subset_left`.
* `TauCeti.ValuationSpectrum.spa_integralClosure` : replacing the plus ring by its integral
  closure leaves `Spa` unchanged.
* `TauCeti.ValuationSpectrum.spa_eq_empty_of_one_mem_closure_zero` : if `1 ∈ closure {0}` in a
  commutative ring `A` with separately continuous addition, then `Spa(A, A⁺) = ∅` for any plus
  ring `A⁺` (the `1 ∈ closure {0} → Spa(A, A⁺) = ∅` half of Wedhorn Proposition 7.49(1)).

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23 and Proposition 7.49.
-/

public section

namespace TauCeti.ValuationSpectrum

open Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The continuous points of `Spv A` that are sub-unit on the subring `A⁺`, as a
`Set (Spv A)` — the subspace topology is the one the coercion `↥(spa Aplus)` carries.

For a Huber ring `A` and a ring of integral elements `A⁺` this is **Wedhorn's adic spectrum
`Spa (A, A⁺)`** (Definition 7.23); the definition itself asks for neither — an arbitrary
subring of an arbitrary commutative ring with a topology — and the Wedhorn hypotheses enter
only in later theorems. -/
def spa (Aplus : Subring A) : Set (Spv A) :=
  cont A ∩ {v : Spv A | ∀ a ∈ Aplus, v.toValuativeRel.vle a 1}

/-- The set-level characterization of the adic spectrum: `spa` is the intersection of the
continuous locus with the sub-unit locus of the plus ring. The definition is not exposed
across the module boundary, so this equation is how consumers apply set-level results to
`spa` — for instance `spa_def ▸ Set.inter_subset_left : spa Aplus ⊆ cont A`. -/
theorem spa_def (Aplus : Subring A) :
    spa Aplus = cont A ∩ {v : Spv A | ∀ a ∈ Aplus, v.toValuativeRel.vle a 1} := (rfl)

/-- Membership in the adic spectrum is continuity together with the sub-unit condition on the
plus ring: `v ∈ Spa (A, A⁺)` iff `v` is continuous and `v(a) ≤ 1` for every `a ∈ A⁺`. -/
@[simp]
theorem mem_spa_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spa Aplus ↔ v.IsContinuous ∧ ∀ a ∈ Aplus, v.toValuativeRel.vle a 1 := by
  rw [spa_def, Set.mem_inter_iff, mem_cont_iff, Set.mem_ofPred_eq]

/-- Enlarging the plus ring shrinks the adic spectrum. -/
theorem spa_antitone : Antitone (spa (A := A)) := fun _ _ hle ↦ by
  rw [spa_def, spa_def]
  exact Set.inter_subset_inter_right _ fun _ hv a ha ↦ hv a (hle ha)

/-- Replacing a subring by its integral closure does not change the sub-unit valuation locus. -/
@[simp]
theorem spa_integralClosure (R : Subring A) :
    spa (integralClosure R A).toSubring = spa R := by
  ext v
  rw [mem_spa_iff, mem_spa_iff]
  refine and_congr_right fun _ ↦ ⟨fun h r hr ↦ ?_, fun h x hx ↦ ?_⟩
  · exact h r (algebraMap_mem (integralClosure R A) ⟨r, hr⟩)
  · let φ : R →+* v.valuation.integer :=
      R.subtype.codRestrict v.valuation.integer fun r ↦ by
        rw [Valuation.mem_integer_iff, ← map_one v.valuation, valuation_le_iff]
        exact h r r.2
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff] at hx
    have hint : IsIntegral v.valuation.integer x :=
      hx.map_of_comp_eq φ (RingHom.id A) (by ext r; rfl)
    have hxint := (Valuation.integer.integers v.valuation).mem_of_integral hint
    rw [Valuation.mem_integer_iff, ← map_one v.valuation, valuation_le_iff] at hxint
    exact hxint

section SeparatelyContinuousAdd

variable [SeparatelyContinuousAdd A]

/-- **The `1 ∈ closure {0} → Spa(A, A⁺) = ∅` half of Wedhorn Proposition 7.49(1).** If
`1 ∈ closure {0}` in a commutative ring `A` with separately continuous addition, then
`Spa (A, A⁺) = ∅` for any plus ring `A⁺`. -/
theorem spa_eq_empty_of_one_mem_closure_zero (Aplus : Subring A)
    (h : (1 : A) ∈ closure ({0} : Set A)) : spa Aplus = ∅ := by
  rw [spa_def, cont_eq_empty_of_one_mem_closure_zero h, Set.empty_inter]

end SeparatelyContinuousAdd

end TauCeti.ValuationSpectrum

end
