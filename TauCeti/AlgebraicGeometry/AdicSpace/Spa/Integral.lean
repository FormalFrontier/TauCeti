/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Basic
import TauCeti.RingTheory.Huber.Continuous.ValuativeCriterion

/-!
# The ring of integral elements is cut out by the points of the adic spectrum

Wedhorn's Proposition 7.52(1): for a Huber pair `(A, A⁺)`, an element `f` of `A` whose value is
at most `1` at *every* point of `Spa(A, A⁺)` already lies in `A⁺`. The converse is the defining
condition of `spa`, so the two together say that `A⁺` is exactly the sub-unit locus of the adic
spectrum — the half proved here is the one that has content.

Of the three conditions making `A⁺` a ring of integral elements, only openness and integral
closedness in `A` enter, so the statements are made for any open subring `A⁺` integrally closed
in `A`; for a ring of integral elements `hplus`, the two hypotheses are `hplus.isOpen` and
`hplus.isIntegrallyClosedIn`.

## Where it comes from

`spa A⁺` consists of the *continuous* valuations that are at most `1` on `A⁺`
(`TauCeti.ValuationSpectrum.mem_spa_iff`), so the hypothesis is precisely the hypothesis of
Wedhorn's Proposition 7.18(1),
`TauCeti.Huber.isIntegral_of_forall_continuous_valuation_le_one`, at the open subring `A⁺`.
That criterion returns integrality of `f` over `A⁺`, and `A⁺` is integrally closed in `A`, so
`f ∈ A⁺` follows. Nothing beyond a Huber ring enters: the criterion asks neither for a domain
nor for a chosen ring of definition.

The all-valuations criterion `TauCeti.isIntegral_of_forall_valuation_le_one` does *not* suffice
here: its hypothesis quantifies over every valuation of `A`, and a point of `Spa(A, A⁺)` supplies
only the continuous ones. Cutting the criterion down to the continuous valuations is exactly what
Wedhorn 7.18(1) does and what this statement consumes.

## Main results

* `TauCeti.ValuationSpectrum.mem_of_forall_vle_one` : Proposition 7.52(1), the direction with
  content.
* `TauCeti.ValuationSpectrum.mem_iff_forall_vle_one` : the membership criterion
  `f ∈ A⁺ ↔ ∀ v ∈ Spa(A, A⁺), v(f) ≤ 1`.
* `TauCeti.ValuationSpectrum.coe_eq_setOf_forall_vle_one` : the same statement as the displayed
  set equality `A⁺ = {a ∈ A : v(a) ≤ 1 for every v ∈ Spa(A, A⁺)}`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 7.18 and 7.52.

## Provenance

Assembled here from `TauCeti.Huber.isIntegral_of_forall_continuous_valuation_le_one` and
Mathlib's `Subring.isIntegrallyClosedIn_iff`; nothing is ported. AINTLIB reaches 7.52(1) by a
different route, the height-one reduction pairing Wedhorn's Propositions 7.18 and 7.41, which is
not followed.
-/

public section

open TauCeti.Huber

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **Wedhorn's Proposition 7.52(1)**: an element of `A` whose value is at most `1` at every
point of `Spa(A, A⁺)` lies in `A⁺`, for any open subring `A⁺` integrally closed in `A`.

The points of `Spa(A, A⁺)` are the continuous valuations that are sub-unit on `A⁺`, so the
hypothesis is the hypothesis of Wedhorn's Proposition 7.18(1); that criterion makes `f` integral
over `A⁺`, and `A⁺` is integrally closed in `A`. -/
theorem mem_of_forall_vle_one {Aplus : Subring A} (hopen : IsOpen (Aplus : Set A))
    [IsIntegrallyClosedIn Aplus A] {f : A} (hf : ∀ v ∈ spa Aplus, v.toValuativeRel.vle f 1) :
    f ∈ Aplus :=
  Subring.isIntegrallyClosedIn_iff.mp inferInstance
    (isIntegral_of_forall_continuous_valuation_le_one hopen fun v hcont hv ↦
      hf v ((mem_spa_iff Aplus v).mpr ⟨hcont, hv⟩))

/-- **Wedhorn's Proposition 7.52(1)** as a membership criterion: `f ∈ A⁺` iff every point of
`Spa(A, A⁺)` is sub-unit at `f`.

The forward direction is the defining condition of `spa` and needs no hypothesis; the content is
`mem_of_forall_vle_one`. This is deliberately not a `simp` lemma: `mem_spa_iff` is one, and
unfolding `v ∈ spa A⁺` on the right reintroduces membership in `A⁺`, so the two would rewrite
each other without end. -/
theorem mem_iff_forall_vle_one {Aplus : Subring A} (hopen : IsOpen (Aplus : Set A))
    [IsIntegrallyClosedIn Aplus A] {f : A} :
    f ∈ Aplus ↔ ∀ v ∈ spa Aplus, v.toValuativeRel.vle f 1 :=
  ⟨fun hf v hv ↦ ((mem_spa_iff Aplus v).mp hv).2 _ hf, mem_of_forall_vle_one hopen⟩

/-- **Wedhorn's Proposition 7.52(1)** as a set equality: `A⁺` *is* the locus of `A` on which
every point of `Spa(A, A⁺)` is sub-unit. -/
theorem coe_eq_setOf_forall_vle_one {Aplus : Subring A} (hopen : IsOpen (Aplus : Set A))
    [IsIntegrallyClosedIn Aplus A] :
    (Aplus : Set A) = {a | ∀ v ∈ spa Aplus, v.toValuativeRel.vle a 1} :=
  Set.ext fun _ ↦ mem_iff_forall_vle_one hopen

end TauCeti.ValuationSpectrum
