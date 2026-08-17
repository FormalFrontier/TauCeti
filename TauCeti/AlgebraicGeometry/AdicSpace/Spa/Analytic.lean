/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Analytic points and the analytic locus of `Spa(A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.39, Remark 7.40(3), and
Proposition 7.49.**

This file formalizes the analytic locus of the adic spectrum `Spa(A, A⁺)`.

## Main definitions

* `TauCeti.ValuationSpectrum.IsAnalyticPoint` : extends Wedhorn's analytic-point predicate from
  `Cont A` to `Spv A`; on continuous points it is Definition 7.39.
* `TauCeti.ValuationSpectrum.spaAnalytic` : **Wedhorn's `Spa(A, A⁺)ᵃ`**, the analytic locus of
  `Spa(A, A⁺)` as a `Set (Spv A)`.
* `TauCeti.ValuationSpectrum.spaAnalytic_def` : the analytic locus as a set intersection.

## Main results

* `TauCeti.ValuationSpectrum.isAnalyticPoint_of_isTateRing` : over a Tate ring every point of
  `Spv A` (and hence `Spa(A, A⁺)`) is analytic.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_spa_of_isTateRing` : **Wedhorn Remark 7.40(3)**,
  for a Tate ring `A`, the analytic locus is the entire adic spectrum.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.39, Remark 7.40(3), and
  Proposition 7.49.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Analytic points of `Spv A`.** A point `v : Spv A` is *analytic* if its support `v.supp` is
not an open ideal of `A`. This extends Wedhorn's Definition 7.39 from `Cont A` to all of `Spv A`;
its restriction to continuous points is his predicate. -/
def IsAnalyticPoint (v : Spv A) : Prop :=
  ¬ IsOpen (v.supp : Set A)

/-- A point of `Spv A` is analytic exactly when its support is not open. -/
@[simp]
theorem isAnalyticPoint_def (v : Spv A) :
    IsAnalyticPoint v ↔ ¬ IsOpen (v.supp : Set A) :=
  Iff.rfl

/-- **Wedhorn's Analytic Locus `Spa(A, A⁺)ᵃ`**: the subset of `spa Aplus` consisting of analytic
points (Definition 7.39). -/
def spaAnalytic (Aplus : Subring A) : Set (Spv A) :=
  spa Aplus ∩ {v : Spv A | IsAnalyticPoint v}

/-- The analytic locus as a set intersection. -/
theorem spaAnalytic_def (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus ∩ {v : Spv A | IsAnalyticPoint v} := (rfl)

/-- Membership in the analytic locus: `v ∈ Spa(A, A⁺)ᵃ` iff `v ∈ Spa(A, A⁺)` and `v` is an
analytic point. -/
@[simp]
theorem mem_spaAnalytic_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spaAnalytic Aplus ↔ v ∈ spa Aplus ∧ IsAnalyticPoint v :=
  Iff.rfl

/-- The analytic locus is contained in the adic spectrum. -/
theorem spaAnalytic_subset_spa (Aplus : Subring A) :
    spaAnalytic Aplus ⊆ spa Aplus :=
  Set.inter_subset_left

/-- Enlarging the plus ring shrinks the analytic locus. -/
theorem spaAnalytic_antitone : Antitone (spaAnalytic (A := A)) := fun _ _ hle ↦
  Set.inter_subset_inter_left _ (spa_antitone hle)

section TateRing

variable [IsTopologicalRing A] [IsTateRing A]

/-- Over a Tate ring, every point of `Spv A` is analytic, extending Wedhorn Remark 7.40(3) beyond
continuous points. -/
theorem isAnalyticPoint_of_isTateRing (v : Spv A) : IsAnalyticPoint v :=
  fun h ↦ (instIsPrimeSupp v).ne_top (IsTateRing.eq_top_of_isOpen h)

/-- **Wedhorn Remark 7.40(3).** Over a Tate ring, the analytic locus is the entire adic
spectrum: `Spa (A, A⁺)ᵃ = Spa (A, A⁺)`. -/
@[simp]
theorem spaAnalytic_eq_spa_of_isTateRing (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus := by
  ext v
  rw [mem_spaAnalytic_iff]
  exact and_iff_left (isAnalyticPoint_of_isTateRing v)

end TateRing

end TauCeti.ValuationSpectrum
