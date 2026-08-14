/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Basic

/-!
# Analytic points, the analytic locus, and emptiness of `Spa(A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.39 and Proposition 7.49.**

This file formalizes the analytic locus of the adic spectrum `Spa(A, A⁺)` and the forward
direction of the emptiness criterion for `Spa(A, A⁺)`.

## Main definitions

* `TauCeti.ValuationSpectrum.IsAnalyticPoint` : a point `v : Spv A` is *analytic* if its support
  `v.supp` is not an open ideal of `A`.
* `TauCeti.ValuationSpectrum.spaAnalytic` : **Wedhorn's `Spa(A, A⁺)ᵃ`**, the analytic locus of
  `Spa(A, A⁺)` as a `Set (Spv A)`.

## Main results

* `TauCeti.ValuationSpectrum.spa_eq_empty_of_one_mem_closure_zero` : if `1 ∈ closure {0}` in a
  topological additive group `A`, then `Spa(A, A⁺) = ∅` for any plus ring `A⁺`
  (Wedhorn Proposition 7.49(1)).
* `TauCeti.ValuationSpectrum.spa_eq_empty_of_subsingleton` : over a zero ring `A`, `Spa(A, A⁺) = ∅`.
* `TauCeti.ValuationSpectrum.isAnalyticPoint_of_isTateRing` : **Wedhorn Proposition 7.49(2)**,
  over a Tate ring every point of `Spv A` (and hence `Spa(A, A⁺)`) is analytic.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_spa_of_isTateRing` : for a Tate ring `A`, the
  analytic locus is the entire adic spectrum `spaAnalytic Aplus = spa Aplus`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.39 and Proposition 7.49.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber TauCeti.Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Analytic points of `Spv A` (Wedhorn Definition 7.39).** A point `v : Spv A` is *analytic*
if its support `v.supp` is not an open ideal of `A`. -/
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

/-- The set-level characterization of the analytic locus. -/
theorem spaAnalytic_def (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus ∩ {v : Spv A | IsAnalyticPoint v} := (rfl)

/-- Membership in the analytic locus: `v ∈ Spa(A, A⁺)ᵃ` iff `v ∈ Spa(A, A⁺)` and `v` is an
analytic point. -/
@[simp]
theorem mem_spaAnalytic_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spaAnalytic Aplus ↔ v ∈ spa Aplus ∧ IsAnalyticPoint v := by
  rw [spaAnalytic_def, Set.mem_inter_iff, Set.mem_ofPred_eq]

/-- The analytic locus is contained in the adic spectrum. -/
theorem spaAnalytic_subset_spa (Aplus : Subring A) :
    spaAnalytic Aplus ⊆ spa Aplus :=
  spaAnalytic_def Aplus ▸ Set.inter_subset_left

section TopologicalAddGroup

variable [IsTopologicalAddGroup A]

/-- **Wedhorn Proposition 7.49(1) (forward direction for `Spa`).** If `1 ∈ closure {0}` in a
topological additive group `A`, then `Spa (A, A⁺) = ∅` for any plus ring `A⁺`. -/
theorem spa_eq_empty_of_one_mem_closure_zero (Aplus : Subring A)
    (h : (1 : A) ∈ closure ({0} : Set A)) : spa Aplus = ∅ := by
  rw [spa_def, cont_eq_empty_of_one_mem_closure_zero h, Set.empty_inter]

end TopologicalAddGroup

/-- Over a zero ring, `Spa (A, A⁺) = ∅`. -/
@[simp]
theorem spa_eq_empty_of_subsingleton [Subsingleton A] (Aplus : Subring A) :
    spa Aplus = ∅ := by
  rw [spa_def, cont_eq_empty_of_subsingleton, Set.empty_inter]

/-- Over a zero ring, the analytic locus `Spa (A, A⁺)ᵃ` is empty. -/
@[simp]
theorem spaAnalytic_eq_empty_of_subsingleton [Subsingleton A] (Aplus : Subring A) :
    spaAnalytic Aplus = ∅ := by
  rw [spaAnalytic_def, spa_eq_empty_of_subsingleton, Set.empty_inter]

section TateRing

variable [IsTopologicalRing A] [IsTateRing A]

/-- **Wedhorn Proposition 7.49(2).** Over a Tate ring, every point of `Spv A` is analytic. -/
theorem isAnalyticPoint_of_isTateRing (v : Spv A) : IsAnalyticPoint v :=
  Huber.not_isOpen_of_isPrime v.supp

/-- **Wedhorn Proposition 7.49(2).** Over a Tate ring, the analytic locus is the entire adic
spectrum: `Spa (A, A⁺)ᵃ = Spa (A, A⁺)`. -/
@[simp]
theorem spaAnalytic_eq_spa_of_isTateRing (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus := by
  ext v
  rw [mem_spaAnalytic_iff]
  exact and_iff_left (isAnalyticPoint_of_isTateRing v)

end TateRing

end TauCeti.ValuationSpectrum
