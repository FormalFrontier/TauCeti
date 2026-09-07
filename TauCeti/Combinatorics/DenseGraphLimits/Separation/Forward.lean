/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Counting

/-!
# Forward separation of graphons by homomorphism densities

The forward half of graphon separation is the qualitative consequence of the cut-distance form of
the counting lemma

`|t(F, U) - t(F, W)| ≤ e(F) * δ□(U, W)`

(`abs_homDensity_sub_le_cutDist`): graphons at cut distance zero have equal homomorphism densities
for every finite graph.  Here `U` and `W` may live on different probability spaces, and no
standard-Borel, atomlessness, or common-carrier assumption is needed.

This is the easy direction of the inverse-counting/separation theorem.  The converse — equality of
all homomorphism densities implies cut distance zero — is the hard inverse-counting theorem and
belongs in the subsequent separation development.

## Main results

* `TauCeti.DenseGraphLimits.forall_homDensity_eq_of_cutDist_eq_zero` — graphons at cut distance
  zero have the same homomorphism densities.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Lemma 10.23 and Theorem 11.3 (forward direction).
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.2 and Theorem 8.10 (forward direction).
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 6a — the cross-carrier forward
  separation theorem `forall_homDensity_eq_of_cutDist_eq_zero`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {V Ω₁ Ω₂ : Type*} [Fintype V] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
  [IsProbabilityMeasure μ₂]

/-- **Forward separation, across arbitrary carriers.** If two graphons have cut distance zero,
then every finite graph has the same homomorphism density in them.

This is the counting direction of graphon separation.  It has no standard-Borel or atomlessness
hypothesis because both the coupling counting lemma and the coupling-primary cut distance are
defined on arbitrary probability carriers. -/
theorem forall_homDensity_eq_of_cutDist_eq_zero (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : cutDist U W = 0) :
    ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F U = homDensity F W := by
  intro n F _
  have hbound := abs_homDensity_sub_le_cutDist F U W
  rw [h, mul_zero] at hbound
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _)))

end DenseGraphLimits

end TauCeti
