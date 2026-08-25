/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Counting
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance

/-!
# Homomorphism densities are Lipschitz in the cut distance

The counting lemma says the homomorphism density `t(F, ·)` moves by at most `e(F)` times the cut
norm. Its coupling form (`counting_lemma_coupling`) says the same across carriers, one coupling at a
time; taking the infimum over couplings turns it into a bound by the **cut distance** itself:

`|t(F, U) - t(F, W)| ≤ e(F) · δ□(U, W)`.

Nothing here restricts the two carriers: they may be different probability spaces, and neither has
to be standard Borel or atomless. That is the point of the coupling-primary cut distance — the
infimum ranges over couplings of the two given carriers, so the bound above is available as soon as
the two graphons exist.

Specialising to `δ□(U, W) = 0` gives the **forward direction of the separation theorem**: graphons
at cut distance zero have the same homomorphism densities, so the moment map `W ↦ (t(F, W))_F` is
constant on cut-distance-zero classes. The converse — that matching densities force cut distance
zero — is the genuinely hard inverse counting lemma and is not proved here.

**Why a Lipschitz bound rather than a bare implication.** The `= 0` statement is the corollary the
separation theorem quotes, but the quantitative bound is what the later layers actually consume: it
is the estimate that makes each `t(F, ·)` descend to a *continuous* function on the quotient
`GraphonSpace`, which is in turn what the convergence equivalence and the point-separating
coordinate algebra of the mixture representation rest on. Proving the sharp bound first also avoids
an `ε`-argument in the corollary.

## Main results

* `TauCeti.DenseGraphLimits.abs_homDensity_sub_le_mul_cutDist` — the cross-carrier Lipschitz bound
  `|t(F, U) - t(F, W)| ≤ e(F) · δ□(U, W)`;
* `TauCeti.DenseGraphLimits.homDensity_eq_of_cutDist_eq_zero` — cut distance zero forces every
  homomorphism density to agree;
* `TauCeti.DenseGraphLimits.forall_homDensity_eq_of_cutDist_eq_zero` — the same statement quantified
  over the finite-graph representatives `SimpleGraph (Fin n)`, the shape the separation `iff` is
  stated in;
* `TauCeti.DenseGraphLimits.cutDist_pos_of_homDensity_ne` — the contrapositive: a single density
  gap already separates two graphons in cut distance.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 6a — the forward direction
  `forall_homDensity_eq_of_cutDist_eq_zero`, obtained from `counting_lemma_coupling` as the roadmap
  prescribes, cross-carrier and with no standard-Borel or atomless hypothesis. The converse
  `cutDist_eq_zero_of_forall_homDensity_eq_cross`, the assembled `iff`, and the quotient-level
  `graphonSpace_ext_homDensity` are separate targets and are not built here.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.2 and Theorem 8.10.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Lemma 10.23
  and Theorem 11.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁}
  {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  {V : Type*} [Fintype V]

/-- **Homomorphism densities are Lipschitz in the cut distance**, with constant `e(F)`, across
arbitrary probability carriers: `|t(F, U) - t(F, W)| ≤ e(F) · δ□(U, W)`.

Every coupling contributes the bound `counting_lemma_coupling`, so `e(F)⁻¹ · |t(F, U) - t(F, W)|`
is a lower bound for the whole set of overlaid cut norms, hence for their infimum. The edgeless
case is separate only because dividing by `e(F)` needs it to be positive; there the left-hand side
already vanishes, since the empty product makes both densities `1`. -/
theorem abs_homDensity_sub_le_mul_cutDist (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    |homDensity F U - homDensity F W| ≤ (F.edgeFinset.card : ℝ) * cutDist U W := by
  rcases Nat.eq_zero_or_pos F.edgeFinset.card with hzero | hpos
  · have h := counting_lemma_coupling F U W (TauCeti.MeasureTheory.isCoupling_prod μ₁ μ₂)
    rw [hzero] at h ⊢
    simpa using h
  · have hcard : (0 : ℝ) < (F.edgeFinset.card : ℝ) := by exact_mod_cast hpos
    have hle : |homDensity F U - homDensity F W| / (F.edgeFinset.card : ℝ) ≤ cutDist U W := by
      refine le_cutDist U W fun π hπ => ?_
      have h := counting_lemma_coupling F U W hπ
      rw [div_le_iff₀ hcard]
      linarith
    rw [div_le_iff₀ hcard] at hle
    linarith

/-- **The forward direction of the separation theorem, for one graph.** Two graphons at cut
distance zero have the same homomorphism density at every finite graph.

The two carriers are arbitrary probability spaces; in particular this is the cross-carrier
statement, and the same-carrier one is the case `Ω₁ = Ω₂`, `μ₁ = μ₂`. -/
theorem homDensity_eq_of_cutDist_eq_zero (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (h : cutDist U W = 0) :
    homDensity F U = homDensity F W := by
  have hle := abs_homDensity_sub_le_mul_cutDist F U W
  rw [h, mul_zero] at hle
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm hle (abs_nonneg _)))

/-- **The forward direction of the separation theorem.** If `δ□(U, W) = 0` then `U` and `W` have the
same homomorphism densities.

Finite graphs are quantified over the representatives `SimpleGraph (Fin n)`, one type per vertex
count, rather than over an arbitrary vertex type in an arbitrary universe: this is the shape the
converse (the inverse counting lemma) can be stated in, so it is the shape the eventual separation
`iff` is assembled from. Nothing is lost, since every finite graph is isomorphic to one of these and
`homDensity` is an isomorphism invariant. -/
theorem forall_homDensity_eq_of_cutDist_eq_zero (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : cutDist U W = 0) :
    ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F U = homDensity F W :=
  fun _ F _ => homDensity_eq_of_cutDist_eq_zero F U W h

/-- **A single density gap separates.** If `U` and `W` differ at some homomorphism density, their
cut distance is positive — the contrapositive of the forward separation direction, in the form a
lower-bound argument uses. -/
theorem cutDist_pos_of_homDensity_ne (F : SimpleGraph V) [DecidableRel F.Adj] (U : Graphon Ω₁ μ₁)
    (W : Graphon Ω₂ μ₂) (h : homDensity F U ≠ homDensity F W) : 0 < cutDist U W :=
  (cutDist_nonneg U W).lt_of_ne fun hzero =>
    h (homDensity_eq_of_cutDist_eq_zero F U W hzero.symm)

end DenseGraphLimits

end TauCeti
