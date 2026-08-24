/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Coupling
public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm

/-!
# The cut distance of two graphons

The **cut distance** of two graphons is

`δ□(U, W) = inf { ‖overlayDiff U W π‖□ | π a coupling of the two carriers }`,

the infimum, over couplings of the two carriers, of the cut norm of the overlaid difference. This
file defines it and develops the part of its theory that does not need the triangle inequality.

**Coupling-primary, and cross-carrier by construction.** `U` and `W` live on *different*
probability spaces, and nothing here asks them to be standard Borel or atomless — a coupling
always exists (`isCoupling_prod`), so the infimum is over a nonempty set of nonnegative reals and
is a genuine infimum rather than a junk value. The competing definition, an infimum over
measure-preserving maps into a common carrier, is not more general: it agrees with this one over
standard Borel carriers, which is a separate later target.

**The triangle inequality is not proved here.** On arbitrary carriers it is Janson's Lemma 6.5,
whose proof reduces the gluing of two couplings to the finite case by step-graphon approximation,
and the roadmap makes that reduction a milestone of its own. Everything below — nonnegativity, the
`[0, 1]` range, symmetry, reflexivity, and the common-carrier upper bound — is independent of it.

**Symmetry is a swap of couplings, not a rearrangement.** `cutDist_comm` holds on arbitrary
carriers because `Prod.swap` turns a coupling of `μ₁, μ₂` into one of `μ₂, μ₁` and negates the
overlaid difference, and the cut norm is even and drops along a pushforward
(`cutNorm_le_cutNorm_comap`). No common carrier and no measurable-isomorphism hypothesis appears.

## Main definitions

* `TauCeti.DenseGraphLimits.cutDist` — the infimum of the overlaid cut norms over couplings of the
  two carriers.

## Main results

* `cutDist_le` and `le_cutDist` are the introduction and elimination rules for the infimum, and
  `exists_isCoupling_cutNorm_lt` produces a coupling beating any strict upper bound;
* `cutDist_nonneg` and `cutDist_le_one` are the range;
* `cutDist_comm` is symmetry;
* `cutDist_le_cutNorm_sub_of_measurePreserving` bounds the cut distance by the same-carrier cut
  norm of the difference of two pullbacks, `cutDist_le_cutNorm_sub` is its identity case, and
  `cutDist_self` follows.

## Implementation

The private implementation set `couplingCutNorms` is named rather than inlined because both `csInf`
rules need it: `cutDist_le` needs the set to be bounded below and `le_cutDist` needs it to be
nonempty, and those two facts are stated about it once instead of being unfolded at each use. The
definition carries the `IsFiniteMeasure` evidence supplied by a coupling explicitly, in the `@`
form, because an existentially quantified witness cannot supply an instance by unification. Since
`IsFiniteMeasure` is a `Prop` class, that instance is interchangeable with any other by proof
irrelevance, and callers holding `[IsProbabilityMeasure π]` may use the lemmas below with the
ordinary `cutNorm π` on the nose.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §6 — the coupling definition of the cut distance, and Lemma 6.5 for the triangle
  inequality on arbitrary carriers.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §8.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the coupling-primary,
  cross-carrier `cutDist` and its basic laws; the signature follows
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`, with the two carrier measures implicit as in
  `overlayDiff`. The triangle inequality, the `GraphonSpace` quotient, and the agreement with the
  measure-preserving-map form are separate targets and are not built here.
-/

public section

noncomputable section

open MeasureTheory TauCeti.MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- The set of cut norms of the overlaid difference of `U` and `W`, one for each coupling of their
two carriers. The cut distance is its infimum.

Nonempty by `couplingCutNorms_nonempty` and bounded below by `0` through
`nonneg_of_mem_couplingCutNorms`, which is what makes that infimum meaningful in `ℝ`. -/
private def couplingCutNorms (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : Set ℝ :=
  {r | ∃ (π : Measure (Ω₁ × Ω₂)) (hπ : IsCoupling μ₁ μ₂ π),
    @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U W π) = r}

/-- Every coupling contributes its overlaid cut norm to `couplingCutNorms`. -/
private theorem mem_couplingCutNorms (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    {π : Measure (Ω₁ × Ω₂)}
    [IsProbabilityMeasure π] (hπ : IsCoupling μ₁ μ₂ π) :
    cutNorm π (overlayDiff U W π) ∈ couplingCutNorms U W :=
  ⟨π, hπ, rfl⟩

/-- The independent coupling shows that two graphons always admit at least one comparison. -/
private theorem couplingCutNorms_nonempty (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    (couplingCutNorms U W).Nonempty :=
  ⟨_, mem_couplingCutNorms U W (isCoupling_prod μ₁ μ₂)⟩

/-- Every overlaid cut norm is nonnegative, being a cut norm. -/
private theorem nonneg_of_mem_couplingCutNorms {U : Graphon Ω₁ μ₁} {W : Graphon Ω₂ μ₂} {r : ℝ}
    (hr : r ∈ couplingCutNorms U W) : 0 ≤ r := by
  obtain ⟨π, hπ, rfl⟩ := hr
  have := hπ.isProbabilityMeasure
  exact cutNorm_nonneg π _

/-- The set of overlaid cut norms is bounded below by `0`. -/
private theorem bddBelow_couplingCutNorms (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    BddBelow (couplingCutNorms U W) :=
  ⟨0, fun _ hr => nonneg_of_mem_couplingCutNorms hr⟩

/-- The **cut distance** of two graphons: the infimum, over couplings of their carriers, of the cut
norm of the overlaid difference.

The two graphons may live on different probability spaces, and no standard Borel or atomless
hypothesis is imposed on either. -/
def cutDist (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : ℝ := sInf (couplingCutNorms U W)

/-- The cut distance is at most the overlaid cut norm along any coupling: the introduction rule
for the infimum. -/
theorem cutDist_le (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {π : Measure (Ω₁ × Ω₂)}
    (hπ : IsCoupling μ₁ μ₂ π) :
    cutDist U W ≤ @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U W π) :=
  csInf_le (bddBelow_couplingCutNorms U W) ⟨π, hπ, rfl⟩

/-- To bound the cut distance from below it suffices to bound every overlaid cut norm from below:
the elimination rule for the infimum. -/
theorem le_cutDist {c : ℝ} (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : ∀ (π : Measure (Ω₁ × Ω₂)) (hπ : IsCoupling μ₁ μ₂ π),
      c ≤ @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U W π)) :
    c ≤ cutDist U W :=
  le_csInf (couplingCutNorms_nonempty U W) (by
    rintro r ⟨π, hπ, rfl⟩
    exact h π hπ)

/-- Any strict upper bound on the cut distance is beaten by some coupling. This is the form in
which a cut-distance hypothesis is used: it turns an infimum into an explicit coupling. -/
theorem exists_isCoupling_cutNorm_lt (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {c : ℝ}
    (h : cutDist U W < c) :
    ∃ (π : Measure (Ω₁ × Ω₂)) (hπ : IsCoupling μ₁ μ₂ π),
      @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U W π) < c := by
  rw [cutDist] at h
  obtain ⟨r, ⟨π, hπ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (couplingCutNorms_nonempty U W) h
  exact ⟨π, hπ, hlt⟩

/-- The cut distance is nonnegative. -/
theorem cutDist_nonneg (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : 0 ≤ cutDist U W :=
  le_cutDist U W fun π hπ => @cutNorm_nonneg _ _ π hπ.isFiniteMeasure _

/-- The cut distance of two graphons is at most `1`: the independent coupling already realises a
value at most `1`, since the overlaid difference is `[-1, 1]`-valued and the carrier is a
probability space. -/
theorem cutDist_le_one (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : cutDist U W ≤ 1 := by
  refine (cutDist_le U W (isCoupling_prod μ₁ μ₂)).trans ?_
  refine (cutNorm_le_integral_abs _ (overlayDiff U W (μ₁.prod μ₂))).trans ?_
  calc
    ∫ p, |overlayDiff U W (μ₁.prod μ₂) p.1 p.2| ∂((μ₁.prod μ₂).prod (μ₁.prod μ₂))
        ≤ ∫ _p, (1 : ℝ) ∂((μ₁.prod μ₂).prod (μ₁.prod μ₂)) :=
      integral_mono (overlayDiff U W (μ₁.prod μ₂)).integrable_uncurry.abs (integrable_const 1)
        fun p => abs_overlayDiff_apply_le_one U W (μ₁.prod μ₂) p.1 p.2
    _ = 1 := by simp

/-- Swapping the two graphons can only decrease the cut distance; applying it twice therefore
proves `cutDist_comm`.

Given a coupling `ρ` of `μ₂` and `μ₁`, its pushforward along `Prod.swap` couples `μ₁` and `μ₂`,
and `overlayDiff_swap` identifies the overlaid difference along it, up to sign and pullback, with
the one along `ρ`. -/
private theorem cutDist_le_cutDist_swap (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDist U W ≤ cutDist W U := by
  refine le_cutDist W U fun ρ hρ => ?_
  have := hρ.isFiniteMeasure
  have := hρ.swap.isProbabilityMeasure
  refine (cutDist_le U W hρ.swap).trans ?_
  have hmp : MeasurePreserving (Prod.swap : Ω₂ × Ω₁ → Ω₁ × Ω₂) ρ (ρ.map Prod.swap) :=
    ⟨measurable_swap, rfl⟩
  refine (cutNorm_le_cutNorm_comap _ hmp (overlayDiff U W (ρ.map Prod.swap))).trans_eq ?_
  rw [overlayDiff_swap U W (ρ.map Prod.swap) ρ, cutNorm_neg]

/-- The cut distance is symmetric.

This holds on arbitrary probability carriers: a coupling of `μ₁` and `μ₂` swaps to one of `μ₂` and
`μ₁`, so the two infima range over matching sets of values. -/
theorem cutDist_comm (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : cutDist U W = cutDist W U :=
  le_antisymm (cutDist_le_cutDist_swap U W) (cutDist_le_cutDist_swap W U)

section CommonCarrier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **A common carrier bounds the cut distance.** If `f` and `g` are measure preserving from a
common finite-measure space onto the two carriers, then the cut distance is at most the ordinary cut
norm of the difference of the two pullbacks.

This is the inequality that makes the measure-preserving-map picture an upper bound for the
coupling-primary one: the graph of `(f, g)` pushes `μ` forward to a coupling
(`isCoupling_map_prodMk`), and the overlaid difference along it pulls back to the plain difference
of the pullback kernels. That the infimum over such pairs is *equal* to the cut distance is a
separate, later target, and needs standard Borel carriers. -/
theorem cutDist_le_cutNorm_sub_of_measurePreserving [IsFiniteMeasure μ]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    {f : Ω → Ω₁} {g : Ω → Ω₂} (hf : MeasurePreserving f μ μ₁) (hg : MeasurePreserving g μ μ₂) :
    cutDist U W ≤
      cutNorm μ
        (U.toSymmKernel.comap f hf.measurable μ - W.toSymmKernel.comap g hg.measurable μ) := by
  set h : Ω → Ω₁ × Ω₂ := fun x => (f x, g x) with hdef
  have : IsProbabilityMeasure (μ.map h) := (isCoupling_map_prodMk hf hg).isProbabilityMeasure
  refine (cutDist_le U W (isCoupling_map_prodMk hf hg)).trans ?_
  have hmp : MeasurePreserving h μ (μ.map h) := ⟨hf.measurable.prodMk hg.measurable, rfl⟩
  refine (cutNorm_le_cutNorm_comap _ hmp (overlayDiff U W (μ.map h))).trans_eq ?_
  congr 1
  ext x y
  simp [hdef]

variable [IsProbabilityMeasure μ]

/-- **The cut distance of two graphons on one carrier is at most the cut norm of their
difference.** It is the identity case of `cutDist_le_cutNorm_sub_of_measurePreserving`, realised by
the diagonal coupling.

The reverse inequality is false: two graphons that differ by a measure-preserving rearrangement of
the carrier are at cut distance zero while their difference can have cut norm bounded away from
zero. -/
theorem cutDist_le_cutNorm_sub (U W : Graphon Ω μ) :
    cutDist U W ≤ cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
  have := cutDist_le_cutNorm_sub_of_measurePreserving U W (MeasurePreserving.id μ)
    (MeasurePreserving.id μ)
  rwa [SymmKernel.comap_id, SymmKernel.comap_id] at this

/-- The cut distance of a graphon to itself is zero. -/
@[simp]
theorem cutDist_self (U : Graphon Ω μ) : cutDist U U = 0 :=
  le_antisymm (by simpa using cutDist_le_cutNorm_sub U U) (cutDist_nonneg U U)

end CommonCarrier

end DenseGraphLimits

end TauCeti
