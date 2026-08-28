/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance
import TauCeti.MeasureTheory.Measure.UnitIntervalMap
import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback

/-!
# The map form of the cut distance, and its agreement with the coupling form

The **map form** of the cut distance is the classical one: read both graphons on the canonical
carrier `(I, volume)` through measure-preserving maps, and take the infimum of the cut norm of the
difference of the two pullbacks,

`δ□ᵐᵃᵖ(U, W) = inf { ‖U ∘ (f × f) − W ∘ (g × g)‖□ | f : I → Ω₁, g : I → Ω₂ measure preserving }`.

The main result is that it agrees with the coupling-primary `cutDist` over standard Borel carriers,
`cutDist_eq_cutDistPullback`. This is the design equivalence that justifies taking the coupling
form as primary: nothing is lost by doing so, since on the carriers where the classical definition
is usually stated the two numbers are equal.

**Atoms are allowed.** No atomless hypothesis appears on either carrier, and none is needed. The
inequality `cutDistPullback ≤ cutDist` turns a coupling into a pair of maps by pushing `(I, volume)`
forward onto the coupling itself — a probability measure on the standard Borel space `Ω₁ × Ω₂` —
and `exists_measurePreserving_from_unitInterval` (Janson, Thm A.9) does that with no atomless
hypothesis. That is the whole content of the harder direction: an *arbitrary* coupling, however
atomic, is realized by a pair of measure-preserving maps out of `(I, volume)`, because the pair of
projections of such a realization has the coupling as its joint law. The companion
`CutMetric.Pullback.Validation` module instantiates the equivalence at a point-mass coupling, at a
finitely atomic one, and at one mixing an atomic with a continuous direction; these regressions are
what the absence of an atomless hypothesis buys, and each fails to typecheck for any formulation
that assumes one.

**Why the easy direction is easy.** A pair of measure-preserving maps `f, g` out of a common
carrier pushes that carrier forward to a coupling along `x ↦ (f x, g x)`, and the overlaid
difference along that coupling pulls back to the plain difference of pullbacks — this is
`cutDist_le_cutNorm_sub_of_measurePreserving`, already available on an arbitrary common carrier.
Specializing it to `(I, volume)` gives `cutDist ≤ cutDistPullback` outright.

**The junk value.** `cutDistPullback` is an infimum over a set of reals that is empty when a
carrier receives no measure-preserving map from `(I, volume)` at all, and then it is `0` by the
`sInf` convention. The elimination rules — and `cutDist_le_cutDistPullback` through them — carry
standard Borel hypotheses on the two carriers that rule this out (`pullbackCutNorms_nonempty`);
`cutDistPullback_le_cutDist` runs the other way and only needs the product carrier standard Borel,
which is where it applies Thm A.9. The range and common-carrier bounds hold with no such hypothesis
at all: in the empty case they reduce to the corresponding fact about `0`, and in the nonempty case
any witness supplies the required upper bound.

## Main definitions

* `TauCeti.DenseGraphLimits.cutDistPullback` — the infimum, over pairs of measure-preserving maps
  from `(I, volume)` to the two carriers, of the cut norm of the difference of the two pullbacks.

## Main results

* `cutDist_eq_cutDistPullback` — **the coupling and map forms of the cut distance agree** over
  standard Borel carriers, atoms allowed; it is `cutDist_le_cutDistPullback` and
  `cutDistPullback_le_cutDist` together;
* `cutDistPullback_le` and `le_cutDistPullback` are the introduction and elimination rules for the
  infimum, and `exists_measurePreserving_cutNorm_sub_lt` produces a pair of maps beating any strict
  upper bound; `cutDistPullback_def` spells the defining infimum out in public terms;
* `cutDistPullback_comm` is symmetry, and holds with no hypothesis on either carrier;
* `cutDistPullback_nonneg`, `cutDistPullback_le_one`, `cutDistPullback_self` and
  `cutDistPullback_le_cutNorm_sub` are the range and the same-carrier bounds.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Thm 6.9 (the two forms agree) with Thm A.9 (the transport from `(I, volume)`).
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §8.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 5 — `cutDistPullback` and
  `cutDist_eq_cutDistPullback`, whose signatures follow
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean` (with the two carrier measures implicit, as
  they are for `cutDist` here). The atomless mod-null equivalence
  `exists_mpModNull_equiv_unitInterval` is the layer's other target and is not built here.
-/

public section

noncomputable section

open MeasureTheory TauCeti.MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- The set of cut norms of the difference of the two pullbacks, one for each pair of
measure-preserving maps from `(I, volume)` to the two carriers. The map form of the cut distance is
its infimum.

Bounded below by `0` through `nonneg_of_mem_pullbackCutNorms`, and nonempty over standard Borel
carriers by `pullbackCutNorms_nonempty`; both facts are needed by the `csInf` rules, and are stated
once here rather than unfolded at each use. -/
private def pullbackCutNorms (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : Set ℝ :=
  {r | ∃ (f : I → Ω₁) (g : I → Ω₂) (hf : MeasurePreserving f volume μ₁)
      (hg : MeasurePreserving g volume μ₂),
    cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
      - W.toSymmKernel.comap g hg.measurable volume) = r}

/-- Every pair of measure-preserving maps contributes its pulled-back cut norm. -/
private theorem mem_pullbackCutNorms (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {f : I → Ω₁}
    {g : I → Ω₂} (hf : MeasurePreserving f volume μ₁) (hg : MeasurePreserving g volume μ₂) :
    cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
      - W.toSymmKernel.comap g hg.measurable volume) ∈ pullbackCutNorms U W :=
  ⟨f, g, hf, hg, rfl⟩

/-- Over standard Borel carriers there is at least one pair of maps to compare along: this is
Janson's Thm A.9, applied to each carrier separately. -/
private theorem pullbackCutNorms_nonempty [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : (pullbackCutNorms U W).Nonempty := by
  obtain ⟨f, hf⟩ := Measure.exists_measurePreserving_from_unitInterval μ₁
  obtain ⟨g, hg⟩ := Measure.exists_measurePreserving_from_unitInterval μ₂
  exact ⟨_, mem_pullbackCutNorms U W hf hg⟩

/-- Every pulled-back cut norm is nonnegative, being a cut norm. -/
private theorem nonneg_of_mem_pullbackCutNorms {U : Graphon Ω₁ μ₁} {W : Graphon Ω₂ μ₂} {r : ℝ}
    (hr : r ∈ pullbackCutNorms U W) : 0 ≤ r := by
  obtain ⟨f, g, hf, hg, rfl⟩ := hr
  exact cutNorm_nonneg volume _

/-- The set of pulled-back cut norms is bounded below by `0`. -/
private theorem bddBelow_pullbackCutNorms (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    BddBelow (pullbackCutNorms U W) :=
  ⟨0, fun _ hr => nonneg_of_mem_pullbackCutNorms hr⟩

/-- **The map form of the cut distance**: the infimum, over measure-preserving maps from the
canonical carrier `(I, volume)` to each of `(Ω₁, μ₁)` and `(Ω₂, μ₂)`, of the cut norm of the
difference of the two pullbacks.

This is the classical definition. Over standard Borel carriers it agrees with the
coupling-primary `cutDist` (`cutDist_eq_cutDistPullback`); off them it can be a junk `0`, since the
infimum is then taken over an empty set. -/
def cutDistPullback (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : ℝ := sInf (pullbackCutNorms U W)

/-- The defining infimum of the map form of the cut distance, with its index set spelled out in
public terms: the cut norms of the differences of the two pullbacks, one for each pair of
measure-preserving maps out of `(I, volume)`.

Ordinary use should go through `cutDistPullback_le` and `le_cutDistPullback` instead; this is the
escape hatch for a goal that has to be stated or rewritten at the infimum itself. -/
theorem cutDistPullback_def (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDistPullback U W =
      sInf {r | ∃ (f : I → Ω₁) (g : I → Ω₂) (hf : MeasurePreserving f volume μ₁)
        (hg : MeasurePreserving g volume μ₂),
        cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
          - W.toSymmKernel.comap g hg.measurable volume) = r} := by
  rw [cutDistPullback, pullbackCutNorms]

/-- The map form of the cut distance is at most the pulled-back cut norm along any pair of
measure-preserving maps: the introduction rule for the infimum. -/
theorem cutDistPullback_le (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {f : I → Ω₁} {g : I → Ω₂}
    (hf : MeasurePreserving f volume μ₁) (hg : MeasurePreserving g volume μ₂) :
    cutDistPullback U W ≤ cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
      - W.toSymmKernel.comap g hg.measurable volume) :=
  csInf_le (bddBelow_pullbackCutNorms U W) (mem_pullbackCutNorms U W hf hg)

/-- To bound the map form of the cut distance from below it suffices to bound every pulled-back cut
norm from below: the elimination rule for the infimum. The standard Borel hypotheses are what make
the infimum a genuine one rather than the empty-set junk value. -/
theorem le_cutDistPullback [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] {c : ℝ}
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : ∀ (f : I → Ω₁) (g : I → Ω₂) (hf : MeasurePreserving f volume μ₁)
      (hg : MeasurePreserving g volume μ₂),
      c ≤ cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
        - W.toSymmKernel.comap g hg.measurable volume)) :
    c ≤ cutDistPullback U W :=
  le_csInf (pullbackCutNorms_nonempty U W) (by
    rintro r ⟨f, g, hf, hg, rfl⟩
    exact h f g hf hg)

/-- Any strict upper bound on the map form of the cut distance is beaten by some pair of
measure-preserving maps. This is the form in which a `cutDistPullback` hypothesis is used: it turns
an infimum into an explicit pair of maps. -/
theorem exists_measurePreserving_cutNorm_sub_lt [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {c : ℝ} (h : cutDistPullback U W < c) :
    ∃ (f : I → Ω₁) (g : I → Ω₂) (hf : MeasurePreserving f volume μ₁)
      (hg : MeasurePreserving g volume μ₂),
      cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
        - W.toSymmKernel.comap g hg.measurable volume) < c := by
  rw [cutDistPullback] at h
  obtain ⟨r, ⟨f, g, hf, hg, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt (pullbackCutNorms_nonempty U W) h
  exact ⟨f, g, hf, hg, hlt⟩

/-- Exchanging the roles of the two maps negates the difference of the pullbacks, and the cut norm
is even, so each pulled-back cut norm for `U, W` is one for `W, U`. -/
private theorem pullbackCutNorms_subset_comm (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    pullbackCutNorms U W ⊆ pullbackCutNorms W U := by
  rintro r ⟨f, g, hf, hg, rfl⟩
  refine ⟨g, f, hg, hf, ?_⟩
  rw [← cutNorm_neg volume (W.toSymmKernel.comap g hg.measurable volume
    - U.toSymmKernel.comap f hf.measurable volume), neg_sub]

/-- The index set of the map form is symmetric in the two graphons. -/
private theorem pullbackCutNorms_comm (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    pullbackCutNorms U W = pullbackCutNorms W U :=
  subset_antisymm (pullbackCutNorms_subset_comm U W) (pullbackCutNorms_subset_comm W U)

/-- The map form of the cut distance is symmetric.

No hypothesis is needed: the two infima are taken over *the same* set of reals, since a pair
`(f, g)` for `(U, W)` is a pair `(g, f)` for `(W, U)` with the same value. -/
theorem cutDistPullback_comm (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDistPullback U W = cutDistPullback W U := by
  rw [cutDistPullback, cutDistPullback, pullbackCutNorms_comm]

/-- The map form of the cut distance is nonnegative. -/
theorem cutDistPullback_nonneg (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    0 ≤ cutDistPullback U W := by
  rw [cutDistPullback]
  by_cases h : (pullbackCutNorms U W).Nonempty
  · exact le_csInf h fun _ hr => nonneg_of_mem_pullbackCutNorms hr
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-! ### The two forms agree -/

/-- **A pair of measure-preserving maps bounds the cut distance from above.** This is the easy half
of `cutDist_eq_cutDistPullback`: the graph of `(f, g)` pushes `volume` forward to a coupling, along
which the overlaid difference is exactly the difference of the two pullbacks. -/
theorem cutDist_le_cutDistPullback [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : cutDist U W ≤ cutDistPullback U W :=
  le_cutDistPullback U W fun _ _ hf hg => cutDist_le_cutNorm_sub_of_measurePreserving U W hf hg

/-- **Every coupling is realized by a pair of measure-preserving maps.** This is the substance of
`cutDist_eq_cutDistPullback`.

A coupling `π` of `μ₁` and `μ₂` is a probability measure on `Ω₁ × Ω₂`, so Janson's Thm A.9 gives a
measure-preserving `h : I → Ω₁ × Ω₂`. Its two coordinates are measure preserving onto the two
carriers, and `h` is their pairing, so the overlaid difference along `π` pulls back along `h` to the
difference of the two pullbacks. No atomless hypothesis enters: `π` may be a point mass.

Only the product carrier is assumed standard Borel, which is all Thm A.9 is applied to here; when
both factors are standard Borel — the hypotheses of `cutDist_eq_cutDistPullback` — the instance is
synthesized from them. -/
theorem cutDistPullback_le_cutDist [StandardBorelSpace (Ω₁ × Ω₂)]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : cutDistPullback U W ≤ cutDist U W := by
  refine le_cutDist U W fun π hπ => ?_
  have := hπ.isProbabilityMeasure
  obtain ⟨h, hh⟩ := Measure.exists_measurePreserving_from_unitInterval π
  have hf : MeasurePreserving (fun t => (h t).1) volume μ₁ := hπ.measurePreserving_fst.comp hh
  have hg : MeasurePreserving (fun t => (h t).2) volume μ₂ := hπ.measurePreserving_snd.comp hh
  refine (cutDistPullback_le U W hf hg).trans_eq ?_
  exact (cutNorm_overlayDiff_map_prodMk U W hf.measurable hg.measurable hh).symm

/-- **The coupling and map forms of the cut distance agree**, over standard Borel carriers, with
atoms allowed.

This is the design equivalence behind the coupling-primary definition: the classical
measure-preserving-map infimum is not more general, so nothing is lost by taking the cross-carrier
coupling form — which needs no hypothesis even to be stated — as the primary object. In particular
the whole `cutDist` API transfers to `cutDistPullback` over standard Borel carriers. -/
theorem cutDist_eq_cutDistPullback [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : cutDist U W = cutDistPullback U W :=
  le_antisymm (cutDist_le_cutDistPullback U W) (cutDistPullback_le_cutDist U W)

/-- The map form of the cut distance is at most `1`. -/
theorem cutDistPullback_le_one (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDistPullback U W ≤ 1 := by
  by_cases h : (pullbackCutNorms U W).Nonempty
  · obtain ⟨_, f, g, hf, hg, rfl⟩ := h
    refine (cutDistPullback_le U W hf hg).trans ((cutNorm_le_integral_abs _ _).trans ?_)
    calc
      ∫ p, |U.toSymmKernel.comap f hf.measurable volume p.1 p.2 -
          W.toSymmKernel.comap g hg.measurable volume p.1 p.2| ∂(volume.prod volume)
          ≤ ∫ _p, (1 : ℝ) ∂(volume.prod volume) :=
        integral_mono
          (U.toSymmKernel.comap f hf.measurable volume -
            W.toSymmKernel.comap g hg.measurable volume).integrable_uncurry.abs
          (integrable_const 1) fun p => by
            simp only [SymmKernel.comap_apply, Graphon.coe_toSymmKernel]
            rw [abs_le]
            constructor <;> linarith [U.nonneg (f p.1) (f p.2), U.le_one (f p.1) (f p.2),
              W.nonneg (g p.1) (g p.2), W.le_one (g p.1) (g p.2)]
      _ = 1 := by simp
  · rw [cutDistPullback, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]
    norm_num

section CommonCarrier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The map form of the cut distance of a graphon to itself is zero. -/
@[simp]
theorem cutDistPullback_self (U : Graphon Ω μ) : cutDistPullback U U = 0 := by
  by_cases h : (pullbackCutNorms U U).Nonempty
  · obtain ⟨_, f, _, hf, _, _⟩ := h
    exact le_antisymm (by simpa using cutDistPullback_le U U hf hf) (cutDistPullback_nonneg U U)
  · rw [cutDistPullback, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- On a common carrier the map form of the cut distance is at most the cut norm of the difference.
As for `cutDist_le_cutNorm_sub`, the reverse inequality is false: a measure-preserving rearrangement
of the carrier leaves the left-hand side at `0` while the right-hand side can be bounded away from
it. -/
theorem cutDistPullback_le_cutNorm_sub (U W : Graphon Ω μ) :
    cutDistPullback U W ≤ cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
  by_cases h : (pullbackCutNorms U W).Nonempty
  · obtain ⟨_, f, _, hf, _, _⟩ := h
    calc
      cutDistPullback U W ≤ cutNorm volume
          (U.toSymmKernel.comap f hf.measurable volume -
            W.toSymmKernel.comap f hf.measurable volume) := cutDistPullback_le U W hf hf
      _ = cutNorm volume
          ((U.toSymmKernel - W.toSymmKernel).comap f hf.measurable volume) := by
            rw [SymmKernel.comap_sub]
      _ = cutNorm μ (U.toSymmKernel - W.toSymmKernel) :=
        cutNorm_comap hf (U.toSymmKernel - W.toSymmKernel)
  · rw [cutDistPullback, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]
    exact cutNorm_nonneg μ _

end CommonCarrier

end DenseGraphLimits

end TauCeti
