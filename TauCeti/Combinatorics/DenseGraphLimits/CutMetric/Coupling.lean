/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Couplings of carriers, and the overlaid difference of two graphons

A **coupling** of two probability spaces `(Ω₁, μ₁)` and `(Ω₂, μ₂)` is a probability measure `π` on
`Ω₁ × Ω₂` whose two marginals are `μ₁` and `μ₂`. Given a coupling, two graphons living on
*different* carriers can be compared: read `U` through the first coordinate, read `W` through the
second, and subtract. The result is the **overlaid difference kernel** `overlayDiff U W π`, a
symmetric kernel on the coupled space `(Ω₁ × Ω₂, π)`.

These two objects are what makes the cut distance of the dense graph limit theory cross-carrier.
`cutDist U W` is the infimum, over all couplings `π`, of the cut norm of `overlayDiff U W π`; the
cut norm acts on kernels, and `overlayDiff U W π` is exactly the kernel it is applied to. Neither
object needs a standard Borel or atomless hypothesis, which is why the resulting distance is
*defined* on arbitrary probability carriers. That its triangle inequality also holds there is a
separate result, proved by step-graphon approximation (Janson, Lemma 6.5) rather than by gluing
couplings, and is not built here.

**`IsCoupling` is a `Prop`, not a structure or a class.** A coupling of two given marginals is not
canonical: the independent coupling `μ₁ ⊗ μ₂` and, on a common carrier, the diagonal coupling are
both couplings of the same pair, and the cut distance minimizes over all of them. A typeclass would
have instance resolution silently pick one. The predicate is stated with Mathlib's marginals
`MeasureTheory.Measure.fst` and `MeasureTheory.Measure.snd`, matching the optimal transport
gluing API of `TauCeti/MeasureTheory/OptimalTransport/Gluing.lean`, whose hypotheses and conclusions
are phrased the same way, so a plan composed there is recognized as a coupling here by `rw`.

**`overlayDiff` does not need the coupling hypothesis.** The measure argument of `SymmKernel` is a
phantom parameter, so the kernel `fun p q => U p.1 q.1 - W p.2 q.2` is well-formed over *any*
measure `π` on `Ω₁ × Ω₂`. The marginal conditions enter one level up, where the cut norm integrates
against `π`; keeping them off the constructor means the pointwise algebra below — and in particular
`overlayDiff_swap`, the swap symmetry the cut distance's `cutDist_comm` runs on — carries no
hypotheses at all.

## Main definitions

* `TauCeti.DenseGraphLimits.IsCoupling` — the predicate "`π` has marginals `μ₁` and `μ₂`";
* `TauCeti.DenseGraphLimits.diagonalCoupling` — the coupling of a probability space with itself
  carried by the diagonal;
* `TauCeti.DenseGraphLimits.overlayDiff` — the overlaid difference kernel of two graphons on a
  coupling of their carriers.

## Main results

* `isCoupling_prod` and `isCoupling_diagonalCoupling` — the independent and diagonal couplings;
  the first is what makes the set `cutDist` minimizes over nonempty, and the two together show that
  couplings of a given pair of marginals are not unique, which is why `IsCoupling` is a `Prop`;
* `IsCoupling.isProbabilityMeasure` — a coupling of probability measures is one;
* `IsCoupling.measurePreserving_fst` / `_snd` and `IsCoupling.integral_comp_fst` / `_snd` — the
  marginal conditions as measure-preserving projections, and as the identity that an integrand
  depending on one coordinate only integrates against `π` exactly as against that marginal;
* `IsCoupling.swap` — a coupling of `μ₁, μ₂` swaps to one of `μ₂, μ₁`;
* `overlayDiff_apply`, `abs_overlayDiff_apply_le_one` — the eliminator and the `[-1, 1]` bound;
* `overlayDiff_swap` — swapping the two graphons negates the overlaid difference, up to the pullback
  along `Prod.swap`, for *any* two measures on the two products;
* `comap_overlayDiff_diagonalCoupling` — on a common carrier the overlaid difference along the
  diagonal coupling pulls back along the diagonal to the plain difference `U - W`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — `IsCoupling`, `isCoupling_prod`,
  `overlayDiff` and `overlayDiff_apply`, the ingredients of the coupling-primary cross-carrier
  `cutDist`. The cut norm, `cutDist` itself, its triangle inequality, and the `GraphonSpace`
  quotient are separate targets and are not built here. The signatures follow
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`, which pins `IsCoupling` as a `Prop` (not a
  structure or class) for the reason recorded above.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §6 — cut distance via couplings.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §8.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- A **coupling** of `μ₁` and `μ₂`: a measure on the product whose marginals are `μ₁` and `μ₂`.

Deliberately a `Prop` rather than a structure or a class: a coupling of two given marginals is not
canonical, and the cut distance minimizes over all of them. Use `isCoupling_iff` to unfold. -/
def IsCoupling (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (π : Measure (Ω₁ × Ω₂)) : Prop :=
  π.fst = μ₁ ∧ π.snd = μ₂

variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}

/-- The defining conditions of `IsCoupling`. The definition's body is not exposed, so this is the
lemma downstream modules should rewrite with. -/
theorem isCoupling_iff : IsCoupling μ₁ μ₂ π ↔ π.fst = μ₁ ∧ π.snd = μ₂ := (Iff.rfl)

/-- The first marginal of a coupling. -/
theorem IsCoupling.fst_eq (hπ : IsCoupling μ₁ μ₂ π) : π.fst = μ₁ := isCoupling_iff.1 hπ |>.1

/-- The second marginal of a coupling. -/
theorem IsCoupling.snd_eq (hπ : IsCoupling μ₁ μ₂ π) : π.snd = μ₂ := isCoupling_iff.1 hπ |>.2

/-- The first projection out of a coupling is measure preserving. This is the marginal condition in
the form the integral transfer below consumes, and the form the measure-preserving-map picture of
the cut distance is stated in. -/
theorem IsCoupling.measurePreserving_fst (hπ : IsCoupling μ₁ μ₂ π) :
    MeasurePreserving Prod.fst π μ₁ :=
  ⟨measurable_fst, hπ.fst_eq⟩

/-- The second projection out of a coupling is measure preserving. -/
theorem IsCoupling.measurePreserving_snd (hπ : IsCoupling μ₁ μ₂ π) :
    MeasurePreserving Prod.snd π μ₂ :=
  ⟨measurable_snd, hπ.snd_eq⟩

/-- A coupling of probability measures is itself a probability measure.

This is why the cut norm — which needs a finite measure to integrate against — may be applied to a
kernel on the coupled space without a further hypothesis. -/
theorem IsCoupling.isProbabilityMeasure [IsProbabilityMeasure μ₁] (hπ : IsCoupling μ₁ μ₂ π) :
    IsProbabilityMeasure π :=
  ⟨by rw [← Measure.fst_univ, hπ.fst_eq, measure_univ]⟩

/-- The **independent coupling**: the product measure couples its two factors.

Every pair of probability spaces therefore admits a coupling, so the infimum defining the cut
distance is taken over a nonempty set. -/
theorem isCoupling_prod (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] : IsCoupling μ₁ μ₂ (μ₁.prod μ₂) :=
  isCoupling_iff.2 ⟨Measure.fst_prod, Measure.snd_prod⟩

/-- Swapping the two coordinates of a coupling of `μ₁` and `μ₂` gives a coupling of `μ₂` and `μ₁`.

Together with `overlayDiff_swap` this is what makes the cut distance symmetric. -/
theorem IsCoupling.swap (hπ : IsCoupling μ₁ μ₂ π) : IsCoupling μ₂ μ₁ (π.map Prod.swap) :=
  isCoupling_iff.2
    ⟨by rw [Measure.fst_map_swap, hπ.snd_eq], by rw [Measure.snd_map_swap, hπ.fst_eq]⟩

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function of the first coordinate integrates against a coupling as it does against the first
marginal: an integrand that reads only one coordinate is blind to which coupling it is integrated
against. (A homomorphism density is an integral over `Ω ^ V(F)` of a product of kernel values, so
transporting one needs the iterated form of `measurePreserving_fst`, not this lemma.) -/
theorem IsCoupling.integral_comp_fst (hπ : IsCoupling μ₁ μ₂ π) {f : Ω₁ → E}
    (hf : AEStronglyMeasurable f μ₁) : ∫ p, f p.1 ∂π = ∫ x, f x ∂μ₁ := by
  rw [← hπ.measurePreserving_fst.map_eq] at hf ⊢
  exact (integral_map measurable_fst.aemeasurable hf).symm

/-- A function of the second coordinate integrates against a coupling as it does against the second
marginal. -/
theorem IsCoupling.integral_comp_snd (hπ : IsCoupling μ₁ μ₂ π) {f : Ω₂ → E}
    (hf : AEStronglyMeasurable f μ₂) : ∫ p, f p.2 ∂π = ∫ x, f x ∂μ₂ := by
  rw [← hπ.measurePreserving_snd.map_eq] at hf ⊢
  exact (integral_map measurable_snd.aemeasurable hf).symm

end Integral

section Diagonal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **diagonal coupling** of a measure with itself: the pushforward of `μ` along `x ↦ (x, x)`.

It is the coupling that reads two graphons on a common carrier at the *same* point: it couples `μ`
with itself (`isCoupling_diagonalCoupling`), and the overlaid difference taken along it pulls back
along the diagonal to the plain difference `U - W` (`comap_overlayDiff_diagonalCoupling`). Use
`diagonalCoupling_apply` to compute it. -/
def diagonalCoupling (μ : Measure Ω) : Measure (Ω × Ω) := μ.map fun x => (x, x)

/-- The diagonal coupling of a measurable set is the measure of its diagonal slice. -/
theorem diagonalCoupling_apply (μ : Measure Ω) {s : Set (Ω × Ω)} (hs : MeasurableSet s) :
    diagonalCoupling μ s = μ {x | (x, x) ∈ s} := by
  rw [diagonalCoupling, Measure.map_apply (measurable_id'.prodMk measurable_id') hs]
  rfl

/-- The diagonal coupling is a coupling of `μ` with itself. -/
theorem isCoupling_diagonalCoupling (μ : Measure Ω) : IsCoupling μ μ (diagonalCoupling μ) :=
  isCoupling_iff.2
    ⟨by rw [diagonalCoupling, Measure.fst_map_prodMk measurable_id', Measure.map_id'],
      by rw [diagonalCoupling, Measure.snd_map_prodMk measurable_id', Measure.map_id']⟩

/-- The diagonal coupling of a probability measure is a probability measure. -/
instance instIsProbabilityMeasureDiagonalCoupling (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (diagonalCoupling μ) :=
  (isCoupling_diagonalCoupling μ).isProbabilityMeasure

end Diagonal

section OverlayDiff

variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- The **overlaid difference kernel** of two graphons along a measure `π` on the product of their
carriers: `U` read through the first coordinate minus `W` read through the second.

This is the kernel whose cut norm the cut distance minimizes over couplings — not a neutral overlay
of the two graphons, but the difference that the counting lemma bounds a density gap by. It is a
literal difference of two `SymmKernel.comap`s, so the kernel algebra applies to it directly.

The measure `π` is unconstrained here: `SymmKernel` carries its measure as a phantom parameter, and
the marginal conditions are only needed once the cut norm integrates against `π`. -/
def overlayDiff (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂)) :
    SymmKernel (Ω₁ × Ω₂) π :=
  U.toSymmKernel.comap Prod.fst measurable_fst π - W.toSymmKernel.comap Prod.snd measurable_snd π

/-- The overlaid difference is the difference of the two coordinate pullbacks. Outside this module,
use this to unfold `overlayDiff`. -/
theorem overlayDiff_eq_comap_sub_comap (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (π : Measure (Ω₁ × Ω₂)) :
    overlayDiff U W π =
      U.toSymmKernel.comap Prod.fst measurable_fst π -
        W.toSymmKernel.comap Prod.snd measurable_snd π := (rfl)

/-- The overlaid difference evaluates as the difference of the two graphons read through the two
coordinates. -/
@[simp]
theorem overlayDiff_apply (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂))
    (p q : Ω₁ × Ω₂) : overlayDiff U W π p q = U p.1 q.1 - W p.2 q.2 := by
  rw [overlayDiff_eq_comap_sub_comap]
  simp

/-- The overlaid difference of two graphons takes values in `[-1, 1]`: it is a difference of two
`[0, 1]`-valued functions. -/
theorem abs_overlayDiff_apply_le_one (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (π : Measure (Ω₁ × Ω₂)) (p q : Ω₁ × Ω₂) : |overlayDiff U W π p q| ≤ 1 := by
  have h₁ := U.nonneg p.1 q.1
  have h₂ := U.le_one p.1 q.1
  have h₃ := W.nonneg p.2 q.2
  have h₄ := W.le_one p.2 q.2
  rw [overlayDiff_apply, abs_le]
  constructor <;> linarith

/-- Swapping the roles of the two graphons — and correspondingly the two coordinates of the
coupling — negates the overlaid difference.

This is the identity behind the symmetry of the cut distance: the cut norm is even and invariant
under the pullback along the measure-preserving `Prod.swap`, so the two infima agree. Both measures
are unconstrained — they are phantom parameters of the two kernel types — so a caller holding a
coupling `ρ` of `μ₂, μ₁` may use it directly, without rewriting `ρ` into the form `π.map Prod.swap`
inside its type. -/
theorem overlayDiff_swap (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂))
    (ρ : Measure (Ω₂ × Ω₁)) :
    overlayDiff W U ρ = -(overlayDiff U W π).comap Prod.swap measurable_swap ρ := by
  ext p q
  simp

/-- On a common carrier, the overlaid difference of `U` and `W` along the diagonal coupling pulls
back along the diagonal `x ↦ (x, x)` to their plain difference as kernels.

`diagonalCoupling μ` is the pushforward of `μ` along that same diagonal, and by
`isCoupling_diagonalCoupling` it is one of the couplings the cross-carrier cut distance takes an
infimum over. This identity computes the kernel it contributes; recognizing the resulting value as
the same-carrier cut norm `‖U - W‖□` additionally needs the cut norm's change of variables along a
pushforward, which is not part of this file. -/
theorem comap_overlayDiff_diagonalCoupling {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U W : Graphon Ω μ) :
    (overlayDiff U W (diagonalCoupling μ)).comap (fun x => (x, x))
        (measurable_id'.prodMk measurable_id') μ = U.toSymmKernel - W.toSymmKernel := by
  ext x y
  simp

end OverlayDiff

end DenseGraphLimits

end TauCeti
