/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Basic
public import TauCeti.MeasureTheory.Measure.Coupling

/-!
# The overlaid difference of two graphons

Given a coupling of two probability spaces, two graphons living on *different* carriers can be
compared: read `U` through the first coordinate, read `W` through the second, and subtract. The
result is the **overlaid difference kernel** `overlayDiff U W π`, a symmetric kernel on the coupled
space `(Ω₁ × Ω₂, π)`. The carrier-independent coupling API lives in
`TauCeti.MeasureTheory.Measure.Coupling`.

These two objects are what makes the cut distance of the dense graph limit theory cross-carrier.
`cutDist U W` is the infimum, over all couplings `π`, of the cut norm of `overlayDiff U W π`; the
cut norm acts on kernels, and `overlayDiff U W π` is exactly the kernel it is applied to. Neither
object needs a standard Borel or atomless hypothesis, which is why the resulting distance is
*defined* on arbitrary probability carriers. That its triangle inequality also holds there is a
separate result, proved by step-graphon approximation (Janson, Lemma 6.5) rather than by gluing
couplings, and is not built here.

**`overlayDiff` does not need the coupling hypothesis.** The measure argument of `SymmKernel` is a
phantom parameter, so the kernel `fun p q => U p.1 q.1 - W p.2 q.2` is well-formed over *any*
measure `π` on `Ω₁ × Ω₂`. The marginal conditions enter one level up, where the cut norm integrates
against `π`; keeping them off the constructor means the pointwise algebra below — and in particular
`overlayDiff_swap`, the swap symmetry the cut distance's `cutDist_comm` runs on — carries no
hypotheses at all.

## Main definitions

* `TauCeti.DenseGraphLimits.overlayDiff` — the overlaid difference kernel of two graphons on a
  coupling of their carriers.

## Main results

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
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}

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

/-- The overlaid difference evaluates as the difference of the two graphons read through the two
coordinates. -/
@[simp]
theorem overlayDiff_apply (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂))
    (p q : Ω₁ × Ω₂) : overlayDiff U W π p q = U p.1 q.1 - W p.2 q.2 := by
  simp [overlayDiff]

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

`TauCeti.MeasureTheory.diagonalCoupling μ` is the pushforward of `μ` along that same diagonal, and
by `TauCeti.MeasureTheory.isCoupling_diagonalCoupling` it is one of the couplings the cross-carrier
cut distance takes an infimum over. This identity computes the kernel it contributes; recognizing
the resulting value as the same-carrier cut norm `‖U - W‖□` additionally needs the cut norm's
change of variables along a pushforward, which is not part of this file. -/
theorem comap_overlayDiff_diagonalCoupling {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U W : Graphon Ω μ) :
    (overlayDiff U W (TauCeti.MeasureTheory.diagonalCoupling μ)).comap (fun x => (x, x))
        (measurable_id'.prodMk measurable_id') μ = U.toSymmKernel - W.toSymmKernel := by
  ext x y
  simp

end OverlayDiff

end DenseGraphLimits

end TauCeti
