/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance
public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Pullback
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# The almost-everywhere view of a graphon

A graphon is carried as a *strict* function `W : Ω → Ω → ℝ`, symmetric and `[0, 1]`-valued at every
point.  This file is the single place where the almost-everywhere picture enters: it sends a
graphon to its class `Graphon.toAEEqFun W : (Ω × Ω) →ₘ[μ ⊗ μ] ℝ` in Mathlib's `AEEqFun`, proves
that the three observables — homomorphism densities, the cut norm, and the cut distance — do not
see the difference between two representatives of one class, and exhibits the reverse passage: an
a.e. `[0, 1]`-valued, a.e. symmetric class is the class of a strict graphon.

**Why the bridge is a deliverable and not a definition change.** Carrying the strict function is
what makes `U - W` a literal kernel and `∀ x y, W x y ∈ Set.Icc 0 1` a stateable hypothesis, so the
cut norm and the counting lemma never carry a null-set side condition.  The price is that
representatives are not unique, and analytic arguments that produce a function only up to a null
set — conditional expectations and martingale limits — are naturally `AEEqFun`-native.  The
theorems below pay that price once: `homDensity_congr_ae`, `cutNorm_congr_ae` and
`cutDist_eq_zero_of_aeEq` say the strict representative may be chosen freely, and
`exists_graphon_repr` says such a choice always exists.

**The round trip is lossy in exactly one direction.** `Graphon.toAEEqFun` forgets the values of `W`
on a null set, so it is not injective; `exists_graphon_repr` inverts it only up to that forgetting.
What is *not* lost is the pair of pointwise constraints: the class of a graphon is a.e. `[0, 1]`
-valued and a.e. symmetric (`Graphon.toAEEqFun_mem_Icc_ae`, `Graphon.toAEEqFun_symm_ae`), and those
two conditions are exactly what a class needs in order to come from a graphon
(`exists_graphon_repr_iff`).  Symmetrising and clamping a measurable representative is what
converts "a.e." back into "everywhere".

## Main definitions

* `TauCeti.DenseGraphLimits.Graphon.toAEEqFun` — the a.e. class of a graphon on `μ ⊗ μ`.

## Main results

* `Graphon.toAEEqFun_eq_iff` — two graphons have the same class exactly when they agree a.e.;
* `Graphon.toAEEqFun_mem_Icc_ae`, `Graphon.toAEEqFun_symm_ae` — the class of a graphon is a.e.
  `[0, 1]`-valued and a.e. symmetric;
* `Graphon.toAEEqFun_comap` — the class of a measure-preserving pullback is the composition of the
  class with the pullback, Mathlib's `AEEqFun.compMeasurePreserving`;
* `cutNorm_congr_ae` and `SymmKernel.rectIntegral_congr_ae` — the cut norm, and already each
  rectangle integral, factor through the a.e. class of a kernel;
* `homDensity_congr_ae` — homomorphism densities factor through the a.e. class of a graphon;
* `cutNorm_overlayDiff_congr_ae_left`, `cutDist_congr_ae_left` and `cutDist_congr_ae_right` — the
  cut distance itself, not merely its vanishing, factors through the a.e. classes of its two
  arguments, on arbitrary carriers;
* `cutDist_eq_zero_of_aeEq` — a.e. equal graphons are at cut distance zero;
* `exists_graphon_repr` and `exists_graphon_repr_iff` — an a.e. `[0, 1]`-valued, a.e. symmetric
  class is the class of a strict graphon, and only such a class is.

## Implementation

The rectangle integrals of two a.e. equal kernels agree because a.e. equality passes to the
restriction of `μ ⊗ μ` to a rectangle, and the cut norm is a supremum of their absolute values.
For the cut distance the a.e. hypothesis lives on `μ₁ ⊗ μ₁` while the overlaid difference lives on
`π ⊗ π` for a coupling `π`; the first-coordinate projection relates them, and is measure preserving
exactly because `π` has left marginal `μ₁`.  Every coupling therefore contributes the same value to
the two infima, which gives the invariance of `δ□` with no triangle inequality; vanishing on a.e.
equal graphons is then the case `U' = W` of that invariance together with `cutDist_self`.

For homomorphism densities the a.e. hypothesis lives on `μ ⊗ μ` while the integral is over
`Measure.pi`, so it has to be transported along the evaluation map `x ↦ (x a, x b)` at the two
endpoints of an edge.  That map is measure preserving precisely because the endpoints of an edge of
a `SimpleGraph` are distinct (`TauCeti.measurePreserving_eval_pair`); the finitely many edges are
then intersected with `Filter.eventually_all_finset`.

The strict representative built by `exists_graphon_repr` is
`fun x y => max 0 (min 1 ((f (x, y) + f (y, x)) / 2))`: the average symmetrises *everywhere*, not
just a.e., and the clamping puts the values in `[0, 1]` everywhere.  Both operations are the
identity a.e., which is what makes the result represent the class it started from — and both are
needed, since a class has no reason to have a representative with either property on the nose.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 3 — the AE / `AEEqFun` view, with
  `toAEEqFun`, the measurable-representative section, and the invariance theorems
  `homDensity_congr_ae`, `cutNorm_congr_ae`, `cutDist_eq_zero_of_aeEq`.  The signatures follow
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.  The conditional-expectation and martingale
  arguments that consume this view are Layer 4 and are not built here.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §6 — graphons up to a.e. equality.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.
-/

public section

noncomputable section

open MeasureTheory TauCeti.MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **A rectangle integral only sees the a.e. class of the kernel.** Almost everywhere equality on
`μ ⊗ μ` restricts to any rectangle, so the two integrands agree there. -/
theorem SymmKernel.rectIntegral_congr_ae {K L : SymmKernel Ω μ}
    (h : ∀ᵐ p ∂(μ.prod μ), K p.1 p.2 = L p.1 p.2) (S T : Set Ω) :
    K.rectIntegral μ S T = L.rectIntegral μ S T := by
  rw [SymmKernel.rectIntegral_def, SymmKernel.rectIntegral_def]
  exact integral_congr_ae (ae_restrict_of_ae h)

section Kernel

variable [IsFiniteMeasure μ]

/-- **The cut norm factors through the a.e. class of a kernel.** Two kernels agreeing off a
`μ ⊗ μ`-null set have the same cut norm: they have the same rectangle integrals, and the cut norm
is the supremum of their absolute values. -/
theorem cutNorm_congr_ae {K L : SymmKernel Ω μ}
    (h : ∀ᵐ p ∂(μ.prod μ), K p.1 p.2 = L p.1 p.2) : cutNorm μ K = cutNorm μ L := by
  have hrect (S T : Set Ω) : K.rectIntegral μ S T = L.rectIntegral μ S T :=
    SymmKernel.rectIntegral_congr_ae h S T
  refine le_antisymm (cutNorm_le μ fun S hS T hT => ?_) (cutNorm_le μ fun S hS T hT => ?_)
  · rw [hrect]
    exact abs_rectIntegral_le_cutNorm μ L hS hT
  · rw [← hrect]
    exact abs_rectIntegral_le_cutNorm μ K hS hT

end Kernel

variable [IsProbabilityMeasure μ]

namespace Graphon

/-- **The a.e. class of a graphon**, an element of Mathlib's `AEEqFun` on the product carrier
`μ ⊗ μ`.

This is the one place the strict carrier is traded for an a.e. class.  Outside this module use
`Graphon.coeFn_toAEEqFun` and `Graphon.toAEEqFun_eq_iff` rather than unfolding the definition. -/
def toAEEqFun (W : Graphon Ω μ) : (Ω × Ω) →ₘ[μ.prod μ] ℝ :=
  AEEqFun.mk (fun p => W p.1 p.2) W.measurable.aestronglyMeasurable

/-- The class of a graphon is represented by the graphon itself. -/
theorem coeFn_toAEEqFun (W : Graphon Ω μ) :
    ⇑(toAEEqFun W) =ᵐ[μ.prod μ] fun p => W p.1 p.2 :=
  AEEqFun.coeFn_mk _ _

/-- **Two graphons have the same class exactly when they agree almost everywhere.** -/
theorem toAEEqFun_eq_iff {U W : Graphon Ω μ} :
    toAEEqFun U = toAEEqFun W ↔ ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = W p.1 p.2 :=
  AEEqFun.mk_eq_mk

/-- A graphon whose values agree a.e. with a given class has that class. -/
theorem toAEEqFun_eq_of_ae {W : Graphon Ω μ} {f : (Ω × Ω) →ₘ[μ.prod μ] ℝ}
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = f p) : toAEEqFun W = f := by
  rw [← AEEqFun.mk_coeFn f]
  exact AEEqFun.mk_eq_mk.2 h

/-- The class of a graphon is a.e. `[0, 1]`-valued — one of the two constraints that characterise
the classes coming from graphons. -/
theorem toAEEqFun_mem_Icc_ae (W : Graphon Ω μ) :
    ∀ᵐ p ∂(μ.prod μ), toAEEqFun W p ∈ Set.Icc (0 : ℝ) 1 :=
  (coeFn_toAEEqFun W).mono fun p hp => hp ▸ W.mem_Icc p.1 p.2

/-- The class of a graphon is a.e. symmetric — the other constraint characterising the classes
coming from graphons.  Symmetry of the representative is pointwise; transporting it to the class
uses that `Prod.swap` preserves `μ ⊗ μ`. -/
theorem toAEEqFun_symm_ae (W : Graphon Ω μ) :
    ∀ᵐ p ∂(μ.prod μ), toAEEqFun W p = toAEEqFun W p.swap := by
  have hswap : ∀ᵐ p ∂(μ.prod μ), toAEEqFun W p.swap = W p.2 p.1 :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (coeFn_toAEEqFun W)
  filter_upwards [coeFn_toAEEqFun W, hswap] with p hp hps
  rw [hp, hps, W.symm]

/-- **The a.e. view is compatible with measure-preserving pullbacks.** Pulling a graphon back along
a measure-preserving map is, on classes, Mathlib's `AEEqFun.compMeasurePreserving` along the
pullback of the product carrier. -/
theorem toAEEqFun_comap {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (W : Graphon Ω μ) {φ : Ω' → Ω} (hφ : MeasurePreserving φ μ' μ) :
    toAEEqFun (W.comap φ hφ.measurable μ') =
      AEEqFun.compMeasurePreserving (toAEEqFun W) (Prod.map φ φ) (hφ.prod hφ) := by
  refine toAEEqFun_eq_of_ae ?_
  have hpull : ∀ᵐ p ∂(μ'.prod μ'), toAEEqFun W (Prod.map φ φ p) = W (φ p.1) (φ p.2) :=
    (hφ.prod hφ).quasiMeasurePreserving.ae (coeFn_toAEEqFun W)
  filter_upwards [AEEqFun.coeFn_compMeasurePreserving (toAEEqFun W) (hφ.prod hφ), hpull]
    with p hp hpp
  rw [hp, Function.comp_apply, hpp, Graphon.comap_apply]

end Graphon

/-- **Homomorphism densities factor through the a.e. class of a graphon.** Changing a graphon on a
`μ ⊗ μ`-null set changes no `t(F, ·)`.

The hypothesis is the a.e. equality itself; for the equality of classes use
`Graphon.toAEEqFun_eq_iff`. -/
theorem homDensity_congr_ae {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    {U W : Graphon Ω μ} (h : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = W p.1 p.2) :
    homDensity F U = homDensity F W := by
  have hedge : ∀ e ∈ F.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => μ),
      edgeFactor U x e = edgeFactor W x e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab : a ≠ b := F.ne_of_adj (by simpa using he)
      simpa using
        (TauCeti.measurePreserving_eval_pair (fun _ : V => μ) hab).quasiMeasurePreserving.ae h
  rw [homDensity_def, homDensity_def]
  refine integral_congr_ae (((Filter.eventually_all_finset _).2 hedge).mono fun x hx => ?_)
  exact Finset.prod_congr rfl hx

section CutDistance

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- **Along any coupling, the overlaid cut norm only sees the a.e. class of the left graphon.**

Almost everywhere equality holds on `μ₁ ⊗ μ₁` while the overlaid difference lives on `π ⊗ π`; the
two are related by the first-coordinate projection, which is measure preserving precisely because
`π` is a coupling with left marginal `μ₁`. -/
theorem cutNorm_overlayDiff_congr_ae_left {U U' : Graphon Ω₁ μ₁} {W : Graphon Ω₂ μ₂}
    {π : Measure (Ω₁ × Ω₂)} (hπ : IsCoupling μ₁ μ₂ π)
    (h : ∀ᵐ p ∂(μ₁.prod μ₁), U p.1 p.2 = U' p.1 p.2) :
    @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U W π) =
      @cutNorm _ _ π hπ.isFiniteMeasure (overlayDiff U' W π) := by
  let _ := hπ.isFiniteMeasure
  refine cutNorm_congr_ae ?_
  have hmp : MeasurePreserving (fun q : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => (q.1.1, q.2.1))
      (π.prod π) (μ₁.prod μ₁) :=
    hπ.measurePreserving_fst.prod hπ.measurePreserving_fst
  filter_upwards [hmp.quasiMeasurePreserving.ae h] with q hq
  rw [overlayDiff_apply, overlayDiff_apply, hq]

/-- **The cut distance factors through the a.e. class of its left argument.**

This is the full a.e.-invariance of `δ□`, not just of its vanishing, and it holds on arbitrary
probability carriers: every coupling contributes the same value to the two infima, so the infima
agree.  No triangle inequality is involved. -/
theorem cutDist_congr_ae_left {U U' : Graphon Ω₁ μ₁} {W : Graphon Ω₂ μ₂}
    (h : ∀ᵐ p ∂(μ₁.prod μ₁), U p.1 p.2 = U' p.1 p.2) : cutDist U W = cutDist U' W := by
  refine le_antisymm (le_cutDist U' W fun π hπ => ?_) (le_cutDist U W fun π hπ => ?_)
  · rw [← cutNorm_overlayDiff_congr_ae_left hπ h]
    exact cutDist_le U W hπ
  · rw [cutNorm_overlayDiff_congr_ae_left hπ h]
    exact cutDist_le U' W hπ

/-- **The cut distance factors through the a.e. class of its right argument**, by symmetry
(`cutDist_comm`). -/
theorem cutDist_congr_ae_right {U : Graphon Ω₁ μ₁} {W W' : Graphon Ω₂ μ₂}
    (h : ∀ᵐ p ∂(μ₂.prod μ₂), W p.1 p.2 = W' p.1 p.2) : cutDist U W = cutDist U W' := by
  rw [cutDist_comm U W, cutDist_comm U W', cutDist_congr_ae_left (W := U) h]

/-- **Almost everywhere equal graphons are at cut distance zero.** Replacing `U` by the a.e. equal
`W` leaves `δ□(U, W)` unchanged, and `δ□(W, W) = 0`.

No triangle inequality is used, so this holds on an arbitrary probability carrier. -/
theorem cutDist_eq_zero_of_aeEq {U W : Graphon Ω μ}
    (h : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = W p.1 p.2) : cutDist U W = 0 := by
  rw [cutDist_congr_ae_left h, cutDist_self]

end CutDistance

/-- **The reverse bridge: an a.e. `[0, 1]`-valued, a.e. symmetric class comes from a graphon.**
This is the measurable-selection step that lets `AEEqFun`-native constructions — conditional
expectations, martingale limits — be read back as strict graphons.

The witness is built from a measurable representative by averaging it with its transpose and
clamping to `[0, 1]`; both operations are the identity almost everywhere, and both are needed,
since a representative has no reason to be symmetric or `[0, 1]`-valued at every point. -/
theorem exists_graphon_repr (f : (Ω × Ω) →ₘ[μ.prod μ] ℝ)
    (hbdd : ∀ᵐ p ∂(μ.prod μ), f p ∈ Set.Icc (0 : ℝ) 1)
    (hsymm : ∀ᵐ p ∂(μ.prod μ), f p = f p.swap) :
    ∃ W : Graphon Ω μ, Graphon.toAEEqFun W = f := by
  set g : Ω × Ω → ℝ := fun p => max 0 (min 1 ((f p + f p.swap) / 2)) with hg
  have hgmem (p : Ω × Ω) : g p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hgmeas : Measurable g :=
    measurable_const.max (measurable_const.min
      (((AEEqFun.measurable f).add ((AEEqFun.measurable f).comp measurable_swap)).div_const 2))
  refine ⟨{ toFun := fun x y => g (x, y)
            symm' := fun x y => by simp only [hg, Prod.swap_prod_mk, add_comm]
            meas' := hgmeas
            bdd' := ⟨1, fun x y => abs_le.2 ⟨by linarith [(hgmem (x, y)).1], (hgmem (x, y)).2⟩⟩
            mem01' := fun x y => hgmem (x, y) }, ?_⟩
  refine Graphon.toAEEqFun_eq_of_ae ?_
  filter_upwards [hbdd, hsymm] with p hp hps
  -- The graphon just built reads `g` at `(p.1, p.2) = p`, so this is the claim about `g`.
  have hgp : g p = f p := by
    simp only [hg, ← hps, add_self_div_two, min_eq_right hp.2, max_eq_right hp.1]
  exact hgp

/-- **The classes that come from graphons are exactly the a.e. `[0, 1]`-valued, a.e. symmetric
ones.**  The forward direction is the pointwise range and symmetry of a strict graphon read on its
class; the converse is `exists_graphon_repr`. -/
theorem exists_graphon_repr_iff (f : (Ω × Ω) →ₘ[μ.prod μ] ℝ) :
    (∃ W : Graphon Ω μ, Graphon.toAEEqFun W = f) ↔
      (∀ᵐ p ∂(μ.prod μ), f p ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ᵐ p ∂(μ.prod μ), f p = f p.swap := by
  refine ⟨?_, fun h => exists_graphon_repr f h.1 h.2⟩
  rintro ⟨W, rfl⟩
  exact ⟨Graphon.toAEEqFun_mem_Icc_ae W, Graphon.toAEEqFun_symm_ae W⟩

end DenseGraphLimits

end TauCeti
