/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.Basic
public import Mathlib.Topology.Path
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuous logarithms on simple arcs

A zero-free continuous complex-valued function on a **simple arc** has a continuous logarithm.
Here an arc is presented as the range of a path `γ : Path x y` whose parametrization is an
embedding; the main theorem is `TauCeti.hasContinuousLogOn_range_of_isEmbedding_path`.

The proof extends `γ` constantly to `ℝ` and lifts `g ∘ γ.extend` through the covering map
`Complex.exp : ℂ → ℂ \ {0}`. Since `ℝ` is simply connected, Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp` supplies the lift, and the embedding hypothesis makes
the parametrization a homeomorphism onto the range, along which the lift descends to the arc
itself. The Borsuk-map specialization
`TauCeti.hasContinuousLogOn_sub_div_sub_range_of_injective_path` records the form used by plane
separation; there the embedding comes for free, an injective path from the compact unit interval
into a Hausdorff space being a closed embedding. No formalization is vendored.

## Roadmap role

The Carathéodory enclosure step (layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`) is now unconditional: the
preconnectedness/winding-number route in
`TauCeti/Analysis/Complex/Conformal/Crosscut/Inside.lean` discharges it without plane
separation. The classical separation route — Borsuk's criterion (PR #4701) plus arc
nonseparation — remains relevant for future work. This file supplies the logarithm
construction needed for that
route: applying `TauCeti.hasContinuousLogOn_sub_div_sub_range_of_injective_path` shows that any two
points off a simple arc lie in the same component of its complement.

This is deliberately stated for paths in an arbitrary topological space, since neither the lifting
argument nor descent to the range uses planar geometry. The logarithm is still complex-valued, as
required by `TauCeti.HasContinuousLogOn` and by the L5 Borsuk-map consumer.

## Main results

* `TauCeti.hasContinuousLogOn_range_of_isEmbedding_path` — every zero-free continuous function on
  the range of a path with embedded parametrization has a continuous logarithm.
* `TauCeti.hasContinuousLogOn_sub_div_sub_range_of_injective_path` — the Borsuk map of two points
  outside a simple complex arc has a continuous logarithm on that arc.

## References

* S. Janiszewski, *Sur les coupures du plan faites par les continus*, Prace Mat.-Fiz. **26**
  (1913).
* J. R. Munkres, *Topology*, §61–63.
-/

public section

namespace TauCeti

open Set Topology

variable {X : Type*} [TopologicalSpace X] {x y : X} {g : X → ℂ}

/-- **A zero-free continuous function on a simple arc has a continuous logarithm.** Let `γ` be a
path whose parametrization is an embedding. If `g` is continuous and nonzero on `range γ`, then
there is a function continuous on `range γ` whose exponential is `g` there. -/
theorem hasContinuousLogOn_range_of_isEmbedding_path (γ : Path x y)
    (hγe : IsEmbedding γ) (hg : ContinuousOn g (range γ))
    (hzero : ∀ z ∈ range γ, g z ≠ 0) : HasContinuousLogOn g (range γ) := by
  classical
  let G : ℝ → ℂ := fun t => g (γ.extend t)
  have hGc : Continuous G := by
    rw [← continuousOn_univ]
    simpa only [G, Function.comp_def] using
      hg.comp γ.continuous_extend.continuousOn fun t _ =>
        γ.extend_range ▸ mem_range_self t
  have hGzero : ∀ t, G t ≠ 0 := fun t =>
    hzero _ (γ.extend_range ▸ mem_range_self t)
  have hsimply : IsSimplyConnected (univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨H, hHc, hH⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimply isOpen_univ
    hGc.continuousOn (by rintro ⟨t, -, ht⟩; exact hGzero t ht)
  let e : unitInterval ≃ₜ range γ := hγe.toHomeomorph
  let h : X → ℂ := fun z => if hz : z ∈ range γ then H (e.symm ⟨z, hz⟩ : ℝ) else 0
  refine hasContinuousLogOn_iff.mpr ⟨h, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert (continuousOn_univ.mp hHc).comp (continuous_subtype_val.comp e.symm.continuous) using 1
    ext z
    simp only [domRestrict_apply, h, z.2, ↓reduceDIte, Function.comp_apply]
  · intro z hz
    have he : γ (e.symm ⟨z, hz⟩) = z := by
      have he' := congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)
      simpa only [e, IsEmbedding.toHomeomorph_apply_coe] using he'
    have hextend : γ.extend (e.symm ⟨z, hz⟩ : ℝ) = z := by
      rw [γ.extend_extends']
      exact he
    have hlift := hH (mem_univ (e.symm ⟨z, hz⟩ : ℝ))
    simpa only [h, hz, ↓reduceDIte, Function.comp_apply, G, hextend] using hlift

/-- **The Borsuk map of two points off a simple complex arc has a continuous logarithm on the
arc.** The two nonmembership hypotheses say exactly that the numerator and the denominator of
`z ↦ (z - a) / (z - b)` do not vanish along the arc.

Together with Borsuk's converse criterion for bounded closed sets, this is the standard proof that
an arc does not separate the plane. -/
theorem hasContinuousLogOn_sub_div_sub_range_of_injective_path {p q a b : ℂ} (γ : Path p q)
    (hγ : Function.Injective γ) (ha : a ∉ range γ) (hb : b ∉ range γ) :
    HasContinuousLogOn (fun z => (z - a) / (z - b)) (range γ) := by
  refine hasContinuousLogOn_range_of_isEmbedding_path γ
    (γ.continuous.isClosedEmbedding hγ).isEmbedding
    ((continuousOn_id.sub continuousOn_const).div
      (continuousOn_id.sub continuousOn_const) fun z hz =>
        sub_ne_zero.mpr fun hzb => hb (hzb ▸ hz)) fun z hz => ?_
  exact div_ne_zero (sub_ne_zero.mpr fun hza => ha (hza ▸ hz))
    (sub_ne_zero.mpr fun hzb => hb (hzb ▸ hz))

end TauCeti
