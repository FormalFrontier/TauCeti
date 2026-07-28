module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

/-!
# Images of open simply connected sets under injective holomorphic maps

A holomorphic map that is injective on an open set `Ω ⊆ ℂ` carries `Ω` to an open set, and carries
a simply connected `Ω` to a simply connected set. Both facts are used by the Riemann mapping
theorem, where the image of an extremal map has to be recognized as a domain of the same kind as
the original.

## The argument

Openness is the open mapping theorem. It is local, so it needs no connectivity hypothesis on `Ω`:
around each point of `Ω` sits a ball on which `g` is analytic and — being injective — nonconstant,
and `Mathlib.Analysis.Complex.OpenMapping` opens that ball.

Simple connectivity is then purely topological, and Mathlib supplies it: injectivity and continuity
make `Ω.restrict g` an injective continuous map, openness makes it an open map, hence a topological
embedding, and `Topology.IsEmbedding.isSimplyConnected_image` transports simple connectivity across
an embedding. Holomorphy enters *only* through the open mapping theorem; there is no separate
homotopy argument here.

## Main statements

* `TauCeti.isOpen_image_of_injOn` — the image of an open set is open.
* `TauCeti.isSimplyConnected_image_of_injOn` — the image of an open simply connected set is simply
  connected.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. The declarations here are an explicitly
**temporary shim**: delete them and refactor downstream consumers onto the exported Mathlib
versions once those land.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §3.4 (the open mapping theorem).
-/

public section

namespace TauCeti

open Complex Set Metric Topology

variable {Ω : Set ℂ} {g : ℂ → ℂ}

/-- **The image of an open set under an injective holomorphic map is open.** No connectivity
hypothesis is needed: openness is local, and on a small ball around any point of `Ω` the map is
analytic and nonconstant, so the open mapping theorem applies there. -/
theorem isOpen_image_of_injOn (hΩo : IsOpen Ω) (hgd : DifferentiableOn ℂ g Ω) (hgi : InjOn g Ω) :
    IsOpen (g '' Ω) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩo z hz
  have hz' : z ∈ ball z ε := mem_ball_self hε
  -- On the ball, `g` is analytic and injective, hence nonconstant.
  have hana : AnalyticOnNhd ℂ g (ball z ε) := (hgd.mono hball).analyticOnNhd isOpen_ball
  have hnc : ¬ ∃ w, ∀ y ∈ ball z ε, g y = w := by
    rintro ⟨w, hw⟩
    have hshift : z + ((ε / 2 : ℝ) : ℂ) ∈ ball z ε := by
      rw [mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have hne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have := hgi (hball hz') (hball hshift) ((hw z hz').trans (hw _ hshift).symm)
    exact hne (by simpa using this)
  rcases hana.is_constant_or_isOpen (convex_ball z ε).isPreconnected with hconst | hopen
  · exact absurd hconst hnc
  · exact ⟨g '' ball z ε, image_mono hball, hopen _ subset_rfl isOpen_ball, ⟨z, hz', rfl⟩⟩

/-- Restricted to its open domain, an injective holomorphic map is an open map into `ℂ`: an open
subset of the subtype `↥Ω` is `Ω` met with an open set, and the image of that is open by
`TauCeti.isOpen_image_of_injOn`. -/
private theorem isOpenMap_restrict (hΩo : IsOpen Ω) (hgd : DifferentiableOn ℂ g Ω)
    (hgi : InjOn g Ω) : IsOpenMap (Ω.restrict g) := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  rw [Set.image_restrict]
  exact isOpen_image_of_injOn (hW.inter hΩo) (hgd.mono inter_subset_right)
    (hgi.mono inter_subset_right)

/-- **Injective holomorphic maps preserve simple connectivity.** The image of an open simply
connected set under a holomorphic map injective on it is again simply connected.

The mathematical content beyond openness is Mathlib's
`Topology.IsEmbedding.isSimplyConnected_image`: the restriction of `g` to `Ω` is a topological
embedding, because it is continuous, injective, and open. -/
theorem isSimplyConnected_image_of_injOn (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hgd : DifferentiableOn ℂ g Ω) (hgi : InjOn g Ω) : IsSimplyConnected (g '' Ω) := by
  have hemb : IsEmbedding (Ω.restrict g) :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuousOn_iff_continuous_restrict.mp hgd.continuousOn)
      (Set.injOn_iff_injective.mp hgi) (isOpenMap_restrict hΩo hgd hgi)).isEmbedding
  have himg := hemb.isSimplyConnected_image (s := (univ : Set ↥Ω))
  rw [image_univ, Set.range_restrict] at himg
  refine himg.mpr ?_
  -- `IsSimplyConnected (univ : Set ↥Ω)` is simple connectivity of `↥Ω` itself.
  have : SimplyConnectedSpace ↥Ω := hΩc
  exact (Homeomorph.Set.univ ↥Ω).toHomotopyEquiv.simplyConnectedSpace

end TauCeti
