/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence
import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Triangle
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Uniqueness
import TauCeti.Analysis.Complex.Conformal.InverseFunction

/-!
# The hyperbolic metric of a domain biholomorphic to the disc

`Hyperbolic/Distance.lean` puts the hyperbolic (Poincaré) distance on the unit disc, and
`RiemannMapping/Existence.lean` maps every simply connected open proper subset of `ℂ`
biholomorphically onto that disc. Transporting the distance along such a map equips the domain
with a hyperbolic distance of its own. This file carries out the transport and shows that the
result depends on the domain alone.

The transported distance is well defined because the ambiguity in the transporting map is
exactly a disc automorphism: two holomorphic injections of `Ω` onto the disc differ by a
standard automorphism `z ↦ u * (z - a) / (1 - conj a * z)`
(`TauCeti.exists_eqOn_unitDiscStandardAutomorphismFormula_comp`), and those automorphisms are
hyperbolic isometries (`TauCeti.hyperbolicDist_unitDiscStandardAutomorphismEquiv`). So the
definition may pick *any* transporting map, and `TauCeti.hyperbolicDistOn_eq` evaluates it
against whichever one the caller has at hand.

Two theorems record what makes this distance the natural conformal invariant of a plane domain:

* `TauCeti.hyperbolicDistOn_image` — a biholomorphism `Ω → Ω'` is an **isometry**, so the
  hyperbolic distance is a conformal invariant and not merely a choice of metric;
* `TauCeti.hyperbolicDistOn_map_le` — **Schwarz--Pick for domains**: *every* holomorphic map
  `Ω → Ω'`, injective or not, is distance-decreasing. On `Ω = Ω' = 𝔻` this is the disc statement
  `TauCeti.hyperbolicDist_map_le` it is deduced from.

## Main declarations

* `TauCeti.IsBiholomorphicToDisc` — the domains that carry the distance: those admitting a
  holomorphic injection onto `Metric.ball 0 1`.
* `TauCeti.isBiholomorphicToDisc_of_isSimplyConnected` — the Riemann mapping theorem supplies
  them: every simply connected open proper subset of `ℂ` qualifies.
* `TauCeti.hyperbolicDistOn` — the hyperbolic distance of such a domain.
* `TauCeti.hyperbolicDistOn_eq` — its value along any transporting map.
* `TauCeti.hyperbolicDistOn_ball` — on the disc itself it is `TauCeti.hyperbolicDist`.
* `TauCeti.hyperbolicDistOn_comm`, `TauCeti.hyperbolicDistOn_self`,
  `TauCeti.hyperbolicDistOn_nonneg`, `TauCeti.hyperbolicDistOn_eq_zero_iff`,
  `TauCeti.hyperbolicDistOn_triangle` — the metric axioms.
* `TauCeti.hyperbolicDistOn_image` — conformal invariance.
* `TauCeti.hyperbolicDistOn_map_le` — Schwarz--Pick for domains.

## Coordination with upstream Mathlib

This file rests on the L3 Riemann-mapping shim in `RiemannMapping/Existence.lean`, so per the
*Coordination with upstream Mathlib* clause of `TauCetiRoadmap/ConformalMapping/README.md` it
inherits that shim's status: the Riemann mapping theorem is being formalized upstream in
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), alongside the
human-curated `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`.
Once the human-curated Mathlib theorem lands, `TauCeti.isBiholomorphicToDisc_of_isSimplyConnected`
should be re-proved on top of it and the shim deleted. The transported distance itself has no
Mathlib counterpart (Mathlib has the hyperbolic metric only on the upper half-plane, and no
plane-domain version), so only the dependence on the L3 shim is temporary.

## Roadmap status

`TauCetiRoadmap/ConformalMapping/README.md` scopes its hyperbolic-metric target to the disc: L2
reads "the **hyperbolic / Poincaré metric** on `𝔻`", and that target is already discharged by
`Conformal/Poincare/MetricSpace.lean`. Carrying the metric to a general disc-uniformizable domain
is not covered by it, and no later layer (L4 reflection, L5 Carathéodory, L6 Schwarz--Christoffel)
consumes it. So this file is pending a roadmap decision that only a human can make: a
`ConformalMapping` node for the conformally invariant metric on disc-uniformizable domains
(Ahlfors, *Conformal Invariants*, Ch. 1, already in that entry's References). Replace this section
with a citation of that node once it exists.

## References

* L. Ahlfors, *Conformal Invariants: Topics in Geometric Function Theory*, Ch. 1.
* J. B. Conway, *Functions of One Complex Variable I*, Ch. VII.
-/

public section

namespace TauCeti

open _root_.Complex Function Metric Set
open scoped ComplexConjugate

variable {Ω Ω' : Set ℂ} {f φ : ℂ → ℂ} {z w u : ℂ}

/-- A subset of `ℂ` is **biholomorphic to the disc** when some holomorphic injection maps it
onto `Metric.ball 0 1`. The inverse of such a map is automatically holomorphic on the disc
(`TauCeti.DifferentiableOn.invFunOn`), so no separate condition on it is needed.

By the Riemann mapping theorem every simply connected open proper subset of `ℂ` has this
property; see `TauCeti.isBiholomorphicToDisc_of_isSimplyConnected`. -/
def IsBiholomorphicToDisc (Ω : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ f '' Ω = ball (0 : ℂ) 1

/-- The unit disc is biholomorphic to itself, via the identity. -/
theorem isBiholomorphicToDisc_ball : IsBiholomorphicToDisc (ball (0 : ℂ) 1) :=
  ⟨id, differentiableOn_id, injOn_id _, image_id _⟩

/-- **The Riemann mapping theorem**, in the form used here: every simply connected open proper
subset of `ℂ` is biholomorphic to the unit disc. -/
theorem isBiholomorphicToDisc_of_isSimplyConnected (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩ : Ω ≠ univ) : IsBiholomorphicToDisc Ω := by
  obtain ⟨f, hbij, hfd, -⟩ := riemannMapping hΩo hΩc hΩ
  exact ⟨f, hfd, hbij.injOn, hbij.image_eq⟩

open scoped Classical in
/-- The hyperbolic (Poincaré) distance of a plane domain `Ω`, obtained by transporting
`TauCeti.hyperbolicDist` along a holomorphic injection of `Ω` onto the unit disc.

The transporting map is chosen, but the choice does not matter: `TauCeti.hyperbolicDistOn_eq`
computes the distance along an arbitrary such map, because any two of them differ by a disc
automorphism and those are hyperbolic isometries. On a set admitting no such map the value is
the junk `0`, with no geometric meaning. -/
noncomputable def hyperbolicDistOn (Ω : Set ℂ) (z w : ℂ) : ℝ :=
  if h : IsBiholomorphicToDisc Ω then hyperbolicDist (h.choose z) (h.choose w) else 0

/-- **The hyperbolic distance of a domain is well defined.** It may be computed along *any*
holomorphic injection `f` of the open set `Ω` onto the unit disc: the ambiguity in `f` is a disc
automorphism, and disc automorphisms preserve `TauCeti.hyperbolicDist`. -/
theorem hyperbolicDistOn_eq (hΩo : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) (hfi : InjOn f Ω)
    (hfim : f '' Ω = ball (0 : ℂ) 1) (hz : z ∈ Ω) (hw : w ∈ Ω) :
    hyperbolicDistOn Ω z w = hyperbolicDist (f z) (f w) := by
  have hΩ : IsBiholomorphicToDisc Ω := ⟨f, hf, hfi, hfim⟩
  obtain ⟨hg, hgi, hgim⟩ := hΩ.choose_spec
  have hgmaps : MapsTo hΩ.choose Ω (ball (0 : ℂ) 1) :=
    (mapsTo_image hΩ.choose Ω).mono_right hgim.subset
  have hnorm : ∀ {x : ℂ}, x ∈ Ω → ‖hΩ.choose x‖ < 1 := fun {x} hx => by
    simpa [mem_ball_zero_iff] using hgmaps hx
  -- The chosen map and `f` differ by a standard disc automorphism `z ↦ u * (z - a)/(1 - ā z)`.
  obtain ⟨u, a, hua⟩ :=
    exists_eqOn_unitDiscStandardAutomorphismFormula_comp hΩo hg hf hgi hfi hgim hfim
  have hfz : f z = (u : ℂ) * ((hΩ.choose z - (a : ℂ)) / (1 - conj (a : ℂ) * hΩ.choose z)) :=
    hua hz
  have hfw : f w = (u : ℂ) * ((hΩ.choose w - (a : ℂ)) / (1 - conj (a : ℂ) * hΩ.choose w)) :=
    hua hw
  have hiso := hyperbolicDist_unitDiscStandardAutomorphismEquiv u a
    (Complex.UnitDisc.mk _ (hnorm hz)) (Complex.UnitDisc.mk _ (hnorm hw))
  rw [coe_unitDiscStandardAutomorphismEquiv_apply,
    coe_unitDiscStandardAutomorphismEquiv_apply] at hiso
  simp only [Complex.UnitDisc.coe_mk] at hiso
  rw [hyperbolicDistOn, dif_pos hΩ, hfz, hfw]
  exact hiso.symm

/-- On the unit disc itself the transported distance is the hyperbolic distance of
`Hyperbolic/Distance.lean`. -/
theorem hyperbolicDistOn_ball (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDistOn (ball (0 : ℂ) 1) z w = hyperbolicDist z w :=
  hyperbolicDistOn_eq isOpen_ball differentiableOn_id (injOn_id _) (image_id _) hz hw

/-- The hyperbolic distance of a domain is symmetric. -/
theorem hyperbolicDistOn_comm (Ω : Set ℂ) (z w : ℂ) :
    hyperbolicDistOn Ω z w = hyperbolicDistOn Ω w z := by
  unfold hyperbolicDistOn
  by_cases h : IsBiholomorphicToDisc Ω
  · rw [dif_pos h, dif_pos h]
    exact hyperbolicDist_comm _ _
  · rw [dif_neg h, dif_neg h]

/-- The hyperbolic distance of a domain vanishes on the diagonal. -/
@[simp]
theorem hyperbolicDistOn_self (Ω : Set ℂ) (z : ℂ) : hyperbolicDistOn Ω z z = 0 := by
  unfold hyperbolicDistOn
  by_cases h : IsBiholomorphicToDisc Ω
  · rw [dif_pos h]
    exact hyperbolicDist_self _
  · rw [dif_neg h]

/-- The hyperbolic distance of a domain is nonnegative. -/
theorem hyperbolicDistOn_nonneg (Ω : Set ℂ) (z w : ℂ) : 0 ≤ hyperbolicDistOn Ω z w := by
  unfold hyperbolicDistOn
  by_cases h : IsBiholomorphicToDisc Ω
  · rw [dif_pos h]
    exact hyperbolicDist_nonneg _ _
  · rw [dif_neg h]

/-- On a domain biholomorphic to the disc the hyperbolic distance separates points. -/
theorem hyperbolicDistOn_eq_zero_iff (hΩo : IsOpen Ω) (hΩ : IsBiholomorphicToDisc Ω)
    (hz : z ∈ Ω) (hw : w ∈ Ω) : hyperbolicDistOn Ω z w = 0 ↔ z = w := by
  obtain ⟨f, hf, hfi, hfim⟩ := hΩ
  have hmaps : MapsTo f Ω (ball (0 : ℂ) 1) := (mapsTo_image f Ω).mono_right hfim.subset
  rw [hyperbolicDistOn_eq hΩo hf hfi hfim hz hw,
    hyperbolicDist_eq_zero_iff_of_mem_ball (hmaps hz) (hmaps hw)]
  exact ⟨fun h => hfi hz hw h, fun h => by rw [h]⟩

/-- **The hyperbolic triangle inequality on a domain.** -/
theorem hyperbolicDistOn_triangle (hΩo : IsOpen Ω) (hΩ : IsBiholomorphicToDisc Ω)
    (hz : z ∈ Ω) (hw : w ∈ Ω) (hu : u ∈ Ω) :
    hyperbolicDistOn Ω z w ≤ hyperbolicDistOn Ω z u + hyperbolicDistOn Ω u w := by
  obtain ⟨f, hf, hfi, hfim⟩ := hΩ
  have hmaps : MapsTo f Ω (ball (0 : ℂ) 1) := (mapsTo_image f Ω).mono_right hfim.subset
  rw [hyperbolicDistOn_eq hΩo hf hfi hfim hz hw, hyperbolicDistOn_eq hΩo hf hfi hfim hz hu,
    hyperbolicDistOn_eq hΩo hf hfi hfim hu hw]
  exact hyperbolicDist_triangle (hmaps hz) (hmaps hw) (hmaps hu)

/-- **Conformal invariance of the hyperbolic distance.** A biholomorphism `φ` of an open set `Ω`
onto an open set `Ω'` biholomorphic to the disc is an isometry for the two hyperbolic distances.

This is what singles the hyperbolic distance out among metrics on a plane domain: it is
attached to the conformal structure alone. Taking `Ω' = Ω` it says that the biholomorphic
automorphisms of a domain act on it by isometries. -/
theorem hyperbolicDistOn_image (hΩo : IsOpen Ω) (hΩ'o : IsOpen Ω')
    (hΩ' : IsBiholomorphicToDisc Ω') (hφ : DifferentiableOn ℂ φ Ω) (hφi : InjOn φ Ω)
    (hφim : φ '' Ω = Ω') (hz : z ∈ Ω) (hw : w ∈ Ω) :
    hyperbolicDistOn Ω' (φ z) (φ w) = hyperbolicDistOn Ω z w := by
  obtain ⟨g, hg, hgi, hgim⟩ := hΩ'
  have hmaps : MapsTo φ Ω Ω' := (mapsTo_image φ Ω).mono_right hφim.subset
  -- Transporting `Ω'` to the disc by `g` transports `Ω` to the disc by `g ∘ φ`.
  have hgφim : (g ∘ φ) '' Ω = ball (0 : ℂ) 1 := by rw [image_comp, hφim, hgim]
  rw [hyperbolicDistOn_eq hΩ'o hg hgi hgim (hmaps hz) (hmaps hw),
    hyperbolicDistOn_eq hΩo (hg.comp hφ hmaps) (hgi.comp hφi hmaps) hgφim hz hw]
  rfl

/-- **Schwarz--Pick for domains.** Every holomorphic map from a domain biholomorphic to the disc
into another one decreases the hyperbolic distance. No injectivity is assumed: the map is
conjugated into a holomorphic self-map of the disc, where `TauCeti.hyperbolicDist_map_le`
applies.

Biholomorphisms attain equality, by `TauCeti.hyperbolicDistOn_image`; the case
`Ω = Ω' = Metric.ball 0 1` recovers the classical disc statement. -/
theorem hyperbolicDistOn_map_le (hΩo : IsOpen Ω) (hΩ'o : IsOpen Ω')
    (hΩ : IsBiholomorphicToDisc Ω) (hΩ' : IsBiholomorphicToDisc Ω')
    (hf : DifferentiableOn ℂ f Ω) (hmaps : MapsTo f Ω Ω') (hz : z ∈ Ω) (hw : w ∈ Ω) :
    hyperbolicDistOn Ω' (f z) (f w) ≤ hyperbolicDistOn Ω z w := by
  obtain ⟨F, hF, hFi, hFim⟩ := hΩ
  obtain ⟨G, hG, hGi, hGim⟩ := hΩ'
  have hFmaps : MapsTo F Ω (ball (0 : ℂ) 1) := (mapsTo_image F Ω).mono_right hFim.subset
  have hGmaps : MapsTo G Ω' (ball (0 : ℂ) 1) := (mapsTo_image G Ω').mono_right hGim.subset
  -- `F` transports `Ω` to the disc; its inverse is holomorphic there.
  have hFinv : DifferentiableOn ℂ (invFunOn F Ω) (ball (0 : ℂ) 1) := by
    rw [← hFim]
    exact DifferentiableOn.invFunOn hF hΩo hFi
  have hFsurj : SurjOn F Ω (ball (0 : ℂ) 1) := by
    rw [← hFim]
    exact surjOn_image F Ω
  have hFinvmaps : MapsTo (invFunOn F Ω) (ball (0 : ℂ) 1) Ω := hFsurj.mapsTo_invFunOn
  -- `G ∘ f ∘ F⁻¹` is a holomorphic self-map of the disc, so Schwarz--Pick applies to it.
  have hcompd : DifferentiableOn ℂ (G ∘ f ∘ invFunOn F Ω) (ball (0 : ℂ) 1) :=
    hG.comp (hf.comp hFinv hFinvmaps) (hmaps.comp hFinvmaps)
  have hcompmaps : MapsTo (G ∘ f ∘ invFunOn F Ω) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    hGmaps.comp (hmaps.comp hFinvmaps)
  have key := hyperbolicDist_map_le hcompd hcompmaps (hFmaps hz) (hFmaps hw)
  simp only [Function.comp_apply, hFi.leftInvOn_invFunOn hz, hFi.leftInvOn_invFunOn hw] at key
  rw [hyperbolicDistOn_eq hΩ'o hG hGi hGim (hmaps hz) (hmaps hw),
    hyperbolicDistOn_eq hΩo hF hFi hFim hz hw]
  exact key

end TauCeti
