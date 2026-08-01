/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Complex.Conformal.Monodromy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The global branch of a germ on a simply connected domain

`Monodromy.lean` proves that analytic continuation along a path depends on the path only through
its homotopy class. This file draws the conclusion that makes monodromy usable: **on a simply
connected domain, a germ that continues along every path is the germ of a single holomorphic
function on the whole domain**. Equivalently, on such a domain continuation creates no new
branches, so "multi-valued analytic function" is a phenomenon of the topology of the domain and
not of the germ.

The hypothesis is `TauCeti.ContinuesInside f₀ U z₀` from `Conformal/Continuation.lean`: the germ
of `f₀` at `z₀` continues along *every* path in `U` issuing from `z₀`. It is exactly what a
holomorphic function on `U` supplies (`TauCeti.ContinuesInside.of_differentiableOn`), and by the
two-way form below it is supplied by nothing else once `U` is simply connected.

## Main results

* `TauCeti.ContinuesInside.eventuallyEq_at_one` — **path independence**: on a simply connected `U`,
  two continuations of one germ along two paths in `U` with the same endpoints end at the same
  germ.
* `TauCeti.ContinuesInside.eventuallyEq_of_loop` — the loop form: continuing a germ around a loop
  in a simply connected `U` returns it unchanged.
* `TauCeti.ContinuesInside.exists_analyticOnNhd` — **the monodromy theorem for a simply connected
  domain**: a germ that continues along every path of a simply connected open `U` is the germ of
  a function analytic on all of `U`.
* `TauCeti.continuesInside_iff_exists_analyticOnNhd` — the two-way form on a simply connected open
  set: continuable along every path inside `U` ⟺ the germ of a function analytic on `U`.

The branch produced is unique as soon as `U` is preconnected, by the identity principle
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`); no uniqueness statement is added here.

## The construction

Path independence is monodromy plus simple connectivity: two paths in `U` with the same endpoints
lift to paths in the subspace `↥U`, where `SimplyConnectedSpace.paths_homotopic` produces a
homotopy rel endpoints; pushing that homotopy back down to `ℂ` keeps every intermediate path
inside `U`, so the hypothesis supplies a continuation along each of them and
`TauCeti.monodromy_theorem` applies. Uniqueness of continuation along a *fixed* path
(`TauCeti.IsAnalyticContinuationAlong.eventuallyEq`, over the preconnected parameter interval)
then matches the two given continuations with the two extreme members of that family.

The global branch is `F w = (value at w of the terminal germ of a continuation to w)`, chosen once
per point of `U` by path connectedness; path independence says the choice does not matter. The
work is in showing `F` analytic, that is, in comparing the terminal germs at two *different*
points. The comparison uses the metric stability of continuation
(`TauCeti.IsAnalyticContinuationAlong.exists_isAnalyticContinuationAlong_of_dist_lt`): a
continuation along a path `δ` ending at `z` is carried by a family that continues along *every*
path uniformly `ρ`-close to `δ`, so the sheared path `x ↦ δ x + x • (w - z)`, which ends at a
nearby `w`, is continued by that same family. The shear leaves `δ` by less than `ρ`, and by less
than the distance from the compact set `δ '' I` to the complement of `U`, so it stays inside `U`
and path independence applies to it. Hence `F` agrees near `z` with a fixed analytic
representative of the terminal germ at `z`, which is what analyticity at `z` needs. The same
identification at `z₀`, applied to the constant path, is what gives `F` the prescribed germ
there.

## Relation to the roadmap and to Mathlib

This completes the L4 target "the monodromy theorem (continuations along homotopic paths agree)"
of `TauCetiRoadmap/ConformalMapping/README.md` with the statement that layer is built for: the
passage from local germ data to a single-valued function on a simply connected domain, which is
what the reflection and continuation layers hand to their consumers. Layer L4 lies outside the
roadmap's shim-deletion clause for the upstream Riemann-mapping effort
(leanprover-community/mathlib4#33505), which contains no continuation or monodromy material.

Mathlib has the abstract monodromy statement `IsLocalHomeomorph.monodromy_theorem` and the lifting
criterion `IsCoveringMap.existsUnique_continuousMap_lifts` for a simply connected base
(`Mathlib/Topology/Homotopy/Lifting.lean`), but consuming them for germs of holomorphic functions
would first require the étale space of those germs as a topological space, which Mathlib does not
have; see the discussion in `Conformal/Monodromy.lean`. Mathlib's simple-connectivity API
(`SimplyConnectedSpace.paths_homotopic`, `IsSimplyConnected.isPathConnected`), its path homotopy
API (`Path.Homotopy.map`), and its metric thickening of a compact set are consumed rather than
restated.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.3.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §3.
* W. Rudin, *Real and Complex Analysis*, Ch. 16 (the monodromy theorem).
-/

public section

namespace TauCeti

open Filter Metric Set Topology unitInterval

variable {U : Set ℂ} {z₀ : ℂ} {f₀ : ℂ → ℂ} {γ δ : I → ℂ} {f g : I → ℂ → ℂ}

/-! ### Path independence and the global branch -/

namespace ContinuesInside

/-- **Path independence of continuation on a simply connected domain.** Two continuations of one
germ, along two paths in `U` that start at `z₀` and share their endpoint, carry the same germ at
the endpoint.

The proof lifts the two paths to the subspace `↥U`, where simple connectivity makes them homotopic
rel endpoints, pushes the homotopy back to `ℂ` — every intermediate path still lies in `U`, so the
hypothesis continues the germ along it — and applies `TauCeti.monodromy_theorem` to the resulting
family. The two given continuations are then matched with the extreme members of that family by
uniqueness along a fixed path. -/
theorem eventuallyEq_at_one (hUc : IsSimplyConnected U) (H : ContinuesInside f₀ U z₀)
    (hγ : Continuous γ) (hγU : ∀ x, γ x ∈ U) (hγ0 : γ 0 = z₀)
    (hδ : Continuous δ) (hδU : ∀ x, δ x ∈ U) (hδ0 : δ 0 = z₀) (hend : δ 1 = γ 1)
    (hf : IsAnalyticContinuationAlong f γ univ) (hf0 : f 0 =ᶠ[𝓝 z₀] f₀)
    (hg : IsAnalyticContinuationAlong g δ univ) (hg0 : g 0 =ᶠ[𝓝 z₀] f₀) :
    f 1 =ᶠ[𝓝 (γ 1)] g 1 := by
  haveI := hUc.simplyConnectedSpace
  have hz₀U : z₀ ∈ U := hγ0 ▸ hγU 0
  -- The two paths, read in the subspace `↥U`, where simple connectivity lives.
  let p : Path (⟨z₀, hz₀U⟩ : U) (⟨γ 1, hγU 1⟩ : U) :=
    { toFun := fun x => ⟨γ x, hγU x⟩
      continuous_toFun := hγ.subtype_mk _
      source' := Subtype.ext hγ0
      target' := rfl }
  let q : Path (⟨z₀, hz₀U⟩ : U) (⟨γ 1, hγU 1⟩ : U) :=
    { toFun := fun x => ⟨δ x, hδU x⟩
      continuous_toFun := hδ.subtype_mk _
      source' := Subtype.ext hδ0
      target' := Subtype.ext hend }
  obtain ⟨h⟩ := SimplyConnectedSpace.paths_homotopic p q
  -- The same homotopy, read back in `ℂ`; it never leaves `U`.
  set K := h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, ℂ)) with hK
  have hKmem : ∀ t x : I, K (t, x) ∈ U := fun t x => (h (t, x)).2
  have hKzero : ∀ t : I, K (t, 0) = z₀ := fun t => by simp [hK]
  have hKp : (fun x => K (0, x)) = γ := funext fun x => by simp [hK, p]
  have hKq : (fun x => K (1, x)) = δ := funext fun x => by simp [hK, q]
  -- A continuation along every intermediate path, all starting from the germ of `f₀`.
  have hcont : ∀ t : I, ContinuesAlong f₀ fun x => K (t, x) := fun t =>
    H _ (by fun_prop) (hKmem t) (hKzero t)
  choose F hF hF₀ using hcont
  have hF₀' : ∀ t : I, F t 0 =ᶠ[𝓝 z₀] f₀ := fun t => by
    rw [← hKzero t]; exact hF₀ t
  have hmono := monodromy_theorem K hF (fun t => (hF₀' t).trans (hF₀' 0).symm) 1
  -- Match the two given continuations with the extremes of the family.
  have e₀ : f 1 =ᶠ[𝓝 (γ 1)] F 0 1 :=
    hf.eventuallyEq (hKp ▸ hF 0) isPreconnected_univ (mem_univ 0) (mem_univ 1)
      (by rw [hγ0]; exact hf0.trans (hF₀' 0).symm)
  have e₁ : g 1 =ᶠ[𝓝 (δ 1)] F 1 1 :=
    hg.eventuallyEq (hKq ▸ hF 1) isPreconnected_univ (mem_univ 0) (mem_univ 1)
      (by rw [hδ0]; exact hg0.trans (hF₀' 1).symm)
  rw [hend] at e₁
  exact (e₀.trans hmono.symm).trans e₁.symm

/-- **A germ continued around a loop in a simply connected domain returns to itself.** This is the
loop form of path independence, the constant path being the second path. -/
theorem eventuallyEq_of_loop (hUc : IsSimplyConnected U) (H : ContinuesInside f₀ U z₀)
    (hγ : Continuous γ) (hγU : ∀ x, γ x ∈ U) (hγ0 : γ 0 = z₀) (hγ1 : γ 1 = z₀)
    (hf : IsAnalyticContinuationAlong f γ univ) (hf0 : f 0 =ᶠ[𝓝 z₀] f₀) :
    f 1 =ᶠ[𝓝 z₀] f₀ := by
  have hz₀U : z₀ ∈ U := hγ0 ▸ hγU 0
  have han : AnalyticAt ℂ f₀ z₀ := H.analyticAt hz₀U
  have := H.eventuallyEq_at_one hUc hγ hγU hγ0 continuous_const (fun _ => hz₀U) rfl (by rw [hγ1]) hf
    hf0 (.const continuousOn_const fun _ _ => han) .rfl
  rwa [hγ1] at this

/-- **The monodromy theorem for a simply connected domain.** A germ that continues along every
path of a simply connected open set `U` issuing from `z₀` is the germ at `z₀` of a single function
analytic on all of `U`.

So on a simply connected domain analytic continuation produces no new branches, and a
"multi-valued analytic function" there is single-valued after all. -/
theorem exists_analyticOnNhd (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hz₀ : z₀ ∈ U)
    (H : ContinuesInside f₀ U z₀) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ F =ᶠ[𝓝 z₀] f₀ := by
  -- A path from `z₀` to each point of `U`, and a continuation of the germ along it.
  have hpath : ∀ w ∈ U, ∃ γ : I → ℂ,
      Continuous γ ∧ (∀ x, γ x ∈ U) ∧ γ 0 = z₀ ∧ γ 1 = w := by
    intro w hw
    obtain ⟨c, hc⟩ := hUc.isPathConnected.joinedIn z₀ hz₀ w hw
    exact ⟨c, c.continuous, hc, c.source, c.target⟩
  choose! γ hγc hγU hγ0 hγ1 using hpath
  choose! f hf hf₀ using fun w (hw : w ∈ U) => H _ (hγc w hw) (hγU w hw) (hγ0 w hw)
  have hf₀' : ∀ w ∈ U, f w 0 =ᶠ[𝓝 z₀] f₀ := fun w hw => by
    have := hf₀ w hw; rwa [hγ0 w hw] at this
  -- The candidate branch: the value at `w` of the terminal germ of the chosen continuation.
  set F : ℂ → ℂ := fun w => f w 1 w with hFdef
  -- **The key step.** Near the endpoint of *any* continuation of the germ, `F` is the value of
  -- that continuation's terminal germ.
  have key : ∀ z : ℂ, ∀ δ : I → ℂ, ∀ g : I → ℂ → ℂ, Continuous δ → (∀ x, δ x ∈ U) → δ 0 = z₀ →
      δ 1 = z → IsAnalyticContinuationAlong g δ univ → g 0 =ᶠ[𝓝 z₀] f₀ → F =ᶠ[𝓝 z] g 1 := by
    intro z δ g hδ hδU hδ0 hδ1 hg hg0
    -- One family of germs continues along every path uniformly `ρ`-close to `δ`, ...
    obtain ⟨ρ, hρ, G, hGg, hGcont⟩ :=
      hg.exists_isAnalyticContinuationAlong_of_dist_lt isCompact_univ
    -- ... and an `ε`-neighbourhood of the compact `δ '' I` is still inside `U`.
    obtain ⟨ε, hε, hεU⟩ := (isCompact_range hδ).exists_thickening_subset_open hUo
      (range_subset_iff.2 hδU)
    have hGone : G 1 =ᶠ[𝓝 z] g 1 := by
      have := hGg 1 (mem_univ 1); rwa [hδ1] at this
    filter_upwards [ball_mem_nhds z (lt_min hρ hε), hGone] with w hw hwG
    -- The path `δ` sheared to end at `w` instead of `z`.
    set δ' : I → ℂ := fun x => δ x + (x : ℝ) • (w - z) with hδ'def
    have hδ'c : Continuous δ' := by fun_prop
    have hdist : ∀ x : I, dist (δ' x) (δ x) < min ρ ε := by
      intro x
      have hx : |(x : ℝ)| ≤ 1 := abs_le.2 ⟨by linarith [x.2.1], x.2.2⟩
      have hd : dist (δ' x) (δ x) = |(x : ℝ)| * dist w z := by
        rw [dist_eq_norm, dist_eq_norm, hδ'def]
        simp
      have hwz : dist w z < min ρ ε := mem_ball.1 hw
      have : |(x : ℝ)| * dist w z ≤ dist w z :=
        mul_le_of_le_one_left dist_nonneg hx
      linarith [hd ▸ this]
    have hδ'U : ∀ x, δ' x ∈ U := fun x =>
      hεU (mem_thickening_iff.2 ⟨δ x, mem_range_self x, (hdist x).trans_le (min_le_right _ _)⟩)
    have hδ'0 : δ' 0 = z₀ := by simp [hδ'def, hδ0]
    have hδ'1 : δ' 1 = w := by simp [hδ'def, hδ1]
    have hwU : w ∈ U := hδ'1 ▸ hδ'U 1
    have hGδ' : IsAnalyticContinuationAlong G δ' univ :=
      hGcont δ' hδ'c.continuousOn fun t _ => (hdist t).trans_le (min_le_left _ _)
    have hG0 : G 0 =ᶠ[𝓝 z₀] f₀ := by
      have := hGg 0 (mem_univ 0); rw [hδ0] at this; exact this.trans hg0
    -- Path independence: the chosen continuation to `w` and `G` end at the same germ.
    have hterm := H.eventuallyEq_at_one hUc (hγc w hwU) (hγU w hwU) (hγ0 w hwU) hδ'c hδ'U hδ'0
      (by rw [hδ'1, hγ1 w hwU]) (hf w hwU) (hf₀' w hwU) hGδ' hG0
    have hval := hterm.eq_of_nhds
    rw [hγ1 w hwU] at hval
    rw [hFdef]
    exact hval.trans hwG
  refine ⟨F, fun z hz => ?_, ?_⟩
  · -- Analyticity at `z`: `F` agrees near `z` with the terminal germ of the continuation to `z`.
    have han : AnalyticAt ℂ (f z 1) z := by
      have := (hf z hz).analyticAt 1 (mem_univ 1); rwa [hγ1 z hz] at this
    exact han.congr
      (key z (γ z) (f z) (hγc z hz) (hγU z hz) (hγ0 z hz) (hγ1 z hz) (hf z hz) (hf₀' z hz)).symm
  · -- The prescribed germ at `z₀`: apply the key step to the constant path.
    exact key z₀ (fun _ => z₀) (fun _ => f₀) continuous_const (fun _ => hz₀) rfl rfl
      (.const continuousOn_const fun _ _ => H.analyticAt hz₀) .rfl

end ContinuesInside

/-- **The monodromy theorem, in two-way form.** On a simply connected open set `U`, a germ at a
point `z₀ ∈ U` continues along every path in `U` from `z₀` if and only if it is the germ of a
function analytic on all of `U`.

The forward direction is `TauCeti.ContinuesInside.exists_analyticOnNhd`; the reverse is the
observation that a holomorphic function is its own continuation. -/
theorem continuesInside_iff_exists_analyticOnNhd (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hz₀ : z₀ ∈ U) :
    ContinuesInside f₀ U z₀ ↔ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ F =ᶠ[𝓝 z₀] f₀ := by
  refine ⟨fun H => H.exists_analyticOnNhd hUo hUc hz₀, ?_⟩
  rintro ⟨F, hF, hFeq⟩ c hc hcU hc0
  obtain ⟨f, hf, hf0⟩ := ContinuesAlong.of_analyticAt hc fun x => hF _ (hcU x)
  exact ⟨f, hf, by rw [hc0] at hf0 ⊢; exact hf0.trans hFeq⟩

end TauCeti
