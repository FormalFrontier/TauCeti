/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Complex.Conformal.Continuation
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The monodromy theorem

Analytic continuation along a path is unique (`Continuation.lean`), but the germ it delivers at
the far end may depend on the path. The **monodromy theorem** says that it only depends on the
path up to homotopy: if a germ continues along every path of a homotopy rel endpoints, all those
continuations end at the same germ. This is the L4 milestone of the conformal-mapping roadmap
that `Continuation.lean` left as a follow-up.

## The engine: stability under uniform perturbation of the path

Homotopy invariance is a consequence of a purely metric statement, proved here first and useful
on its own: **a continuation over a compact parameter set is stable under small uniform
perturbations of the path**. Concretely, `IsAnalyticContinuationAlong.exists_representatives`
turns the germs carried by a continuation into honest analytic functions on discs of one common
radius `ρ > 0`, matched on overlaps; the very same family of functions is then a continuation
along *any* path staying within `ρ` of the original
(`IsAnalyticContinuationAlong.exists_isAnalyticContinuationAlong_of_dist_lt`), so by
uniqueness the terminal germ is unchanged
(`IsAnalyticContinuationAlong.exists_eventuallyEq_of_dist_lt`).

The passage from germs to a uniform radius is where compactness of the parameter set enters: for
each parameter time one picks a disc on which the carried germ has an analytic representative and
a parameter neighbourhood on which the germ is constant, and a finite subcover turns the
resulting radii into a single positive `ρ`. Two representatives are then compared on the
intersection of their two discs, which is convex, hence preconnected, so the identity principle
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) upgrades germ agreement at one point to
equality on the whole overlap.

## Monodromy

With the engine in place, `TauCeti.monodromy` is a second connectedness argument, this time in
the homotopy parameter: the terminal germ of the continuation along `h (t, ·)` is a locally
constant function of `t`, because the paths `h (t, ·)` and `h (t₀, ·)` are uniformly close for
`t` near `t₀` — that uniformity is the continuity of the curried homotopy `I → C(I, ℂ)` into the
sup metric. A locally constant function on the connected parameter interval is constant.

`TauCeti.monodromy_refl` records the loop form: continuing a germ around a null-homotopic loop
returns the germ one started with, since the continuation along the constant loop is constant.

## Main results

* `TauCeti.IsAnalyticContinuationAlong.exists_representatives` — uniform disc representatives for
  a continuation over a compact parameter set.
* `TauCeti.IsAnalyticContinuationAlong.exists_isAnalyticContinuationAlong_of_dist_lt` —
  those representatives continue along every uniformly nearby path.
* `TauCeti.IsAnalyticContinuationAlong.exists_eventuallyEq_of_dist_lt` — **stability**: a
  continuation along a nearby path with the same endpoints and the same initial germ has the same
  terminal germ.
* `TauCeti.monodromy` — **the monodromy theorem**: continuations along the paths of a homotopy
  rel endpoints, all starting from one germ, all end at one germ.
* `TauCeti.monodromy_refl` — a germ continued around a null-homotopic loop comes back to itself.

## Relation to Mathlib

Mathlib's `IsLocalHomeomorph.monodromy_theorem` (`Mathlib/Topology/Homotopy/Lifting.lean`) is an
abstract monodromy statement about lifts through a separated local homeomorphism, and its
docstring names analytic continuation as the intended application. Consuming it here would first
require building the étale space of holomorphic germs over `ℂ` as a topological space and proving
the germ projection to be a separated local homeomorphism; Mathlib has no such space, and that
construction is a larger, independent piece of work. The route taken instead reuses what this
area already has — germ-level uniqueness of continuation along a fixed path
(`IsAnalyticContinuationAlong.eventuallyEq`) — and adds only the metric stability engine, which
is the concrete content that the abstract theorem's separatedness hypothesis packages. Building
the étale space and rederiving `monodromy` from Mathlib's abstract theorem remains worthwhile
follow-up work.

This advances the conformal-mapping roadmap's L4 target "the monodromy theorem (continuations
along homotopic paths agree)" (see `ConformalMapping/README.md`). L4 is not covered by the
roadmap's shim-deletion clause for the upstream Mathlib Riemann-mapping effort
(leanprover-community/mathlib4#33505), which contains no reflection, continuation or monodromy
material.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §3.
* W. Rudin, *Real and Complex Analysis*, Ch. 16.
-/

public section

namespace TauCeti

open Filter Metric Set Topology unitInterval

variable {X : Type*} [TopologicalSpace X] {f : X → ℂ → ℂ} {γ : X → ℂ} {s : Set X}

namespace IsAnalyticContinuationAlong

/-! ### Uniform disc representatives -/

/-- **Uniform disc representatives for a continuation over a compact parameter set.** The germs
carried by a continuation can be represented by honest functions `F t`, each analytic on a disc
about `γ t` of one radius `ρ > 0` independent of `t`, in such a way that nearby parameter times
carry representatives that agree on the whole disc — not merely near `γ t`.

The uniform radius is what makes the family usable along a *perturbed* path: the defining
condition of a continuation controls `f t` only near `γ t`, so `f t` itself carries no
information at a nearby point `γ' t`. -/
theorem exists_representatives (hf : IsAnalyticContinuationAlong f γ s) (hs : IsCompact s) :
    ∃ ρ > 0, ∃ F : X → ℂ → ℂ,
      (∀ t ∈ s, AnalyticOnNhd ℂ (F t) (ball (γ t) ρ)) ∧
      (∀ t ∈ s, F t =ᶠ[𝓝 (γ t)] f t) ∧
      (∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, EqOn (F u) (F t) (ball (γ t) ρ)) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨1, one_pos, 0, by simp, by simp, by simp⟩
  -- A disc of analyticity for each carried germ.
  choose! r hr hra using fun t (ht : t ∈ s) =>
    AnalyticAt.exists_ball_analyticOnNhd (hf.analyticAt t ht)
  -- An open parameter neighbourhood on which the germ is constant and the path barely moves.
  have hV : ∀ t ∈ s, ∃ V : Set X, IsOpen V ∧ t ∈ V ∧
      ∀ u ∈ V ∩ s, (f u =ᶠ[𝓝 (γ u)] f t) ∧ dist (γ u) (γ t) < r t / 4 := by
    intro t ht
    have hpos : 0 < r t / 4 := by have hrt := hr t ht; linarith
    have h₁ : ∀ᶠ u in 𝓝[s] t, dist (γ u) (γ t) < r t / 4 :=
      Metric.tendsto_nhds.1 (hf.continuousOn t ht) _ hpos
    obtain ⟨V, hVo, htV, hVsub⟩ := mem_nhdsWithin.1 (h₁.and (hf.locallyEq t ht))
    exact ⟨V, hVo, htV, fun u hu => ⟨(hVsub hu).2, (hVsub hu).1⟩⟩
  choose! V hVo hVt hVmem using hV
  obtain ⟨T, hTs, hTcov⟩ := hs.elim_nhds_subcover V fun t ht => (hVo t ht).mem_nhds (hVt t ht)
  have hTne : T.Nonempty := by
    obtain ⟨t, ht⟩ := hsne
    obtain ⟨j, hj, -⟩ := mem_iUnion₂.1 (hTcov ht)
    exact ⟨j, hj⟩
  choose! i hiT hiV using fun t (ht : t ∈ s) => mem_iUnion₂.1 (hTcov ht)
  -- The sampled index `i t` provides the representative `f (i t)`.
  have hmem : ∀ t ∈ s, i t ∈ s := fun t ht => hTs _ (hiT t ht)
  have hle : ∀ t ∈ s, T.inf' hTne r / 4 ≤ r (i t) / 4 := fun t ht => by
    have hinf := Finset.inf'_le r (hiT t ht)
    linarith
  have key : ∀ t ∈ s, (f t =ᶠ[𝓝 (γ t)] f (i t)) ∧ dist (γ t) (γ (i t)) < r (i t) / 4 :=
    fun t ht => hVmem (i t) (hmem t ht) t ⟨hiV t ht, ht⟩
  have hρpos : 0 < T.inf' hTne r / 4 := by
    have hinf : 0 < T.inf' hTne r := (Finset.lt_inf'_iff hTne).2 fun j hj => hr j (hTs j hj)
    linarith
  refine ⟨T.inf' hTne r / 4, hρpos, fun t => f (i t), fun t ht => ?_, fun t ht => (key t ht).1.symm,
    fun t ht => ?_⟩
  · refine (hra _ (hmem t ht)).mono (ball_subset_ball' ?_)
    have hdt := (key t ht).2
    have hlet := hle t ht
    have hrt := hr _ (hmem t ht)
    linarith
  -- Local agreement of representatives: compare them on the overlap of their two discs.
  · have hcont : ∀ᶠ u in 𝓝[s] t, dist (γ u) (γ t) < T.inf' hTne r / 4 :=
      Metric.tendsto_nhds.1 (hf.continuousOn t ht) _ hρpos
    have hnear : ∀ᶠ u in 𝓝[s] t, u ∈ V (i t) :=
      mem_nhdsWithin_of_mem_nhds ((hVo _ (hmem t ht)).mem_nhds (hiV t ht))
    filter_upwards [hcont, hnear, self_mem_nhdsWithin] with u hud huV hus
    have hju : (f u =ᶠ[𝓝 (γ u)] f (i t)) ∧ dist (γ u) (γ (i t)) < r (i t) / 4 :=
      hVmem (i t) (hmem t ht) u ⟨huV, hus⟩
    have hru := hr _ (hmem u hus)
    have hrt := hr _ (hmem t ht)
    have hagree : f (i u) =ᶠ[𝓝 (γ u)] f (i t) := ((key u hus).1.symm).trans hju.1
    have hCconn : IsPreconnected (ball (γ (i u)) (r (i u)) ∩ ball (γ (i t)) (r (i t))) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    have hEq : EqOn (f (i u)) (f (i t))
        (ball (γ (i u)) (r (i u)) ∩ ball (γ (i t)) (r (i t))) :=
      ((hra _ (hmem u hus)).mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
        ((hra _ (hmem t ht)).mono inter_subset_right) hCconn
        ⟨mem_ball.2 (by have hdu := (key u hus).2; linarith),
          mem_ball.2 (by linarith [hju.2])⟩ hagree
    refine fun z hz => hEq ⟨?_, ?_⟩
    · refine ball_subset_ball' ?_ hz
      have htri : dist (γ t) (γ (i u)) ≤ dist (γ t) (γ u) + dist (γ u) (γ (i u)) := dist_triangle ..
      have hsymm : dist (γ t) (γ u) = dist (γ u) (γ t) := dist_comm ..
      have hdu := (key u hus).2
      have hleu := hle u hus
      linarith
    · refine ball_subset_ball' ?_ hz
      have hdt := (key t ht).2
      have hlet := hle t ht
      linarith

/-! ### Stability under uniform perturbation of the path -/

/-- **One family of germs continues along every nearby path.** For a continuation over a compact
parameter set there are a radius `ρ > 0` and a family `F` carrying the same germs as `f` such
that `F` is an analytic continuation along *any* path that stays within `ρ` of `γ`.

Note the order of the quantifiers: the family `F` is produced once and for all, before the
perturbed path is given. -/
theorem exists_isAnalyticContinuationAlong_of_dist_lt (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsCompact s) :
    ∃ ρ > 0, ∃ F : X → ℂ → ℂ, (∀ t ∈ s, F t =ᶠ[𝓝 (γ t)] f t) ∧
      ∀ γ' : X → ℂ, ContinuousOn γ' s → (∀ t ∈ s, dist (γ' t) (γ t) < ρ) →
        IsAnalyticContinuationAlong F γ' s := by
  obtain ⟨ρ, hρ, F, hF₁, hF₂, hF₃⟩ := hf.exists_representatives hs
  refine ⟨ρ, hρ, F, hF₂, fun γ' hγ' hd => ⟨hγ', fun t ht => hF₁ t ht _ (mem_ball.2 (hd t ht)), ?_⟩⟩
  intro t ht
  have hmem : ∀ᶠ u in 𝓝[s] t, γ' u ∈ ball (γ t) ρ :=
    (hγ' t ht) (isOpen_ball.mem_nhds (mem_ball.2 (hd t ht)))
  filter_upwards [hF₃ t ht, hmem] with u hEq hu
  exact eventuallyEq_of_mem (isOpen_ball.mem_nhds hu) hEq

/-- **Stability of the terminal germ under uniform perturbation of the path.** For a continuation
`f` along `γ` over a compact preconnected parameter set there is a radius `ρ > 0` with the
following property: any continuation `g` along a path `γ'` that stays within `ρ` of `γ`, shares
the endpoints `γ' a = γ a` and `γ' b = γ b` of `γ`, and starts from the same germ as `f`, also
ends at the same germ as `f`.

This is the metric heart of the monodromy theorem: nearby paths with common endpoints continue a
germ to the same place. -/
theorem exists_eventuallyEq_of_dist_lt (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsCompact s) (hsc : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    ∃ ρ > 0, ∀ (γ' : X → ℂ) (g : X → ℂ → ℂ), ContinuousOn γ' s →
      (∀ t ∈ s, dist (γ' t) (γ t) < ρ) → γ' a = γ a → γ' b = γ b →
      IsAnalyticContinuationAlong g γ' s → g a =ᶠ[𝓝 (γ a)] f a → g b =ᶠ[𝓝 (γ b)] f b := by
  obtain ⟨ρ, hρ, F, hF, hcont⟩ := hf.exists_isAnalyticContinuationAlong_of_dist_lt hs
  refine ⟨ρ, hρ, fun γ' g hγ' hd hga hgb hg hstart => ?_⟩
  have h₀ : g a =ᶠ[𝓝 (γ' a)] F a := by
    rw [hga]; exact hstart.trans (hF a ha).symm
  have h₁ := hg.eventuallyEq (hcont γ' hγ' hd) hsc ha hb h₀
  rw [hgb] at h₁
  exact h₁.trans (hF b hb)

end IsAnalyticContinuationAlong

/-! ### The monodromy theorem -/

/-- **The monodromy theorem.** Let `h` be a homotopy rel endpoints between two paths from `z₀` to
`z₁` in `ℂ`, and suppose a germ at `z₀` continues along every path `h (t, ·)` of the homotopy,
all the continuations starting from that one germ. Then they all end at one and the same germ at
`z₁`: the result of the continuation depends on the path only through its homotopy class.

The proof is a connectedness argument in the homotopy parameter. For `t` near `t₀` the paths
`h (t, ·)` and `h (t₀, ·)` are uniformly close, since currying the homotopy gives a continuous
map into `C(I, ℂ)` with its sup metric; so
`IsAnalyticContinuationAlong.exists_eventuallyEq_of_dist_lt` applies and the terminal germ
is a locally constant function of `t` on the connected interval. -/
theorem monodromy {z₀ z₁ : ℂ} {p₀ p₁ : Path z₀ z₁} (h : p₀.Homotopy p₁) {f : I → I → ℂ → ℂ}
    (hf : ∀ t, IsAnalyticContinuationAlong (f t) (fun x => h (t, x)) univ)
    (hstart : ∀ t, f t 0 =ᶠ[𝓝 z₀] f 0 0) (t : I) :
    f t 1 =ᶠ[𝓝 z₁] f 0 1 := by
  have hloc : IsLocallyConstant fun t : I => f t 1 =ᶠ[𝓝 z₁] f 0 1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ρ, hρ, hkey⟩ := (hf t₀).exists_eventuallyEq_of_dist_lt isCompact_univ
      isPreconnected_univ (mem_univ 0) (mem_univ 1)
    -- Uniform closeness of the paths near `t₀`, from continuity of the curried homotopy.
    have hclose : ∀ᶠ t in 𝓝 t₀, ∀ x : I, dist (h (t, x)) (h (t₀, x)) < ρ := by
      have hd : ∀ᶠ t in 𝓝 t₀,
          dist (h.toHomotopy.curry t) (h.toHomotopy.curry t₀) < ρ :=
        Metric.tendsto_nhds.1 (h.toHomotopy.curry.continuous.tendsto t₀) ρ hρ
      filter_upwards [hd] with t ht x
      calc dist (h (t, x)) (h (t₀, x))
          = dist (h.toHomotopy.curry t x) (h.toHomotopy.curry t₀ x) := by
            simp [ContinuousMap.Homotopy.curry_apply]
        _ ≤ dist (h.toHomotopy.curry t) (h.toHomotopy.curry t₀) :=
            ContinuousMap.dist_apply_le_dist x
        _ < ρ := ht
    filter_upwards [hclose] with t ht
    have hstep : f t 1 =ᶠ[𝓝 z₁] f t₀ 1 := by
      have h₀ : f t 0 =ᶠ[𝓝 (h (t₀, 0))] f t₀ 0 := by
        simpa using (hstart t).trans (hstart t₀).symm
      have := hkey (fun x => h (t, x)) (f t) (hf t).continuousOn (fun x _ => ht x) (by simp)
        (by simp) (hf t) h₀
      simpa using this
    exact propext ⟨fun hp => hstep.symm.trans hp, fun hp => hstep.trans hp⟩
  have := hloc.apply_eq_of_preconnectedSpace t 0
  rw [this]

/-- **A germ continued around a null-homotopic loop returns to itself.** If the loop `p` at `z₀`
is homotopic rel endpoints to the constant loop and a germ at `z₀` continues along every path of
the homotopy, then continuing it along `p` gives the germ back.

Together with the uniqueness of continuation along a fixed path, this is the reason a germ on a
simply connected domain is single-valued: no loop there can create a new branch. -/
theorem monodromy_refl {z₀ : ℂ} {p : Path z₀ z₀} (h : p.Homotopy (Path.refl z₀))
    {f : I → I → ℂ → ℂ}
    (hf : ∀ t, IsAnalyticContinuationAlong (f t) (fun x => h (t, x)) univ)
    (hstart : ∀ t, f t 0 =ᶠ[𝓝 z₀] f 0 0) :
    f 0 1 =ᶠ[𝓝 z₀] f 0 0 := by
  have hconst : (fun x : I => h (1, x)) = fun _ : I => z₀ := by
    funext x; simp
  have hc : IsAnalyticContinuationAlong (f 1) (fun _ : I => z₀) univ := hconst ▸ hf 1
  have hc' : IsAnalyticContinuationAlong (fun _ : I => f 1 0) (fun _ : I => z₀) univ :=
    .const continuousOn_const fun _ _ => hc.analyticAt 0 (mem_univ 0)
  have hloop : f 1 1 =ᶠ[𝓝 z₀] f 1 0 :=
    hc.eventuallyEq hc' isPreconnected_univ (mem_univ 0) (mem_univ 1) .rfl
  exact (monodromy h hf hstart 1).symm.trans (hloop.trans (hstart 1))

/-- The hypotheses of `monodromy` are satisfiable, so the theorem is not vacuous: a function
holomorphic on an open set through which the whole homotopy passes continues itself along every
path of that homotopy, from one and the same germ. (What monodromy then says in this special
case is of course trivial — a single-valued function carries a single germ; the theorem has
content exactly when the continuations are not all restrictions of one function.) -/
example {z₀ z₁ : ℂ} {p₀ p₁ : Path z₀ z₁} (h : p₀.Homotopy p₁) {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hmaps : ∀ q : I × I, h q ∈ U) :
    (∀ t, IsAnalyticContinuationAlong ((fun _ _ : I => F) t) (fun x => h (t, x)) univ) ∧
      ∀ t : I, (fun _ _ : I => F) t 0 =ᶠ[𝓝 z₀] (fun _ _ : I => F) 0 0 :=
  ⟨fun t => .of_differentiableOn hU hF (h.toHomotopy.curry t).continuous.continuousOn
    fun x _ => hmaps (t, x), fun _ => .rfl⟩

end TauCeti
