/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.UniformSpace.Compact

/-!
# The monodromy theorem

Analytic continuation along a path is unique (`Continuation/Basic.lean`), but the germ it
delivers at the far end may depend on the path. The **monodromy theorem** says that it only
depends on the path up to homotopy: if a germ continues along every path of a homotopy rel
endpoints, all those continuations end at the same germ. This is the L4 milestone of the
conformal-mapping roadmap that `Continuation/Basic.lean` left as a follow-up.

The theorem is proved here in the form that does **not** hold the endpoints fixed. A homotopy of
paths whose endpoints move carries the initial germs along the path `t ↦ h (t, 0)` swept out by
the starting point, and what `TauCeti.monodromy_theorem_of_free_homotopy` asserts is that the
terminal germs are then carried along the path `t ↦ h (t, 1)` swept out by the finishing point:
the conclusion is again a continuation, not an equality of germs. Fixing the endpoints degenerates
both edges to constant paths, where "continues along a constant path" means "is one germ", and
recovers the classical statement `TauCeti.monodromy_theorem`. The extra generality is not
decorative — it is what makes monodromy an invariant of the *free* homotopy class of a loop
(`TauCeti.monodromy_theorem_of_free_homotopy_loop`), a statement about a homotopy that moves the
base point and so out of reach of the rel-endpoints form.

## The engine: stability under uniform perturbation of the path

Homotopy invariance is a consequence of a purely metric statement, proved here first and useful
on its own: **a continuation over a compact parameter set is stable under small uniform
perturbations of the path**. Concretely, `IsAnalyticContinuationAlong.exists_representatives`
turns the germs carried by a continuation into honest analytic functions on discs of one common
radius `ρ > 0`, matched on overlaps; the very same family of functions is then a continuation
along *any* path staying within `ρ` of the original
(`IsAnalyticContinuationAlong.exists_isAnalyticContinuationAlong_of_dist_lt`), so by uniqueness a
continuation along a nearby path that meets it at one parameter time meets it at all of them
(`IsAnalyticContinuationAlong.exists_forall_eventuallyEq_of_dist_lt`).

That comparison is made against the representative family `F`, not against `f` itself, and the
distinction is what the moving endpoints cost: the germ of the perturbed continuation lives at
`γ' a`, a point at which `f a` need not even be analytic, whereas `F a` is analytic on a whole
disc of radius `ρ` about `γ a`. When the perturbation fixes the endpoints the representative can
be traded back for `f`, and that is the classical statement
`IsAnalyticContinuationAlong.exists_eventuallyEq_of_dist_lt`.

The passage from germs to a uniform radius is where compactness of the parameter set enters: for
each parameter time one picks a disc on which the carried germ has an analytic representative and
a parameter neighbourhood on which the germ is constant, and a finite subcover turns the
resulting radii into a single positive `ρ`. Two representatives are then compared on the
intersection of their two discs, which is convex, hence preconnected, so the identity principle
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) upgrades germ agreement at one point to
equality on the whole overlap.

## Monodromy

With the engine in place, `TauCeti.monodromy_theorem_of_free_homotopy` is the statement that the
terminal germs form a continuation along the terminal edge. Its three clauses are read off in
turn: continuity of that edge and analyticity of each terminal germ are immediate, and the
remaining clause — nearby parameters carry the same terminal germ — is the engine applied to the
row at `t₀`. Rows `h (t, ·)` and `h (t₀, ·)` are uniformly close for `t` near `t₀` because `h` is
uniformly continuous on the compact square, and the two rows meet at the initial parameter because
`hstart` is a continuation. The one point needing care is that the engine compares germs at the
*moved* endpoints `h (t, 0)` and `h (t, 1)`, while the representative family is matched to `f t₀`
only at `h (t₀, 0)` and `h (t₀, 1)`. Transporting that match is what
`TauCeti.eventually_eventuallyEq_iff_of_analyticAt` is for: two analytic functions with a common
germ at a point have a common germ at every point near it, so the match survives the move.

`TauCeti.monodromy_theorem_of_homotopy_refl` records the loop form of the rel-endpoints statement:
continuing a germ around a null-homotopic loop returns the germ one started with, since the
continuation along the constant loop is constant.

## Main results

* `TauCeti.IsAnalyticContinuationAlong.exists_representatives` — uniform disc representatives for
  a continuation over a compact parameter set.
* `TauCeti.IsAnalyticContinuationAlong.exists_isAnalyticContinuationAlong_of_dist_lt` —
  those representatives continue along every uniformly nearby path.
* `TauCeti.IsAnalyticContinuationAlong.exists_forall_eventuallyEq_of_dist_lt` — **stability with
  moving endpoints**: a continuation along a nearby path that matches the representative family at
  one parameter time matches it at every parameter time.
* `TauCeti.IsAnalyticContinuationAlong.exists_eventuallyEq_of_dist_lt` — **stability**: a
  continuation along a nearby path with the same endpoints and the same initial germ has the same
  terminal germ.
* `TauCeti.monodromy_theorem_of_free_homotopy` — **the monodromy theorem for a free homotopy**:
  germs continued across a homotopy whose endpoints move form a continuation along the path the
  far endpoint sweeps out.
* `TauCeti.monodromy_theorem` — **the monodromy theorem**: continuations along the paths of a
  homotopy rel endpoints, all starting from one germ, all end at one germ.
* `TauCeti.monodromy_theorem_of_free_homotopy_loop` — the monodromy of a loop is unchanged by a
  free homotopy through loops, base point included.
* `TauCeti.monodromy_theorem_of_homotopy_refl` — a germ continued around a null-homotopic loop
  comes back to itself.

## Generality

The germs carried are germs of maps `ℂ → E` into a complex Banach space, as in
`Continuation/Basic.lean`, where the choice is discussed; the conformal-mapping consumers of the
monodromy theorem instantiate `E = ℂ`. Nothing in the stability engine sees the target: the disc
representatives come from `AnalyticAt.exists_ball_analyticOnNhd` and are compared by the identity
principle, both of which Mathlib states for maps into an arbitrary Banach space.

## Relation to Mathlib

Mathlib's `IsLocalHomeomorph.monodromy_theorem` (`Mathlib/Topology/Homotopy/Lifting.lean`) is an
abstract monodromy statement about lifts through a separated local homeomorphism, and its
docstring names analytic continuation as the intended application. The route taken here is
independent of it: it reuses what this area already has — germ-level uniqueness of continuation
along a fixed path (`IsAnalyticContinuationAlong.eventuallyEq`) — and adds only the metric
stability engine, which is the concrete content that the abstract theorem's separatedness
hypothesis packages. The other route is now available too:
`TauCeti/Analysis/Complex/HolomorphicSheaf.lean` builds the étale space of holomorphic germs and
proves its projection to be a separated local homeomorphism, and
Mathlib's abstract theorem applies directly to that projection. That route does not subsume this
file:
`TauCeti.monodromy_theorem_of_free_homotopy` moves the endpoints and concludes with a
continuation along the path they sweep out, whereas the abstract theorem is rel endpoints and
concludes with an equality of two lifted points.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {X : Type*} [TopologicalSpace X] {f : X → ℂ → E} {γ : X → ℂ} {s : Set X}

namespace IsAnalyticContinuationAlong

/-! ### Uniform disc representatives -/

omit [CompleteSpace E] in
/-- Around any parameter time of a continuation there is an open neighbourhood on which the
carried germ is constant and the path has moved by less than a prescribed `ε`.

The two clauses are the continuation's own local data — `locallyEq` and continuity of `γ` —
intersected; `ε` is arbitrary rather than tied to any disc radius. -/
private lemma exists_isOpen_locallyEq_and_dist_lt (hf : IsAnalyticContinuationAlong f γ s)
    {t : X} (ht : t ∈ s) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ t ∈ V ∧
      ∀ u ∈ V ∩ s, (f u =ᶠ[𝓝 (γ u)] f t) ∧ dist (γ u) (γ t) < ε := by
  have h₁ : ∀ᶠ u in 𝓝[s] t, dist (γ u) (γ t) < ε :=
    Metric.tendsto_nhds.1 (hf.continuousOn t ht) _ hε
  obtain ⟨V, hVo, htV, hVsub⟩ := mem_nhdsWithin.1 (h₁.and (hf.locallyEq t ht))
  exact ⟨V, hVo, htV, fun u hu => ⟨(hVsub hu).2, (hVsub hu).1⟩⟩

/-- **Sampling a compact parameter set.** Compactness turns the purely local data of a
continuation into a *uniform* package: one radius `ρ > 0`, a sampling `i` of parameter times, and
a radius `R t` for the disc of analyticity at the sampled time, such that

* the disc of analyticity at the sample has radius `R t ≥ 4ρ`;
* `f t` and `f (i t)` carry the same germ, with `γ t` well inside that disc; and
* the same holds for every `u` near `t`, still measured against the sample `i t`.

The last clause is the finite subcover doing its work: one sample serves a whole parameter
neighbourhood. -/
private lemma exists_uniform_sampling (hf : IsAnalyticContinuationAlong f γ s) (hs : IsCompact s)
    (hsne : s.Nonempty) :
    ∃ ρ > 0, ∃ (i : X → X) (R : X → ℝ),
      (∀ t ∈ s, i t ∈ s) ∧
      (∀ t ∈ s, 4 * ρ ≤ R t) ∧
      (∀ t ∈ s, AnalyticOnNhd ℂ (f (i t)) (ball (γ (i t)) (R t))) ∧
      (∀ t ∈ s, (f t =ᶠ[𝓝 (γ t)] f (i t)) ∧ dist (γ t) (γ (i t)) < R t / 4) ∧
      (∀ t ∈ s, ∀ᶠ u in 𝓝[s] t,
        (f u =ᶠ[𝓝 (γ u)] f (i t)) ∧ dist (γ u) (γ (i t)) < R t / 4) := by
  -- A disc of analyticity for each carried germ.
  choose! r hr hra using fun t (ht : t ∈ s) =>
    AnalyticAt.exists_ball_analyticOnNhd (hf.analyticAt t ht)
  -- An open parameter neighbourhood on which the germ is constant and the path barely moves.
  have hV : ∀ t ∈ s, ∃ V : Set X, IsOpen V ∧ t ∈ V ∧
      ∀ u ∈ V ∩ s, (f u =ᶠ[𝓝 (γ u)] f t) ∧ dist (γ u) (γ t) < r t / 4 := fun t ht =>
    exists_isOpen_locallyEq_and_dist_lt hf ht (by have hrt := hr t ht; linarith)
  choose! V hVo hVt hVmem using hV
  obtain ⟨T, hTs, hTcov⟩ := hs.elim_nhds_subcover V fun t ht => (hVo t ht).mem_nhds (hVt t ht)
  have hTne : T.Nonempty := by
    obtain ⟨t, ht⟩ := hsne
    obtain ⟨j, hj, -⟩ := mem_iUnion₂.1 (hTcov ht)
    exact ⟨j, hj⟩
  choose! i hiT hiV using fun t (ht : t ∈ s) => mem_iUnion₂.1 (hTcov ht)
  have hmem : ∀ t ∈ s, i t ∈ s := fun t ht => hTs _ (hiT t ht)
  have hρpos : 0 < T.inf' hTne r / 4 := by
    have hinf : 0 < T.inf' hTne r := (Finset.lt_inf'_iff hTne).2 fun j hj => hr j (hTs j hj)
    linarith
  refine ⟨T.inf' hTne r / 4, hρpos, i, fun t => r (i t), hmem, fun t ht => ?_,
    fun t ht => hra _ (hmem t ht), fun t ht => hVmem (i t) (hmem t ht) t ⟨hiV t ht, ht⟩,
    fun t ht => ?_⟩
  · have hinf := Finset.inf'_le r (hiT t ht)
    linarith
  · have hnear : ∀ᶠ u in 𝓝[s] t, u ∈ V (i t) :=
      mem_nhdsWithin_of_mem_nhds ((hVo _ (hmem t ht)).mem_nhds (hiV t ht))
    filter_upwards [hnear, self_mem_nhdsWithin] with u huV hus
    exact hVmem (i t) (hmem t ht) u ⟨huV, hus⟩

/-- **Uniform disc representatives for a continuation over a compact parameter set.** The germs
carried by a continuation can be represented by honest functions `F t`, each analytic on a disc
about `γ t` of one radius `ρ > 0` independent of `t`, in such a way that nearby parameter times
carry representatives that agree on the whole disc — not merely near `γ t`.

The uniform radius is what makes the family usable along a *perturbed* path: the defining
condition of a continuation controls `f t` only near `γ t`, so `f t` itself carries no
information at a nearby point `γ' t`. -/
theorem exists_representatives (hf : IsAnalyticContinuationAlong f γ s) (hs : IsCompact s) :
    ∃ ρ > 0, ∃ F : X → ℂ → E,
      (∀ t ∈ s, AnalyticOnNhd ℂ (F t) (ball (γ t) ρ)) ∧
      (∀ t ∈ s, F t =ᶠ[𝓝 (γ t)] f t) ∧
      (∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, EqOn (F u) (F t) (ball (γ t) ρ)) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨1, one_pos, 0, by simp, by simp, by simp⟩
  obtain ⟨ρ, hρpos, i, R, hmem, hR, hra, key, hloc⟩ := exists_uniform_sampling hf hs hsne
  refine ⟨ρ, hρpos, fun t => f (i t), fun t ht => ?_, fun t ht => (key t ht).1.symm,
    fun t ht => ?_⟩
  · refine (hra t ht).mono (ball_subset_ball' ?_)
    have hdt := (key t ht).2
    have hRt := hR t ht
    linarith
  -- Local agreement of representatives: compare them on the overlap of their two discs.
  · have hcont : ∀ᶠ u in 𝓝[s] t, dist (γ u) (γ t) < ρ :=
      Metric.tendsto_nhds.1 (hf.continuousOn t ht) _ hρpos
    filter_upwards [hcont, hloc t ht, self_mem_nhdsWithin] with u hud hju hus
    have hRu := hR u hus
    have hRt := hR t ht
    -- The overlap of the two discs is convex, hence preconnected, so the identity principle
    -- upgrades germ agreement at `γ u` to equality on all of it.
    have hEq : EqOn (f (i u)) (f (i t)) (ball (γ (i u)) (R u) ∩ ball (γ (i t)) (R t)) :=
      ((hra u hus).mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
        ((hra t ht).mono inter_subset_right)
        ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
        ⟨mem_ball.2 (by have hdu := (key u hus).2; linarith),
          mem_ball.2 (by linarith [hju.2])⟩ (((key u hus).1.symm).trans hju.1)
    refine fun z hz => hEq ⟨?_, ?_⟩
    · refine ball_subset_ball' ?_ hz
      have htri : dist (γ t) (γ (i u)) ≤ dist (γ t) (γ u) + dist (γ u) (γ (i u)) := dist_triangle ..
      have hsymm : dist (γ t) (γ u) = dist (γ u) (γ t) := dist_comm ..
      have hdu := (key u hus).2
      linarith
    · refine ball_subset_ball' ?_ hz
      have hdt := (key t ht).2
      linarith

/-! ### Stability under uniform perturbation of the path -/

/-- **One family of germs continues along every nearby path.** For a continuation over a compact
parameter set there are a radius `ρ > 0` and a family `F` carrying the same germs as `f` such
that `F` is an analytic continuation along *any* path that stays within `ρ` of `γ`.

Note the order of the quantifiers: the family `F` is produced once and for all, before the
perturbed path is given. -/
theorem exists_isAnalyticContinuationAlong_of_dist_lt (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsCompact s) :
    ∃ ρ > 0, ∃ F : X → ℂ → E, (∀ t ∈ s, F t =ᶠ[𝓝 (γ t)] f t) ∧
      ∀ γ' : X → ℂ, ContinuousOn γ' s → (∀ t ∈ s, dist (γ' t) (γ t) < ρ) →
        IsAnalyticContinuationAlong F γ' s := by
  obtain ⟨ρ, hρ, F, hF₁, hF₂, hF₃⟩ := hf.exists_representatives hs
  refine ⟨ρ, hρ, F, hF₂, fun γ' hγ' hd => ⟨hγ', fun t ht => hF₁ t ht _ (mem_ball.2 (hd t ht)), ?_⟩⟩
  intro t ht
  have hmem : ∀ᶠ u in 𝓝[s] t, γ' u ∈ ball (γ t) ρ :=
    (hγ' t ht) (isOpen_ball.mem_nhds (mem_ball.2 (hd t ht)))
  filter_upwards [hF₃ t ht, hmem] with u hEq hu
  exact eventuallyEq_of_mem (isOpen_ball.mem_nhds hu) hEq

/-- **Stability of the carried germ under uniform perturbation of the path, measured against a
fixed comparison family.** For a continuation `f` along `γ` over a compact preconnected parameter
set there are a radius `ρ > 0` and a family `F` carrying the same germs as `f` such that any
continuation `g` along a path `γ'` staying within `ρ` of `γ` and agreeing with `F` at *one*
parameter time agrees with `F` at *every* parameter time.

No relation between the endpoints of `γ'` and those of `γ` is required, which is what makes this
the form a homotopy with moving endpoints consumes. The price is that the comparison has to be
made against `F` rather than against `f`: the germ of `g a` lives at `γ' a`, where `f a` need not
even be analytic, while `F a` is analytic on a whole disc of radius `ρ` about `γ a`. When the
endpoints do not move, `TauCeti.IsAnalyticContinuationAlong.exists_eventuallyEq_of_dist_lt`
eliminates `F` again. -/
theorem exists_forall_eventuallyEq_of_dist_lt (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsCompact s) (hsc : IsPreconnected s) :
    ∃ ρ > 0, ∃ F : X → ℂ → E, (∀ t ∈ s, F t =ᶠ[𝓝 (γ t)] f t) ∧
      ∀ (γ' : X → ℂ) (g : X → ℂ → E), (∀ t ∈ s, dist (γ' t) (γ t) < ρ) →
        IsAnalyticContinuationAlong g γ' s →
        ∀ ⦃a : X⦄, a ∈ s → ∀ ⦃b : X⦄, b ∈ s →
          g a =ᶠ[𝓝 (γ' a)] F a → g b =ᶠ[𝓝 (γ' b)] F b := by
  obtain ⟨ρ, hρ, F, hF, hcont⟩ := hf.exists_isAnalyticContinuationAlong_of_dist_lt hs
  exact ⟨ρ, hρ, F, hF, fun γ' g hd hg _ ha _ hb h₀ =>
    hg.eventuallyEq (hcont γ' hg.continuousOn hd) hsc ha hb h₀⟩

/-- **Stability of the terminal germ under uniform perturbation of the path.** For a continuation
`f` along `γ` over a compact preconnected parameter set there is a radius `ρ > 0` with the
following property: any continuation `g` along a path `γ'` that stays within `ρ` of `γ`, shares
the endpoints `γ' a = γ a` and `γ' b = γ b` of `γ`, and starts from the same germ as `f`, also
ends at the same germ as `f`.

This is the metric heart of the monodromy theorem for a homotopy rel endpoints: nearby paths with
common endpoints continue a germ to the same place. It is the fixed-endpoint specialization of
`TauCeti.IsAnalyticContinuationAlong.exists_forall_eventuallyEq_of_dist_lt`, the endpoint
equalities being exactly what lets the comparison family be traded back for `f`. -/
theorem exists_eventuallyEq_of_dist_lt (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsCompact s) (hsc : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    ∃ ρ > 0, ∀ (γ' : X → ℂ) (g : X → ℂ → E),
      (∀ t ∈ s, dist (γ' t) (γ t) < ρ) → γ' a = γ a → γ' b = γ b →
      IsAnalyticContinuationAlong g γ' s → g a =ᶠ[𝓝 (γ a)] f a → g b =ᶠ[𝓝 (γ b)] f b := by
  obtain ⟨ρ, hρ, F, hF, hkey⟩ := hf.exists_forall_eventuallyEq_of_dist_lt hs hsc
  refine ⟨ρ, hρ, fun γ' g hd hga hgb hg hstart => ?_⟩
  have h₀ : g a =ᶠ[𝓝 (γ' a)] F a := by
    rw [hga]; exact hstart.trans (hF a ha).symm
  have h₁ := hkey γ' g hd hg ha hb h₀
  rw [hgb] at h₁
  exact h₁.trans (hF b hb)

end IsAnalyticContinuationAlong

/-! ### The monodromy theorem -/

/-- Germ agreement at a point spreads to the points a moving base point reaches nearby: if `F` and
`G` are analytic at `c t₀` and have the same germ there, then they have the same germ at `c t` for
every `t` near `t₀`.

This is the transport that lets a germ comparison made at the base point `c t₀` be re-used at the
moving endpoint `c t` of a free homotopy, and it is why the two edges of such a homotopy may be
compared against one fixed representative family. -/
private lemma eventually_eventuallyEq_of_continuousAt {Z : Type*} [TopologicalSpace Z] {c : Z → ℂ}
    {t₀ : Z} {F G : ℂ → E} (hc : ContinuousAt c t₀) (hF : AnalyticAt ℂ F (c t₀))
    (hG : AnalyticAt ℂ G (c t₀)) (h : F =ᶠ[𝓝 (c t₀)] G) :
    ∀ᶠ t in 𝓝 t₀, F =ᶠ[𝓝 (c t)] G :=
  hc.eventually ((eventually_eventuallyEq_iff_of_analyticAt hF hG).mono fun _ hiff => hiff.mpr h)

/-- **The monodromy theorem for a free homotopy of paths.** Let `h` be a continuous map of the
square, read as a family of paths `h (t, ·)` whose *endpoints are allowed to move*, and suppose a
family of germs continues along each of those paths. If the initial germs — the germ of `f t 0` at
`h (t, 0)` — themselves continue along the initial edge `t ↦ h (t, 0)`, then the terminal germs
continue along the terminal edge `t ↦ h (t, 1)`.

This is the monodromy theorem in the form the deck-group and covering-space consumers need: the
continuation of a germ across a homotopy is itself a continuation, along the path the far endpoint
sweeps out. Nothing is assumed rel endpoints; `TauCeti.monodromy_theorem` is the special case in
which both edges are constant, where "continues along a constant path" degenerates to "carries one
germ throughout". -/
theorem monodromy_theorem_of_free_homotopy {h : I × I → ℂ} (hh : Continuous h)
    {f : I → I → ℂ → E}
    (hf : ∀ t, IsAnalyticContinuationAlong (f t) (fun x => h (t, x)) univ)
    (hstart : IsAnalyticContinuationAlong (fun t => f t 0) (fun t => h (t, 0)) univ) :
    IsAnalyticContinuationAlong (fun t => f t 1) (fun t => h (t, 1)) univ := by
  have hedge : ∀ y : I, Continuous fun t : I => h (t, y) := fun y => by fun_prop
  refine ⟨(hedge 1).continuousOn, fun t _ => (hf t).analyticAt 1 (mem_univ 1), ?_⟩
  intro t₀ _
  rw [nhdsWithin_univ]
  obtain ⟨ρ, hρ, F, hF, hkey⟩ :=
    (hf t₀).exists_forall_eventuallyEq_of_dist_lt isCompact_univ isPreconnected_univ
  -- The representative of the row at `t₀` still matches `f t₀` at the points a moving edge reaches.
  have hedgeEq : ∀ y : I, ∀ᶠ t in 𝓝 t₀, F y =ᶠ[𝓝 (h (t, y))] f t₀ y := fun y =>
    eventually_eventuallyEq_of_continuousAt (hedge y).continuousAt
      (((hf t₀).analyticAt y (mem_univ y)).congr (hF y (mem_univ y)).symm)
      ((hf t₀).analyticAt y (mem_univ y)) (hF y (mem_univ y))
  -- Uniform closeness of nearby rows, from uniform continuity of `h` on the compact square.
  obtain ⟨δ, hδ, hδρ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hh) ρ hρ
  have hclose : ∀ᶠ t in 𝓝 t₀, ∀ x : I, dist (h (t, x)) (h (t₀, x)) < ρ := by
    filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht x
    have hdist : dist ((t, x) : I × I) (t₀, x) = dist t t₀ := by simp [Prod.dist_eq]
    exact hδρ (hdist ▸ mem_ball.1 ht)
  -- The initial germs of nearby rows agree, because `hstart` is itself a continuation.
  have hstart₀ : ∀ᶠ t in 𝓝 t₀, f t 0 =ᶠ[𝓝 (h (t, 0))] f t₀ 0 := by
    simpa using hstart.locallyEq t₀ (mem_univ t₀)
  filter_upwards [hclose, hedgeEq 0, hedgeEq 1, hstart₀] with t hct hz₀ hz₁ hs₀
  exact (hkey (fun x => h (t, x)) (f t) (fun x _ => hct x) (hf t) (mem_univ 0) (mem_univ 1)
    (hs₀.trans hz₀.symm)).trans hz₁

/-- **The monodromy theorem.** Let `h` be a homotopy rel endpoints between two paths from `z₀` to
`z₁` in `ℂ`, and suppose a germ at `z₀` continues along every path `h (t, ·)` of the homotopy,
all the continuations starting from that one germ. Then they all end at one and the same germ at
`z₁`: the result of the continuation depends on the path only through its homotopy class.

This is the rel-endpoints case of `TauCeti.monodromy_theorem_of_free_homotopy`, whose homotopy is
allowed to move the endpoints and whose conclusion is correspondingly a continuation along the
path the terminal point sweeps out rather than a single germ at `z₁`. -/
theorem monodromy_theorem {z₀ z₁ : ℂ} {p₀ p₁ : Path z₀ z₁} (h : p₀.Homotopy p₁)
    {f : I → I → ℂ → E}
    (hf : ∀ t, IsAnalyticContinuationAlong (f t) (fun x => h (t, x)) univ)
    (hstart : ∀ t, f t 0 =ᶠ[𝓝 z₀] f 0 0) (t : I) :
    f t 1 =ᶠ[𝓝 z₁] f 0 1 := by
  have hsrc : ∀ u : I, h (u, 0) = z₀ := fun u => by simp
  have htgt : ∀ u : I, h (u, 1) = z₁ := fun u => by simp
  have hstart' : IsAnalyticContinuationAlong (fun u => f u 0) (fun u => h (u, 0)) univ := by
    refine ⟨by simp only [hsrc]; exact continuousOn_const, fun u _ => ?_,
      fun u _ => .of_forall fun v => ?_⟩
    · simpa [hsrc] using (hf u).analyticAt 0 (mem_univ 0)
    · rw [hsrc]; exact (hstart v).trans (hstart u).symm
  have hend := monodromy_theorem_of_free_homotopy (map_continuous h) hf hstart'
  have hconst : IsAnalyticContinuationAlong (fun _ : I => f 0 1) (fun u => h (u, 1)) univ :=
    .const (by simp only [htgt]; exact continuousOn_const)
      fun u _ => by simpa [htgt] using (hf 0).analyticAt 1 (mem_univ 1)
  simpa [htgt] using
    hend.eventuallyEq hconst isPreconnected_univ (mem_univ 0) (mem_univ t) .rfl

/-- **The monodromy of a loop depends only on its free homotopy class.** If `h` is a homotopy
through *loops* — each row `h (t, ·)` closes up, `h (t, 1) = h (t, 0)` — and the initial germs
continue along the path `t ↦ h (t, 0)` swept out by the base point, then the germ is preserved by
continuation around every loop of the homotopy as soon as it is preserved around one of them.

This is the statement that makes monodromy an invariant of the free homotopy class of a loop, and
it is out of reach of `TauCeti.monodromy_theorem`, whose homotopies must fix the base point. -/
theorem monodromy_theorem_of_free_homotopy_loop {h : I × I → ℂ} (hh : Continuous h)
    (hloop : ∀ t : I, h (t, 1) = h (t, 0)) {f : I → I → ℂ → E}
    (hf : ∀ t, IsAnalyticContinuationAlong (f t) (fun x => h (t, x)) univ)
    (hstart : IsAnalyticContinuationAlong (fun t => f t 0) (fun t => h (t, 0)) univ)
    (hbase : f 0 1 =ᶠ[𝓝 (h (0, 0))] f 0 0) (t : I) :
    f t 1 =ᶠ[𝓝 (h (t, 0))] f t 0 := by
  have hend := monodromy_theorem_of_free_homotopy hh hf hstart
  rw [funext hloop] at hend
  exact hend.eventuallyEq hstart isPreconnected_univ (mem_univ 0) (mem_univ t) hbase

/-- **A germ continued around a null-homotopic loop returns to itself.** If the loop `p` at `z₀`
is homotopic rel endpoints to the constant loop and a germ at `z₀` continues along every path of
the homotopy, then continuing it along `p` gives the germ back.

Together with the uniqueness of continuation along a fixed path, this is the reason a germ that
can be analytically continued along every path of a simply connected domain is single-valued
there: no loop in such a domain can create a new branch. -/
theorem monodromy_theorem_of_homotopy_refl {z₀ : ℂ} {p : Path z₀ z₀}
    (h : p.Homotopy (Path.refl z₀)) {f : I → I → ℂ → E}
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
  exact (monodromy_theorem h hf hstart 1).symm.trans (hloop.trans (hstart 1))

/-- The hypotheses of `monodromy_theorem` are satisfiable, so it is not vacuous: a function
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
