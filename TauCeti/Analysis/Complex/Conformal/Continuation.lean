/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Analytic continuation along a path

An **analytic continuation along a path** `γ` is the classical device that turns a single
holomorphic germ into a multi-valued function: one carries the germ along `γ`, re-expanding it at
each parameter time. This file introduces that notion and proves its fundamental property, that a
continuation is **determined by its initial germ**.

A continuation is recorded as a family `f : X → ℂ → ℂ` of functions indexed by the path parameter,
subject to the requirement that `f t` be analytic at `γ t` and that the germ of `f u` at `γ u`
agree with the germ of `f t` at `γ u` for all `u` near `t`. Equivalently — and this is the way to
read the definition — the assignment `t ↦ (germ of f t at γ t)` is a *continuous lift* of `γ` to
the étale space of holomorphic germs. The classical "chain of overlapping discs" definition is the
same condition written with explicit discs; the germ formulation avoids carrying the discs around.

The parameter space `X` is an arbitrary topological space, and the parameter set `s : Set X` is
constrained only by `IsPreconnected` where the mathematics needs it. Nothing here uses the order or
the field structure of the reals, so the usual `X = ℝ` with `s = Set.Icc 0 1` and Mathlib's
`Path`, whose parameter space is `unitInterval`, are both directly available.

## The uniqueness theorem

`TauCeti.IsAnalyticContinuationAlong.eventuallyEq`: two continuations along the same path over a
preconnected parameter set whose germs agree at one parameter time agree at every parameter time.

The proof is the standard connectedness argument. Germ agreement is a *locally constant* property
of the parameter: at a time `t`, both `f t` and `g t` are analytic on a common disc `D` about
`γ t`, so by the identity principle (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) their
germs agree at one point of `D` exactly when they agree at every point of `D` — and for `u` near
`t` the point `γ u` lies in `D` while the germs of `f u, g u` at `γ u` are those of `f t, g t`.
A locally constant property on a preconnected parameter set is constant
(`IsLocallyConstant.apply_eq_of_preconnectedSpace`).

## Continuability as a property of the initial germ

A continuation is determined by its initial germ, so *being continuable* is a property of that
germ alone. `TauCeti.ContinuesAlong` records it for a single path of the unit interval, and
`TauCeti.ContinuesInside` for every path inside a domain issuing from a base point; both transport
across eventual equality of the initial function (`TauCeti.continuesAlong_congr`,
`TauCeti.continuesInside_congr`). `TauCeti.ContinuesInside` is the hypothesis of the monodromy
theorem for a simply connected domain (`Conformal/GlobalBranch.lean`).

Both predicates are closed under the ring operations and under differentiation, because a
continuation of a combination of germs is the corresponding combination of continuations of the
parts: the closure lemmas of `TauCeti.IsAnalyticContinuationAlong` transport to them verbatim, with
no choice of continuation to reconcile. A function analytic at every point of a continuous path
continues along it via the constant family (`TauCeti.ContinuesAlong.of_analyticAt`), so
continuability is a condition one may check on the pieces of a germ built from simpler ones.

## Substitution, reciprocals and reparametrisation

Beyond the ring operations a germ is built by two further moves, and continuation is closed under
both. **Substitution** is `TauCeti.IsAnalyticContinuationAlong.comp`: continuing `f` along `γ` and
continuing `g` along the path `t ↦ f t (γ t)` that the *values* of `f` sweep out continues the
composite germ `g t ∘ f t` along `γ`. The inner path is not a further datum — it is forced, and it
is continuous, which is `TauCeti.IsAnalyticContinuationAlong.continuousOn_apply`. **Reciprocals**
are `TauCeti.IsAnalyticContinuationAlong.inv`, whose hypothesis is that the value carried at each
time is nonzero; nonvanishing at the initial time alone will not do, since a germ may continue to a
vanishing germ.

Both statements need the continuation itself, not just its initial germ, since the values along the
way are what the hypotheses speak about. At the germ level they therefore appear only in the case
that dispenses with those hypotheses, post-composition with an *entire* function
(`TauCeti.ContinuesAlong.postcomp`, `TauCeti.ContinuesInside.postcomp`).

Finally, continuation is a property of the path only up to **reparametrisation**
(`TauCeti.IsAnalyticContinuationAlong.reparam`, `TauCeti.ContinuesAlong.reparam`): precomposing
with a continuous map of parameters, injective or not, transports a continuation to the
reparametrised path, restriction to a smaller parameter set
(`TauCeti.IsAnalyticContinuationAlong.mono`) being the case of the identity.

## Relation to the monodromy theorem

This is the L4 prerequisite that the monodromy theorem of the conformal-mapping roadmap needs:
uniqueness of the continuation along a *fixed* path. The monodromy theorem itself compares
continuations along *homotopic* paths, and in the étale-space picture is an instance of Mathlib's
abstract `IsLocalHomeomorph.monodromy_theorem` (`Mathlib/Topology/Homotopy/Lifting.lean`), whose
docstring describes exactly this application; the uniqueness proved here is the concrete form of
the separatedness hypothesis that abstract theorem consumes. Building the étale space of
holomorphic germs and deducing monodromy from it is left to a follow-up.

## Main definitions and results

* `TauCeti.IsAnalyticContinuationAlong` — `f` is an analytic continuation along `γ` over the
  parameter set `s`.
* `TauCeti.IsAnalyticContinuationAlong.const`, `.of_differentiableOn` — a holomorphic function
  continues itself along any path in its domain.
* `TauCeti.IsAnalyticContinuationAlong.congr` — only the carried germs matter.
* `TauCeti.IsAnalyticContinuationAlong.deriv`, `.add`, `.mul`, `.neg`, `.sub`, `.pow`, `.inv`,
  `.div` — continuations are closed under the germ-wise operations, the last two under the
  hypothesis that no zero value is carried.
* `TauCeti.IsAnalyticContinuationAlong.continuousOn_apply` — the values a continuation carries
  trace out a continuous path.
* `TauCeti.IsAnalyticContinuationAlong.comp` — **substitution**: a continuation along the value
  path of another composes with it; `TauCeti.IsAnalyticContinuationAlong.postcomp` is the case of
  a single analytic outer function.
* `TauCeti.IsAnalyticContinuationAlong.reparam` — **reparametrisation invariance**, of which
  `TauCeti.IsAnalyticContinuationAlong.mono` is the identity case.
* `TauCeti.IsAnalyticContinuationAlong.eventuallyEq` — **uniqueness**: a continuation over a
  preconnected parameter set is determined by its germ at a single time.
* `TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_mapsTo` — continuing a holomorphic function
  along a path that stays inside its domain gives that function back.
* `TauCeti.ContinuesAlong`, `TauCeti.ContinuesInside` — continuability of a germ along one path,
  and along every path inside a domain. Neither body is exposed; downstream files use them through
  `TauCeti.continuesAlong_iff_exists`, `TauCeti.ContinuesInside.continuesAlong` and
  `TauCeti.ContinuesInside.of_forall`.
* `TauCeti.ContinuesAlong.add`, `.mul`, `.neg`, `.sub`, `.pow`, `.deriv` and their
  `TauCeti.ContinuesInside` counterparts — continuability of a germ is inherited by sums, products,
  differences, powers and derivatives.
* `TauCeti.ContinuesAlong.postcomp` and `TauCeti.ContinuesInside.postcomp` — and by composition
  with an entire function.
* `TauCeti.ContinuesAlong.reparam` — continuability along a path depends on the path only up to
  reparametrisation.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
* W. Rudin, *Real and Complex Analysis*, Ch. 16.
-/

public section

namespace TauCeti

open Filter Metric Topology

variable {X : Type*} [TopologicalSpace X] {f g : X → ℂ → ℂ} {γ : X → ℂ} {s : Set X}

/-! ### Germ agreement is a locally constant property -/

/-- Two functions analytic on a ball whose germs agree at one point of the ball have equal germs
at every point of the ball. This is the identity principle in germ form: the ball is preconnected,
so agreement near one of its points propagates to all of it, and the ball is open, so agreement on
it is agreement near each of its points. -/
theorem eventuallyEq_nhds_of_analyticOnNhd_ball {F G : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball c r)) (hG : AnalyticOnNhd ℂ G (ball c r)) {z w : ℂ}
    (hz : z ∈ ball c r) (hw : w ∈ ball c r) (h : F =ᶠ[𝓝 z] G) :
    F =ᶠ[𝓝 w] G :=
  eventually_of_mem (isOpen_ball.mem_nhds hw)
    (hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_ball c r).isPreconnected hz h)

/-- **Germ agreement is locally constant.** If `F` and `G` are both analytic at `z`, then for all
`w` near `z` the germs of `F` and `G` agree at `w` exactly when they agree at `z`. -/
theorem eventually_eventuallyEq_iff_of_analyticAt {F G : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (hG : AnalyticAt ℂ G z) :
    ∀ᶠ w in 𝓝 z, ((F =ᶠ[𝓝 w] G) ↔ (F =ᶠ[𝓝 z] G)) := by
  obtain ⟨r₁, hr₁, hF'⟩ := hF.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hG'⟩ := hG.exists_ball_analyticOnNhd
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hFr : AnalyticOnNhd ℂ F (ball z (min r₁ r₂)) :=
    hF'.mono (ball_subset_ball (min_le_left _ _))
  have hGr : AnalyticOnNhd ℂ G (ball z (min r₁ r₂)) :=
    hG'.mono (ball_subset_ball (min_le_right _ _))
  have hz : z ∈ ball z (min r₁ r₂) := mem_ball_self hr
  filter_upwards [ball_mem_nhds z hr] with w hw
  exact ⟨fun h => eventuallyEq_nhds_of_analyticOnNhd_ball hFr hGr hw hz h,
    fun h => eventuallyEq_nhds_of_analyticOnNhd_ball hFr hGr hz hw h⟩

/-- A property that is locally constant along a preconnected set is constant along it.

This is `IsLocallyConstant.apply_eq_of_preconnectedSpace` transported to the subspace `s`; it is
kept private because the general-topology statement belongs upstream rather than in a
complex-analysis file. -/
private theorem eq_of_isPreconnected_of_eventually_iff (hs : IsPreconnected s) {P : X → Prop}
    (hP : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, (P u ↔ P t)) {a b : X} (ha : a ∈ s) (hb : b ∈ s) (hPa : P a) :
    P b := by
  have hlc : IsLocallyConstant fun x : s => P x.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t, ht⟩
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.Eventually.comap ((hP t ht).mono fun _ hu => propext hu) _
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  rw [hlc.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨a, ha⟩]
  exact hPa

/-! ### Analytic continuation along a path -/

/-- `IsAnalyticContinuationAlong f γ s` says that the family `f` is an **analytic continuation
along the path `γ`** over the parameter set `s`: for each parameter time `t ∈ s` the function `f t`
is analytic at the point `γ t`, and the germ carried at time `t` is locally constant in `t`, in the
sense that `f u` and `f t` have the same germ at `γ u` for every `u ∈ s` close enough to `t`.

Only the germ of `f t` at `γ t` matters; the values of `f t` away from `γ t` are unconstrained.
Reading the germs as points of the étale space of holomorphic germs over `ℂ`, the condition says
precisely that `t ↦ (germ of f t at γ t)` is a continuous lift of `γ`. -/
structure IsAnalyticContinuationAlong (f : X → ℂ → ℂ) (γ : X → ℂ) (s : Set X) : Prop where
  /-- The path is continuous on the parameter set. -/
  continuousOn : ContinuousOn γ s
  /-- At each parameter time the carried function is analytic at the corresponding path point. -/
  analyticAt : ∀ t ∈ s, AnalyticAt ℂ (f t) (γ t)
  /-- The carried germ varies continuously: nearby parameter times carry the same germ. -/
  locallyEq : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, f u =ᶠ[𝓝 (γ u)] f t

namespace IsAnalyticContinuationAlong

/-- **Continuation is invariant under reparametrisation of the path.** Precomposing both the
family and the path with a continuous map `φ` of parameters again gives a continuation, along the
reparametrised path `γ ∘ φ`.

Nothing is asked of `φ` beyond continuity — it need not be injective, surjective or monotone — so
this covers restriction (`TauCeti.IsAnalyticContinuationAlong.mono`, the case `φ = id`),
reversal of a path, and the passage between the parameter conventions `X = ℝ` with `s = Icc 0 1`
and `X = unitInterval` with `s = univ` that this file's two layers use. The germ carried at a
reparametrised time is by construction the germ carried at the original time, so no uniqueness
argument is needed: the conclusion is about the *same* family, read along `φ`. -/
theorem reparam {Y : Type*} [TopologicalSpace Y] {φ : Y → X} {s' : Set Y}
    (hf : IsAnalyticContinuationAlong f γ s) (hφ : ContinuousOn φ s')
    (hmaps : Set.MapsTo φ s' s) :
    IsAnalyticContinuationAlong (f ∘ φ) (γ ∘ φ) s' where
  continuousOn := hf.continuousOn.comp hφ hmaps
  analyticAt t ht := hf.analyticAt (φ t) (hmaps ht)
  locallyEq t ht :=
    ((hφ t ht).tendsto_nhdsWithin hmaps).eventually (hf.locallyEq (φ t) (hmaps ht))

/-- A continuation restricts to any smaller parameter set: the case `φ = id` of
`TauCeti.IsAnalyticContinuationAlong.reparam`. -/
theorem mono (hf : IsAnalyticContinuationAlong f γ s) {s' : Set X} (hs' : s' ⊆ s) :
    IsAnalyticContinuationAlong f γ s' :=
  hf.reparam (φ := id) continuousOn_id hs'

/-- The constant family is a continuation: a function analytic at every point of the path
continues itself along it. -/
theorem const {F : ℂ → ℂ} (hγ : ContinuousOn γ s) (hF : ∀ t ∈ s, AnalyticAt ℂ F (γ t)) :
    IsAnalyticContinuationAlong (fun _ => F) γ s where
  continuousOn := hγ
  analyticAt := hF
  locallyEq _ _ := .of_forall fun _ => .rfl

/-- A holomorphic function on an open set continues itself along any path that stays in that
set. This is the source of the continuations that a single-valued function admits. -/
theorem of_differentiableOn {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hγ : ContinuousOn γ s) (hmem : ∀ t ∈ s, γ t ∈ U) :
    IsAnalyticContinuationAlong (fun _ => F) γ s :=
  const hγ fun t ht => hF.analyticOnNhd hU _ (hmem t ht)

/-- **A continuation depends only on the germs it carries.** Replacing each `f t` by a function
with the same germ at `γ t` again gives a continuation along `γ`. -/
protected theorem congr (hf : IsAnalyticContinuationAlong f γ s) {f' : X → ℂ → ℂ}
    (h : ∀ t ∈ s, f' t =ᶠ[𝓝 (γ t)] f t) : IsAnalyticContinuationAlong f' γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).congr (h t ht).symm
  locallyEq t ht := by
    have hball := eventually_eventuallyEq_iff_of_analyticAt
      ((hf.analyticAt t ht).congr (h t ht).symm) (hf.analyticAt t ht)
    filter_upwards [(hf.continuousOn t ht).eventually hball, hf.locallyEq t ht,
      self_mem_nhdsWithin] with u hiff hfu hu
    exact ((h u hu).trans hfu).trans (hiff.mpr (h t ht)).symm

/-- Differentiating a continuation term by term gives a continuation of the derivative germ. -/
protected theorem deriv (hf : IsAnalyticContinuationAlong f γ s) :
    IsAnalyticContinuationAlong (fun t => _root_.deriv (f t)) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).deriv
  locallyEq t ht := (hf.locallyEq t ht).mono fun _ hu => hu.deriv

/-- Continuations add: the pointwise sum family `f + g` continues along `γ` as well. -/
protected theorem add (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) :
    IsAnalyticContinuationAlong (f + g) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).add (hg.analyticAt t ht)
  locallyEq t ht := by
    filter_upwards [hf.locallyEq t ht, hg.locallyEq t ht] with u hu hu' using hu.add hu'

/-- Continuations multiply: the pointwise product family `f * g` continues along `γ` as well. -/
protected theorem mul (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) :
    IsAnalyticContinuationAlong (f * g) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).mul (hg.analyticAt t ht)
  locallyEq t ht := by
    filter_upwards [hf.locallyEq t ht, hg.locallyEq t ht] with u hu hu' using hu.mul hu'

/-- Continuations negate: the pointwise negation family `-f` continues along `γ` as well. -/
protected theorem neg (hf : IsAnalyticContinuationAlong f γ s) :
    IsAnalyticContinuationAlong (-f) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).neg
  locallyEq t ht := (hf.locallyEq t ht).mono fun _ hu => hu.neg

/-- Continuations subtract: the pointwise difference family `f - g` continues along `γ` as
well. -/
protected theorem sub (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) :
    IsAnalyticContinuationAlong (f - g) γ s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Continuations take powers: the pointwise power family `f ^ n` continues along `γ` as well. -/
protected theorem pow (hf : IsAnalyticContinuationAlong f γ s) (n : ℕ) :
    IsAnalyticContinuationAlong (f ^ n) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).pow n
  locallyEq t ht := (hf.locallyEq t ht).mono fun _ hu => hu.pow_const n

/-- **The reciprocal of a nowhere-vanishing continuation continues.** The hypothesis is that the
*value carried at each time*, `f t (γ t)`, is nonzero; nothing is asked of `f t` away from `γ t`,
which the germ `(f t)⁻¹` does not see either.

The condition cannot be weakened to nonvanishing at the initial time alone: a germ may continue to
a germ that vanishes — `z ↦ z` continued along a path through `0` is the standard example — and
there the reciprocal germ has a pole rather than a continuation. -/
protected theorem inv (hf : IsAnalyticContinuationAlong f γ s) (hne : ∀ t ∈ s, f t (γ t) ≠ 0) :
    IsAnalyticContinuationAlong f⁻¹ γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).inv (hne t ht)
  locallyEq t ht := (hf.locallyEq t ht).mono fun _ hu => hu.inv

/-- Continuations divide, provided the denominator carries no zero value. -/
protected theorem div (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) (hne : ∀ t ∈ s, g t (γ t) ≠ 0) :
    IsAnalyticContinuationAlong (f / g) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).div (hg.analyticAt t ht) (hne t ht)
  locallyEq t ht := by
    filter_upwards [hf.locallyEq t ht, hg.locallyEq t ht] with u hu hu' using hu.div hu'

/-! ### Composition -/

/-- **The value carried by a continuation is continuous in the parameter.** The germs themselves
vary only "locally constantly", but their values at the moving point `γ t` trace out an honest
continuous path `t ↦ f t (γ t)` — the path along which an outer germ is to be continued when two
continuations are composed.

The proof is the one-line consequence of the two clauses of the definition: near `t` the family is
constant as a germ, so `f u (γ u) = f t (γ u)`, and the right-hand side is continuous because the
single function `f t` is analytic, hence continuous, at `γ t`. -/
theorem continuousOn_apply (hf : IsAnalyticContinuationAlong f γ s) :
    ContinuousOn (fun t => f t (γ t)) s := by
  intro t₀ ht₀
  have hval : (fun u => f t₀ (γ u)) =ᶠ[𝓝[s] t₀] fun u => f u (γ u) := by
    filter_upwards [hf.locallyEq t₀ ht₀] with u hu using hu.eq_of_nhds.symm
  exact Filter.Tendsto.congr' hval
    ((hf.analyticAt t₀ ht₀).continuousAt.comp_continuousWithinAt (hf.continuousOn t₀ ht₀))

/-- **Continuations compose.** If `f` continues a germ along `γ` and `g` continues a germ along the
path `t ↦ f t (γ t)` traced out by the values of `f`, then the composites `g t ∘ f t` continue the
composite germ along `γ`.

This is the closure rule that the ring operations do not reach, and it is what lets a germ built
by substitution be continued by continuing its two constituents separately. The inner path is
forced: it is the value path of `f`, which is continuous by
`TauCeti.IsAnalyticContinuationAlong.continuousOn_apply`.

Germ agreement propagates through the composite because `f u` is continuous at `γ u`: the points
`f u z` for `z` near `γ u` are near `f u (γ u)`, which is where `g u` and `g t` are known to have
the same germ. -/
protected theorem comp {g : X → ℂ → ℂ}
    (hg : IsAnalyticContinuationAlong g (fun t => f t (γ t)) s)
    (hf : IsAnalyticContinuationAlong f γ s) :
    IsAnalyticContinuationAlong (fun t => g t ∘ f t) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hg.analyticAt t ht).comp (hf.analyticAt t ht)
  locallyEq t ht := by
    filter_upwards [hf.locallyEq t ht, hg.locallyEq t ht, self_mem_nhdsWithin] with u hfu hgu hu
    have houter : ∀ᶠ z in 𝓝 (γ u), g u (f u z) = g t (f u z) :=
      Filter.Tendsto.eventually (hf.analyticAt u hu).continuousAt hgu
    filter_upwards [hfu, houter] with z hz hz'
    rw [Function.comp_apply, Function.comp_apply, hz', hz]

/-- **Post-composing a continuation with a single analytic function.** If `F` is analytic at every
value `f t (γ t)` carried by a continuation — for an entire `F` that is automatic — then the
family `F ∘ f t` is a continuation along the same path.

This is `TauCeti.IsAnalyticContinuationAlong.comp` against the constant outer family, which is a
continuation along the value path by
`TauCeti.IsAnalyticContinuationAlong.continuousOn_apply`. -/
theorem postcomp {F : ℂ → ℂ} (hf : IsAnalyticContinuationAlong f γ s)
    (hF : ∀ t ∈ s, AnalyticAt ℂ F (f t (γ t))) :
    IsAnalyticContinuationAlong (fun t => F ∘ f t) γ s :=
  (IsAnalyticContinuationAlong.const hf.continuousOn_apply hF).comp hf

/-! ### Uniqueness -/

/-- Agreement of two continuations along the same path is a locally constant property of the
parameter. This is the local step of the uniqueness theorem. -/
theorem eventually_eventuallyEq_iff (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) {t : X} (ht : t ∈ s) :
    ∀ᶠ u in 𝓝[s] t, ((f u =ᶠ[𝓝 (γ u)] g u) ↔ (f t =ᶠ[𝓝 (γ t)] g t)) := by
  have hball := eventually_eventuallyEq_iff_of_analyticAt (hf.analyticAt t ht) (hg.analyticAt t ht)
  filter_upwards [(hf.continuousOn t ht).eventually hball, hf.locallyEq t ht, hg.locallyEq t ht]
    with u hiff hfu hgu
  exact ⟨fun h => hiff.mp (hfu.symm.trans (h.trans hgu)),
    fun h => hfu.trans ((hiff.mpr h).trans hgu.symm)⟩

/-- **Uniqueness of analytic continuation along a path.** Two analytic continuations along the same
path, over a preconnected parameter set, that carry the same germ at one parameter time carry the
same germ at every parameter time.

Preconnectedness of the parameter set cannot be dropped: over a two-point parameter set the
hypotheses put no relation at all between the germs carried at its two points. -/
theorem eventuallyEq (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) (hab : f a =ᶠ[𝓝 (γ a)] g a) :
    f b =ᶠ[𝓝 (γ b)] g b :=
  eq_of_isPreconnected_of_eventually_iff hs
    (P := fun t => f t =ᶠ[𝓝 (γ t)] g t) (fun _ ht => hf.eventually_eventuallyEq_iff hg ht) ha hb
    hab

/-- Two continuations along the same path that carry the same germ at one parameter time take the
same value at every parameter time. -/
theorem eq_of_eventuallyEq (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) (hab : f a =ᶠ[𝓝 (γ a)] g a) :
    f b (γ b) = g b (γ b) :=
  (hf.eventuallyEq hg hs ha hb hab).eq_of_nhds

/-- **A single-valued function is its own continuation.** If a path stays inside an open set on
which `F` is holomorphic, then any continuation along that path which starts at the germ of `F`
carries the germ of `F` throughout. So continuing a holomorphic function inside its domain never
produces a new branch: new branches can only appear once the path leaves the domain. -/
theorem eventuallyEq_of_mapsTo {U : Set ℂ} {F : ℂ → ℂ} (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsPreconnected s) (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hmem : ∀ t ∈ s, γ t ∈ U) {a b : X} (ha : a ∈ s) (hb : b ∈ s) (hab : f a =ᶠ[𝓝 (γ a)] F) :
    f b =ᶠ[𝓝 (γ b)] F :=
  hf.eventuallyEq (of_differentiableOn hU hF hf.continuousOn hmem) hs ha hb hab

end IsAnalyticContinuationAlong

section Germ

open unitInterval

variable {U : Set ℂ} {z₀ : ℂ} {f₀ g₀ : ℂ → ℂ} {c : I → ℂ}

/-! ### Continuation along a path, as a property of the initial germ -/

/-- The germ of `f₀` at `c 0` **continues along the path `c`**: there is an analytic continuation
along `c` whose germ at the initial time is that of `f₀`.

Only the germ of `f₀` at `c 0` enters, so this is a property of that germ rather than of `f₀`
(`TauCeti.continuesAlong_congr`). -/
def ContinuesAlong (f₀ : ℂ → ℂ) (c : I → ℂ) : Prop :=
  ∃ f : I → ℂ → ℂ, IsAnalyticContinuationAlong f c Set.univ ∧ f 0 =ᶠ[𝓝 (c 0)] f₀

/-- **The defining property of `TauCeti.ContinuesAlong`**: a germ continues along `c` exactly when
some analytic continuation along `c` starts at it. This is the introduction and elimination rule
for the predicate, whose body is not exposed. -/
theorem continuesAlong_iff_exists :
    ContinuesAlong f₀ c ↔
      ∃ f : I → ℂ → ℂ, IsAnalyticContinuationAlong f c Set.univ ∧ f 0 =ᶠ[𝓝 (c 0)] f₀ :=
  Iff.rfl

namespace ContinuesAlong

/-- A germ that continues along a path is a germ of an analytic function at the initial point. -/
theorem analyticAt (h : ContinuesAlong f₀ c) : AnalyticAt ℂ f₀ (c 0) := by
  obtain ⟨f, hf, h0⟩ := h
  exact (hf.analyticAt 0 (Set.mem_univ 0)).congr h0

/-- **Continuability along a path depends only on the initial germ.** -/
protected theorem congr (h : ContinuesAlong f₀ c) (hfg : f₀ =ᶠ[𝓝 (c 0)] g₀) :
    ContinuesAlong g₀ c :=
  let ⟨f, hf, h0⟩ := h
  ⟨f, hf, h0.trans hfg⟩

/-- A function analytic at every point of a path continues itself along it: the constant family is
the continuation. -/
theorem of_analyticAt (hc : Continuous c) (hf₀ : ∀ x, AnalyticAt ℂ f₀ (c x)) :
    ContinuesAlong f₀ c :=
  ⟨fun _ => f₀, .const hc.continuousOn fun t _ => hf₀ t, .rfl⟩

/-- A function holomorphic on an open set continues along every path that stays in that set. -/
theorem of_differentiableOn (hUo : IsOpen U) (hf₀ : DifferentiableOn ℂ f₀ U) (hc : Continuous c)
    (hcU : ∀ x, c x ∈ U) : ContinuesAlong f₀ c :=
  of_analyticAt hc fun x => hf₀.analyticOnNhd hUo _ (hcU x)

/-! #### Closure under the germ-wise operations

Continuing two germs along one path and combining the results is the same as combining first and
continuing after: the operations act on the carried germs time by time
(`TauCeti.IsAnalyticContinuationAlong.add` and its companions), so a continuation of the combination
is obtained from continuations of the parts, with no new choices to make. -/

/-- The sum of two germs that continue along a path continues along it. -/
protected theorem add (h : ContinuesAlong f₀ c) (h' : ContinuesAlong g₀ c) :
    ContinuesAlong (f₀ + g₀) c :=
  let ⟨f, hf, hf0⟩ := h
  let ⟨g, hg, hg0⟩ := h'
  ⟨f + g, hf.add hg, hf0.add hg0⟩

/-- The product of two germs that continue along a path continues along it. -/
protected theorem mul (h : ContinuesAlong f₀ c) (h' : ContinuesAlong g₀ c) :
    ContinuesAlong (f₀ * g₀) c :=
  let ⟨f, hf, hf0⟩ := h
  let ⟨g, hg, hg0⟩ := h'
  ⟨f * g, hf.mul hg, hf0.mul hg0⟩

/-- The negation of a germ that continues along a path continues along it. -/
protected theorem neg (h : ContinuesAlong f₀ c) : ContinuesAlong (-f₀) c :=
  let ⟨f, hf, hf0⟩ := h
  ⟨-f, hf.neg, hf0.neg⟩

/-- The difference of two germs that continue along a path continues along it. -/
protected theorem sub (h : ContinuesAlong f₀ c) (h' : ContinuesAlong g₀ c) :
    ContinuesAlong (f₀ - g₀) c := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

/-- A power of a germ that continues along a path continues along it. -/
protected theorem pow (h : ContinuesAlong f₀ c) (n : ℕ) : ContinuesAlong (f₀ ^ n) c :=
  let ⟨f, hf, hf0⟩ := h
  ⟨f ^ n, hf.pow n, hf0.pow_const n⟩

/-- The derivative of a germ that continues along a path continues along it. -/
protected theorem deriv (h : ContinuesAlong f₀ c) : ContinuesAlong (_root_.deriv f₀) c :=
  let ⟨f, hf, hf0⟩ := h
  ⟨fun t => _root_.deriv (f t), hf.deriv, hf0.deriv⟩

/-- **Post-composing with an entire function preserves continuability.** If the germ of `f₀`
continues along `c` and `F` is analytic everywhere, then the germ of `F ∘ f₀` continues along `c`.

Analyticity of `F` on all of `ℂ` is what makes this a statement about the germ of `f₀` alone: for
an `F` analytic only on a proper open subset the hypothesis one would need — that the continuation
of `f₀` keeps its values inside that subset — is not readable off `f₀`, and the statement belongs
at the level of `TauCeti.IsAnalyticContinuationAlong.postcomp`, where the continuation is named.
Taking `F` to be `Complex.exp`, a polynomial, or `Complex.sin` are the typical uses. -/
theorem postcomp (h : ContinuesAlong f₀ c) {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z) :
    ContinuesAlong (F ∘ f₀) c :=
  let ⟨f, hf, hf0⟩ := h
  ⟨fun t => F ∘ f t, hf.postcomp fun _ _ => hF _, hf0.fun_comp F⟩

/-- **Continuability along a path is invariant under reparametrisation.** A germ that continues
along `c` continues along `c ∘ φ` for every continuous `φ : I → I` fixing the initial time.

Fixing `φ 0 = 0` is what keeps the *initial* germ the one being continued; without it the
reparametrised path starts somewhere else, and the statement is
`TauCeti.IsAnalyticContinuationAlong.reparam` instead. -/
theorem reparam (h : ContinuesAlong f₀ c) {φ : I → I} (hφ : Continuous φ) (hφ0 : φ 0 = 0) :
    ContinuesAlong f₀ (c ∘ φ) :=
  let ⟨f, hf, hf0⟩ := h
  ⟨f ∘ φ, hf.reparam hφ.continuousOn (Set.mapsTo_univ _ _), by
    simpa only [Function.comp_apply, hφ0] using hf0⟩

end ContinuesAlong

/-- Continuability along a path is a property of the germ of `f₀` at the initial point. -/
theorem continuesAlong_congr (h : f₀ =ᶠ[𝓝 (c 0)] g₀) : ContinuesAlong f₀ c ↔ ContinuesAlong g₀ c :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

/-! ### Continuation inside a domain -/

/-- The germ of `f₀` at `z₀` **continues inside `U`**: it continues along every path that starts
at `z₀` and stays in `U`.

This is the hypothesis of the monodromy theorem. It is a condition on the germ
(`TauCeti.continuesInside_congr`) and on the domain jointly: the germ of `Complex.log` at `1`
continues inside `ℂ \ {0}`, and continues inside the slit plane, but is single-valued only on the
latter. -/
def ContinuesInside (f₀ : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) : Prop :=
  ∀ c : I → ℂ, Continuous c → (∀ x, c x ∈ U) → c 0 = z₀ → ContinuesAlong f₀ c

namespace ContinuesInside

/-- **Elimination for `TauCeti.ContinuesInside`**: a germ that continues inside `U` continues
along each individual path that starts at `z₀` and stays in `U`. -/
theorem continuesAlong (H : ContinuesInside f₀ U z₀) (hc : Continuous c) (hcU : ∀ x, c x ∈ U)
    (hc0 : c 0 = z₀) : ContinuesAlong f₀ c :=
  H c hc hcU hc0

/-- **Introduction for `TauCeti.ContinuesInside`**: a germ that continues along every path
starting at `z₀` and staying in `U` continues inside `U`. -/
theorem of_forall
    (h : ∀ c : I → ℂ, Continuous c → (∀ x, c x ∈ U) → c 0 = z₀ → ContinuesAlong f₀ c) :
    ContinuesInside f₀ U z₀ :=
  h

/-- A germ that continues inside `U` is analytic at the base point, as witnessed by the constant
path. -/
theorem analyticAt (H : ContinuesInside f₀ U z₀) (hz₀ : z₀ ∈ U) : AnalyticAt ℂ f₀ z₀ :=
  (H.continuesAlong (c := fun _ => z₀) continuous_const (fun _ => hz₀) rfl).analyticAt

/-- **Continuability inside a domain depends only on the germ at the base point.** -/
protected theorem congr (H : ContinuesInside f₀ U z₀) (hfg : f₀ =ᶠ[𝓝 z₀] g₀) :
    ContinuesInside g₀ U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).congr (hc0 ▸ hfg)

/-- A function holomorphic on an open set continues inside that set from each of its points. -/
theorem of_differentiableOn (hUo : IsOpen U) (hf₀ : DifferentiableOn ℂ f₀ U) :
    ContinuesInside f₀ U z₀ :=
  of_forall fun _ hc hcU _ => .of_differentiableOn hUo hf₀ hc hcU

/-! #### Closure under the germ-wise operations

Continuability inside `U` is continuability along each path of `U` at once, so it inherits the
closure properties of `TauCeti.ContinuesAlong` path by path. Read through the monodromy theorem for
a simply connected domain (`Conformal/GlobalBranch.lean`), these are the statements that a germ
assembled from germs extending to `U` extends to `U` itself. -/

/-- The sum of two germs that continue inside a domain continues inside it. -/
protected theorem add (H : ContinuesInside f₀ U z₀) (H' : ContinuesInside g₀ U z₀) :
    ContinuesInside (f₀ + g₀) U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).add (H'.continuesAlong hc hcU hc0)

/-- The product of two germs that continue inside a domain continues inside it. -/
protected theorem mul (H : ContinuesInside f₀ U z₀) (H' : ContinuesInside g₀ U z₀) :
    ContinuesInside (f₀ * g₀) U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).mul (H'.continuesAlong hc hcU hc0)

/-- The negation of a germ that continues inside a domain continues inside it. -/
protected theorem neg (H : ContinuesInside f₀ U z₀) : ContinuesInside (-f₀) U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).neg

/-- The difference of two germs that continue inside a domain continues inside it. -/
protected theorem sub (H : ContinuesInside f₀ U z₀) (H' : ContinuesInside g₀ U z₀) :
    ContinuesInside (f₀ - g₀) U z₀ := by
  simpa only [sub_eq_add_neg] using H.add H'.neg

/-- A power of a germ that continues inside a domain continues inside it. -/
protected theorem pow (H : ContinuesInside f₀ U z₀) (n : ℕ) : ContinuesInside (f₀ ^ n) U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).pow n

/-- **The derivative of a germ that continues inside a domain continues inside it.** If `U` is open
and simply connected and contains `z₀`, the derivative therefore has a branch of its own on `U`
(`TauCeti.ContinuesInside.exists_analyticOnNhd`). -/
protected theorem deriv (H : ContinuesInside f₀ U z₀) : ContinuesInside (_root_.deriv f₀) U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).deriv

/-- **An entire function applied to a germ that continues inside a domain continues inside it.**
Composed with the monodromy theorem for a simply connected domain
(`TauCeti.ContinuesInside.exists_analyticOnNhd`), this says that `F ∘ f₀` has a branch on `U`
whenever `f₀` has one — the substitution instance of the closure properties above. -/
theorem postcomp (H : ContinuesInside f₀ U z₀) {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z) :
    ContinuesInside (F ∘ f₀) U z₀ :=
  of_forall fun _ hc hcU hc0 => (H.continuesAlong hc hcU hc0).postcomp hF

end ContinuesInside

/-- Continuability inside `U` is a property of the germ of `f₀` at the base point. -/
theorem continuesInside_congr (h : f₀ =ᶠ[𝓝 z₀] g₀) :
    ContinuesInside f₀ U z₀ ↔ ContinuesInside g₀ U z₀ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

end Germ

end TauCeti
