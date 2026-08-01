/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.Complex.Conformal.Rouche
public import TauCeti.Analysis.Complex.IsolatedZero
public import TauCeti.Analysis.Complex.ZeroCount
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Hurwitz's theorem

Hurwitz's theorem describes how the zeros of a locally uniform limit of holomorphic functions
relate to the zeros of the approximants, and it does so in both directions. The limit acquires no
new zeros — a limit of nowhere-vanishing functions is nowhere vanishing or identically zero — and
it loses none either: every zero of the limit is approached by zeros of the approximants. This is
the second target of layer **L0 (the local-mapping engine)** of the conformal-mapping roadmap, and
the perturbation backbone for the injectivity step of the Riemann mapping theorem.

Both directions come from one Rouché estimate, isolated here as
`TauCeti.eventually_finsum_analyticOrderNatAt_ball_eq`. Fix a disc whose closure lies in `Ω` and on
whose bounding circle the limit `g` does not vanish. Then `‖g‖` has a positive minimum `δ` on that
circle by compactness, and locally uniform convergence eventually forces `‖g - F i‖ < δ ≤ ‖g‖`
there — exactly Rouché's hypothesis. So *eventually the zero counts of `F i` and of `g` inside the
disc agree*, an equality of natural numbers from which both halves of Hurwitz's theorem are read
off by looking at one side or the other:

* the count of `g` is `0` whenever the `F i` are zero-free, and a function whose count vanishes on
  every such disc has no zeros at all;
* the count of `g` is positive at an isolated zero of `g`, so the count of `F i` is too, and `F i`
  has a zero in a disc that can be taken as small as one likes.

The second reading needs the zero of `g` to be isolated, which is why the *identically zero*
alternative is unavoidable and why `Ω` is assumed connected: it is the identity theorem that turns
"`g` is not constantly `v`" into "`g ≠ v` on a punctured neighbourhood of each point".

Everything is stated for an arbitrary value `v`, not only for `v = 0`: applying the above to
`g - v` costs nothing and gives the statement actually used downstream — a value omitted by the
`F i` is omitted by the limit unless the limit is constantly that value. Specialising to `v = 0`
recovers the classical phrasing `TauCeti.hurwitz`.

Throughout, every hypothesis on the family — holomorphy, omitting a value, injectivity — is
assumed only *eventually along `l`*: it holds on some index set belonging to `l`, not on every
index. Along a sequence that reads "for all sufficiently large `i`", the phrasing the docstrings
below use; for a general filter it says only that the indices where the hypothesis fails are
excluded by a member of `l`, whose complement need not be finite. That is the form limit arguments
produce and consume, and it costs nothing: the conclusions are eventual along `l` as well, so
indices outside a set of `l` never enter.

The corollary usually quoted alongside is the injectivity form: a locally uniform limit of
*injective* holomorphic functions is injective or constant. That is the version the Riemann mapping
theorem consumes. It is proved from the value form rather than by applying `TauCeti.hurwitz` to the
differences `F i - F i b` on the punctured domain `Ω \ {b}`, since that route needs the punctured
set to be connected — a fact Mathlib does not currently supply for an open connected subset of `ℂ`.

## Main results

* `TauCeti.eventually_finsum_analyticOrderNatAt_ball_eq` — **Hurwitz's theorem, counting form**:
  on a disc whose bounding circle avoids the zeros of the limit, the approximants eventually have
  the same number of zeros as the limit, counted with multiplicity.
* `TauCeti.hurwitz_eventually_exists_eq` — **zeros of the limit are limits of zeros**: if `g` is
  not constantly `v` and `g z₀ = v`, then every neighbourhood of `z₀` eventually contains a point
  where `F i` takes the value `v`.
* `TauCeti.hurwitz_eventually_exists_eq_zero` — the same for `v = 0`.
* `TauCeti.hurwitz_forall_ne` — a value omitted by the `F i` is omitted by a limit that is not
  constantly that value.
* `TauCeti.hurwitz_forall_ne_or_forall_eq` — the dichotomy form of the previous statement.
* `TauCeti.hurwitz` — a locally uniform limit of nowhere-vanishing holomorphic functions on a
  connected open set is nowhere vanishing or identically zero.
* `TauCeti.hurwitz_injOn` — a locally uniform limit of injective holomorphic functions is injective
  or constant.

## Coordination with upstream Mathlib

Mathlib has no Hurwitz theorem. However, per the *Coordination with upstream Mathlib* section of
`ConformalMapping/README.md`, this layer overlaps
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which proves this material internally as the private
lemmas `eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn` and
`eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`. **This file is therefore a temporary shim**:
once the corresponding Mathlib lemmas land, these statements should be backed by them — or deleted
and their consumers refactored — rather than maintained as independent re-proofs. What Tau Ceti
adds at L0 is named, discoverable API, not first proof.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII.
-/

public section

open Complex Metric Filter Topology

namespace TauCeti

variable {ι : Type*} {l : Filter ι} {Ω : Set ℂ} {F : ι → ℂ → ℂ} {g : ℂ → ℂ}

/-- **A small disc on which `v` is attained only at the centre.** If `g` avoids `v` on some
punctured neighbourhood of `z₀ ∈ Ω` with `Ω` open — the value at `z₀` itself is unconstrained —
then there are arbitrarily small radii whose *closed* ball lies in `Ω` and on which `v` is taken
nowhere but possibly at `z₀`. Rouché's theorem is applied to the bounding circle of such a
ball. -/
private lemma exists_radius_forall_ne (hΩ : IsOpen Ω) {v z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hpunct : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r ≤ ε ∧ closedBall z₀ r ⊆ Ω ∧ ∀ z ∈ closedBall z₀ r, z ≠ z₀ → g z ≠ v := by
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ Ω ∧ (z ≠ z₀ → g z ≠ v) :=
    (hΩ.eventually_mem hz₀).and (eventually_nhdsWithin_iff.mp hpunct)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  have hmono : closedBall z₀ (min r ε) ⊆ closedBall z₀ r :=
    closedBall_subset_closedBall (min_le_left _ _)
  exact ⟨min r ε, lt_min hr hε, min_le_right _ _, fun z hz => (hball (hmono hz)).1,
    fun z hz => (hball (hmono hz)).2⟩

/-- **An analytic function on a preconnected set attains a value it does not attain identically
only in isolation.** If `g` is analytic on `Ω` and is not constantly `v` there, then `g z ≠ v` on
a punctured neighbourhood of any `x ∈ Ω`. -/
private theorem eventually_ne_of_not_forall_eq (hconn : IsPreconnected Ω)
    (hgA : AnalyticOnNhd ℂ g Ω) {v : ℂ} (hnc : ¬ ∀ z ∈ Ω, g z = v)
    {x : ℂ} (hx : x ∈ Ω) : ∀ᶠ z in 𝓝[≠] x, g z ≠ v := by
  rcases (hgA x hx).eventually_eq_or_eventually_ne (analyticAt_const (v := v)) with h | h
  · exact absurd (fun z hz =>
      hgA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hx h hz) hnc
  · exact h

/-- **Hurwitz's theorem, counting form.** Let `g` and — for all sufficiently large `i` — the `F i`
be analytic on a closed disc `closedBall c r` of positive radius, let `F i → g` uniformly on the
bounding circle `sphere c r`, and let `g` not vanish on that circle. Then for all sufficiently
large `i`, `F i` has exactly as many zeros in `ball c r` as `g` does, counted with multiplicity.

This is Rouché's theorem `TauCeti.rouche` applied along the filter: the bound `δ ≤ ‖g‖` on the
compact circle, from `TauCeti.exists_pos_le_norm_of_mem_sphere`, is eventually beaten by the
uniform error `‖g - F i‖` there. Nothing about an ambient domain enters, so a locally uniform
limit on an open `Ω` feeds this lemma through
`tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact` on any disc with
`closedBall c r ⊆ Ω`, which is how both halves of Hurwitz's theorem below use it.

Those two halves are readings of this one equality, so the hypothesis on the circle is the only
genuine constraint: some circle must separate the zero being tracked from the rest of the zero
set, and that is exactly what the identity theorem provides when `g` is not locally constant. -/
theorem eventually_finsum_analyticOrderNatAt_ball_eq {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) (closedBall c r))
    (hconv : TendstoUniformlyOn F g l (sphere c r))
    (hne : ∀ z ∈ sphere c r, g z ≠ 0) :
    ∀ᶠ i in l, (∑ᶠ z ∈ ball c r, analyticOrderNatAt (F i) z)
      = ∑ᶠ z ∈ ball c r, analyticOrderNatAt g z := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_mem_sphere
    (hg.continuousOn.mono sphere_subset_closedBall) hne
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv _ hδ, hF] with i hi hFi
  exact (rouche hr hg hFi fun z hz =>
    lt_of_lt_of_le (by simpa [dist_eq_norm] using hi z hz) (hδle z hz)).symm

/-- **Hurwitz's theorem: zeros of the limit are limits of zeros.** If `g` is the locally uniform
limit on a connected open `Ω` of functions `F i` that are holomorphic for all sufficiently large
`i`, is not identically zero, and vanishes at `z₀ ∈ Ω`, then every ball about `z₀` contains a zero
of `F i` for all sufficiently large `i`.

The hypothesis that `g` is not identically zero cannot be dropped: for `ι = ℕ` and `l = atTop`,
the constant functions `F n z = 1 / (n + 1 : ℂ)` are holomorphic and nowhere zero and converge
locally uniformly to `g = 0`, which vanishes at every `z₀`, yet no `F n` has a zero anywhere.

Note that the ball is *not* assumed to lie in `Ω`; the zero produced is located in `Ω ∩ ball z₀ ε`,
which the proof reaches by shrinking `ε` first. -/
theorem hurwitz_eventually_exists_eq_zero [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hgz₀ : g z₀ = 0) (hnc : ¬ ∀ z ∈ Ω, g z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ z ∈ Ω ∩ ball z₀ ε, F i z = 0 := by
  have hgA : AnalyticOnNhd ℂ g Ω :=
    (_root_.TendstoLocallyUniformlyOn.differentiableOn hconv hF hΩ).analyticOnNhd hΩ
  obtain ⟨r, hr, hrε, hball, hzf⟩ :=
    exists_radius_forall_ne hΩ hz₀ (eventually_ne_of_not_forall_eq hconn hgA hnc hz₀) hε
  have hsphne : ∀ z ∈ sphere z₀ r, g z ≠ 0 := fun z hz =>
    hzf z (sphere_subset_closedBall hz) (Metric.ne_of_mem_sphere hz hr.ne')
  have hFA : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) (closedBall z₀ r) :=
    hF.mono fun i hi => (hi.analyticOnNhd hΩ).mono hball
  have hconvS : TendstoUniformlyOn F g l (sphere z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z₀ r)).mp
      (hconv.mono (sphere_subset_closedBall.trans hball))
  -- `g` vanishes at the centre but not on the bounding circle, so its count is nonzero
  have hcount : (∑ᶠ z ∈ ball z₀ r, analyticOrderNatAt g z) ≠ 0 := fun h =>
    (finsum_analyticOrderNatAt_ball_eq_zero_iff (hgA.mono hball)
        (exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero hr.le hsphne)).mp h z₀
      (mem_ball_self hr) hgz₀
  filter_upwards [eventually_finsum_analyticOrderNatAt_ball_eq hr (hgA.mono hball) hFA hconvS
    hsphne, hF] with i hi hFi
  by_contra hcon
  push Not at hcon
  refine hcount (hi ▸ finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero
    ((hFi.analyticOnNhd hΩ).mono (ball_subset_closedBall.trans hball)) fun z hz => ?_)
  exact hcon z ⟨hball (ball_subset_closedBall hz), ball_subset_ball hrε hz⟩

/-- **Hurwitz's theorem: values of the limit are limits of values.** If `g` is the locally uniform
limit on a connected open `Ω` of functions `F i` that are holomorphic for all sufficiently large
`i`, is not constantly `v`, and takes the value `v` at `z₀ ∈ Ω`, then every ball about `z₀`
contains a point where `F i` takes the value `v`, again for all sufficiently large `i`.

This is `TauCeti.hurwitz_eventually_exists_eq_zero` applied to the translated family `F i - v`,
which converges locally uniformly to `g - v`. It is the form the injectivity corollary consumes:
two disjoint balls about two points where `g` takes the same value eventually both contain points
where `F i` takes that value, contradicting injectivity of `F i`. -/
theorem hurwitz_eventually_exists_eq [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    {v z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hgz₀ : g z₀ = v) (hnc : ¬ ∀ z ∈ Ω, g z = v)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ z ∈ Ω ∩ ball z₀ ε, F i z = v := by
  have hconst : TendstoLocallyUniformlyOn (fun (_ : ι) (_ : ℂ) => v) (fun _ => v) l Ω :=
    (tendsto_const_nhds.tendstoUniformlyOn_const Ω).tendstoLocallyUniformlyOn
  have hzero := hurwitz_eventually_exists_eq_zero (F := fun i z => F i z - v)
    (g := fun z => g z - v) hΩ hconn (hF.mono fun i hi => hi.sub_const v) (hconv.sub hconst)
    hz₀ (by simp [hgz₀]) (fun h => hnc fun z hz => sub_eq_zero.mp (h z hz)) hε
  filter_upwards [hzero] with i hi
  obtain ⟨z, hz, hz0⟩ := hi
  exact ⟨z, hz, sub_eq_zero.mp hz0⟩

/-- **Hurwitz's theorem for an omitted value.** If `F i` is holomorphic on `Ω` and avoids the value
`v` there for all sufficiently large `i`, and the locally uniform limit `g` is not constantly `v`,
then `g` avoids `v` as well.

Contrapositive of `TauCeti.hurwitz_eventually_exists_eq`: a point where `g` took the value `v`
would force `F i` to take it too. -/
theorem hurwitz_forall_ne [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω) {v : ℂ}
    (hne : ∀ᶠ i in l, ∀ z ∈ Ω, F i z ≠ v) (hnc : ¬ ∀ z ∈ Ω, g z = v) :
    ∀ z ∈ Ω, g z ≠ v := by
  intro z₀ hz₀ hgz₀
  obtain ⟨i, ⟨z, hz, hzv⟩, hnei⟩ :=
    ((hurwitz_eventually_exists_eq hΩ hconn hF hconv hz₀ hgz₀ hnc one_pos).and hne).exists
  exact hnei z hz.1 hzv

/-- **Hurwitz's theorem for an omitted value**, dichotomy form. On a connected open set, a locally
uniform limit of functions that are holomorphic and avoid the value `v` for all sufficiently large
`i` either avoids `v` everywhere or is constantly `v`.

The dichotomy is genuine: for `ι = ℕ` and `l = atTop`, the functions `F n z = v + 1 / (n + 1 : ℂ)`
avoid `v` on any `Ω` and converge locally uniformly to the constant `v`. -/
theorem hurwitz_forall_ne_or_forall_eq [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω) {v : ℂ}
    (hne : ∀ᶠ i in l, ∀ z ∈ Ω, F i z ≠ v) :
    (∀ z ∈ Ω, g z ≠ v) ∨ (∀ z ∈ Ω, g z = v) := by
  by_cases hnc : ∀ z ∈ Ω, g z = v
  · exact Or.inr hnc
  · exact Or.inl (hurwitz_forall_ne hΩ hconn hF hconv hne hnc)

/-- **Hurwitz's theorem.** On a connected open set, a locally uniform limit of functions that are
holomorphic and nowhere zero for all sufficiently large `i` is itself either nowhere zero or
identically zero.

This is the value `v = 0` of `TauCeti.hurwitz_forall_ne_or_forall_eq`. The dichotomy is genuine:
for `ι = ℕ` and `l = atTop`, the constant functions `F n z = 1 / (n + 1 : ℂ)` on any `Ω` converge
locally uniformly to `0`, so the second alternative cannot be dropped. -/
theorem hurwitz [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    (hne : ∀ᶠ i in l, ∀ z ∈ Ω, F i z ≠ 0) :
    (∀ z ∈ Ω, g z ≠ 0) ∨ (∀ z ∈ Ω, g z = 0) :=
  hurwitz_forall_ne_or_forall_eq hΩ hconn hF hconv hne

/-- **Hurwitz's theorem for injectivity.** On a connected open set, a locally uniform limit of
functions that are holomorphic and *injective* for all sufficiently large `i` is either injective
or constant.

This is the form the Riemann mapping theorem consumes: it is what keeps the extremal map injective
in the limit. Both alternatives genuinely occur — for `ι = ℕ` and `l = atTop`, the injective maps
`F n z = z / (n + 1 : ℂ)` converge locally uniformly to the constant `0`.

The proof does not route through `TauCeti.hurwitz` on the punctured domain `Ω \ {b}`, which would
need that set to be connected — a fact Mathlib does not currently provide for an open connected
subset of `ℂ`. Instead, if `g` were non-constant with `g a = g b` for `a ≠ b`, then
`TauCeti.hurwitz_eventually_exists_eq` places a point where `F i` takes the single value `g a`
within `dist a b / 3` of each of `a` and `b`; the triangle inequality separates those two points,
contradicting injectivity of `F i`. -/
theorem hurwitz_injOn [l.NeBot] (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    (hinj : ∀ᶠ i in l, Set.InjOn (F i) Ω) :
    Set.InjOn g Ω ∨ ∃ v, ∀ z ∈ Ω, g z = v := by
  by_cases hconst : ∃ v, ∀ z ∈ Ω, g z = v
  · exact Or.inr hconst
  refine Or.inl fun a ha b hb hab => ?_
  by_contra hne
  have hd : 0 < dist a b / 3 := by have := dist_pos.mpr hne; linarith
  have hnc : ¬ ∀ z ∈ Ω, g z = g a := fun h => hconst ⟨g a, h⟩
  obtain ⟨i, ⟨⟨z₁, hz₁, hFz₁⟩, ⟨z₂, hz₂, hFz₂⟩⟩, hinji⟩ :=
    (((hurwitz_eventually_exists_eq hΩ hconn hF hconv ha rfl hnc hd).and
      (hurwitz_eventually_exists_eq hΩ hconn hF hconv hb hab.symm hnc hd)).and hinj).exists
  have hz₁₂ : z₁ ≠ z₂ := by
    rintro rfl
    have h1 : dist a z₁ < dist a b / 3 := by rw [dist_comm]; exact mem_ball.mp hz₁.2
    have h2 : dist z₁ b < dist a b / 3 := mem_ball.mp hz₂.2
    have h3 := dist_triangle a z₁ b
    linarith
  exact hz₁₂ (hinji hz₁.1 hz₂.1 (hFz₁.trans hFz₂.symm))

end TauCeti
