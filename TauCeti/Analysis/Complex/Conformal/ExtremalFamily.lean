module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.Complex.Conformal.DiscInjection
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.Complex.Conformal.Hurwitz
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.Montel
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Order.IsLUB

/-!
# The extremal problem of the Riemann mapping theorem

The Riemann mapping theorem is proved by solving an extremal problem: among all holomorphic
injections of a domain `Ω` into the unit disc that send a chosen base point `z₀` to the origin,
maximize `‖deriv · z₀‖`. This file introduces that competing family and shows the maximum is
**attained**.

The sibling file `DiscInjection.lean` supplies the family's nonemptiness; this file supplies
compactness. Together they set up the Koebe square-root argument, which shows that a maximizer
cannot omit a value — that step is not in this file.

## The argument

Cauchy's estimate on a closed ball inside `Ω` bounds `‖deriv f z₀‖` by `1 / r` uniformly over the
family, so the supremum `M` is finite; it is positive because the family is nonempty and an
injective holomorphic map has nonvanishing derivative. Along a maximizing sequence, Montel's
selection theorem extracts a locally uniformly convergent subsequence. Its limit `g` inherits every
defining property:

* holomorphy, from Montel;
* `g z₀ = 0` and `‖deriv g z₀‖ = M`, by passing to the limit pointwise — the derivatives converge
  locally uniformly too, by the Weierstrass convergence theorem;
* injectivity, from Hurwitz's theorem for injectivity (`TauCeti.hurwitz_injOn`); the competing
  alternative, that `g` is constant, is excluded because `‖deriv g z₀‖ = M > 0`;
* mapping into the **open** disc. This is the one property that does not pass to the limit for
  free: a locally uniform limit of maps into `ball 0 1` a priori only lands in `closedBall 0 1`.
  A boundary value would make `‖g‖` attain an interior maximum, so the maximum modulus principle
  would force `‖g‖ ≡ 1` on `Ω`, contradicting `g z₀ = 0`.

## Attribution and upstream coordination

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. The declarations here are an explicitly
**temporary shim**: delete them and refactor downstream consumers onto the exported Mathlib
versions once those land.

## Main statements

* `TauCeti.IsPointedDiscInjectionOn` — membership in the competing family.
* `TauCeti.exists_isPointedDiscInjectionOn` — the family is nonempty.
* `TauCeti.exists_isMaxOn_norm_deriv` — the extremal problem has a solution, given one competitor.
* `TauCeti.exists_isMaxOn_norm_deriv_of_isSimplyConnected` — the form used by the Riemann mapping
  theorem, where simple connectivity supplies that competitor.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §4.
-/

public section

namespace TauCeti

open Complex Set Metric Filter Topology

variable {Ω : Set ℂ} {f g : ℂ → ℂ} {z₀ : ℂ}

/-- A **pointed disc injection** on `Ω` at the base point `z₀`: a holomorphic injection of `Ω`
into the open unit disc sending `z₀` to the origin. It is the pointed form of the maps produced by
`TauCeti.exists_differentiableOn_injOn_mapsTo_unitBall` in `DiscInjection.lean`.

Such maps are classically called *schlicht*, the traditional name for an injective holomorphic map;
the name here deliberately avoids *normalized*, which conventionally demands the further
normalization `deriv f z₀ = 1` that this predicate does not impose.

This is the competing family of the Riemann mapping theorem's extremal problem: the theorem is
proved by maximizing `‖deriv f z₀‖` over all such `f`. -/
structure IsPointedDiscInjectionOn (f : ℂ → ℂ) (Ω : Set ℂ) (z₀ : ℂ) : Prop where
  /-- A pointed disc injection is holomorphic on `Ω`. -/
  differentiableOn : DifferentiableOn ℂ f Ω
  /-- A pointed disc injection takes `Ω` into the open unit disc. -/
  mapsTo : MapsTo f Ω (ball (0 : ℂ) 1)
  /-- A pointed disc injection is injective on `Ω`. -/
  injOn : InjOn f Ω
  /-- A pointed disc injection sends the base point to the origin. -/
  map_base : f z₀ = 0

namespace IsPointedDiscInjectionOn

/-- A pointed disc injection is bounded by `1`, since it lands in the unit disc. -/
theorem norm_le_one (hf : IsPointedDiscInjectionOn f Ω z₀) {z : ℂ} (hz : z ∈ Ω) : ‖f z‖ ≤ 1 :=
  (mem_ball_zero_iff.mp (hf.mapsTo hz)).le

/-- A pointed disc injection has nonvanishing derivative throughout `Ω`: it is injective on a
neighbourhood of each point, which by the local injectivity criterion forces `deriv f z ≠ 0`. -/
theorem deriv_ne_zero (hf : IsPointedDiscInjectionOn f Ω z₀) (hΩo : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    deriv f z ≠ 0 :=
  (exists_injOn_nhds_iff_deriv_ne_zero
    (hf.differentiableOn.analyticOnNhd hΩo z hz)).mp ⟨Ω, hΩo.mem_nhds hz, hf.injOn⟩

end IsPointedDiscInjectionOn

/-- **The competing family is nonempty.** Every base point of a nonempty, simply connected, open,
proper subset of `ℂ` admits a pointed disc injection.

This repackages `TauCeti.exists_differentiableOn_injOn_mapsTo_unitBall_apply_eq_zero`. -/
theorem exists_isPointedDiscInjectionOn (hΩc : IsSimplyConnected Ω) (hΩo : IsOpen Ω)
    (hΩne : Ω ≠ univ) (hz₀ : z₀ ∈ Ω) :
    ∃ f : ℂ → ℂ, IsPointedDiscInjectionOn f Ω z₀ := by
  obtain ⟨f, hfd, hfi, hfm, hf₀⟩ :=
    exists_differentiableOn_injOn_mapsTo_unitBall_apply_eq_zero hΩc hΩo hΩne hz₀
  exact ⟨f, hfd, hfm, hfi, hf₀⟩

/-- Cauchy's estimate bounds the derivatives at the base point uniformly over the family: on a
closed ball of radius `r` inside `Ω`, every member is bounded by `1`, hence its derivative at the
centre is bounded by `1 / r`. -/
private theorem bddAbove_norm_deriv (hΩo : IsOpen Ω) (hz₀ : z₀ ∈ Ω) :
    BddAbove ((fun f : ℂ → ℂ => ‖deriv f z₀‖) '' {f | IsPointedDiscInjectionOn f Ω z₀}) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩo z₀ hz₀
  have hsub : closedBall z₀ (ε / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hball
  refine ⟨1 / (ε / 2), ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact norm_deriv_le_of_forall_mem_closedBall_norm_le hf.differentiableOn (by linarith) hsub
    fun w hw => hf.norm_le_one (hsub hw)

/-- A function constant on an open set has vanishing derivative there. -/
private theorem deriv_eq_zero_of_forall_eq (hΩo : IsOpen Ω) {v z : ℂ} (hz : z ∈ Ω)
    (h : ∀ w ∈ Ω, g w = v) : deriv g z = 0 := by
  have hev : g =ᶠ[𝓝 z] fun _ => v := eventually_nhds_iff.mpr ⟨Ω, h, hΩo, hz⟩
  rw [hev.deriv_eq, deriv_const]

/-- A holomorphic map bounded by `1` on a preconnected open set, vanishing somewhere, maps into the
**open** unit disc. A boundary value would be an interior maximum of `‖g‖`, and the maximum modulus
principle would then force `‖g‖` to be constantly `1`, contradicting the vanishing. -/
private theorem mapsTo_ball_of_forall_norm_le_one (hΩo : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hgd : DifferentiableOn ℂ g Ω) (hle : ∀ z ∈ Ω, ‖g z‖ ≤ 1) (hz₀ : z₀ ∈ Ω) (hg₀ : g z₀ = 0) :
    MapsTo g Ω (ball (0 : ℂ) 1) := by
  intro z hz
  rw [mem_ball_zero_iff]
  rcases lt_or_eq_of_le (hle z hz) with hlt | heq
  · exact hlt
  · exfalso
    have hmax : IsMaxOn (norm ∘ g) Ω z := fun w hw => by
      simpa [Function.comp_def, heq] using hle w hw
    have hconst := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hconn hΩo hgd hz hmax hz₀
    simp only [Function.comp_def, hg₀, norm_zero] at hconst
    exact one_ne_zero (heq.symm.trans hconst.symm)

/-- **The extremal problem has a solution.** If the competing family at a base point `z₀` of an
open preconnected set `Ω` is nonempty, then some member maximizes `‖deriv · z₀‖` over the whole
family.

The compactness argument needs nothing beyond these hypotheses: preconnectedness for the maximum
modulus principle and for Hurwitz's theorem, and one competitor to make the supremum positive.
Simple connectivity enters only through
`TauCeti.exists_isPointedDiscInjectionOn`, which supplies that competitor; see the corollary
`TauCeti.exists_isMaxOn_norm_deriv_of_isSimplyConnected`.

This is the compactness half of the Riemann mapping theorem. It does **not** assert that the
maximizer is surjective; that is the Koebe square-root argument, proved elsewhere. -/
theorem exists_isMaxOn_norm_deriv (hΩo : IsOpen Ω) (hconn : IsPreconnected Ω) (hz₀ : z₀ ∈ Ω)
    (hne : ∃ f : ℂ → ℂ, IsPointedDiscInjectionOn f Ω z₀) :
    ∃ g : ℂ → ℂ, IsPointedDiscInjectionOn g Ω z₀ ∧
      ∀ f : ℂ → ℂ, IsPointedDiscInjectionOn f Ω z₀ → ‖deriv f z₀‖ ≤ ‖deriv g z₀‖ := by
  classical
  obtain ⟨f₀, hf₀⟩ := hne
  have hbdd := bddAbove_norm_deriv hΩo hz₀ (Ω := Ω)
  have hSne : ((fun f : ℂ → ℂ => ‖deriv f z₀‖) '' {f | IsPointedDiscInjectionOn f Ω z₀}).Nonempty :=
    ⟨_, ⟨f₀, hf₀, rfl⟩⟩
  -- The supremum of the derivative norms is positive: `f₀` already contributes a nonzero value.
  have hM₀ : 0 < sSup ((fun f : ℂ → ℂ => ‖deriv f z₀‖) '' {f | IsPointedDiscInjectionOn f Ω z₀}) :=
    lt_of_lt_of_le (norm_pos_iff.mpr (hf₀.deriv_ne_zero hΩo hz₀)) (le_csSup hbdd ⟨f₀, hf₀, rfl⟩)
  -- A maximizing sequence, indexed by `ℕ` as Montel's theorem requires.
  obtain ⟨u, -, hu_tendsto, hu_mem⟩ := exists_seq_tendsto_sSup hSne hbdd
  simp only [Set.mem_image, Set.mem_setOf_eq] at hu_mem
  choose F hF hFu using hu_mem
  have hb : IsLocallyBoundedOn F Ω :=
    isLocallyBoundedOn_of_forall_norm_le fun n z hz => (hF n).norm_le_one hz
  obtain ⟨φ, g, hφ, hgd, hconv⟩ := montel hΩo (fun n => (hF n).differentiableOn) hb
  -- The limit fixes the base point.
  have hg₀ : g z₀ = 0 := by
    have h1 : Tendsto (fun n => F (φ n) z₀) atTop (𝓝 (g z₀)) := hconv.tendsto_at hz₀
    rw [funext fun n => (hF (φ n)).map_base] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- The limit is bounded by `1`, hence lands in the open disc.
  have hle : ∀ z ∈ Ω, ‖g z‖ ≤ 1 := fun z hz =>
    le_of_tendsto (hconv.tendsto_at hz).norm
      (Eventually.of_forall fun n => (hF (φ n)).norm_le_one hz)
  have hgm : MapsTo g Ω (ball (0 : ℂ) 1) :=
    mapsTo_ball_of_forall_norm_le_one hΩo hconn hgd hle hz₀ hg₀
  -- The derivatives converge locally uniformly, so the supremum is attained at the limit.
  have hderiv : TendstoLocallyUniformlyOn (fun n => deriv (F (φ n))) (deriv g) atTop Ω := by
    have h := _root_.TendstoLocallyUniformlyOn.deriv hconv
      (Eventually.of_forall fun n => (hF (φ n)).differentiableOn) hΩo
    simpa [Function.comp_def] using h
  have hMg : ‖deriv g z₀‖ =
      sSup ((fun f : ℂ → ℂ => ‖deriv f z₀‖) '' {f | IsPointedDiscInjectionOn f Ω z₀}) := by
    refine tendsto_nhds_unique (hderiv.tendsto_at hz₀).norm ?_
    simpa [Function.comp_def, hFu] using hu_tendsto.comp hφ.tendsto_atTop
  -- Injectivity survives by Hurwitz; the constant alternative is excluded by positivity.
  have hgi : InjOn g Ω := by
    rcases hurwitz_injOn hΩo hconn (Eventually.of_forall fun n => (hF (φ n)).differentiableOn)
      hconv (Eventually.of_forall fun n => (hF (φ n)).injOn) with hinj | ⟨v, hv⟩
    · exact hinj
    · exfalso
      rw [deriv_eq_zero_of_forall_eq hΩo hz₀ hv, norm_zero] at hMg
      exact hM₀.ne hMg
  exact ⟨g, ⟨hgd, hgm, hgi, hg₀⟩, fun f hf => hMg ▸ le_csSup hbdd ⟨f, hf, rfl⟩⟩

/-- **The extremal problem has a solution on a simply connected proper subdomain.** This is the
form the Riemann mapping theorem uses: on a nonempty, simply connected, open, proper subset `Ω` of
`ℂ` with base point `z₀`, some pointed disc injection maximizes `‖deriv · z₀‖`.

Simple connectivity and properness serve only to produce one competitor; the compactness argument
itself is `TauCeti.exists_isMaxOn_norm_deriv`. -/
theorem exists_isMaxOn_norm_deriv_of_isSimplyConnected (hΩc : IsSimplyConnected Ω) (hΩo : IsOpen Ω)
    (hΩne : Ω ≠ univ) (hz₀ : z₀ ∈ Ω) :
    ∃ g : ℂ → ℂ, IsPointedDiscInjectionOn g Ω z₀ ∧
      ∀ f : ℂ → ℂ, IsPointedDiscInjectionOn f Ω z₀ → ‖deriv f z₀‖ ≤ ‖deriv g z₀‖ :=
  exists_isMaxOn_norm_deriv hΩo hΩc.isPathConnected.isConnected.isPreconnected hz₀
    (exists_isPointedDiscInjectionOn hΩc hΩo hΩne hz₀)

end TauCeti
