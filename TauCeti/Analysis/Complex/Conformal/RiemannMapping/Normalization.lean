/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Complex.Conformal.Koebe
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Uniqueness
public import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Isometry

/-!
# The normalized Riemann map

The Riemann mapping theorem of `RiemannMapping/Existence.lean` produces *some* biholomorphism of a
simply connected proper domain onto the unit disc, and `RiemannMapping/Uniqueness.lean` shows any
two such maps differ by a disc automorphism. Neither statement singles out a map. This file adds
the classical normalization that does: fixing a base point `z₀ ∈ Ω`, there is exactly one
biholomorphism `Ω → 𝔻` with

`f z₀ = 0` and `deriv f z₀ > 0`,

the second condition being an inequality in the scoped order `ComplexOrder` on `ℂ`, so that it says
precisely that `deriv f z₀` is a *positive real number*. With `Ω` and `z₀` fixed, this pins the
Riemann map down on `Ω`: the maps here are total functions `ℂ → ℂ`, whose values off `Ω` no
condition constrains, and what is proved is that any two normalized maps agree *on* `Ω` — that is,
that the biholomorphism `Ω → 𝔻` they restrict to is unique.

## The argument

Both halves reduce to the existing ones by a rotation.

* **Existence.** The extremal map of `ExtremalFamily.lean` is already a bijection onto the disc
  sending `z₀` to `0` (`Koebe.lean` supplies the surjectivity), and its derivative `c` at `z₀` is
  nonzero. Multiplying it by the unimodular constant `‖c‖ / c` leaves both of those properties
  intact — rotations preserve the disc — and turns the derivative at `z₀` into `‖c‖ > 0`.
* **Uniqueness.** Two normalized maps differ by a rotation `u` of the disc by
  `TauCeti.exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero`. Differentiating at `z₀` gives
  `deriv g z₀ = u * deriv f z₀` with both derivatives positive reals of the same modulus, so `u = 1`
  and the two maps agree on `Ω`.

## A note on "normalized"

`TauCeti.IsPointedDiscInjectionOn` in `ExtremalFamily.lean` deliberately avoids the word
*normalized*, reserving it for the schlicht-function normalization `deriv f z₀ = 1`. The
normalization used here is the other classical one, the *Riemann-map* normalization
`f z₀ = 0`, `deriv f z₀ > 0` of Ahlfors, Ch. 6 §1: it is the one that is achievable for every
domain, since the size of `deriv f z₀` is not free once the image is required to be the unit disc.

## Main statements

* `TauCeti.IsNormalizedRiemannMapOn` — the normalization, as a predicate.
* `TauCeti.exists_isNormalizedRiemannMapOn` — existence of the normalized Riemann map.
* `TauCeti.IsNormalizedRiemannMapOn.eqOn` — uniqueness: two normalized maps agree on the domain.
* `TauCeti.riemannMapping_normalized` — the two combined.
* `TauCeti.eqOn_id_of_isNormalizedRiemannMapOn_ball` — the normalized Riemann map of the disc at
  the origin is the identity.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. As with the rest of this development's L0–L3
material, the declarations here are an explicitly **temporary shim**: delete them and refactor
downstream consumers onto the exported Mathlib versions once those land.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §4.
-/

public section

namespace TauCeti

open _root_.Complex Filter Metric Set
open scoped ComplexOrder Topology

variable {Ω : Set ℂ} {f g : ℂ → ℂ} {z₀ : ℂ}

/-- Multiplying by a unimodular constant preserves a bijection onto a ball about the origin:
rotations of the ball are bijections of it. Neither the domain nor the radius plays any role, so
this is stated for an arbitrary source set and an arbitrary radius. -/
private theorem bijOn_ball_const_mul {α : Type*} {s : Set α} {F : α → ℂ} {r : ℝ} {u : ℂ}
    (hu : ‖u‖ = 1) (hF : BijOn F s (ball (0 : ℂ) r)) :
    BijOn (fun z => u * F z) s (ball (0 : ℂ) r) := by
  -- Multiplication by `u` is the rotation `rotation ⟨u, hu⟩`, a linear isometry equivalence of `ℂ`
  -- fixing `0`, so it carries the ball about the origin bijectively onto itself.
  have hrot : BijOn (fun w : ℂ => u * w) (ball (0 : ℂ) r) (ball (0 : ℂ) r) := by
    have h := (rotation ⟨u, mem_sphere_zero_iff_norm.mpr hu⟩).injective.injOn.bijOn_image
      (s := ball (0 : ℂ) r)
    rwa [LinearIsometryEquiv.image_ball, map_zero] at h
  exact hrot.comp hF

/-- A unimodular constant carrying one positive real to another is `1`: the modulus forces the two
positive reals to be equal, and cancelling them leaves `u = 1`. This is the rigidity behind the
uniqueness of the normalized Riemann map. -/
private theorem eq_one_of_norm_eq_one_of_mul_pos {u a b : ℂ} (hu : ‖u‖ = 1) (ha : 0 < a)
    (hb : 0 < b) (hab : u * a = b) : u = 1 := by
  have hnorm : ‖b‖ = ‖a‖ := by rw [← hab, norm_mul, hu, one_mul]
  have hab' : b = a := by
    refine Complex.ext ?_ ?_
    · rw [← Complex.re_eq_norm.mpr hb.le, ← Complex.re_eq_norm.mpr ha.le] at hnorm
      exact hnorm
    · rw [← (Complex.pos_iff.mp hb).2, ← (Complex.pos_iff.mp ha).2]
  rw [hab'] at hab
  exact mul_right_cancel₀ ha.ne' (by rw [hab, one_mul])

/-- A **normalized Riemann map** of a domain `Ω` at a base point `z₀ ∈ Ω`: a holomorphic bijection
of `Ω` onto the open unit disc that sends `z₀` to the origin and has a *positive real* derivative
there.

The order on `deriv f z₀` is the scoped `ComplexOrder` one, so `0 < deriv f z₀` unfolds to
`0 < (deriv f z₀).re ∧ 0 = (deriv f z₀).im`.

This normalization is what makes the Riemann map unique: `TauCeti.riemannMapping` produces a map
only up to a disc automorphism, whereas by `TauCeti.riemannMapping_normalized` any two functions
satisfying the predicate below agree on `Ω`. Uniqueness can only be uniqueness on `Ω`, since the
predicate says nothing about the values of `f` outside `Ω`. -/
structure IsNormalizedRiemannMapOn (f : ℂ → ℂ) (Ω : Set ℂ) (z₀ : ℂ) : Prop where
  /-- The base point of a normalized Riemann map lies in its domain, so that the conditions at the
  base point really do constrain the map on `Ω`. -/
  base_mem : z₀ ∈ Ω
  /-- A normalized Riemann map is holomorphic on its domain. -/
  differentiableOn : DifferentiableOn ℂ f Ω
  /-- A normalized Riemann map is a bijection of its domain onto the open unit disc. -/
  bijOn : BijOn f Ω (ball (0 : ℂ) 1)
  /-- A normalized Riemann map sends the base point to the origin. -/
  map_base : f z₀ = 0
  /-- A normalized Riemann map has positive real derivative at the base point. -/
  deriv_pos : 0 < deriv f z₀

namespace IsNormalizedRiemannMapOn

variable (hf : IsNormalizedRiemannMapOn f Ω z₀)
include hf

theorem mapsTo : MapsTo f Ω (ball (0 : ℂ) 1) := hf.bijOn.mapsTo

theorem injOn : InjOn f Ω := hf.bijOn.injOn

theorem surjOn : SurjOn f Ω (ball (0 : ℂ) 1) := hf.bijOn.surjOn

theorem image_eq : f '' Ω = ball (0 : ℂ) 1 := hf.bijOn.image_eq

/-- A normalized Riemann map competes in the extremal family of `ExtremalFamily.lean`: it is a
holomorphic injection into the disc fixing the base point. -/
theorem isPointedDiscInjectionOn : IsPointedDiscInjectionOn f Ω z₀ :=
  ⟨hf.differentiableOn, hf.mapsTo, hf.injOn, hf.map_base⟩

theorem deriv_ne_zero_base : deriv f z₀ ≠ 0 := hf.deriv_pos.ne'

/-- The derivative of a normalized Riemann map at the base point is its own modulus. -/
theorem coe_norm_deriv : ((‖deriv f z₀‖ : ℝ) : ℂ) = deriv f z₀ := by
  have hre : (deriv f z₀).re = ‖deriv f z₀‖ := Complex.re_eq_norm.mpr hf.deriv_pos.le
  rw [← hre]
  exact (Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hf.deriv_pos.le)).symm

end IsNormalizedRiemannMapOn

/-- **Existence of the normalized Riemann map.** Every nonempty, simply connected, open, proper
subset `Ω` of `ℂ` carries, at each of its points `z₀`, a holomorphic bijection onto the open unit
disc sending `z₀` to `0` with positive real derivative there.

The extremal map of `TauCeti.exists_isMaxOn_norm_deriv_of_isSimplyConnected` already fixes the base
point and is onto by `TauCeti.surjOn_ball_of_isMaxOn`; only a rotation is needed to make its
derivative positive. -/
theorem exists_isNormalizedRiemannMapOn (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩ : Ω ≠ univ) (hz₀ : z₀ ∈ Ω) :
    ∃ f : ℂ → ℂ, IsNormalizedRiemannMapOn f Ω z₀ := by
  obtain ⟨g, hg, hmax⟩ := exists_isMaxOn_norm_deriv_of_isSimplyConnected hΩc hΩo hΩ hz₀
  have hbij : BijOn g Ω (ball (0 : ℂ) 1) :=
    ⟨hg.mapsTo, hg.injOn, surjOn_ball_of_isMaxOn hΩo hΩc hz₀ hg hmax⟩
  have hc : deriv g z₀ ≠ 0 := hg.deriv_ne_zero hΩo hz₀
  have hcpos : 0 < ‖deriv g z₀‖ := norm_pos_iff.mpr hc
  -- The rotation that turns `deriv g z₀` into its own modulus.
  set u : ℂ := ((‖deriv g z₀‖ : ℝ) : ℂ) / deriv g z₀ with hu_def
  have hnu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
      div_self hcpos.ne']
  refine ⟨fun z => u * g z, hz₀, hg.differentiableOn.const_mul u,
    bijOn_ball_const_mul hnu hbij, ?_, ?_⟩
  · rw [hg.map_base, mul_zero]
  · rw [deriv_const_mul_field, hu_def, div_mul_cancel₀ _ hc]
    exact Complex.zero_lt_real.mpr hcpos

/-- **Uniqueness of the normalized Riemann map.** Two normalized Riemann maps of the same domain at
the same base point agree on that domain.

Together with `TauCeti.exists_isNormalizedRiemannMapOn` this makes the normalized Riemann map a
genuinely well-defined function of `(Ω, z₀)` *on* `Ω`: what is determined is the restriction
`Ω → 𝔻`, not the values of a representative off `Ω`. Note that neither simple connectivity nor
properness of `Ω` is needed here: uniqueness holds wherever two such maps happen to exist. -/
theorem IsNormalizedRiemannMapOn.eqOn (hg : IsNormalizedRiemannMapOn g Ω z₀)
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) : EqOn g f Ω := by
  obtain ⟨u, hu⟩ :=
    exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero hΩo hf.differentiableOn
      hg.differentiableOn hf.injOn hg.injOn hf.image_eq hg.image_eq hf.base_mem hf.map_base
      hg.map_base
  -- The two maps agree near `z₀` up to the constant `u`, so their derivatives there do too.
  have hev : g =ᶠ[𝓝 z₀] fun z => (u : ℂ) * f z :=
    eventually_nhds_iff.mpr ⟨Ω, fun z hz => hu hz, hΩo, hf.base_mem⟩
  have hderiv : (u : ℂ) * deriv f z₀ = deriv g z₀ := by
    rw [hev.deriv_eq, deriv_const_mul_field]
  have hu1 : (u : ℂ) = 1 :=
    eq_one_of_norm_eq_one_of_mul_pos (Circle.norm_coe u) hf.deriv_pos hg.deriv_pos hderiv
  intro z hz
  have hz' := hu hz
  simpa only [hu1, one_mul] using hz'

/-- **The Riemann mapping theorem, normalized.** A nonempty, simply connected, open, proper subset
`Ω` of `ℂ` with a base point `z₀` carries a holomorphic bijection onto the open unit disc that
sends `z₀` to `0` with positive real derivative there, and that map is unique: any other one agrees
with it on `Ω`.

This is the pinned-down form of `TauCeti.riemannMapping`, which asserts existence only. -/
theorem riemannMapping_normalized (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ)
    (hz₀ : z₀ ∈ Ω) :
    ∃ f : ℂ → ℂ, IsNormalizedRiemannMapOn f Ω z₀ ∧
      ∀ g : ℂ → ℂ, IsNormalizedRiemannMapOn g Ω z₀ → EqOn g f Ω := by
  obtain ⟨f, hf⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hΩ hz₀
  exact ⟨f, hf, fun g hg => hg.eqOn hf hΩo⟩

/-- The identity is the normalized Riemann map of the unit disc at the origin. -/
theorem isNormalizedRiemannMapOn_id_ball : IsNormalizedRiemannMapOn id (ball (0 : ℂ) 1) 0 where
  base_mem := mem_ball_self one_pos
  differentiableOn := differentiable_id.differentiableOn
  bijOn := bijOn_id _
  map_base := rfl
  deriv_pos := by rw [deriv_id, Complex.lt_def]; norm_num

/-- **Rigidity of the disc.** A holomorphic bijection of the open unit disc onto itself that fixes
the origin and has positive real derivative there is the identity.

This strengthens `TauCeti.eqOn_id_of_leftInvOn_ball_of_map_zero_of_deriv_zero_eq_one`, which
assumes the derivative at the origin is exactly `1`: here it is only assumed to be a positive real,
and uniqueness of the normalized Riemann map supplies the rest. -/
theorem eqOn_id_of_isNormalizedRiemannMapOn_ball
    (hf : IsNormalizedRiemannMapOn f (ball (0 : ℂ) 1) 0) : EqOn f id (ball (0 : ℂ) 1) :=
  hf.eqOn isNormalizedRiemannMapOn_id_ball isOpen_ball

end TauCeti
