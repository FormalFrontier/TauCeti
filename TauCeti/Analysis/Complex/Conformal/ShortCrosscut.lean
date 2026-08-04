/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
public import TauCeti.Analysis.Complex.Conformal.LengthArea

/-!
# A circular crosscut with a short image

`Conformal/LengthArea.lean` proves Wolff's lemma — among the circles `‖z - ζ‖ = ρ` with
`r < ρ < R`, one has small `TauCeti.circleImageLength f s ζ ρ` — and the chord bound
`TauCeti.ofReal_dist_le_circleImageLength`, which controls the distance between the images of the
two endpoints of an *arc of angles*. It leaves open, in its own words, the step of "turning that
into a crosscut of small diameter at a boundary point". This file takes that step: it reads the
intersection `ball c r ∩ sphere ζ ρ` of the circle `sphere ζ ρ` with the disc — the **circular
crosscut** of `Conformal/Crosscut/Basic.lean` when `ρ < 2 * r`, and empty otherwise — as an arc of
angles, and concludes that its image under a conformal map has small diameter at suitable radii
`ρ`.

That is the first of the two geometric inputs
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` of
`Conformal/CutDiameter.lean` runs on, and hence of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's boundary correspondence. The second —
a small set `E` enclosing the boundary points of the image domain that cling to the piece the
crosscut cuts off — is a matter of local connectedness of that boundary and is not treated here.

## The intersection is an arc

Everything rests on the angular description of the intersection proved in
`Conformal/Crosscut/Basic.lean`. Writing `α = arg (c - ζ)` for the direction from the boundary
point `ζ` to the centre, `TauCeti.circleMap_mem_ball_iff` says that

> `circleMap ζ ρ θ ∈ ball c r ↔ ρ < 2 * r * cos (θ - α)`,

and `TauCeti.circleMap_mem_ball_of_mem_Icc` deduces that the condition holds throughout an interval
of angles inside the period centred at `α` as soon as it holds at both ends. Every point of the
circle `sphere ζ ρ` is `circleMap ζ ρ (α + t)` for some `t ∈ [-π, π]`, so any two points of the
intersection are the endpoints of such an interval, of width at most `2 * π`, along which the chord
bound applies.

## Main results

* `TauCeti.ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere` — the chord bound for
  `ball c r ∩ sphere ζ ρ`: any two of its points have images at distance at most
  `TauCeti.circleImageLength f (ball c r) ζ ρ`.
* `TauCeti.diam_image_ball_inter_sphere_le` — hence the image of `ball c r ∩ sphere ζ ρ` is no
  wider than that quantity.
* `TauCeti.exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top` — the conclusion, from
  Wolff's lemma: a holomorphic map of a disc with finite Dirichlet integral has, at every boundary
  point and below every positive radius, a radius `ρ` at which `f '' (ball c r ∩ sphere ζ ρ)` has
  diameter at most `ε`.
* `TauCeti.exists_diam_image_ball_inter_sphere_le` — its corollary for an injective map with
  bounded image, the case a Riemann map falls under.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The disc is a
general `ball c r` rather than the unit disc, since nothing is cheaper in the normalised case, and
the boundary point enters only through `dist ζ c = r`.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and
Mathlib has no boundary correspondence for conformal maps. So this file is new Lean formalization
rather than a temporary shim; it consumes no L0–L3 shim, its analytic inputs being the length–area
estimates of `Conformal/LengthArea.lean` and the area formula they rest on.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method, Wolff's
  lemma and crosscuts).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set
open scoped ENNReal Real

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The chord bound on a circular crosscut -/

/-- **The chord bound for a circular crosscut.** For `f` holomorphic on `ball c r` and `ζ` on the
circle `sphere c r`, any two points of `ball c r ∩ sphere ζ ρ` have images at distance at most
`TauCeti.circleImageLength f (ball c r) ζ ρ`.

The two points are `circleMap ζ ρ (α + t₁)` and `circleMap ζ ρ (α + t₂)` for angles
`t₁, t₂ ∈ [-π, π]` off the direction `α = arg (c - ζ)` of the centre; the arc of angles between
them has width at most `2 * π` and stays in the disc by
`TauCeti.circleMap_mem_ball_of_mem_Icc`, so `TauCeti.ofReal_dist_le_circleImageLength` applies to
it with `s = U = ball c r`. -/
theorem ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball c r)) {z w : ℂ} (hz : z ∈ ball c r ∩ sphere ζ ρ)
    (hw : w ∈ ball c r ∩ sphere ζ ρ) :
    ENNReal.ofReal (dist (f z) (f w)) ≤ circleImageLength f (ball c r) ζ ρ := by
  -- it suffices to treat a pair of angles in increasing order
  suffices h : ∀ z' w' : ℂ, z' ∈ ball c r ∩ sphere ζ ρ → w' ∈ ball c r ∩ sphere ζ ρ →
      ∀ t₁ ∈ Icc (-π) π, ∀ t₂ ∈ Icc (-π) π, t₁ ≤ t₂ →
      circleMap ζ ρ ((c - ζ).arg + t₁) = z' → circleMap ζ ρ ((c - ζ).arg + t₂) = w' →
      ENNReal.ofReal (dist (f z') (f w')) ≤ circleImageLength f (ball c r) ζ ρ by
    obtain ⟨t₁, ht₁, hz'⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hz.2
    obtain ⟨t₂, ht₂, hw'⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hw.2
    rcases le_total t₁ t₂ with hle | hle
    · exact h z w hz hw t₁ ht₁ t₂ ht₂ hle hz' hw'
    · rw [dist_comm]
      exact h w z hw hz t₂ ht₂ t₁ ht₁ hle hw' hz'
  rintro z' w' hz' hw' t₁ ht₁ t₂ ht₂ hle rfl rfl
  have harc : ∀ θ ∈ Icc ((c - ζ).arg + t₁) ((c - ζ).arg + t₂), circleMap ζ ρ θ ∈ ball c r :=
    fun θ hθ =>
      circleMap_mem_ball_of_mem_Icc hζ hρ (by rw [add_sub_cancel_left]; exact ht₁.1)
        (by rw [add_sub_cancel_left]; exact ht₂.2) hθ hz'.1 hw'.1
  exact ofReal_dist_le_circleImageLength isOpen_ball hf ζ hρ (by linarith)
    (by linarith [ht₁.1, ht₂.2, Real.pi_pos]) harc harc

/-- **The image of a circular crosscut is no wider than its length.** A bound `ε` on
`TauCeti.circleImageLength f (ball c r) ζ ρ` bounds the diameter of the image of
`ball c r ∩ sphere ζ ρ`, by the chord bound
`TauCeti.ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere`. -/
theorem diam_image_ball_inter_sphere_le (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball c r)) {ε : ℝ} (hε : 0 ≤ ε)
    (hlen : circleImageLength f (ball c r) ζ ρ ≤ ENNReal.ofReal ε) :
    diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  refine diam_le_of_forall_dist_le hε ?_
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp
    ((ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere hζ hρ hf hz hw).trans hlen)

/-! ## Crosscuts with a short image -/

/-- **A holomorphic map of finite Dirichlet integral has short image crosscuts at every boundary
point.** For `f` holomorphic on `ball c r` with `∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤` and `ζ` on
the circle `sphere c r`, every tolerance `ε > 0` and every bound `R > 0` admit a radius `ρ < R` at
which the image of `ball c r ∩ sphere ζ ρ` has diameter at most `ε`.

This is the limiting form `TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top` of Wolff's
lemma fed to `TauCeti.diam_image_ball_inter_sphere_le`. The annulus in which the good `ρ` is sought
is chosen there rather than here: it is made logarithmically long enough that the length–area
average of `circleImageLength f (ball c r) ζ ρ ^ 2` over it falls below the threshold, and is
shrunk against `R` so that the radius produced lies in `Ioo 0 R`.

The bound is on the intersection `ball c r ∩ sphere ζ ρ`, which is a genuine circular crosscut only
when `ρ < 2 * r`, being empty otherwise; since `R` is arbitrary, a caller wanting a crosscut applies
the theorem with `R ≤ 2 * r`.

This is the first of the two geometric inputs of
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le`; nothing here bounds
the boundary piece the crosscut cuts off, which is a matter of the image domain rather than of the
map. -/
theorem exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top (hζ : dist ζ c = r)
    (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  obtain ⟨ρ, hρmem, hlen⟩ :=
    exists_circleImageLength_lt_of_lintegral_ne_top (s := ball c r) f measurableSet_ball ζ hfin
      (ENNReal.ofReal_pos.mpr hε).ne' hR
  exact ⟨ρ, hρmem, diam_image_ball_inter_sphere_le hζ hρmem.1 hf hε.le hlen.le⟩

/-- **A conformal map of a disc has arbitrarily small images of the circle intersections
`ball c r ∩ sphere ζ ρ` at every boundary point.** This is the case of
`TauCeti.exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top` that a Riemann map falls under:
for `f` injective on `ball c r` with bounded image the Dirichlet integral is the area of that image,
hence finite by `TauCeti.lintegral_enorm_deriv_sq_ne_top_of_isBounded`.

As there, the intersection bounded is a genuine circular crosscut only when `ρ < 2 * r`, being
empty otherwise — in particular when `r = 0`, which the hypotheses allow; a caller wanting a
crosscut applies the theorem with `R ≤ 2 * r`. -/
theorem exists_diam_image_ball_inter_sphere_le (hζ : dist ζ c = r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε :=
  exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top hζ hf
    (lintegral_enorm_deriv_sq_ne_top_of_isBounded isOpen_ball hf
      measurableSet_ball.nullMeasurableSet subset_rfl hinj hb) hε hR

end TauCeti
