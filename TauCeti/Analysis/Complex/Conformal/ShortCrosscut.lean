/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut
public import TauCeti.Analysis.Complex.Conformal.LengthArea

/-!
# A circular crosscut with a short image

`Conformal/LengthArea.lean` proves Wolff's lemma — among the circles `‖z - ζ‖ = ρ` with
`r < ρ < R`, one has small `TauCeti.circleImageLength f s ζ ρ` — and the chord bound
`TauCeti.ofReal_dist_le_circleImageLength`, which controls the distance between the images of the
two endpoints of an *arc of angles*. It leaves open, in its own words, the step of "turning that
into a crosscut of small diameter at a boundary point". This file takes that step: it identifies
the *set* `ball c r ∩ sphere ζ ρ` cut out of the circle `sphere ζ ρ` by the disc — the **circular
crosscut** of `Conformal/Crosscut.lean` — as such an arc of angles, and concludes that its image
under a conformal map has small diameter at suitable radii `ρ`.

That is the first of the two geometric inputs
`TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le` of
`Conformal/CutDiameter.lean` runs on, and hence of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's boundary correspondence. The second —
a small set `E` enclosing the boundary points of the image domain that cling to the piece the
crosscut cuts off — is a matter of local connectedness of that boundary and is not treated here.

## The crosscut is an arc

Everything rests on an angular description of the crosscut. Writing `α = arg (c - ζ)` for the
direction from the boundary point `ζ` to the centre, the inversion identity
`TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv` of `Conformal/Crosscut.lean` becomes
(`TauCeti.circleMap_mem_ball_iff`)

> `circleMap ζ ρ θ ∈ ball c r ↔ ρ < 2 * r * cos (θ - α)`:

the crosscut consists of the angles within `arccos (ρ / (2 * r))` of `α`. Rather than name that
half-width, the file uses only what the estimate needs — that `cos` has no interior minimum on
`[-π, π]`, so the condition `ρ < 2 * r * cos (θ - α)` holds throughout an interval of angles as
soon as it holds at both ends (`TauCeti.circleMap_mem_ball_of_mem_Icc`). Every point of the
crosscut is `circleMap ζ ρ (α + t)` for a single `t ∈ [-π, π]`, so any two of them are the
endpoints of such an interval, of width at most `2 * π`, along which the chord bound applies.

## Main results

* `TauCeti.circleMap_mem_ball_iff` — the angular description of a circular crosscut at a boundary
  point.
* `TauCeti.circleMap_mem_ball_of_mem_Icc` — the crosscut is an arc: an interval of angles inside
  the period centred at `α` whose endpoints lie in the disc lies in the disc throughout.
* `TauCeti.ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere` — the chord bound for the
  crosscut: any two of its points have images at distance at most
  `TauCeti.circleImageLength f (ball c r) ζ ρ`.
* `TauCeti.diam_image_ball_inter_sphere_le` — hence the image of the crosscut is no wider than that
  quantity.
* `TauCeti.exists_diam_image_ball_inter_sphere_le` — the conclusion, from Wolff's lemma: a
  conformal map of a disc with bounded image has, at every boundary point and below every positive
  radius, a circular crosscut whose image has diameter at most `ε`.

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

/-! ## The angular description of a circular crosscut -/

/-- **A circular crosscut is an arc of angles around the direction of the centre.** For `ζ` on the
circle `sphere c r` and `ρ > 0`, the point of `sphere ζ ρ` at angle `θ` lies in `ball c r` exactly
when `ρ < 2 * r * cos (θ - arg (c - ζ))`.

This is the inversion identity `TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv` written in polar
form: with `c - ζ = r * exp (arg (c - ζ) * I)`, the inverted point
`(c - ζ) * (circleMap ζ ρ θ - ζ)⁻¹` is `(r / ρ) * exp ((arg (c - ζ) - θ) * I)`, whose real part is
`(r / ρ) * cos (θ - arg (c - ζ))`.

Nothing is assumed of `r` beyond what `dist ζ c = r` forces; for `r = 0` both sides are false. -/
theorem circleMap_mem_ball_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    circleMap ζ ρ θ ∈ ball c r ↔ ρ < 2 * r * Real.cos (θ - (c - ζ).arg) := by
  have hnorm : ‖c - ζ‖ = r := by rw [← dist_eq_norm, dist_comm, hζ]
  have hpolar : c - ζ = (r : ℂ) * exp (((c - ζ).arg : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (c - ζ)]
    rw [hnorm]
  have hsphere : circleMap ζ ρ θ ∈ sphere ζ ρ := circleMap_mem_sphere ζ hρ.le θ
  have hne : circleMap ζ ρ θ ≠ ζ := by
    intro h
    rw [mem_sphere, h, dist_self] at hsphere
    exact hρ.ne hsphere
  have hsub : circleMap ζ ρ θ - ζ = (ρ : ℂ) * exp ((θ : ℂ) * I) := by
    rw [circleMap_sub_center, circleMap_zero]
  have hexp : exp (((c - ζ).arg : ℂ) * I) * (exp ((θ : ℂ) * I))⁻¹
      = exp ((((c - ζ).arg - θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    push_cast
    ring_nf
  have hprod : (c - ζ) * (circleMap ζ ρ θ - ζ)⁻¹
      = ((r * ρ⁻¹ : ℝ) : ℂ) * exp ((((c - ζ).arg - θ : ℝ) : ℂ) * I) := by
    rw [hsub, mul_inv, ← hexp]
    conv_lhs => rw [hpolar]
    push_cast
    ring
  have hre : ((c - ζ) * (circleMap ζ ρ θ - ζ)⁻¹).re = r * ρ⁻¹ * Real.cos (θ - (c - ζ).arg) := by
    rw [hprod, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, ← Real.cos_neg, neg_sub]
  rw [mem_ball_iff_one_lt_two_mul_re_mul_inv hζ hne, hre]
  rw [show 2 * (r * ρ⁻¹ * Real.cos (θ - (c - ζ).arg))
      = (2 * r * Real.cos (θ - (c - ζ).arg)) * ρ⁻¹ by ring, ← div_eq_mul_inv,
    lt_div_iff₀ hρ, one_mul]

/-- **The cosine has no interior minimum on `[-π, π]`.** If `k < cos a` and `k < cos b`, with
`-π ≤ a` and `b ≤ π`, then `k < cos θ` for every `θ ∈ [a, b]`: `cos` increases on `[-π, 0]` and
decreases on `[0, π]`, so on `[a, b]` its minimum is attained at an endpoint. -/
private theorem lt_cos_of_mem_Icc {k a b θ : ℝ} (ha : -π ≤ a) (hb : b ≤ π) (hθ : θ ∈ Icc a b)
    (hka : k < Real.cos a) (hkb : k < Real.cos b) : k < Real.cos θ := by
  rcases le_total θ 0 with hθ0 | hθ0
  · refine hka.trans_le ?_
    rw [← Real.cos_neg θ, ← Real.cos_neg a]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith [hθ.1])
  · exact hkb.trans_le (Real.cos_le_cos_of_nonneg_of_le_pi hθ0 hb hθ.2)

/-- **A circular crosscut is connected as a set of angles.** If the angles `a` and `b` both lie
within `π` of the direction `arg (c - ζ)` of the centre and both put the point of `sphere ζ ρ` they
name inside `ball c r`, then so does every angle in `[a, b]`.

This is `TauCeti.circleMap_mem_ball_iff` read through the unimodality of `cos` on a period centred
at `arg (c - ζ)`; positivity of `r` is not assumed, being forced by the hypotheses. -/
theorem circleMap_mem_ball_of_mem_Icc (hζ : dist ζ c = r) (hρ : 0 < ρ) {a b θ : ℝ}
    (ha : -π ≤ a - (c - ζ).arg) (hb : b - (c - ζ).arg ≤ π) (hθ : θ ∈ Icc a b)
    (hain : circleMap ζ ρ a ∈ ball c r) (hbin : circleMap ζ ρ b ∈ ball c r) :
    circleMap ζ ρ θ ∈ ball c r := by
  rw [circleMap_mem_ball_iff hζ hρ] at hain hbin ⊢
  have hr : 0 < r := by
    rcases (hζ ▸ dist_nonneg : (0 : ℝ) ≤ r).eq_or_lt with h | h
    · rw [← h, mul_zero, zero_mul] at hain
      linarith
    · exact h
  have hkey : ∀ x : ℝ, (ρ < 2 * r * Real.cos (x - (c - ζ).arg))
      ↔ ρ / (2 * r) < Real.cos (x - (c - ζ).arg) := fun x => by
    rw [div_lt_iff₀ (by linarith), mul_comm]
  rw [hkey] at hain hbin ⊢
  exact lt_cos_of_mem_Icc ha hb ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hain hbin

/-- Every point of the circle `sphere ζ ρ` is reached at an angle within `π` of any prescribed
direction `α`: the argument of `(z - ζ) * exp (-α * I)` measures the point off from `α`. -/
private theorem exists_mem_Icc_circleMap_eq (α : ℝ) {z : ℂ} (hz : z ∈ sphere ζ ρ) :
    ∃ t ∈ Icc (-π) π, circleMap ζ ρ (α + t) = z := by
  set v : ℂ := (z - ζ) * exp (((-α : ℝ) : ℂ) * I) with hv
  have hznorm : ‖z - ζ‖ = ρ := by rw [← dist_eq_norm, mem_sphere.mp hz]
  have hvnorm : ‖v‖ = ρ := by
    rw [hv, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hznorm]
  refine ⟨v.arg, Ioc_subset_Icc_self (Complex.arg_mem_Ioc v), ?_⟩
  have hpolar : (ρ : ℂ) * exp ((v.arg : ℂ) * I) = v := by
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I v]
    rw [hvnorm]
  have hunit : exp (((-α : ℝ) : ℂ) * I) * exp (((α : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    push_cast
    rw [show -(α : ℂ) * I + (α : ℂ) * I = 0 by ring, Complex.exp_zero]
  have hsplit : exp (((α + v.arg : ℝ) : ℂ) * I) = exp (((α : ℝ) : ℂ) * I) * exp ((v.arg : ℂ) * I) :=
    by rw [← Complex.exp_add]; push_cast; ring_nf
  rw [circleMap, hsplit, ← mul_assoc, mul_comm ((ρ : ℂ)) _, mul_assoc, hpolar, hv, mul_comm,
    mul_assoc, hunit, mul_one]
  ring

/-! ## The chord bound on a circular crosscut -/

/-- **The chord bound for a circular crosscut.** For `f` holomorphic on `ball c r` and `ζ` on the
circle `sphere c r`, any two points of the crosscut `ball c r ∩ sphere ζ ρ` have images at distance
at most `TauCeti.circleImageLength f (ball c r) ζ ρ`.

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
`TauCeti.circleImageLength f (ball c r) ζ ρ` bounds the diameter of the image of the crosscut
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

/-- **A conformal map of a disc has crosscuts with arbitrarily small image at every boundary
point.** For `f` holomorphic and injective on `ball c r` with bounded image and `ζ` on the circle
`sphere c r`, every tolerance `ε > 0` and every bound `R > 0` admit a radius `ρ < R` at which the
image of the circular crosscut `ball c r ∩ sphere ζ ρ` has diameter at most `ε`.

This is Wolff's lemma `TauCeti.exists_circleImageLength_sq_lt` — the Dirichlet integral of `f` is
finite because the image is bounded — fed to `TauCeti.diam_image_ball_inter_sphere_le`. The inner
radius of the annulus in which the good `ρ` is sought is `R * exp (-(A + 1) / ε ^ 2)`, where `A` is
`2 * π` times that Dirichlet integral: the annulus is made logarithmically long enough that the
average of `circleImageLength f (ball c r) ζ ρ ^ 2` over it falls below `ε ^ 2`.

This is the first of the two geometric inputs of
`TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le`; nothing here bounds
the boundary piece the crosscut cuts off, which is a matter of the image domain rather than of the
map. -/
theorem exists_diam_image_ball_inter_sphere_le (hζ : dist ζ c = r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  -- the Dirichlet integral is finite, and `A` is `2 * π` times it
  have hfin : ENNReal.ofReal (2 * π) * ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_enorm_deriv_sq_ne_top_of_isBounded isOpen_ball hf
        measurableSet_ball.nullMeasurableSet subset_rfl hinj hb)
  set A : ℝ := (ENNReal.ofReal (2 * π) * ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2).toReal with hA
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  -- the annulus `Ioo r' R`, long enough on the logarithmic scale
  set L : ℝ := (A + 1) / ε ^ 2 with hL
  have hLpos : 0 < L := div_pos (by linarith) (by positivity)
  set r' : ℝ := R * Real.exp (-L) with hr'
  have hr'pos : 0 < r' := mul_pos hR (Real.exp_pos _)
  have hr'R : r' < R := by
    have : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  have hRr' : R / r' = Real.exp L := by
    rw [eq_comm, eq_div_iff hr'pos.ne', hr',
      show Real.exp L * (R * Real.exp (-L)) = R * (Real.exp L * Real.exp (-L)) from by ring,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hlog : Real.log (R / r') = L := by rw [hRr', Real.log_exp]
  -- Wolff's lemma on that annulus, with threshold `ε ^ 2`
  have hc : ENNReal.ofReal (2 * π) * ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2
      < ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (Real.log (R / r')) := by
    have hAeq : ENNReal.ofReal (2 * π) * ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 = ENNReal.ofReal A :=
      (ENNReal.ofReal_toReal hfin).symm
    rw [hAeq, hlog, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε ^ 2), hL,
      show ε ^ 2 * ((A + 1) / ε ^ 2) = A + 1 from by field_simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨ρ, hρmem, hρlt⟩ :=
    exists_circleImageLength_sq_lt (s := ball c r) f measurableSet_ball ζ hr'pos hr'R hc
  -- undo the square
  have hlen : circleImageLength f (ball c r) ζ ρ ≤ ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_pow hε.le] at hρlt
    by_contra hcon
    exact absurd (pow_le_pow_left' (not_le.mp hcon).le 2) (not_le.mpr hρlt)
  exact ⟨ρ, ⟨hr'pos.trans hρmem.1, hρmem.2⟩,
    diam_image_ball_inter_sphere_le hζ (hr'pos.trans hρmem.1) hf hε.le hlen⟩

end TauCeti
