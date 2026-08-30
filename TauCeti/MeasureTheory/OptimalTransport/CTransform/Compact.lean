/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.Topology.Semicontinuity.CompactInfimum

/-!
# The infimal `c`-transform in the compact lower semicontinuous regime

`TauCeti.cTransform c φ y = ⨅ x, (c (x, y) - φ x)` is an infimum over the source, so its
regularity in `y` splits into two halves needing opposite hypotheses. An infimum of upper
semicontinuous functions is upper semicontinuous with no hypothesis on the source at all, which is
`TauCeti.upperSemicontinuous_cTransform`. The reverse half fails in general and needs the source to
be compact: this file proves that on a compact source a lower semicontinuous integrand makes the
transform lower semicontinuous, that the defining infimum is then attained, and hence that a
continuous cost and a continuous real-valued potential give a continuous transform. With a lower
semicontinuous cost section and an upper semicontinuous real-valued potential, attainment in turn
makes the transform real-valued and the `c`-superdifferential meet every vertical fibre. Borel
measurability of the transform is recorded as a corollary. The
measurability corollaries of the opposite, upper semicontinuous regime need no compactness and
live with that regime in `TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic`.

The integrand of the transform is `x ↦ (c (x, y) : EReal) - φ x`, and the hypotheses below are
stated on it rather than on `c` and `φ` separately, since the extended-real subtraction is what a
lower bound has to survive. The `_coe` results specialize to a real-valued potential, where a lower
semicontinuous cost and an upper semicontinuous potential do supply that hypothesis; the pointwise
ones ask for lower semicontinuity of only the one section of the cost that their infimum ranges
over.

No metrizability, separability or countability of the source is assumed: attainment and lower
semicontinuity of a partial infimum need compactness alone, as
`TauCeti.exists_iInf_eq_of_lowerSemicontinuous` and
`TauCeti.lowerSemicontinuous_iInf_of_compactSpace` record.

## Main results

* `TauCeti.exists_cTransform_eq`: on a nonempty compact source the infimum defining the transform
  is attained, and `TauCeti.exists_cTransformSymm_eq` on a nonempty compact target.
* `TauCeti.lowerSemicontinuous_cTransform`: on a compact source a jointly lower semicontinuous
  integrand makes the transform lower semicontinuous.
* `TauCeti.exists_cTransform_coe_eq_coe`, `TauCeti.exists_cTransformSymm_coe_eq_coe`,
  `TauCeti.cTransform_coe_ne_bot`, and `TauCeti.cTransformSymm_coe_ne_bot`: on a nonempty compact
  factor, a lower semicontinuous cost section and an upper semicontinuous real-valued potential
  make the transform real-valued.
* `TauCeti.exists_mem_cSuperdifferential_coe` and
  `TauCeti.exists_mem_cSuperdifferentialSymm_coe`: on a nonempty compact factor, a lower
  semicontinuous cost section and an upper semicontinuous real-valued potential supply a contact
  point in the corresponding fibre.
* `TauCeti.continuous_cTransform_coe`: on a compact source a continuous cost and a continuous
  real-valued potential make the transform continuous.
* `TauCeti.measurable_cTransform_of_lowerSemicontinuous` and
  `TauCeti.measurable_cTransformSymm_of_lowerSemicontinuous`: Borel measurability of the transform
  in the compact lower semicontinuous regime.

## References

The regularity of the infimal transform under these hypotheses is Villani, *Optimal Transport, Old
and New*, Chapter 5, and Santambrogio, *Optimal Transport for Applied Mathematicians*, §1.6.
-/

public section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {c : X × Y → ℝ} {φ : X → EReal}
  {ψ : Y → EReal} {f : X → ℝ} {g : Y → ℝ} {x : X} {y : Y}

/-! ## Attainment of the defining infimum -/

omit [TopologicalSpace Y] in
/-- On a nonempty compact source with a lower semicontinuous integrand, the infimum defining the
`c`-transform is attained. -/
theorem exists_cTransform_eq [CompactSpace X] [Nonempty X]
    (h : LowerSemicontinuous fun x => (c (x, y) : EReal) - φ x) :
    ∃ x, cTransform c φ y = (c (x, y) : EReal) - φ x := by
  simp only [cTransform_apply]
  exact exists_iInf_eq_of_lowerSemicontinuous h

omit [TopologicalSpace X] in
/-- On a nonempty compact target with a lower semicontinuous integrand, the infimum defining the
symmetric `c`-transform is attained. -/
theorem exists_cTransformSymm_eq [CompactSpace Y] [Nonempty Y]
    (h : LowerSemicontinuous fun y => (c (x, y) : EReal) - ψ y) :
    ∃ y, cTransformSymm c ψ x = (c (x, y) : EReal) - ψ y := by
  simp only [cTransformSymm_apply]
  exact exists_iInf_eq_of_lowerSemicontinuous h

/-! ## Lower semicontinuity over a compact factor -/

/-- A `c`-transform over a compact source is lower semicontinuous when the integrand of its
defining infimum is jointly lower semicontinuous.

Compactness of the source cannot be dropped: an arbitrary infimum of lower semicontinuous
functions need not be lower semicontinuous. -/
theorem lowerSemicontinuous_cTransform [CompactSpace X]
    (h : LowerSemicontinuous fun p : X × Y => (c p : EReal) - φ p.1) :
    LowerSemicontinuous (cTransform c φ) := by
  have hfun : cTransform c φ = fun y => ⨅ x, ((c (x, y) : EReal) - φ x) :=
    funext (cTransform_apply c φ)
  rw [hfun]
  exact lowerSemicontinuous_iInf_of_compactSpace h

/-- A symmetric `c`-transform over a compact target is lower semicontinuous when the integrand of
its defining infimum is jointly lower semicontinuous. -/
theorem lowerSemicontinuous_cTransformSymm [CompactSpace Y]
    (h : LowerSemicontinuous fun p : X × Y => (c p : EReal) - ψ p.2) :
    LowerSemicontinuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact lowerSemicontinuous_cTransform (h.comp continuous_swap)

/-! ## Real-valued potentials -/

/-- The difference of a lower semicontinuous function and an upper semicontinuous one is lower
semicontinuous after coercion to the extended reals. This is the shape in which a real-valued
potential meets the hypotheses above. -/
private theorem lowerSemicontinuous_coe_sub_coe {α : Type*} [TopologicalSpace α] {u v : α → ℝ}
    (hu : LowerSemicontinuous u) (hv : UpperSemicontinuous v) :
    LowerSemicontinuous fun a => (u a : EReal) - (v a : EReal) := by
  have hneg : LowerSemicontinuous fun a => -v a :=
    continuous_neg.comp_upperSemicontinuous_antitone hv fun _ _ h => neg_le_neg h
  have hsub : LowerSemicontinuous fun a => u a - v a := by
    simpa only [sub_eq_add_neg] using hu.add hneg
  simpa only [Function.comp_def, EReal.coe_sub] using
    continuous_coe_real_ereal.comp_lowerSemicontinuous hsub EReal.coe_strictMono.monotone

/-- A lower semicontinuous cost and an upper semicontinuous real-valued potential give a lower
semicontinuous `c`-transform over a compact source. -/
theorem lowerSemicontinuous_cTransform_coe [CompactSpace X] (hc : LowerSemicontinuous c)
    (hf : UpperSemicontinuous f) :
    LowerSemicontinuous (cTransform c fun x => (f x : EReal)) :=
  lowerSemicontinuous_cTransform (lowerSemicontinuous_coe_sub_coe hc (hf.comp continuous_fst))

/-- A lower semicontinuous cost and an upper semicontinuous real-valued potential give a lower
semicontinuous symmetric `c`-transform over a compact target. -/
theorem lowerSemicontinuous_cTransformSymm_coe [CompactSpace Y] (hc : LowerSemicontinuous c)
    (hg : UpperSemicontinuous g) :
    LowerSemicontinuous (cTransformSymm c fun y => (g y : EReal)) :=
  lowerSemicontinuous_cTransformSymm (lowerSemicontinuous_coe_sub_coe hc (hg.comp continuous_snd))

omit [TopologicalSpace Y] in
/-- On a nonempty compact source, a cost whose section at `y` is lower semicontinuous and an
upper semicontinuous real-valued potential make the infimum defining the `c`-transform attained.
Only that one section of the cost is used, so no topology on the target is needed. -/
theorem exists_cTransform_coe_eq [CompactSpace X] [Nonempty X]
    (hc : LowerSemicontinuous fun x => c (x, y)) (hf : UpperSemicontinuous f) :
    ∃ x, cTransform c (fun x => (f x : EReal)) y = (c (x, y) : EReal) - (f x : EReal) :=
  exists_cTransform_eq (lowerSemicontinuous_coe_sub_coe hc hf)

omit [TopologicalSpace X] in
/-- On a nonempty compact target, a cost whose section at `x` is lower semicontinuous and an
upper semicontinuous real-valued potential make the infimum defining the symmetric `c`-transform
attained. -/
theorem exists_cTransformSymm_coe_eq [CompactSpace Y] [Nonempty Y]
    (hc : LowerSemicontinuous fun y => c (x, y)) (hg : UpperSemicontinuous g) :
    ∃ y, cTransformSymm c (fun y => (g y : EReal)) x = (c (x, y) : EReal) - (g y : EReal) :=
  exists_cTransformSymm_eq (lowerSemicontinuous_coe_sub_coe hc hg)

/-! ## Finiteness and contact points -/

omit [TopologicalSpace Y] in
/-- On a nonempty compact source, a lower semicontinuous cost section and an upper semicontinuous
real-valued potential make the `c`-transform real-valued: the infimum is attained, and its value at
a minimiser is a difference of reals. The general bridge `TauCeti.cTransform_coe` instead assumes
that the corresponding real infimum is bounded below; compactness and semicontinuity here supply
both that bound and attainment. -/
theorem exists_cTransform_coe_eq_coe [CompactSpace X] [Nonempty X]
    (hc : LowerSemicontinuous fun x => c (x, y)) (hf : UpperSemicontinuous f) :
    ∃ b : ℝ, cTransform c (fun x => (f x : EReal)) y = (b : EReal) := by
  obtain ⟨x₀, hx₀⟩ := exists_cTransform_coe_eq hc hf
  exact ⟨c (x₀, y) - f x₀, by rw [hx₀, EReal.coe_sub]⟩

omit [TopologicalSpace X] in
/-- On a nonempty compact target, a lower semicontinuous cost section and an upper semicontinuous
real-valued potential make the symmetric `c`-transform real-valued. -/
theorem exists_cTransformSymm_coe_eq_coe [CompactSpace Y] [Nonempty Y]
    (hc : LowerSemicontinuous fun y => c (x, y)) (hg : UpperSemicontinuous g) :
    ∃ b : ℝ, cTransformSymm c (fun y => (g y : EReal)) x = (b : EReal) := by
  obtain ⟨y₀, hy₀⟩ := exists_cTransformSymm_coe_eq hc hg
  exact ⟨c (x, y₀) - g y₀, by rw [hy₀, EReal.coe_sub]⟩

omit [TopologicalSpace Y] in
/-- On a nonempty compact source, a lower semicontinuous cost section and an upper semicontinuous
real-valued potential make the `c`-transform avoid `-∞`. The opposite bound needs no compactness
and is `TauCeti.cTransform_lt_top_of_ne_bot`. -/
theorem cTransform_coe_ne_bot [CompactSpace X] [Nonempty X]
    (hc : LowerSemicontinuous fun x => c (x, y)) (hf : UpperSemicontinuous f) :
    cTransform c (fun x => (f x : EReal)) y ≠ ⊥ := by
  obtain ⟨b, hb⟩ := exists_cTransform_coe_eq_coe hc hf
  rw [hb]
  exact EReal.coe_ne_bot b

omit [TopologicalSpace X] in
/-- On a nonempty compact target, a lower semicontinuous cost section and an upper semicontinuous
real-valued potential make the symmetric `c`-transform avoid `-∞`. -/
theorem cTransformSymm_coe_ne_bot [CompactSpace Y] [Nonempty Y]
    (hc : LowerSemicontinuous fun y => c (x, y)) (hg : UpperSemicontinuous g) :
    cTransformSymm c (fun y => (g y : EReal)) x ≠ ⊥ := by
  obtain ⟨b, hb⟩ := exists_cTransformSymm_coe_eq_coe hc hg
  rw [hb]
  exact EReal.coe_ne_bot b

omit [TopologicalSpace Y] in
/-- On a nonempty compact source, a lower semicontinuous cost section and an upper semicontinuous
real-valued potential make the `c`-superdifferential meet the vertical fibre over `y`. This is the
complementary-slackness input that a dual optimizer supplies, and it is what fails without
compactness, the infimum then being only approached. -/
theorem exists_mem_cSuperdifferential_coe [CompactSpace X] [Nonempty X]
    (hc : LowerSemicontinuous fun x => c (x, y)) (hf : UpperSemicontinuous f) :
    ∃ x, (x, y) ∈ cSuperdifferential c fun x => (f x : EReal) := by
  obtain ⟨x₀, hx₀⟩ := exists_cTransform_coe_eq hc hf
  exact ⟨x₀, mem_cSuperdifferential_of_cTransform_eq rfl hx₀⟩

omit [TopologicalSpace X] in
/-- On a nonempty compact target, a lower semicontinuous cost section and an upper semicontinuous
real-valued potential supply a contact point for the swapped cost in the fibre over `x`. -/
theorem exists_mem_cSuperdifferentialSymm_coe [CompactSpace Y] [Nonempty Y]
    (hc : LowerSemicontinuous fun y => c (x, y)) (hg : UpperSemicontinuous g) :
    ∃ y, (y, x) ∈ cSuperdifferential (fun p : Y × X => c (p.2, p.1))
      (fun y => (g y : EReal)) :=
  exists_mem_cSuperdifferential_coe hc hg

/-! ## Continuity and measurability -/

/-- On a compact source, a continuous cost and a continuous real-valued potential give a
continuous `c`-transform: the compact-source argument supplies lower semicontinuity, and
`TauCeti.upperSemicontinuous_cTransform_of_continuous` supplies upper semicontinuity. -/
theorem continuous_cTransform_coe [CompactSpace X] (hc : Continuous c) (hf : Continuous f) :
    Continuous (cTransform c fun x => (f x : EReal)) :=
  continuous_iff_lower_upperSemicontinuous.2
    ⟨lowerSemicontinuous_cTransform_coe hc.lowerSemicontinuous hf.upperSemicontinuous,
      upperSemicontinuous_cTransform_of_continuous
        (fun _ => hc.comp (continuous_const.prodMk continuous_id)) _⟩

/-- On a compact target, a continuous cost and a continuous real-valued potential give a
continuous symmetric `c`-transform. -/
theorem continuous_cTransformSymm_coe [CompactSpace Y] (hc : Continuous c) (hg : Continuous g) :
    Continuous (cTransformSymm c fun y => (g y : EReal)) :=
  continuous_iff_lower_upperSemicontinuous.2
    ⟨lowerSemicontinuous_cTransformSymm_coe hc.lowerSemicontinuous hg.upperSemicontinuous,
      upperSemicontinuous_cTransformSymm_of_continuous
        (fun _ => hc.comp (continuous_id.prodMk continuous_const)) _⟩

/-- A `c`-transform over a compact source is Borel measurable when the integrand of its defining
infimum is jointly lower semicontinuous. -/
theorem measurable_cTransform_of_lowerSemicontinuous [CompactSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace Y]
    (h : LowerSemicontinuous fun p : X × Y => (c p : EReal) - φ p.1) :
    Measurable (cTransform c φ) :=
  (lowerSemicontinuous_cTransform h).measurable

/-- A symmetric `c`-transform over a compact target is Borel measurable when the integrand of its
defining infimum is jointly lower semicontinuous. -/
theorem measurable_cTransformSymm_of_lowerSemicontinuous [CompactSpace Y] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (h : LowerSemicontinuous fun p : X × Y => (c p : EReal) - ψ p.2) :
    Measurable (cTransformSymm c ψ) :=
  (lowerSemicontinuous_cTransformSymm h).measurable

end TauCeti
