/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-!
# The Schwarz reflection principle across an affine line

This file transports the real-axis Schwarz reflection principle through complex affine charts.
For a base point `p` and a nonzero direction `a`, the chart `w ↦ p + a * w` carries the real
axis to the affine line through `p` in direction `a`. Applying such a chart in both source and
target gives the explicit extension `lineSchwarzReflection`.

The main theorem, `differentiableOn_lineSchwarzReflection_of_symmetric`, proves that this
extension is holomorphic on a domain invariant under reflection in the source line. The hypotheses
say that the original branch is continuous and holomorphic on one side of the line and maps its
boundary values into the target line. The accompanying branch and symmetry lemmas characterize
the extension without requiring consumers to unfold its definition.

This is the straight-arc case of layer L4 in the conformal-mapping roadmap, which asks for Schwarz
reflection across an analytic arc or circle by Möbius reduction. The construction follows the
standard affine reduction to the real-axis principle; see Ahlfors, *Complex Analysis*,
Chapters 4--6. Layer L4 is absent from the upstream Mathlib Riemann-mapping draft
leanprover-community/mathlib4#33505.
-/

public section

namespace TauCeti

open Complex Set
open scoped ComplexConjugate

/-- The explicit Schwarz-reflection extension across affine source and target lines.

The source line has base point `p` and direction `a`, while the target line has base point `q`
and direction `b`. In affine coordinates, this is exactly the real-axis extension:
`q + b * schwarzReflection (w ↦ (f (p + a * w) - q) / b) ((z - p) / a)`.
The definition is total. Agreement with the original branch and the reflection symmetry assume
`a ≠ 0` and `b ≠ 0`; holomorphy itself only needs `a ≠ 0`, since `b = 0` makes the function
constant. -/
noncomputable def lineSchwarzReflection (p a q b : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  q + b * schwarzReflection (fun w => (f (p + a * w) - q) / b) ((z - p) / a)

/-- The affine-line Schwarz-reflection extension in source and target coordinates. -/
theorem lineSchwarzReflection_def (p a q b : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    lineSchwarzReflection p a q b f z =
      q + b * schwarzReflection (fun w => (f (p + a * w) - q) / b) ((z - p) / a) :=
  by rw [lineSchwarzReflection]

/-- On the closed positive side of the source line, affine-line Schwarz reflection agrees with
the original function. -/
@[simp]
lemma lineSchwarzReflection_of_coord_im_nonneg {p a q b z : ℂ} (f : ℂ → ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hz : 0 ≤ ((z - p) / a).im) :
    lineSchwarzReflection p a q b f z = f z := by
  rw [lineSchwarzReflection_def, schwarzReflection_of_im_nonneg hz]
  rw [mul_div_cancel₀ (z - p) ha]
  have hpz : p + (z - p) = z := by ring
  rw [hpz]
  rw [mul_div_cancel₀ (f z - q) hb]
  ring

/-- On the negative side of the source line, affine-line Schwarz reflection is obtained by
reflecting the argument in the source line and the value in the target line. -/
@[simp]
lemma lineSchwarzReflection_of_coord_im_neg {p a q b z : ℂ} (f : ℂ → ℂ)
    (hz : ((z - p) / a).im < 0) :
    lineSchwarzReflection p a q b f z =
      q + b * (starRingEnd ℂ)
        ((f (p + a * (starRingEnd ℂ) ((z - p) / a)) - q) / b) := by
  rw [lineSchwarzReflection_def, schwarzReflection_of_im_neg hz]

private lemma affineChart_left_inv {p a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    p + a * ((z - p) / a) = z := by
  rw [mul_div_cancel₀ _ ha]
  ring

private lemma affineChart_right_inv {p a : ℂ} (ha : a ≠ 0) (w : ℂ) : (p + a * w - p) / a = w := by
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ ha]

private lemma affineChart_reflection_coord {p a z : ℂ} (ha : a ≠ 0) :
    (p + a * (starRingEnd ℂ) ((z - p) / a) - p) / a = (starRingEnd ℂ) ((z - p) / a) :=
  affineChart_right_inv ha _

/-- **The affine chart carries a pulled-back imaginary-coordinate cut to the original one.** For
any predicate `P` on the imaginary part, the chart `w ↦ p + a·w` maps `φ⁻¹(Ω)` cut by `P ∘ im`
into `Ω` cut by `P` on the *rotated* imaginary part `((z - p)/a).im`. Taking `P` to be `0 ≤ ·`
and `0 < ·` gives the closed and open half-planes, which is how the continuity and holomorphy
transports below use it; the statement itself constrains `P` no further. -/
private lemma mapsTo_affineChart_inter_im {p a : ℂ} (ha : a ≠ 0) {Ω : Set ℂ} {P : ℝ → Prop} :
    MapsTo (fun w : ℂ => p + a * w)
      ((fun w : ℂ => p + a * w) ⁻¹' Ω ∩ {w : ℂ | P w.im})
      (Ω ∩ {z : ℂ | P ((z - p) / a).im}) := by
  refine (Set.mapsTo_preimage _ Ω).inter_inter fun w hw => ?_
  simpa only [Set.mem_ofPred_eq, affineChart_right_inv ha] using hw

/-- **The chart pullback of a line-symmetric domain is conjugation-symmetric.** If `Ω` is carried
into itself by reflection in the line `p + a·ℝ`, then its pullback along `w ↦ p + a·w` is carried
into itself by ordinary complex conjugation — which is what the half-plane reflection theorem asks
for. -/
private lemma mapsTo_conj_affineChart_preimage {p a : ℂ} (ha : a ≠ 0) {Ω : Set ℂ}
    (hΩ : MapsTo (fun z => p + a * (starRingEnd ℂ) ((z - p) / a)) Ω Ω) :
    MapsTo (starRingEnd ℂ) ((fun w : ℂ => p + a * w) ⁻¹' Ω)
      ((fun w : ℂ => p + a * w) ⁻¹' Ω) := fun _ hw => by
  simpa only [Set.mem_preimage, affineChart_right_inv ha] using hΩ hw

/-- **Continuity transports along the chart.** Reading `f` in the source coordinate `w ↦ p + a·w`
and normalizing its values by `(· - q) / b` turns continuity on the closed positive side of the line
into continuity on the closed upper half-plane. -/
private lemma continuousOn_targetChart_comp_affineChart {p a q b : ℂ} (ha : a ≠ 0) {Ω : Set ℂ}
    {f : ℂ → ℂ} (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ ((z - p) / a).im})) :
    ContinuousOn (fun w : ℂ => (f (p + a * w) - q) / b)
      ((fun w : ℂ => p + a * w) ⁻¹' Ω ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hfcomp : ContinuousOn (f ∘ fun w : ℂ => p + a * w)
      ((fun w : ℂ => p + a * w) ⁻¹' Ω ∩ {w : ℂ | 0 ≤ w.im}) :=
    hcont.comp (by fun_prop) (mapsTo_affineChart_inter_im ha)
  simpa [Function.comp_apply] using hfcomp.sub continuousOn_const |>.div_const b

/-- **Holomorphy transports along the chart**, the open-side companion of
`continuousOn_targetChart_comp_affineChart`. -/
private lemma differentiableOn_targetChart_comp_affineChart {p a q b : ℂ} (ha : a ≠ 0) {Ω : Set ℂ}
    {f : ℂ → ℂ} (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < ((z - p) / a).im})) :
    DifferentiableOn ℂ (fun w : ℂ => (f (p + a * w) - q) / b)
      ((fun w : ℂ => p + a * w) ⁻¹' Ω ∩ {w : ℂ | 0 < w.im}) := by
  have hfcomp : DifferentiableOn ℂ (f ∘ fun w : ℂ => p + a * w)
      ((fun w : ℂ => p + a * w) ⁻¹' Ω ∩ {w : ℂ | 0 < w.im}) :=
    hholo.comp (Differentiable.differentiableOn (by fun_prop))
      (mapsTo_affineChart_inter_im ha)
  simpa only [Function.comp_apply] using hfcomp.sub_const q |>.div_const b

/-- **The boundary condition transports to the real axis.** In the source coordinate the line
`p + a·ℝ` is the real axis, so the hypothesis that the normalized values `(f z - q) / b` are real on
the line becomes the hypothesis that the transported function is real on the reals. For `b ≠ 0` that
says `f` maps the source line into the target line `q + b·ℝ`; at `b = 0` the normalization is
identically `0`, so both conditions are vacuous. -/
private lemma im_targetChart_comp_affineChart_eq_zero {p a q b : ℂ} (ha : a ≠ 0) {Ω : Set ℂ}
    {f : ℂ → ℂ} (hline : ∀ z ∈ Ω, ((z - p) / a).im = 0 → ((f z - q) / b).im = 0) :
    ∀ w ∈ (fun w : ℂ => p + a * w) ⁻¹' Ω, w.im = 0 →
      ((fun w : ℂ => (f (p + a * w) - q) / b) w).im = 0 := fun w hw hwim =>
  hline (p + a * w) hw (by rw [affineChart_right_inv ha]; exact hwim)

/-- **Schwarz reflection principle across an affine line, holomorphy form.** Let the source line
be `p + a * ℝ`, with `a ≠ 0`. Suppose an open domain `Ω` is invariant under reflection in this
line. If `f` is continuous on the closed positive side, holomorphic on the open positive side,
and its boundary values have real target coordinate, then `lineSchwarzReflection p a q b f` is
holomorphic throughout `Ω`.

The side and boundary conditions are expressed in the affine coordinates `(z - p) / a` and
`(f z - q) / b`. The target direction `b` need not be nonzero for holomorphy: when `b = 0`, the
conclusion is the constant function with value `q`. The packaged reflection theorem below assumes
`b ≠ 0` to obtain branch agreement and target-line symmetry. -/
theorem differentiableOn_lineSchwarzReflection_of_symmetric {Ω : Set ℂ} {p a q b : ℂ} {f : ℂ → ℂ}
    (ha : a ≠ 0) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (fun z => p + a * (starRingEnd ℂ) ((z - p) / a)) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ ((z - p) / a).im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < ((z - p) / a).im}))
    (hline : ∀ z ∈ Ω, ((z - p) / a).im = 0 → ((f z - q) / b).im = 0) :
    DifferentiableOn ℂ (lineSchwarzReflection p a q b f) Ω := by
  -- Read everything in the charts `φ w = p + a·w` and `ψ z = (z - p)/a`, where the source line is
  -- the real axis and the four hypotheses become those of the half-plane theorem.
  have hUopen : IsOpen ((fun w : ℂ => p + a * w) ⁻¹' Ω) :=
    hΩopen.preimage (by fun_prop)
  have hg := differentiableOn_schwarzReflection_of_symmetric
    (f := fun w : ℂ => (f (p + a * w) - q) / b) hUopen
    (mapsTo_conj_affineChart_preimage ha hΩ)
    (continuousOn_targetChart_comp_affineChart ha hcont)
    (differentiableOn_targetChart_comp_affineChart ha hholo)
    (im_targetChart_comp_affineChart_eq_zero ha hline)
  -- Push back along `ψ`, whose image lands in `φ⁻¹(Ω)` by the other inverse law.
  have hcomp : DifferentiableOn ℂ
      (fun z => schwarzReflection (fun w : ℂ => (f (p + a * w) - q) / b) ((z - p) / a)) Ω := by
    refine hg.comp (Differentiable.differentiableOn (by fun_prop)) fun z hz => ?_
    simpa only [Set.mem_preimage, affineChart_left_inv ha] using hz
  exact ((differentiableOn_const q).add ((differentiableOn_const b).mul hcomp)).congr
    fun z _ => lineSchwarzReflection_def p a q b f z

/-- Affine-line Schwarz reflection intertwines reflection in the source line with reflection in
the target line. The boundary hypothesis says precisely that the original function takes the
source line into the target line. -/
theorem lineSchwarzReflection_sourceReflection {Ω : Set ℂ} {p a q b : ℂ} {f : ℂ → ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hline : ∀ z ∈ Ω, ((z - p) / a).im = 0 → ((f z - q) / b).im = 0)
    {z : ℂ} (hz : z ∈ Ω) :
    lineSchwarzReflection p a q b f
        (p + a * (starRingEnd ℂ) ((z - p) / a)) =
      q + b * (starRingEnd ℂ)
        ((lineSchwarzReflection p a q b f z - q) / b) := by
  let g := fun w : ℂ => (f (p + a * w) - q) / b
  have hgline : ((z - p) / a).im = 0 → (g ((z - p) / a)).im = 0 := by
    intro him
    simpa only [g, affineChart_left_inv ha z] using hline z hz him
  rw [lineSchwarzReflection_def, lineSchwarzReflection_def,
    affineChart_reflection_coord ha]
  rw [schwarzReflection_conj _ hgline]
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hb]

/-- **Schwarz reflection principle across affine source and target lines, packaged form.**
Under the hypotheses of `differentiableOn_lineSchwarzReflection_of_symmetric`, with both line
directions nonzero, there is a holomorphic extension which agrees with `f` on the closed positive
side and intertwines reflection in the source and target lines. The witness is the explicit
function `lineSchwarzReflection p a q b f`. -/
theorem exists_differentiableOn_eqOn_lineReflection_of_symmetric
    {Ω : Set ℂ} {p a q b : ℂ} {f : ℂ → ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (fun z => p + a * (starRingEnd ℂ) ((z - p) / a)) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ ((z - p) / a).im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < ((z - p) / a).im}))
    (hline : ∀ z ∈ Ω, ((z - p) / a).im = 0 → ((f z - q) / b).im = 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F Ω ∧
      EqOn F f (Ω ∩ {z : ℂ | 0 ≤ ((z - p) / a).im}) ∧
      ∀ z ∈ Ω,
        F (p + a * (starRingEnd ℂ) ((z - p) / a)) =
          q + b * (starRingEnd ℂ) ((F z - q) / b) := by
  refine ⟨lineSchwarzReflection p a q b f,
    differentiableOn_lineSchwarzReflection_of_symmetric ha hΩopen hΩ hcont hholo hline,
    ?_, ?_⟩
  · intro z hz
    exact lineSchwarzReflection_of_coord_im_nonneg f ha hb hz.2
  · intro z hz
    exact lineSchwarzReflection_sourceReflection ha hb hline hz

end TauCeti
