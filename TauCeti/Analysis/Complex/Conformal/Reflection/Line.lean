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

private lemma affineChart_right_inv {p a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    (p + a * w - p) / a = w := by
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ ha]

private lemma affineChart_reflection_coord {p a z : ℂ} (ha : a ≠ 0) :
    (p + a * (starRingEnd ℂ) ((z - p) / a) - p) / a =
      (starRingEnd ℂ) ((z - p) / a) :=
  affineChart_right_inv ha _

/-- **Schwarz reflection principle across an affine line, holomorphy form.** Let the source line
be `p + a * ℝ`, with `a ≠ 0`. Suppose an open domain `Ω` is invariant under reflection in this
line. If `f` is continuous on the closed positive side, holomorphic on the open positive side,
and its boundary values have real target coordinate, then `lineSchwarzReflection p a q b f` is
holomorphic throughout `Ω`.

The side and boundary conditions are expressed in the affine coordinates `(z - p) / a` and
`(f z - q) / b`. The target direction `b` need not be nonzero for holomorphy: when `b = 0`, the
conclusion is the constant function with value `q`. The packaged reflection theorem below assumes
`b ≠ 0` to obtain branch agreement and target-line symmetry. -/
theorem differentiableOn_lineSchwarzReflection_of_symmetric
    {Ω : Set ℂ} {p a q b : ℂ} {f : ℂ → ℂ}
    (ha : a ≠ 0) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (fun z => p + a * (starRingEnd ℂ) ((z - p) / a)) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ ((z - p) / a).im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < ((z - p) / a).im}))
    (hline : ∀ z ∈ Ω, ((z - p) / a).im = 0 → ((f z - q) / b).im = 0) :
    DifferentiableOn ℂ (lineSchwarzReflection p a q b f) Ω := by
  let φ := fun w : ℂ => p + a * w
  let ψ := fun z : ℂ => (z - p) / a
  let g := fun w : ℂ => (f (φ w) - q) / b
  let U := φ ⁻¹' Ω
  have hφdiff : Differentiable ℂ φ := by
    dsimp only [φ]
    fun_prop
  have hψdiff : Differentiable ℂ ψ := by
    dsimp only [ψ]
    fun_prop
  have hφψ : ∀ z : ℂ, φ (ψ z) = z := by
    intro z
    exact affineChart_left_inv ha z
  have hψφ : ∀ w : ℂ, ψ (φ w) = w := by
    intro w
    exact affineChart_right_inv ha w
  have hUopen : IsOpen U := hΩopen.preimage hφdiff.continuous
  have hUsymm : MapsTo (starRingEnd ℂ) U U := by
    intro w hw
    -- Expose the pullback chart so the source-reflection hypothesis can be applied.
    change φ ((starRingEnd ℂ) w) ∈ Ω
    have hreflect := hΩ hw
    simpa only [φ, ψ, hψφ] using hreflect
  have hgcont : ContinuousOn g (U ∩ {w : ℂ | 0 ≤ w.im}) := by
    have hfcomp : ContinuousOn (f ∘ φ) (U ∩ {w : ℂ | 0 ≤ w.im}) := by
      refine hcont.comp hφdiff.continuous.continuousOn ?_
      intro w hw
      refine ⟨hw.1, ?_⟩
      -- The local chart abbreviations hide the inverse law identifying the two side conditions.
      change 0 ≤ (ψ (φ w)).im
      rw [hψφ]
      exact hw.2
    simpa [g, Function.comp_apply] using hfcomp.sub continuousOn_const |>.div_const b
  have hgdiff : DifferentiableOn ℂ g (U ∩ {w : ℂ | 0 < w.im}) := by
    have hfcomp : DifferentiableOn ℂ (f ∘ φ) (U ∩ {w : ℂ | 0 < w.im}) := by
      refine hholo.comp hφdiff.differentiableOn ?_
      intro w hw
      refine ⟨hw.1, ?_⟩
      -- As above, expose the coordinate composite before applying the inverse law.
      change 0 < (ψ (φ w)).im
      rw [hψφ]
      exact hw.2
    simpa only [g, Function.comp_apply] using hfcomp.sub_const q |>.div_const b
  have hgline : ∀ w ∈ U, w.im = 0 → (g w).im = 0 := by
    intro w hw hwim
    apply hline (φ w) hw
    -- Pull the source-line condition back to the real axis.
    change (ψ (φ w)).im = 0
    rw [hψφ]
    exact hwim
  have hg := differentiableOn_schwarzReflection_of_symmetric hUopen hUsymm hgcont hgdiff hgline
  have hcomp : DifferentiableOn ℂ (fun z => schwarzReflection g (ψ z)) Ω := by
    refine hg.comp hψdiff.differentiableOn ?_
    intro z hz
    -- Membership in the pulled-back domain reduces along the other inverse law.
    change φ (ψ z) ∈ Ω
    simpa only [hφψ] using hz
  have hresult : DifferentiableOn ℂ (fun z => q + b * schwarzReflection g (ψ z)) Ω :=
    (differentiableOn_const q).add ((differentiableOn_const b).mul hcomp)
  exact hresult.congr fun z _ => lineSchwarzReflection_def p a q b f z

/-- Affine-line Schwarz reflection intertwines reflection in the source line with reflection in
the target line. The boundary hypothesis says precisely that the original function takes the
source line into the target line. -/
theorem lineSchwarzReflection_sourceReflection
    {Ω : Set ℂ} {p a q b : ℂ} {f : ℂ → ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hline : ∀ z ∈ Ω, ((z - p) / a).im = 0 → ((f z - q) / b).im = 0)
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
    {Ω : Set ℂ} {p a q b : ℂ} {f : ℂ → ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hΩopen : IsOpen Ω)
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
