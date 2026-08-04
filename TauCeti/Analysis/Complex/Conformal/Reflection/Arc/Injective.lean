/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Arc.Principle
public import TauCeti.Analysis.Complex.Conformal.Biholomorph
import TauCeti.Analysis.Complex.Conformal.InverseFunction
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.Reflection.Injective

/-!
# Schwarz reflection across an analytic arc is conformal

`Conformal/Reflection/Arc/Principle.lean` extends a function holomorphic on one side of an
analytic arc to a function holomorphic across it, by straightening the source arc with a
biholomorphic chart `e`, the target arc with a biholomorphic chart `d`, and reflecting in the real
axis in between. This file upgrades that extension from *holomorphic* to *conformal*: if the
original map is injective on the closed positive side of the source arc and sends the open
positive side to the open positive side of the target arc, then `chartedSchwarzReflection e d f`
is injective on all of `e.source` — hence conformal at every point of `e.source`, with a
holomorphic inverse on its image.

It is the arc-level counterpart of `Conformal/Reflection/Injective.lean`, which proves the same
six statements for reflection across the real axis; each theorem below is that file's theorem read
through the two charts, with `Ω` replaced by `e.source`, the half-planes `{0 ≤ z.im}` and
`{0 < z.im}` by their pullbacks `{0 ≤ (e z).im}` and `{0 < (e z).im}`, the reality condition on
values by `(d (f z)).im = 0`, and the conjugations by the reflections `z ↦ e.symm (conj (e z))`
and `v ↦ d.symm (conj (d v))` that the charts induce on the two arcs.

That generality is what layer **L5** of `ConformalMapping/README.md` actually asks for. The
boundary correspondence extends a Riemann map across an *analytic boundary arc*, not across a
straight line, and what the step needs is not merely a holomorphic continuation but a conformal
one: a continuation that is again injective, and whose derivative therefore does not vanish *on
the arc itself*. As on the real axis, `f` is not assumed differentiable at the points of the arc
at all, only continuous there from one side, yet
`TauCeti.conformalAt_chartedSchwarzReflection_of_symmetric` produces a nonvanishing derivative
there for the extension.

## The proof

Everything is transported, not reproved. Writing `g = fun w => d (f (e.symm w))` for the map read
in the straightening coordinates, the three hypotheses of the real-axis theorem hold for `g` on
`e.target` — injectivity on the closed upper half because `e.symm`, `f` and `d` are injective in
turn, and the two half-plane conditions because `e (e.symm w) = w` on `e.target`. So
`TauCeti.injOn_schwarzReflection_of_symmetric` makes `schwarzReflection g` injective on
`e.target`, and `chartedSchwarzReflection e d f` is `d.symm ∘ schwarzReflection g ∘ e` on
`e.source`, a composition of three maps injective on the relevant sets; reading the middle step
off in target coordinates is exactly
`TauCeti.chartedSchwarzReflection_in_coordinates`.

The image description is transported the same way: the real-axis description of
`schwarzReflection g '' e.target` is pushed forward along `d.symm` and pulled back along `e`,
which turns the conjugation of the real-axis statement into the chart-induced reflection
`v ↦ d.symm (conj (d v))` of the target arc.

## Main results

* `TauCeti.injOn_chartedSchwarzReflection_of_symmetric` — the charted reflection of a map
  injective on the closed positive side is injective across the arc.
* `TauCeti.image_chartedSchwarzReflection_of_symmetric` — its image is the image of the closed
  positive side together with the mirror image of that set in the target arc.
* `TauCeti.deriv_chartedSchwarzReflection_ne_zero` — its derivative vanishes nowhere on
  `e.source`, in particular on the boundary arc `e.source ∩ e ⁻¹' ℝ`.
* `TauCeti.conformalAt_chartedSchwarzReflection_of_symmetric` — the extension is conformal at
  every point of `e.source`, including the points of the arc.
* `TauCeti.differentiableOn_invFunOn_chartedSchwarzReflection_of_symmetric` — its inverse is
  holomorphic, so the extension is a biholomorphism onto its image.
* `TauCeti.exists_differentiableOn_injOn_eqOn_chartedReflection_of_symmetric` — the packaged form,
  strengthening `TauCeti.exists_differentiableOn_eqOn_chartedReflection_of_symmetric` by the
  injectivity clause.

## Coordination with upstream Mathlib

Layer L4 (reflection) and layer L5 (boundary correspondence) are absent from the in-progress
Mathlib Riemann-mapping draft
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
so this is new Lean formalization rather than a shim; the shared L0--L3 infrastructure it consumes
(`Conformal/Biholomorph.lean`, `Conformal/InverseFunction.lean`, `Conformal/LocalDegree.lean`)
carries its own shim notice.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 1--3.
-/

public section

namespace TauCeti

open Complex Set
open scoped ComplexConjugate

variable (e d : OpenPartialHomeomorph ℂ ℂ) (f : ℂ → ℂ)

/-- In the straightening coordinates, injectivity of the original branch on the closed positive
side of the source arc becomes injectivity on the closed upper half-plane: `e.symm`, `f` and `d`
are injective in turn on the sets involved. -/
private theorem injOn_in_coordinates
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    InjOn (fun w => d (f (e.symm w))) (e.target ∩ {w : ℂ | 0 ≤ w.im}) := by
  intro w₁ h₁ w₂ h₂ hw
  have hs₁ := mapsTo_symm_inter_im e h₁
  have hs₂ := mapsTo_symm_inter_im e h₂
  have hsymm : e.symm w₁ = e.symm w₂ :=
    hf_inj hs₁ hs₂ (d.injOn (hf_maps hs₁) (hf_maps hs₂) hw)
  simpa only [e.right_inv h₁.1, e.right_inv h₂.1] using congrArg e hsymm

/-- In the straightening coordinates, the hypothesis that the open positive side of the source arc
goes to the open positive side of the target arc becomes the upper-half-plane hypothesis of the
real-axis theorem. -/
private theorem mapsTo_im_pos_in_coordinates
    (hupper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im) :
    MapsTo (fun w => d (f (e.symm w))) (e.target ∩ {w : ℂ | 0 < w.im}) {w : ℂ | 0 < w.im} := by
  rintro w ⟨hw, him⟩
  simp only [Set.mem_ofPred_eq] at him ⊢
  exact hupper _ (e.map_target hw) (by simpa only [e.right_inv hw] using him)

/-- In the straightening coordinates, the sign condition on the arc becomes the sign condition on
the real axis. -/
private theorem im_nonneg_axis_in_coordinates
    (haxis : ∀ z ∈ e.source, (e z).im = 0 → 0 ≤ (d (f z)).im) :
    ∀ w ∈ e.target, w.im = 0 → 0 ≤ ((fun w => d (f (e.symm w))) w).im := fun w hw him =>
  haxis _ (e.map_target hw) (by simpa only [e.right_inv hw] using him)

/-- **Schwarz reflection across an analytic arc preserves injectivity.** Let `e` and `d` be open
partial homeomorphisms with conjugation-invariant coordinate domains. If `f` is injective on the
closed positive side of the source arc, maps that side into the source of `d`, sends the open
positive side to the open positive side of the target arc, and has nonnegative target coordinate
on the arc itself, then `chartedSchwarzReflection e d f` is injective on all of `e.source`.

Injectivity does not need the value of `f` on the arc to *lie* on the target arc, only to stay on
its closed positive side; the corollaries below feed `haxis` from the reflection principle's
`hf_real`. -/
theorem injOn_chartedSchwarzReflection_of_symmetric
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hupper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im)
    (haxis : ∀ z ∈ e.source, (e z).im = 0 → 0 ≤ (d (f z)).im)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    InjOn (chartedSchwarzReflection e d f) e.source := by
  have hginj : InjOn (schwarzReflection fun w => d (f (e.symm w))) e.target :=
    injOn_schwarzReflection_of_symmetric he_symm (mapsTo_im_pos_in_coordinates e d f hupper)
      (im_nonneg_axis_in_coordinates e d f haxis) (injOn_in_coordinates e d f hf_maps hf_inj)
  intro z hz w hw hzw
  have hcoord : schwarzReflection (fun w => d (f (e.symm w))) (e z) =
      schwarzReflection (fun w => d (f (e.symm w))) (e w) := by
    rw [← chartedSchwarzReflection_in_coordinates e d f he_symm hd_symm hf_maps hz,
      ← chartedSchwarzReflection_in_coordinates e d f he_symm hd_symm hf_maps hw, hzw]
  exact e.injOn hz hw (hginj (e.map_source hz) (e.map_source hw) hcoord)

/-- The image of the charted reflection extension is the image of the closed positive side of the
source arc together with its mirror image `v ↦ d.symm (conj (d v))` in the target arc. The arc
itself contributes to both pieces, since `f` lands on the target arc there. -/
theorem image_chartedSchwarzReflection_of_symmetric
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0) :
    chartedSchwarzReflection e d f '' e.source =
      f '' (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) ∪
        (fun v => d.symm ((starRingEnd ℂ) (d v))) ''
          (f '' (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) := by
  -- The inverse chart identifies the closed upper half of `e.target` with the closed positive
  -- side of the source arc, so the coordinate map has image `d '' (f '' _)` there.
  have hsymm : e.symm '' (e.target ∩ {w : ℂ | 0 ≤ w.im}) = e.source ∩ {z : ℂ | 0 ≤ (e z).im} := by
    have h := e.toPartialEquiv.symm_image_target_inter_eq' {w : ℂ | 0 ≤ w.im}
    rwa [Set.preimage_ofPred_eq] at h
  have hcoord : (fun w => d (f (e.symm w))) '' (e.target ∩ {w : ℂ | 0 ≤ w.im}) =
      d '' (f '' (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) := by
    rw [← hsymm, Set.image_image, Set.image_image]
  have hleft : LeftInvOn (d.symm : ℂ → ℂ) d d.source := fun _ hv => d.left_inv hv
  -- The real-axis image description for the coordinate map on `e.target`.
  have himage := image_schwarzReflection_of_symmetric (f := fun w => d (f (e.symm w)))
    (Ω := e.target) he_symm
    (fun w hw him => hf_real _ (e.map_target hw) (by simpa only [e.right_inv hw] using him))
  calc chartedSchwarzReflection e d f '' e.source
      = (fun z => d.symm (schwarzReflection (fun w => d (f (e.symm w))) (e z))) '' e.source :=
        Set.image_congr' (chartedSchwarzReflection_def e d f)
    _ = d.symm '' (schwarzReflection (fun w => d (f (e.symm w))) '' (e '' e.source)) := by
        rw [Set.image_image, Set.image_image]
    _ = d.symm '' (d '' (f '' (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) ∪
          (starRingEnd ℂ) '' (d '' (f '' (e.source ∩ {z : ℂ | 0 ≤ (e z).im})))) := by
        rw [e.image_source_eq_target, himage, hcoord]
    _ = _ := by
        rw [Set.image_union, (hleft.mono hf_maps.image_subset).image_image]
        simp only [Set.image_image]

/-- **The charted reflection has nonvanishing derivative on the boundary arc.** Under the
hypotheses of the analytic-arc reflection principle, together with injectivity of `f` on the
closed positive side and the requirement that the open positive side goes to the open positive
side of the target arc, the derivative of the extension vanishes nowhere on `e.source`. At a
point of the arc this is a statement about the boundary behaviour of `f`, which is not assumed
differentiable there. -/
theorem deriv_chartedSchwarzReflection_ne_zero
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hupper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    {z : ℂ} (hz : z ∈ e.source) : deriv (chartedSchwarzReflection e d f) z ≠ 0 := by
  have hA : AnalyticAt ℂ (chartedSchwarzReflection e d f) z :=
    (differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm hd_symm hf_maps
      hf_cont hf_diff hf_real).analyticAt (e.open_source.mem_nhds hz)
  exact (exists_injOn_nhds_iff_deriv_ne_zero hA).mp
    ⟨e.source, e.open_source.mem_nhds hz,
      injOn_chartedSchwarzReflection_of_symmetric e d f he_symm hd_symm hf_maps hupper
        (fun w hw h => (hf_real w hw h).ge) hf_inj⟩

/-- **Schwarz reflection across an analytic arc of a conformal map is conformal.** Under the
hypotheses of the analytic-arc reflection principle, together with injectivity of `f` on the
closed positive side and the requirement that the open positive side goes to the open positive
side of the target arc, the extension is conformal at every point of `e.source` — in particular
at the points of the arc, where `f` itself is not assumed differentiable. -/
theorem conformalAt_chartedSchwarzReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hupper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    {z : ℂ} (hz : z ∈ e.source) : ConformalAt (chartedSchwarzReflection e d f) z :=
  TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn
    (differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm hd_symm hf_maps
      hf_cont hf_diff hf_real) e.open_source
    (injOn_chartedSchwarzReflection_of_symmetric e d f he_symm hd_symm hf_maps hupper
      (fun w hw h => (hf_real w hw h).ge) hf_inj) hz

/-- The inverse of the charted reflection extension is holomorphic on its image: the extension is
a biholomorphism of `e.source` onto the doubled image described by
`TauCeti.image_chartedSchwarzReflection_of_symmetric`. -/
theorem differentiableOn_invFunOn_chartedSchwarzReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hupper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    DifferentiableOn ℂ (Function.invFunOn (chartedSchwarzReflection e d f) e.source)
      (chartedSchwarzReflection e d f '' e.source) :=
  TauCeti.DifferentiableOn.invFunOn
    (differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm hd_symm hf_maps
      hf_cont hf_diff hf_real) e.open_source
    (injOn_chartedSchwarzReflection_of_symmetric e d f he_symm hd_symm hf_maps hupper
      (fun w hw h => (hf_real w hw h).ge) hf_inj)

/-- **The conformal reflection principle across an analytic arc**, packaged existential form: a
conformal map of the positive side of the source arc that carries the arc into the target arc and
its open positive side into the open positive side of the target arc extends to a *conformal* map
of the whole chart domain, agreeing with the original on the closed positive side and
intertwining the two chart-induced reflections. The explicit witness is
`chartedSchwarzReflection e d f`.

This strengthens `TauCeti.exists_differentiableOn_eqOn_chartedReflection_of_symmetric` by the
injectivity clause. -/
theorem exists_differentiableOn_injOn_eqOn_chartedReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hupper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F e.source ∧ InjOn F e.source ∧
      EqOn F f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) ∧
      ∀ z ∈ e.source,
        F (e.symm ((starRingEnd ℂ) (e z))) = d.symm ((starRingEnd ℂ) (d (F z))) :=
  ⟨chartedSchwarzReflection e d f,
    differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm hd_symm hf_maps
      hf_cont hf_diff hf_real,
    injOn_chartedSchwarzReflection_of_symmetric e d f he_symm hd_symm hf_maps hupper
      (fun w hw h => (hf_real w hw h).ge) hf_inj,
    fun _ hz => chartedSchwarzReflection_of_coord_im_nonneg e d f hf_maps hz.1 hz.2,
    fun _ hz => chartedSchwarzReflection_sourceReflection e d f he_symm hd_symm hf_maps hf_real hz⟩

end TauCeti
