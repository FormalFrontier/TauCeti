/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-!
# The Schwarz reflection principle across an analytic arc

This file transports the real-axis Schwarz reflection principle through biholomorphic coordinate
charts. An `OpenPartialHomeomorph ℂ ℂ` whose forward map is holomorphic on its source is a
biholomorphic chart: injectivity and the holomorphic inverse theorem make its inverse holomorphic
on the target. The inverse image of the real axis under such a chart is therefore locally a
real-analytic arc.

For source and target charts `e` and `d`, `chartedSchwarzReflection e d f` straightens the source
arc with `e`, applies `d` to the values, uses real-axis reflection in the two coordinate domains,
and then maps back with `d.symm`. The coordinate domains are assumed invariant under conjugation.
The main theorem proves that this explicit extension is holomorphic throughout `e.source`; its
packaged form also records agreement with the original branch and the induced reflection
symmetry.

This proves the analytic-arc part of layer L4 in the conformal-mapping roadmap. It follows the
standard reduction of reflection across an analytic arc to reflection across the real axis; see
Ahlfors, *Complex Analysis*, Chapters 4--6. The underlying real-axis theorem is
`TauCeti.differentiableOn_schwarzReflection_of_symmetric`.
-/

public section

namespace TauCeti

open Complex Set
open scoped ComplexConjugate

variable (e d : OpenPartialHomeomorph ℂ ℂ) (f : ℂ → ℂ)

/-- The Schwarz-reflection extension transported through source and target biholomorphic charts.

The source chart `e` straightens the source arc, and the target chart `d` straightens the target
arc. Thus the middle function in real-axis coordinates is `w ↦ d (f (e.symm w))`. The definition
is total, while its characteristic properties only concern the sources and targets of the two
partial homeomorphisms. -/
noncomputable def chartedSchwarzReflection (z : ℂ) : ℂ :=
  d.symm
    (schwarzReflection (fun w => d (f (e.symm w))) (e z))

/-- The defining formula for Schwarz reflection transported through biholomorphic charts. -/
theorem chartedSchwarzReflection_def (z : ℂ) :
    chartedSchwarzReflection e d f z =
      d.symm (schwarzReflection (fun w => d (f (e.symm w))) (e z)) :=
  (rfl)

/-- The inverse chart preserves a cut expressed in chart coordinates. -/
private theorem mapsTo_symm_inter_im {P : ℝ → Prop} :
    MapsTo e.symm (e.target ∩ {w : ℂ | P w.im})
      (e.source ∩ {z : ℂ | P (e z).im}) := by
  rintro w ⟨hw, hP⟩
  exact ⟨e.map_target hw, by simpa only [Set.mem_ofPred_eq, e.right_inv hw] using hP⟩

/-- If both coordinate domains are conjugation-invariant, the reflected coordinate values stay
in the target coordinate domain. -/
private theorem mapsTo_schwarzReflection (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source) :
    MapsTo (schwarzReflection (fun w => d (f (e.symm w)))) e.target d.target := by
  intro w hw
  by_cases him : 0 ≤ w.im
  · rw [schwarzReflection_of_im_nonneg him]
    exact d.map_source (hf (mapsTo_symm_inter_im e ⟨hw, him⟩))
  · have him_neg : w.im < 0 := lt_of_not_ge him
    rw [schwarzReflection_of_im_neg him_neg]
    apply hd_symm
    apply d.map_source
    apply hf
    refine mapsTo_symm_inter_im e ⟨he_symm hw, ?_⟩
    rw [Set.mem_ofPred_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
    exact neg_nonneg.mpr him_neg.le

/-- Charted Schwarz reflection maps the source chart domain into the target chart domain. -/
theorem mapsTo_chartedSchwarzReflection (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source) :
    MapsTo (chartedSchwarzReflection e d f) e.source d.source := by
  intro z hz
  rw [chartedSchwarzReflection_def]
  exact d.map_target
    (mapsTo_schwarzReflection e d f he_symm hd_symm hf (e.map_source hz))

/-- On the closed positive side of the source arc, charted Schwarz reflection agrees with the
original function. -/
@[simp]
theorem chartedSchwarzReflection_of_coord_im_nonneg
    (hf : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    {z : ℂ} (hz : z ∈ e.source) (him : 0 ≤ (e z).im) :
    chartedSchwarzReflection e d f z = f z := by
  rw [chartedSchwarzReflection_def, schwarzReflection_of_im_nonneg him,
    e.left_inv hz, d.left_inv (hf ⟨hz, him⟩)]

/-- On the negative side of the source arc, charted Schwarz reflection is obtained by reflecting
the argument and value in the two coordinate charts. -/
@[simp]
theorem chartedSchwarzReflection_of_coord_im_neg {z : ℂ} (him : (e z).im < 0) :
    chartedSchwarzReflection e d f z =
      d.symm ((starRingEnd ℂ) (d (f (e.symm ((starRingEnd ℂ) (e z)))))) := by
  rw [chartedSchwarzReflection_def, schwarzReflection_of_im_neg him]

/-- In source coordinates, the original branch is continuous on the closed upper half-plane. -/
private theorem continuousOn_in_coordinates
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    ContinuousOn (fun w => d (f (e.symm w)))
      (e.target ∩ {w : ℂ | 0 ≤ w.im}) := by
  have he_inv := TauCeti.OpenPartialHomeomorph.differentiableOn_symm he
  have hfe : ContinuousOn (f ∘ e.symm) (e.target ∩ {w : ℂ | 0 ≤ w.im}) :=
    hf.comp (he_inv.mono inter_subset_left).continuousOn (mapsTo_symm_inter_im e)
  exact hd.continuousOn.comp hfe fun w hw =>
    hf_maps (mapsTo_symm_inter_im e hw)

/-- In source coordinates, the original branch is holomorphic on the open upper half-plane. -/
private theorem differentiableOn_in_coordinates
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im})) :
    DifferentiableOn ℂ (fun w => d (f (e.symm w)))
      (e.target ∩ {w : ℂ | 0 < w.im}) := by
  have he_inv := TauCeti.OpenPartialHomeomorph.differentiableOn_symm he
  have hfe : DifferentiableOn ℂ (f ∘ e.symm) (e.target ∩ {w : ℂ | 0 < w.im}) :=
    hf.comp (he_inv.mono inter_subset_left) (mapsTo_symm_inter_im e)
  refine hd.comp hfe fun w hw => hf_maps ?_
  rcases hw with ⟨hw_target, hw_im⟩
  simp only [Set.mem_ofPred_eq] at hw_im
  apply mapsTo_symm_inter_im e
  exact ⟨hw_target, hw_im.le⟩

/-- The real-boundary condition for the original branch becomes the usual real-axis condition in
the two coordinate charts. -/
private theorem apply_im_eq_zero_in_coordinates
    (hf : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0) :
    ∀ w ∈ e.target, w.im = 0 → (d (f (e.symm w))).im = 0 := by
  intro w hw him
  apply hf (e.symm w) (e.map_target hw)
  simpa only [e.right_inv hw] using him

/-- **Schwarz reflection across an analytic arc.** Let `e` and `d` be holomorphic open partial
homeomorphisms whose coordinate domains are invariant under conjugation. If `f` is continuous on
the closed positive side of the source arc, holomorphic on its open positive side, maps that side
into the source of `d`, and maps the arc into the target arc, then its charted Schwarz-reflection
extension is holomorphic throughout the source of `e`.

The source and target arcs are the inverse images of the real axis under `e` and `d`. Holomorphy
of the inverse charts is a consequence of holomorphy and injectivity of their forward maps, so it
is not imposed as an additional hypothesis. -/
theorem differentiableOn_chartedSchwarzReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0) :
    DifferentiableOn ℂ (chartedSchwarzReflection e d f) e.source := by
  let g := fun w => d (f (e.symm w))
  have hg : DifferentiableOn ℂ (schwarzReflection g) e.target :=
    differentiableOn_schwarzReflection_of_symmetric e.open_target he_symm
      (continuousOn_in_coordinates e d f he hd hf_maps hf_cont)
      (differentiableOn_in_coordinates e d f he hd hf_maps hf_diff)
      (apply_im_eq_zero_in_coordinates e d f hf_real)
  have hge : DifferentiableOn ℂ (fun z => schwarzReflection g (e z)) e.source :=
    hg.comp he e.mapsTo
  have hd_inv := TauCeti.OpenPartialHomeomorph.differentiableOn_symm hd
  have hresult : DifferentiableOn ℂ (fun z => d.symm (schwarzReflection g (e z))) e.source :=
    hd_inv.comp hge (mapsTo_schwarzReflection e d f he_symm hd_symm hf_maps |>.comp e.mapsTo)
  exact hresult.congr fun z _ => chartedSchwarzReflection_def e d f z

/-- Charted Schwarz reflection intertwines the source and target reflections induced by the two
biholomorphic charts. -/
theorem chartedSchwarzReflection_sourceReflection
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0) {z : ℂ} (hz : z ∈ e.source) :
    chartedSchwarzReflection e d f
        (e.symm ((starRingEnd ℂ) (e z))) =
      d.symm ((starRingEnd ℂ) (d (chartedSchwarzReflection e d f z))) := by
  let g := fun w => d (f (e.symm w))
  have hez : e z ∈ e.target := e.map_source hz
  have hconj_ez : (starRingEnd ℂ) (e z) ∈ e.target := he_symm hez
  have hreflected : schwarzReflection g (e z) ∈ d.target :=
    mapsTo_schwarzReflection e d f he_symm hd_symm hf_maps hez
  have hgreal : (e z).im = 0 → (g (e z)).im = 0 := by
    intro him
    simpa only [g, e.left_inv hz] using hf_real z hz him
  rw [chartedSchwarzReflection_def, e.right_inv hconj_ez,
    schwarzReflection_conj (f := g) (e z) hgreal, chartedSchwarzReflection_def,
    d.right_inv hreflected]

/-- **Packaged Schwarz reflection across an analytic arc.** Under the hypotheses of
`differentiableOn_chartedSchwarzReflection_of_symmetric`, there is a holomorphic extension that
agrees with the original function on the closed positive side and intertwines the source and
target reflections induced by the charts. The witness is `chartedSchwarzReflection e d f`. -/
theorem exists_differentiableOn_eqOn_chartedReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F e.source ∧
      EqOn F f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) ∧
      ∀ z ∈ e.source,
        F (e.symm ((starRingEnd ℂ) (e z))) =
          d.symm ((starRingEnd ℂ) (d (F z))) := by
  refine ⟨chartedSchwarzReflection e d f,
    differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm hd_symm
      hf_maps hf_cont hf_diff hf_real, ?_, ?_⟩
  · intro z hz
    exact chartedSchwarzReflection_of_coord_im_nonneg e d f hf_maps hz.1 hz.2
  · intro z hz
    exact chartedSchwarzReflection_sourceReflection e d f he_symm hd_symm hf_maps hf_real hz

end TauCeti
