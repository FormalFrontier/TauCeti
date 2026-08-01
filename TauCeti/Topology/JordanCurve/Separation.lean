/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic

/-!
# Two points cut a Jordan curve into two arcs

Removing one point from a Jordan curve leaves a connected set; removing two leaves exactly two
pieces. This file proves both, first for the model curve `Circle` and then for an arbitrary Jordan
curve by transport along the homeomorphism that `TauCeti.IsJordanCurve` provides.

## The argument on the circle

Both circle statements come straight out of Mathlib's arc API. For one point,
`Circle.isPathConnected_compl_singleton` already gives more than connectedness of the complement,
and is used directly. For two distinct points `z` and `w`,
Mathlib parametrizes the two arcs they determine by the paths `Circle.path z w` and
`Circle.path w z`, and records that the two ranges meet exactly in `{z, w}`
(`Circle.range_path_inter_range_path`) and that each open arc is the complement of the opposite
closed one (`Circle.compl_range_path`). So the two open arcs are complements of compact sets, hence
*open*, and they are connected as continuous images of `Set.Ioo 0 1`; openness is what makes the
pair a genuine separation rather than merely a partition.

## Why this is a layer-L5 prerequisite

Layer **L5** of the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`) is
Carathéodory's boundary correspondence, and the injectivity half of its hard direction argues by
contradiction: if the continuous extension of a Riemann map identified two distinct points of the
bounding circle, those two points would cut the circle into two arcs, and the geometry of the image
would force the extension to be constant on one of them — which
`TauCeti.not_eqOn_const_inter_sphere_of_injOn` in
`TauCeti/Analysis/Complex/Conformal/ArcConstancy.lean` rules out. That file records the missing
input explicitly: "two identified boundary points cut the circle into two arcs" is a statement about
the curve, not about the map. Mathlib cuts the *circle*; what this file adds is the same cutting for
an arbitrary Jordan curve, which is the generality the argument needs, since it applies the cutting
to `frontier Ω` — a Jordan curve, not a circle — on the image side.

## Generality

The Jordan-curve statements are for a subset of an arbitrary topological space, as in
`TauCeti/Topology/JordanCurve/Basic.lean`; no separation axiom is needed, because the curve carries
the subspace topology of a space homeomorphic to the circle and every hypothesis is checked there.
The corollaries for a circle `Metric.sphere c r` of `ℂ` are the case the conformal layers consume.

## Main results

* `TauCeti.IsJordanCurve.isConnected_diff_singleton` — a Jordan curve minus a point is connected;
  it is an *arc*, and in particular one point never separates the curve.
* `TauCeti.exists_isOpen_isConnected_union_eq_compl_pair_circle` — two distinct points cut the
  circle into two disjoint nonempty open connected arcs.
* `TauCeti.IsJordanCurve.exists_isConnected_union_eq_diff_pair` — the same for an arbitrary Jordan
  curve, together with the statement that the two arcs are its connected components: every
  preconnected subset of the cut curve lies in one of them.
* `TauCeti.IsJordanCurve.not_isPreconnected_diff_pair` — consequently two points always separate a
  Jordan curve.
* `TauCeti.isConnected_sphere_diff_singleton`,
  `TauCeti.exists_isConnected_union_eq_sphere_diff_pair` and
  `TauCeti.not_isPreconnected_sphere_diff_pair` — the three statements for a circle of `ℂ`, the
  form in which the bounding circle of a disc is cut.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Metric Set Topology

variable {X : Type*} [TopologicalSpace X] {C : Set X} {p q : X} {r : ℝ}

/-! ## Cutting the circle -/

/-- **Two distinct points cut the circle into two arcs.** The complement of `{z, w}` is the union
of two disjoint nonempty open connected sets, namely the two open arcs `Circle.path z w '' Ioo 0 1`
and `Circle.path w z '' Ioo 0 1` that Mathlib cuts the circle into.

Openness is the substantive part: it says the two arcs are a *separation* of `{z, w}ᶜ`, so that no
connected subset of the cut circle can meet both, which is how the pair is used. Each open arc is
the complement of the opposite closed arc by `Circle.compl_range_path`, hence open because a range
of a path is compact; and the two closed arcs meet in `{z, w}` by
`Circle.range_path_inter_range_path`, which is the union statement. -/
theorem exists_isOpen_isConnected_union_eq_compl_pair_circle {z w : Circle} (hzw : z ≠ w) :
    ∃ A B : Set Circle, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = ({z, w} : Set Circle)ᶜ := by
  have hcon : ∀ u v : Circle, IsConnected (Circle.path u v '' Ioo 0 1) := fun u v =>
    (isConnected_Ioo (by norm_num)).image _ (Circle.path u v).continuous.continuousOn
  have hA : Circle.path z w '' Ioo 0 1 = (range (Circle.path w z))ᶜ :=
    (Circle.compl_range_path hzw.symm).symm
  have hB : Circle.path w z '' Ioo 0 1 = (range (Circle.path z w))ᶜ :=
    (Circle.compl_range_path hzw).symm
  refine ⟨_, _, ?_, ?_, hcon z w, hcon w z, ?_, ?_⟩
  · rw [hA]; exact (isCompact_range (Circle.path w z).continuous).isClosed.isOpen_compl
  · rw [hB]; exact (isCompact_range (Circle.path z w).continuous).isClosed.isOpen_compl
  · rw [hA]; exact disjoint_compl_left_iff_subset.mpr (image_subset_range _ _)
  · rw [hA, hB, ← compl_inter, Circle.range_path_inter_range_path hzw.symm, pair_comm w z]

/-! ## Cutting a Jordan curve

Both statements below are the circle statement carried across the parametrization `jordanParam e`
of a Jordan curve by the circle, so its properties — continuity, injectivity, range, and that it is
inducing — are collected first. -/

/-- The parametrization of a Jordan curve by the circle underlying a homeomorphism `e`: the
composite of `e.symm` with the inclusion of the curve into the ambient space. -/
private noncomputable def jordanParam (e : C ≃ₜ Circle) : Circle → X :=
  fun u => ((e.symm u : C) : X)

private lemma continuous_jordanParam (e : C ≃ₜ Circle) : Continuous (jordanParam e) :=
  continuous_subtype_val.comp e.symm.continuous

private lemma injective_jordanParam (e : C ≃ₜ Circle) : Function.Injective (jordanParam e) :=
  Subtype.val_injective.comp e.symm.injective

private lemma isInducing_jordanParam (e : C ≃ₜ Circle) : Topology.IsInducing (jordanParam e) :=
  Topology.IsInducing.subtypeVal.comp e.symm.isInducing

private lemma range_jordanParam (e : C ≃ₜ Circle) : range (jordanParam e) = C := by
  refine subset_antisymm ?_ fun x hx => ⟨e ⟨x, hx⟩, by simp [jordanParam]⟩
  rintro _ ⟨u, rfl⟩
  exact (e.symm u).2

private lemma jordanParam_apply (e : C ≃ₜ Circle) (hp : p ∈ C) :
    jordanParam e (e ⟨p, hp⟩) = p := by
  simp [jordanParam]

/-- **A Jordan curve minus a point is connected**, being homeomorphic to the circle minus a point
(`Circle.isPathConnected_compl_singleton`). So a Jordan curve is *not* separated by any one of its
points; it takes two, by `TauCeti.IsJordanCurve.not_isPreconnected_diff_pair`. -/
theorem IsJordanCurve.isConnected_diff_singleton (h : IsJordanCurve C) (hp : p ∈ C) :
    IsConnected (C \ {p}) := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  have himg : jordanParam e '' ({e ⟨p, hp⟩}ᶜ) = C \ {p} := by
    rw [compl_eq_univ_sdiff, image_sdiff (injective_jordanParam e), image_univ, image_singleton,
      range_jordanParam, jordanParam_apply]
  exact himg ▸ (Circle.isPathConnected_compl_singleton _).isConnected.image _
    (continuous_jordanParam e).continuousOn

/-- **Two distinct points cut a Jordan curve into two arcs.** For `p ≠ q` on a Jordan curve `C`
there are two disjoint connected sets `A` and `B` with `A ∪ B = C \ {p, q}`, and they are the
connected components of the cut curve: every preconnected subset of `C \ {p, q}` lies inside one of
them.

The last clause is what makes the pair canonical, and is the form the Carathéodory boundary
argument uses: a connected set that avoids `p` and `q` cannot get from one arc to the other. It
comes from openness of the two arcs of the circle in
`TauCeti.exists_isOpen_isConnected_union_eq_compl_pair_circle`, transported along the
parametrization, which is an inducing map, so preconnectedness may be tested upstairs. -/
theorem IsJordanCurve.exists_isConnected_union_eq_diff_pair (h : IsJordanCurve C) (hp : p ∈ C)
    (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧ A ∪ B = C \ {p, q} ∧
      ∀ ⦃S : Set X⦄, S ⊆ C \ {p, q} → IsPreconnected S → S ⊆ A ∨ S ⊆ B := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  set g := jordanParam e with hg
  have hinj : Function.Injective g := injective_jordanParam e
  have hrange : range g = C := range_jordanParam e
  have hzw : e ⟨p, hp⟩ ≠ e ⟨q, hq⟩ := fun hh => hpq (congrArg Subtype.val (e.injective hh))
  obtain ⟨A₀, B₀, hA₀o, hB₀o, hA₀c, hB₀c, hdisj, hunion⟩ :=
    exists_isOpen_isConnected_union_eq_compl_pair_circle hzw
  have himg : g '' (A₀ ∪ B₀) = C \ {p, q} := by
    rw [hunion, compl_eq_univ_sdiff, image_sdiff hinj, image_univ, hrange]
    congr 1
    rw [image_insert_eq, image_singleton, hg, jordanParam_apply, jordanParam_apply]
  refine ⟨g '' A₀, g '' B₀, hA₀c.image _ (continuous_jordanParam e).continuousOn,
    hB₀c.image _ (continuous_jordanParam e).continuousOn,
    Set.disjoint_image_of_injective hinj hdisj, by rwa [← image_union], fun S hS hSc => ?_⟩
  have hSr : S ⊆ range g := hrange ▸ hS.trans sdiff_subset
  have hpre : IsPreconnected (g ⁻¹' S) := by
    rw [← (isInducing_jordanParam e).isPreconnected_image, image_preimage_eq_of_subset hSr]
    exact hSc
  have hsub : g ⁻¹' S ⊆ A₀ ∪ B₀ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ : g x ∈ g '' (A₀ ∪ B₀) := himg ▸ hS hx
    exact hinj hxy ▸ hy
  rcases hpre.subset_or_subset hA₀o hB₀o hdisj hsub with hc | hc
  · exact Or.inl (by rw [← image_preimage_eq_of_subset hSr]; exact image_mono hc)
  · exact Or.inr (by rw [← image_preimage_eq_of_subset hSr]; exact image_mono hc)

/-- **Two points separate a Jordan curve.** Removing two distinct points from a Jordan curve leaves
a set that is not preconnected: it splits into the two arcs of
`TauCeti.IsJordanCurve.exists_isConnected_union_eq_diff_pair`, each of which is nonempty, and a
preconnected set lying in one of them cannot contain the other. -/
theorem IsJordanCurve.not_isPreconnected_diff_pair (h : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C)
    (hpq : p ≠ q) : ¬ IsPreconnected (C \ {p, q}) := by
  obtain ⟨A, B, hAc, hBc, hdisj, hunion, hdich⟩ :=
    h.exists_isConnected_union_eq_diff_pair hp hq hpq
  intro hcon
  obtain ⟨x, hx⟩ := hAc.nonempty
  obtain ⟨y, hy⟩ := hBc.nonempty
  rcases hdich subset_rfl hcon with hc | hc
  · exact Set.disjoint_left.mp hdisj (hc (hunion ▸ mem_union_right _ hy)) hy
  · exact Set.disjoint_left.mp hdisj hx (hc (hunion ▸ mem_union_left _ hx))

/-! ## The circles of `ℂ` -/

/-- **A circle of `ℂ` minus a point is connected**, being a Jordan curve
(`TauCeti.isJordanCurve_sphere`). This is the boundary circle of a disc with one boundary point
removed, the set the Carathéodory boundary argument works on. -/
theorem isConnected_sphere_diff_singleton (c : ℂ) (hr : 0 < r) {z : ℂ} (hz : z ∈ sphere c r) :
    IsConnected (sphere c r \ {z}) :=
  (isJordanCurve_sphere c hr).isConnected_diff_singleton hz

/-- **Two points cut a circle of `ℂ` into two arcs.** This is
`TauCeti.IsJordanCurve.exists_isConnected_union_eq_diff_pair` for the bounding circle of a disc,
which is the curve the Carathéodory boundary argument cuts: a connected set of boundary points
avoiding `z` and `w` lies in one of the two arcs they determine. -/
theorem exists_isConnected_union_eq_sphere_diff_pair (c : ℂ) (hr : 0 < r) {z w : ℂ}
    (hz : z ∈ sphere c r) (hw : w ∈ sphere c r) (hzw : z ≠ w) :
    ∃ A B : Set ℂ, IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧ A ∪ B = sphere c r \ {z, w} ∧
      ∀ ⦃S : Set ℂ⦄, S ⊆ sphere c r \ {z, w} → IsPreconnected S → S ⊆ A ∨ S ⊆ B :=
  (isJordanCurve_sphere c hr).exists_isConnected_union_eq_diff_pair hz hw hzw

/-- **Two points separate a circle of `ℂ`**: removing two distinct points of `Metric.sphere c r`
leaves a set that is not preconnected. -/
theorem not_isPreconnected_sphere_diff_pair (c : ℂ) (hr : 0 < r) {z w : ℂ} (hz : z ∈ sphere c r)
    (hw : w ∈ sphere c r) (hzw : z ≠ w) : ¬ IsPreconnected (sphere c r \ {z, w}) :=
  (isJordanCurve_sphere c hr).not_isPreconnected_diff_pair hz hw hzw

end TauCeti
