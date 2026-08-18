/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Chart

/-!
# Local collars of a manifold with boundary

`Boundary.Collar.Chart` reads a manifold with boundary in tangential and inward-normal
coordinates, and `Boundary.Collar.Manifold` proves those coordinates are a `C^k` atlas. What they
do not provide is a *collar*: the target of a collar chart is an arbitrary open subset of the
product model, so it does not exhibit any neighbourhood as a product. This file shrinks a collar
chart around a boundary point until its target is a genuine product box `V × [0, ε)`, and reads
off the resulting local product structure.

The shrinking is the elementary half of the collar-neighbourhood theorem: the boxes `V × [0, ε)`
are a neighbourhood basis of a point of the product model lying on the boundary factor, because
the sets `[0, ε)` are a neighbourhood basis of the origin of the one-dimensional half-space
model. The remaining, global half is to patch these boxes into a single neighbourhood of the whole
boundary, which is what Hirsch's bump-function argument does and what this file does not do.

## Main definitions

* `TauCeti.EuclideanHalfSpace.normalRay`: the inward normal ray `[0, ∞) → EuclideanHalfSpace 1`,
  the parametrization by which the one-dimensional half-space model is a half-line.
* `TauCeti.EuclideanHalfSpace.normalIio`: the initial segment `[0, ε)` of the one-dimensional
  half-space model, cut out by the normal coordinate.
* `TauCeti.IsProductCollarChart`: a collar chart whose target is a product box `V × [0, ε)`, is
  `C^k` in both directions, and cuts out the boundary as the zero slice of its normal coordinate.
* `TauCeti.EuclideanHalfSpace.homeomorphNormalIio`: that segment, read by its normal coordinate
  as the real interval `[0, ε)`.
* `TauCeti.IsProductCollarChart.homeomorphProd`: the local collar itself, a homeomorphism of the
  source of a product collar chart onto (its part of) the boundary times `[0, ε)`.

## Main results

* `TauCeti.EuclideanHalfSpace.exists_normalIio_subset`: the segments `[0, ε)` are a neighbourhood
  basis of the origin of the one-dimensional half-space model.
* `TauCeti.exists_isProductCollarChart_of_mem_boundary`: **every boundary point has a product
  collar chart.** This is the shrinking step.
* `TauCeti.IsProductCollarChart.image_source_inter_boundary`: a product collar chart carries the
  boundary onto the zero slice `V × {0}` of its box.
* `TauCeti.IsProductCollarChart.map_homeomorphProd_fst`: the first component of the local collar
  is the boundary retraction, in coordinates the map setting the normal coordinate to zero.
* `TauCeti.exists_homeomorph_prod_Ico_of_mem_boundary`: **a boundary point has a neighbourhood
  `U` homeomorphic to `(U ∩ ∂M) × [0, ε)`**, the local collar neighbourhood.

## Implementation notes

The height `ε` of the box is kept as a parameter rather than normalised to `1`. Rescaling the
normal coordinate is a diffeomorphism of the model half-space, so nothing is lost, and carrying
`ε` avoids inserting a rescaling into every chart produced here; the patching step chooses its own
heights anyway.

`TauCeti.IsProductCollarChart.homeomorphProd` is only a homeomorphism, not a diffeomorphism: its
target `(U ∩ ∂M) × [0, ε)` is a product of a piece of the boundary manifold of
`Boundary.Charts` with an interval, and identifying that manifold structure with the one the
chart transports is a separate step. What is smooth here is the chart itself, through
`IsProductCollarChart.contMDiffOn` and `IsProductCollarChart.contMDiffOn_symm`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Theorem 6.1 (the collar
  neighbourhood theorem, whose local half is proved here).
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public section

noncomputable section

open Function Set Topology WithLp

open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

/-- The inward normal ray of the one-dimensional half-space model: the point of
`EuclideanHalfSpace 1` at normal distance `r` from the boundary, for `r ≤ 0` the origin.

Truncating at `0` is what makes the ray a globally defined continuous map on `ℝ`; it is used
only for `0 ≤ r`, where `normalRay_normalCoord` inverts it. -/
def normalRay (r : ℝ) : EuclideanHalfSpace 1 := ⟨toLp 2 fun _ ↦ max r 0, le_max_right r 0⟩

/-- The normal coordinate of a point of the normal ray. -/
@[simp]
theorem normalRay_coe_apply (r : ℝ) : (normalRay r).1 0 = max r 0 := (rfl)

/-- The origin of the one-dimensional half-space model has vanishing normal coordinate. -/
@[simp]
theorem val_zero_apply : (0 : EuclideanHalfSpace 1).1 0 = 0 := (rfl)

/-- The normal ray starts at the origin. -/
@[simp]
theorem normalRay_zero : normalRay 0 = 0 := by
  refine EuclideanHalfSpace.ext _ _ ?_
  ext i
  rw [Subsingleton.elim i 0]
  simp [normalRay]

/-- The normal ray parametrizes the one-dimensional half-space model by its normal coordinate. -/
@[simp]
theorem normalRay_normalCoord (t : EuclideanHalfSpace 1) : normalRay (t.1 0) = t := by
  refine EuclideanHalfSpace.ext _ _ ?_
  ext i
  rw [Subsingleton.elim i 0]
  simp [normalRay, max_eq_left t.2]

/-- The normal ray is continuous. -/
theorem continuous_normalRay : Continuous normalRay := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

/-- A point of the one-dimensional half-space model vanishes exactly when its normal coordinate
does. -/
theorem eq_zero_iff {t : EuclideanHalfSpace 1} : t = 0 ↔ t.1 0 = 0 := by
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  rw [← normalRay_normalCoord t, h, normalRay_zero]

/-- The initial segment `[0, ε)` of the one-dimensional half-space model: the points whose normal
coordinate is smaller than `ε`. It is empty for `ε ≤ 0`, and is the model factor of the collar
boxes below. -/
def normalIio (ε : ℝ) : Set (EuclideanHalfSpace 1) := {t | t.1 0 < ε}

/-- Membership in the initial segment is one inequality on the normal coordinate. -/
@[simp]
theorem mem_normalIio {ε : ℝ} {t : EuclideanHalfSpace 1} : t ∈ normalIio ε ↔ t.1 0 < ε := (Iff.rfl)

/-- The initial segments are open, being sublevel sets of the continuous normal coordinate. -/
theorem isOpen_normalIio (ε : ℝ) : IsOpen (normalIio ε) := by
  have : Continuous fun t : EuclideanHalfSpace 1 ↦ t.1 0 := by fun_prop
  exact isOpen_Iio.preimage this

/-- An initial segment of positive height contains the origin.

Not `@[simp]`: `mem_normalIio` and `val_zero_apply` already reduce this to `0 < ε`. -/
theorem zero_mem_normalIio {ε : ℝ} (hε : 0 < ε) : (0 : EuclideanHalfSpace 1) ∈ normalIio ε := by
  rw [mem_normalIio]
  simpa using hε

/-- An initial segment of positive height is nonempty. -/
theorem nonempty_normalIio {ε : ℝ} (hε : 0 < ε) : (normalIio ε).Nonempty :=
  ⟨0, zero_mem_normalIio hε⟩

/-- **The segments `[0, ε)` are a neighbourhood basis of the origin** of the one-dimensional
half-space model. This is the only point-set input to the shrinking step: it is what turns an
arbitrary neighbourhood of a boundary point into a product box. -/
theorem exists_normalIio_subset {W : Set (EuclideanHalfSpace 1)} (hW : IsOpen W)
    (h0 : (0 : EuclideanHalfSpace 1) ∈ W) : ∃ ε, 0 < ε ∧ normalIio ε ⊆ W := by
  have hpre : IsOpen (normalRay ⁻¹' W) := hW.preimage continuous_normalRay
  have h0' : (0 : ℝ) ∈ normalRay ⁻¹' W := by simpa using h0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0'
  refine ⟨ε, hε, fun t ht ↦ ?_⟩
  have hmem : t.1 0 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg t.2]
    exact ht
  have := hball hmem
  rwa [mem_preimage, normalRay_normalCoord] at this

/-- **The initial segment `[0, ε)` of the one-dimensional half-space model is the real interval
`[0, ε)`**, by the normal coordinate. It is the identification through which a local collar reads
as a product with a half-open interval. -/
def homeomorphNormalIio (ε : ℝ) : ↥(normalIio ε) ≃ₜ ↥(Set.Ico (0 : ℝ) ε) where
  toEquiv :=
    { toFun := fun t ↦ ⟨t.1.1 0, t.1.2, mem_normalIio.1 t.2⟩
      invFun := fun r ↦ ⟨normalRay r.1, by
        rw [mem_normalIio, normalRay_coe_apply, max_eq_left r.2.1]
        exact r.2.2⟩
      left_inv := fun t ↦ Subtype.ext (normalRay_normalCoord t.1)
      right_inv := fun r ↦ Subtype.ext (by
        have hr : (normalRay r.1).1 0 = r.1 := by
          rw [normalRay_coe_apply, max_eq_left r.2.1]
        exact hr) }
  continuous_toFun := by fun_prop
  continuous_invFun := (continuous_normalRay.comp continuous_subtype_val).subtype_mk _

/-- The interval identification is the normal coordinate. -/
@[simp]
theorem coe_homeomorphNormalIio {ε : ℝ} (t : ↥(normalIio ε)) :
    (homeomorphNormalIio ε t : ℝ) = t.1.1 0 := (rfl)

end EuclideanHalfSpace

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- A **product collar chart** on a manifold with boundary: a `C^k` chart in tangential and
inward-normal coordinates whose target is a box `V × [0, ε)`, and in which the boundary is the
zero slice of the normal coordinate.

Unlike `TauCeti.collarChart`, whose target is whatever open set the ambient chart happens to have,
the target here is a product, so the source is a product neighbourhood: that is what makes such a
chart a *local collar*, `TauCeti.IsProductCollarChart.homeomorphProd`.

The regularity `k` is an argument rather than a field of the chart, so that one chart can be a
product collar chart at several regularities. -/
structure IsProductCollarChart (k : WithTop ℕ∞)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1))
    (V : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) : Prop where
  /-- The collar has positive height. -/
  height_pos : 0 < ε
  /-- The chart is onto the product box `V × [0, ε)`. -/
  target_eq : φ.target = V ×ˢ EuclideanHalfSpace.normalIio ε
  /-- The chart is `C^k`. -/
  contMDiffOn : ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k φ φ.source
  /-- The inverse of the chart is `C^k`. -/
  contMDiffOn_symm : ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k φ.symm φ.target
  /-- The boundary is the zero slice of the normal coordinate. -/
  mem_boundary_iff : ∀ y ∈ φ.source, y ∈ (𝓡∂ (n + 1)).boundary M ↔ (φ y).2.1 0 = 0

namespace IsProductCollarChart

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)}
  {V : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ}

/-- The base of a product collar chart is open: it is a factor of the open target. -/
theorem isOpen_base (h : IsProductCollarChart k φ V ε) : IsOpen V := by
  have hopen : IsOpen (V ×ˢ EuclideanHalfSpace.normalIio ε) := h.target_eq ▸ φ.open_target
  rcases isOpen_prod_iff'.1 hopen with ⟨hV, -⟩ | hV | hW
  · exact hV
  · rw [hV]
    exact isOpen_empty
  · exact absurd (EuclideanHalfSpace.nonempty_normalIio h.height_pos) (by rw [hW]; simp)

/-- **A product collar chart carries the boundary onto the zero slice of its box.** -/
theorem image_source_inter_boundary (h : IsProductCollarChart k φ V ε) :
    φ '' (φ.source ∩ (𝓡∂ (n + 1)).boundary M) = V ×ˢ ({0} : Set (EuclideanHalfSpace 1)) := by
  ext p
  constructor
  · rintro ⟨y, ⟨hy, hyb⟩, rfl⟩
    have hmem : φ y ∈ V ×ˢ EuclideanHalfSpace.normalIio ε :=
      h.target_eq ▸ φ.map_source hy
    exact ⟨hmem.1, EuclideanHalfSpace.eq_zero_iff.2 ((h.mem_boundary_iff y hy).1 hyb)⟩
  · rintro ⟨hp1, hp2⟩
    have hp : p ∈ φ.target := by
      rw [h.target_eq]
      refine ⟨hp1, ?_⟩
      rw [show p.2 = 0 from hp2]
      exact EuclideanHalfSpace.zero_mem_normalIio h.height_pos
    refine ⟨φ.symm p, ⟨φ.map_target hp, ?_⟩, φ.right_inv hp⟩
    rw [h.mem_boundary_iff _ (φ.map_target hp), φ.right_inv hp, show p.2 = 0 from hp2]
    rfl

/-- The boundary points of the source of a product collar chart, as a subtype, are homeomorphic
to its base. -/
def homeomorphBase (h : IsProductCollarChart k φ V ε) :
    ↥(φ.source ∩ (𝓡∂ (n + 1)).boundary M) ≃ₜ ↥V :=
  (φ.homeomorphOfImageSubsetSource inter_subset_left h.image_source_inter_boundary).trans
    ((Homeomorph.Set.prod V ({0} : Set (EuclideanHalfSpace 1))).trans (Homeomorph.prodUnique _ _))

/-- The identification of the boundary part with the base is the tangential coordinate. -/
@[simp]
theorem coe_homeomorphBase (h : IsProductCollarChart k φ V ε)
    (y : ↥(φ.source ∩ (𝓡∂ (n + 1)).boundary M)) : (h.homeomorphBase y : _) = (φ y).1 := (rfl)

/-- **The local collar.** A product collar chart splits its source as the product of its part of
the boundary with the interval `[0, ε)`. -/
def homeomorphProd (h : IsProductCollarChart k φ V ε) :
    ↥φ.source ≃ₜ ↥(φ.source ∩ (𝓡∂ (n + 1)).boundary M) × ↥(EuclideanHalfSpace.normalIio ε) :=
  ((φ.toHomeomorphSourceTarget.trans (Homeomorph.setCongr h.target_eq)).trans
      (Homeomorph.Set.prod V (EuclideanHalfSpace.normalIio ε))).trans
    (h.homeomorphBase.symm.prodCongr (Homeomorph.refl _))

/-- The second component of the local collar is the normal coordinate. -/
@[simp]
theorem coe_homeomorphProd_snd (h : IsProductCollarChart k φ V ε) (y : ↥φ.source) :
    ((h.homeomorphProd y).2 : EuclideanHalfSpace 1) = (φ y).2 := (rfl)

/-- **The first component of the local collar is the boundary retraction**: in coordinates it
sets the normal coordinate to zero. Together with `coe_homeomorphProd_snd` this pins the
homeomorphism down: it is the chart, read in the box. -/
theorem map_homeomorphProd_fst (h : IsProductCollarChart k φ V ε) (y : ↥φ.source) :
    φ ((h.homeomorphProd y).1 : M) = ((φ y).1, 0) := by
  have hmem : ((φ y).1, (0 : EuclideanHalfSpace 1)) ∈ φ.target := by
    rw [h.target_eq]
    exact ⟨(h.target_eq ▸ φ.map_source y.2).1, EuclideanHalfSpace.zero_mem_normalIio h.height_pos⟩
  exact φ.right_inv hmem

end IsProductCollarChart

variable [IsManifold (𝓡∂ (n + 1)) k M]

/-- **Every boundary point has a product collar chart.** Shrinking the collar chart of the
preferred ambient chart until its target is a box `V × [0, ε)` is possible because the target is
open and the boundary point is read in it as a point of the zero slice, where the boxes are a
neighbourhood basis.

This is the local half of the collar neighbourhood theorem; the global statement patches these
boxes along the whole boundary. -/
theorem exists_isProductCollarChart_of_mem_boundary (hk : k ≠ 0) {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    ∃ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1))
      (V : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ),
      x ∈ φ.source ∧ IsProductCollarChart k φ V ε := by
  set e := chartAt (EuclideanHalfSpace (n + 1)) x
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hxs : x ∈ (collarChart e).source := by rwa [collarChart_source]
  -- the boundary point is read in the collar chart as a point of the zero slice
  have hx0 : (collarChart e x).2 = 0 :=
    EuclideanHalfSpace.eq_zero_iff.2
      ((mem_boundary_iff_collarChart_snd_apply_zero_eq_zero hk (chart_mem_atlas _ x) hxe).1 hx)
  have hxt : ((collarChart e x).1, (collarChart e x).2) ∈ (collarChart e).target :=
    (collarChart e).map_source hxs
  -- shrink an ambient box to a box of the form `V × [0, ε)`
  obtain ⟨V, W, hV, hW, hxV, hxW, hVW⟩ :=
    isOpen_prod_iff.1 (collarChart e).open_target _ _ hxt
  obtain ⟨ε, hε, hεW⟩ :=
    EuclideanHalfSpace.exists_normalIio_subset hW (by rwa [← hx0])
  have hBopen : IsOpen (V ×ˢ EuclideanHalfSpace.normalIio ε) :=
    hV.prod (EuclideanHalfSpace.isOpen_normalIio ε)
  have hBsub : V ×ˢ EuclideanHalfSpace.normalIio ε ⊆ (collarChart e).target :=
    fun p hp ↦ hVW ⟨hp.1, hεW hp.2⟩
  set φ := ((collarChart e).symm.restrOpen _ hBopen).symm with hφ
  have hcoe : ⇑φ = ⇑(collarChart e) := by simp [hφ]
  have hcoe_symm : ⇑φ.symm = ⇑(collarChart e).symm := by simp [hφ]
  have hsource : φ.source = (collarChart e).source ∩ collarChart e ⁻¹' (V ×ˢ
      EuclideanHalfSpace.normalIio ε) := rfl
  have htarget : φ.target = V ×ˢ EuclideanHalfSpace.normalIio ε := by
    have hinter : φ.target =
        (collarChart e).target ∩ (V ×ˢ EuclideanHalfSpace.normalIio ε) := rfl
    rw [hinter, inter_eq_self_of_subset_right hBsub]
  have hxφ : x ∈ φ.source := by
    refine hsource ▸ ⟨hxs, hxV, ?_⟩
    rw [hx0]
    exact EuclideanHalfSpace.zero_mem_normalIio hε
  have hsub : φ.source ⊆ e.source := fun y hy ↦ by
    have hys := (hsource ▸ hy).1
    rwa [collarChart_source] at hys
  refine ⟨φ, V, ε, hxφ, hε, htarget, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact (contMDiffOn_collarChart (IsManifold.chart_mem_maximalAtlas x)).mono hsub
  · rw [hcoe_symm, htarget]
    exact (contMDiffOn_collarChart_symm (IsManifold.chart_mem_maximalAtlas x)).mono hBsub
  · intro y hy
    rw [hcoe]
    exact mem_boundary_iff_collarChart_snd_apply_zero_eq_zero hk (chart_mem_atlas _ x) (hsub hy)

/-- **A local collar neighbourhood of a boundary point.** Every boundary point of a `C^k`
manifold with boundary, `k ≠ 0`, has an open neighbourhood `U` homeomorphic to the product of its
part `U ∩ ∂M` of the boundary with a half-open interval `[0, ε)`.

This is the local collar; the collar neighbourhood theorem is the statement that the `U` can be
taken to be a single neighbourhood of the whole boundary, with `U ∩ ∂M = ∂M`. -/
theorem exists_homeomorph_prod_Ico_of_mem_boundary (hk : k ≠ 0) {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    ∃ (U : Set M) (ε : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ε ∧
      Nonempty (↥U ≃ₜ ↥(U ∩ (𝓡∂ (n + 1)).boundary M) × ↥(Set.Ico (0 : ℝ) ε)) := by
  obtain ⟨φ, V, ε, hxφ, h⟩ := exists_isProductCollarChart_of_mem_boundary hk hx
  exact ⟨φ.source, ε, φ.open_source, hxφ, h.height_pos,
    ⟨h.homeomorphProd.trans
      ((Homeomorph.refl _).prodCongr (EuclideanHalfSpace.homeomorphNormalIio ε))⟩⟩

end TauCeti
