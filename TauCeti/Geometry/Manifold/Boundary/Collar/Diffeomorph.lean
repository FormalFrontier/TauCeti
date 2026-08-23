/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# Smooth local collars of a manifold with boundary

`Boundary.Collar.Local` shrinks collar coordinates around a boundary point to a product box and
splits the source of the resulting chart as a product, `IsProductCollarChart.homeomorphProdOpens`,
whose three factors — the source, its part of the boundary, and the normal interval — are read as
open subspaces. That splitting is only a homeomorphism. This file constructs the corresponding
smooth product decomposition for the canonical manifold structure on the boundary.

For a product collar chart `φ`, the diffeomorphism
`TauCeti.IsProductCollarChart.diffeomorphProd` sends a point to its boundary retraction and normal
coordinate. Its underlying equivalence is the one of
`TauCeti.IsProductCollarChart.homeomorphProdOpens`, so no topological content is reproved here;
what is new is that both directions are `C^k`. Its inverse combines a boundary point and a normal
coordinate and reads the resulting pair back through `φ`.

This is the smooth local-product step in the collar-neighbourhood target of Layer 1 of the
`GeometricTopology` roadmap. The global collar theorem still requires patching these local
diffeomorphisms along the whole boundary.

## Main definitions

* `TauCeti.IsProductCollarChart.diffeomorphProd`: the canonical smooth local collar.

## Main results

* `TauCeti.IsProductCollarChart.contMDiff_boundaryRetract`: the boundary retraction of a product
  collar chart is `C^k`.
* `TauCeti.IsProductCollarChart.map_diffeomorphProd_fst` and
  `TauCeti.IsProductCollarChart.coe_diffeomorphProd_snd`: the forward coordinate formulas.
* `TauCeti.IsProductCollarChart.map_diffeomorphProd_symm`: the inverse coordinate formula.
* `TauCeti.IsProductCollarChart.diffeomorphProd_apply_of_mem_boundary`: the local collar fixes the
  boundary and gives it normal coordinate zero.
* `TauCeti.IsProductCollarChart.coe_diffeomorphProd`: the smooth local collar has the same
  underlying map as the topological one, so all of the latter's coordinate formulas transfer.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Theorem 6.1.
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

namespace IsProductCollarChart

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)}
  {V : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ}

private theorem contMDiffAt_chart (h : IsProductCollarChart k φ V ε) {y : M} (hy : y ∈ φ.source) :
    ContMDiffAt (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k φ y :=
  (h.contMDiffOn y hy).contMDiffAt (φ.open_source.mem_nhds hy)

private theorem contMDiffAt_chart_symm (h : IsProductCollarChart k φ V ε)
    {p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1} (hp : p ∈ φ.target) :
    ContMDiffAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k φ.symm p :=
  (h.contMDiffOn_symm p hp).contMDiffAt (φ.open_target.mem_nhds hp)

private theorem contMDiff_coe_chart (h : IsProductCollarChart k φ V ε) :
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k (fun y : h.sourceOpens ↦ φ y) := fun y ↦
  contMDiffAt_subtype_iff.2 (h.contMDiffAt_chart (h.mem_sourceOpens.1 y.2))

/-- The boundary component of the local collar, read in the ambient manifold, is the point
obtained by setting the normal coordinate to zero. -/
private theorem coe_homeomorphProdOpens_fst (h : IsProductCollarChart k φ V ε)
    (y : h.sourceOpens) :
    (((h.homeomorphProdOpens y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) := by
  rw [← h.map_homeomorphProdOpens_fst y]
  exact (φ.left_inv (h.mem_sourceBoundaryOpens.1 (h.homeomorphProdOpens y).1.2)).symm

/-- The inverse local collar reads a boundary point and a normal coordinate back through the
collar chart. -/
private theorem coe_homeomorphProdOpens_symm (h : IsProductCollarChart k φ V ε)
    (p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) :
    (h.homeomorphProdOpens.symm p : M) =
      φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) := by
  obtain ⟨y, rfl⟩ := h.homeomorphProdOpens.surjective p
  rw [Homeomorph.symm_apply_apply, h.map_homeomorphProdOpens_fst y,
    h.coe_homeomorphProdOpens_snd y]
  exact (φ.left_inv (h.mem_sourceOpens.1 y.2)).symm

/-- The boundary retraction of a product collar chart is `C^k`: it sets the normal coordinate to
zero and reads the result back through the chart. -/
theorem contMDiff_boundaryRetract (h : IsProductCollarChart k φ V ε) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      (fun y : h.sourceOpens ↦
        φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1))) := by
  have hzero : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y : h.sourceOpens ↦
        ((φ y).1, (0 : EuclideanHalfSpace 1))) :=
    h.contMDiff_coe_chart.fst.prodMk contMDiff_const
  exact fun y ↦ (h.contMDiffAt_chart_symm
    (h.fst_zero_mem_target (h.mem_sourceOpens.1 y.2))).comp y hzero.contMDiffAt

variable [IsManifold (𝓡∂ (n + 1)) k M]

private theorem contMDiff_homeomorphProdOpens (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k h.homeomorphProdOpens := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      ↥((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M hk
  have hretractVal : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      (fun y : h.sourceOpens ↦
        (((h.homeomorphProdOpens y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M)) := by
    rw [funext h.coe_homeomorphProdOpens_fst]
    exact h.contMDiff_boundaryRetract
  have hretractBoundary : ContMDiff (𝓡∂ (n + 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (fun y : h.sourceOpens ↦
        ((h.homeomorphProdOpens y).1 : ↥((𝓡∂ (n + 1)).boundary M))) :=
    (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M hk).isImmersion).2
      ⟨continuous_induced_rng.2 hretractVal.continuous, hretractVal⟩
  have hnormalVal : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ 1) k
      (fun y : h.sourceOpens ↦ ((h.homeomorphProdOpens y).2 : EuclideanHalfSpace 1)) := by
    rw [funext h.coe_homeomorphProdOpens_snd]
    exact h.contMDiff_coe_chart.snd
  have hretract : ContMDiff (𝓡∂ (n + 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (fun y : h.sourceOpens ↦ (h.homeomorphProdOpens y).1) := fun y ↦
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 (hretractBoundary y)
  have hnormal : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ 1) k
      (fun y : h.sourceOpens ↦ (h.homeomorphProdOpens y).2) := fun y ↦
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 (hnormalVal y)
  exact hretract.prodMk hnormal

private theorem contMDiff_homeomorphProdOpens_symm (h : IsProductCollarChart k φ V ε)
    (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k h.homeomorphProdOpens.symm := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      ↥((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M hk
  have hboundaryVal : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦ (p.1.1 : M)) :=
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M hk).contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_fst)
  have hφboundary : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦ φ p.1.1) := fun p ↦
    (h.contMDiffAt_chart (h.mem_sourceBoundaryOpens.1 p.1.2)).comp p hboundaryVal.contMDiffAt
  have hpair : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦
        ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1))) :=
    hφboundary.fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  have hassembleVal : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦
        (h.homeomorphProdOpens.symm p : M)) := by
    rw [funext h.coe_homeomorphProdOpens_symm]
    exact fun p ↦ (h.contMDiffAt_chart_symm (h.mk_mem_target
      (h.mem_sourceBoundaryOpens.1 p.1.2)
      (EuclideanHalfSpace.mem_normalIio.2
        (EuclideanHalfSpace.mem_normalIioOpens.1 p.2.2)))).comp p hpair.contMDiffAt
  exact fun p ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 (hassembleVal p)

/-- A product collar chart gives a `C^k` diffeomorphism from its open source to the product of its
open boundary part and open normal interval. Its underlying equivalence is the one of the
topological local collar `IsProductCollarChart.homeomorphProdOpens`. -/
def diffeomorphProd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    Diffeomorph (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1))
      h.sourceOpens (h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) k :=
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  { toEquiv := h.homeomorphProdOpens.toEquiv
    contMDiff_toFun := h.contMDiff_homeomorphProdOpens hk
    contMDiff_invFun := h.contMDiff_homeomorphProdOpens_symm hk }

section Characteristic

/-- **The smooth local collar is the topological one.** Its underlying map is that of
`IsProductCollarChart.homeomorphProdOpens`, so every coordinate formula proved there transfers. -/
theorem coe_diffeomorphProd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    ⇑(h.diffeomorphProd hk) = ⇑h.homeomorphProdOpens :=
  funext fun _ ↦ rfl

/-- The boundary component of the smooth local collar is obtained by setting the normal
coordinate to zero and reading back through the collar chart. -/
theorem coe_diffeomorphProd_fst (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) :=
  h.coe_homeomorphProdOpens_fst y

/-- The normal component of the smooth local collar is the normal component of the collar chart. -/
@[simp]
theorem coe_diffeomorphProd_snd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    ((h.diffeomorphProd hk y).2 : EuclideanHalfSpace 1) = (φ y).2 :=
  h.coe_homeomorphProdOpens_snd y

/-- The inverse smooth local collar forms a collar-coordinate pair and reads it back through the
chart. -/
theorem coe_diffeomorphProd_symm (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ((h.diffeomorphProd hk).symm p : M) =
      φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) :=
  h.coe_homeomorphProdOpens_symm p

/-- In collar coordinates, the boundary retraction keeps the tangential coordinate and sets the
normal coordinate to zero. -/
@[simp]
theorem map_diffeomorphProd_fst (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    φ (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      ((φ y).1, (0 : EuclideanHalfSpace 1)) :=
  h.map_homeomorphProdOpens_fst y

/-- Applying the collar chart after the inverse smooth local collar recovers the supplied
tangential and normal coordinates. -/
@[simp]
theorem map_diffeomorphProd_symm (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    φ ((h.diffeomorphProd hk).symm p : M) =
      ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) := by
  rw [coe_diffeomorphProd_symm]
  exact φ.right_inv (h.mk_mem_target (h.mem_sourceBoundaryOpens.1 p.1.2)
    (EuclideanHalfSpace.mem_normalIio.2 (EuclideanHalfSpace.mem_normalIioOpens.1 p.2.2)))

/-- On the boundary, the smooth local collar is the identity in the boundary factor and has zero
normal coordinate. -/
@[simp]
theorem diffeomorphProd_apply_of_mem_boundary (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens)
    (hy : (y : M) ∈ (𝓡∂ (n + 1)).boundary M) :
    h.diffeomorphProd hk y =
      (⟨⟨(y : M), hy⟩,
        h.mem_sourceBoundaryOpens.2 (h.mem_sourceOpens.1 y.2)⟩,
        ⟨0, EuclideanHalfSpace.mem_normalIioOpens.2
          (EuclideanHalfSpace.mem_normalIio.1
            (EuclideanHalfSpace.zero_mem_normalIio h.height_pos))⟩) := by
  have hyzero : (φ y).2 = 0 :=
    EuclideanHalfSpace.eq_zero_iff.2 ((h.mem_boundary_iff y (h.mem_sourceOpens.1 y.2)).1 hy)
  have hfst : (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) = (y : M) := by
    rw [h.coe_diffeomorphProd_fst hk y, ← hyzero]
    exact φ.left_inv (h.mem_sourceOpens.1 y.2)
  exact Prod.ext (Subtype.ext (Subtype.ext hfst))
    (Subtype.ext ((h.coe_diffeomorphProd_snd hk y).trans hyzero))

end Characteristic

end IsProductCollarChart

end TauCeti
