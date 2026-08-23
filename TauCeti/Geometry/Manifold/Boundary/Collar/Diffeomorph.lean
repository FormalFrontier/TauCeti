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
extracts a homeomorphism with a product of the boundary and a half-open interval. This file
constructs a smooth product decomposition for the canonical manifold structure on the boundary.

For a product collar chart `φ`, the diffeomorphism
`TauCeti.IsProductCollarChart.diffeomorphProd` sends a point to its boundary retraction and normal
coordinate. Its underlying equivalence is obtained from
`TauCeti.IsProductCollarChart.homeomorphProd`, after identifying the boundary factor with an open
subspace of the canonical boundary manifold. Its inverse combines a boundary point and a normal
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
* `TauCeti.IsProductCollarChart.coe_diffeomorphProd_fst_eq_homeomorphProd_fst` and
  `TauCeti.IsProductCollarChart.coe_diffeomorphProd_snd_eq_homeomorphProd_snd`: the smooth and
  topological local collars have the same underlying map.

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

private theorem source_mem (h : IsProductCollarChart k φ V ε) (y : h.sourceOpens) :
    (y : M) ∈ φ.source :=
  h.mem_sourceOpens.1 y.2

private theorem sourceSubtype_mem
    (h : IsProductCollarChart k φ V ε) (y : h.sourceBoundaryOpens) : (y.1 : M) ∈ φ.source :=
  h.mem_sourceBoundaryOpens.1 y.2

private theorem normalIio_mem (t : EuclideanHalfSpace.normalIioOpens ε) :
    (t : EuclideanHalfSpace 1) ∈ EuclideanHalfSpace.normalIio ε :=
  EuclideanHalfSpace.mem_normalIio.2 (EuclideanHalfSpace.mem_normalIioOpens.1 t.2)

private def prodEquiv (h : IsProductCollarChart k φ V ε) :
    h.sourceOpens ≃ h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε :=
  h.homeomorphProdOpens.toEquiv

private theorem coe_prodEquiv_fst (h : IsProductCollarChart k φ V ε)
    (y : h.sourceOpens) :
    (((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) := by
  rw [← h.map_homeomorphProdOpens_fst y]
  exact (φ.left_inv
    (h.mem_sourceBoundaryOpens.1 (h.prodEquiv y).1.2)).symm

private theorem coe_prodEquiv_snd (h : IsProductCollarChart k φ V ε)
    (y : h.sourceOpens) :
    ((h.prodEquiv y).2 : EuclideanHalfSpace 1) = (φ y).2 :=
  h.coe_homeomorphProdOpens_snd y

private theorem map_prodEquiv_fst (h : IsProductCollarChart k φ V ε)
    (y : h.sourceOpens) :
    φ (((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      ((φ y).1, (0 : EuclideanHalfSpace 1)) := by
  exact h.map_homeomorphProdOpens_fst y

private theorem coe_prodEquiv_symm (h : IsProductCollarChart k φ V ε)
    (p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) :
    (h.prodEquiv.symm p : M) =
      φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) := by
  let y := h.prodEquiv.symm p
  have hp : h.prodEquiv y = p := h.prodEquiv.apply_symm_apply p
  have hfirst :
      (((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) = (p.1.1 : M) :=
    congrArg (fun q ↦ (((q.1 : ↥((𝓡∂ (n + 1)).boundary M)) : M))) hp
  have hfst : (φ p.1.1).1 = (φ y).1 := by
    have hmap := congrArg Prod.fst (h.map_prodEquiv_fst y)
    rwa [hfirst] at hmap
  have hsnd : (φ y).2 = (p.2 : EuclideanHalfSpace 1) :=
    (h.coe_prodEquiv_snd y).symm.trans
      (congrArg (fun q ↦ (q.2 : EuclideanHalfSpace 1)) hp)
  calc
    (h.prodEquiv.symm p : M) = φ.symm (φ y) := (φ.left_inv (source_mem h y)).symm
    _ = φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) :=
      congrArg φ.symm (Prod.ext hfst.symm hsnd)

/-- The boundary retraction of a product collar chart is `C^k`: it sets the normal coordinate to
zero and reads the result back through the chart. -/
theorem contMDiff_boundaryRetract (h : IsProductCollarChart k φ V ε) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
      (fun y : h.sourceOpens ↦
        φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1))) := by
  have hφ : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y : h.sourceOpens ↦ φ y) := by
    intro y
    rw [contMDiffAt_subtype_iff]
    exact (h.contMDiffOn y (source_mem h y)).contMDiffAt
      (φ.open_source.mem_nhds (source_mem h y))
  have hzero : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y : h.sourceOpens ↦
        ((φ y).1, (0 : EuclideanHalfSpace 1))) :=
    hφ.fst.prodMk contMDiff_const
  intro y
  exact ((h.contMDiffOn_symm _ (h.fst_zero_mem_target (source_mem h y))).contMDiffAt
    (φ.open_target.mem_nhds (h.fst_zero_mem_target (source_mem h y)))).comp y hzero.contMDiffAt

variable [IsManifold (𝓡∂ (n + 1)) k M]

private theorem contMDiff_prodEquiv (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k h.prodEquiv := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      ↥((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M hk
  have hretractBoundary : ContMDiff (𝓡∂ (n + 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (fun y : h.sourceOpens ↦
        ((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M))) := by
    apply (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M hk).isImmersion).2
    refine ⟨?_, ?_⟩
    · apply continuous_induced_rng.2
      convert h.contMDiff_boundaryRetract.continuous using 1
      funext y
      exact h.coe_prodEquiv_fst y
    · convert h.contMDiff_boundaryRetract using 1
      funext y
      exact h.coe_prodEquiv_fst y
  have hretract : ContMDiff (𝓡∂ (n + 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (fun y : h.sourceOpens ↦ (h.prodEquiv y).1) := by
    intro y
    have hcomp : ContMDiffAt (𝓡∂ (n + 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
        (Subtype.val ∘ fun y : h.sourceOpens ↦ (h.prodEquiv y).1) y := by
      change ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
        (fun y : h.sourceOpens ↦
          ((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M))) y
      exact hretractBoundary y
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 hcomp
  have hφ : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y : h.sourceOpens ↦ φ y) := by
    intro y
    rw [contMDiffAt_subtype_iff]
    exact (h.contMDiffOn y (source_mem h y)).contMDiffAt
      (φ.open_source.mem_nhds (source_mem h y))
  have hnormal : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ 1) k
      (fun y : h.sourceOpens ↦ (h.prodEquiv y).2) := by
    intro y
    have hcomp : ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ 1) k
        (Subtype.val ∘ fun y : h.sourceOpens ↦ (h.prodEquiv y).2) y := by
      change ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ 1) k
        (fun y : h.sourceOpens ↦
          ((h.prodEquiv y).2 : EuclideanHalfSpace 1)) y
      convert hφ.snd y using 1
      funext z
      exact h.coe_prodEquiv_snd z
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 hcomp
  exact hretract.prodMk hnormal

private theorem contMDiff_prodEquiv_symm (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k h.prodEquiv.symm := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      ↥((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M hk
  have hboundaryVal : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦ (p.1.1 : M)) :=
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M hk).contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_fst)
  have hφboundary : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦ φ p.1.1) := by
    intro p
    exact ((h.contMDiffOn p.1.1 (sourceSubtype_mem h p.1)).contMDiffAt
      (φ.open_source.mem_nhds (sourceSubtype_mem h p.1))).comp p hboundaryVal.contMDiffAt
  have hnormalVal : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ 1) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦
        (p.2 : EuclideanHalfSpace 1)) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hpair : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦
        ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1))) :=
    hφboundary.fst.prodMk hnormalVal
  have hassembleAmbient : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε ↦
        φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1))) := by
    intro p
    exact ((h.contMDiffOn_symm _
      (h.mk_mem_target (sourceSubtype_mem h p.1) (normalIio_mem p.2))).contMDiffAt
      (φ.open_target.mem_nhds
        (h.mk_mem_target (sourceSubtype_mem h p.1) (normalIio_mem p.2)))).comp p hpair.contMDiffAt
  change ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k h.prodEquiv.symm
  intro p
  have hcomp : ContMDiffAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (Subtype.val ∘ h.prodEquiv.symm) p := by
    change ContMDiffAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p ↦ (h.prodEquiv.symm p : M)) p
    convert hassembleAmbient p using 1
    funext q
    exact h.coe_prodEquiv_symm q
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 hcomp

/-- A product collar chart gives a `C^k` diffeomorphism from its open source to the product of its
open boundary part and open normal interval. Its underlying equivalence is the existing
`IsProductCollarChart.homeomorphProd`, transported across the canonical identification of the
boundary factor. -/
def diffeomorphProd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    Diffeomorph (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1))
      h.sourceOpens (h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) k :=
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  { toEquiv := h.prodEquiv
    contMDiff_toFun := h.contMDiff_prodEquiv hk
    contMDiff_invFun := h.contMDiff_prodEquiv_symm hk }

section Characteristic

/-- The boundary component of the smooth local collar agrees with the boundary component of the
topological local collar. -/
theorem coe_diffeomorphProd_fst_eq_homeomorphProd_fst
    (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      ((h.homeomorphProd ⟨y, h.mem_sourceOpens.1 y.2⟩).1 : M) :=
  h.coe_homeomorphProdOpens_fst_eq_homeomorphProd_fst y

/-- The normal component of the smooth local collar agrees with the normal component of the
topological local collar. -/
theorem coe_diffeomorphProd_snd_eq_homeomorphProd_snd
    (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    ((h.diffeomorphProd hk y).2 : EuclideanHalfSpace 1) =
      ((h.homeomorphProd ⟨y, h.mem_sourceOpens.1 y.2⟩).2 : EuclideanHalfSpace 1) :=
  h.coe_homeomorphProdOpens_snd_eq_homeomorphProd_snd y

/-- The boundary component of the smooth local collar is obtained by setting the normal
coordinate to zero and reading back through the collar chart. -/
theorem coe_diffeomorphProd_fst (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) :=
  h.coe_prodEquiv_fst y

/-- The normal component of the smooth local collar is the normal component of the collar chart. -/
@[simp]
theorem coe_diffeomorphProd_snd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    ((h.diffeomorphProd hk y).2 : EuclideanHalfSpace 1) = (φ y).2 :=
  h.coe_prodEquiv_snd y

/-- The inverse smooth local collar forms a collar-coordinate pair and reads it back through the
chart. -/
theorem coe_diffeomorphProd_symm (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (p : h.sourceBoundaryOpens × EuclideanHalfSpace.normalIioOpens ε) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ((h.diffeomorphProd hk).symm p : M) =
      φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) :=
  h.coe_prodEquiv_symm p

/-- In collar coordinates, the boundary retraction keeps the tangential coordinate and sets the
normal coordinate to zero. -/
@[simp]
theorem map_diffeomorphProd_fst (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    φ (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      ((φ y).1, (0 : EuclideanHalfSpace 1)) :=
  h.map_prodEquiv_fst y

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
  exact φ.right_inv (h.mk_mem_target (sourceSubtype_mem h p.1) (normalIio_mem p.2))

/-- On the boundary, the smooth local collar is the identity in the boundary factor and has zero
normal coordinate. -/
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
    EuclideanHalfSpace.eq_zero_iff.2 ((h.mem_boundary_iff y (source_mem h y)).1 hy)
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    change (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) = (y : M)
    rw [coe_diffeomorphProd_fst]
    calc
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) = φ.symm (φ y) :=
        congrArg φ.symm (Prod.ext (rfl) hyzero.symm)
      _ = y := φ.left_inv (source_mem h y)
  · apply Subtype.ext
    rw [coe_diffeomorphProd_snd]
    exact hyzero

/-- The normal component of the smooth local collar vanishes on the boundary. -/
theorem coe_diffeomorphProd_snd_of_mem_boundary
    (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens)
    (hy : (y : M) ∈ (𝓡∂ (n + 1)).boundary M) :
    ((h.diffeomorphProd hk y).2 : EuclideanHalfSpace 1) = 0 := by
  rw [coe_diffeomorphProd_snd]
  exact EuclideanHalfSpace.eq_zero_iff.2 ((h.mem_boundary_iff y (source_mem h y)).1 hy)

end Characteristic

end IsProductCollarChart

end TauCeti
