/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# Smooth local collars of a manifold with boundary

The module Boundary.Collar.Local shrinks collar coordinates around a boundary point to a product
box and extracts a homeomorphism with a product of the boundary and a half-open interval. This file
proves that product decomposition is smooth for the canonical manifold structure on the boundary.

For a product collar chart φ, the source, its boundary part, and its normal interval are recorded
as open submanifolds. The diffeomorphism IsProductCollarChart.diffeomorphProd sends a point to its
boundary retraction and normal coordinate. Its inverse takes a boundary point and a normal
coordinate and reads the resulting pair back through φ.

This is the smooth local-product step in the collar-neighbourhood target of Layer 1 of the
GeometricTopology roadmap. The global collar theorem still requires patching these local
diffeomorphisms along the whole boundary.

## Main definitions

* TauCeti.IsProductCollarChart.sourceOpens: the source of a product collar chart as an open
  submanifold of the ambient manifold.
* TauCeti.IsProductCollarChart.boundaryOpens: the boundary part of that source as an open
  submanifold of the canonical boundary manifold.
* TauCeti.IsProductCollarChart.normalOpens: the normal interval as an open submanifold of the
  one-dimensional half-space.
* TauCeti.IsProductCollarChart.diffeomorphProd: the canonical smooth local collar.
* TauCeti.exists_diffeomorphProd_of_mem_boundary: every boundary point lies in the source of such
  a smooth local collar.

## References

* M. Hirsch, Differential Topology, Springer GTM 33 (1976), Theorem 6.1.
* J. Lee, Introduction to Smooth Manifolds, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
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

/-- The source of a product collar chart, regarded as an open submanifold of the ambient
manifold. -/
def sourceOpens (_h : IsProductCollarChart k φ V ε) : TopologicalSpace.Opens M :=
  ⟨φ.source, φ.open_source⟩

/-- Membership in the open source of a product collar chart is membership in the chart source. -/
@[simp]
theorem mem_sourceOpens (h : IsProductCollarChart k φ V ε) {x : M} :
    x ∈ h.sourceOpens ↔ x ∈ φ.source := Iff.rfl

/-- The part of the boundary in the source of a product collar chart, regarded as an open
submanifold of the canonical boundary manifold. -/
def boundaryOpens (_h : IsProductCollarChart k φ V ε) :
    TopologicalSpace.Opens ↥((𝓡∂ (n + 1)).boundary M) :=
  ⟨Subtype.val ⁻¹' φ.source, φ.open_source.preimage continuous_subtype_val⟩

/-- A boundary point belongs to the collar base exactly when its ambient point belongs to the
chart source. -/
@[simp]
theorem mem_boundaryOpens (h : IsProductCollarChart k φ V ε)
    {x : ↥((𝓡∂ (n + 1)).boundary M)} :
    x ∈ h.boundaryOpens ↔ (x : M) ∈ φ.source := Iff.rfl

/-- The normal interval of a product collar chart, regarded as an open submanifold of the
one-dimensional half-space. -/
def normalOpens (_h : IsProductCollarChart k φ V ε) :
    TopologicalSpace.Opens (EuclideanHalfSpace 1) :=
  ⟨EuclideanHalfSpace.normalIio ε, EuclideanHalfSpace.isOpen_normalIio ε⟩

/-- A normal coordinate belongs to the collar interval exactly when it is smaller than the collar
height. -/
@[simp]
theorem mem_normalOpens (h : IsProductCollarChart k φ V ε) {t : EuclideanHalfSpace 1} :
    t ∈ h.normalOpens ↔ t.1 0 < ε := EuclideanHalfSpace.mem_normalIio

private def prodEquiv (h : IsProductCollarChart k φ V ε) :
    h.sourceOpens ≃ h.boundaryOpens × h.normalOpens where
  toFun y := by
    have hyφ : φ y ∈ φ.target := φ.map_source y.2
    have hybox : φ y ∈ V ×ˢ EuclideanHalfSpace.normalIio ε := h.target_eq ▸ hyφ
    have hzero : ((φ y).1, (0 : EuclideanHalfSpace 1)) ∈ φ.target := by
      rw [h.target_eq]
      exact ⟨hybox.1, EuclideanHalfSpace.zero_mem_normalIio h.height_pos⟩
    let q := φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1))
    have hqsource : q ∈ φ.source := φ.map_target hzero
    have hqboundary : q ∈ (𝓡∂ (n + 1)).boundary M := by
      rw [h.mem_boundary_iff q hqsource, φ.right_inv hzero]
      exact EuclideanHalfSpace.val_zero_apply
    exact (⟨⟨q, hqboundary⟩, hqsource⟩, ⟨(φ y).2, hybox.2⟩)
  invFun p := by
    have hqtarget : φ p.1.1 ∈ φ.target := φ.map_source p.1.2
    have hqbox : φ p.1.1 ∈ V ×ˢ EuclideanHalfSpace.normalIio ε := h.target_eq ▸ hqtarget
    have hpbox : ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) ∈ φ.target := by
      rw [h.target_eq]
      exact ⟨hqbox.1, p.2.2⟩
    exact ⟨φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)), φ.map_target hpbox⟩
  left_inv y := by
    have hybox : φ y ∈ V ×ˢ EuclideanHalfSpace.normalIio ε :=
      h.target_eq ▸ φ.map_source y.2
    have hzero : ((φ y).1, (0 : EuclideanHalfSpace 1)) ∈ φ.target := by
      rw [h.target_eq]
      exact ⟨hybox.1, EuclideanHalfSpace.zero_mem_normalIio h.height_pos⟩
    apply Subtype.ext
    simp only
    rw [φ.right_inv hzero]
    exact φ.left_inv y.2
  right_inv p := by
    have hqtarget : φ p.1.1 ∈ φ.target := φ.map_source p.1.2
    have hpbox : ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) ∈ φ.target := by
      rw [h.target_eq]
      exact ⟨(h.target_eq ▸ hqtarget).1, p.2.2⟩
    have hqzero : (φ p.1.1).2 = 0 := EuclideanHalfSpace.eq_zero_iff.2 <|
      (h.mem_boundary_iff p.1.1 p.1.2).1 p.1.1.2
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      simp only
      rw [φ.right_inv hpbox]
      rw [← hqzero]
      exact φ.left_inv p.1.2
    · apply Subtype.ext
      simp only
      rw [φ.right_inv]
      rw [h.target_eq]
      exact ⟨(h.target_eq ▸ hqtarget).1, p.2.2⟩

private theorem coe_prodEquiv_fst (h : IsProductCollarChart k φ V ε) (y : h.sourceOpens) :
    (((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) := rfl

private theorem coe_prodEquiv_snd (h : IsProductCollarChart k φ V ε) (y : h.sourceOpens) :
    ((h.prodEquiv y).2 : EuclideanHalfSpace 1) = (φ y).2 := rfl

private theorem coe_prodEquiv_symm (h : IsProductCollarChart k φ V ε)
    (p : h.boundaryOpens × h.normalOpens) :
    (h.prodEquiv.symm p : M) =
      φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) := rfl

variable [IsManifold (𝓡∂ (n + 1)) k M]

/-- A product collar chart gives a C^k diffeomorphism from its source to the product of its
boundary part and its normal interval. The boundary factor uses the canonical manifold structure
from Boundary.Charts. -/
def diffeomorphProd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    Diffeomorph (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) h.sourceOpens
      (h.boundaryOpens × h.normalOpens) k := by
  letI : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  letI : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      ↥((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M hk
  refine { toEquiv := h.prodEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hφ : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
        (fun y : h.sourceOpens ↦ φ y) := by
      intro y
      rw [contMDiffAt_subtype_iff]
      exact (h.contMDiffOn y y.2).contMDiffAt (φ.open_source.mem_nhds y.2)
    have hzero : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
        (fun y : h.sourceOpens ↦ ((φ y).1, (0 : EuclideanHalfSpace 1))) :=
      hφ.fst.prodMk contMDiff_const
    have hzero_mem (y : h.sourceOpens) :
        ((φ y).1, (0 : EuclideanHalfSpace 1)) ∈ φ.target := by
      rw [h.target_eq]
      exact ⟨(h.target_eq ▸ φ.map_source y.2).1,
        EuclideanHalfSpace.zero_mem_normalIio h.height_pos⟩
    have hretractAmbient : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) k
        (fun y : h.sourceOpens ↦ φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1))) := by
      intro y
      exact ((h.contMDiffOn_symm _ (hzero_mem y)).contMDiffAt
        (φ.open_target.mem_nhds (hzero_mem y))).comp y hzero.contMDiffAt
    have hretractBoundary : ContMDiff (𝓡∂ (n + 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
        (fun y : h.sourceOpens ↦ ((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M))) := by
      apply (ContMDiff.iff_comp_isImmersion
        (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M hk).isImmersion).2
      refine ⟨?_, ?_⟩
      · exact continuous_induced_rng.2 hretractAmbient.continuous
      · convert hretractAmbient using 1
        rfl
    have hretract : ContMDiff (𝓡∂ (n + 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
        (fun y : h.sourceOpens ↦ (h.prodEquiv y).1) := by
      apply (ContMDiff.iff_comp_isImmersion
        (Manifold.IsImmersion.of_opens h.boundaryOpens)).2
      refine ⟨?_, ?_⟩
      · exact continuous_induced_rng.2 hretractBoundary.continuous
      · convert hretractBoundary using 1
        rfl
    have hnormal : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ 1) k
        (fun y : h.sourceOpens ↦ (h.prodEquiv y).2) := by
      apply (ContMDiff.iff_comp_isImmersion
        (Manifold.IsImmersion.of_opens h.normalOpens)).2
      refine ⟨?_, ?_⟩
      · exact continuous_induced_rng.2 hφ.snd.continuous
      · convert hφ.snd using 1
        rfl
    exact hretract.prodMk hnormal
  · have hboundaryVal : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
        (fun p : h.boundaryOpens × h.normalOpens ↦ (p.1.1 : M)) := by
      exact (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) M hk).contMDiff.comp
        (contMDiff_subtype_val.comp contMDiff_fst)
    have hφboundary : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k
        (fun p : h.boundaryOpens × h.normalOpens ↦ φ p.1.1) := by
      intro p
      exact ((h.contMDiffOn p.1.1 p.1.2).contMDiffAt
        (φ.open_source.mem_nhds p.1.2)).comp p hboundaryVal.contMDiffAt
    have hnormalVal : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ 1) k
        (fun p : h.boundaryOpens × h.normalOpens ↦ (p.2 : EuclideanHalfSpace 1)) :=
      contMDiff_subtype_val.comp contMDiff_snd
    have hpair : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k
        (fun p : h.boundaryOpens × h.normalOpens ↦
          ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1))) :=
      hφboundary.fst.prodMk hnormalVal
    have hpair_mem (p : h.boundaryOpens × h.normalOpens) :
        ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) ∈ φ.target := by
      rw [h.target_eq]
      exact ⟨(h.target_eq ▸ φ.map_source p.1.2).1, p.2.2⟩
    have hassembleAmbient : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
        (fun p : h.boundaryOpens × h.normalOpens ↦
          φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1))) := by
      intro p
      exact ((h.contMDiffOn_symm _ (hpair_mem p)).contMDiffAt
        (φ.open_target.mem_nhds (hpair_mem p))).comp p hpair.contMDiffAt
    apply (ContMDiff.iff_comp_isImmersion
      (Manifold.IsImmersion.of_opens h.sourceOpens)).2
    refine ⟨?_, ?_⟩
    · exact continuous_induced_rng.2 hassembleAmbient.continuous
    · convert hassembleAmbient using 1
      rfl

private theorem diffeomorphProd_toEquiv (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    (h.diffeomorphProd hk).toEquiv = h.prodEquiv := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  rw [diffeomorphProd.eq_def]

section Characteristic

/-- The boundary component of the local collar is obtained by setting the normal coordinate to
zero and reading back through the collar chart. -/
@[simp]
theorem coe_diffeomorphProd_fst (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  have heq := congrArg
    (fun e : h.sourceOpens ≃ h.boundaryOpens × h.normalOpens ↦
      (e y).1)
    (diffeomorphProd_toEquiv h hk)
  calc
    (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
        (((h.diffeomorphProd hk).toEquiv y).1 :
          ↥((𝓡∂ (n + 1)).boundary M)) :=
      congrArg (fun p ↦ ((p.1 : ↥((𝓡∂ (n + 1)).boundary M)) : M))
        (congrFun (Diffeomorph.coe_toEquiv (h.diffeomorphProd hk)) y).symm
    _ = ((h.prodEquiv y).1 : ↥((𝓡∂ (n + 1)).boundary M)) :=
      congrArg (fun q : h.boundaryOpens ↦
        (((q : ↥((𝓡∂ (n + 1)).boundary M)) : M))) heq
    _ = φ.symm ((φ y).1, (0 : EuclideanHalfSpace 1)) := coe_prodEquiv_fst h y

/-- The normal component of the local collar is the normal component of the collar chart. -/
@[simp]
theorem coe_diffeomorphProd_snd (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    ((h.diffeomorphProd hk y).2 : EuclideanHalfSpace 1) = (φ y).2 := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  have heq : ((h.diffeomorphProd hk).toEquiv y).2 = (h.prodEquiv y).2 := congrArg
    (fun e : h.sourceOpens ≃ h.boundaryOpens × h.normalOpens ↦
      (e y).2)
    (diffeomorphProd_toEquiv h hk)
  calc
    ((h.diffeomorphProd hk y).2 : EuclideanHalfSpace 1) =
        (((h.diffeomorphProd hk).toEquiv y).2 : EuclideanHalfSpace 1) :=
      congrArg (fun p ↦ (p.2 : EuclideanHalfSpace 1))
        (congrFun (Diffeomorph.coe_toEquiv (h.diffeomorphProd hk)) y).symm
    _ = ((h.prodEquiv y).2 : EuclideanHalfSpace 1) :=
      congrArg (fun t : h.normalOpens ↦ (t : EuclideanHalfSpace 1)) heq
    _ = (φ y).2 := coe_prodEquiv_snd h y

/-- The inverse local collar forms a collar-coordinate pair and reads it back through the
chart. -/
@[simp]
theorem coe_diffeomorphProd_symm (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (p : h.boundaryOpens × h.normalOpens) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    ((h.diffeomorphProd hk).symm p : M) =
      φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  have heq : ((h.diffeomorphProd hk).toEquiv.symm p : M) =
      (h.prodEquiv.symm p : M) := congrArg
    (fun e : h.sourceOpens ≃ h.boundaryOpens × h.normalOpens ↦ (e.symm p : M))
    (diffeomorphProd_toEquiv h hk)
  calc
    ((h.diffeomorphProd hk).symm p : M) =
        ((h.diffeomorphProd hk).toEquiv.symm p : M) :=
      congrArg (fun q : h.sourceOpens ↦ (q : M))
        (congrFun (Diffeomorph.toEquiv_coe_symm (h.diffeomorphProd hk)) p).symm
    _ = (h.prodEquiv.symm p : M) := heq
    _ = φ.symm ((φ p.1.1).1, (p.2 : EuclideanHalfSpace 1)) := coe_prodEquiv_symm h p

/-- In collar coordinates, the boundary retraction keeps the tangential coordinate and sets the
normal coordinate to zero. -/
theorem map_diffeomorphProd_fst (h : IsProductCollarChart k φ V ε) (hk : k ≠ 0)
    (y : h.sourceOpens) :
    φ (((h.diffeomorphProd hk y).1 : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      ((φ y).1, (0 : EuclideanHalfSpace 1)) := by
  rw [coe_diffeomorphProd_fst]
  apply φ.right_inv
  rw [h.target_eq]
  exact ⟨(h.target_eq ▸ φ.map_source y.2).1,
    EuclideanHalfSpace.zero_mem_normalIio h.height_pos⟩

end Characteristic

end IsProductCollarChart

/-- Every boundary point of a positive-regularity manifold with boundary lies in a product collar
chart whose source is diffeomorphic to the product of its boundary part and its normal interval.

This is the local smooth collar theorem. The global collar theorem asks for one source containing
the entire boundary, rather than one source around each boundary point. -/
theorem exists_diffeomorphProd_of_mem_boundary [IsManifold (𝓡∂ (n + 1)) k M]
    (hk : k ≠ 0) {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    ∃ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1))
      (V : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
      (h : IsProductCollarChart k φ V ε),
      x ∈ h.sourceOpens ∧
        let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
          IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
        Nonempty (Diffeomorph (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) h.sourceOpens
          (h.boundaryOpens × h.normalOpens) k) := by
  obtain ⟨φ, V, ε, hxφ, h⟩ := exists_isProductCollarChart_of_mem_boundary hk hx
  exact ⟨φ, V, ε, h, hxφ, ⟨h.diffeomorphProd hk⟩⟩

end TauCeti
