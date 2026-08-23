/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic

/-!
# The graph automorphism of the pinned type `E₆` root datum

This file specializes the general diagram-automorphism construction
`TauCeti.DynkinType.diagramAut` to the order-two symmetry `TauCeti.graphPermE6` of the
Bourbaki-numbered `E₆` diagram. It gives short type-`E₆` names for the resulting automorphism and
root-index permutation, and records their nontriviality and preservation of the pinned base.

## Main declarations

* `TauCeti.DynkinType.e6GraphIndexEquiv`: the induced permutation of all root indices.
* `TauCeti.DynkinType.e6GraphAut`: the graph automorphism of the pinned simply connected datum.
* `TauCeti.DynkinType.e6GraphAut_sq`: the automorphism has square one.
* `TauCeti.DynkinType.image_e6GraphIndexEquiv_e6SimplyConnectedBase_support`: the pinned base
  support is preserved.

## References

The coordinates and node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate V. The graph automorphism and its role in the twisted family `²E₆` follow R. W. Carter,
*Simple Groups of Lie Type*, §12.2.

The pinned-isomorphism target in Layer 9 of the ReductiveGroups roadmap lifts root-datum
automorphisms such as this one to pinned group-scheme automorphisms.
-/

public section

namespace TauCeti.DynkinType

open TauCeti

noncomputable section

private theorem graphPermE6_mem_diagramSymmetry :
    graphPermE6 ∈ E6.diagramSymmetry :=
  mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6

/-- The permutation of all roots induced by the `E₆` graph symmetry, expressed on the native root
indices of the pinned datum. -/
def e6GraphIndexEquiv : Equiv.Perm (Fin 72) :=
  diagramRootPerm valid_E6 graphPermE6_mem_diagramSymmetry

/-- The order-two diagram symmetry as an automorphism of the pinned simply connected root datum of
type `E₆`. -/
def e6GraphAut := diagramAut valid_E6 graphPermE6_mem_diagramSymmetry

/-- The root-index permutation packaged by the type-`E₆` graph automorphism is the separately
named specialization of the general induced permutation. -/
@[simp] theorem e6GraphAut_indexEquiv : e6GraphAut.indexEquiv = e6GraphIndexEquiv := by
  exact diagramAut_indexEquiv valid_E6 graphPermE6_mem_diagramSymmetry

/-- The character-lattice action of the type-`E₆` graph automorphism permutes the node
coordinates. This is not a simp lemma because its left side normalizes across the opaque
`E6.rank = 6` equation. -/
theorem weightMap_e6GraphAut_apply (x : Fin 6 → ℤ) (i : Fin 6) :
    e6GraphAut.weightMap x i = x (graphPermE6 i) := by
  change Fin 6 → ℤ at x
  change Fin 6 at i
  have h : graphPermE6.symm = graphPermE6 :=
    (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using graphPermE6_sq)).symm
  have hmap := diagramAut_weightMap valid_E6 graphPermE6_mem_diagramSymmetry
  have hx := LinearMap.congr_fun hmap x
  have hxi := congrFun hx i
  have heval : (LinearEquiv.funCongrLeft ℤ ℤ graphPermE6.symm) x i =
      x (graphPermE6 i) := by
    change x (graphPermE6.symm i) = x (graphPermE6 i)
    rw [h]
  simpa only [e6GraphAut] using hxi.trans heval

/-- The cocharacter-lattice action of the type-`E₆` graph automorphism permutes the node
coordinates. As for `weightMap_e6GraphAut_apply`, the opaque rank equation prevents a simp-normal
left side. -/
theorem coweightMap_e6GraphAut_apply (x : Fin 6 → ℤ) (i : Fin 6) :
    e6GraphAut.coweightMap x i = x (graphPermE6 i) := by
  change Fin 6 → ℤ at x
  change Fin 6 at i
  have hmap := diagramAut_coweightMap valid_E6 graphPermE6_mem_diagramSymmetry
  have hx := LinearMap.congr_fun hmap x
  have hxi := congrFun hx i
  have heval : (LinearEquiv.funCongrLeft ℤ ℤ graphPermE6) x i =
      x (graphPermE6 i) := rfl
  simpa only [e6GraphAut] using hxi.trans heval

/-- The type-`E₆` root permutation restricts to the numbered diagram involution on the pinned
simple roots. -/
@[simp] theorem e6GraphIndexEquiv_e6SimpleIndex (i : Fin 6) :
    e6GraphIndexEquiv (e6SimpleIndex i) = e6SimpleIndex (graphPermE6 i) := by
  have hi : E6.simpleIndex valid_E6 i = e6SimpleIndex i := by
    apply Fin.ext
    simpa only [e6SimpleIndex_val] using simpleIndex_val E6 valid_E6 i
  have hσi : E6.simpleIndex valid_E6 (graphPermE6 i) =
      e6SimpleIndex (graphPermE6 i) := by
    apply Fin.ext
    simpa only [e6SimpleIndex_val] using simpleIndex_val E6 valid_E6 (graphPermE6 i)
  rw [← hi, e6GraphIndexEquiv]
  exact (diagramRootPerm_simpleIndex valid_E6 graphPermE6_mem_diagramSymmetry i).trans hσi

/-- Applying the type-`E₆` graph automorphism twice is the identity. -/
@[simp] theorem e6GraphAut_sq : e6GraphAut ^ 2 = 1 := by
  exact diagramAut_pow_eq_one valid_E6 graphPermE6_mem_diagramSymmetry graphPermE6_sq

/-- Applying the type-`E₆` root permutation twice is the identity. -/
@[simp] theorem e6GraphIndexEquiv_apply_apply (i : Fin 72) :
    e6GraphIndexEquiv (e6GraphIndexEquiv i) = i := by
  have h := congrArg (fun g => g.indexEquiv) e6GraphAut_sq
  simp only [pow_two, _root_.RootPairing.Equiv.mul_eq_comp,
    _root_.RootPairing.Equiv.toHom_comp, _root_.RootPairing.Hom.comp,
    e6GraphAut_indexEquiv, _root_.RootPairing.Equiv.toHom_one,
    _root_.RootPairing.Hom.indexEquiv_one] at h
  have hi := DFunLike.congr_fun h i
  change e6GraphIndexEquiv (e6GraphIndexEquiv i) = i at hi
  exact hi

/-- The type-`E₆` graph automorphism is nontrivial: it exchanges the first and sixth simple
roots. -/
theorem e6GraphAut_ne_one : e6GraphAut ≠ 1 := by
  intro h
  have hvalue := congrArg (fun g => g.weightMap (Pi.single (5 : Fin 6) 1) (0 : Fin 6)) h
  simp only [_root_.RootPairing.Equiv.toHom_one, _root_.RootPairing.Hom.weightMap_one,
    LinearMap.id_coe, id_eq] at hvalue
  have haction := weightMap_e6GraphAut_apply (Pi.single (5 : Fin 6) 1) (0 : Fin 6)
  have hbad := haction.symm.trans hvalue
  simp only [graphPermE6_apply_zero, Pi.single_apply] at hbad
  change (1 : ℤ) = 0 at hbad
  norm_num at hbad

/-- The induced root permutation preserves the support of the pinned type-`E₆` base. Together with
`RootPairing.Base.support_map_eq`, this computes the support of the transported base. -/
@[simp] theorem image_e6GraphIndexEquiv_e6SimplyConnectedBase_support :
    e6SimplyConnectedBase.support.image e6GraphIndexEquiv =
      e6SimplyConnectedBase.support := by
  have hmem : ∀ j : Fin 72, j ∈ e6SimplyConnectedBase.support →
      e6GraphIndexEquiv j ∈ e6SimplyConnectedBase.support := by
    intro j hj
    rw [mem_e6SimplyConnectedBase_support] at hj ⊢
    let a : Fin 6 := ⟨j, hj⟩
    have hja : j = e6SimpleIndex a := by
      apply Fin.ext
      rw [e6SimpleIndex_val]
    rw [hja, e6GraphIndexEquiv_e6SimpleIndex, e6SimpleIndex_val]
    exact (graphPermE6 a).isLt
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hmem j hj
  · intro hi
    exact ⟨e6GraphIndexEquiv i, hmem i hi, e6GraphIndexEquiv_apply_apply i⟩

end

end TauCeti.DynkinType
