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

This file records two type-`E₆` consequences of applying the general diagram-automorphism
construction `TauCeti.DynkinType.diagramAut` to the order-two symmetry `TauCeti.graphPermE6` of
the Bourbaki-numbered `E₆` diagram: nontriviality and preservation of the pinned base.

## Main declarations

* `TauCeti.DynkinType.diagramAut_graphPermE6_ne_one`: the induced automorphism is nontrivial.
* `TauCeti.DynkinType.image_diagramRootPerm_e6SimplyConnectedBase_support`: the induced root
  permutation preserves the pinned-base support.

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

/-- The type-`E₆` graph automorphism is nontrivial: it exchanges the first and sixth simple
roots. -/
theorem diagramAut_graphPermE6_ne_one :
    diagramAut valid_E6 (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6) ≠ 1 := by
  let hσ : graphPermE6 ∈ E6.diagramSymmetry :=
    mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6
  change diagramAut valid_E6 hσ ≠ 1
  let x : Fin 6 → ℤ := Pi.single 5 1
  intro h
  have hvalue := congrArg (fun g => g.weightMap x (0 : Fin 6)) h
  simp only [_root_.RootPairing.Equiv.toHom_one, _root_.RootPairing.Hom.weightMap_one,
    LinearMap.id_coe] at hvalue
  have hsymm : graphPermE6.symm = graphPermE6 :=
    (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using graphPermE6_sq)).symm
  have hmap := diagramAut_weightMap valid_E6 hσ
  have hx := LinearMap.congr_fun hmap x
  have haction := congrFun hx (0 : Fin 6)
  have heval :
      (LinearEquiv.funCongrLeft ℤ ℤ graphPermE6.symm) x 0 = x (graphPermE6 0) := by
    change x (graphPermE6.symm 0) = x (graphPermE6 0)
    rw [hsymm]
  have haction' := haction.trans heval
  have hbad := haction'.symm.trans hvalue
  simp only [x, graphPermE6_apply_zero, Pi.single_apply] at hbad
  change (1 : ℤ) = 0 at hbad
  norm_num at hbad

/-- The induced root permutation preserves the support of the pinned type-`E₆` base. Together with
`RootPairing.Base.support_map_eq`, this computes the support of the transported base. -/
theorem image_diagramRootPerm_e6SimplyConnectedBase_support :
    e6SimplyConnectedBase.support.image
        (diagramRootPerm valid_E6
          (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6) : Equiv.Perm (Fin 72)) =
      e6SimplyConnectedBase.support := by
  let hσ : graphPermE6 ∈ E6.diagramSymmetry :=
    mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6
  let p : Equiv.Perm (Fin 72) := diagramRootPerm valid_E6 hσ
  change e6SimplyConnectedBase.support.image p = e6SimplyConnectedBase.support
  have hsimple (a : Fin 6) :
      p (e6SimpleIndex a) = e6SimpleIndex (graphPermE6 a) := by
    have ha : E6.simpleIndex valid_E6 a = e6SimpleIndex a := by
      apply Fin.ext
      simpa only [e6SimpleIndex_val] using simpleIndex_val E6 valid_E6 a
    have hσa : E6.simpleIndex valid_E6 (graphPermE6 a) =
        e6SimpleIndex (graphPermE6 a) := by
      apply Fin.ext
      simpa only [e6SimpleIndex_val] using simpleIndex_val E6 valid_E6 (graphPermE6 a)
    rw [← ha]
    change diagramRootPerm valid_E6 hσ (E6.simpleIndex valid_E6 a) = _
    exact (diagramRootPerm_simpleIndex valid_E6 hσ a).trans hσa
  have hmem : ∀ j : Fin 72, j ∈ e6SimplyConnectedBase.support →
      p j ∈ e6SimplyConnectedBase.support := by
    intro j hj
    rw [mem_e6SimplyConnectedBase_support] at hj ⊢
    let a : Fin 6 := ⟨j, hj⟩
    have hja : j = e6SimpleIndex a := by
      apply Fin.ext
      rw [e6SimpleIndex_val]
    rw [hja, hsimple, e6SimpleIndex_val]
    exact (graphPermE6 a).isLt
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hmem j hj
  · intro hi
    rw [mem_e6SimplyConnectedBase_support] at hi
    let a : Fin 6 := ⟨i, hi⟩
    refine ⟨e6SimpleIndex (graphPermE6 a), ?_, ?_⟩
    · rw [mem_e6SimplyConnectedBase_support, e6SimpleIndex_val]
      exact (graphPermE6 a).isLt
    · rw [hsimple]
      have haa : graphPermE6 (graphPermE6 a) = a := by
        have ha := congrArg (fun e : Equiv.Perm (Fin 6) => e a) graphPermE6_sq
        simp only [pow_two, Equiv.Perm.mul_apply] at ha
        change graphPermE6 (graphPermE6 a) = a at ha
        exact ha
      rw [haa]
      apply Fin.ext
      rw [e6SimpleIndex_val]

end

end TauCeti.DynkinType
