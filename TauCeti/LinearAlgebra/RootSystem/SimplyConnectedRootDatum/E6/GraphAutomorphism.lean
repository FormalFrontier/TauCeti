/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight

/-!
# The type `E₆` diagram automorphism on the pinned root datum

This file records the type-`E₆` consequences of applying the general
`TauCeti.DynkinType.diagramAut` construction to the order-two symmetry
`TauCeti.graphPermE6` of the Bourbaki-numbered diagram: that it is nontrivial, and how it moves
the minuscule weights. The automorphism itself and its order-two relation remain expressed through
the generic API, without introducing type-specific aliases.

Its weight map is the pullback of a character along the diagram symmetry, so it acts on the
weight tables of `TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/E6/MinusculeWeight.lean`
by permuting coordinates. It does not preserve the twenty-seven minuscule weights, and does
permute the fifty-four weights of `V(ϖ₁) ⊕ V(ϖ₆)`.

## Main declarations

* `TauCeti.DynkinType.diagramAut_graphPermE6_ne_one`: the diagram automorphism induced by
  `TauCeti.graphPermE6` is nontrivial.
* `TauCeti.DynkinType.diagramAut_weightMap_graphPermE6`: its weight map is precomposition with
  `TauCeti.graphPermE6`.
* `TauCeti.DynkinType.diagramAut_weightMap_e6DoubledMinusculeWeight`: it permutes the doubled
  minuscule weight family, along `TauCeti.DynkinType.e6DoubledMinusculeGraphPerm`.
* `TauCeti.DynkinType.diagramAut_weightMap_e6MinusculeWeight_notMem_range`: it does not
  preserve the minuscule weight family alone.

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

/-- The canonical diagram automorphism induced by the nontrivial symmetry of the
Bourbaki-numbered type-`E₆` diagram is nontrivial. -/
theorem diagramAut_graphPermE6_ne_one :
    diagramAut valid_E6 (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6) ≠ 1 := by
  intro h
  have hσ_one : graphPermE6 = 1 :=
    (diagramAut_eq_one_iff valid_E6
      (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6)).mp h
  simpa [hσ_one] using orderOf_graphPermE6

/-- The weight map of the type-`E₆` diagram automorphism is precomposition with the diagram
symmetry, which is an involution. -/
theorem diagramAut_weightMap_graphPermE6 (x : Fin 6 → ℤ) :
    (diagramAut valid_E6
        (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6)).toHom.weightMap x =
      x ∘ graphPermE6 := by
  have h : (diagramAut valid_E6
      (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6)).toHom.weightMap x =
      x ∘ graphPermE6.symm :=
    (LinearMap.congr_fun (diagramAut_weightMap valid_E6
      (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6)) x).trans
      (funext fun i =>
        (congrFun (LinearEquiv.funCongrLeft_apply ℤ ℤ graphPermE6.symm x) i).trans
          (LinearMap.funLeft_apply ℤ ℤ graphPermE6.symm x i))
  rw [h, graphPermE6_symm]

/-- **The type-`E₆` diagram automorphism permutes the doubled minuscule weight family.** This is
`TauCeti.DynkinType.e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm` read on the character
lattice of the pinned root datum. -/
theorem diagramAut_weightMap_e6DoubledMinusculeWeight (x : Fin 27 ⊕ Fin 27) :
    (diagramAut valid_E6
        (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6)).toHom.weightMap
        (e6DoubledMinusculeWeight x) =
      e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm x) := by
  rw [diagramAut_weightMap_graphPermE6]
  exact funext fun i => (e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm x i).symm

/-- **The type-`E₆` diagram automorphism moves every minuscule weight off the family.** At the
highest weight it sends `ϖ₁` to `ϖ₆`, which is not a weight of `V(ϖ₁)`. -/
theorem diagramAut_weightMap_e6MinusculeWeight_notMem_range (a : Fin 27) :
    (diagramAut valid_E6
        (mem_diagramSymmetry_iff.mpr cartanMatrix_E6_graphPermE6)).toHom.weightMap
        (e6MinusculeWeight a) ∉ Set.range e6MinusculeWeight := by
  rw [diagramAut_weightMap_graphPermE6]
  exact e6MinusculeWeight_comp_graphPermE6_notMem_range a

end

end TauCeti.DynkinType
