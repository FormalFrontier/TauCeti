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

This file records the type-`E₆` nontriviality consequence of applying the general
diagram-automorphism construction `TauCeti.DynkinType.diagramAut` to the order-two symmetry
`TauCeti.graphPermE6` of the Bourbaki-numbered `E₆` diagram. Preservation of the pinned base is
the specialization of the generic simp theorem
`TauCeti.DynkinType.image_diagramRootPerm_simplyConnectedBase_support`.

## Main declarations

* `TauCeti.DynkinType.diagramAut_graphPermE6_ne_one`: the induced automorphism is nontrivial.

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
  intro h
  have hσ_one : graphPermE6 = 1 := (diagramAut_eq_one_iff valid_E6 hσ).mp h
  have hzero := congrArg (fun e : Equiv.Perm (Fin 6) => e 0) hσ_one
  simp only [graphPermE6_apply_zero, Equiv.Perm.one_def, Equiv.refl_apply] at hzero
  omega

end

end TauCeti.DynkinType
