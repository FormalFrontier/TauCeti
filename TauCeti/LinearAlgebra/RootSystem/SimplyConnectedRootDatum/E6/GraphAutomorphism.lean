/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic

/-!
# Nontriviality of the type `E₆` diagram automorphism

This file records the type-`E₆` nontriviality consequence of applying the general
`TauCeti.DynkinType.diagramAut` construction to the order-two symmetry
`TauCeti.graphPermE6` of the Bourbaki-numbered diagram. The automorphism itself and its order-two
relation remain expressed through the generic API, without introducing type-specific aliases.

## Main declarations

* `TauCeti.DynkinType.diagramAut_graphPermE6_ne_one`: the diagram automorphism induced by
  `TauCeti.graphPermE6` is nontrivial.

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

end

end TauCeti.DynkinType
