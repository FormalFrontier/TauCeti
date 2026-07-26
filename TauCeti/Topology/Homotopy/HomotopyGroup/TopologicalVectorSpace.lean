/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Homotopy groups of a real topological vector space

Any two generalized loops with the same basepoint in a real topological vector space are
homotopic relative to the cube boundary: Mathlib's affine homotopy
`ContinuousMap.Homotopy.affine`, which interpolates linearly at each point of the cube, is
constant at the basepoint on the boundary. Consequently every homotopy group of such a space
is a subsingleton.

## Main declarations

* `TauCeti.GenLoop.homotopic_of_topologicalVectorSpace`: generalized loops in a real
  topological vector space with the same basepoint are homotopic.
* `TauCeti.HomotopyGroup.subsingleton_of_topologicalVectorSpace`: all homotopy groups of a
  real topological vector space are subsingletons.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy

variable {N E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {x : E}

namespace GenLoop

/-- Any two generalized loops based at the same point in a real topological vector space are
homotopic relative to the cube boundary. The homotopy is pointwise linear interpolation. -/
theorem homotopic_of_topologicalVectorSpace (f g : Ω^ N E x) :
    _root_.GenLoop.Homotopic f g :=
  ⟨{ toHomotopy := .affine f.1 g.1
     prop' := fun _ u hu ↦ by
       simp [_root_.GenLoop.boundary f u hu, _root_.GenLoop.boundary g u hu] }⟩

end GenLoop

namespace HomotopyGroup

/-- Every homotopy group of a real topological vector space is a subsingleton. This includes
dimension zero: a real topological vector space is path connected. -/
theorem subsingleton_of_topologicalVectorSpace : Subsingleton (HomotopyGroup N E x) := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b fun f g ↦ ?_
  exact Quotient.sound (GenLoop.homotopic_of_topologicalVectorSpace f g)

end HomotopyGroup

end TauCeti
