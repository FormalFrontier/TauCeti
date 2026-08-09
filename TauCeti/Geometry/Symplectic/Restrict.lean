/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Symplectic forms along complementary subspaces

A symplectic form that restricts nondegenerately to a subspace and its symplectic complement is
the product of those restrictions under the linear equivalence supplied by a complementary
splitting.

## Main declaration

* `TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`: the equivalence associated to
  `V = L ⊕ L^ω` is a symplectomorphism from the product of the restricted forms to `ω`.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Along the splitting `V = L ⊕ L^ω`, the symplectic form is the product of its restrictions to
the two summands: the cross terms vanish by the very definition of the symplectic complement. -/
lemma isSymplectomorphism_prodEquivOfIsCompl (ω : SymplecticForm V) {L : Submodule ℝ V}
    (hL : (ω.toBilinForm.restrict L).Nondegenerate)
    (hL' : (ω.toBilinForm.restrict (ω.orthogonal L)).Nondegenerate)
    (hcompl : IsCompl L (ω.orthogonal L)) :
    IsSymplectomorphism ((ω.restrict L hL).prod (ω.restrict (ω.orthogonal L) hL')) ω
      (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl) := by
  rw [isSymplectomorphism_iff]
  intro p q
  have h₁ : ω (p.1 : V) (q.2 : V) = 0 := mem_orthogonal_iff.1 q.2.2 _ p.1.2
  have h₂ : ω (p.2 : V) (q.1 : V) = 0 := mem_orthogonal_iff'.1 p.2.2 _ q.1.2
  simp only [Submodule.coe_prodEquivOfIsCompl', prod_apply, restrict_apply, map_add,
    LinearMap.add_apply, h₁, h₂]
  ring

end SymplecticForm

end TauCeti
