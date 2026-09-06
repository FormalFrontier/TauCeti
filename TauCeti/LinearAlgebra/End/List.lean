/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Fintype.Basic

/-!
# List products of diagonal endomorphisms

This file contains the small generic combinators used by basis-diagonal projector
constructions on exterior algebras and exterior powers.
-/

public section

namespace TauCeti

namespace Module.End

universe u v w

variable {R : Type u} {M : Type v} {I : Type w} {S : Type*}

section

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A list product of endomorphisms acts by the product of its eigenvalues on a common
eigenvector. -/
theorem listProd_apply_eq_smul (f : I → Module.End R M) (c : I → R) (x : M) (l : List I)
    (h : ∀ i ∈ l, f i x = c i • x) :
    (l.map f).prod x = (l.map c).prod • x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj)), map_smul, h i (List.mem_cons_self)]
    rw [smul_smul, mul_comm ((l.map c).prod) (c i)]

end

end Module.End

namespace Module.End

section

variable {R : Type u} {M : Type v} {I : Type w} {S : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Fintype I] [DecidableEq I]

/-- The product of a family of endomorphisms over a coordinate list.

The selected parameter is explicit so this combinator can represent both occupation/vacancy and
other diagonal factor families. -/
noncomputable def basisDiagonalProjector (coords : List I)
    (factor : S → I → Module.End R M) (s : S) : Module.End R M :=
  (coords.map (factor s)).prod

omit [Fintype I] [DecidableEq I] in
/-- The defining equation for `basisDiagonalProjector`, exposed for clients in module-style files
where the definition itself is opaque. -/
theorem basisDiagonalProjector_eq_listProd (coords : List I)
    (factor : S → I → Module.End R M) (s : S) :
    basisDiagonalProjector coords factor s = (coords.map (factor s)).prod := by
  rfl

end

end Module.End

end TauCeti
