/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End

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

section

variable {R : Type u} {I : Type v}
variable [CommRing R] [DecidableEq I]

/-- A list containing every element of the index type has indicator product one exactly when two
finite labels agree, and zero otherwise. -/
theorem listProd_indicator_eq_if_eq (l : List I) (hl : ∀ i, i ∈ l) (s t : Finset I) :
    (l.map fun i ↦ if (i ∈ s ↔ i ∈ t) then (1 : R) else 0).prod = if s = t then 1 else 0 := by
  classical
  by_cases hst : s = t
  · subst t
    simp only [iff_self, ite_true]
    have hall : l.map (fun _ ↦ (1 : R)) = List.replicate l.length 1 := by
      apply List.eq_replicate_iff.mpr
      simp
    rw [hall, List.prod_replicate, one_pow]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ s ↔ i ∈ t) := by
      contrapose! hst
      exact Finset.ext hst
    have hzero : (0 : R) ∈ l.map (fun i ↦ if (i ∈ s ↔ i ∈ t) then 1 else 0) := by
      apply List.mem_map.mpr
      exact ⟨i, hl i, by simp [hi]⟩
    simp only [hst, ite_false]
    exact List.prod_eq_zero hzero

end

end Module.End

end TauCeti
