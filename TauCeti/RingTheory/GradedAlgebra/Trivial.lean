/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The trivial grading of an algebra

Every algebra has a grading concentrated in degree zero.  This file packages that grading in the
internal `GradedAlgebra` presentation and records its elementary membership and projection API.
It is the canonical target grading for augmentations of integer-graded algebras.

## Main definitions

* `TauCeti.trivialGrading`: the internal integer grading with the whole algebra in degree zero.

## Main results

* `TauCeti.instGradedAlgebraTrivialGrading`: the trivial grading is a graded algebra.
* `TauCeti.proj_trivialGrading`: its degree projection is the identity in degree zero and zero in
  every other degree.
-/

public section

open DirectSum

namespace TauCeti

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- The trivial integer grading of an `R`-algebra: all elements have degree zero and every other
homogeneous piece is zero. -/
def trivialGrading (p : ℤ) : Submodule R A :=
  if p = 0 then ⊤ else ⊥

/-- The degree-zero piece of the trivial grading is the whole algebra. -/
@[simp]
theorem trivialGrading_zero : trivialGrading R A 0 = ⊤ := by
  simp [trivialGrading]

/-- Every nonzero-degree piece of the trivial grading is zero. -/
theorem trivialGrading_eq_bot {p : ℤ} (hp : p ≠ 0) : trivialGrading R A p = ⊥ := by
  simp [trivialGrading, hp]

/-- An element belongs to degree `p` of the trivial grading exactly when `p = 0` or the element
itself is zero. -/
@[simp]
theorem mem_trivialGrading_iff {p : ℤ} {a : A} :
    a ∈ trivialGrading R A p ↔ p = 0 ∨ a = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [trivialGrading, hp]

noncomputable instance instGradedAlgebraTrivialGrading :
    GradedAlgebra (trivialGrading R A) := by
  letI : SetLike.GradedMonoid (trivialGrading R A) := {
    one_mem := by simp
    mul_mem := by
      intro p q a b ha hb
      rcases (mem_trivialGrading_iff R A).mp ha with rfl | rfl
      · rcases (mem_trivialGrading_iff R A).mp hb with rfl | rfl <;> simp
      · simp }
  apply DirectSum.IsInternal.gradedAlgebra
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro p
    by_cases hp : p = 0
    · subst hp
      simp only [trivialGrading_zero, top_disjoint, iSup_eq_bot]
      exact fun i hi ↦ trivialGrading_eq_bot R A hi
    · rw [trivialGrading_eq_bot R A hp]
      exact disjoint_bot_left
  · apply top_unique
    exact le_iSup_of_le 0 (by simp)

/-- The homogeneous projection for the trivial grading is the identity in degree zero and the
zero map in every other degree. -/
@[simp]
theorem proj_trivialGrading (p : ℤ) (a : A) :
    GradedRing.proj (trivialGrading R A) p a = if p = 0 then a else 0 := by
  rw [GradedRing.proj_apply]
  by_cases hp : p = 0
  · subst hp
    rw [ite_eq_left rfl]
    exact DirectSum.decompose_of_mem_same (trivialGrading R A)
      (show a ∈ trivialGrading R A 0 by simp)
  · rw [DirectSum.decompose_of_mem_ne _
      (show a ∈ trivialGrading R A 0 by simp) (Ne.symm hp)]
    simp [hp]

/-- Scalar multiplication by the trivially graded base ring preserves every homogeneous piece of
an internally graded algebra. -/
instance instGradedSMulTrivialGrading (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :
    SetLike.GradedSMul (trivialGrading R R) 𝒜 where
  smul_mem := by
    intro p q r a hr ha
    rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
    · simpa using (𝒜 q).smul_mem r ha
    · simp

end TauCeti
