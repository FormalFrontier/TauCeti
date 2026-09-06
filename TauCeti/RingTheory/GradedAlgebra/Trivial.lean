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
* `TauCeti.toTrivialGradingZero`: the algebra viewed as the degree-zero piece of that grading.

## Main results

* `TauCeti.instGradedAlgebraTrivialGrading`: the trivial grading is a graded algebra.
* `TauCeti.proj_trivialGrading`: its degree projection is the identity in degree zero and zero in
  every other degree.
-/

public section

open DirectSum

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

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

/-- Every element of the algebra, viewed as an element of the degree-zero piece of the trivial
grading. -/
def toTrivialGradingZero : A →+ trivialGrading R A 0 where
  toFun a := ⟨a, by simp⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_toTrivialGradingZero (a : A) : (toTrivialGradingZero R A a : A) = a := (rfl)

/-- The trivial grading is an internal grading: an element is its own degree-zero component, and
all higher components vanish. -/
instance instGradedAlgebraTrivialGrading : GradedAlgebra (trivialGrading R A) where
  one_mem := by simp
  mul_mem := by
    intro p q a b ha hb
    rcases (mem_trivialGrading_iff R A).mp ha with rfl | rfl
    · rcases (mem_trivialGrading_iff R A).mp hb with rfl | rfl <;> simp
    · simp
  decompose' a := DirectSum.of (fun p ↦ trivialGrading R A p) 0 (toTrivialGradingZero R A a)
  left_inv a := by simp
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      rw [DirectSum.coeAddMonoidHom_of]
      by_cases hp : p = 0
      · subst hp
        exact congrArg _ (Subtype.ext rfl)
      · have hy : y = 0 :=
          Subtype.ext (((mem_trivialGrading_iff R A).mp y.2).resolve_left hp)
        rw [hy]
        simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The homogeneous projection for the trivial grading is the identity in degree zero and the
zero map in every other degree. -/
@[simp]
theorem proj_trivialGrading (p : ℤ) (a : A) :
    ((DirectSum.decompose (trivialGrading R A) a) p : A) = if p = 0 then a else 0 := by
  have ha : a ∈ trivialGrading R A 0 := by simp
  by_cases hp : p = 0
  · subst hp
    rw [ite_eq_left rfl]
    exact DirectSum.decompose_of_mem_same (trivialGrading R A) ha
  · rw [DirectSum.decompose_of_mem_ne _ ha (Ne.symm hp)]
    simp [hp]

/-- Scalar multiplication by the trivially graded base ring preserves every homogeneous piece of
an internally graded algebra. -/
instance instGradedSMulTrivialGrading (𝒜 : ℤ → Submodule R A) :
    SetLike.GradedSMul (trivialGrading R R) 𝒜 where
  smul_mem := by
    intro p q r a hr ha
    rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
    · simpa using (𝒜 q).smul_mem r ha
    · simp

end TauCeti
