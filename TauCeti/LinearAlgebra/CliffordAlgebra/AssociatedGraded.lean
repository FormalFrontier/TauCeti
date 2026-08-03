/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# Homogeneous multiplication for a Clifford filtration

This file defines the successive quotient pieces of the Clifford degree filtration and lifts
Clifford multiplication to a bilinear product between any two homogeneous pieces.

This is the multiplication prerequisite for the Layer 0 associated-graded comparison in the spin
representations roadmap. It is generic in the quadratic form and does not yet package the direct
sum as a graded algebra or identify it with the exterior algebra.
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The filtration step preceding degree `k`. At degree zero it is bottom, so the degree-zero
piece remains the scalar filtration step rather than a zero quotient. -/
def filtrationPrevious (Q : QuadraticForm R M) : ℕ → Submodule R (CliffordAlgebra Q)
  | 0 => ⊥
  | k + 1 => filtration Q k

-- Parenthesized `rfl` exports the intended reduction API without exposing the definition.
@[simp]
theorem filtrationPrevious_zero (Q : QuadraticForm R M) : filtrationPrevious Q 0 = ⊥ :=
  (rfl)

@[simp]
theorem filtrationPrevious_succ (Q : QuadraticForm R M) (k : ℕ) :
    filtrationPrevious Q (k + 1) = filtration Q k :=
  (rfl)

/-- The degree-`k` piece of the associated graded Clifford filtration. -/
abbrev filtrationGradedPiece (Q : QuadraticForm R M) (k : ℕ) : Type max u v :=
  filtration Q k ⧸
    Submodule.comap (filtration Q k).subtype (filtrationPrevious Q k)

private theorem mul_mem_filtrationPrevious_left (Q : QuadraticForm R M) (i j : ℕ)
    {x y : CliffordAlgebra Q} (hx : x ∈ filtrationPrevious Q i) (hy : y ∈ filtration Q j) :
    x * y ∈ filtrationPrevious Q (i + j) := by
  cases i with
  | zero =>
      rw [filtrationPrevious_zero] at hx
      rw [Submodule.mem_bot] at hx
      subst x
      simp
  | succ i =>
      rw [filtrationPrevious_succ] at hx
      rw [Nat.succ_add, filtrationPrevious_succ, ← filtration_mul]
      exact Submodule.mul_mem_mul hx hy

private theorem mul_mem_filtrationPrevious_right (Q : QuadraticForm R M) (i j : ℕ)
    {x y : CliffordAlgebra Q} (hx : x ∈ filtration Q i) (hy : y ∈ filtrationPrevious Q j) :
    x * y ∈ filtrationPrevious Q (i + j) := by
  cases j with
  | zero =>
      rw [filtrationPrevious_zero] at hy
      rw [Submodule.mem_bot] at hy
      subst y
      simp
  | succ j =>
      rw [filtrationPrevious_succ] at hy
      rw [Nat.add_succ, filtrationPrevious_succ, ← filtration_mul]
      exact Submodule.mul_mem_mul hx hy

private noncomputable def filtrationMul (Q : QuadraticForm R M) (i j : ℕ) :
    filtration Q i →ₗ[R] filtration Q j →ₗ[R] filtration Q (i + j) :=
  TensorProduct.curry
    ((LinearEquiv.ofEq _ _ (filtration_mul Q i j)).toLinearMap ∘ₗ
      Submodule.mulMap' (filtration Q i) (filtration Q j))

private noncomputable def filtrationGradedPreMul (Q : QuadraticForm R M) (i j : ℕ) :
    filtration Q i →ₗ[R] filtration Q j →ₗ[R] filtrationGradedPiece Q (i + j) :=
  (filtrationMul Q i j).compr₂ (Submodule.mkQ _)

private theorem filtrationGradedPreMul_mem_ker_left (Q : QuadraticForm R M) (i j : ℕ) :
    Submodule.comap (filtration Q i).subtype (filtrationPrevious Q i) ≤
      (filtrationGradedPreMul Q i j).ker := by
  rintro ⟨x, hx⟩ hprevious
  rw [LinearMap.mem_ker]
  ext y
  -- Expose the quotient representative before using its zero-class membership criterion.
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero]
  -- The filtration product lemma is stated for ambient Clifford-algebra elements.
  change (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q) ∈ filtrationPrevious Q (i + j)
  exact mul_mem_filtrationPrevious_left Q i j hprevious y.property

private theorem filtrationGradedPreMul_mem_ker_right (Q : QuadraticForm R M) (i j : ℕ) :
    Submodule.comap (filtration Q j).subtype (filtrationPrevious Q j) ≤
      (filtrationGradedPreMul Q i j).flip.ker := by
  rintro ⟨y, hy⟩ hprevious
  rw [LinearMap.mem_ker]
  ext x
  -- Expose the quotient representative before using its zero-class membership criterion.
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero]
  -- The filtration product lemma is stated for ambient Clifford-algebra elements.
  change (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q) ∈ filtrationPrevious Q (i + j)
  exact mul_mem_filtrationPrevious_right Q i j x.property hprevious

/-- Multiplication of two homogeneous pieces of the Clifford associated graded algebra. -/
noncomputable def filtrationGradedMul (Q : QuadraticForm R M) (i j : ℕ) :
    filtrationGradedPiece Q i →ₗ[R] filtrationGradedPiece Q j →ₗ[R]
      filtrationGradedPiece Q (i + j) :=
  (filtrationGradedPreMul Q i j).liftQ₂ _ _
    (filtrationGradedPreMul_mem_ker_left Q i j)
    (filtrationGradedPreMul_mem_ker_right Q i j)

/-- On quotient representatives, the homogeneous product is induced by Clifford multiplication. -/
@[simp]
theorem filtrationGradedMul_apply_mk (Q : QuadraticForm R M) (i j : ℕ) (x : filtration Q i)
    (y : filtration Q j) :
    filtrationGradedMul Q i j (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (⟨(x : CliffordAlgebra Q) * y, by
          rw [← filtration_mul Q i j]
          exact Submodule.mul_mem_mul x.property y.property⟩ : filtration Q (i + j)) :=
  by
  rw [filtrationGradedMul, LinearMap.liftQ₂_mk]
  rfl

private theorem filtrationGradedPiece_cast_mk' (Q : QuadraticForm R M) {i j : ℕ}
    (h : i = j) (x : filtration Q i) :
    cast (congrArg (filtrationGradedPiece Q) h) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cast (congrArg (fun k => ↥(filtration Q k)) h) x) := by
  subst j
  rfl

private theorem filtration_subtype_cast (Q : QuadraticForm R M) {i j : ℕ}
    (h : i = j) (x : filtration Q i) :
    (filtration Q j).subtype (cast (congrArg (fun k => ↥(filtration Q k)) h) x) = x := by
  subst j
  rfl

/-- Homogeneous Clifford filtration multiplication is associative after reindexing degrees. -/
theorem filtrationGradedMul_assoc (Q : QuadraticForm R M) (i j k : ℕ)
    (x : filtrationGradedPiece Q i) (y : filtrationGradedPiece Q j)
    (z : filtrationGradedPiece Q k) :
    cast (congrArg (filtrationGradedPiece Q) (Nat.add_assoc i j k))
      (filtrationGradedMul Q (i + j) k (filtrationGradedMul Q i j x y) z) =
      filtrationGradedMul Q i (j + k) x (filtrationGradedMul Q j k y z) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          induction z using Submodule.Quotient.induction_on with
          | _ z =>
              simp only [filtrationGradedMul_apply_mk]
              rw [filtrationGradedPiece_cast_mk' Q (Nat.add_assoc i j k)]
              apply (Submodule.Quotient.eq _).mpr
              rw [Submodule.mem_comap, map_sub,
                filtration_subtype_cast Q (Nat.add_assoc i j k)]
              change ((x : CliffordAlgebra Q) * y) * z - x * (y * z) ∈
                filtrationPrevious Q (i + (j + k))
              rw [mul_assoc, sub_self]
              exact Submodule.zero_mem (filtrationPrevious Q (i + (j + k)))

end CliffordAlgebra

end TauCeti
