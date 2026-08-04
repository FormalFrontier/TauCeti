/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Units

/-!
# Coprime lifting from `ZMod d`

Coprime residues modulo `d` lift to coprime integers (`IsCoprime.exists_int_lifts`).

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/SL2Surjection.lean`, Chris Birkbeck); the consumer is the
strong approximation theorem `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective` in
`TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup.lean`.
-/

public section

variable {d : ℕ}

private lemma isCoprime_emod {a₁ c₁ : ℤ}
    (hac : IsCoprime (a₁ : ZMod d) (c₁ : ZMod d)) :
    IsCoprime (c₁ : ZMod d) ((a₁ % c₁ : ℤ) : ZMod d) := by
  have h : (a₁ % c₁ : ℤ) = a₁ + c₁ * (-(a₁ / c₁)) := by rw [Int.emod_def]; ring
  rw [h]
  push_cast
  exact hac.symm.add_mul_left_right _

/-- Coprime residues modulo `d` lift to coprime integers: if `a` and `c` are coprime in
`ZMod d`, there are integers `a₀`, `c₀` reducing to `a`, `c` with `IsCoprime a₀ c₀`. -/
theorem IsCoprime.exists_int_lifts {a c : ZMod d}
    (hac : IsCoprime a c) :
    ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a ∧ (c₀ : ZMod d) = c ∧ IsCoprime a₀ c₀ := by
  obtain ⟨a₁, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨c₁, rfl⟩ := ZMod.intCast_surjective c
  suffices h : ∀ n, ∀ a₁ c₁ : ℤ, c₁.natAbs ≤ n →
      IsCoprime (a₁ : ZMod d) (c₁ : ZMod d) →
      ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = c₁ ∧ IsCoprime a₀ c₀ from
    h c₁.natAbs a₁ c₁ le_rfl hac
  have zero_case : ∀ a₁ : ℤ, IsCoprime (a₁ : ZMod d) 0 →
      ∃ a₀ c₀ : ℤ,
        (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = 0 ∧ IsCoprime a₀ c₀ := by
    intro a₁ hac
    have hunit : IsUnit (a₁ : ZMod d) := by rwa [isCoprime_zero_right] at hac
    rw [ZMod.coe_int_isUnit_iff_isCoprime] at hunit
    exact ⟨a₁, d, rfl, by simp, hunit.symm⟩
  intro n
  induction n with
  | zero =>
    intro a₁ c₁ hle hac
    have hc₁ : c₁ = 0 := by omega
    subst hc₁
    simpa using zero_case a₁ (by simpa using hac)
  | succ n ih =>
    intro a₁ c₁ hle hac
    by_cases hc₁ : c₁ = 0
    · subst hc₁; simpa using zero_case a₁ (by simpa using hac)
    obtain ⟨c₀, r₀, hc₀, hr₀, hcop⟩ := ih c₁ (a₁ % c₁)
      (Nat.lt_succ_iff.mp ((EuclideanDomain.remainder_lt a₁ hc₁).trans_le hle)) (isCoprime_emod hac)
    refine ⟨r₀ + a₁ / c₁ * c₀, c₀, ?_, hc₀, hcop.symm.add_mul_right_left _⟩
    conv_rhs => rw [← Int.emod_add_ediv_mul a₁ c₁]
    push_cast
    rw [hr₀, hc₀]
