/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Values represented by quadratic forms

This file defines representation of values by a quadratic map and the represented-unit value set.
It proves the elementary square-class invariance of the latter and the criterion that, for a form
with trivial radical, representing a unit is equivalent to isotropy after adjoining the
one-dimensional form with that unit as its negative coefficient. A nondegenerate form has trivial
radical by Mathlib's `radical_eq_bot` theorem. These results provide the basic bridge from value
questions to isotropy questions, following Lam, *Introduction to Quadratic Forms over Fields*,
I.2.3 and I.3.5.
-/

public section

open _root_.QuadraticMap

namespace TauCeti

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A value `a : N` is represented by a quadratic map if it is the value of the map at a vector. -/
def _root_.QuadraticMap.Represents (Q : QuadraticMap R M N) (a : N) : Prop := ∃ v, Q v = a

/-- Every quadratic map represents zero. -/
@[simp]
theorem _root_.QuadraticMap.represents_zero (Q : QuadraticMap R M N) : Represents Q 0 :=
  ⟨0, Q.map_zero⟩

/-- Representation is the same as membership in the range of the quadratic map. -/
theorem _root_.QuadraticMap.represents_iff (Q : QuadraticMap R M N) (a : N) :
    Represents Q a ↔ a ∈ Set.range Q :=
  Iff.rfl

/-- The set of represented units of a scalar-valued quadratic map.

This is the classical value set `D(Q)` over a field; over a general commutative semiring it is
the set of units represented by `Q`, rather than the full value set. -/
def _root_.QuadraticMap.unitValueSet (Q : QuadraticMap R M R) : Set Rˣ :=
  {a | Represents Q (a : R)}

/-- Membership in `unitValueSet` is representation of the underlying scalar. -/
@[simp]
theorem _root_.QuadraticMap.mem_unitValueSet {Q : QuadraticMap R M R} {a : Rˣ} :
    a ∈ unitValueSet Q ↔ Represents Q (a : R) :=
  Iff.rfl

/-- Representation is preserved by an isometric equivalence of quadratic maps. -/
theorem _root_.QuadraticMap.IsometryEquiv.represents_iff
    {M₁ M₂ N : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N]
    [Module R M₁] [Module R M₂] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (a : N) :
    Represents Q₁ a ↔ Represents Q₂ a := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨e v, (e.map_app v).trans hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨e.symm v, (e.symm.map_app v).trans hv⟩

/-- Equivalent quadratic forms have the same represented-unit value set. -/
theorem _root_.QuadraticMap.Equivalent.unitValueSet_eq
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (h : Q₁.Equivalent Q₂) : unitValueSet Q₁ = unitValueSet Q₂ := by
  obtain ⟨e⟩ := h
  ext a
  rw [mem_unitValueSet, mem_unitValueSet]
  exact e.represents_iff a

/-- A value represented by one factor is represented by the product with any other factor. -/
theorem _root_.QuadraticMap.Represents.prod
    {M₁ M₂ P : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid P]
    [Module R M₁] [Module R M₂] [Module R P]
    {Q₁ : QuadraticMap R M₁ P} {a : P} (h : Represents Q₁ a)
    (Q₂ : QuadraticMap R M₂ P) : Represents (Q₁.prod Q₂) a := by
  obtain ⟨v, hv⟩ := h
  exact ⟨(v, 0), by simp [QuadraticMap.prod_apply, hv]⟩

/-- Representing a value is preserved after multiplying it by the square of any scalar. -/
theorem _root_.QuadraticMap.Represents.smul_mul_self
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {Q : QuadraticMap R M N} {a : N}
    (h : Represents Q a) (b : R) : Represents Q ((b * b) • a) := by
  obtain ⟨v, hv⟩ := h
  exact ⟨b • v, by rw [Q.map_smul, hv]⟩

/-- Representation is invariant under multiplication by the square of a unit. -/
theorem _root_.QuadraticMap.represents_smul_mul_self_iff
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (Q : QuadraticMap R M N) (a : N) (b : Rˣ) :
    Represents Q (((b : R) * b) • a) ↔ Represents Q a := by
  constructor
  · intro h
    simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using
      h.smul_mul_self (↑(b⁻¹ : Rˣ) : R)
  · exact fun h => h.smul_mul_self (b : R)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A quadratic form with trivial radical and a nonzero isotropic vector represents every scalar. -/
theorem _root_.QuadraticMap.represents_of_radical_eq_bot_of_not_anisotropic
    (Q : QuadraticForm K V)
    (hQ : Q.radical = ⊥) (hiso : ¬Q.Anisotropic) (a : K) :
    Represents Q a := by
  obtain ⟨v, hv, hvQ⟩ := (not_anisotropic_iff_exists Q).mp hiso
  obtain ⟨w, hw⟩ : ∃ w, Q.polarBilin v w ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    have hv_rad : v ∈ Q.radical := by
      rw [mem_radical_iff']
      refine ⟨hvQ, ?_⟩
      intro w
      have hw : polar Q v w = 0 := by
        simpa only [polarBilin_apply_apply] using h w
      rw [QuadraticMap.map_add Q, hvQ, hw, zero_add, add_zero]
    rw [hQ] at hv_rad
    simpa only [Submodule.mem_bot] using hv_rad
  have hw' : polar Q v w ≠ 0 := by
    simpa only [polarBilin_apply_apply] using hw
  have hw'' : polar Q w v ≠ 0 := by
    simpa only [polar_comm] using hw'
  refine ⟨w + ((a - Q w) / polar Q v w) • v, ?_⟩
  rw [QuadraticMap.map_add Q, Q.map_smul, smul_eq_mul, hvQ, mul_zero, add_zero,
    polar_smul_right, polar_comm]
  rw [smul_eq_mul]
  field_simp [hw'']
  ring

/-- Multiplying a represented scalar by the square of a unit preserves representation. -/
theorem _root_.QuadraticMap.represents_mul_sq_iff (Q : QuadraticMap R M R) (a : R)
    (b : Rˣ) :
    Represents Q (a * (b : R) ^ 2) ↔ Represents Q a := by
  simpa [smul_eq_mul, pow_two, mul_comm] using
    (represents_smul_mul_self_iff Q a b)

/-- Membership in `unitValueSet` is invariant under multiplication by a unit square. -/
theorem _root_.QuadraticMap.mem_unitValueSet_mul_sq_iff (Q : QuadraticMap R M R) (a b : Rˣ) :
    (a * b ^ 2) ∈ unitValueSet Q ↔ a ∈ unitValueSet Q := by
  simpa only [mem_unitValueSet, Units.val_mul, Units.val_pow_eq_pow_val] using
    (represents_mul_sq_iff Q (a : R) b)

/-- A unit is represented exactly when adjoining its negative line makes the form isotropic, under
triviality of the quadratic radical.

The added line is the one-dimensional form `x ↦ -a * x²`, written as a scalar multiple of
`QuadraticMap.sq`. -/
theorem _root_.QuadraticMap.mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot
    (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) (a : Kˣ) :
    a ∈ unitValueSet Q ↔
      ¬(Q.prod ((-(a : K)) • (QuadraticMap.sq : QuadraticForm K K))).Anisotropic := by
  constructor
  · rw [mem_unitValueSet, represents_iff, Set.mem_range]
    rintro ⟨v, hv⟩
    rw [not_anisotropic_iff_exists]
    refine ⟨(v, 1), ?_, ?_⟩
    · simp
    · simp [QuadraticMap.prod_apply, hv]
  · intro h
    rw [mem_unitValueSet, represents_iff, Set.mem_range]
    obtain ⟨⟨v, t⟩, hvt, hzero⟩ := (not_anisotropic_iff_exists _).mp h
    simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.sq_apply] at hzero
    by_cases ht : t = 0
    · have hv : v ≠ 0 := by
        intro hv
        apply hvt
        simp [hv, ht]
      have hvQ : Q v = 0 := by simpa [ht] using hzero
      obtain ⟨w, hw⟩ := represents_of_radical_eq_bot_of_not_anisotropic Q
        hQ ((not_anisotropic_iff_exists Q).mpr ⟨v, hv, hvQ⟩) (a : K)
      exact ⟨w, hw⟩
    · have hvQ : Q v = (a : K) * (t * t) := by
        linear_combination hzero
      refine ⟨t⁻¹ • v, ?_⟩
      rw [Q.map_smul, smul_eq_mul, hvQ]
      field_simp

end TauCeti
