/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic.LinearCombination
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Values represented by quadratic forms

This file defines representation of a scalar by a quadratic map and the nonzero value set of a
quadratic form. It proves the elementary square-class invariance of the latter and the criterion
that, for a regular form, representing a unit is equivalent to isotropy after adjoining the
one-dimensional form with that unit as its negative coefficient.

The criterion is the basic bridge from value questions to isotropy questions. Its regularity
hypothesis is needed only for the case where the isotropic vector has zero component in the added
line: a regular isotropic form represents every scalar. The representation criterion follows
Lam, *Introduction to Quadratic Forms over Fields*, I.2.3 and I.3.5.
-/

public section

open _root_.QuadraticMap

namespace TauCeti

namespace QuadraticMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A scalar is represented by a quadratic map if it is the value of the map at some vector. -/
def _root_.QuadraticMap.Represents (Q : QuadraticMap R M N) (a : N) : Prop := ∃ v, Q v = a

/-- Every quadratic map represents zero, using the zero vector. -/
theorem _root_.QuadraticMap.represents_zero (Q : QuadraticMap R M N) : Represents Q 0 :=
  ⟨0, Q.map_zero⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The set of nonzero scalars represented by a quadratic form.

This is the classical value set `D(Q)`, so it is a set of units rather than the full value set;
the latter always contains zero by `represents_zero`. -/
def unitValueSet (Q : QuadraticForm K V) : Set Kˣ :=
  {a | Represents Q (a : K)}

/-- Membership in `unitValueSet` is representation of the underlying field element. -/
@[simp]
theorem mem_unitValueSet {Q : QuadraticForm K V} {a : Kˣ} :
    a ∈ unitValueSet Q ↔ Represents Q (a : K) :=
  Iff.rfl

/-- A regular isotropic quadratic form represents every scalar.

The proof chooses a vector not orthogonal to a nonzero isotropic vector and varies the latter
along it. This is the elementary hyperbolic-plane argument in a form useful to the representation
criterion below. -/
theorem represents_of_isotropic_of_nondegenerate (Q : QuadraticForm K V)
    [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) (a : K) :
    Represents Q a := by
  obtain ⟨v, hv, hvQ⟩ := (not_anisotropic_iff_exists Q).mp hiso
  have hB : Q.polarBilin.Nondegenerate :=
    (nondegenerate_polar_iff (Q := Q)).mpr hQ
  obtain ⟨w, hw⟩ : ∃ w, Q.polarBilin v w ≠ 0 := by
    by_contra h
    apply hv
    apply hB.1 v
    intro w
    by_contra hw
    exact h ⟨w, hw⟩
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

/-- Multiplying a represented unit by a square preserves representation, in both directions. -/
theorem mem_unitValueSet_mul_square_iff (Q : QuadraticForm K V) (a b : Kˣ) :
    a * b ^ 2 ∈ unitValueSet Q ↔ a ∈ unitValueSet Q := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(b : K)⁻¹ • v, ?_⟩
    rw [Q.map_smul, smul_eq_mul, hv]
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp
  · rintro ⟨v, hv⟩
    refine ⟨(b : K) • v, ?_⟩
    rw [Q.map_smul, smul_eq_mul, hv]
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

/-- A unit is represented exactly when adjoining its negative line makes the form isotropic.

The added line is the one-dimensional form `x ↦ -a * x²`, written as a scalar multiple of
`QuadraticMap.sq`. -/
theorem mem_unitValueSet_iff_isotropic_prod [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a : Kˣ) :
    a ∈ unitValueSet Q ↔
      ¬(Q.prod ((-(a : K)) • (QuadraticMap.sq : QuadraticForm K K))).Anisotropic := by
  constructor
  · rintro ⟨v, hv⟩
    rw [not_anisotropic_iff_exists]
    refine ⟨(v, 1), ?_, ?_⟩
    · simp
    · simp [QuadraticMap.prod_apply, hv]
  · intro h
    obtain ⟨⟨v, t⟩, hvt, hzero⟩ := (not_anisotropic_iff_exists _).mp h
    simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.sq_apply] at hzero
    by_cases ht : t = 0
    · have hv : v ≠ 0 := by
        intro hv
        apply hvt
        simp [hv, ht]
      have hvQ : Q v = 0 := by simpa [ht] using hzero
      exact represents_of_isotropic_of_nondegenerate Q hQ
        ((not_anisotropic_iff_exists Q).mpr ⟨v, hv, hvQ⟩) (a : K)
    · have hvQ : Q v = (a : K) * (t * t) := by
        linear_combination hzero
      refine ⟨t⁻¹ • v, ?_⟩
      rw [Q.map_smul, smul_eq_mul, hvQ]
      field_simp

end QuadraticMap

end TauCeti
