/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Definiteness and the signature of a quadratic form

This file characterizes positive and negative semidefiniteness by the vanishing of the
corresponding index of inertia.  It also characterizes positive-definiteness by the negative
index and the radical.  These are convenient consequences of Sylvester's law of inertia which
complement Mathlib's definitions of `QuadraticMap.PosDef`, `QuadraticForm.sigPos`, and
`QuadraticForm.sigNeg`.

The results are proved by reducing to Mathlib's weighted-sum-of-squares normal form.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Finset QuadraticMap

namespace TauCeti

namespace QuadraticForm

open _root_.QuadraticForm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A quadratic form is nonnegative exactly when its negative index of inertia vanishes. -/
theorem forall_nonneg_iff_sigNeg_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, 0 ≤ Q x) ↔ sigNeg Q = 0 := by
  classical
  let _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  obtain ⟨w, hQw⟩ := Q.equivalent_weightedSumSquares
  rw [hQw.sigNeg_eq, sigNeg_weightedSumSquares, Set.ncard_eq_zero]
  obtain ⟨e⟩ := hQw
  constructor
  · intro hQ
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have hi := hQ (e.symm (Pi.single i 1))
    rw [e.symm.map_app] at hi
    have hsingle : weightedSumSquares K w (Pi.single i 1) = w i := by
      rw [weightedSumSquares_apply, Fintype.sum_eq_single i]
      · rw [Pi.single_eq_same, one_mul, smul_eq_mul, mul_one]
      · intro j hji
        rw [Pi.single_eq_of_ne hji, mul_zero, smul_zero]
    rw [hsingle] at hi
    exact not_lt.mpr hi
  · intro hw x
    rw [← e.map_app, weightedSumSquares_apply]
    exact sum_nonneg fun i _ ↦ mul_nonneg (not_lt.mp (by
      have hi := Set.ext_iff.mp hw i
      simpa only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false] using hi))
        (mul_self_nonneg _)

/-- A quadratic form is nonpositive exactly when its positive index of inertia vanishes. -/
theorem forall_nonpos_iff_sigPos_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, Q x ≤ 0) ↔ sigPos Q = 0 := by
  simpa only [neg_apply, neg_nonneg, sigNeg_neg] using forall_nonneg_iff_sigNeg_eq_zero (-Q)

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K M] in
/-- Negating a quadratic form does not change its radical. -/
@[simp]
theorem radical_neg (Q : _root_.QuadraticForm K M) : (-Q).radical = Q.radical := by
  ext x
  simp only [QuadraticMap.mem_radical_iff', neg_apply, neg_eq_zero, neg_inj]

/-- A quadratic form is positive-definite exactly when its negative index vanishes and its
radical is trivial. -/
theorem posDef_iff_sigNeg_eq_zero_and_radical_eq_bot (Q : _root_.QuadraticForm K M) :
    Q.PosDef ↔ sigNeg Q = 0 ∧ Q.radical = ⊥ := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  constructor
  · intro hQ
    refine ⟨(forall_nonneg_iff_sigNeg_eq_zero Q).mp hQ.nonneg, ?_⟩
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hQ.anisotropic x (QuadraticMap.mem_radical_iff'.mp hx).1
  · rintro ⟨hneg, hrad⟩
    obtain ⟨W, hWrank, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
    have hsig := sigPos_add_sigNeg_add_radical (Q := Q)
    rw [hneg, hrad] at hsig
    have hsig' : sigPos Q = Module.finrank K M := by
      simpa only [add_zero, finrank_bot] using hsig
    have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (hWrank.trans hsig')
    intro x hx
    have hxW : x ∈ W := hWtop.symm ▸ Submodule.mem_top
    exact hWpos ⟨x, hxW⟩ (by simpa only [ne_eq, Submodule.mk_eq_zero])

end QuadraticForm

end TauCeti
