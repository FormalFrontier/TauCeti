/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Definiteness and the signature of a quadratic form

This file characterizes positive and negative semidefiniteness by the vanishing of the
opposite index of inertia. It also characterizes positive-definiteness by the negative
index and the radical. These are convenient consequences of Sylvester's law of inertia which
complement Mathlib's definitions of `QuadraticMap.PosDef`, `sigPos`, and `sigNeg`.

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
  constructor
  · intro hQ
    have h := sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := ⊤) (fun x _ ↦ by
      simp only [neg_apply]
      exact neg_nonpos.mpr (hQ x))
    rw [sigPos_neg, finrank_top] at h
    omega
  · intro hsig x
    by_contra hlt
    have hQx : 0 < -Q x := neg_pos.mpr (not_le.mp hlt)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, neg_zero] at hQx
      exact lt_irrefl 0 hQx
    have hpos : ((-Q).restrict (Submodule.span K {x})).PosDef := by
      rintro ⟨v, hv⟩ hv0
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hv0 (by simp)
      rw [restrict_apply, neg_apply, Q.map_smul, smul_eq_mul]
      have : -(c * c * Q x) = (c * c) * -Q x := by ring
      rw [this]
      exact mul_pos (mul_self_pos.mpr hc0) hQx
    have hrank : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx0
    have hle := le_sigNeg_of_negDef (Q := Q) hpos
    rw [hrank, hsig] at hle
    omega

/-- A quadratic form is nonpositive exactly when its positive index of inertia vanishes. -/
theorem forall_nonpos_iff_sigPos_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, Q x ≤ 0) ↔ sigPos Q = 0 := by
  simpa only [neg_apply, neg_nonneg, sigNeg_neg] using forall_nonneg_iff_sigNeg_eq_zero (-Q)

omit [IsStrictOrderedRing K] in
/-- Restricting a quadratic form to a subspace cannot increase its positive index. -/
theorem sigPos_restrict_le (Q : _root_.QuadraticForm K M) (W : Subspace K M) :
    sigPos (Q.restrict W) ≤ sigPos Q := by
  obtain ⟨U, hUrank, hUpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q.restrict W)
  rw [← hUrank, ← Submodule.finrank_map_subtype_eq W U]
  apply le_sigPos_of_posDef (V := U.map W.subtype)
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ hx0
  rw [restrict_apply]
  exact hUpos ⟨x, hx⟩ (by simpa using hx0)

omit [IsStrictOrderedRing K] in
/-- Restricting a quadratic form to a subspace cannot increase its negative index. -/
theorem sigNeg_restrict_le (Q : _root_.QuadraticForm K M) (W : Subspace K M) :
    sigNeg (Q.restrict W) ≤ sigNeg Q := by
  obtain ⟨U, hUrank, hUneg⟩ := exists_finrank_eq_sigNeg_and_negDef (Q.restrict W)
  rw [← hUrank, ← Submodule.finrank_map_subtype_eq W U]
  apply le_sigNeg_of_negDef (V := U.map W.subtype)
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ hx0
  rw [QuadraticMap.restrict_apply, neg_apply]
  exact hUneg ⟨x, hx⟩ (by simpa using hx0)

/-- A quadratic form is positive-definite exactly when its negative index vanishes and its
radical is trivial. -/
@[grind =]
theorem posDef_iff_sigNeg_eq_zero_and_radical_eq_bot (Q : _root_.QuadraticForm K M) :
    Q.PosDef ↔ sigNeg Q = 0 ∧ Q.radical = ⊥ := by
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

namespace LinearMap.BilinForm

open _root_.QuadraticForm

section Semiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [LE R]

/-- A symmetric bilinear form is positive-semidefinite if and only if its values on all vectors
are nonnegative. -/
@[grind =]
theorem isPosSemidef_iff_forall_nonneg (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ ∀ x, 0 ≤ B x x := by
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [hB, true_and]

end Semiring

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A symmetric bilinear form is positive-semidefinite if and only if the negative index of its
associated quadratic form vanishes. -/
@[grind =]
theorem isPosSemidef_iff_sigNeg_eq_zero (B : LinearMap.BilinForm K M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ _root_.sigNeg B.toQuadraticMap = 0 := by
  rw [isPosSemidef_iff_forall_nonneg B hB]
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using
    QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero B.toQuadraticMap

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
bilinear form is positive-semidefinite and nondegenerate. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate (B : LinearMap.BilinForm K M)
    (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ B.IsPosSemidef ∧ B.Nondegenerate := by
  have _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  rw [isPosSemidef_iff_sigNeg_eq_zero B hB,
    QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    _root_.LinearMap.BilinForm.radical_toQuadraticMap B hB]

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
kernel of the bilinear form and the negative index of the quadratic form both vanish. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    (B : LinearMap.BilinForm K M) (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ Module.finrank K B.ker = 0 ∧ _root_.sigNeg B.toQuadraticMap = 0 := by
  rw [posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate B hB,
    isPosSemidef_iff_sigNeg_eq_zero B hB,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    Submodule.finrank_eq_zero, and_comm]

end LinearMap.BilinForm

end TauCeti
