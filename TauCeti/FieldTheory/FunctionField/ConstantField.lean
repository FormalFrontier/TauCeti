/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# The constant field of an algebraic function field

The *field of constants* of an algebraic function field `F / k` is the relative algebraic closure
`algebraicClosure k F` of `k` in `F`: the elements of `F` that are algebraic over `k`. This file
proves that it is a finite extension of `k`, records the dictionary for the hypothesis that it is
no larger than `k` (the literature's "`k` is the full field of constants"), and shows that
replacing `k` by the field of constants normalizes any function field to one whose field of
constants is exact.

## Main results

* `TauCeti.IsFunctionField.finiteDimensional_of_isAlgebraic`: an intermediate extension of a
  function field `F / k` which is algebraic over `k` is finite over `k`.
* `TauCeti.IsFunctionField.finiteDimensional_algebraicClosure`: the field of constants of a
  function field is finite over the base field.
* `TauCeti.algebraicClosure_eq_bot_iff_isIntegrallyClosedIn`,
  `TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic`,
  `TauCeti.isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one`: the three faces of the
  exactness hypothesis on the field of constants.
* `TauCeti.IsFunctionField.algebraicClosure` and
  `TauCeti.isIntegrallyClosedIn_algebraicClosure`: `F` is a function field over its field of
  constants, and there the field of constants is exact; the two are packaged as
  `TauCeti.IsFunctionField.exists_intermediateField_isIntegrallyClosedIn`.
* `TauCeti.algebraicClosure_ratFunc`: `k` is the field of constants of `k(x)`.

## References

The statements follow Stichtenoth, *Algebraic Function Fields and Codes*, second edition:
Corollary 1.1.16 for the finiteness of the field of constants, the standing hypothesis of
Section 1.4 for its exactness, and Proposition 1.2.1(d) for the rational function field.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField Polynomial

open scoped RatFunc

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### Finiteness of the field of constants -/

namespace IsFunctionField

/-- An intermediate extension of an algebraic function field `F / k` which is algebraic over `k`
is a finite extension of `k`.

This is Stichtenoth, Corollary 1.1.16; the proof transports the hypothesis to Mathlib's
chosen-parameter formulation and reads off `FunctionField.finiteDimensional_of_constantExtension`,
which compares `k(x)` with `E(x)`. -/
theorem finiteDimensional_of_isAlgebraic (hF : IsFunctionField k F) (E : Type*) [Field E]
    [Algebra k E] [Algebra E F] [IsScalarTower k E F] [Algebra.IsAlgebraic k E] :
    FiniteDimensional k E := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  let : Algebra k[X] F := (Polynomial.aeval x).toRingHom.toAlgebra
  have : IsScalarTower k k[X] F := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have : FaithfulSMul k[X] F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (transcendental_iff_injective.1 hx)
  let : Algebra E[X] F := (Polynomial.aeval x (R := E)).toRingHom.toAlgebra
  have : FaithfulSMul E[X] F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (transcendental_iff_injective.1 (hx.extendScalars (S := E)))
  let : Algebra k[X] E[X] := Polynomial.algebra k E
  have : IsScalarTower k[X] E[X] F := .of_algebraMap_eq fun p ↦
    (Polynomial.aeval_map_algebraMap E x p).symm
  have : FunctionField k F := isFunctionField_iff_functionField.1 hF
  exact FunctionField.finiteDimensional_of_constantExtension F

/-- The field of constants of an algebraic function field is a finite extension of the base
field (Stichtenoth, Corollary 1.1.16). -/
theorem finiteDimensional_algebraicClosure (hF : IsFunctionField k F) :
    FiniteDimensional k (_root_.algebraicClosure k F) :=
  hF.finiteDimensional_of_isAlgebraic _

end IsFunctionField

/-! ### Exactness of the field of constants -/

/-- `k` is integrally closed in `F` exactly when no element of `F` outside `k` is algebraic over
`k`, that is, when the field of constants of `F / k` is `k` itself. -/
theorem algebraicClosure_eq_bot_iff_isIntegrallyClosedIn :
    algebraicClosure k F = ⊥ ↔ IsIntegrallyClosedIn k F := by
  rw [← IsIntegrallyClosedIn.integralClosure_eq_bot_iff F (algebraMap k F).injective,
    ← algebraicClosure_toSubalgebra, ← IntermediateField.bot_toSubalgebra,
    IntermediateField.toSubalgebra_inj]

/-- The elementwise form of the exactness hypothesis on the field of constants: every element of
`F` algebraic over `k` is already a constant. This is the field-extension reading of Mathlib's
`isIntegrallyClosedIn_iff`, whose injectivity clause is automatic here. -/
theorem isIntegrallyClosedIn_iff_forall_isAlgebraic :
    IsIntegrallyClosedIn k F ↔ ∀ x : F, IsAlgebraic k x → ∃ c : k, algebraMap k F c = x := by
  rw [← algebraicClosure_eq_bot_iff_isIntegrallyClosedIn, eq_bot_iff, SetLike.le_def]
  simp [mem_algebraicClosure_iff, IntermediateField.mem_bot]

/-- The exactness hypothesis on the field of constants, read off its degree. -/
theorem isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one :
    IsIntegrallyClosedIn k F ↔ Module.finrank k (algebraicClosure k F) = 1 := by
  rw [IntermediateField.finrank_eq_one_iff, algebraicClosure_eq_bot_iff_isIntegrallyClosedIn]

/-- The field of constants is exact in itself: nothing in `F` outside `algebraicClosure k F` is
algebraic over `algebraicClosure k F`. -/
instance isIntegrallyClosedIn_algebraicClosure :
    IsIntegrallyClosedIn (algebraicClosure k F) F :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.1 (algebraicClosure.algebraicClosure_eq_bot k F)

/-! ### The normalization device -/

/-- An algebraic function field is a function field over its own field of constants, and by
`TauCeti.isIntegrallyClosedIn_algebraicClosure` the field of constants is exact there.

This is the device that lets a statement needing an exact field of constants be applied to an
arbitrary function field. -/
theorem IsFunctionField.algebraicClosure (hF : IsFunctionField k F) :
    IsFunctionField (_root_.algebraicClosure k F) F := by
  have : Algebra.EssFiniteType k F := hF.essFiniteType
  have : Algebra.EssFiniteType (_root_.algebraicClosure k F) F :=
    Algebra.EssFiniteType.of_comp k (_root_.algebraicClosure k F) F
  rw [isFunctionField_iff_trdeg_eq_one]
  have h := lift_trdeg_add_eq k (_root_.algebraicClosure k F) F
  rw [trdeg_eq_zero_iff.2 inferInstance, hF.trdeg_eq_one] at h
  simpa using h

/-- The normalization device: every algebraic function field is, over a finite extension of its
base field, an algebraic function field with an exact field of constants. Later layers, whose
statements are stated under the exactness hypothesis, are applied to a general function field
through this. -/
theorem IsFunctionField.exists_intermediateField_isIntegrallyClosedIn (hF : IsFunctionField k F) :
    ∃ k' : IntermediateField k F,
      FiniteDimensional k k' ∧ IsFunctionField k' F ∧ IsIntegrallyClosedIn k' F :=
  ⟨_root_.algebraicClosure k F, hF.finiteDimensional_algebraicClosure, hF.algebraicClosure,
    inferInstance⟩

/-! ### The rational function field -/

/-- The field of constants of the rational function field `k(x)` is `k`
(Stichtenoth, Proposition 1.2.1(d)). -/
theorem algebraicClosure_ratFunc (K : Type*) [Field K] :
    algebraicClosure K (RatFunc K) = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  obtain ⟨c, rfl⟩ := not_not.1 fun h ↦
    RatFunc.transcendental_of_ne_C f h (mem_algebraicClosure_iff.1 hf)
  rw [← RatFunc.algebraMap_eq_C]
  exact IntermediateField.algebraMap_mem _ _

/-- `k` is integrally closed in the rational function field `k(x)`. -/
instance isIntegrallyClosedIn_ratFunc : IsIntegrallyClosedIn k (RatFunc k) :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.1 (algebraicClosure_ratFunc k)

end TauCeti
