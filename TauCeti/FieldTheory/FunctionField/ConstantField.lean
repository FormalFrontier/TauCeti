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

It then identifies the constant fields along a change of base.  An intermediate field `k'` of
`F / k` is again a legitimate base field exactly when it is algebraic over `k`, and it is then
automatically finite over `k`; if moreover `k'` is its own field of constants, it *is* the field
of constants of `F / k`.  Specialized to the standing tower of an extension `F' / k'` of `F / k`
with `F' / F` finite, this says that the extension of constant fields `k' / k` is finite — a
theorem, not a hypothesis, and the finiteness that makes the factor `[k' : k]` in the conorm
degree identity and in the Hurwitz genus formula meaningful.

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
* `TauCeti.isFunctionField_base_iff_isAlgebraic`, with its two directions
  `TauCeti.IsFunctionField.isAlgebraic_base` and `TauCeti.IsFunctionField.of_isAlgebraic`: an
  intermediate field of `F / k` is a base field for `F` exactly when it is algebraic over `k`;
  `TauCeti.IsFunctionField.of_finiteDimensional` lowers the base field again.
* `TauCeti.IsFunctionField.finiteDimensional_base` and
  `TauCeti.IsFunctionField.algebraicClosure_eq_restrictScalars_bot`: such an intermediate base
  field is finite over `k`, and is the field of constants of `F / k` as soon as it is its own.
* `TauCeti.IsFunctionField.finiteDimensional_constantExtension`: in an extension `F' / k'` of
  `F / k` with `F' / F` finite, `k' / k` is a finite extension (Stichtenoth, Definition 3.1.1);
  `TauCeti.IsFunctionField.isAlgebraic_algebraMap_iff_isAlgebraic` identifies the fields of
  constants
  along `F ⊆ F'`.
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
is a finite extension of `k` (Stichtenoth, Corollary 1.1.16). -/
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

/-! ### Intermediate base fields -/

section IntermediateBase

variable {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' F] [IsScalarTower k k' F]

/-- An intermediate field `k'` between `k` and an algebraic function field `F / k` over which `F`
is again an algebraic function field is algebraic over `k`: transcendence degree one leaves no
room for a transcendental constant. -/
theorem IsFunctionField.isAlgebraic_base (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) : Algebra.IsAlgebraic k k' := by
  rw [← trdeg_eq_zero_iff]
  have h := lift_trdeg_add_eq k k' F
  rw [hF.trdeg_eq_one, hF'.trdeg_eq_one] at h
  simp only [Cardinal.lift_one] at h
  rcases Cardinal.add_eq_right_iff.mp h with h | h
  -- the first alternative would force `ℵ₀ ≤ 1`
  · exact absurd ((le_max_left _ _).trans h) (by simp)
  · simpa using h

/-- Enlarging the base field of an algebraic function field by an algebraic extension inside it
leaves an algebraic function field (Stichtenoth, Corollary 1.1.16 and Definition 3.1.1): the new
base contributes no transcendence. -/
theorem IsFunctionField.of_isAlgebraic (hF : IsFunctionField k F) [Algebra.IsAlgebraic k k'] :
    IsFunctionField k' F := by
  have : Algebra.EssFiniteType k F := hF.essFiniteType
  have : Algebra.EssFiniteType k' F := Algebra.EssFiniteType.of_comp k k' F
  rw [isFunctionField_iff_trdeg_eq_one]
  have h := lift_trdeg_add_eq k k' F
  rw [trdeg_eq_zero_iff.mpr ‹Algebra.IsAlgebraic k k'›, hF.trdeg_eq_one] at h
  simpa using h

/-- Shrinking the base field of an algebraic function field along a finite extension leaves an
algebraic function field: if `F` is a function field over `k'` and `k'` is finite over `k`, then
`F` is a function field over `k`.  This is the converse of
`TauCeti.IsFunctionField.of_isAlgebraic` for the finite extensions that
`TauCeti.IsFunctionField.finiteDimensional_base` produces. -/
theorem IsFunctionField.of_finiteDimensional (hF' : IsFunctionField k' F)
    [FiniteDimensional k k'] : IsFunctionField k F := by
  have : Algebra.EssFiniteType k' F := hF'.essFiniteType
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k k' F
  rw [isFunctionField_iff_trdeg_eq_one]
  have h := lift_trdeg_add_eq k k' F
  rw [trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite k k'), hF'.trdeg_eq_one] at h
  simpa using h.symm

/-- An intermediate field of an algebraic function field `F / k` is a legitimate base field for
`F` exactly when it is algebraic over `k`. -/
theorem isFunctionField_base_iff_isAlgebraic (hF : IsFunctionField k F) :
    IsFunctionField k' F ↔ Algebra.IsAlgebraic k k' :=
  ⟨hF.isAlgebraic_base, fun h ↦ have := h; hF.of_isAlgebraic⟩

/-- An intermediate base field of an algebraic function field is a finite extension of the
original base field (Stichtenoth, Corollary 1.1.16). -/
theorem IsFunctionField.finiteDimensional_base (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) : FiniteDimensional k k' :=
  have := hF.isAlgebraic_base hF'
  hF.finiteDimensional_of_isAlgebraic k'

/-- **The field of constants of `F / k` is the intermediate base field `k'`**, whenever `k'` is
its own field of constants in `F`. -/
theorem IsFunctionField.algebraicClosure_eq_restrictScalars_bot (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) (hex : IsIntegrallyClosedIn k' F) :
    _root_.algebraicClosure k F = (⊥ : IntermediateField k' F).restrictScalars k := by
  have := hF.isAlgebraic_base hF'
  rw [_root_.algebraicClosure.eq_restrictScalars_of_isAlgebraic k k' F,
    algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.2 hex]

/-- The elementwise form of `TauCeti.IsFunctionField.algebraicClosure_eq_restrictScalars_bot`: an
element of `F` is algebraic over `k` exactly when it is one of the constants `k'`. -/
theorem IsFunctionField.isAlgebraic_iff_exists_algebraMap (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) (hex : IsIntegrallyClosedIn k' F) {x : F} :
    IsAlgebraic k x ↔ ∃ c : k', algebraMap k' F c = x := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hmem : x ∈ _root_.algebraicClosure k F := mem_algebraicClosure_iff.2 hx
    rw [hF.algebraicClosure_eq_restrictScalars_bot hF' hex] at hmem
    simpa [IntermediateField.mem_bot] using hmem
  · rintro ⟨c, rfl⟩
    have := hF.isAlgebraic_base hF'
    exact (Algebra.IsAlgebraic.isAlgebraic c).algebraMap

end IntermediateBase

/-! ### Extensions of function fields -/

section Extension

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F']
variable [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

/-- **The constant field of an extension of function fields is algebraic over the constant field
below** (Stichtenoth, Definition 3.1.1 and the remark following it): in the standing tower of an
extension `F' / k'` of `F / k` with `F' / F` finite, `k' / k` is not an assumption but a
theorem. -/
theorem IsFunctionField.isAlgebraic_constantExtension (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') : Algebra.IsAlgebraic k k' :=
  (hF.finite_extension (E := F')).isAlgebraic_base hF'

/-- **The constant field of an extension of function fields is a finite extension of the constant
field below** (Stichtenoth, Corollary 1.1.16 applied in the tower of Definition 3.1.1).  This is
the finiteness that makes the factor `[k' : k]` of the conorm degree identity and of the Hurwitz
genus formula meaningful. -/
theorem IsFunctionField.finiteDimensional_constantExtension (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') : FiniteDimensional k k' :=
  (hF.finite_extension (E := F')).finiteDimensional_base hF'

/-- **A function of `F` is a constant of `F' / k'` exactly when it is a constant of `F / k`**: the
two fields of constants meet in `F` along the field of constants of `F / k`, so the inclusion
`k → k'` of the tower really is an inclusion of constant fields.  No exactness hypothesis is
needed: the statement is about being algebraic, not about lying in the base field. -/
theorem IsFunctionField.isAlgebraic_algebraMap_iff_isAlgebraic (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') {a : F} :
    IsAlgebraic k' (algebraMap F F' a) ↔ IsAlgebraic k a := by
  have := hF.isAlgebraic_constantExtension hF'
  rw [← mem_algebraicClosure_iff, ← IntermediateField.mem_restrictScalars (K := k),
    ← _root_.algebraicClosure.eq_restrictScalars_of_isAlgebraic k k' F',
    mem_algebraicClosure_iff]
  exact isAlgebraic_algebraMap_iff (FaithfulSMul.algebraMap_injective F F')

end Extension

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
