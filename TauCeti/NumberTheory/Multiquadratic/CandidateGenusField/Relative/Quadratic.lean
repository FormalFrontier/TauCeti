/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Degree
public import TauCeti.NumberTheory.NumberField.IntegralSqrt

/-!
# The quadratic base of the candidate genus field, as a quadratic field

For a squarefree integer `d`, `candidateGenusFieldBase hd` is the copy of `ℚ(√d)` cut out inside
`candidateGenusField hd` by the chosen square root `candidateGenusFieldBaseRoot hd` of `d`. The
quadratic-field API of `TauCeti.NumberTheory.NumberField.Quadratic` and of
`Multiquadratic/Quadratic/*` — the ring of integers, the discriminant, the ramified primes, the
conjugation — is phrased for a number field `K` presented by an algebraic integer `θ : 𝓞 K` with

`minpoly ℤ θ = X ^ 2 - d` and `Algebra.adjoin ℚ {(θ : K)} = ⊤`.

This file supplies that presentation for the embedded base, so those results become available for
it. The generator is `candidateGenusFieldBaseGen`, the chosen root packaged as an algebraic
integer; its minimal polynomial is `X ^ 2 - d` as soon as `d` is not a rational square
(`TauCeti.NumberField.minpoly_integralSqrt`), and it generates the base over `ℚ` because the base
is by definition the simple extension it generates.

## Main definitions

* `TauCeti.Multiquadratic.candidateGenusFieldBaseSqrt`: the chosen square root of `d`, viewed as an
  element of the embedded base rather than of the whole candidate genus field.
* `TauCeti.Multiquadratic.candidateGenusFieldBaseGen`: the same element as an algebraic integer.

## Main results

* `TauCeti.Multiquadratic.minpoly_candidateGenusFieldBaseGen`: its minimal polynomial over `ℤ` is
  `X ^ 2 - d`, for `d` not a rational square.
* `TauCeti.Multiquadratic.adjoin_candidateGenusFieldBaseSqrt_eq_top`: the chosen root generates the
  base as an intermediate field.
* `TauCeti.Multiquadratic.adjoin_candidateGenusFieldBaseGen_eq_top`: it generates the base over
  `ℚ`.
-/

public section

open IntermediateField Polynomial

open scoped NumberField

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- The chosen square root of `d`, viewed inside the embedded base `ℚ(√d)` of the candidate genus
field rather than inside the candidate genus field itself. -/
@[expose] noncomputable def candidateGenusFieldBaseSqrt (hd : Squarefree d) :
    candidateGenusFieldBase hd :=
  ⟨candidateGenusFieldBaseRoot hd, candidateGenusFieldBaseRoot_mem hd⟩

@[simp] theorem candidateGenusFieldBaseSqrt_val (hd : Squarefree d) :
    (candidateGenusFieldBaseSqrt hd : candidateGenusField hd) = candidateGenusFieldBaseRoot hd :=
  rfl

@[simp] theorem candidateGenusFieldBaseSqrt_sq (hd : Squarefree d) :
    candidateGenusFieldBaseSqrt hd ^ 2 = algebraMap ℤ (candidateGenusFieldBase hd) d := by
  -- Both sides are compared in `candidateGenusField hd`, where the statement is
  -- `candidateGenusFieldBaseRoot_sq` up to rewriting `algebraMap ℤ _` as an `Int.cast`.
  apply Subtype.ext
  rw [IntermediateField.coe_pow, candidateGenusFieldBaseSqrt_val, candidateGenusFieldBaseRoot_sq]
  simp

/-- The chosen square root of `d`, as an algebraic integer of the embedded base. This is the `θ` of
the quadratic-field presentation `minpoly ℤ θ = X ^ 2 - d`, `Algebra.adjoin ℚ {θ} = ⊤`. -/
noncomputable def candidateGenusFieldBaseGen (hd : Squarefree d) :
    𝓞 (candidateGenusFieldBase hd) :=
  TauCeti.NumberField.integralSqrt (candidateGenusFieldBaseSqrt_sq hd)

@[simp] theorem coe_candidateGenusFieldBaseGen (hd : Squarefree d) :
    ((candidateGenusFieldBaseGen hd : 𝓞 (candidateGenusFieldBase hd)) :
      candidateGenusFieldBase hd) = candidateGenusFieldBaseSqrt hd := by
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
  exact TauCeti.NumberField.algebraMap_integralSqrt _

/-- **The minimal polynomial of the base generator is `X ^ 2 - d`**, for `d` not a rational square.
Together with `adjoin_candidateGenusFieldBaseGen_eq_top` this presents `candidateGenusFieldBase hd`
as the quadratic field `ℚ(√d)` in the form the quadratic-field API expects. -/
theorem minpoly_candidateGenusFieldBaseGen (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    minpoly ℤ (candidateGenusFieldBaseGen hd) = X ^ 2 - C d :=
  TauCeti.NumberField.minpoly_integralSqrt _ hnsq

/-- The chosen square root of `d` generates the embedded base as an intermediate field: the base is
by definition the simple extension it generates, read one level down. -/
theorem adjoin_candidateGenusFieldBaseSqrt_eq_top (hd : Squarefree d) :
    adjoin ℚ {candidateGenusFieldBaseSqrt hd} = ⊤ := by
  -- Compare the two sides through their images in `candidateGenusField hd`.
  have himage : (candidateGenusFieldBase hd).val '' {candidateGenusFieldBaseSqrt hd} =
      {candidateGenusFieldBaseRoot hd} := by simp
  refine IntermediateField.map_injective (candidateGenusFieldBase hd).val ?_
  refine (IntermediateField.adjoin_map ℚ _ _).trans ?_
  refine Eq.trans ?_ (IntermediateField.lift_top (F := ℚ) (candidateGenusFieldBase hd)).symm
  rw [himage, candidateGenusFieldBase_def]

/-- **The base generator generates the base over `ℚ`.** The embedded base is by definition the
simple extension generated by the chosen square root of `d`; being integral, that root generates
the base already as a `ℚ`-algebra. -/
theorem adjoin_candidateGenusFieldBaseGen_eq_top (hd : Squarefree d) :
    Algebra.adjoin ℚ {((candidateGenusFieldBaseGen hd : 𝓞 (candidateGenusFieldBase hd)) :
      candidateGenusFieldBase hd)} = ⊤ := by
  have hint : IsIntegral ℚ (candidateGenusFieldBaseSqrt hd) :=
    IsIntegral.of_pow (n := 2) (by norm_num)
      (by rw [candidateGenusFieldBaseSqrt_sq]; exact isIntegral_algebraMap)
  rw [coe_candidateGenusFieldBaseGen,
    ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    adjoin_candidateGenusFieldBaseSqrt_eq_top hd]
  rfl

end TauCeti.Multiquadratic
