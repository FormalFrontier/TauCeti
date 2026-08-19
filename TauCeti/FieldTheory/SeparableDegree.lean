/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Separable and inseparable degrees under a surjective base change

In a tower `K → E → L` of fields whose lower map `algebraMap K E` is onto, `E` carries no more
information over `K` than `K` itself does, so the degree of `L` is the same whichever of the two
it is measured over. This file records that for the separable and inseparable degrees, alongside
`Module.finrank`, for which Mathlib already has the statement.

The hypothesis is surjectivity rather than bijectivity because a map of fields is automatically
injective; and it is stated for an arbitrary tower rather than for a specific construction, so
that a caller with any surjectively-presented intermediate field can use it.

## Main results

* `Field.finSepDegree_eq_of_surjective`: `[L : E]_s = [L : K]_s`.
* `Field.finInsepDegree_eq_of_surjective`: `[L : E]_i = [L : K]_i`.
-/

public section

variable {K L : Type*} [Field K] [Field L]

/-- **The separable degree is unchanged by a surjective base change.** Use this to move a
separable degree between an intermediate field and a field presented as mapping onto it. -/
theorem Field.finSepDegree_eq_of_surjective {E : Type*} [Field E] [Algebra K L] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] (hsurj : Function.Surjective (algebraMap K E)) :
    Field.finSepDegree E L = Field.finSepDegree K L := by
  -- an `L`-embedding is `E`-linear exactly when it is `K`-linear, so the embedding sets agree
  unfold Field.finSepDegree
  exact Nat.card_congr (AlgHom.extendScalarsOfSurjective hsurj).symm

/-- **The inseparable degree is unchanged by a surjective base change.** The inseparable
counterpart of `Field.finSepDegree_eq_of_surjective`, for the same tower. -/
theorem Field.finInsepDegree_eq_of_surjective {E : Type*} [Field E] [Algebra K L] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] (hsurj : Function.Surjective (algebraMap K E)) :
    Field.finInsepDegree E L = Field.finInsepDegree K L := by
  -- the lower step is bijective, hence of degree one, so the tower law leaves the upper step alone
  have : FiniteDimensional K E := Module.Finite.of_surjective (Algebra.linearMap K E) hsurj
  have hrank : Module.finrank K E = 1 :=
    Module.finrank_of_bijective_algebraMap ⟨FaithfulSMul.algebraMap_injective _ _, hsurj⟩
  have h1 : Field.finInsepDegree K E = 1 := by
    have hmul := Field.finSepDegree_mul_finInsepDegree K E
    rw [hrank] at hmul
    exact Nat.eq_one_of_mul_eq_one_left hmul
  have hmul := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K E L
  rw [h1, one_mul] at hmul
  exact hmul
