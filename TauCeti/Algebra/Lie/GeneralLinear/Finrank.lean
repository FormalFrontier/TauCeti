/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Basic

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The dimension of the special linear Lie algebra

Over a field, `sl n K` is the kernel of the trace functional on the `n × n` matrices. The trace is
surjective as soon as there is an index at all — the matrix unit `Eᵢᵢ` scaled by `c` has trace `c` —
so rank-nullity makes its kernel a hyperplane:

`finrank K (sl n K) = (card n) ^ 2 - 1`.

The truncated subtraction is not a fudge. For an empty index type the matrix algebra is the zero
ring and both sides are `0`, since `0 - 1 = 0` in `ℕ`. The statement therefore carries no
nonemptiness hypothesis, and `TauCeti.finrank_sl_add_one` records the untruncated form
`finrank K (sl n K) + 1 = (card n) ^ 2` where nonemptiness is available.

A field is genuinely used. The same formula holds over any commutative ring, because `sl n R` is
free on the off-diagonal matrix units together with the differences `Eᵢᵢ - E_{i₀i₀}`, but reading
it off needs that explicit basis; only its rank-two case is on `main`
(`TauCeti.slFinTwoBasis`, with `TauCeti.finrank_sl_fin_two` its dimension count over any ring
satisfying the strong rank condition). Rank-nullity, the argument used here, instead needs the
kernel to be complemented, hence needs the field.

## Main results

* `TauCeti.surjective_traceLinearMap` and `TauCeti.range_traceLinearMap`: the trace of a square
  matrix is surjective onto the scalars.
* `TauCeti.finrank_sl`: `sl n K` has dimension `(card n) ^ 2 - 1`.
* `TauCeti.finrank_slIdeal`: the same for the trace-zero ideal of `gl n K`.
* `TauCeti.finrank_sl_add_one`: the untruncated form, for a nonempty index type.

## Roadmap context

Layer 8 of the
[highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
asks for the dimension check `finrank (𝔰𝔩₉ ⊕ ⋀³(K⁹) ⊕ ⋀³(K⁹)^*) = 248 = 80 + 84 + 84` of the
Vinberg `ℤ/3`-model of split `E₈`. This file supplies the `80`; the check itself is in
`TauCeti/Algebra/Lie/E8/Vinberg.lean`.
-/

public section

namespace TauCeti

open Matrix Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} {n : Type*} [Fintype n]

section Trace

variable (K n) [CommRing K] [Nonempty n]

/-- **The trace is surjective onto the scalars** as soon as there is an index: the matrix unit
`Eᵢᵢ` scaled by `c` has trace `c`. -/
theorem surjective_traceLinearMap :
    Function.Surjective (Matrix.traceLinearMap n K K) := by
  classical
  intro c
  exact ⟨Matrix.single (Classical.arbitrary n) (Classical.arbitrary n) c,
    Matrix.trace_single_eq_same _ _⟩

/-- The trace has full range: the `LinearMap.range` form of
`TauCeti.surjective_traceLinearMap`, which is what rank-nullity consumes. -/
theorem range_traceLinearMap :
    LinearMap.range (Matrix.traceLinearMap n K K) = ⊤ :=
  LinearMap.range_eq_top.2 (surjective_traceLinearMap K n)

end Trace

section Finrank

variable (K n) [Field K] [DecidableEq n]

/-- The special linear Lie algebra is, as a subspace, the kernel of the trace. -/
theorem toSubmodule_sl :
    (SpecialLinear.sl n K : Submodule K (Matrix n n K))
      = LinearMap.ker (Matrix.traceLinearMap n K K) :=
  Submodule.ext fun _ => Iff.rfl

/-- **`sl n K` is a hyperplane in the matrices**: `finrank K (sl n K) = (card n) ^ 2 - 1`.

For an empty index type the matrix algebra is trivial and both sides are `0`, the truncated
subtraction `0 - 1` doing the work. -/
theorem finrank_sl :
    finrank K (SpecialLinear.sl n K) = Fintype.card n ^ 2 - 1 := by
  have hmatrix : finrank K (Matrix n n K) = Fintype.card n ^ 2 := by
    rw [Module.finrank_matrix, finrank_self, mul_one, sq]
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap n K K)
  rw [hmatrix] at hrank
  have hker : finrank K (SpecialLinear.sl n K)
      = finrank K (LinearMap.ker (Matrix.traceLinearMap n K K)) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ (toSubmodule_sl K n))
  rw [hker]
  rcases isEmpty_or_nonempty n with _ | _
  · have hcard : Fintype.card n ^ 2 = 0 := by simp [Fintype.card_eq_zero]
    rw [hcard] at hrank ⊢
    omega
  · rw [range_traceLinearMap K n, finrank_top, finrank_self] at hrank
    omega

/-- The trace-zero ideal of `gl n K` has dimension `(card n) ^ 2 - 1`: the `TauCeti.slIdeal`
spelling of `TauCeti.finrank_sl`. -/
theorem finrank_slIdeal :
    finrank K (slIdeal K n) = Fintype.card n ^ 2 - 1 := by
  rw [← finrank_sl K n]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _
    (congrArg LieSubalgebra.toSubmodule (slIdeal_toLieSubalgebra_eq_sl K n)))

variable [Nonempty n]

/-- The untruncated codimension-one statement: `sl n K` is a hyperplane in the matrices. -/
theorem finrank_sl_add_one :
    finrank K (SpecialLinear.sl n K) + 1 = Fintype.card n ^ 2 := by
  have hpos : 1 ≤ Fintype.card n ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  rw [finrank_sl]
  omega

end Finrank

end TauCeti
