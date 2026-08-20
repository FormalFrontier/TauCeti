/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Cartan
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form

/-!
# The Kostant form attached to a Lie algebra basis

A `LieAlgebra.Basis` supplies raising, lowering, and Cartan generators. This file combines the
raising and lowering generators into one family and attaches the corresponding simple-generator
Kostant form. The basis axiom `span_ef` immediately implies that this form spans the rational
universal enveloping algebra.

The resulting subring is defined using only the simple raising and lowering generators. Its
identification with the classical all-root Kostant form requires a separate comparison theorem.

## Main definitions and results

* `TauCeti.LieBasis.rootGenerator`: the combined raising and lowering generators.
* `TauCeti.LieBasis.kostantForm`: the associated simple-generator Kostant form.
* `TauCeti.LieBasis.kostantForm_le_iff`: its universal property.
* `TauCeti.LieBasis.span_kostantForm_eq_top`: the form spans the enveloping algebra.
-/

public section

namespace TauCeti.LieBasis

open Set

noncomputable section

variable {ι L : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L]
  {H : _root_.LieSubalgebra ℚ L} (b : _root_.LieAlgebra.Basis ι H)

attribute [local instance] TauCeti.moduleNNRat

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

/-- The raising and lowering generators of a Lie algebra basis, combined into one family. -/
def rootGenerator : ι ⊕ ι → L :=
  Sum.elim b.e b.f

/-- The combined root-generator family evaluates to the raising generator on the left summand. -/
@[simp]
theorem rootGenerator_inl (i : ι) : rootGenerator b (.inl i) = b.e i := (rfl)

/-- The combined root-generator family evaluates to the lowering generator on the right summand. -/
@[simp]
theorem rootGenerator_inr (i : ι) : rootGenerator b (.inr i) = b.f i := (rfl)

/-- The combined root generators have the union of the raising and lowering ranges. -/
theorem range_rootGenerator : range (rootGenerator b) = range b.e ∪ range b.f :=
  Sum.elim_range _ _

/-- The root and Cartan generators of a Lie algebra basis generate the Lie algebra. -/
theorem lieSpan_range_rootGenerator_union_range_h_eq_top :
    _root_.LieSubalgebra.lieSpan ℚ L (range (rootGenerator b) ∪ range b.h) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← b.span_ef]
  refine _root_.LieSubalgebra.lieSpan_mono ?_
  rw [range_rootGenerator b]
  exact subset_union_left

/-- The simple-generator Kostant form attached to a Lie algebra basis. -/
def kostantForm : Subring U :=
  UniversalEnvelopingAlgebra.kostantForm (rootGenerator b) b.h

/-- The basis Kostant form is the generic form for the combined root generators and Cartan
generators. -/
theorem kostantForm_def :
    kostantForm b = UniversalEnvelopingAlgebra.kostantForm (rootGenerator b) b.h := (rfl)

/-- Every divided power of a raising or lowering generator lies in the basis Kostant form. -/
theorem dividedPower_mem_kostantForm (i : ι ⊕ ι) (n : ℕ) :
    Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator b i)) ∈
      kostantForm b := by
  rw [kostantForm_def b]
  exact UniversalEnvelopingAlgebra.dividedPower_mem_kostantForm _ _ i n

/-- Every binomial coefficient of a Cartan generator lies in the basis Kostant form. -/
theorem ringChoose_mem_kostantForm (i : ι) (n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (b.h i)) n ∈ kostantForm b := by
  rw [kostantForm_def b]
  exact UniversalEnvelopingAlgebra.ringChoose_mem_kostantForm _ _ i n

/-- The universal property of the basis Kostant form, split into its root and Cartan families. -/
@[simp]
theorem kostantForm_le_iff (T : Subring U) :
    kostantForm b ≤ T ↔
      (∀ i n, Associative.dividedPower n
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator b i)) ∈ T) ∧
      ∀ i n, Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (b.h i)) n ∈ T := by
  rw [kostantForm_def b, UniversalEnvelopingAlgebra.kostantForm_le_iff]

/-- The basis Kostant form spans the rational universal enveloping algebra. -/
theorem span_kostantForm_eq_top :
    Submodule.span ℚ (kostantForm b : Set U) = ⊤ := by
  rw [kostantForm_def b]
  exact UniversalEnvelopingAlgebra.span_kostantForm_eq_top _ _
    (lieSpan_range_rootGenerator_union_range_h_eq_top b)

end

end TauCeti.LieBasis
