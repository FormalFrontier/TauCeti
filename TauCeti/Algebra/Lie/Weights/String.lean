/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.FormalCharacter

/-!
# The `α`-string of weights above a weight

Let `M` be a finite-dimensional module over a nilpotent Lie algebra `H` -- in practice a Cartan
subalgebra -- and let `μ` and `α` be linear forms on `H`.  The **`α`-string above `μ`** is the set
of `j` for which `μ + j • α` is a weight of `M`.  Because `M` has only finitely many weights and,
for `α ≠ 0`, the forms `μ + j • α` are pairwise distinct, the string is **finite**: this is the
statement that makes the inner sum of Freudenthal's multiplicity recursion a sum over a `Finset`.

This file proves that finiteness, packages the string as `TauCeti.weightString`, records the
resulting uniform bound (`μ + j • α` is not a weight once `j` is large), and computes the string in
the degenerate direction `α = 0`, where it is all of `ℕ` as soon as `μ` is a weight.

## Main definitions

* `TauCeti.weightString M hα μ`: the `α`-string above `μ`, as a `Finset ℕ`.

## Main results

* `TauCeti.finite_setOf_genWeightSpace_add_nsmul_ne_bot`: for `α ≠ 0` the `α`-string above `μ` is
  finite.  This is the finiteness the Freudenthal recursion's inner sum rests on.
* `TauCeti.exists_genWeightSpace_add_nsmul_eq_bot_of_le`: the string terminates -- past some `N`,
  no `μ + j • α` is a weight.
* `TauCeti.sum_finrank_genWeightSpace_weightString_le`: the multiplicities along the string add
  up to at most `Module.finrank K M`, because distinct members of the string are distinct weights
  and the weight spaces of `M` are independent.
* `TauCeti.weightString_congr`: the string is an isomorphism invariant of the Lie module.
* `TauCeti.sum_weightString_eq_sum_of_subset`: a sum over the string may be replaced by a sum over
  any finite superset of it, the form in which a Freudenthal-style double sum is manipulated.

## Implementation notes

The string is indexed by `j : ℕ` and the displacement is the `ℕ`-scalar multiple `j • α` in
`Module.Dual K H`; `Nat.cast_smul_eq_nsmul` converts to the `(j : K) • α` spelling where a
computation in the base field is wanted.

The index `j = 0` is **included**: `0 ∈ weightString M hα μ` exactly when `μ` itself is a weight, so
`weightString` is the whole `α`-string above `μ` and `mem_weightString_iff` characterises membership
with no side condition on `j`.  Freudenthal's inner sum runs over `j ≥ 1` instead, i.e. over
`(weightString M hα μ).erase 0`; being a subset of the string, that index set is finite for the same
reason, which is the finiteness this file supplies.  Restricting the definition itself to `j ≥ 1`
would lose the `j = 0` term, which is the multiplicity `mult_μ` standing on the *left* of the
recursion, and would make every statement below carry a `0 < j` hypothesis.

`TauCeti.weightString` carries the hypothesis `α ≠ 0` as an explicit argument rather than
choosing a junk value, because the `α = 0` case is genuinely infinite (whenever `μ` is a weight)
rather than merely uninteresting;
`TauCeti.infinite_setOf_genWeightSpace_add_nsmul_zero_ne_bot` records that degenerate case
separately.

## References

* H. Freudenthal, *Zur Berechnung der Charaktere der halbeinfachen Lieschen Gruppen I*,
  Indag. Math. **16** (1954), 369--376.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.3, where
  the finiteness of the string is what makes the multiplicity recursion effective.
* [Highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 7, whose `freudenthalRHS` is pinned with the note that "the inner sum over `j ≥ 1` is
  finite because `μ + j • α` leaves the (finite) weight set for large `j`, so it ranges over a
  finite `Finset`".  That finiteness is what this file supplies.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w w₁

section Distinct

variable {K : Type u} {H : Type v} [Field K] [CharZero K] [AddCommMonoid H] [Module K H]

/-- Translating `μ` by the multiples of a nonzero `α` gives pairwise distinct linear forms.  Only
the `K`-module structure of `H` is involved, so no Lie bracket is assumed here. -/
theorem injective_add_nsmul {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) :
    Function.Injective fun j : ℕ ↦ ((mu + j • alpha : Dual K H) : H → K) := by
  intro a b hab
  have h : (mu + a • alpha : Dual K H) = mu + b • alpha := DFunLike.coe_injective hab
  have h' : (a : K) • alpha = (b : K) • alpha := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact add_left_cancel h
  have h'' : ((a : K) - (b : K)) • alpha = 0 := by
    rw [sub_smul (a : K) (b : K) alpha, h', sub_self]
  rcases smul_eq_zero.mp h'' with h₀ | h₀
  · exact Nat.cast_injective (sub_eq_zero.mp h₀)
  · exact absurd h₀ halpha

end Distinct

section WeightString

variable {K : Type u} {H : Type v} {M : Type w} [Field K] [CharZero K] [LieRing H]
  [LieAlgebra K H] [LieRing.IsNilpotent H] [AddCommGroup M] [Module K M] [LieRingModule H M]
  [LieModule K H M] [FiniteDimensional K M]

variable (M)

/-- **The `α`-string above `μ` is finite** for `α ≠ 0`: the forms `μ + j • α` are pairwise
distinct, and a finite-dimensional module has only finitely many weights. -/
theorem finite_setOf_genWeightSpace_add_nsmul_ne_bot {alpha : Dual K H} (halpha : alpha ≠ 0)
    (mu : Dual K H) :
    {j : ℕ | genWeightSpace M ((mu + j • alpha : Dual K H) : H → K) ≠ ⊥}.Finite :=
  Set.Finite.preimage ((injective_add_nsmul halpha mu).injOn)
    (LieModule.finite_genWeightSpace_ne_bot K H M)

/-- **The `α`-string above `μ`**: the `j : ℕ` for which `μ + j • α` is a weight of `M`.  The
hypothesis `α ≠ 0` is what makes the string finite.  The index `j = 0` is included, so this is the
full string; the `j ≥ 1` index set of Freudenthal's inner sum is the subset
`(weightString M halpha mu).erase 0`. -/
noncomputable def weightString {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) :
    Finset ℕ :=
  (finite_setOf_genWeightSpace_add_nsmul_ne_bot M halpha mu).toFinset

variable {M}

@[simp]
theorem mem_weightString_iff {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) {j : ℕ} :
    j ∈ weightString M halpha mu ↔ genWeightSpace M ((mu + j • alpha : Dual K H) : H → K) ≠ ⊥ :=
  Set.Finite.mem_toFinset _

/-- Membership in the string, read off the formal character. -/
theorem mem_weightString_iff_formalCharacter_coeff_ne_zero [LinearWeights K H M]
    {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) {j : ℕ} :
    j ∈ weightString M halpha mu ↔ (formalCharacter K H M).coeff (mu + j • alpha) ≠ 0 := by
  rw [mem_weightString_iff, Ne, Ne, not_iff_not, formalCharacter_coeff_eq_zero_iff]

/-- **The string is an isomorphism invariant**: an equivalence of Lie modules carries the
`χ`-weight space of one onto the `χ`-weight space of the other, so the two modules have the same
`α`-string above any `μ`. -/
theorem weightString_congr {N : Type w₁} [AddCommGroup N] [Module K N]
    [LieRingModule H N] [LieModule K H N] [FiniteDimensional K N]
    (e : M ≃ₗ⁅K,H⁆ N) {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) :
    weightString M halpha mu = weightString N halpha mu := by
  have hker : (e : M →ₗ⁅K,H⁆ N).ker = ⊥ := (LieModuleHom.ker_eq_bot _).mpr e.injective
  ext j
  rw [mem_weightString_iff, mem_weightString_iff, ← map_genWeightSpace_eq e, Ne, Ne,
    ← LieModuleHom.le_ker_iff_map, hker, le_bot_iff]

/-- **The string terminates**: past some `N`, no `μ + j • α` is a weight.  This is the bound that
turns the Freudenthal inner sum into a finite one. -/
theorem exists_genWeightSpace_add_nsmul_eq_bot_of_le {alpha : Dual K H} (halpha : alpha ≠ 0)
    (mu : Dual K H) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → genWeightSpace M ((mu + j • alpha : Dual K H) : H → K) = ⊥ := by
  classical
  refine ⟨(weightString M halpha mu).sup id + 1, fun j hj ↦ ?_⟩
  by_contra h
  have hmem : j ∈ weightString M halpha mu := (mem_weightString_iff halpha mu).mpr h
  have hle := Finset.le_sup (f := id) hmem
  simp only [id_eq] at hle
  omega

/-- The string is contained in an initial segment of `ℕ`. -/
theorem weightString_subset_range {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) :
    weightString M halpha mu ⊆ Finset.range ((weightString M halpha mu).sup id + 1) := by
  intro j hj
  have hle := Finset.le_sup (f := id) hj
  simp only [id_eq] at hle
  simp only [Finset.mem_range]
  omega

/-- The string is empty exactly when no translate of `μ` by a multiple of `α` is a weight. -/
theorem weightString_eq_empty_iff {alpha : Dual K H} (halpha : alpha ≠ 0) (mu : Dual K H) :
    weightString M halpha mu = ∅ ↔
      ∀ j : ℕ, genWeightSpace M ((mu + j • alpha : Dual K H) : H → K) = ⊥ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  refine forall_congr' fun j ↦ ?_
  rw [mem_weightString_iff, not_ne_iff]

/-- **The multiplicities along the string add up to at most the dimension of `M`.** The forms
`μ + j • α` for `j` in the string are pairwise distinct, so the corresponding weight spaces are an
independent family of subspaces of `M`; their span therefore has the sum of their dimensions, and
that span sits inside `M`. -/
theorem sum_finrank_genWeightSpace_weightString_le {alpha : Dual K H} (halpha : alpha ≠ 0)
    (mu : Dual K H) :
    ∑ j ∈ weightString M halpha mu,
        (finrank K (genWeightSpace M ((mu + j • alpha : Dual K H) : H → K)) : ℤ)
      ≤ (finrank K M : ℤ) := by
  classical
  have hindep : iSupIndep fun j : {j // j ∈ weightString M halpha mu} ↦
      (genWeightSpace M ((mu + (j : ℕ) • alpha : Dual K H) : H → K) : Submodule K M) :=
    (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H M)).comp
      fun a b hab ↦ Subtype.ext (injective_add_nsmul halpha mu hab)
  have hle : ∑ j : {j // j ∈ weightString M halpha mu},
      finrank K ((genWeightSpace M ((mu + (j : ℕ) • alpha : Dual K H) : H → K) : Submodule K M))
        ≤ finrank K M := by
    rw [← finrank_iSup_eq_sum_finrank_of_iSupIndep hindep]
    exact Submodule.finrank_le _
  simp only [finrank_toSubmodule] at hle
  rw [← Finset.sum_coe_sort (weightString M halpha mu)]
  exact_mod_cast hle

/-- A sum over the string is a sum over any finite superset of it, the terms off the string
vanishing.  This is how a Freudenthal-style double sum is compared with a sum over a common
index set. -/
theorem sum_weightString_eq_sum_of_subset {A : Type*} [AddCommMonoid A] {alpha : Dual K H}
    (halpha : alpha ≠ 0) (mu : Dual K H) (f : ℕ → A) {s : Finset ℕ}
    (hs : weightString M halpha mu ⊆ s)
    (hf : ∀ j ∈ s, genWeightSpace M ((mu + j • alpha : Dual K H) : H → K) = ⊥ → f j = 0) :
    ∑ j ∈ weightString M halpha mu, f j = ∑ j ∈ s, f j := by
  refine Finset.sum_subset hs fun j hjs hj ↦ hf j hjs ?_
  by_contra h
  exact hj ((mem_weightString_iff halpha mu).mpr h)

omit [CharZero K] [FiniteDimensional K M] in
/-- **The hypothesis `α ≠ 0` cannot be dropped**: in the degenerate direction `α = 0` every `j`
translates `μ` to itself, so the string above a weight is all of `ℕ`. -/
theorem infinite_setOf_genWeightSpace_add_nsmul_zero_ne_bot (mu : Dual K H)
    (h : genWeightSpace M (mu : H → K) ≠ ⊥) :
    {j : ℕ | genWeightSpace M ((mu + j • (0 : Dual K H) : Dual K H) : H → K) ≠ ⊥}.Infinite := by
  have huniv : {j : ℕ | genWeightSpace M ((mu + j • (0 : Dual K H) : Dual K H) : H → K) ≠ ⊥}
      = Set.univ := by
    ext j
    simp [h]
  rw [huniv]
  exact Set.infinite_univ

end WeightString

end TauCeti
