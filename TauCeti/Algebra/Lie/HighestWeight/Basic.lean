/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Borel
public import TauCeti.Algebra.Lie.Weights.Integrality

public section

/-!
# Highest weight vectors and dominant integral weights

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of the root
system `LieAlgebra.IsKilling.rootSystem H`, so that the nilradicals and the Borel subalgebra of
`TauCeti/Algebra/Lie/Weights/Borel.lean` are available. This file introduces the two notions the
classification of the finite-dimensional irreducible modules is stated with, and proves the
implication between them that the rank-one theory already supplies.

A vector `v` of an `L`-module `M` is a **highest weight vector of weight `lam`** when it is
nonzero, when the Cartan subalgebra acts on it through the linear form `lam`, and when the whole
positive nilradical `n⁺` annihilates it (`TauCeti.IsHighestWeightVector`). A linear form
`lam : Module.Dual K H` is **dominant integral** when its value on each simple coroot is a natural
number (`TauCeti.IsDominantIntegral`).

The main theorem is `TauCeti.IsHighestWeightVector.isDominantIntegral`: the weight of a highest
weight vector in a *finite-dimensional* module is dominant integral. The proof is the rank-one
reduction, one simple root at a time. A simple root `αᵢ` is positive, so the root space `Lαᵢ`
annihilates `v`, and `v` is an eigenvector of `αᵢ^∨` with eigenvalue `lam (αᵢ^∨)`; that is exactly
the hypothesis of
`TauCeti.exists_nat_of_lie_coroot_eq_smul_of_forall_rootSpace_lie_eq_zero`, which produces the
natural number through the `sl₂` triple of `αᵢ`. Dominance then propagates from the simple coroots
to all the positive ones by pure root-system combinatorics
(`TauCeti.IsDominantIntegral.exists_nat_apply_coroot`), a positive coroot being a natural
combination of the simple coroots.

## Main definitions

* `TauCeti.IsHighestWeightVector b lam v`: `v` is nonzero, `H` acts on it by `lam`, and the
  positive nilradical of `b` annihilates it.
* `TauCeti.IsHighestWeightVector.weight`: the weight of `M` that a highest weight vector exhibits.
* `TauCeti.IsDominantIntegral b lam`: the value of `lam` on every simple coroot is a natural
  number.

## Main results

* `TauCeti.isHighestWeightVector_iff_forall_rootSpace`: it is enough to check that each *positive
  root space* annihilates `v`, the positive nilradical being spanned by them.
* `TauCeti.IsHighestWeightVector.unique`: a vector is a highest weight vector for at most one
  weight.
* `TauCeti.IsHighestWeightVector.map` and `TauCeti.IsHighestWeightVector.congr`: morphisms with
  nonzero image, and in particular equivalences, preserve highest weight vectors and their weights.
* `TauCeti.IsHighestWeightVector.mem_genWeightSpace` and
  `TauCeti.IsHighestWeightVector.weight`: a highest weight vector really does exhibit `lam` as a
  weight of `M`, so the vocabulary is not vacuous.
* `TauCeti.IsDominantIntegral.exists_nat_apply_coroot`: a dominant integral weight takes natural
  values on *every* positive coroot, not only on the simple ones.
* `TauCeti.IsDominantIntegral.isIntegralWeight`: every dominant integral weight is integral.
* `TauCeti.IsHighestWeightVector.isDominantIntegral`: the weight of a highest weight vector in a
  finite-dimensional module is dominant integral.

## Implementation notes

`TauCeti.IsHighestWeightVector` is stated as the conjunction pinned by the roadmap rather than as a
structure, and `TauCeti.isHighestWeightVector_iff` together with the three projections
`TauCeti.IsHighestWeightVector.ne_zero`, `TauCeti.IsHighestWeightVector.lie_eq_smul` and
`TauCeti.IsHighestWeightVector.lie_eq_zero_of_mem_positiveNilradical` is its elimination API; no
consumer needs to take the conjunction apart by hand.

The annihilator of a vector is a Lie subalgebra, by the Leibniz rule, and that is the only reason
`TauCeti.isHighestWeightVector_of_forall_rootSpace` holds: the universal property
`TauCeti.positiveNilradical_le_iff` of the positive nilradical is stated against Lie subalgebras.
The annihilator is kept private, being a device of that one proof.

Finite-dimensionality of `M` is a hypothesis of the dominance theorem alone: the definitions and
the elimination API are stated for an arbitrary `L`-module, since the Verma modules that Layer 3 of
the roadmap builds next are infinite-dimensional and carry highest weight vectors all the same.

## References

This file supplies the "highest weight vectors" item of Layer 3 and the `IsDominantIntegral`
definition of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose target signatures
`IsHighestWeightVector` and `IsDominantIntegral` are pinned in the accompanying `Suggested.lean`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §20.2.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w w₁

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]

/-! ### Highest weight vectors -/

variable (b : (IsKilling.rootSystem H).Base)

/-- A **highest weight vector** of weight `lam`, relative to the positive system determined by the
base `b`: a nonzero vector on which the Cartan subalgebra acts through the linear form `lam` and
which is annihilated by the positive nilradical `n⁺`.

For a single positive root this is `IsSl2Triple.HasPrimitiveVectorWith`, and that is how the
dominance theorem `TauCeti.IsHighestWeightVector.isDominantIntegral` below consumes it. -/
def IsHighestWeightVector [LieModule K L M] (lam : Dual K H) (v : M) : Prop :=
  v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧
    ∀ x ∈ positiveNilradical H b, ⁅x, v⁆ = 0

variable [LieModule K L M] {b}

/-- The three defining conditions on a highest weight vector. -/
theorem isHighestWeightVector_iff {lam : Dual K H} {v : M} :
    IsHighestWeightVector b lam v ↔
      v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧
        ∀ x ∈ positiveNilradical H b, ⁅x, v⁆ = 0 :=
  Iff.rfl

namespace IsHighestWeightVector

variable {lam mu : Dual K H} {v : M}

/-- A highest weight vector is nonzero. -/
theorem ne_zero (hv : IsHighestWeightVector b lam v) : v ≠ 0 :=
  (isHighestWeightVector_iff.mp hv).1

/-- The Cartan subalgebra acts on a highest weight vector through its weight. -/
theorem lie_eq_smul (hv : IsHighestWeightVector b lam v) (x : H) : ⁅(x : L), v⁆ = lam x • v :=
  (isHighestWeightVector_iff.mp hv).2.1 x

/-- The positive nilradical annihilates a highest weight vector. -/
theorem lie_eq_zero_of_mem_positiveNilradical (hv : IsHighestWeightVector b lam v) {x : L}
    (hx : x ∈ positiveNilradical H b) : ⁅x, v⁆ = 0 :=
  (isHighestWeightVector_iff.mp hv).2.2 x hx

variable {N : Type w₁} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- A morphism of Lie modules preserves a highest weight vector and its weight whenever its image
is nonzero. -/
theorem map (hv : IsHighestWeightVector b lam v) (f : M →ₗ⁅K,L⁆ N) (hf : f v ≠ 0) :
    IsHighestWeightVector b lam (f v) := by
  refine isHighestWeightVector_iff.mpr ⟨hf, fun x => ?_, fun x hx => ?_⟩
  · rw [← f.map_lie, hv.lie_eq_smul x, map_smul]
  · rw [← f.map_lie, hv.lie_eq_zero_of_mem_positiveNilradical hx, map_zero]

/-- An equivalence of Lie modules preserves highest weight vectors and their weights. -/
theorem congr (hv : IsHighestWeightVector b lam v) (e : M ≃ₗ⁅K,L⁆ N) :
    IsHighestWeightVector b lam (e v) :=
  hv.map (e : M →ₗ⁅K,L⁆ N) fun h =>
    hv.ne_zero (e.injective (h.trans (map_zero e).symm))

/-- Every positive root space annihilates a highest weight vector. -/
theorem lie_eq_zero_of_mem_rootSpace (hv : IsHighestWeightVector b lam v) {α : H.root}
    (hα : α ∈ posRoots (IsKilling.rootSystem H) b) {x : L} (hx : x ∈ rootSpace H (α : H → K)) :
    ⁅x, v⁆ = 0 :=
  hv.lie_eq_zero_of_mem_positiveNilradical (mem_positiveNilradical_of_mem_rootSpace H b hα hx)

/-- **A highest weight vector determines its weight.** A vector is a highest weight vector for at
most one linear form, since it is nonzero and each value `lam x` is read off the action of `x`. -/
theorem unique (hv : IsHighestWeightVector b lam v) (hw : IsHighestWeightVector b mu v) :
    lam = mu := by
  ext x
  have h : (lam x - mu x) • v = 0 := by
    rw [sub_smul, ← hv.lie_eq_smul x, ← hw.lie_eq_smul x, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hv.ne_zero)

end IsHighestWeightVector

/-! ### Recognising a highest weight vector on the root spaces -/

/-- The elements of `L` annihilating a fixed vector `v` form a Lie subalgebra: the bracket is
linear in its left argument, and the Leibniz rule `lie_lie` closes the set under brackets.

This is the Lie subalgebra that the universal property `TauCeti.positiveNilradical_le_iff`, whose
target is a Lie subalgebra rather than a submodule, is applied to in
`TauCeti.isHighestWeightVector_of_forall_rootSpace`. -/
private def annihilator (v : M) : LieSubalgebra K L where
  carrier := {x : L | ⁅x, v⁆ = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [add_lie, hx, hy, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [zero_lie]
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_lie, hx, smul_zero]
  lie_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [lie_lie, hx, hy, lie_zero, lie_zero, sub_zero]

omit [CharZero K] [IsKilling K L] [FiniteDimensional K L] in
private theorem mem_annihilator {v : M} {x : L} :
    x ∈ (annihilator v : LieSubalgebra K L) ↔ ⁅x, v⁆ = 0 :=
  Iff.rfl

/-- **Positive root spaces suffice.** A nonzero `H`-eigenvector annihilated by the root space of
every positive root is a highest weight vector: the positive nilradical is spanned by those root
spaces, and the annihilator of a vector is a Lie subalgebra, so the universal property
`TauCeti.positiveNilradical_le_iff` applies. -/
theorem isHighestWeightVector_of_forall_rootSpace {lam : Dual K H} {v : M} (hv0 : v ≠ 0)
    (hcartan : ∀ x : H, ⁅(x : L), v⁆ = lam x • v)
    (hpos : ∀ α ∈ posRoots (IsKilling.rootSystem H) b,
      ∀ x ∈ rootSpace H (α : H → K), ⁅x, v⁆ = 0) :
    IsHighestWeightVector b lam v := by
  refine isHighestWeightVector_iff.mpr ⟨hv0, hcartan, fun x hx => ?_⟩
  have hle : positiveNilradical H b ≤ (annihilator v : LieSubalgebra K L) :=
    (positiveNilradical_le_iff H b).mpr fun α hα y hy => mem_annihilator.mpr (hpos α hα y hy)
  exact mem_annihilator.mp (hle hx)

/-- Being a highest weight vector is exactly being a nonzero `H`-eigenvector annihilated by every
positive root space. -/
theorem isHighestWeightVector_iff_forall_rootSpace {lam : Dual K H} {v : M} :
    IsHighestWeightVector b lam v ↔
      v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧
        ∀ α ∈ posRoots (IsKilling.rootSystem H) b,
          ∀ x ∈ rootSpace H (α : H → K), ⁅x, v⁆ = 0 :=
  ⟨fun hv => ⟨hv.ne_zero, hv.lie_eq_smul, fun _ hα _ hx => hv.lie_eq_zero_of_mem_rootSpace hα hx⟩,
    fun ⟨hv0, hcartan, hpos⟩ => isHighestWeightVector_of_forall_rootSpace hv0 hcartan hpos⟩

/-! ### The weight exhibited by a highest weight vector -/

namespace IsHighestWeightVector

variable {lam : Dual K H} {v : M}

/-- A nonzero rescaling of a highest weight vector is again one, of the same weight: the two
conditions a highest weight vector satisfies are linear, so only the nonvanishing constrains the
scale. -/
theorem smul (hv : IsHighestWeightVector b lam v) {c : K} (hc : c ≠ 0) :
    IsHighestWeightVector b lam (c • v) :=
  isHighestWeightVector_iff.mpr
    ⟨smul_ne_zero hc hv.ne_zero, fun x => by rw [lie_smul, hv.lie_eq_smul x, smul_comm],
      fun x hx => by rw [lie_smul, hv.lie_eq_zero_of_mem_positiveNilradical hx, smul_zero]⟩

/-- A highest weight vector lies in the generalized weight space of its weight; being an honest
simultaneous eigenvector, it does so at nilpotency index one. -/
theorem mem_genWeightSpace (hv : IsHighestWeightVector b lam v) :
    v ∈ genWeightSpace M (lam : H → K) := by
  rw [LieModule.mem_genWeightSpace]
  refine fun x => ⟨1, ?_⟩
  have hx : (toEnd K H M x) v = lam x • v := by
    rw [toEnd_apply_apply, LieSubalgebra.coe_bracket_of_module, hv.lie_eq_smul x]
  simp [hx]

/-- The weight of a highest weight vector is a weight of the module: the vocabulary is not
vacuous. -/
theorem genWeightSpace_ne_bot (hv : IsHighestWeightVector b lam v) :
    genWeightSpace M (lam : H → K) ≠ ⊥ := fun hbot =>
  hv.ne_zero (by simpa [hbot] using hv.mem_genWeightSpace)

/-- The weight of `M` exhibited by a highest weight vector, packaging
`TauCeti.IsHighestWeightVector.genWeightSpace_ne_bot` so that Mathlib's weight API applies to it. -/
def weight (hv : IsHighestWeightVector b lam v) : Weight K H M where
  toFun := lam
  genWeightSpace_ne_bot' := hv.genWeightSpace_ne_bot

@[simp]
theorem coe_weight (hv : IsHighestWeightVector b lam v) : (hv.weight : H → K) = lam :=
  (rfl)

end IsHighestWeightVector

/-! ### Dominant integral weights -/

variable (b)

/-- A linear form on the Cartan subalgebra is **dominant integral** for the base `b` when its value
on the coroot of every simple root is a natural number. -/
def IsDominantIntegral (lam : Dual K H) : Prop :=
  ∀ i ∈ b.support, ∃ n : ℕ, lam ((IsKilling.rootSystem H).coroot i) = (n : K)

variable {b}

/-- The defining condition on a dominant integral weight. -/
theorem isDominantIntegral_iff {lam : Dual K H} :
    IsDominantIntegral b lam ↔
      ∀ i ∈ b.support, ∃ n : ℕ, lam ((IsKilling.rootSystem H).coroot i) = (n : K) :=
  Iff.rfl

/-- The zero weight is dominant integral. -/
theorem isDominantIntegral_zero : IsDominantIntegral b (0 : Dual K H) :=
  fun _ _ => ⟨0, by simp⟩

/-- Dominant integral weights are closed under addition. -/
theorem IsDominantIntegral.add {lam mu : Dual K H} (hlam : IsDominantIntegral b lam)
    (hmu : IsDominantIntegral b mu) : IsDominantIntegral b (lam + mu) := by
  intro i hi
  obtain ⟨n, hn⟩ := hlam i hi
  obtain ⟨m, hm⟩ := hmu i hi
  exact ⟨n + m, by rw [LinearMap.add_apply, hn, hm, Nat.cast_add]⟩

/-- **Dominance extends from the simple coroots to all the positive ones.** A dominant integral
weight takes a natural value on the coroot of every positive root, because such a coroot is a
natural combination of the simple coroots
(`TauCeti.exists_coroot_eq_sum_nat_of_mem_posRoots`). -/
theorem IsDominantIntegral.exists_nat_apply_coroot {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) :
    ∃ n : ℕ, lam ((IsKilling.rootSystem H).coroot i) = (n : K) := by
  classical
  obtain ⟨f, -, hsum⟩ := exists_coroot_eq_sum_nat_of_mem_posRoots (IsKilling.rootSystem H) b hi
  -- name the natural value of `lam` on each simple coroot
  obtain ⟨g, hg⟩ : ∃ g : H.root → ℕ, ∀ j ∈ b.support,
      lam ((IsKilling.rootSystem H).coroot j) = (g j : K) :=
    ⟨fun j => if hj : j ∈ b.support then (hlam j hj).choose else 0,
      fun j hj => by simpa only [dite_eq_left hj] using (hlam j hj).choose_spec⟩
  refine ⟨∑ j ∈ b.support, f j * g j, ?_⟩
  rw [hsum, map_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_nsmul, hg j hj, Nat.cast_mul, nsmul_eq_mul]

/-- **A dominant integral weight is integral**: it takes integer values on every coroot, not just
natural values on the simple ones. A coroot is the coroot of a positive root or the negative of
one, and on a positive coroot dominance gives a natural value. -/
theorem IsDominantIntegral.isIntegralWeight {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) : IsIntegralWeight lam := by
  apply isIntegralWeight_of_forall_exists_int_apply_coroot
  intro α
  rcases eq_or_ne (α : Dual K H) 0 with h | h
  · refine ⟨0, ?_⟩
    have hcoroot : IsKilling.coroot α = 0 :=
      IsKilling.coroot_eq_zero_iff.mpr (Weight.coe_toLinear_eq_zero_iff.mp h)
    rw [hcoroot]
    simp
  have hα : α.IsNonZero := fun hz ↦ h (Weight.coe_toLinear_eq_zero_iff.mpr hz)
  obtain ⟨i, rfl⟩ : ∃ i : H.root, (i : Weight K H L) = α :=
    ⟨⟨α, by simpa [LieSubalgebra.root] using hα⟩, rfl⟩
  rcases mem_posRoots_or_mem_negRoots (IsKilling.rootSystem H) b i with hi | hi
  · obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi
    exact ⟨n, by simpa using hn⟩
  · have hi' : -i ∈ posRoots (IsKilling.rootSystem H) b := by
      rw [← IsKilling.rootSystem_reflectionPerm_self_eq_neg]
      exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots (IsKilling.rootSystem H) b i).mpr hi
    obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi'
    refine ⟨-n, ?_⟩
    rw [IsKilling.rootSystem_coroot_apply, IsKilling.val_neg_root, IsKilling.coroot_neg,
      map_neg] at hn
    push_cast
    linear_combination -hn

/-! ### The weight of a highest weight vector is dominant integral -/

variable [FiniteDimensional K M]

/-- **The weight of a highest weight vector is dominant integral.** For a highest weight vector `v`
in a finite-dimensional module and a simple root `αᵢ`, the vector `v` is an eigenvector of the
coroot `αᵢ^∨` with eigenvalue `lam (αᵢ^∨)` and is annihilated by the root space `Lαᵢ`, simple roots
being positive; the `sl₂` triple of `αᵢ` then forces the eigenvalue to be a natural number.

This is the half of the highest-weight classification that the rank-one theory supplies on its own.
The converse, that every dominant integral weight is the weight of a highest weight vector in a
finite-dimensional module, needs the Verma modules and is not proved here. -/
theorem IsHighestWeightVector.isDominantIntegral {lam : Dual K H} {v : M}
    (hv : IsHighestWeightVector b lam v) : IsDominantIntegral b lam := by
  intro i hi
  have hipos : i ∈ posRoots (IsKilling.rootSystem H) b :=
    support_subset_posRoots (IsKilling.rootSystem H) b hi
  rw [IsKilling.rootSystem_coroot_apply]
  exact exists_nat_of_lie_coroot_eq_smul_of_forall_rootSpace_lie_eq_zero (M := M)
    (LieSubalgebra.isNonZero_coe_root i) hv.ne_zero (hv.lie_eq_smul _)
    fun _ he => hv.lie_eq_zero_of_mem_rootSpace hipos he

end TauCeti
