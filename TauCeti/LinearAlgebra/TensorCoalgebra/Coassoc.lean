/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.TensorCoalgebra.Basic

/-!
# Reduced deconcatenation is coassociative

`TauCeti.ReducedTensorWords.deconcatenation` cuts a nonempty tensor word at every nontrivial
position.  This file proves that it is coassociative, so that reduced tensor words carry the
structure of a (non-counital) coalgebra: cutting twice is the same operation whether the second
cut is made in the left or in the right factor of the first one, both sides being the sum over
all pairs of nested cuts.

The bookkeeping runs through `TauCeti.ReducedTensorWords.subword`, the length-`b` block of a
tuple starting at position `a`.  Storing the block length as a plain natural-number argument,
rather than as the tensor-power index it names, keeps every reindexing of the sums below an
ordinary computation with natural numbers.  In these terms deconcatenation is
`Δ (subword x a b) = ∑ c, subword x a c ⊗ subword x (a + c) (b - c)`, and coassociativity becomes
`Finset.sum_comm` after both double sums have been extended over the same square of cut positions.

## Main results

* `TauCeti.ReducedTensorWords.deconcatenation_coassoc`: reduced deconcatenation is coassociative.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable (R : Type uR) {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Cutting the left block again gives the sum over all possible earlier cut positions. -/
private theorem rTensor_deconcatenation_subword {n : ℕ} (y : Fin n → M) (a b : ℕ) {c : ℕ}
    (hc : c ∈ Finset.Ioo 0 b) :
    TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
        (ReducedTensorWords R M)
        (LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M)
          (subword R y a c ⊗ₜ[R] subword R y (a + c) (b - c))) =
      ∑ d ∈ Finset.Ioo 0 b,
        subword R y a d ⊗ₜ[R]
          (subword R y (a + d) (c - d) ⊗ₜ[R] subword R y (a + c) (b - c)) := by
  simp only [Finset.mem_Ioo] at hc
  rw [LinearMap.rTensor_tmul, deconcatenation_subword R y (a := a) (b := c),
    TensorProduct.sum_tmul, map_sum]
  simp only [TensorProduct.assoc_tmul]
  refine Finset.sum_subset (Finset.Ioo_subset_Ioo le_rfl (by omega)) ?_
  intro d hd hd'
  simp only [Finset.mem_Ioo] at hd hd'
  have hcd : c - d = 0 := by omega
  rw [hcd, subword_length_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-- Cutting the right block again gives the sum over the absolute position `q` of the second cut
inside the length-`b` block; inside the right block that cut sits at the relative position
`q - c`. -/
private theorem lTensor_deconcatenation_subword {n : ℕ} (y : Fin n → M) (a b : ℕ) {c : ℕ}
    (hc : c ∈ Finset.Ioo 0 b) :
    LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M)
        (subword R y a c ⊗ₜ[R] subword R y (a + c) (b - c)) =
      ∑ q ∈ Finset.Ioo 0 b,
        subword R y a c ⊗ₜ[R]
          (subword R y (a + c) (q - c) ⊗ₜ[R] subword R y (a + q) (b - q)) := by
  simp only [Finset.mem_Ioo] at hc
  rw [LinearMap.lTensor_tmul, deconcatenation_subword R y (a := a + c) (b := b - c),
    TensorProduct.tmul_sum]
  let g := fun q ↦ subword R y a c ⊗ₜ[R]
    (subword R y (a + c) (q - c) ⊗ₜ[R] subword R y (a + q) (b - q))
  calc
    _ = ∑ q ∈ Finset.Ioo c b, g q := by
      rw [← Finset.Ico_succ_left_eq_Ioo 0 (b - c), ← Finset.Ico_succ_left_eq_Ioo c b]
      calc
        _ = ∑ e ∈ Finset.Ico 1 (b - c), g (c + e) := by
          refine Finset.sum_congr rfl fun e he ↦ ?_
          simp only [Finset.mem_Ico] at he
          dsimp only [g]
          have h1 : c + e - c = e := by omega
          have h2 : b - (c + e) = b - c - e := by omega
          rw [h1, h2, Nat.add_assoc]
        _ = ∑ q ∈ Finset.Ico (1 + c) (b - c + c), g q :=
          Finset.sum_Ico_add g 1 (b - c) c
        _ = _ := by
          congr 2
          · simp only [Order.succ_eq_add_one]
            omega
          · omega
    _ = ∑ q ∈ Finset.Ioo 0 b, g q := by
      refine Finset.sum_subset (Finset.Ioo_subset_Ioo (Nat.zero_le c) le_rfl) ?_
      intro q hq hq'
      simp only [Finset.mem_Ioo] at hq hq'
      have hqc : q - c = 0 := by omega
      dsimp only [g]
      rw [hqc, subword_length_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-- Both ways of iterating deconcatenation agree on every subword. -/
theorem deconcatenation_coassoc_subword {n : ℕ} (y : Fin n → M) (a b : ℕ) :
    TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
        (ReducedTensorWords R M)
        (LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M)
          (deconcatenation R M (subword R y a b))) =
      LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M)
        (deconcatenation R M (subword R y a b)) := by
  rw [deconcatenation_subword R y (a := a) (b := b)]
  simp only [map_sum]
  rw [Finset.sum_congr rfl fun c hc ↦ rTensor_deconcatenation_subword R y a b hc,
    Finset.sum_congr rfl fun c hc ↦ lTensor_deconcatenation_subword R y a b hc]
  exact Finset.sum_comm

variable (M)

/-- Reduced deconcatenation is coassociative: cutting a tensor word twice gives the same sum of
triples of blocks whether the second cut is taken in the left or in the right factor of the
first. -/
theorem deconcatenation_coassoc :
    (TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
          (ReducedTensorWords R M)).toLinearMap ∘ₗ
        LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M) ∘ₗ
          deconcatenation R M =
      LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M) ∘ₗ deconcatenation R M := by
  apply linearMap_ext R M
  intro k y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [of_tprod_eq_subword R k.2 y]
  exact deconcatenation_coassoc_subword R y 0 k.1

end ReducedTensorWords

end TauCeti
