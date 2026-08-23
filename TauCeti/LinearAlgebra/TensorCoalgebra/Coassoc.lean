/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Order.Interval.Finset.Nat
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
  have key : ∀ (n : ℕ) (hn : 0 < n) (y : Fin n → M),
      TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
          (ReducedTensorWords R M)
          (LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M)
            (deconcatenation R M (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R y)))) =
        LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M)
          (deconcatenation R M (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R y))) := by
    intro n hn y
    rw [of_tprod_eq_subword R hn y, deconcatenation_subword R y (a := 0) (b := n)]
    simp only [Nat.zero_add, map_sum]
    -- Cutting the left factor again, then extending the inner sum by vanishing terms.
    have hL : ∀ c ∈ Finset.Ioo 0 n,
        TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
            (ReducedTensorWords R M)
            (LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M)
              (subword R y 0 c ⊗ₜ[R] subword R y c (n - c))) =
          ∑ d ∈ Finset.Ioo 0 n,
            subword R y 0 d ⊗ₜ[R] (subword R y d (c - d) ⊗ₜ[R] subword R y c (n - c)) := by
      intro c hc
      simp only [Finset.mem_Ioo] at hc
      rw [LinearMap.rTensor_tmul, deconcatenation_subword R y (a := 0) (b := c),
        TensorProduct.sum_tmul, map_sum]
      simp only [Nat.zero_add, TensorProduct.assoc_tmul]
      refine Finset.sum_subset (Finset.Ioo_subset_Ioo le_rfl (by omega)) ?_
      intro d hd hd'
      simp only [Finset.mem_Ioo] at hd hd'
      have hcd : c - d = 0 := by omega
      rw [hcd, subword_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    -- Cutting the right factor again, reindexing by the absolute position of the second cut.
    have hR : ∀ c ∈ Finset.Ioo 0 n,
        LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M)
            (subword R y 0 c ⊗ₜ[R] subword R y c (n - c)) =
          ∑ q ∈ Finset.Ioo 0 n,
            subword R y 0 c ⊗ₜ[R] (subword R y c (q - c) ⊗ₜ[R] subword R y q (n - q)) := by
      intro c hc
      simp only [Finset.mem_Ioo] at hc
      rw [LinearMap.lTensor_tmul, deconcatenation_subword R y (a := c) (b := n - c),
        TensorProduct.tmul_sum]
      rw [Finset.sum_nbij' (t := Finset.Ioo c n) (fun e ↦ c + e) (fun q ↦ q - c)
        (g := fun q ↦ subword R y 0 c ⊗ₜ[R]
          (subword R y c (q - c) ⊗ₜ[R] subword R y q (n - q)))]
      · refine Finset.sum_subset (Finset.Ioo_subset_Ioo (Nat.zero_le c) le_rfl) ?_
        intro q hq hq'
        simp only [Finset.mem_Ioo] at hq hq'
        have hqc : q - c = 0 := by omega
        rw [hqc, subword_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
      · intro e he
        simp only [Finset.mem_Ioo] at he ⊢
        omega
      · intro q hq
        simp only [Finset.mem_Ioo] at hq ⊢
        omega
      · intro e _
        omega
      · intro q hq
        simp only [Finset.mem_Ioo] at hq
        omega
      · intro e he
        simp only [Finset.mem_Ioo] at he
        have h1 : c + e - c = e := by omega
        have h2 : n - (c + e) = n - c - e := by omega
        rw [h1, h2]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    exact Finset.sum_comm
  apply DirectSum.linearMap_ext R
  intro k
  apply LinearMap.ext
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r y =>
      simp only [LinearMap.comp_apply, map_smul, LinearEquiv.coe_coe]
      convert congrArg (r • ·) (key k.1 k.2 y) using 1 <;> rfl
  | add u v hu hv =>
      simp only [LinearMap.comp_apply, map_add] at hu hv ⊢
      rw [hu, hv]

end ReducedTensorWords

end TauCeti
