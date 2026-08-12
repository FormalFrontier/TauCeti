/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# Height and integral relations among roots

The height of a root relative to a base of a root pairing is the sum of the coefficients of its
expansion in the simple roots. This file records that height respects every integral relation
among the roots: a vanishing integral combination of roots has a vanishing combination of heights,
so two integral combinations with the same value have the same combination of heights.

## Main results

* `TauCeti.sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero` says that height respects integral
  relations among roots.
* `TauCeti.sum_mul_height_eq_of_sum_zsmul_root_eq` compares the heights of two integral
  combinations of roots with the same value.

## References

This supports “Simple-root lowering” in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The argument follows Bourbaki,
*Lie Groups and Lie Algebras*, Chapters 4--6.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [CharZero R]

/-- If an integral combination of roots vanishes, the same combination of their heights
vanishes. -/
theorem sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero (b : P.Base) {s : Finset ι} {e : ι → ℤ}
    (he : ∑ i ∈ s, e i • P.root i = 0) :
    ∑ i ∈ s, e i * b.height i = 0 := by
  classical
  -- Expand the roots in the simple roots and use their linear independence.
  choose g _hgsupp _hgsign hg using fun i : ι ↦ b.exists_root_eq_sum_int i
  have hcomb : ∑ j ∈ b.support, (∑ i ∈ s, e i * g i j) • P.root j = 0 := by
    rw [← he]
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.smul_sum, ← hg i]
  have hczero : ∀ j ∈ b.support, (∑ i ∈ s, e i * g i j) = 0 :=
    linearIndepOn_iff'.mp (b.linearIndepOn_root.restrict_scalars' ℤ) b.support
      (fun j ↦ ∑ i ∈ s, e i * g i j) (fun _ h ↦ h) hcomb
  calc ∑ i ∈ s, e i * b.height i
      = ∑ i ∈ s, ∑ j ∈ b.support, e i * g i j :=
        Finset.sum_congr rfl fun i _ ↦ by rw [b.height_eq_sum (hg i), Finset.mul_sum]
    _ = ∑ j ∈ b.support, ∑ i ∈ s, e i * g i j := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero hczero

/-- Two integral combinations of roots with the same value have the same combination of
heights. -/
theorem sum_mul_height_eq_of_sum_zsmul_root_eq (b : P.Base) {s t : Finset ι} {e f : ι → ℤ}
    (h : ∑ i ∈ s, e i • P.root i = ∑ i ∈ t, f i • P.root i) :
    ∑ i ∈ s, e i * b.height i = ∑ i ∈ t, f i * b.height i := by
  classical
  -- Extend both coefficient functions by zero to `s ∪ t`, where the two combinations can be
  -- subtracted from one another.
  have key := sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero P b (s := s ∪ t)
    (e := fun i ↦ (if i ∈ s then e i else 0) - (if i ∈ t then f i else 0)) ?_
  · simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, sub_eq_zero] at key
    exact key
  · simp_rw [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, h, sub_self]

end TauCeti
