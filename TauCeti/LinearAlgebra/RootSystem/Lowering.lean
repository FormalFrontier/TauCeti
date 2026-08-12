/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# Lowering positive roots by simple reflections

This file records how reflection in a simple root changes the height relative to a root-pairing
base. The change is the corresponding Cartan integer. When the root index type is finite, every
positive root admits a simple reflection that strictly decreases its height. If the coefficient
ring is also a domain and the pairing is reduced, a positive root that is not simple can be lowered
while remaining positive.

It also records that height respects integral relations among roots, the general height fact used
to compare different expressions of an element of the root lattice.

## Main results

* `TauCeti.sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero` says that height respects integral
  relations among roots.
* `TauCeti.height_reflectionPerm` computes the height after an arbitrary root reflection.
* `TauCeti.height_reflectionPerm_lt_iff` characterizes strict height decrease by positivity of
  the corresponding Cartan integer.
* `TauCeti.exists_mem_support_height_reflectionPerm_lt` gives the positive-root lowering step for
  a nonsimple positive root.

## References

This file implements “Simple-root lowering” in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The argument follows Bourbaki,
*Lie Groups and Lie Algebras*, Chapters 4--6.

Mathlib already carries out this height computation and lowering step inside the proof of
`RootPairing.Base.IsPos.induction_on_reflect`, where it is packaged as a strong induction
principle rather than exposed. The declarations below state that computation and the resulting
existence results in their own right.
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
theorem sum_mul_height_eq_of_sum_zsmul_root_eq (b : P.Base) {s : Finset ι} {e f : ι → ℤ}
    (h : ∑ i ∈ s, e i • P.root i = ∑ i ∈ s, f i • P.root i) :
    ∑ i ∈ s, e i * b.height i = ∑ i ∈ s, f i * b.height i := by
  have h0 : ∑ i ∈ s, (e i - f i) • P.root i = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have key := sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero P b h0
  simp_rw [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at key
  exact key

variable [P.IsCrystallographic]

/-- Reflection in the root indexed by `i` changes the height of `j` by the Cartan integer
`P.pairingIn ℤ j i` times the height of `i`. -/
lemma height_reflectionPerm (b : P.Base) (i j : ι) :
    b.height (P.reflectionPerm i j) =
      b.height j - P.pairingIn ℤ j i * b.height i := by
  have hreflect := P.reflection_apply_root' ℤ (i := i) (j := j)
  rw [← P.root_reflectionPerm, sub_eq_add_neg, ← neg_smul] at hreflect
  rw [b.height_add_zsmul hreflect]
  simp [sub_eq_add_neg]

/-- Reflection in a simple root subtracts the corresponding Cartan integer from the height. -/
@[simp]
lemma height_reflectionPerm_of_mem_support (b : P.Base) {i j : ι}
    (hi : i ∈ b.support) :
    b.height (P.reflectionPerm i j) =
      b.height j - P.pairingIn ℤ j i := by
  rw [height_reflectionPerm P b, b.height_one_of_mem_support hi, mul_one]

/-- Reflection in a simple root strictly decreases height exactly when the corresponding Cartan
integer is positive. -/
lemma height_reflectionPerm_lt_iff (b : P.Base) {i j : ι}
    (hi : i ∈ b.support) :
    b.height (P.reflectionPerm i j) < b.height j ↔
      0 < P.pairingIn ℤ j i := by
  rw [height_reflectionPerm_of_mem_support P b hi]
  omega

/-- A positive root has positive Cartan pairing with some simple coroot. -/
lemma exists_mem_support_pos_pairingIn [Finite ι] (b : P.Base) {j : ι} (hj : b.IsPos j) :
    ∃ i ∈ b.support, 0 < P.pairingIn ℤ j i := by
  -- Mathlib provides the transposed pairing; finiteness makes the two pairings have the same sign.
  obtain ⟨i, hi, hpair⟩ := hj.exists_mem_support_pos_pairingIn
  exact ⟨i, hi, (P.zero_lt_pairingIn_iff' ℤ).mp hpair⟩

private lemma exists_mem_support_height_reflectionPerm_lt_aux [Finite ι]
    (b : P.Base) {j : ι} (hj : b.IsPos j) :
    ∃ i ∈ b.support,
      b.height (P.reflectionPerm i j) < b.height j := by
  obtain ⟨i, hi, hpair⟩ := exists_mem_support_pos_pairingIn P b hj
  exact ⟨i, hi, (height_reflectionPerm_lt_iff P b hi).mpr hpair⟩

/-- A nonsimple positive root admits a simple reflection that remains positive and has strictly
smaller height. This is the positive-root lowering step used by induction on height. -/
theorem exists_mem_support_height_reflectionPerm_lt [Finite ι] [IsDomain R]
    [P.IsReduced] (b : P.Base) {j : ι}
    (hj : b.IsPos j) (hj' : j ∉ b.support) :
    ∃ i ∈ b.support, b.IsPos (P.reflectionPerm i j) ∧
      b.height (P.reflectionPerm i j) < b.height j := by
  obtain ⟨i, hi, hheight⟩ :=
    exists_mem_support_height_reflectionPerm_lt_aux P b hj
  refine ⟨i, hi, hj.reflectionPerm hi ?_, hheight⟩
  exact fun hji ↦ hj' (hji ▸ hi)

end TauCeti
