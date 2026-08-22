/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Two-sided ideals spanned by homogeneous elements

A relation ideal of a noncommutative graded ring is presented as `TwoSidedIdeal.span` of a set of
relators, and it is homogeneous as soon as those relators are. This file proves that, together
with the two absorption lemmas the proof runs on: if every homogeneous component of `x` lies in a
two-sided ideal, then so does every homogeneous component of `a * x` and of `x * a`.

Homogeneity itself is stated through Mathlib's `Ideal.IsHomogeneous`, applied to the underlying
one-sided ideal `TwoSidedIdeal.asIdeal`, which is where the quotient by a two-sided ideal is
formed.

## Main results

* `TauCeti.isHomogeneous_asIdeal_span`: **a two-sided ideal spanned by homogeneous elements is
  homogeneous.**
* `TauCeti.proj_mul_mem_left` and `TauCeti.proj_mul_mem_right`: the absorption lemmas.

## Implementation notes

`Ideal.mul_homogeneous_element_mem_of_mem` supplies the one-sided half of `proj_mul_mem_left`,
where the *homogeneous* factor is on the right; `TauCeti.proj_homogeneous_mul_mem` is its mirror
image, which needs the two-sidedness of the ideal and is therefore stated for a `TwoSidedIdeal`.
-/

public section

namespace TauCeti

open DirectSum

variable {ι σ A : Type*} [Ring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
  [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

/-- The homogeneous components of `x * a`, for `x` a homogeneous element of a two-sided ideal,
lie in that ideal. This is the mirror image of `Ideal.mul_homogeneous_element_mem_of_mem`, and it
is where the two-sidedness is used. -/
theorem proj_homogeneous_mul_mem (I : TwoSidedIdeal A) {x : A}
    (hx : SetLike.IsHomogeneousElem 𝒜 x) (hxI : x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (x * a) ∈ I := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.mul_sum, map_sum]
  refine sum_mem fun l _ => ?_
  obtain ⟨i, hi⟩ := hx
  have mem₁ : x * (DirectSum.decompose 𝒜 a l : A) ∈ 𝒜 (i + l) :=
    SetLike.GradedMul.mul_mem hi (SetLike.coe_mem _)
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 mem₁, DirectSum.coe_of_apply]
  split_ifs
  · exact I.mul_mem_right _ _ hxI
  · exact I.zero_mem

/-- **Left absorption of componentwise membership**: if every homogeneous component of `x` lies in
a two-sided ideal, so does every homogeneous component of `a * x`. -/
theorem proj_mul_mem_left {I : TwoSidedIdeal A} {x : A}
    (hx : ∀ i, GradedRing.proj 𝒜 i x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (a * x) ∈ I := by
  classical
  have hsplit : GradedRing.proj 𝒜 j (a * x)
      = ∑ l ∈ (DirectSum.decompose 𝒜 x).support,
          GradedRing.proj 𝒜 j (a * (DirectSum.decompose 𝒜 x l : A)) := by
    rw [← map_sum, ← Finset.mul_sum, DirectSum.sum_support_decompose]
  rw [hsplit]
  refine sum_mem fun l _ => ?_
  rw [← TwoSidedIdeal.mem_asIdeal]
  refine Ideal.mul_homogeneous_element_mem_of_mem 𝒜 a _ ⟨l, SetLike.coe_mem _⟩ ?_ j
  rw [TwoSidedIdeal.mem_asIdeal, ← GradedRing.proj_apply]
  exact hx l

/-- **Right absorption of componentwise membership**: if every homogeneous component of `x` lies in
a two-sided ideal, so does every homogeneous component of `x * a`. -/
theorem proj_mul_mem_right {I : TwoSidedIdeal A} {x : A}
    (hx : ∀ i, GradedRing.proj 𝒜 i x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (x * a) ∈ I := by
  classical
  have hsplit : GradedRing.proj 𝒜 j (x * a)
      = ∑ l ∈ (DirectSum.decompose 𝒜 x).support,
          GradedRing.proj 𝒜 j ((DirectSum.decompose 𝒜 x l : A) * a) := by
    rw [← map_sum, ← Finset.sum_mul, DirectSum.sum_support_decompose]
  rw [hsplit]
  refine sum_mem fun l _ => ?_
  refine proj_homogeneous_mul_mem 𝒜 I ⟨l, SetLike.coe_mem _⟩ ?_ a j
  rw [← GradedRing.proj_apply]
  exact hx l

/-- Every homogeneous component of an element of a two-sided ideal spanned by homogeneous elements
lies in that ideal again. -/
theorem proj_mem_span_of_mem_span {s : Set A} (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x)
    {x : A} (hx : x ∈ TwoSidedIdeal.span s) (i : ι) :
    GradedRing.proj 𝒜 i x ∈ TwoSidedIdeal.span s := by
  induction hx using TwoSidedIdeal.span_induction generalizing i with
  | mem y hy =>
    obtain ⟨d, hd⟩ := hs y hy
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 hd, DirectSum.coe_of_apply]
    split_ifs
    · exact TwoSidedIdeal.subset_span hy
    · exact TwoSidedIdeal.zero_mem _
  | zero => rw [map_zero]; exact TwoSidedIdeal.zero_mem _
  | add y z _ _ ihy ihz => rw [map_add]; exact TwoSidedIdeal.add_mem _ (ihy i) (ihz i)
  | neg y _ ihy => rw [map_neg]; exact TwoSidedIdeal.neg_mem _ (ihy i)
  | left_absorb a y _ ihy => exact proj_mul_mem_left 𝒜 (fun j => ihy j) a i
  | right_absorb b y _ ihy => exact proj_mul_mem_right 𝒜 (fun j => ihy j) b i

/-- **A two-sided ideal spanned by homogeneous elements is homogeneous.** This is what makes a
relation quotient of a graded ring graded: relators homogeneous for the grading generate a
homogeneous ideal. -/
theorem isHomogeneous_asIdeal_span {s : Set A} (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    (TwoSidedIdeal.span s).asIdeal.IsHomogeneous 𝒜 := by
  intro i x hx
  rw [TwoSidedIdeal.mem_asIdeal] at hx ⊢
  rw [← GradedRing.proj_apply]
  exact proj_mem_span_of_mem_span 𝒜 hs hx i

end TauCeti
