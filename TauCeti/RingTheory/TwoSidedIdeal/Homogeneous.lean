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
with the two absorption lemmas the proof runs on: if every homogeneous component of `x` lies in an
ideal, then so does every homogeneous component of `a * x` and of `x * a`.

Homogeneity itself is stated through Mathlib's `Ideal.IsHomogeneous`, applied to the underlying
one-sided ideal `TwoSidedIdeal.asIdeal`, which is where the quotient by a two-sided ideal is
formed.

## Main results

* `TauCeti.TwoSidedIdeal.homogeneous_span`: **a two-sided ideal spanned by homogeneous elements
  is homogeneous.**
* `TauCeti.Ideal.proj_mul_mem_left` and `TauCeti.TwoSidedIdeal.proj_mul_mem_right`: the absorption
  lemmas.

## Implementation notes

Mathlib's `Ideal.mul_homogeneous_element_mem_of_mem` supplies the one-sided half of
`TauCeti.Ideal.proj_mul_mem_left`, where the *homogeneous* factor is on the right; multiplying on
the right only asks the ideal to absorb on the left, so that lemma is stated for an `Ideal` and
lives in the matching namespace. Its mirror image
`TauCeti.TwoSidedIdeal.homogeneous_element_mul_mem_of_mem` is the one place two-sidedness is used,
and it is therefore stated for a `TwoSidedIdeal`.

## References

Mathlib's `Ideal.homogeneous_span` is the one-sided statement that
`TauCeti.TwoSidedIdeal.homogeneous_span` extends from `Ideal.span` to `TwoSidedIdeal.span`, and the
proof of `TauCeti.TwoSidedIdeal.homogeneous_element_mul_mem_of_mem` is adapted from Mathlib's proof
of `Ideal.mul_homogeneous_element_mem_of_mem`, with the two factors swapped.

The open Mathlib PR [#36501](https://github.com/leanprover-community/mathlib4/pull/36501) builds
the graded structure on the quotient of a graded ring by a homogeneous relation. That is the step
*after* the one taken here, and it is independent of it: homogeneity of the relation is an input
there, and it is what the statements below produce for a relation ideal presented by generators.
-/

public section

namespace TauCeti

open DirectSum

variable {ι σ A : Type*}

namespace Ideal

variable [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
  [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

/-- **Left absorption of componentwise membership**: if every homogeneous component of `x` lies in
an ideal, so does every homogeneous component of `a * x`. -/
theorem proj_mul_mem_left {I : _root_.Ideal A} {x : A}
    (hx : ∀ i, GradedRing.proj 𝒜 i x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (a * x) ∈ I := by
  classical
  have hsplit : GradedRing.proj 𝒜 j (a * x)
      = ∑ l ∈ (DirectSum.decompose 𝒜 x).support,
          GradedRing.proj 𝒜 j (a * (DirectSum.decompose 𝒜 x l : A)) := by
    rw [← map_sum, ← Finset.mul_sum, DirectSum.sum_support_decompose]
  rw [hsplit]
  refine sum_mem fun l _ => ?_
  refine _root_.Ideal.mul_homogeneous_element_mem_of_mem 𝒜 a _ ⟨l, SetLike.coe_mem _⟩ ?_ j
  rw [← GradedRing.proj_apply]
  exact hx l

end Ideal

namespace TwoSidedIdeal

variable [Ring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
  [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

/-- The homogeneous components of `x * a`, for `x` a homogeneous element of a two-sided ideal,
lie in that ideal. This is the mirror image of `Ideal.mul_homogeneous_element_mem_of_mem`, and it
is where the two-sidedness is used. -/
theorem homogeneous_element_mul_mem_of_mem {I : _root_.TwoSidedIdeal A} {x : A}
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

/-- **Right absorption of componentwise membership**: if every homogeneous component of `x` lies in
a two-sided ideal, so does every homogeneous component of `x * a`. -/
theorem proj_mul_mem_right {I : _root_.TwoSidedIdeal A} {x : A}
    (hx : ∀ i, GradedRing.proj 𝒜 i x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (x * a) ∈ I := by
  classical
  have hsplit : GradedRing.proj 𝒜 j (x * a)
      = ∑ l ∈ (DirectSum.decompose 𝒜 x).support,
          GradedRing.proj 𝒜 j ((DirectSum.decompose 𝒜 x l : A) * a) := by
    rw [← map_sum, ← Finset.sum_mul, DirectSum.sum_support_decompose]
  rw [hsplit]
  refine sum_mem fun l _ => ?_
  refine homogeneous_element_mul_mem_of_mem 𝒜 ⟨l, SetLike.coe_mem _⟩ ?_ a j
  rw [← GradedRing.proj_apply]
  exact hx l

/-- Every homogeneous component of an element of a two-sided ideal spanned by homogeneous elements
lies in that ideal again. Private: it is `homogeneous_span` read through `GradedRing.proj` and
`TwoSidedIdeal.mem_asIdeal`. -/
private theorem proj_mem_span_of_mem_span {s : Set A}
    (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) {x : A}
    (hx : x ∈ _root_.TwoSidedIdeal.span s) (i : ι) :
    GradedRing.proj 𝒜 i x ∈ _root_.TwoSidedIdeal.span s := by
  induction hx using _root_.TwoSidedIdeal.span_induction generalizing i with
  | mem y hy =>
    obtain ⟨d, hd⟩ := hs y hy
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 hd, DirectSum.coe_of_apply]
    split_ifs
    · exact _root_.TwoSidedIdeal.subset_span hy
    · exact _root_.TwoSidedIdeal.zero_mem _
  | zero => rw [map_zero]; exact _root_.TwoSidedIdeal.zero_mem _
  | add y z _ _ ihy ihz => rw [map_add]; exact _root_.TwoSidedIdeal.add_mem _ (ihy i) (ihz i)
  | neg y _ ihy => rw [map_neg]; exact _root_.TwoSidedIdeal.neg_mem _ (ihy i)
  | left_absorb a y _ ihy =>
    rw [← _root_.TwoSidedIdeal.mem_asIdeal]
    exact Ideal.proj_mul_mem_left 𝒜 (fun j => _root_.TwoSidedIdeal.mem_asIdeal.2 (ihy j)) a i
  | right_absorb b y _ ihy => exact proj_mul_mem_right 𝒜 (fun j => ihy j) b i

/-- **A two-sided ideal spanned by homogeneous elements is homogeneous.** This supplies the
homogeneity condition needed to descend a grading to a relation quotient. -/
theorem homogeneous_span {s : Set A} (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    (_root_.TwoSidedIdeal.span s).asIdeal.IsHomogeneous 𝒜 := by
  intro i x hx
  rw [_root_.TwoSidedIdeal.mem_asIdeal] at hx ⊢
  rw [← GradedRing.proj_apply]
  exact proj_mem_span_of_mem_span 𝒜 hs hx i

end TwoSidedIdeal

end TauCeti
