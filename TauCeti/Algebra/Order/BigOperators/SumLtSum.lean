/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin

/-!
# Comparing two sums when one index set dominates the other

Two finite sets of the same size, one of which carries a strictly larger weight at every point
than the other, have strictly ordered sums (`TauCeti.sum_lt_sum_of_forall_lt`): the sizes agreeing
is what makes the comparison work without any pointwise pairing of the two sets, since any
bijection between them compares the weights termwise.

`TauCeti.sum_lt_sum_image_sdiff` is the form in which the comparison is used. A permutation `σ`
of a finite set `X` that does not map a part `A` of it to itself must move some point of `A` out
of `A`; if `A` carries the larger weights, the image of the complementary part `X \ A` therefore
weighs strictly more than `X \ A` itself. The two sums involved differ only on the points that
`σ` moves in or out of `X \ A`, and those are compared by the previous lemma.

The weights take values in an ordered cancellative additive commutative monoid, cancellation being
what turns the comparison of the two differences into a comparison of the two sums.
-/

public section

namespace TauCeti

variable {α M : Type*} [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M]
  [AddLeftStrictMono M]

/-- **A set whose weights are all smaller than those of a second set of the same size has the
smaller sum.** The two sets have the same size, so some bijection matches them up, and along it
every weight of the first set is smaller than the weight of its partner. -/
theorem sum_lt_sum_of_forall_lt (f : α → M) {U V : Finset α}
    (hcard : V.card = U.card) (hU : U.Nonempty) (hlt : ∀ u ∈ U, ∀ v ∈ V, f v < f u) :
    ∑ v ∈ V, f v < ∑ u ∈ U, f u := by
  classical
  have _ : Nonempty {x // x ∈ U} := hU.to_subtype
  let e : {x // x ∈ U} ≃ {x // x ∈ V} := Finset.equivOfCardEq hcard.symm
  calc ∑ v ∈ V, f v
      = ∑ u : {x // x ∈ U}, f (e u) := by
        rw [Equiv.sum_comp e fun v : {x // x ∈ V} => f v, Finset.sum_coe_sort V f]
    _ < ∑ u : {x // x ∈ U}, f u :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          fun u _ => hlt u u.2 (e u) (e u).2
    _ = ∑ u ∈ U, f u := Finset.sum_coe_sort U f

/-- **A permutation of a set that does not preserve a prescribed part increases the sum over the
other part.** If every weight of `A` exceeds every weight of `X \ A`, and `σ` permutes `X` without
mapping `A` to itself, then `σ` moves some point of `A` into the image of `X \ A`, exchanging a
point for one of strictly larger weight, so that image has the larger sum. -/
theorem sum_lt_sum_image_sdiff [DecidableEq α] (f : α → M) {X A : Finset α}
    {σ : Equiv.Perm α} (hAX : A ⊆ X) (hXimg : X.image σ = X) (himg : A.image σ ≠ A)
    (hlt : ∀ a ∈ A, ∀ b ∈ X \ A, f b < f a) :
    ∑ z ∈ X \ A, f z < ∑ z ∈ (X \ A).image σ, f z := by
  classical
  have hmemX : ∀ k ∈ X, σ k ∈ X := fun k hk => hXimg ▸ Finset.mem_image_of_mem σ hk
  have hXA : X \ (X \ A) = A := Finset.sdiff_sdiff_eq_self hAX
  have hcard : ((X \ A).image σ).card = (X \ A).card :=
    Finset.card_image_of_injective _ σ.injective
  have hBsub : (X \ A).image σ ⊆ X := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hmemX k (Finset.sdiff_subset hk)
  -- the image of the second part is not the second part again, since `A` is not preserved
  have hne : (X \ A).image σ ≠ X \ A := by
    intro heq
    refine himg (Finset.eq_of_subset_of_card_le (fun z hz => ?_)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm))
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hnot : σ k ∉ X \ A := by
      intro hcontra
      have himg' : σ k ∈ (X \ A).image σ := heq.symm ▸ hcontra
      obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp himg'
      exact (Finset.mem_sdiff.mp hk').2 (σ.injective hk'eq ▸ hk)
    have hmem := Finset.mem_sdiff.mpr ⟨hmemX k (hAX hk), hnot⟩
    rwa [hXA] at hmem
  -- so the two differ, and what the image gains lies in `A`, above everything it loses
  have hUV := Finset.card_sdiff_comm hcard
  have hUne : (((X \ A).image σ) \ (X \ A)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hsub => hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  have hUlt : ∀ u ∈ ((X \ A).image σ) \ (X \ A), ∀ v ∈ (X \ A) \ ((X \ A).image σ), f v < f u := by
    intro u hu v hv
    obtain ⟨huX, huB⟩ := Finset.mem_sdiff.mp hu
    refine hlt u ?_ v (Finset.mem_sdiff.mp hv).1
    have hmem := Finset.mem_sdiff.mpr ⟨hBsub huX, huB⟩
    rwa [hXA] at hmem
  have hlt' := sum_lt_sum_of_forall_lt f hUV.symm hUne hUlt
  -- the two sums agree on the common part, so the two differences compare them
  have hsd1 : (X \ A) \ ((X \ A) ∩ ((X \ A).image σ)) = (X \ A) \ ((X \ A).image σ) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsd2 : ((X \ A).image σ) \ ((X \ A) ∩ ((X \ A).image σ)) =
      ((X \ A).image σ) \ (X \ A) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have h1 : (∑ z ∈ (X \ A) \ ((X \ A).image σ), f z) +
      ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z = ∑ z ∈ X \ A, f z := by
    rw [← hsd1]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have h2 : (∑ z ∈ ((X \ A).image σ) \ (X \ A), f z) +
      ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z = ∑ z ∈ (X \ A).image σ, f z := by
    rw [← hsd2]
    exact Finset.sum_sdiff Finset.inter_subset_right
  calc ∑ z ∈ X \ A, f z
      = (∑ z ∈ (X \ A) \ ((X \ A).image σ), f z) +
        ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z := h1.symm
    _ < (∑ z ∈ ((X \ A).image σ) \ (X \ A), f z) +
        ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z := by gcongr
    _ = ∑ z ∈ (X \ A).image σ, f z := h2

end TauCeti
