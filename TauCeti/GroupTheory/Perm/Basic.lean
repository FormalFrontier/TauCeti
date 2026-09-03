/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Elementary facts about permutations

This file records general-purpose facts about permutations: an identity between transpositions,
a characterization of permutations with a unique fixed point, a permutation transported along an
injection, and the combination of two permutations transported along injections with disjoint
ranges.
-/

public section

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation moves all but one point exactly when it has a unique fixed point. -/
theorem card_support_add_one_eq_card_iff_existsUnique_fixedPoint (σ : Equiv.Perm α) :
    σ.support.card + 1 = Fintype.card α ↔ ∃! x : α, σ x = x := by
  have hfixed : (∃! x : α, x ∈ σ.supportᶜ) ↔ ∃! x : α, σ x = x := by
    simp only [Finset.mem_compl, Equiv.Perm.notMem_support]
  rw [← hfixed, ← Finset.card_eq_one_iff_existsUnique, Finset.card_compl]
  omega

/-- Whenever `a` and `c` are both distinct from `b`, the transpositions `(a b)` and `(b c)`
satisfy the braid relation. The two points `a` and `c` need not be distinct: for `a = c` both
sides are `(a b)`. -/
theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hcb : c ≠ b) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  rcases eq_or_ne a c with rfl | hac
  · rw [Equiv.swap_comm b a]
  · calc Equiv.swap a b * Equiv.swap b c * Equiv.swap a b
        = Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
          rw [Equiv.swap_comm a b, Equiv.swap_comm b c]
      _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hcb (Ne.symm hac)
      _ = Equiv.swap c a := Equiv.swap_comm a c
      _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
          (Equiv.swap_mul_swap_mul_swap hab hac).symm

/-- **A permutation along an injection extends to a permutation of the ambient type.** Given an
injection `e : α → γ`, every permutation `σ` of `α` is realized along `e` by some
`ρ : Equiv.Perm γ`. This is `Equiv.Perm.viaEmbedding` stated in terms of the underlying function
of the injection, which is the form a consumer reindexing along `e` needs. -/
theorem exists_perm_apply_eq {α γ : Type*} {e : α → γ} (he : Function.Injective e)
    (σ : Equiv.Perm α) : ∃ ρ : Equiv.Perm γ, ∀ a, ρ (e a) = e (σ a) :=
  ⟨σ.viaEmbedding ⟨e, he⟩, fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a⟩

/-- **Two permutations along disjoint injections extend to one permutation of the ambient type.**
Given injections `e : α → γ` and `f : β → γ` with disjoint ranges, every pair of permutations
`σ` of `α` and `τ` of `β` is realized by a single `ρ : Equiv.Perm γ` which acts as `σ` along `e`
and as `τ` along `f`. -/
theorem exists_perm_apply_eq_of_disjoint_range {α β γ : Type*} {e : α → γ} {f : β → γ}
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    ∃ ρ : Equiv.Perm γ, (∀ a, ρ (e a) = e (σ a)) ∧ ∀ b, ρ (f b) = f (τ b) := by
  -- `Function.Embedding.coeFn_mk` is what carries a statement about the bundled embedding
  -- `⟨e, he⟩` over to the function `e` it is built from.
  have hrange_e : Set.range (⟨e, he⟩ : α ↪ γ) = Set.range e := by
    rw [Function.Embedding.coeFn_mk]
  have hrange_f : Set.range (⟨f, hf⟩ : β ↪ γ) = Set.range f := by
    rw [Function.Embedding.coeFn_mk]
  have hone : ∀ a, σ.viaEmbedding ⟨e, he⟩ (e a) = e (σ a) :=
    fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a
  have htwo : ∀ b, τ.viaEmbedding ⟨f, hf⟩ (f b) = f (τ b) :=
    fun b => Equiv.Perm.viaEmbedding_apply (ι := ⟨f, hf⟩) τ b
  refine ⟨σ.viaEmbedding ⟨e, he⟩ * τ.viaEmbedding ⟨f, hf⟩, fun a => ?_, fun b => ?_⟩
  · have hmem : e a ∉ Set.range (⟨f, hf⟩ : β ↪ γ) :=
      hrange_f ▸ Set.disjoint_left.mp hd ⟨a, rfl⟩
    rw [Equiv.Perm.mul_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨f, hf⟩) _ _ hmem, hone]
  · have hmem : f (τ b) ∉ Set.range (⟨e, he⟩ : α ↪ γ) :=
      hrange_e ▸ Set.disjoint_right.mp hd ⟨τ b, rfl⟩
    rw [Equiv.Perm.mul_apply, htwo,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨e, he⟩) _ _ hmem]

end TauCeti
