/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Inv
public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# Right-coset collisions and the handedness of Shimura's multiplicity

`DoubleCoset.multiplicity Γ₁ Γ₂ Γ₃ g h d` counts the pairs of representatives of the *left*-coset
decompositions `Γ₁ g Γ₂ = ⊔ᵢ σᵢ g Γ₂` and `Γ₂ h Γ₃ = ⊔ⱼ τⱼ h Γ₃` whose product lies in the left
coset `d Γ₃`. A slash sum runs instead over the *right*-coset decomposition
`Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ (δ τᵥ⁻¹)`, so composing two slash sums produces a count of pairs whose product
lies in a *right* coset `Γ₁ d`. This file identifies the two counts.

Inversion is an anti-automorphism carrying `Γ₁ δ Γ₂` to `Γ₂ δ⁻¹ Γ₁` and right cosets to left
cosets, and it carries the product `(δ₁ τᵥ⁻¹) (δ₂ σ_w⁻¹)` of two right-coset representatives to
`(σ_w δ₂⁻¹) (τᵥ δ₁⁻¹)`, which is exactly the product `multiplicity` counts — with the two factors
*exchanged*. So

`#{(v, w) | (δ₁ τᵥ⁻¹) (δ₂ σ_w⁻¹) ∈ Γ₁ d} = m_{Γ₃ Γ₂ Γ₁}(δ₂⁻¹, δ₁⁻¹; d⁻¹)`.

The exchange of factors is not an artefact of the proof: it is the same order reversal that makes
the action of a Hecke ring on modular forms an *anti*-homomorphism.

Nothing here mentions a slash action, a weight or `GL (Fin 2) ℚ`: which right cosets the products
of representatives meet is a question about the group alone, so it is answered alongside the rest
of the multiplicity API rather than in a file about modular forms.

## Main results

* `DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`: the right-coset collision count of a
  pair of right-coset decompositions is Shimura's multiplicity, with the factors exchanged and
  the arguments inverted.
* `DoubleCoset.card_pairs_mem_rightCoset_congr`: that count depends on the target only through
  its double coset — each right coset of a fixed double coset is hit the same number of times.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1 (the multiplicity) and §3.4 (the slash sum).
-/

public section

open Subgroup MulOpposite

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- **The right-coset collision count is Shimura's multiplicity.**

`δ₁ τᵥ⁻¹` runs over the representatives of the right cosets of `Γ₁ δ₁ Γ₂` and `δ₂ σ_w⁻¹` over
those of `Γ₂ δ₂ Γ₃`; the number of pairs whose product lands in the right coset `Γ₁ d` is the
multiplicity of `d⁻¹` for the *reversed* triple.

Both the exchange of the two factors and the inversion of all three arguments come from the same
source: inversion is an anti-automorphism, and it is what turns the right-coset index a slash sum
uses into the left-coset index `multiplicity` is defined with. -/
theorem card_pairs_mem_rightCoset_eq_multiplicity (Γ₁ Γ₂ Γ₃ : Subgroup G) (δ₁ δ₂ d : G) :
    Nat.card {p : DecompQuotient Γ₂ Γ₁ δ₁⁻¹ × DecompQuotient Γ₃ Γ₂ δ₂⁻¹ |
        δ₁ * (p.1.out : G)⁻¹ * (δ₂ * (p.2.out : G)⁻¹) ∈ op d • (Γ₁ : Set G)} =
      multiplicity Γ₃ Γ₂ Γ₁ δ₂⁻¹ δ₁⁻¹ d⁻¹ := by
  rw [multiplicity_def]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodComm _ _) fun p ↦ ?_)
  -- The two predicates say the same thing about `p`: lying in the right coset `Γ₁ d` is, after
  -- inverting, lying in the left coset `d⁻¹ Γ₁`, and `Equiv.prodComm` supplies the exchange of
  -- factors that the same inversion has already performed on the product.
  simp only [mul_assoc, mem_rightCoset_iff, SetLike.mem_coe, Set.mem_ofPred_eq, QuotientGroup.eq,
    mul_inv_rev, inv_inv, Equiv.prodComm_apply, Prod.snd_swap, Prod.fst_swap]

/-- **Each right coset of a fixed double coset is hit the same number of times.** The right-coset
collision count of `card_pairs_mem_rightCoset_eq_multiplicity` depends on the target `d` only
through the double coset `Γ₁ d Γ₃`.

This is the uniformity that turns the composite of two slash sums into a multiplicity-weighted
sum of slash sums: within one double coset every right coset contributes the same count, so that
count factors out. -/
theorem card_pairs_mem_rightCoset_congr (Γ₁ Γ₂ Γ₃ : Subgroup G) (δ₁ δ₂ : G) {d d' : G}
    (hd : d' ∈ doubleCoset d (Γ₁ : Set G) Γ₃) :
    Nat.card {p : DecompQuotient Γ₂ Γ₁ δ₁⁻¹ × DecompQuotient Γ₃ Γ₂ δ₂⁻¹ |
        δ₁ * (p.1.out : G)⁻¹ * (δ₂ * (p.2.out : G)⁻¹) ∈ op d' • (Γ₁ : Set G)} =
      Nat.card {p : DecompQuotient Γ₂ Γ₁ δ₁⁻¹ × DecompQuotient Γ₃ Γ₂ δ₂⁻¹ |
        δ₁ * (p.1.out : G)⁻¹ * (δ₂ * (p.2.out : G)⁻¹) ∈ op d • (Γ₁ : Set G)} := by
  rw [card_pairs_mem_rightCoset_eq_multiplicity, card_pairs_mem_rightCoset_eq_multiplicity]
  exact multiplicity_doubleCoset_congr _ _ (inv_mem_doubleCoset_inv_iff.mpr hd)

end DoubleCoset
