/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction

/-!
# Restriction maps as morphisms of complete separated rings

`LocalizationTopology.Restriction` builds the restriction map `A⟨T/s⟩ → A⟨T''/s''⟩` of a
refinement as a continuous ring homomorphism, and `LocalizationTopology.CompleteSeparated.Basic`
exhibits `A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat`. This module joins the two:
the restriction map becomes a *morphism* of that category, and the identity and composition laws
of the ring homomorphisms become the identity and composition laws of the morphisms.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.restrictionObjHom` : the restriction map of a refinement, as a
  morphism `completionLocObj … ⟶ completionLocObj …`.

## Main results

* `TauCeti.Huber.PairOfDefinition.restrictionObjHom_congr` : the morphism does not depend on the
  cofactor witnessing the refinement.
* `TauCeti.Huber.PairOfDefinition.restrictionObjHom_self` : a presentation refines itself and
  gives the identity morphism.
* `TauCeti.Huber.PairOfDefinition.restrictionObjHom_comp_restrictionObjHom` : refinements
  compose, and the morphism of the composite is the composite of the morphisms.

## Why the cofactor drops out

`restrictionRingHom` is indexed by a cofactor `r` with `s'' = s * r`, and a refinement can be
witnessed by more than one. `restrictionObjHom_congr` says the morphism is nonetheless a function
of the two presentations alone: the underlying ring homomorphism is characterised by continuity
and compatibility with the structure maps from `A` (`eq_restrictionRingHom`), and neither mentions
`r`. That is what makes the assignment a diagram over a *preorder* of presentations — the
refinement relation, with the cofactor existentially quantified — rather than over a category
whose morphisms carry data, and so what lets `𝒪_X` be formed as a limit.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2, for the structure
  presheaf and its restriction maps.
-/

namespace TauCeti.Huber

open CategoryTheory TauCeti.TopCommRingCat

public section

universe u v

variable {A : Type v} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

variable [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type u)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (T'' : Finset A) (s'' : A) (S'' : Type u) [CommRing S''] [Algebra A S'']
  [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P T'' s'' S'') (r : A)
  (hs'' : s'' = s * r) (hT : ∀ t ∈ T, t * r ∈ T'')

/-! ### The restriction morphism -/

include r hs'' hT in
/-- **The restriction map of a refinement, as a morphism of `CompleteSeparatedTopCommRingCat`.**
The cofactor `r` and the two refinement conditions determine the morphism but do not appear in its
type; `restrictionObjHom_congr` shows they do not affect it either. -/
noncomputable def restrictionObjHom :
    completionLocObj P T s S hden ⟶ completionLocObj P T'' s'' S'' hden'' :=
  completionLocObjHom P T s S hden T'' s'' S'' hden''
    (restrictionRingHom P T s S hden T'' s'' S'' hden'' r hs'' hT)
    (continuous_restrictionRingHom P T s S hden T'' s'' S'' hden'' r hs'' hT)

/-- **The morphism does not depend on the cofactor.** Two cofactors witnessing the same refinement
give the same morphism, because the underlying ring homomorphism is determined by continuity and
compatibility with the structure maps from `A`. -/
theorem restrictionObjHom_congr (r₁ r₂ : A) (hs₁ : s'' = s * r₁) (hT₁ : ∀ t ∈ T, t * r₁ ∈ T'')
    (hs₂ : s'' = s * r₂) (hT₂ : ∀ t ∈ T, t * r₂ ∈ T'') :
    restrictionObjHom P T s S hden T'' s'' S'' hden'' r₁ hs₁ hT₁ =
      restrictionObjHom P T s S hden T'' s'' S'' hden'' r₂ hs₂ hT₂ := by
  have h : restrictionRingHom P T s S hden T'' s'' S'' hden'' r₁ hs₁ hT₁ =
      restrictionRingHom P T s S hden T'' s'' S'' hden'' r₂ hs₂ hT₂ :=
    eq_restrictionRingHom P T s S hden T'' s'' S'' hden'' r₂ hs₂ hT₂ _
      (continuous_restrictionRingHom P T s S hden T'' s'' S'' hden'' r₁ hs₁ hT₁)
      (restrictionRingHom_comp_toCompletionLoc P T s S hden T'' s'' S'' hden'' r₁ hs₁ hT₁)
  -- after unfolding, the two sides differ only in the underlying ring homomorphism, and `congr`
  -- discharges that subgoal from `h`
  unfold restrictionObjHom
  congr 1

/-- **The identity law.** A presentation refines itself with cofactor `1`, and the morphism that
gives is the identity of `completionLocObj`. -/
@[simp]
theorem restrictionObjHom_self :
    restrictionObjHom P T s S hden T s S hden 1 (mul_one s).symm (fun t ht ↦ by rwa [mul_one]) =
      𝟙 (completionLocObj P T s S hden) :=
  completionLocObjHom_eq_id P T s S hden _ _
    (restrictionRingHom_comp_toCompletionLoc P T s S hden T s S hden 1 (mul_one s).symm
      (fun t ht ↦ by rwa [mul_one]))

/-- **The composition law.** A refinement with cofactor `r` followed by one with cofactor `r₂` is a
refinement with cofactor `r * r₂`, and its morphism is the composite. With `restrictionObjHom_self`
this is the functoriality of the assignment. -/
@[simp]
theorem restrictionObjHom_comp_restrictionObjHom (T''' : Finset A) (s''' : A) (S''' : Type u)
    [CommRing S'''] [Algebra A S'''] [IsLocalization.Away s''' S''']
    (hden''' : HasDenominatorPower P T''' s''' S''') (r₂ : A) (hs''' : s''' = s'' * r₂)
    (hT₂ : ∀ t ∈ T'', t * r₂ ∈ T''') :
    restrictionObjHom P T s S hden T'' s'' S'' hden'' r hs'' hT ≫
        restrictionObjHom P T'' s'' S'' hden'' T''' s''' S''' hden''' r₂ hs''' hT₂ =
      restrictionObjHom P T s S hden T''' s''' S''' hden''' (r * r₂)
        (by rw [hs''', hs'', mul_assoc]) (fun t ht ↦ by rw [← mul_assoc]; exact hT₂ _ (hT t ht)) :=
  (completionLocObjHom_eq_comp P T s S hden T'' s'' S'' hden'' T''' s''' S''' hden''' _ _ _ _ _ _
    (restrictionRingHom_comp_toCompletionLoc P T s S hden T'' s'' S'' hden'' r hs'' hT)
    (restrictionRingHom_comp_toCompletionLoc P T'' s'' S'' hden'' T''' s''' S''' hden''' r₂ hs'''
      hT₂)
    (restrictionRingHom_comp_toCompletionLoc P T s S hden T''' s''' S''' hden''' (r * r₂) _ _)).symm

end PairOfDefinition

end

end TauCeti.Huber
