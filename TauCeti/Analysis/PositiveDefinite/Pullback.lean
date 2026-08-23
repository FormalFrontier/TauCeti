/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic

/-!
# Pullbacks of positive-definite functions

This file adds the pullback API for `TauCeti.IsPositiveDefinite`, the positive-definite
function predicate on an involutive additive monoid. A star-preserving additive homomorphism
`φ : N → M` pulls a positive-definite function `F : M → ℂ` back to the positive-definite
function `F ∘ φ : N → ℂ`; if `φ` is surjective, positive-definiteness can also be descended
from the pullback.

This is part of the `OneParameterSemigroups` roadmap, Part C, whose positive-definite-function
API asks for pullbacks alongside the PD-function/PD-kernel correspondence and the closure
properties. The proofs are the finite-family reindexing argument: apply the defining
nonnegativity of `F` to the image family under `φ`, using preservation of addition and star to
identify the Gram entries.

## Main declarations

* `TauCeti.IsPositiveDefinite.comp`: positive-definiteness is preserved by precomposition with
  any star-preserving additive homomorphism, stated using Mathlib's homomorphism classes.
* `TauCeti.IsPositiveDefinite.comp_addMonoidHom`: the same statement for an explicit
  `AddMonoidHom` plus a star-preservation hypothesis.
* `TauCeti.IsPositiveDefinite.comp_smul`: rescaling the argument by a scalar preserves
  positive-definiteness when the involution is negation.
* `TauCeti.IsPositiveDefinite.of_comp_surjective` and
  `TauCeti.IsPositiveDefinite.comp_iff_of_surjective`: descent and equivalence for surjective
  star-preserving additive homomorphisms.
* `TauCeti.IsPositiveDefinite.comp_addEquiv_iff`: invariance under a star-preserving additive
  equivalence.
* `TauCeti.IsPositiveDefinite.comp_fst`, `TauCeti.IsPositiveDefinite.comp_snd`, and
  `TauCeti.IsPositiveDefinite.mul_comp_fst_snd`: the projection pullbacks and their pointwise
  product on a product monoid.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100,
  1984), Chapter 3.
-/

public section

namespace TauCeti

open scoped ComplexOrder

namespace IsPositiveDefinite

variable {M N : Type*} [AddMonoid M] [StarAddMonoid M] [AddMonoid N] [StarAddMonoid N]
  {F : M → ℂ}

/-- Positive-definiteness is preserved by pullback along a star-preserving additive
homomorphism. This is stated for Mathlib's homomorphism classes so it applies to bundled
additive homomorphisms, star algebra homomorphisms, and similar maps. -/
theorem comp {Φ : Type*} [FunLike Φ N M] [AddHomClass Φ N M] [StarHomClass Φ N M]
    (hF : IsPositiveDefinite F) (φ : Φ) : IsPositiveDefinite (fun x : N => F (φ x)) := by
  intro n c v
  simpa [map_add, map_star] using hF n c (fun i => φ (v i))

/-- The explicit `AddMonoidHom` form of pullback: a star-preserving additive homomorphism
pulls back positive-definite functions to positive-definite functions. -/
theorem comp_addMonoidHom (hF : IsPositiveDefinite F) (φ : N →+ M)
    (hstar : ∀ x : N, φ (star x) = star (φ x)) :
    IsPositiveDefinite (fun x : N => F (φ x)) := by
  intro n c v
  simpa [map_add, hstar] using hF n c (fun i => φ (v i))

/-- Rescaling the argument by a scalar preserves positive-definiteness, whenever the involution
on the domain is negation: if `F` is positive definite then so is `x ↦ F (r • x)`. -/
theorem comp_smul {G : Type*} [AddGroup G] [StarAddMonoid G] {R : Type*} [DistribSMul R G]
    {F : G → ℂ} (hF : IsPositiveDefinite F) (hstar : ∀ x : G, star x = -x) (r : R) :
    IsPositiveDefinite fun x : G => F (r • x) :=
  hF.comp_addMonoidHom (DistribSMul.toAddMonoidHom G r) fun x => by simp [hstar, smul_neg]

/-- Positive-definiteness descends along a surjective star-preserving additive homomorphism:
if `F ∘ φ` is positive definite and every point of the codomain is in the range of `φ`, then
`F` is positive definite. -/
theorem of_comp_surjective {Φ : Type*} [FunLike Φ N M] [AddHomClass Φ N M]
    (φ : Φ) (hstar : ∀ x : N, φ (star x) = star (φ x))
    (hsurj : Function.Surjective φ) (hcomp : IsPositiveDefinite (fun x : N => F (φ x))) :
    IsPositiveDefinite F := by
  classical
  intro n c v
  choose w hw using fun i : Fin n => hsurj (v i)
  have h := hcomp n c w
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [map_add, hstar, hw]

/-- Along a surjective star-preserving additive homomorphism, a function is positive definite
if and only if its pullback is positive definite. -/
theorem comp_iff_of_surjective {Φ : Type*} [FunLike Φ N M] [AddHomClass Φ N M]
    [StarHomClass Φ N M] (φ : Φ) (hsurj : Function.Surjective φ) :
    IsPositiveDefinite (fun x : N => F (φ x)) ↔ IsPositiveDefinite F :=
  ⟨of_comp_surjective φ (map_star φ) hsurj, fun hF => hF.comp φ⟩

/-- The explicit `AddMonoidHom` form of the pullback equivalence for surjective maps. -/
theorem comp_addMonoidHom_iff_of_surjective (φ : N →+ M)
    (hstar : ∀ x : N, φ (star x) = star (φ x)) (hsurj : Function.Surjective φ) :
    IsPositiveDefinite (fun x : N => F (φ x)) ↔ IsPositiveDefinite F :=
  ⟨of_comp_surjective φ hstar hsurj, fun hF => hF.comp_addMonoidHom φ hstar⟩

/-- Positive-definiteness is invariant under precomposition with a star-preserving additive
equivalence. -/
theorem comp_addEquiv_iff (e : N ≃+ M) (hstar : ∀ x : N, e (star x) = star (e x)) :
    IsPositiveDefinite (fun x : N => F (e x)) ↔ IsPositiveDefinite F :=
  comp_addMonoidHom_iff_of_surjective e.toAddMonoidHom hstar e.surjective

section Prod

variable {G : N → ℂ}

/-- Pulling back a positive-definite function along the first projection from a product
preserves positive-definiteness. -/
theorem comp_fst (hF : IsPositiveDefinite F) :
    IsPositiveDefinite (fun x : M × N => F x.1) :=
  hF.comp_addMonoidHom (AddMonoidHom.fst M N) fun x => Prod.fst_star x

/-- Pulling back a positive-definite function along the second projection from a product
preserves positive-definiteness. -/
theorem comp_snd (hG : IsPositiveDefinite G) :
    IsPositiveDefinite (fun x : M × N => G x.2) :=
  hG.comp_addMonoidHom (AddMonoidHom.snd M N) fun x => Prod.snd_star x

/-- The product of two positive-definite functions, pulled back from the two factors of a
product monoid, is positive definite. This is the basic product-domain construction obtained by
combining pullback along projections with the Schur product closure. -/
theorem mul_comp_fst_snd (hF : IsPositiveDefinite F) (hG : IsPositiveDefinite G) :
    IsPositiveDefinite (fun x : M × N => F x.1 * G x.2) :=
  (hF.comp_fst).mul hG.comp_snd

end Prod

end IsPositiveDefinite

end TauCeti
