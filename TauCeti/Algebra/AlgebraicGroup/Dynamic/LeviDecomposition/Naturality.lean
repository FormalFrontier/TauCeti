/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Basic

/-!
# Naturality of the dynamic Levi decomposition

The dynamic Levi decomposition identifies the parabolic subgroup attached to a cocharacter with
the semidirect product of its unipotent and Levi subgroups. This file proves that the
identification commutes with extension of the commutative value algebra.

For a cocharacter `l`, extension along `A ⟶ B` preserves the conjugation action of `Z(l)` on
`U(l)`. Hence the maps on the two factors combine to a homomorphism between their semidirect
products. These homomorphisms form a group-valued functor, and the pointwise Levi decompositions
assemble into a natural isomorphism

```text
U(l)(-) ⋊ Z(l)(-) ≅ P(l)(-).
```

This is the functorial bridge between the pointwise decomposition and the represented weight
parabolic, Levi, and unipotent subgroups of `GLₙ`.

## Main declarations

* `TauCeti.Cocharacter.leviSemidirectMap`: extension of the value algebra on the semidirect
  product.
* `TauCeti.Cocharacter.leviSemidirectFunctor`: the dynamic semidirect product as a group-valued
  functor.
* `TauCeti.Cocharacter.leviDecompositionNatIso`: the dynamic Levi decomposition as a natural
  isomorphism of group-valued functors.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic approach to parabolic subgroups and Levi decomposition in Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Cocharacter

universe u v w

noncomputable section

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable (l : H →ₐc[R] LaurentPolynomial R)

/-- Extension of the value algebra commutes with the Levi-valued dynamic limit. -/
@[simp]
theorem mapLevi_limitToLevi {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : parabolic A l) :
    mapLevi l φ (limitToLevi A l g) = limitToLevi B l (mapParabolic l φ g) := by
  apply Subtype.ext
  rw [coe_mapLevi_apply, coe_limitToLevi_apply, coe_limitToLevi_apply]
  rw [mapValue_limit φ.hom g]
  congr 1
  apply Subtype.ext
  exact (coe_mapParabolic_apply l φ g).symm

/-- Extension of the value algebra commutes with inclusion of the dynamic unipotent subgroup
into the dynamic parabolic. -/
@[simp]
theorem mapParabolic_unipotentToParabolic {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : unipotent A l) :
    mapParabolic l φ (unipotentToParabolic A l g) =
      unipotentToParabolic B l (mapUnipotent l φ g) := by
  apply Subtype.ext
  rw [coe_mapParabolic_apply, coe_unipotentToParabolic_apply,
    coe_unipotentToParabolic_apply, coe_mapUnipotent_apply]

/-- Extension of the value algebra commutes with inclusion of the dynamic Levi subgroup into the
dynamic parabolic. -/
@[simp]
theorem mapParabolic_leviToParabolic {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : levi A l) :
    mapParabolic l φ (leviToParabolic A l g) = leviToParabolic B l (mapLevi l φ g) := by
  apply Subtype.ext
  rw [coe_mapParabolic_apply, coe_leviToParabolic_apply,
    coe_leviToParabolic_apply, coe_mapLevi_apply]

/-- Extension of the value algebra preserves the conjugation action of the dynamic Levi subgroup
on the dynamic unipotent subgroup. -/
@[simp]
theorem mapUnipotent_leviConjugation {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (z : levi A l) (g : unipotent A l) :
    mapUnipotent l φ (leviConjugation A l z g) =
      leviConjugation B l (mapLevi l φ z) (mapUnipotent l φ g) := by
  apply Subtype.ext
  simp only [coe_mapUnipotent_apply, coe_leviConjugation_apply,
    coe_mapLevi_apply, map_mul, Subgroup.coe_inv, map_inv]

/-- Extension of the value algebra on the semidirect product in the dynamic Levi decomposition. -/
noncomputable def leviSemidirectMap {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (unipotent A l) ⋊[leviConjugation A l] (levi A l) →*
      (unipotent B l) ⋊[leviConjugation B l] (levi B l) :=
  SemidirectProduct.map (mapUnipotent l φ) (mapLevi l φ) fun z ↦ by
    apply MonoidHom.ext
    intro g
    exact mapUnipotent_leviConjugation l φ z g

/-- Extension on the dynamic Levi semidirect product acts coordinatewise. -/
@[simp]
theorem leviSemidirectMap_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : (unipotent A l) ⋊[leviConjugation A l] (levi A l)) :
    leviSemidirectMap l φ g =
      ⟨mapUnipotent l φ g.left, mapLevi l φ g.right⟩ := by
  rfl

/-- Extension of the value algebra commutes with the dynamic Levi decomposition equivalence. -/
theorem mapParabolic_leviDecompositionMulEquiv_apply
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : (unipotent A l) ⋊[leviConjugation A l] (levi A l)) :
    mapParabolic l φ (leviDecompositionMulEquiv A l g) =
      leviDecompositionMulEquiv B l (leviSemidirectMap l φ g) := by
  simp

private theorem leviSemidirectMap_id (A : CommAlgCat.{w} R) :
    leviSemidirectMap l (𝟙 A) = MonoidHom.id _ := by
  ext g <;> simp [leviSemidirectMap]

private theorem leviSemidirectMap_comp {A B C : CommAlgCat.{w} R}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    leviSemidirectMap l (φ ≫ ψ) =
      (leviSemidirectMap l ψ).comp (leviSemidirectMap l φ) := by
  ext g <;> simp [leviSemidirectMap]

/-- The semidirect product `U(l)(A) ⋊ Z(l)(A)` in the dynamic Levi decomposition, functorial in
the commutative value algebra `A`. -/
-- The object carrier must unfold when constructing the natural decomposition isomorphism.
@[expose] noncomputable def leviSemidirectFunctor :
    Functor (CommAlgCat.{w} R) GrpCat.{max v w} where
  obj A := GrpCat.of ((unipotent A l) ⋊[leviConjugation A l] (levi A l))
  map φ := GrpCat.ofHom (leviSemidirectMap l φ)
  map_id A := by rw [leviSemidirectMap_id]; rfl
  map_comp φ ψ := by rw [leviSemidirectMap_comp]; rfl

/-- The dynamic Levi semidirect-product functor maps a homomorphism by extension on its unipotent
and Levi coordinates. -/
@[simp]
theorem leviSemidirectFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (leviSemidirectFunctor l).map φ = GrpCat.ofHom (leviSemidirectMap l φ) :=
  rfl

/-- **The functorial dynamic Levi decomposition.** The semidirect product of the dynamic
unipotent and Levi subgroup functors is naturally isomorphic to the dynamic parabolic functor. -/
noncomputable def leviDecompositionNatIso :
    leviSemidirectFunctor l ≅ parabolicFunctor l :=
  NatIso.ofComponents (fun A ↦ (leviDecompositionMulEquiv A l).toGrpIso) fun {A B} φ ↦ by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact (mapParabolic_leviDecompositionMulEquiv_apply l φ g).symm

/-- The forward component of the functorial dynamic Levi decomposition is the pointwise
semidirect-product equivalence. -/
@[simp]
theorem leviDecompositionNatIso_hom_app_apply (A : CommAlgCat.{w} R)
    (g : (unipotent A l) ⋊[leviConjugation A l] (levi A l)) :
    (leviDecompositionNatIso l).hom.app A g = leviDecompositionMulEquiv A l g :=
  by unfold leviDecompositionNatIso; rfl

/-- The inverse component of the functorial dynamic Levi decomposition is the inverse pointwise
semidirect-product equivalence. -/
@[simp]
theorem leviDecompositionNatIso_inv_app_apply (A : CommAlgCat.{w} R)
    (g : parabolic A l) :
    (leviDecompositionNatIso l).inv.app A g = (leviDecompositionMulEquiv A l).symm g :=
  by unfold leviDecompositionNatIso; rfl

end

end TauCeti.Cocharacter
