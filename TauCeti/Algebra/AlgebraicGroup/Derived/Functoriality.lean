/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Functoriality of the derived subgroup

A homomorphism of affine group schemes carries commutators to commutators, and therefore
restricts to a homomorphism of their derived closed subgroup schemes. In coordinate Hopf
algebras, a morphism `f : H ⟶ K` sends the ideal defining the derived subgroup of `Spec H`
into the ideal defining the derived subgroup of `Spec K`. It consequently induces a morphism

```text
H / derivedDefiningIdeal H ⟶ K / derivedDefiningIdeal K.
```

This file proves the naturality of the commutator coordinate morphism, constructs the induced
quotient morphism, and packages its identity and composition laws as an endofunctor on
commutative Hopf algebras. Applying `Spec` reverses this map to the expected restriction between
derived subgroup schemes.

## Main declarations

* `TauCeti.HopfAlgebra.map_comp_commutatorAlgHom`: commutators commute with a Hopf-algebra
  morphism.
* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal_map_le`: the derived defining ideals are
  functorial.
* `TauCeti.CommHopfAlgCat.derivedMap`: the induced morphism on derived coordinate algebras.
* `TauCeti.CommHopfAlgCat.derivedFunctor`: the derived coordinate algebra as an endofunctor.
* `TauCeti.CommHopfAlgCat.derivedQuotientNatTrans`: the ambient quotient maps as a natural
  transformation to the derived-coordinate functor.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, especially Proposition 6.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.

This supplies the functoriality part of the derived-group target `G_der` in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement TensorProduct

namespace TauCeti

universe u v

namespace HopfAlgebra

variable {R : Type u} [CommSemiring R]
variable {H K : Type v} [CommSemiring H] [CommSemiring K]
variable [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K]

/-- The coordinate morphism of the commutator is natural under morphisms of commutative Hopf
algebras. This is the coordinate form of `f([g, h]) = [f(g), f(h)]`. -/
theorem map_comp_commutatorAlgHom (f : H →ₐc[R] K) :
    (Bialgebra.TensorProduct.map f f).toAlgHom.comp
        (commutatorAlgHom (R := R) (H := H)) =
      (commutatorAlgHom (R := R) (H := K)).comp f.toAlgHom := by
  apply AlgHom.ext
  intro x
  have hleft :
      AlgHom.mapValue (H := H) (Bialgebra.TensorProduct.map f f).toAlgHom
          (toConv (commutatorAlgHom (R := R) (H := H))) =
        AlgHom.mapDomain (A := K ⊗[R] K) f
          (toConv (commutatorAlgHom (R := R) (H := K))) := by
    have hinclLeft :
        (Bialgebra.TensorProduct.map f f).toAlgHom.comp
            (Bialgebra.TensorProduct.includeLeft
              (R := R) (H₁ := H) (H₂ := H)).toAlgHom =
          (Bialgebra.TensorProduct.includeLeft
            (R := R) (H₁ := K) (H₂ := K)).toAlgHom.comp f.toAlgHom := by
      simpa only [Bialgebra.TensorProduct.map_toAlgHom,
        Bialgebra.TensorProduct.includeLeft_toAlgHom] using
          Algebra.TensorProduct.map_comp_includeLeft f.toAlgHom f.toAlgHom
    have hinclRight :
        (Bialgebra.TensorProduct.map f f).toAlgHom.comp
            (Bialgebra.TensorProduct.includeRight
              (R := R) (H₁ := H) (H₂ := H)).toAlgHom =
          (Bialgebra.TensorProduct.includeRight
            (R := R) (H₁ := K) (H₂ := K)).toAlgHom.comp f.toAlgHom := by
      simpa only [Bialgebra.TensorProduct.map_toAlgHom,
        Bialgebra.TensorProduct.includeRight_toAlgHom] using
          Algebra.TensorProduct.map_comp_includeRight f.toAlgHom f.toAlgHom
    rw [toConv_commutatorAlgHom, toConv_commutatorAlgHom]
    apply WithConv.ofConv_injective
    simp only [map_mul, map_inv, AlgHom.mapValue_apply, AlgHom.mapDomain_apply]
    rw [hinclLeft, hinclRight]
  exact congrArg (fun g : WithConv (H →ₐ[R] K ⊗[R] K) ↦ g.ofConv x) hleft

end HopfAlgebra

namespace CommHopfAlgCat

section Semiring

variable {R : Type u} [CommSemiring R]
variable {H K : Type v} [CommSemiring H] [CommSemiring K]
variable [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K]

/-- A morphism of commutative Hopf algebras sends the derived defining ideal into the derived
defining ideal of its target. Contravariantly, a group-scheme homomorphism sends the source
derived subgroup into the target derived subgroup. -/
theorem derivedDefiningIdeal_map_le (f : H →ₐc[R] K) :
    (derivedDefiningIdeal (R := R) H).map f ≤ derivedDefiningIdeal (R := R) K := by
  rw [le_derivedDefiningIdeal_iff, HopfIdeal.map_toIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hzero : HopfAlgebra.commutatorAlgHom (R := R) (H := H) x = 0 :=
    RingHom.mem_ker.mp
      (derivedDefiningIdeal_toIdeal_le_ker (R := R) H ((HopfIdeal.mem_toIdeal).mpr hx))
  have hnatural := DFunLike.congr_fun (HopfAlgebra.map_comp_commutatorAlgHom f) x
  simpa only [AlgHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    BialgHom.coe_toAlgHom, map_zero] using
    hnatural.symm.trans (congrArg (Bialgebra.TensorProduct.map f f) hzero)

end Semiring

variable {R : Type u} [CommRing R]
variable {H K L : _root_.CommHopfAlgCat.{v} R}

/-- The coordinate morphism induced by a homomorphism on the coordinate algebras of the derived
subgroups. After applying `Spec`, this is the restriction of the original group-scheme
homomorphism to the derived subgroup schemes. -/
noncomputable def derivedMap (f : H ⟶ K) :
    quotient H (derivedDefiningIdeal (R := R) H) ⟶
      quotient K (derivedDefiningIdeal (R := R) K) :=
  liftQuotient (derivedDefiningIdeal (R := R) H)
    (f ≫ mkQuotient K (derivedDefiningIdeal (R := R) K)) <| by
      intro x hx
      rw [RingHom.mem_ker]
      have hmem : f.hom x ∈ derivedDefiningIdeal (R := R) K :=
        derivedDefiningIdeal_map_le f.hom (HopfIdeal.mem_map_of_mem f.hom hx)
      exact (mkQuotient_eq_zero_iff K (derivedDefiningIdeal (R := R) K) (f.hom x)).2 hmem

/-- On quotient classes, the induced derived-coordinate map applies the ambient morphism before
taking the target quotient class. -/
@[simp]
theorem derivedMap_mk (f : H ⟶ K) (x : H) :
    (derivedMap f).hom
        (Ideal.Quotient.mk (derivedDefiningIdeal (R := R) H).toIdeal x) =
      Ideal.Quotient.mkₐ R (derivedDefiningIdeal (R := R) K).toIdeal (f.hom x) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := R)]
  rw [derivedMap, liftQuotient_mk, _root_.CommHopfAlgCat.comp_apply, mkQuotient_apply]

/-- The induced map on derived coordinate algebras commutes with the ambient quotient maps. This
is the coordinate square expressing that the derived-subgroup map restricts the original map. -/
@[simp]
theorem mkQuotient_comp_derivedMap (f : H ⟶ K) :
    mkQuotient H (derivedDefiningIdeal (R := R) H) ≫ derivedMap f =
      f ≫ mkQuotient K (derivedDefiningIdeal (R := R) K) :=
  mkQuotient_comp_liftQuotient _ _ _

/-- The map induced on derived coordinate algebras by the identity is the identity. -/
@[simp]
theorem derivedMap_id (H : _root_.CommHopfAlgCat.{v} R) :
    derivedMap (𝟙 H) = 𝟙 (quotient H (derivedDefiningIdeal (R := R) H)) := by
  symm
  apply liftQuotient_unique
  simp

/-- Maps induced on derived coordinate algebras respect composition. -/
@[simp]
theorem derivedMap_comp (f : H ⟶ K) (g : K ⟶ L) :
    derivedMap (f ≫ g) = derivedMap f ≫ derivedMap g := by
  symm
  apply liftQuotient_unique
  rw [← Category.assoc, mkQuotient_comp_derivedMap, Category.assoc,
    mkQuotient_comp_derivedMap]
  rw [Category.assoc]

/-- Taking the coordinate algebra of the derived subgroup is an endofunctor on commutative Hopf
algebras. On affine group schemes, composition with the contravariant spectrum functor gives the
covariant derived-subgroup construction. -/
@[expose] noncomputable def derivedFunctor :
    _root_.CommHopfAlgCat.{v} R ⥤ _root_.CommHopfAlgCat.{v} R where
  obj H := quotient H (derivedDefiningIdeal (R := R) H)
  map := derivedMap
  map_id := derivedMap_id
  map_comp := derivedMap_comp

/-- The derived-coordinate functor acts on objects by quotienting by the derived defining ideal. -/
@[simp]
theorem derivedFunctor_obj (H : _root_.CommHopfAlgCat.{v} R) :
    (derivedFunctor (R := R)).obj H = quotient H (derivedDefiningIdeal (R := R) H) :=
  (rfl)

/-- The derived-coordinate functor acts on morphisms by the induced quotient morphism. -/
@[simp]
theorem derivedFunctor_map (f : H ⟶ K) :
    (derivedFunctor (R := R)).map f = derivedMap f :=
  (rfl)

/-- The quotient morphisms from an ambient coordinate Hopf algebra to its derived-subgroup
coordinate algebra form a natural transformation. After applying the contravariant spectrum
functor, this is the natural closed immersion of the derived subgroup into the ambient group. -/
noncomputable def derivedQuotientNatTrans :
    𝟭 (_root_.CommHopfAlgCat.{v} R) ⟶ derivedFunctor (R := R) where
  app H := mkQuotient H (derivedDefiningIdeal (R := R) H)
  naturality {H K} f := by
    -- The naturality field retains the identity- and derived-functor object wrappers; expose
    -- their quotient-coordinate shape so the established commuting square applies.
    change f ≫ mkQuotient K (derivedDefiningIdeal (R := R) K) =
      mkQuotient H (derivedDefiningIdeal (R := R) H) ≫ derivedMap f
    exact (mkQuotient_comp_derivedMap f).symm

/-- The component of the derived quotient natural transformation is the coordinate quotient
morphism defining the derived closed subgroup. -/
@[simp]
theorem derivedQuotientNatTrans_app (H : _root_.CommHopfAlgCat.{v} R) :
    (derivedQuotientNatTrans (R := R)).app H =
      mkQuotient H (derivedDefiningIdeal (R := R) H) :=
  (rfl)

end CommHopfAlgCat

end TauCeti
