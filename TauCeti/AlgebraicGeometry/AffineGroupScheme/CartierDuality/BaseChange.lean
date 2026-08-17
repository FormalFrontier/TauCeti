/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.FiniteDual.CartierDuality.BaseChange
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree

/-!
# Cartier duality commutes with base change

Pullback along `Spec S ⟶ Spec R` preserves finite local freeness and commutativity, so it acts
on the category where Cartier duality lives, and it commutes with Cartier duality: the Cartier
dual of a base-changed group scheme is the base change of the Cartier dual.

Everything is transported from the coordinate Hopf algebras, where the corresponding statement is
`TauCeti.FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeDualIso`, itself a repackaging of
`TauCeti.ConvolutionDual.baseChangeBialgEquiv`.

## Main declarations

* `TauCeti.finiteLocallyFreeCommAffineGroupSchemeProperty_baseChange`: pullback preserves finite
  local freeness and commutativity.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.baseChangeFunctor`: pullback of finite
  locally free commutative affine group schemes along `Spec S ⟶ Spec R`.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.baseChangeHopfSpecNatIso`: base change of
  a Hopf spectrum is the Hopf spectrum of the scalar-extended coordinate Hopf algebra.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.coordHopfAlgebraBaseChangeNatIso`: the
  coordinate Hopf algebra of a base change is the scalar extension of the coordinate Hopf
  algebra.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualBaseChangeNatIso` and its
  objectwise form `cartierDualBaseChangeIso`: Cartier duality commutes with base change.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This advances Layer 4, "Cartier duality", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

open finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

open FiniteLocallyFreeCommAffineGroupSchemeCat in
/-- Pullback along `Spec S ⟶ Spec R` preserves finite local freeness and commutativity.

The proof compares the group scheme with the Hopf spectrum of its coordinate Hopf algebra, where
base change is scalar extension. -/
theorem finiteLocallyFreeCommAffineGroupSchemeProperty_baseChange
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of S)
      ((AffineGroupSchemeCat.baseChangeFunctor
        (CommRingCat.ofHom (algebraMap R S))).obj
          ((finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.obj G)) := by
  have hbase :
      finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of S)
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of S)).functor.obj
          (op (CommHopfAlgCat.baseChange (K := S)
            ((finiteLocallyFreeBicommutativeHopfAlgProperty R).ι.obj
              (coordHopfAlgebra R G))))) := by
    refine (ObjectProperty.prop_inverseImage_iff _
      (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of S)).functor _).mp ?_
    rw [finiteLocallyFreeCommAffineGroupSchemeProperty_inverseImage S]
    exact finiteLocallyFreeBicommutativeHopfAlgProperty_baseChange R S (coordHopfAlgebra R G)
  refine (finiteLocallyFreeCommAffineGroupSchemeProperty
    (CommRingCat.of S)).prop_of_iso ?_ hbase
  refine (AffineGroupSchemeCat.hopfSpecBaseChangeIso (R := R) (S := S)
      ((finiteLocallyFreeBicommutativeHopfAlgProperty R).ι.obj (coordHopfAlgebra R G))).symm ≪≫
    (AffineGroupSchemeCat.baseChangeFunctor
      (CommRingCat.ofHom (algebraMap R S))).mapIso ?_
  exact ((functorCompFullSubcategoryιIso R).app (op (coordHopfAlgebra R G))).symm ≪≫
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.mapIso
      ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).counitIso.app G)

namespace FiniteLocallyFreeCommAffineGroupSchemeCat

/-- Pullback of finite locally free commutative affine group schemes along `Spec S ⟶ Spec R`. -/
noncomputable def baseChangeFunctor :
    FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) ⥤
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of S) :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of S)).lift
    ((finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
      AffineGroupSchemeCat.baseChangeFunctor (CommRingCat.ofHom (algebraMap R S)))
    (finiteLocallyFreeCommAffineGroupSchemeProperty_baseChange R S)

/-- Forgetting finite local freeness and commutativity turns the restricted base change into
scheme-theoretic pullback. -/
noncomputable def baseChangeFunctorCompιIso :
    baseChangeFunctor R S ⋙
        (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of S)).ι ≅
      (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        AffineGroupSchemeCat.baseChangeFunctor (CommRingCat.ofHom (algebraMap R S)) :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of S)).liftCompιIso _ _

/-- **Base change of a Hopf spectrum is the Hopf spectrum of the scalar-extended coordinate Hopf
algebra**, restricted to finite locally free commutative objects. -/
noncomputable def baseChangeHopfSpecNatIso :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor ⋙ baseChangeFunctor R S ≅
      (FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctor R S).op ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          S).functor :=
  Functor.fullyFaithfulCancelRight
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of S)).ι <|
    Functor.isoWhiskerLeft
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor (baseChangeFunctorCompιIso R S) ≪≫
      Functor.isoWhiskerRight (functorCompFullSubcategoryιIso R)
        (AffineGroupSchemeCat.baseChangeFunctor (CommRingCat.ofHom (algebraMap R S))) ≪≫
      Functor.isoWhiskerLeft
        (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) (CommHopfAlgCat.{u} R)).op
        (AffineGroupSchemeCat.hopfSpecBaseChangeNatIso (R := R) (S := S)) ≪≫
      Functor.isoWhiskerRight
        (NatIso.op (FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctorCompιIso R S))
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of S)).functor ≪≫
      (Functor.isoWhiskerLeft
        (FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctor R S).op
        (functorCompFullSubcategoryιIso S)).symm

/-- The `rightOp` form of `baseChangeHopfSpecNatIso`, comparing the two ways of passing from a
coordinate Hopf algebra over `R` to a group scheme over `S`. -/
noncomputable def rightOpBaseChangeHopfSpecNatIso :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.functor ⋙ (baseChangeFunctor R S).op ≅
      FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctor R S ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          S).rightOp.functor :=
  NatIso.ofComponents (fun H => ((baseChangeHopfSpecNatIso R S).app (op H)).symm.op)
    fun f => Quiver.Hom.unop_inj ((baseChangeHopfSpecNatIso R S).inv.naturality f.op).symm

/-- **The coordinate Hopf algebra of a base-changed group scheme is the scalar extension of its
coordinate Hopf algebra**, naturally in the group scheme. -/
noncomputable def coordHopfAlgebraBaseChangeNatIso :
    (baseChangeFunctor R S).op ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          S).rightOp.inverse ≅
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).rightOp.inverse ⋙
        FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctor R S :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).rightOp.counitIso.symm (baseChangeFunctor R S).op)
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        S).rightOp.inverse ≪≫
    Functor.isoWhiskerLeft
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.inverse
      (Functor.isoWhiskerRight (rightOpBaseChangeHopfSpecNatIso R S)
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          S).rightOp.inverse) ≪≫
    Functor.isoWhiskerLeft
      ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).rightOp.inverse ⋙
        FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctor R S)
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        S).rightOp.unitIso.symm

/-- **Cartier duality commutes with base change**, naturally in the group scheme. -/
noncomputable def cartierDualBaseChangeNatIso :
    (baseChangeFunctor R S).op ⋙ cartierDualFunctor S ≅
      cartierDualFunctor R ⋙ baseChangeFunctor R S :=
  Functor.isoWhiskerRight (coordHopfAlgebraBaseChangeNatIso R S)
      ((FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor (k := S)).rightOp ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          S).functor) ≪≫
    Functor.isoWhiskerLeft
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.inverse
      (Functor.isoWhiskerRight
        (FiniteLocallyFreeBicommutativeHopfAlgCat.dualBaseChangeNatIso R S).symm
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          S).functor) ≪≫
    Functor.isoWhiskerLeft
      ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).rightOp.inverse ⋙
        (FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor (k := R)).rightOp)
      (baseChangeHopfSpecNatIso R S).symm

variable {R S}

/-- The coordinate Hopf algebra of a base-changed group scheme is the scalar extension of its
coordinate Hopf algebra. -/
noncomputable abbrev coordHopfAlgebraBaseChangeIso
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    coordHopfAlgebra S ((baseChangeFunctor R S).obj G) ≅
      FiniteLocallyFreeBicommutativeHopfAlgCat.baseChange S (coordHopfAlgebra R G) :=
  (coordHopfAlgebraBaseChangeNatIso R S).app (op G)

/-- **Cartier duality commutes with base change**: the Cartier dual of a base-changed finite
locally free commutative affine group scheme is the base change of its Cartier dual. -/
noncomputable abbrev cartierDualBaseChangeIso
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    cartierDual S ((baseChangeFunctor R S).obj G) ≅
      (baseChangeFunctor R S).obj (cartierDual R G) :=
  (cartierDualBaseChangeNatIso R S).app (op G)

end FiniteLocallyFreeCommAffineGroupSchemeCat

end TauCeti
