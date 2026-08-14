/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Functoriality

/-!
# Cartier duality for finite-dimensional Hopf algebras

A commutative finite group scheme over a field is represented by a finite-dimensional Hopf
algebra whose multiplication and comultiplication are both commutative. The finite linear dual
preserves this bicommutative condition, reverses morphisms, and is involutive by evaluation.

This file packages those facts as a contravariant equivalence on finite-dimensional
bicommutative Hopf algebras. It is the algebraic core of Cartier duality over a field; transporting
the equivalence through `Spec` and extending it to finite locally free Hopf algebras over a
general base are separate steps.

## Main declarations

* `TauCeti.FiniteBicommutativeHopfAlgCat`: finite-dimensional commutative, cocommutative Hopf
  algebras over a field.
* `TauCeti.FiniteBicommutativeHopfAlgCat.dualFunctor`: contravariant finite dualization.
* `TauCeti.FiniteBicommutativeHopfAlgCat.evalIso`: the objectwise double-dual evaluation
  isomorphism, natural in morphisms by `evalIso_hom_naturality`.
* `TauCeti.FiniteBicommutativeHopfAlgCat.cartierDuality`: the resulting anti-equivalence.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This advances Layer 4, "Cartier duality", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The object property selecting finite-dimensional bicommutative Hopf algebras over a field.

The ambient `CommHopfAlgCat` supplies commutativity of multiplication; the second conjunct is
cocommutativity of comultiplication. -/
def finiteBicommutativeHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (_root_.CommHopfAlgCat.{u} k) :=
  fun H => Module.Finite k H ∧ Coalgebra.IsCocomm k H

/-- Membership in `finiteBicommutativeHopfAlgProperty` is finite-dimensionality together with
cocommutativity. -/
@[simp]
theorem finiteBicommutativeHopfAlgProperty_iff (k : Type u) [Field k]
    (H : _root_.CommHopfAlgCat.{u} k) :
    finiteBicommutativeHopfAlgProperty k H ↔
      Module.Finite k H ∧ Coalgebra.IsCocomm k H :=
  Iff.rfl

/-- The category of finite-dimensional bicommutative Hopf algebras over a field. -/
abbrev FiniteBicommutativeHopfAlgCat (k : Type u) [Field k] :=
  (finiteBicommutativeHopfAlgProperty (k := k)).FullSubcategory

namespace FiniteBicommutativeHopfAlgCat

variable {k : Type u} [Field k]

instance : CoeSort (FiniteBicommutativeHopfAlgCat.{u} k) (Type u) :=
  ⟨fun H => H.obj⟩

instance commRing (H : FiniteBicommutativeHopfAlgCat.{u} k) : CommRing H :=
  inferInstanceAs (CommRing H.obj)

instance hopfAlgebra (H : FiniteBicommutativeHopfAlgCat.{u} k) :
    HopfAlgebra k H :=
  inferInstanceAs (HopfAlgebra k H.obj)

instance finite (H : FiniteBicommutativeHopfAlgCat.{u} k) : Module.Finite k H :=
  H.property.1

instance isCocomm (H : FiniteBicommutativeHopfAlgCat.{u} k) :
    Coalgebra.IsCocomm k H :=
  H.property.2

variable (k) in
/-- Bundle a finite-dimensional bicommutative Hopf algebra as an object of
`FiniteBicommutativeHopfAlgCat`. -/
abbrev of (H : Type u) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    [Coalgebra.IsCocomm k H] : FiniteBicommutativeHopfAlgCat.{u} k :=
  ⟨_root_.CommHopfAlgCat.of k H,
    (finiteBicommutativeHopfAlgProperty_iff k _).2 ⟨inferInstance, inferInstance⟩⟩

/-- The bialgebra morphism underlying a morphism of finite bicommutative Hopf algebras. -/
abbrev toBialgHom {H K : FiniteBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    H →ₐc[k] K :=
  f.hom.hom

/-- Bundle a bialgebra morphism between finite-dimensional bicommutative Hopf algebras. -/
abbrev ofHom {H K : Type u} [CommRing H] [CommRing K] [HopfAlgebra k H]
    [HopfAlgebra k K] [Module.Finite k H] [Module.Finite k K]
    [Coalgebra.IsCocomm k H] [Coalgebra.IsCocomm k K] (f : H →ₐc[k] K) :
    of k H ⟶ of k K :=
  ObjectProperty.homMk (_root_.CommHopfAlgCat.ofHom f)

/-- Morphisms of finite bicommutative Hopf algebras are determined by their underlying
bialgebra morphisms. -/
@[ext]
theorem hom_ext {H K : FiniteBicommutativeHopfAlgCat.{u} k} {f g : H ⟶ K}
    (h : toBialgHom f = toBialgHom g) : f = g :=
  ObjectProperty.hom_ext (P := finiteBicommutativeHopfAlgProperty k)
    (_root_.CommHopfAlgCat.hom_ext h)

@[simp]
theorem toBialgHom_id {H : FiniteBicommutativeHopfAlgCat.{u} k} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id k H :=
  rfl

@[simp]
theorem toBialgHom_comp {H K L : FiniteBicommutativeHopfAlgCat.{u} k}
    (f : H ⟶ K) (g : K ⟶ L) :
    toBialgHom (f ≫ g) = (toBialgHom g).comp (toBialgHom f) :=
  rfl

/-- The finite dual of a finite-dimensional bicommutative Hopf algebra. -/
noncomputable abbrev dual (H : FiniteBicommutativeHopfAlgCat.{u} k) :
    FiniteBicommutativeHopfAlgCat.{u} k :=
  of k (ConvolutionDual k H)

/-- A morphism of finite bicommutative Hopf algebras induces a morphism of finite duals in the
opposite direction. -/
noncomputable abbrev dualMap {H K : FiniteBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    dual K ⟶ dual H :=
  ofHom (ConvolutionDual.map k (toBialgHom f))

/-- The bialgebra morphism underlying `dualMap` is the transposed morphism. -/
@[simp]
theorem toBialgHom_dualMap {H K : FiniteBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    toBialgHom (dualMap f) = ConvolutionDual.map k (toBialgHom f) :=
  rfl

/-- Finite dualization as a contravariant endofunctor on finite-dimensional bicommutative Hopf
algebras. -/
noncomputable def dualFunctor :
    (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ ⥤
      FiniteBicommutativeHopfAlgCat.{u} k where
  obj H := dual H.unop
  map f := dualMap f.unop
  map_id H := by
    apply hom_ext
    simp only [unop_id, toBialgHom_dualMap, toBialgHom_id, ConvolutionDual.map_id]
  map_comp f g := by
    apply hom_ext
    simp only [unop_comp, toBialgHom_dualMap, toBialgHom_comp,
      ConvolutionDual.map_comp]

/-- The object part of `dualFunctor` is the finite convolution dual. -/
@[simp]
theorem dualFunctor_obj (H : (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ) :
    (dualFunctor (k := k)).obj H = dual H.unop :=
  (rfl)

/-- The morphism part of `dualFunctor` is precomposition on the finite dual. -/
@[simp]
theorem dualFunctor_map {H K : (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ}
    (f : H ⟶ K) :
    (dualFunctor (k := k)).map f =
      eqToHom (dualFunctor_obj H) ≫ dualMap f.unop ≫ eqToHom (dualFunctor_obj K).symm :=
  (rfl)

/-- Evaluation identifies a finite bicommutative Hopf algebra with its double finite dual. -/
noncomputable def evalIso (H : FiniteBicommutativeHopfAlgCat.{u} k) :
    H ≅ dual (dual H) :=
  ObjectProperty.isoMk (finiteBicommutativeHopfAlgProperty k)
    (_root_.CommHopfAlgCat.isoMk (ConvolutionDual.evalBialgEquiv k H))

/-- The forward map of `evalIso` evaluates finite-dual functionals. -/
@[simp]
theorem evalIso_hom_apply_apply (H : FiniteBicommutativeHopfAlgCat.{u} k)
    (x : H) (phi : ConvolutionDual k H) :
    ((evalIso H).hom x).ofConv phi = phi.ofConv x :=
  ConvolutionDual.evalBialgEquiv_apply_apply k H x phi

/-- The inverse map of `evalIso` is characterized by evaluation. -/
@[simp]
theorem evalIso_inv_apply_apply (H : FiniteBicommutativeHopfAlgCat.{u} k)
    (Phi : ConvolutionDual k (ConvolutionDual k H)) (phi : ConvolutionDual k H) :
    phi.ofConv ((evalIso H).inv Phi) = Phi.ofConv phi :=
  ConvolutionDual.evalBialgEquiv_symm_apply_apply k H Phi phi

/-- Double-dual evaluation is natural in finite-dimensional bicommutative Hopf algebras. -/
@[simp, reassoc]
theorem evalIso_hom_naturality {H K : FiniteBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    f ≫ (evalIso K).hom = (evalIso H).hom ≫ dualMap (dualMap f) := by
  apply hom_ext
  exact ConvolutionDual.evalBialgEquiv_naturality k H (toBialgHom f)

/-- Recover the preimage of a morphism between finite duals by double-dual evaluation. -/
private noncomputable def dualMapPreimage
    {H K : (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ}
    (f : dual H.unop ⟶ dual K.unop) : H ⟶ K :=
  (ObjectProperty.homMk (_root_.CommHopfAlgCat.ofHom
    ((ConvolutionDual.evalBialgEquiv k H.unop).symm.toBialgHom.comp
      ((ConvolutionDual.map k (toBialgHom f)).comp
        (ConvolutionDual.evalBialgEquiv k K.unop).toBialgHom)))).op

private theorem toBialgHom_dualMapPreimage_unop
    {H K : (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ}
    (f : dual H.unop ⟶ dual K.unop) :
    toBialgHom (dualMapPreimage f).unop =
      (ConvolutionDual.evalBialgEquiv k H.unop).symm.toBialgHom.comp
        ((ConvolutionDual.map k (toBialgHom f)).comp
          (ConvolutionDual.evalBialgEquiv k K.unop).toBialgHom) :=
  rfl

private theorem dualFunctor_map_dualMapPreimage
    {H K : (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ}
    (f : dual H.unop ⟶ dual K.unop) :
    (dualFunctor (k := k)).map (dualMapPreimage f) = f := by
  apply hom_ext
  change ConvolutionDual.map k (toBialgHom (dualMapPreimage f).unop) = toBialgHom f
  apply BialgHom.ext
  intro phi
  apply WithConv.ofConv_injective
  ext x
  rw [toBialgHom_dualMapPreimage_unop]
  rw [ConvolutionDual.map_apply_apply]
  -- Display the three maps in the composite: the categorical wrappers have no carrier-level
  -- application lemma that would expose them to rewriting.
  change phi.ofConv ((ConvolutionDual.evalBialgEquiv k H.unop).symm
    (ConvolutionDual.map k (toBialgHom f)
      (ConvolutionDual.evalBialgEquiv k K.unop x))) = (toBialgHom f phi).ofConv x
  rw [ConvolutionDual.evalBialgEquiv_symm_apply_apply,
    ConvolutionDual.map_apply_apply, ConvolutionDual.evalBialgEquiv_apply_apply]

private theorem dualFunctor_map_injective
    {H K : (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ} :
    Function.Injective
      ((dualFunctor (k := k)).map : (H ⟶ K) →
        ((dualFunctor (k := k)).obj H ⟶ (dualFunctor (k := k)).obj K)) := by
  intro f g h
  have hmap :
      ConvolutionDual.map k (toBialgHom f.unop) =
        ConvolutionDual.map k (toBialgHom g.unop) := by
    have hmap' := congrArg toBialgHom h
    -- The object computation is hidden behind `dualFunctor`; expose its carrier so that the
    -- equality can be evaluated on finite-dual functionals below.
    change ConvolutionDual.map k (toBialgHom f.unop) =
      ConvolutionDual.map k (toBialgHom g.unop) at hmap'
    exact hmap'
  apply Quiver.Hom.unop_inj
  apply hom_ext
  apply BialgHom.ext
  intro x
  apply (Module.evalEquiv k H.unop).injective
  ext phi
  have h' := congrArg (fun q => (q (WithConv.toConv phi)).ofConv x) hmap
  simpa only [Module.evalEquiv_apply, Module.Dual.eval_apply,
    ConvolutionDual.map_apply_apply, WithConv.ofConv_toConv] using h'

instance dualFunctorFaithful : (dualFunctor (k := k)).Faithful where
  map_injective := fun h => dualFunctor_map_injective h

instance dualFunctorFull : (dualFunctor (k := k)).Full where
  map_surjective f := ⟨dualMapPreimage f, dualFunctor_map_dualMapPreimage f⟩

instance dualFunctorEssSurj : (dualFunctor (k := k)).EssSurj where
  mem_essImage H :=
    ⟨Opposite.op (dual H),
      ⟨eqToIso (dualFunctor_obj (Opposite.op (dual H))) ≪≫ (evalIso H).symm⟩⟩

instance dualFunctorIsEquivalence : (dualFunctor (k := k)).IsEquivalence where

/-- **Finite-dimensional Cartier duality.** Finite dualization is an anti-equivalence of the
category of finite-dimensional bicommutative Hopf algebras over a field. -/
noncomputable def cartierDuality :
    (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ ≌
      FiniteBicommutativeHopfAlgCat.{u} k :=
  (dualFunctor (k := k)).asEquivalence

/-- The forward functor of `cartierDuality` is finite dualization. -/
@[simp]
theorem cartierDuality_functor : (cartierDuality (k := k)).functor = dualFunctor :=
  (rfl)

end FiniteBicommutativeHopfAlgCat

end TauCeti
