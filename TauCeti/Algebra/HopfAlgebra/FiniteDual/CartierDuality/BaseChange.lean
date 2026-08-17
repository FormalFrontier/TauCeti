/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.BaseChange
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.CartierDuality.Basic

/-!
# Base change of finite locally free Cartier duality

Extension of scalars carries a finite locally free bicommutative Hopf algebra over `R` to one
over an `R`-algebra `S`, and `TauCeti.ConvolutionDual.baseChangeBialgEquiv` says that it commutes
with finite dualization. This file records both facts in the category
`TauCeti.FiniteLocallyFreeBicommutativeHopfAlgCat`, where Cartier duality lives.

## Main declarations

* `TauCeti.finiteLocallyFreeBicommutativeHopfAlgProperty_baseChange`: scalar extension preserves
  finite local freeness and cocommutativity.
* `TauCeti.FiniteLocallyFreeBicommutativeHopfAlgCat.baseChange` and
  `TauCeti.FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeFunctor`: scalar extension of
  finite locally free bicommutative Hopf algebras, on objects and functorially.
* `TauCeti.FiniteLocallyFreeBicommutativeHopfAlgCat.baseChangeDualIso`: the scalar extension of
  a finite dual is the finite dual of the scalar extension, naturally by
  `baseChangeDualIso_hom_naturality` and bundled as `dualBaseChangeNatIso`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This advances Layer 4, "Cartier duality", of the ReductiveGroups roadmap: compatibility with
pullback of the base is what makes Cartier duality usable on fibres and after field extension.
-/

public section

open CategoryTheory Opposite

open scoped TensorProduct

namespace TauCeti

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension preserves finite local freeness and cocommutativity. -/
theorem finiteLocallyFreeBicommutativeHopfAlgProperty_baseChange
    (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    finiteLocallyFreeBicommutativeHopfAlgProperty S
      (CommHopfAlgCat.baseChange (K := S)
        ((finiteLocallyFreeBicommutativeHopfAlgProperty R).ι.obj H)) :=
  (finiteLocallyFreeBicommutativeHopfAlgProperty_iff S _).2
    ⟨inferInstanceAs (Module.Finite S (S ⊗[R] H)),
      inferInstanceAs (Module.Projective S (S ⊗[R] H)),
      inferInstanceAs (Coalgebra.IsCocomm S (S ⊗[R] H))⟩

namespace FiniteLocallyFreeBicommutativeHopfAlgCat

variable {R} in
/-- Scalar extension of a single finite locally free bicommutative Hopf algebra. -/
noncomputable abbrev baseChange (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} S :=
  of S (S ⊗[R] H)

variable {R S} in
/-- Scalar extension of a morphism of finite locally free bicommutative Hopf algebras. -/
noncomputable abbrev baseChangeMap {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R}
    (f : H ⟶ K) : baseChange S H ⟶ baseChange S K :=
  ofHom (Bialgebra.TensorProduct.map (BialgHom.id S S) (toBialgHom f))

variable {R S} in
/-- The bialgebra morphism underlying `baseChangeMap` tensors the morphism with the identity on
the new base. -/
@[simp]
theorem toBialgHom_baseChangeMap {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R}
    (f : H ⟶ K) :
    toBialgHom (baseChangeMap (S := S) f) =
      Bialgebra.TensorProduct.map (BialgHom.id S S) (toBialgHom f) :=
  rfl

/-- Scalar extension of finite locally free bicommutative Hopf algebras.

The body is exposed so that `baseChangeFunctor R S ⋙ dualFunctor.rightOp` reduces to the finite
dual of a scalar extension, without which the components of `dualBaseChangeNatIso` do not
typecheck. No other declaration here depends on that reduction. -/
@[expose]
noncomputable def baseChangeFunctor :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R ⥤
      FiniteLocallyFreeBicommutativeHopfAlgCat.{u} S :=
  (finiteLocallyFreeBicommutativeHopfAlgProperty S).lift
    ((finiteLocallyFreeBicommutativeHopfAlgProperty R).ι ⋙
      CommHopfAlgCat.baseChangeFunctor (K := S))
    (finiteLocallyFreeBicommutativeHopfAlgProperty_baseChange R S)

/-- The object part of `baseChangeFunctor` is scalar extension. -/
@[simp]
theorem baseChangeFunctor_obj (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    (baseChangeFunctor R S).obj H = baseChange S H :=
  (rfl)

variable {R S} in
/-- The morphism part of `baseChangeFunctor` is scalar extension of morphisms. -/
@[simp]
theorem baseChangeFunctor_map {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R}
    (f : H ⟶ K) :
    (baseChangeFunctor R S).map f =
      eqToHom (baseChangeFunctor_obj R S H) ≫ baseChangeMap f ≫
        eqToHom (baseChangeFunctor_obj R S K).symm :=
  (rfl)

/-- Forgetting finite local freeness and cocommutativity turns the restricted scalar extension
into the scalar extension of commutative Hopf algebras. -/
noncomputable def baseChangeFunctorCompιIso :
    baseChangeFunctor R S ⋙ (finiteLocallyFreeBicommutativeHopfAlgProperty S).ι ≅
      (finiteLocallyFreeBicommutativeHopfAlgProperty R).ι ⋙
        CommHopfAlgCat.baseChangeFunctor (K := S) :=
  (finiteLocallyFreeBicommutativeHopfAlgProperty S).liftCompιIso _ _

variable {R S}

/-- **Finite dualization commutes with extension of scalars.** -/
noncomputable def baseChangeDualIso (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    baseChange S (dual H) ≅ dual (baseChange S H) :=
  ObjectProperty.isoMk (finiteLocallyFreeBicommutativeHopfAlgProperty S)
    (_root_.CommHopfAlgCat.isoMk (ConvolutionDual.baseChangeBialgEquiv R S H))

/-- The forward map of `baseChangeDualIso` sends a scalar-extended functional to the
scalar-extended evaluation it defines. -/
@[simp]
theorem baseChangeDualIso_hom_apply_tmul_apply_tmul
    (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
    (a b : S) (phi : ConvolutionDual R H) (x : H) :
    (((baseChangeDualIso (S := S) H).hom (a ⊗ₜ[R] phi)) :
        ConvolutionDual S (S ⊗[R] H)).ofConv (b ⊗ₜ[R] x) =
      a * b * algebraMap R S (phi.ofConv x) :=
  ConvolutionDual.baseChangeBialgEquiv_tmul_apply_tmul a b phi x

/-- Finite dualization and scalar extension commute naturally. -/
@[simp, reassoc]
theorem baseChangeDualIso_hom_naturality
    {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R} (f : H ⟶ K) :
    baseChangeMap (S := S) (dualMap f) ≫ (baseChangeDualIso H).hom =
      (baseChangeDualIso K).hom ≫ dualMap (baseChangeMap f) := by
  apply hom_ext
  exact (ConvolutionDual.baseChangeBialgEquiv_naturality (K := S) (toBialgHom f)).symm

/-- The inverse form of `baseChangeDualIso_hom_naturality`. -/
@[simp, reassoc]
theorem baseChangeDualIso_inv_naturality
    {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R} (f : H ⟶ K) :
    (baseChangeDualIso (S := S) K).inv ≫ baseChangeMap (dualMap f) =
      dualMap (baseChangeMap f) ≫ (baseChangeDualIso H).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact baseChangeDualIso_hom_naturality f

variable (R S)

/-- Finite dualization commutes with scalar extension, as a natural isomorphism of functors
`FiniteLocallyFreeBicommutativeHopfAlgCat R ⥤ (FiniteLocallyFreeBicommutativeHopfAlgCat S)ᵒᵖ`. -/
noncomputable def dualBaseChangeNatIso :
    (dualFunctor (k := R)).rightOp ⋙ (baseChangeFunctor R S).op ≅
      baseChangeFunctor R S ⋙ (dualFunctor (k := S)).rightOp :=
  NatIso.ofComponents (fun H => (baseChangeDualIso H).symm.op) fun f =>
    Quiver.Hom.unop_inj (baseChangeDualIso_inv_naturality f)

/-- The components of `dualBaseChangeNatIso` are the objectwise comparisons `baseChangeDualIso`.
They appear inverted because the natural isomorphism lands in an opposite category. -/
@[simp]
theorem dualBaseChangeNatIso_hom_app (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    (dualBaseChangeNatIso R S).hom.app H = (baseChangeDualIso (S := S) H).inv.op :=
  (rfl)

/-- The inverse components of `dualBaseChangeNatIso` are the objectwise comparisons
`baseChangeDualIso`. -/
@[simp]
theorem dualBaseChangeNatIso_inv_app (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    (dualBaseChangeNatIso R S).inv.app H = (baseChangeDualIso (S := S) H).hom.op :=
  (rfl)

end FiniteLocallyFreeBicommutativeHopfAlgCat

end TauCeti
