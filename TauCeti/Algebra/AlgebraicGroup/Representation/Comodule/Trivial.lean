/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Trivial point representations

This file synchronizes the trivial operations across the fixed-object correspondence between
point representations of an affine group and comodules over its commutative Hopf algebra.

Every module has a trivial point representation, in which every point acts by the identity on
scalar extension. This construction agrees with the point representation induced by the trivial
comodule. No finiteness, freeness, projectivity, flatness, or nontriviality hypothesis is used.

## Main declarations

* `HopfAlgebra.PointRepresentation.trivial`: the identity action on scalar extensions of an
  arbitrary module.
* `HopfAlgebra.PointRepresentation.ofComodule_trivial`: compatibility with the trivial
  comodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1.
* J. S. Milne, *Reductive Groups*, §§5.1--5.4.
-/

public section

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {V : Type w} [CommRing R] [CommRing H]
variable [_root_.HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]

namespace PointRepresentation

private noncomputable def rawTrivialAction
    (A : CommAlgCat.{max u v w} R) :
    points (H := H) A ⟶ GeneralLinear.scalarExtensionAutomorphisms (V := V) A :=
  GrpCat.ofHom (1 : points (H := H) A →* GeneralLinear.scalarExtensionAutomorphisms (V := V) A)

private theorem rawTrivialAction_naturality
    {A B : CommAlgCat.{max u v w} R} (phi : A ⟶ B) :
    mapPoints (H := H) phi ≫ rawTrivialAction (H := H) (V := V) B =
      rawTrivialAction (H := H) (V := V) A ≫
        GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi := by
  apply GrpCat.ext
  intro x
  simp [rawTrivialAction]

/-- The trivial point representation on an arbitrary module. Every point acts by the identity
linear automorphism after scalar extension. -/
noncomputable def trivial : PointRepresentation (R := R) (H := H) (V := V) where
  app A := rawTrivialAction (H := H) (V := V) A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm
  naturality A B phi := by
    -- `pointsFunctor_obj` and the scalar-extension object theorem are categorical equalities,
    -- with no computation lemma that rewrites this structure-field goal before it is exposed.
    change
      mapPoints (H := H) phi ≫ rawTrivialAction (H := H) (V := V) B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B).symm =
        rawTrivialAction (H := H) (V := V) A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := V)).map phi
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, rawTrivialAction_naturality (H := H) (V := V) phi]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

@[simp]
private theorem action_trivial (A : CommAlgCat.{max u v w} R) :
    (trivial (H := H) (V := V)).action A = rawTrivialAction (H := H) (V := V) A := by
  rw [action_def, trivial]
  -- The natural-transformation component is stored with the inverse of the opaque object
  -- equality; expose that categorical composite before cancelling the two transports.
  change
    (rawTrivialAction (H := H) (V := V) A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A) =
        rawTrivialAction (H := H) (V := V) A
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Every point acts as the identity in the trivial point representation. -/
@[simp]
theorem trivial_action (A : CommAlgCat.{max u v w} R) (x : points (H := H) A) :
    (trivial (H := H) (V := V)).action A x = 1 := by
  rw [action_trivial]
  simp [rawTrivialAction]

/-- The trivial point representation fixes every vector after scalar extension. -/
@[simp]
theorem trivial_action_apply (A : CommAlgCat.{max u v w} R) (x : points (H := H) A)
    (z : A ⊗[R] V) :
    ((trivial (H := H) (V := V)).action A x).val z = z := by
  rw [trivial_action]
  rfl

/-- The point representation induced by the trivial comodule is the trivial point
representation. -/
@[simp]
theorem ofComodule_trivial :
    ofComodule (Comodule.trivial (R := R) (C := H) (M := V)) =
      trivial (H := H) (V := V) := by
  apply ext
  intro A x
  apply Units.ext
  refine TensorProduct.AlgebraTensorModule.ext fun a v ↦ ?_
  rw [ofComodule_action_tmul, trivial_action_apply]
  rw [Comodule.trivial_coact_apply]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply,
    map_one, TensorProduct.comm_tmul]
  exact (TensorProduct.tmul_eq_smul_one_tmul (M := V) a v).symm

end PointRepresentation

end HopfAlgebra

end TauCeti
