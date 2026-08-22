/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Semidirect products of internal groups

Let `G` and `N` be group objects in a cartesian monoidal category. An internal left action of
`G` on `N` is a morphism `G ⊗ N ⟶ N` whose action on generalized points is unital,
multiplicative in `G`, and by group automorphisms of `N`. This file packages those three laws and
constructs the internal semidirect product `N ⋊ G` on the product object `N ⊗ G`.

The construction is characterized on every generalized-point group. The points of the internal
semidirect product are naturally the ordinary `SemidirectProduct` of the point groups. This gives
the group-object laws without choosing elements of the ambient category and exposes the familiar
component formulas to downstream constructions.

## Main declarations

* `TauCeti.GrpObj.Action`: an internal action by group automorphisms.
* `TauCeti.GrpObj.Action.toMulAutHom`: the induced action on generalized points.
* `TauCeti.GrpObj.Action.semidirectProduct`: the internal semidirect-product group object.
* `TauCeti.GrpObj.Action.pointMulEquiv`: its generalized points are an ordinary
  semidirect product.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.
* J. S. Milne, *Algebraic Groups* (2017), §6.a.

This is a prerequisite for Layer 5, "The unipotent radical", of the ReductiveGroups roadmap.
For two normal closed subgroup schemes, conjugation supplies the action below; multiplication
from their semidirect product is then a group-scheme morphism whose image is their product.
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti.GrpObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G N : C} [GrpObj G] [GrpObj N]

/-- An action of the internal group `G` on the internal group `N`.

The morphism `hom : G ⊗ N ⟶ N` is required to induce a left group action on generalized
points, and each element of `G(X)` must act multiplicatively on `N(X)`. The latter condition makes
the action one by group automorphisms; its inverse is the action of the inverse generalized point.
-/
structure Action (G N : C) [GrpObj G] [GrpObj N] where
  /-- The action morphism `G ⊗ N ⟶ N`. -/
  hom : G ⊗ N ⟶ N
  /-- The identity generalized point acts trivially. -/
  one_act (X : C) (n : X ⟶ N) : lift (1 : X ⟶ G) n ≫ hom = n := by cat_disch
  /-- Multiplication of generalized points acts by composition, in left-action order. -/
  mul_act (X : C) (g h : X ⟶ G) (n : X ⟶ N) :
    lift (g * h) n ≫ hom = lift g (lift h n ≫ hom) ≫ hom := by cat_disch
  /-- Every generalized point acts multiplicatively on the point group of `N`. -/
  act_mul (X : C) (g : X ⟶ G) (n m : X ⟶ N) :
    lift g (n * m) ≫ hom = (lift g n ≫ hom) * (lift g m ≫ hom) := by cat_disch

/-- Internal actions are determined by their action morphisms. -/
@[ext]
theorem Action.ext (A B : Action G N) (h : A.hom = B.hom) : A = B := by
  cases A
  cases B
  subst h
  rfl

namespace Action

variable (A : Action G N)

/-- The action of a generalized point of `G` on a generalized point of `N`. -/
def act {X : C} (g : X ⟶ G) (n : X ⟶ N) : X ⟶ N :=
  lift g n ≫ A.hom

/-- The action on generalized points is induced by the action morphism. -/
theorem act_def {X : C} (g : X ⟶ G) (n : X ⟶ N) :
    A.act g n = lift g n ≫ A.hom :=
  (rfl)

@[simp]
theorem one_act_apply {X : C} (n : X ⟶ N) : A.act (1 : X ⟶ G) n = n :=
  A.one_act X n

@[simp]
theorem mul_act_apply {X : C} (g h : X ⟶ G) (n : X ⟶ N) :
    A.act (g * h) n = A.act g (A.act h n) :=
  A.mul_act X g h n

@[simp]
theorem act_mul_apply {X : C} (g : X ⟶ G) (n m : X ⟶ N) :
    A.act g (n * m) = A.act g n * A.act g m :=
  A.act_mul X g n m

/-- Internal actions commute with precomposition of generalized points. -/
@[reassoc]
theorem comp_act {X Y : C} (f : X ⟶ Y) (g : Y ⟶ G) (n : Y ⟶ N) :
    f ≫ A.act g n = A.act (f ≫ g) (f ≫ n) := by
  rw [act, act, ← Category.assoc, comp_lift]

/-- A generalized point of `G` acts as an automorphism of the generalized-point group of `N`. -/
def toMulAut {X : C} (g : X ⟶ G) : MulAut (X ⟶ N) where
  toFun := A.act g
  invFun := A.act g⁻¹
  left_inv n := by
    rw [← A.mul_act_apply, inv_mul_cancel g, A.one_act_apply]
  right_inv n := by
    rw [← A.mul_act_apply, mul_inv_cancel g, A.one_act_apply]
  map_mul' := A.act_mul_apply g

@[simp]
theorem toMulAut_apply {X : C} (g : X ⟶ G) (n : X ⟶ N) :
    A.toMulAut g n = A.act g n :=
  by rfl

@[simp]
theorem act_one_apply {X : C} (g : X ⟶ G) : A.act g 1 = 1 := by
  simpa only [toMulAut_apply] using map_one (A.toMulAut g)

/-- The action homomorphism from generalized points of `G` to automorphisms of the generalized
points of `N`. -/
def toMulAutHom (X : C) : (X ⟶ G) →* MulAut (X ⟶ N) where
  toFun := A.toMulAut
  map_one' := MulEquiv.ext A.one_act_apply
  map_mul' g h := MulEquiv.ext (A.mul_act_apply g h)

@[simp]
theorem toMulAutHom_apply {X : C} (g : X ⟶ G) (n : X ⟶ N) :
    A.toMulAutHom X g n = A.act g n :=
  by rfl

/-- The presheaf of ordinary semidirect products induced by an internal group action. -/
private def pointSemidirectProduct : Cᵒᵖ ⥤ GrpCat.{v} where
  obj X := GrpCat.of ((unop X ⟶ N) ⋊[A.toMulAutHom (unop X)] (unop X ⟶ G))
  map {X Y} f := GrpCat.ofHom
    { toFun := fun x ↦ ⟨f.unop ≫ x.left, f.unop ≫ x.right⟩
      map_one' := by ext <;> simp
      map_mul' := fun x y ↦ by
        apply SemidirectProduct.ext
        · simp only [SemidirectProduct.mul_left, toMulAutHom_apply]
          rw [MonObj.comp_mul, A.comp_act]
        · simp only [SemidirectProduct.mul_right, MonObj.comp_mul] }
  map_id X := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext <;> simp
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext <;> simp [Category.assoc]

/-- The pointwise semidirect-product presheaf is represented by the product object `N ⊗ G`. -/
private def pointSemidirectProductRepresentableBy :
    (A.pointSemidirectProduct ⋙ forget GrpCat).RepresentableBy (N ⊗ G) where
  homEquiv {X} :=
    { toFun := fun f ↦ ⟨f ≫ fst N G, f ≫ snd N G⟩
      invFun := fun f ↦ lift f.left f.right
      left_inv := fun f ↦ by simp
      right_inv := fun f ↦ by apply SemidirectProduct.ext <;> simp }
  homEquiv_comp f g := by
    apply SemidirectProduct.ext
    · exact Category.assoc _ _ _
    · exact Category.assoc _ _ _

/-- The group-object structure on `N ⊗ G` representing the pointwise semidirect product. -/
@[instance_reducible]
noncomputable def semidirectProductGrpObj : GrpObj (N ⊗ G) :=
  GrpObj.ofRepresentableBy (N ⊗ G) A.pointSemidirectProduct
    A.pointSemidirectProductRepresentableBy

/-- The internal semidirect product associated to an internal action. Its underlying object is
the categorical product `N ⊗ G`. -/
noncomputable abbrev semidirectProduct : Grp C where
  X := N ⊗ G
  grp := A.semidirectProductGrpObj

/-- The Yoneda group of the internal semidirect product is the pointwise semidirect-product
presheaf. -/
private noncomputable def pointIso :
    (yonedaGrp (C := C)).obj A.semidirectProduct ≅ A.pointSemidirectProduct :=
  yonedaGrpObjIsoOfRepresentableBy (N ⊗ G) A.pointSemidirectProduct
    A.pointSemidirectProductRepresentableBy

/-- Generalized points of the internal semidirect product are naturally the ordinary semidirect
product of the generalized-point groups. -/
noncomputable def pointMulEquiv (X : C) :
    letI := A.semidirectProductGrpObj
    (X ⟶ N ⊗ G) ≃* ((X ⟶ N) ⋊[A.toMulAutHom X] (X ⟶ G)) := by
  letI := A.semidirectProductGrpObj
  exact (A.pointIso.app (op X)).groupIsoToMulEquiv

private theorem pointMulEquiv_apply {X : C} (f : X ⟶ N ⊗ G) :
    letI := A.semidirectProductGrpObj
    A.pointMulEquiv X f =
      (⟨f ≫ fst N G, f ≫ snd N G⟩ :
        (X ⟶ N) ⋊[A.toMulAutHom X] (X ⟶ G)) :=
  rfl

private theorem pointMulEquiv_symm_apply_aux {X : C}
    (f : (X ⟶ N) ⋊[A.toMulAutHom X] (X ⟶ G)) :
    letI := A.semidirectProductGrpObj
    (A.pointMulEquiv X).symm f = lift f.left f.right :=
  rfl

@[simp]
theorem pointMulEquiv_left {X : C} (f : X ⟶ N ⊗ G) :
    letI := A.semidirectProductGrpObj
    (A.pointMulEquiv X f).left = f ≫ fst N G :=
  by
    exact congrArg SemidirectProduct.left (A.pointMulEquiv_apply f)

@[simp]
theorem pointMulEquiv_right {X : C} (f : X ⟶ N ⊗ G) :
    letI := A.semidirectProductGrpObj
    (A.pointMulEquiv X f).right = f ≫ snd N G :=
  by
    exact congrArg SemidirectProduct.right (A.pointMulEquiv_apply f)

@[simp]
theorem pointMulEquiv_symm_apply {X : C}
    (f : (X ⟶ N) ⋊[A.toMulAutHom X] (X ⟶ G)) :
    letI := A.semidirectProductGrpObj
    (A.pointMulEquiv X).symm f = lift f.left f.right :=
  by
    exact A.pointMulEquiv_symm_apply_aux f

/-- The natural inclusion of the normal factor into the pointwise semidirect product. -/
private def inlNatTrans : (yonedaGrp (C := C)).obj (Grp.mk N) ⟶
    A.pointSemidirectProduct where
  app X := GrpCat.ofHom SemidirectProduct.inl
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro n
    -- Reduce the categorical and concrete group wrappers to the two semidirect components.
    change
      (⟨f.unop ≫ n, 1⟩ :
        (unop Y ⟶ N) ⋊[A.toMulAutHom (unop Y)] (unop Y ⟶ G)) =
      ⟨f.unop ≫ n, f.unop ≫ (1 : unop X ⟶ G)⟩
    congr 1
    simp

/-- The natural inclusion of the acting factor into the pointwise semidirect product. -/
private def inrNatTrans : (yonedaGrp (C := C)).obj (Grp.mk G) ⟶
    A.pointSemidirectProduct where
  app X := GrpCat.ofHom SemidirectProduct.inr
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    -- Reduce the categorical and concrete group wrappers to the two semidirect components.
    change
      (⟨1, f.unop ≫ g⟩ :
        (unop Y ⟶ N) ⋊[A.toMulAutHom (unop Y)] (unop Y ⟶ G)) =
      ⟨f.unop ≫ (1 : unop X ⟶ N), f.unop ≫ g⟩
    congr 1
    simp

/-- The natural projection from the pointwise semidirect product to the acting factor. -/
private def rightHomNatTrans : A.pointSemidirectProduct ⟶
    (yonedaGrp (C := C)).obj (Grp.mk G) where
  app X := GrpCat.ofHom SemidirectProduct.rightHom
  naturality {_ _} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl

/-- The canonical inclusion `N ⟶ N ⋊ G` of internal groups. -/
noncomputable def inl : Grp.mk N ⟶ A.semidirectProduct :=
  yonedaGrpFullyFaithful.preimage (A.inlNatTrans ≫ A.pointIso.inv)

/-- The canonical inclusion `G ⟶ N ⋊ G` of internal groups. -/
noncomputable def inr : Grp.mk G ⟶ A.semidirectProduct :=
  yonedaGrpFullyFaithful.preimage (A.inrNatTrans ≫ A.pointIso.inv)

/-- The canonical projection `N ⋊ G ⟶ G` of internal groups. -/
noncomputable def rightHom : A.semidirectProduct ⟶ Grp.mk G :=
  yonedaGrpFullyFaithful.preimage (A.pointIso.hom ≫ A.rightHomNatTrans)

/-- On generalized points, the first canonical inclusion is `SemidirectProduct.inl`. -/
@[simp]
theorem pointMulEquiv_comp_inl {X : C} (n : X ⟶ N) :
    letI := A.semidirectProductGrpObj
    A.pointMulEquiv X (n ≫ A.inl.hom.hom) = SemidirectProduct.inl n := by
  -- Expose the Yoneda equivalence at one component; its body is hidden from downstream users.
  change A.pointIso.hom.app (op X) (n ≫ A.inl.hom.hom) = SemidirectProduct.inl n
  have h := congrArg (fun F ↦ F.app (op X) n)
    (yonedaGrpFullyFaithful.map_preimage (A.inlNatTrans ≫ A.pointIso.inv))
  -- Read the fully-faithful preimage equation as an equality of generalized points.
  change n ≫ A.inl.hom.hom =
    A.pointIso.inv.app (op X) (SemidirectProduct.inl n) at h
  rw [h]
  exact A.pointIso.inv_hom_id_app_apply (op X) (SemidirectProduct.inl n)

/-- On generalized points, the second canonical inclusion is `SemidirectProduct.inr`. -/
@[simp]
theorem pointMulEquiv_comp_inr {X : C} (g : X ⟶ G) :
    letI := A.semidirectProductGrpObj
    A.pointMulEquiv X (g ≫ A.inr.hom.hom) = SemidirectProduct.inr g := by
  -- Expose the Yoneda equivalence at one component; its body is hidden from downstream users.
  change A.pointIso.hom.app (op X) (g ≫ A.inr.hom.hom) = SemidirectProduct.inr g
  have h := congrArg (fun F ↦ F.app (op X) g)
    (yonedaGrpFullyFaithful.map_preimage (A.inrNatTrans ≫ A.pointIso.inv))
  -- Read the fully-faithful preimage equation as an equality of generalized points.
  change g ≫ A.inr.hom.hom =
    A.pointIso.inv.app (op X) (SemidirectProduct.inr g) at h
  rw [h]
  exact A.pointIso.inv_hom_id_app_apply (op X) (SemidirectProduct.inr g)

/-- On generalized points, the canonical projection is `SemidirectProduct.rightHom`. -/
@[simp]
theorem comp_rightHom {X : C} (x : X ⟶ N ⊗ G) :
    letI := A.semidirectProductGrpObj
    x ≫ A.rightHom.hom.hom = SemidirectProduct.rightHom (A.pointMulEquiv X x) := by
  have h := congrArg (fun F ↦ F.app (op X) x)
    (yonedaGrpFullyFaithful.map_preimage (A.pointIso.hom ≫ A.rightHomNatTrans))
  exact h

end Action

end TauCeti.GrpObj
