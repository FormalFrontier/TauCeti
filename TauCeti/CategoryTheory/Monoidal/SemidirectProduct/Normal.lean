/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Normal
public import TauCeti.CategoryTheory.Monoidal.SemidirectProduct.Basic

/-!
# Multiplication from semidirect products of internal subgroups

Let `i : N ⟶ G` be a normal subgroup object and let `j : H ⟶ G` be another internal-group
homomorphism. Conjugation through `j` gives an action of `H` on `N`. This file constructs that
action and the canonical internal-group homomorphism

```text
N ⋊ H ⟶ G,    (n, h) ↦ i(n) * j(h).
```

The construction is characterized on generalized points and on the two canonical inclusions.
For two normal closed subgroup schemes, its scheme-theoretic image is their product. This is the
binary-product map used in the maximal-dimension construction of the unipotent radical.

## Main declarations

* `TauCeti.GrpObj.Action.normalConjugation`: conjugation along a map into the ambient group.
* `TauCeti.GrpObj.Action.normalSemidirectMul`: multiplication from the resulting semidirect
  product into the ambient group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. It supplies the
group-scheme multiplication homomorphism whose scheme-theoretic image is the product of two
normal connected smooth unipotent closed subgroups.
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti.GrpObj.Action

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G N H X : C} [GrpObj G] [GrpObj N] [GrpObj H]

omit [GrpObj G] [GrpObj N] [GrpObj H] in
/-- Mapping the first component of a product commutes with forming a pair of generalized
points. -/
private theorem lift_comp_mapLeft (j : H ⟶ G) (h : X ⟶ H) (n : X ⟶ N) :
    lift h n ≫ lift (fst H N ≫ j) (snd H N) = lift (h ≫ j) n := by
  ext <;> simp

/-- Conjugation by an internal group mapping to `G` acts on a normal subgroup object of `G`.

If `i : N ⟶ G` is normal and `j : H ⟶ G` is an internal-group homomorphism, the action sends
`(h, n)` to the unique element of `N` whose image in `G` is `j(h) * i(n) * j(h)⁻¹`. -/
noncomputable def normalConjugation (i : N ⟶ G) [IsMonHom.Normal i]
    (j : H ⟶ G) [IsMonHom j] : Action H N where
  hom := lift (fst H N ≫ j) (snd H N) ≫ TauCeti.normalConjugation i
  one_act Y n := by
    rw [← Category.assoc, lift_comp_mapLeft, MonObj.one_comp]
    exact TauCeti.normalConjugation_one_left i n
  mul_act Y h₁ h₂ n := by
    simp_rw [← Category.assoc, lift_comp_mapLeft]
    rw [MonObj.mul_comp]
    exact TauCeti.normalConjugation_mul_left i (h₁ ≫ j) (h₂ ≫ j) n
  act_mul Y h n₁ n₂ := by
    simp_rw [← Category.assoc, lift_comp_mapLeft]
    exact TauCeti.normalConjugation_mul_right i (h ≫ j) n₁ n₂

/-- The morphism underlying conjugation along `j`. -/
theorem normalConjugation_hom (i : N ⟶ G) [IsMonHom.Normal i]
    (j : H ⟶ G) [IsMonHom j] :
    (normalConjugation i j).hom =
      lift (fst H N ≫ j) (snd H N) ≫ TauCeti.normalConjugation i :=
  (rfl)

/-- The action by conjugation along `j` evaluates as ambient conjugation through `j`. -/
@[simp]
theorem normalConjugation_act (i : N ⟶ G) [IsMonHom.Normal i]
    (j : H ⟶ G) [IsMonHom j] (h : X ⟶ H) (n : X ⟶ N) :
    (normalConjugation i j).act h n =
      lift (h ≫ j) n ≫ TauCeti.normalConjugation i := by
  rw [Action.act_def, normalConjugation_hom, ← Category.assoc, lift_comp_mapLeft]

/-- The generalized-point homomorphism from the normal semidirect product to the ambient group. -/
private noncomputable def normalSemidirectMulPointHom
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j] (X : C) :
    let A := normalConjugation i j
    letI := A.semidirectProductGrpObj
    (X ⟶ N ⊗ H) →* (X ⟶ G) := by
  let A := normalConjugation i j
  letI := A.semidirectProductGrpObj
  let fi : (X ⟶ N) →* (X ⟶ G) :=
    { toFun := fun n ↦ n ≫ i
      map_one' := MonObj.one_comp i
      map_mul' := fun n m ↦ MonObj.mul_comp n m i }
  let fj : (X ⟶ H) →* (X ⟶ G) :=
    { toFun := fun h ↦ h ≫ j
      map_one' := MonObj.one_comp j
      map_mul' := fun h k ↦ MonObj.mul_comp h k j }
  let m : ((X ⟶ N) ⋊[A.toMulAutHom X] (X ⟶ H)) →* (X ⟶ G) :=
    SemidirectProduct.lift fi fj (by
      intro h
      ext n
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      dsimp only [fi, fj, A]
      rw [Action.toMulAutHom_apply, normalConjugation_act]
      -- The local monoid-homomorphism constructors have no application simp lemma.
      change (lift (h ≫ j) n ≫ TauCeti.normalConjugation i) ≫ i =
        (h ≫ j) * (n ≫ i) * (h ≫ j)⁻¹
      simpa only [Category.assoc] using
        TauCeti.lift_normalConjugation_comp i (h ≫ j) n)
  exact m.comp (A.pointMulEquiv X).toMonoidHom

/-- On generalized points, normal semidirect multiplication is the product of the two ambient
images. -/
private theorem normalSemidirectMulPointHom_apply
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j]
    (x : X ⟶ N ⊗ H) :
    normalSemidirectMulPointHom i j X x =
      (x ≫ fst N H ≫ i) * (x ≫ snd N H ≫ j) := by
  simp [normalSemidirectMulPointHom, SemidirectProduct.lift,
    pointMulEquiv_left, pointMulEquiv_right]

/-- The generalized-point maps defining normal semidirect multiplication are natural in the
source object. -/
private noncomputable def normalSemidirectMulNatTrans
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j] :
    let A := normalConjugation i j
    (yonedaGrp (C := C)).obj A.semidirectProduct ⟶
      (yonedaGrp (C := C)).obj (Grp.mk G) := by
  let A := normalConjugation i j
  letI := A.semidirectProductGrpObj
  exact
    { app := fun X ↦ GrpCat.ofHom (normalSemidirectMulPointHom i j (unop X))
      naturality := by
        intro Y Z f
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro x
        let x' : unop Y ⟶ N ⊗ H := x
        -- The two `GrpCat` composition wrappers have no application lemma, so expose their
        -- underlying precomposition maps before using the pointwise formula.
        change normalSemidirectMulPointHom i j (unop Z) (f.unop ≫ x') =
          f.unop ≫ normalSemidirectMulPointHom i j (unop Y) x'
        rw [normalSemidirectMulPointHom_apply i j x',
          normalSemidirectMulPointHom_apply]
        rw [comp_mul]
        simp only [Category.assoc] }

/-- Multiplication from the semidirect product determined by a normal subgroup map.

On generalized points this sends `(n, h)` to `i(n) * j(h)`. -/
noncomputable def normalSemidirectMul
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j] :
    let A := normalConjugation i j
    A.semidirectProduct ⟶ Grp.mk G := by
  let A := normalConjugation i j
  exact yonedaGrpFullyFaithful.preimage (normalSemidirectMulNatTrans i j)

/-- Normal semidirect multiplication sends a generalized point to the product of its two
ambient components. -/
@[simp]
theorem comp_normalSemidirectMul
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j]
    (x : X ⟶ N ⊗ H) :
    let A := normalConjugation i j
    letI := A.semidirectProductGrpObj
    x ≫ (normalSemidirectMul i j).hom.hom =
      (x ≫ fst N H ≫ i) * (x ≫ snd N H ≫ j) := by
  let A := normalConjugation i j
  let _ := A.semidirectProductGrpObj
  have h := congrArg (fun F ↦ F.app (op X) x)
    (yonedaGrpFullyFaithful.map_preimage (normalSemidirectMulNatTrans i j))
  exact h.trans (normalSemidirectMulPointHom_apply i j x)

/-- Normal semidirect multiplication restricts to the normal subgroup map on the first
canonical factor. -/
@[simp, reassoc]
theorem inl_comp_normalSemidirectMul
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j] :
    let A := normalConjugation i j
    A.inl ≫ normalSemidirectMul i j = Grp.ofHom i := by
  let A := normalConjugation i j
  let _ := A.semidirectProductGrpObj
  apply Grp.hom_ext
  have hleft := congrArg SemidirectProduct.left
    (A.pointMulEquiv_comp_inl (X := N) (𝟙 N))
  have hright := congrArg SemidirectProduct.right
    (A.pointMulEquiv_comp_inl (X := N) (𝟙 N))
  simp only [pointMulEquiv_left, pointMulEquiv_right, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, Category.id_comp] at hleft hright
  dsimp only [A] at hleft hright
  rw [Grp.comp_hom_hom, comp_normalSemidirectMul]
  rw [← Category.assoc, hleft, Category.id_comp]
  rw [← Category.assoc, hright, MonObj.one_comp]
  exact mul_one i

/-- Normal semidirect multiplication restricts to the second ambient map on the second canonical
factor. -/
@[simp, reassoc]
theorem inr_comp_normalSemidirectMul
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom j] :
    let A := normalConjugation i j
    A.inr ≫ normalSemidirectMul i j = Grp.ofHom j := by
  let A := normalConjugation i j
  let _ := A.semidirectProductGrpObj
  apply Grp.hom_ext
  have hleft := congrArg SemidirectProduct.left
    (A.pointMulEquiv_comp_inr (X := H) (𝟙 H))
  have hright := congrArg SemidirectProduct.right
    (A.pointMulEquiv_comp_inr (X := H) (𝟙 H))
  simp only [pointMulEquiv_left, pointMulEquiv_right, SemidirectProduct.left_inr,
    SemidirectProduct.right_inr, Category.id_comp] at hleft hright
  dsimp only [A] at hleft hright
  rw [Grp.comp_hom_hom, comp_normalSemidirectMul]
  rw [← Category.assoc, hleft, MonObj.one_comp]
  rw [← Category.assoc, hright, Category.id_comp]
  exact one_mul j

end TauCeti.GrpObj.Action
