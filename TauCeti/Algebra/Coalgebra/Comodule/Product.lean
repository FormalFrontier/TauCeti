/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# Products of comodules

This file equips the product of two right comodules over a fixed coalgebra with the direct-sum
coaction. For comodules `M` and `N`, the coaction on `M × N` is
`ρ(m, n) = (inl ⊗ id) (ρ m) + (inr ⊗ id) (ρ n)`.

The file also records that the four standard linear maps for a product,
`fst`, `snd`, `inl`, and `inr`, are comodule morphisms for this coaction. This is additive
infrastructure for the finite-dimensional comodule representation category in the
reductive-groups roadmap.

## Main declarations

* `TauCeti.Comodule.Prod`: the direct-sum comodule structure on `M × N`.
* `TauCeti.Comodule.prodFst`, `prodSnd`, `prodInl`, `prodInr`: the four canonical comodule
  morphisms.
* `TauCeti.ComoduleCat.prod`: the bundled product comodule, with projections, inclusions,
  `prodLift`, and `prodDesc`.

## References

This supplies a prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target
"Comodules over a coalgebra/Hopf algebra": the finite-dimensional comodule category should be an
additive category before tensor products, duals, and Tannakian reconstruction are built on top.
The construction is the standard direct sum of comodules; see Sweedler, *Hopf Algebras*,
Chapter 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type w} {N : Type x}
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The direct-sum coaction on the product of two comodules. -/
@[expose] def prodCoact : M × N →ₗ[R] (M × N) ⊗[R] C :=
  LinearMap.coprod
    ((TensorProduct.map (LinearMap.inl R M N) LinearMap.id) ∘ₗ
      coact (R := R) (C := C) (M := M))
    ((TensorProduct.map (LinearMap.inr R M N) LinearMap.id) ∘ₗ
      coact (R := R) (C := C) (M := N))

/-- The product coaction evaluated on a pair. -/
@[simp]
theorem prodCoact_apply (x : M × N) :
    prodCoact (R := R) (C := C) (M := M) (N := N) x =
      TensorProduct.map (LinearMap.inl R M N) LinearMap.id
          (coact (R := R) (C := C) (M := M) x.1) +
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id
          (coact (R := R) (C := C) (M := N) x.2) :=
  rfl

/-- The product coaction after the left inclusion. -/
theorem prodCoact_inl (m : M) :
    prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m) =
      TensorProduct.map (LinearMap.inl R M N) LinearMap.id
        (coact (R := R) (C := C) (M := M) m) := by
  simp [prodCoact]

/-- The product coaction after the right inclusion. -/
theorem prodCoact_inr (n : N) :
    prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n) =
      TensorProduct.map (LinearMap.inr R M N) LinearMap.id
        (coact (R := R) (C := C) (M := N) n) := by
  simp [prodCoact]

private theorem prodCoact_coassoc_map {P : Type*} [AddCommMonoid P] [Module R P]
    [Comodule R C P] (f : P →ₗ[R] M × N) (hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ f =
        TensorProduct.map f LinearMap.id ∘ₗ coact (R := R) (C := C) (M := P))
    (p : P) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (f p))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (f p)) := by
  have hcoact :
      prodCoact (R := R) (C := C) (M := M) (N := N) (f p) =
        TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := P) p) :=
    LinearMap.congr_fun hcomp p
  rw [hcoact]
  have h :=
    congrArg
      (TensorProduct.map f
        (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)))
      (coassoc_apply (R := R) (C := C) (M := P) p)
  rw [TensorProduct.map_map_assoc] at h
  -- This transports the coassociativity square across the compatible map `f`.
  simpa [LinearMap.rTensor_map, LinearMap.lTensor_map, hcomp] using h

private theorem prodCoact_coassoc_inl (m : M) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m)) := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inl R M N =
        TensorProduct.map (LinearMap.inl R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M) := by
    ext x
    simp
  exact prodCoact_coassoc_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inl R M N) hcomp m

private theorem prodCoact_coassoc_inr (n : N) :
    TensorProduct.assoc R (M × N) C C
        ((prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n))) =
      Coalgebra.comul.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n)) := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inr R M N =
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := N) := by
    ext x
    simp
  exact prodCoact_coassoc_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inr R M N) hcomp n

theorem prodCoact_coassoc :
    TensorProduct.assoc R (M × N) C C ∘ₗ
        (prodCoact (R := R) (C := C) (M := M) (N := N)).rTensor C ∘ₗ
          prodCoact (R := R) (C := C) (M := M) (N := N) =
      Coalgebra.comul.lTensor (M × N) ∘ₗ
        prodCoact (R := R) (C := C) (M := M) (N := N) := by
  apply LinearMap.prod_ext
  · ext m
    exact prodCoact_coassoc_inl (R := R) (C := C) (M := M) (N := N) m
  · ext n
    exact prodCoact_coassoc_inr (R := R) (C := C) (M := M) (N := N) n

omit [Comodule R C M] [Comodule R C N] in
private theorem counit_lTensor_prod_map {P : Type*} [AddCommMonoid P] [Module R P]
    (f : P →ₗ[R] M × N) (t : P ⊗[R] C) :
    Coalgebra.counit.lTensor (M × N) (TensorProduct.map f LinearMap.id t) =
      TensorProduct.map f LinearMap.id (Coalgebra.counit.lTensor P t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p c => simp
  | add x y hx hy => simp [hx, hy]

private theorem prodCoact_counit_map {P : Type*} [AddCommMonoid P] [Module R P]
    [Comodule R C P] (f : P →ₗ[R] M × N) (hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ f =
        TensorProduct.map f LinearMap.id ∘ₗ coact (R := R) (C := C) (M := P))
    (p : P) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (f p)) =
      f p ⊗ₜ[R] 1 := by
  have hcoact :
      prodCoact (R := R) (C := C) (M := M) (N := N) (f p) =
        TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := P) p) :=
    LinearMap.congr_fun hcomp p
  rw [hcoact]
  have h :=
    congrArg (TensorProduct.map f (LinearMap.id : R →ₗ[R] R))
      (lTensor_counit_coact (R := R) (C := C) (M := P) p)
  -- This transports the counit square across the compatible map `f`.
  rw [counit_lTensor_prod_map]
  rw [h]
  simp

private theorem prodCoact_counit_inl (m : M) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inl R M N m)) =
      LinearMap.inl R M N m ⊗ₜ[R] 1 := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inl R M N =
        TensorProduct.map (LinearMap.inl R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M) := by
    ext x
    simp
  exact prodCoact_counit_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inl R M N) hcomp m

private theorem prodCoact_counit_inr (n : N) :
    Coalgebra.counit.lTensor (M × N)
        (prodCoact (R := R) (C := C) (M := M) (N := N) (LinearMap.inr R M N n)) =
      LinearMap.inr R M N n ⊗ₜ[R] 1 := by
  have hcomp :
      prodCoact (R := R) (C := C) (M := M) (N := N) ∘ₗ LinearMap.inr R M N =
        TensorProduct.map (LinearMap.inr R M N) LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := N) := by
    ext x
    simp
  exact prodCoact_counit_map (R := R) (C := C) (M := M) (N := N)
    (LinearMap.inr R M N) hcomp n

theorem prodCoact_counit :
    Coalgebra.counit.lTensor (M × N) ∘ₗ
        prodCoact (R := R) (C := C) (M := M) (N := N) =
      (TensorProduct.mk R (M × N) R).flip 1 := by
  apply LinearMap.prod_ext
  · ext m
    exact prodCoact_counit_inl (R := R) (C := C) (M := M) (N := N) m
  · ext n
    exact prodCoact_counit_inr (R := R) (C := C) (M := M) (N := N) n

/-- The product of two right comodules, with the direct-sum coaction. -/
@[expose, implicit_reducible]
def Prod : Comodule R C (M × N) where
  coact := prodCoact (R := R) (C := C) (M := M) (N := N)
  coassoc := prodCoact_coassoc (R := R) (C := C) (M := M) (N := N)
  lTensor_counit_comp_coact := prodCoact_counit (R := R) (C := C) (M := M) (N := N)

-- Register `Prod` as a local instance for the rest of this file, so the product comodule
-- structure resolves automatically on `M × N` and need not be threaded through every statement
-- with `letI`. It is deliberately *not* a global instance: several comodule structures can live
-- on one carrier (e.g. `trivial`, `cofree`), so a global product instance would make `Comodule`
-- resolution non-confluent. This matches how `Comodule.trivial` is used in the matrix-coefficient
-- files.
attribute [local instance] Prod

/-- The coaction in `Comodule.Prod` is `Comodule.prodCoact`. -/
@[simp]
theorem Prod_coact :
    coact (R := R) (C := C) (M := M × N) =
      prodCoact (R := R) (C := C) (M := M) (N := N) :=
  rfl

/-- The first projection from the product comodule. -/
@[expose] def prodFst :
    Hom R C (M × N) M := by
  exact
      { toLinearMap := LinearMap.fst R M N
        map_coact := by
          apply LinearMap.prod_ext
          · ext m
            simp [TensorProduct.map_map]
          · ext n
            simp [prodCoact, TensorProduct.map_map] }

/-- The underlying linear map of the first projection from the product comodule. -/
@[simp]
theorem prodFst_toLinearMap : (prodFst (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.fst R M N :=
  rfl

/-- Evaluating the first projection from the product comodule returns the first component. -/
@[simp]
theorem prodFst_apply (x : M × N) :
    prodFst (R := R) (C := C) (M := M) (N := N) x = x.1 :=
  rfl

/-- The second projection from the product comodule. -/
@[expose] def prodSnd :
    Hom R C (M × N) N := by
  exact
      { toLinearMap := LinearMap.snd R M N
        map_coact := by
          apply LinearMap.prod_ext
          · ext m
            simp [prodCoact, TensorProduct.map_map]
          · ext n
            simp [TensorProduct.map_map] }

/-- The underlying linear map of the second projection from the product comodule. -/
@[simp]
theorem prodSnd_toLinearMap : (prodSnd (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.snd R M N :=
  rfl

/-- Evaluating the second projection from the product comodule returns the second component. -/
@[simp]
theorem prodSnd_apply (x : M × N) :
    prodSnd (R := R) (C := C) (M := M) (N := N) x = x.2 :=
  rfl

/-- The left inclusion into the product comodule. -/
@[expose] def prodInl :
    Hom R C M (M × N) := by
  exact
      { toLinearMap := LinearMap.inl R M N
        map_coact := by
          ext m
          simp }

/-- The underlying linear map of the left inclusion into the product comodule. -/
@[simp]
theorem prodInl_toLinearMap : (prodInl (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.inl R M N :=
  rfl

/-- Evaluating the left inclusion into the product comodule gives a pair with zero right
component. -/
@[simp]
theorem prodInl_apply (m : M) :
    prodInl (R := R) (C := C) (M := M) (N := N) m = (m, 0) :=
  rfl

/-- The right inclusion into the product comodule. -/
@[expose] def prodInr :
    Hom R C N (M × N) := by
  exact
      { toLinearMap := LinearMap.inr R M N
        map_coact := by
          ext n
          simp }

/-- The underlying linear map of the right inclusion into the product comodule. -/
@[simp]
theorem prodInr_toLinearMap : (prodInr (R := R) (C := C) (M := M) (N := N)).toLinearMap =
      LinearMap.inr R M N :=
  rfl

/-- Evaluating the right inclusion into the product comodule gives a pair with zero left
component. -/
@[simp]
theorem prodInr_apply (n : N) :
    prodInr (R := R) (C := C) (M := M) (N := N) n = (0, n) :=
  rfl

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
private theorem prodLeft_map_prod {P : Type*} [AddCommMonoid P] [Module R P]
    (f : P →ₗ[R] M) (g : P →ₗ[R] N) (t : P ⊗[R] C) :
    TensorProduct.prodLeft R R M N C
        (TensorProduct.map (f.prod g) LinearMap.id t) =
      (TensorProduct.map f LinearMap.id t, TensorProduct.map g LinearMap.id t) := by
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext <;> simp
  · intro p c
    rfl
  · intro t u ht hu
    simp [ht, hu]

/-- The product morphism induced by two morphisms with a common source. -/
@[expose] def prodLift {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C P M) (g : Hom R C P N) :
    Hom R C P (M × N) := by
  exact
    { toLinearMap := f.toLinearMap.prod g.toLinearMap
      map_coact := by
        ext p
        apply (TensorProduct.prodLeft R R M N C).injective
        simp [prodCoact, prodLeft_map_prod, LinearMap.inl, LinearMap.inr,
          Hom.map_coact_apply] }

/-- The underlying linear map of `Comodule.prodLift`. -/
@[simp]
theorem prodLift_toLinearMap {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C P M) (g : Hom R C P N) :
    (prodLift (R := R) (C := C) (M := M) (N := N) f g).toLinearMap =
      f.toLinearMap.prod g.toLinearMap :=
  rfl

/-- Evaluating `Comodule.prodLift` gives the pair of evaluations. -/
@[simp]
theorem prodLift_apply {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C P M) (g : Hom R C P N) (p : P) :
    prodLift (R := R) (C := C) (M := M) (N := N) f g p = (f p, g p) :=
  rfl

/-- The product morphism induced by two morphisms with a common target. -/
@[expose] def prodDesc {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C M P) (g : Hom R C N P) :
    Hom R C (M × N) P := by
  exact
    { toLinearMap := LinearMap.coprod f.toLinearMap g.toLinearMap
      map_coact := by
        apply LinearMap.prod_ext
        · ext m
          simp [prodCoact, TensorProduct.map_map, Hom.map_coact_apply, map_zero]
        · ext n
          simp [prodCoact, TensorProduct.map_map, Hom.map_coact_apply, map_zero] }

/-- The underlying linear map of `Comodule.prodDesc`. -/
@[simp]
theorem prodDesc_toLinearMap {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C M P) (g : Hom R C N P) :
    (prodDesc (R := R) (C := C) (M := M) (N := N) f g).toLinearMap =
      LinearMap.coprod f.toLinearMap g.toLinearMap :=
  rfl

/-- Evaluating `Comodule.prodDesc` adds the evaluations of its two components. -/
@[simp]
theorem prodDesc_apply {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : Hom R C M P) (g : Hom R C N P) (x : M × N) :
    prodDesc (R := R) (C := C) (M := M) (N := N) f g x = f x.1 + g x.2 :=
  rfl

end Comodule

namespace ComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The product of two bundled comodules, carried by the product of the underlying modules. -/
abbrev prod (M N : ComoduleCat.{u, v, w} R C) : ComoduleCat.{u, v, w} R C where
  carrier := M × N
  instComodule := Comodule.Prod (R := R) (C := C) (M := M) (N := N)

variable {R C}

/-- The first projection from the bundled product comodule. -/
abbrev prodFst (M N : ComoduleCat.{u, v, w} R C) : prod R C M N ⟶ M :=
  Comodule.prodFst (R := R) (C := C) (M := M) (N := N)

/-- The second projection from the bundled product comodule. -/
abbrev prodSnd (M N : ComoduleCat.{u, v, w} R C) : prod R C M N ⟶ N :=
  Comodule.prodSnd (R := R) (C := C) (M := M) (N := N)

/-- The morphism into the bundled product induced by a pair of morphisms. -/
abbrev prodLift {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prod R C M N :=
  Comodule.prodLift (R := R) (C := C) (M := M) (N := N) f g

/-- The left inclusion into the bundled product comodule. -/
abbrev prodInl (M N : ComoduleCat.{u, v, w} R C) : M ⟶ prod R C M N :=
  Comodule.prodInl (R := R) (C := C) (M := M) (N := N)

/-- The right inclusion into the bundled product comodule. -/
abbrev prodInr (M N : ComoduleCat.{u, v, w} R C) : N ⟶ prod R C M N :=
  Comodule.prodInr (R := R) (C := C) (M := M) (N := N)

/-- The morphism out of the bundled product induced by a pair of morphisms. -/
abbrev prodDesc {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prod R C M N ⟶ P :=
  Comodule.prodDesc (R := R) (C := C) (M := M) (N := N) f g

/-- Evaluating the bundled first projection returns the first component. -/
@[simp]
theorem prodFst_apply (M N : ComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodFst M N x = x.1 :=
  rfl

/-- Evaluating the bundled second projection returns the second component. -/
@[simp]
theorem prodSnd_apply (M N : ComoduleCat.{u, v, w} R C) (x : prod R C M N) :
    prodSnd M N x = x.2 :=
  rfl

/-- Evaluating the bundled product lift gives the pair of evaluations. -/
@[simp]
theorem prodLift_apply {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) (p : P) :
    prodLift f g p = (f p, g p) :=
  rfl

/-- Evaluating the bundled left inclusion gives a pair with zero right component. -/
@[simp]
theorem prodInl_apply (M N : ComoduleCat.{u, v, w} R C) (m : M) :
    prodInl M N m = (m, 0) :=
  rfl

/-- Evaluating the bundled right inclusion gives a pair with zero left component. -/
@[simp]
theorem prodInr_apply (M N : ComoduleCat.{u, v, w} R C) (n : N) :
    prodInr M N n = (0, n) :=
  rfl

/-- Evaluating the bundled product desc adds the evaluations of its two components. -/
@[simp]
theorem prodDesc_apply {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P)
    (x : prod R C M N) :
    prodDesc f g x = f x.1 + g x.2 :=
  rfl

/-- The first projection after the bundled product lift is the first morphism. -/
@[simp]
theorem prodLift_fst {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f := by
  ext p
  rfl

/-- The second projection after the bundled product lift is the second morphism. -/
@[simp]
theorem prodLift_snd {P M N : ComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g := by
  ext p
  rfl

/-- The bundled product desc after the left inclusion is the first morphism. -/
@[simp]
theorem prodInl_desc {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prodInl M N ≫ prodDesc f g = f := by
  ext m
  rw [comp_apply, prodDesc_apply, prodInl_apply]
  have hg0 : g 0 = 0 := map_zero g.toLinearMap
  rw [hg0, add_zero]

/-- The bundled product desc after the right inclusion is the second morphism. -/
@[simp]
theorem prodInr_desc {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ P) (g : N ⟶ P) :
    prodInr M N ≫ prodDesc f g = g := by
  ext n
  rw [comp_apply, prodDesc_apply, prodInr_apply]
  have hf0 : f 0 = 0 := map_zero f.toLinearMap
  rw [hf0, zero_add]

/-- The first projection after the left inclusion is the identity. -/
@[simp]
theorem prodInl_fst (M N : ComoduleCat.{u, v, w} R C) :
    prodInl M N ≫ prodFst M N = 𝟙 M := by
  ext m
  rfl

/-- The second projection after the left inclusion is zero. -/
@[simp]
theorem prodInl_snd (M N : ComoduleCat.{u, v, w} R C) :
    prodInl M N ≫ prodSnd M N = 0 := by
  ext m
  rfl

/-- The first projection after the right inclusion is zero. -/
@[simp]
theorem prodInr_fst (M N : ComoduleCat.{u, v, w} R C) :
    prodInr M N ≫ prodFst M N = 0 := by
  ext n
  rfl

/-- The second projection after the right inclusion is the identity. -/
@[simp]
theorem prodInr_snd (M N : ComoduleCat.{u, v, w} R C) :
    prodInr M N ≫ prodSnd M N = 𝟙 N := by
  ext n
  rfl

/-- The two projection-inclusion composites reconstruct the identity of the bundled product. -/
@[simp]
theorem prod_fst_inl_add_snd_inr (M N : ComoduleCat.{u, v, w} R C) :
    prodFst M N ≫ prodInl M N + prodSnd M N ≫ prodInr M N = 𝟙 (prod R C M N) := by
  apply hom_ext
  intro x
  rw [add_apply, comp_apply, comp_apply, prodInl_apply, prodInr_apply, prodFst_apply,
    prodSnd_apply, id_apply]
  ext <;> simp

/-- Morphisms into the bundled product are determined by their projections. -/
@[ext]
theorem prod_hom_ext {P M N : ComoduleCat.{u, v, w} R C} {f g : P ⟶ prod R C M N}
    (hfst : f ≫ prodFst M N = g ≫ prodFst M N)
    (hsnd : f ≫ prodSnd M N = g ≫ prodSnd M N) : f = g := by
  apply hom_ext
  intro p
  have hfstp : prodFst M N (f p) = prodFst M N (g p) := by
    simpa only [comp_apply] using congrArg (fun h : P ⟶ M => h p) hfst
  have hsndp : prodSnd M N (f p) = prodSnd M N (g p) := by
    simpa only [comp_apply] using congrArg (fun h : P ⟶ N => h p) hsnd
  rw [prodFst_apply] at hfstp
  rw [prodSnd_apply] at hsndp
  exact Prod.ext hfstp hsndp

/-- Morphisms out of the bundled product are determined by their values on the inclusions. -/
@[ext]
theorem prod_hom_ext' {M N P : ComoduleCat.{u, v, w} R C} {f g : prod R C M N ⟶ P}
    (hinl : prodInl M N ≫ f = prodInl M N ≫ g)
    (hinr : prodInr M N ≫ f = prodInr M N ≫ g) : f = g := by
  letI : Comodule R C (M × N) := Comodule.Prod (R := R) (C := C) (M := M) (N := N)
  apply hom_ext
  intro x
  have hinlp : f (prodInl M N x.1) = g (prodInl M N x.1) := by
    simpa only [comp_apply] using congrArg (fun h : M ⟶ P => h x.1) hinl
  have hinrp : f (prodInr M N x.2) = g (prodInr M N x.2) := by
    simpa only [comp_apply] using congrArg (fun h : N ⟶ P => h x.2) hinr
  rw [prodInl_apply] at hinlp
  rw [prodInr_apply] at hinrp
  have hx : x = (x.1, 0) + (0, x.2) := by
    ext <;> simp
  have hlin : f.toLinearMap x = g.toLinearMap x := by
    calc
      f.toLinearMap x = f.toLinearMap ((x.1, 0) + (0, x.2)) :=
        congrArg f.toLinearMap hx
      _ = f.toLinearMap (x.1, 0) + f.toLinearMap (0, x.2) := by
        rw [map_add]
      _ = g.toLinearMap (x.1, 0) + g.toLinearMap (0, x.2) :=
        congrArg₂ (fun a b => a + b) hinlp hinrp
      _ = g.toLinearMap ((x.1, 0) + (0, x.2)) := by
        rw [map_add]
      _ = g.toLinearMap x := congrArg g.toLinearMap hx.symm
  exact hlin

end ComoduleCat

end TauCeti
