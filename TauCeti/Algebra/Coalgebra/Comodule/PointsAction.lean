/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial
public import TauCeti.LinearAlgebra.End.ScalarExtension
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.End.ScalarExtension

/-!
# The points action of a comodule

A right comodule `V` over a bialgebra `H` makes the `A`-points of `H` — those of the
corresponding affine monoid scheme, when `H` is commutative — act on the scalar
extension `A ⊗[R] V`: a point `g : H →ₐ[R] A` acts by
pushing the coaction coefficients through `g`, `A`-linearly. The two comodule axioms
are exactly the two monoid-action laws: the counit law sends the convolution unit to
the identity, and coassociativity sends convolution products to composites. (The
upgrade to automorphisms over a Hopf algebra is in
`TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction`, with the group of
points.) On the comodule attached to a group-like element `x`, this action is scalar
multiplication by `g x`.

This is the comodule-to-representation direction of the "representations = comodules"
dictionary (ReductiveGroups roadmap, Layer 1): it realizes a comodule as an action of
the functor of points on scalar extensions of `V`.

## Main declarations

* `TauCeti.Comodule.endOfPoint`: the endomorphism of `A ⊗[R] V` attached to a point.
* `TauCeti.Comodule.endOfPoint_corestrict`: compatibility with corestriction in the coalgebra.
* `TauCeti.Comodule.endOfPoint_tensor`: point actions preserve the diagonal tensor product.
* `TauCeti.Comodule.endOfPoint_groupLike`: on a group-like comodule a point acts by the scalar
  given by its value on the group-like element.
* `TauCeti.Comodule.endOfPoint_trivial`: every point acts identically on a trivial comodule.
* `TauCeti.Comodule.pointsRepresentation`: the action, as a `Representation` of the
  convolution monoid of points on the scalar extension.
* `TauCeti.Comodule.baseChange_comp_endOfPoint`: the action is functorial in the
  comodule.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.1–3.2.
* J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4, for the tensor and unit
  compatibility of point actions.
-/

public section

namespace TauCeti

namespace Comodule

open Coalgebra WithConv TensorProduct

section Coalgebra

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Coalgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

variable (V) in
/-- The endomorphism of the scalar extension `A ⊗[R] V` attached to an `A`-point:
push the coaction coefficients through the point. Only the coalgebra structure of `H`
enters; the bialgebra compatibility is needed for the action laws, not the map. -/
noncomputable def endOfPoint (g : H →ₐ[R] A) : A ⊗[R] V →ₗ[A] A ⊗[R] V :=
  LinearMap.liftBaseChange A
    ((TensorProduct.comm R V A).toLinearMap ∘ₗ
      LinearMap.lTensor V g.toLinearMap ∘ₗ coact (R := R) (C := H))

variable (V) in
@[simp]
lemma endOfPoint_tmul (g : H →ₐ[R] A) (a : A) (v : V) :
    endOfPoint V g (a ⊗ₜ[R] v) =
      a • TensorProduct.comm R V A (LinearMap.lTensor V g.toLinearMap (coact v)) := by
  simp [endOfPoint]

section BaseChange

variable {A' : Type*} [CommSemiring A'] [Algebra R A']

variable (V) in
/-- Base-change compatibility of the action: pushing a point forward along a morphism
of value algebras and acting agrees with acting first and then extending scalars.
Stated on the underlying `R`-linear maps, where both composites live. -/
lemma rTensor_comp_endOfPoint (φ : A →ₐ[R] A') (g : H →ₐ[R] A) :
    LinearMap.rTensor V φ.toLinearMap ∘ₗ (endOfPoint V g).restrictScalars R =
      (endOfPoint V (φ.comp g)).restrictScalars R ∘ₗ
        LinearMap.rTensor V φ.toLinearMap := by
  have hcol : LinearMap.rTensor V φ.toLinearMap ∘ₗ
      (TensorProduct.comm R V A).toLinearMap ∘ₗ LinearMap.lTensor V g.toLinearMap =
      (TensorProduct.comm R V A').toLinearMap ∘ₗ
        LinearMap.lTensor V (φ.comp g).toLinearMap := by
    refine TensorProduct.ext' fun w x => ?_
    simp
  refine TensorProduct.ext' fun a v => ?_
  have hc := DFunLike.congr_fun hcol (coact (R := R) (C := H) v)
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_toLinearMap] at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.rTensor_tmul, endOfPoint_tmul, rTensor_algHom_smul, hc, AlgHom.toLinearMap_apply]

end BaseChange

section Functorial

variable {W : Type*} [AddCommMonoid W] [Module R W] [Comodule R H W]

/-- Scalar extension of a comodule morphism intertwines the point actions: the action
is functorial in the comodule. -/
lemma baseChange_comp_endOfPoint (f : Hom R H V W) (g : H →ₐ[R] A) :
    f.toLinearMap.baseChange A ∘ₗ endOfPoint V g =
      endOfPoint W g ∘ₗ f.toLinearMap.baseChange A := by
  have hcol : (f.toLinearMap.baseChange A).restrictScalars R ∘ₗ
      (TensorProduct.comm R V A).toLinearMap ∘ₗ LinearMap.lTensor V g.toLinearMap =
      (TensorProduct.comm R W A).toLinearMap ∘ₗ LinearMap.lTensor W g.toLinearMap ∘ₗ
        TensorProduct.map f.toLinearMap LinearMap.id := by
    refine TensorProduct.ext' fun w x => ?_
    simp
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a v => ?_
  have hc := DFunLike.congr_fun hcol (coact (R := R) (C := H) v)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap] at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    endOfPoint_tmul, map_smul, LinearMap.baseChange_tmul, hc, Hom.map_coact_apply,
    Hom.coe_toLinearMap]

end Functorial

end Coalgebra

section Corestrict

variable {R H₁ H₂ V A : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [Bialgebra R H₁] [Bialgebra R H₂]
variable [AddCommMonoid V] [Module R V] [Comodule R H₁ V]
variable [CommSemiring A] [Algebra R A]

/-- Acting on a comodule corestricted along a bialgebra morphism agrees with acting by the
point precomposed with the underlying algebra morphism. -/
@[simp]
theorem endOfPoint_corestrict (φ : H₁ →ₐc[R] H₂) (g : H₂ →ₐ[R] A) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     endOfPoint V g) = endOfPoint V (g.comp (φ : H₁ →ₐ[R] H₂)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  rw [endOfPoint_tmul, endOfPoint_tmul]
  simp only [corestrict_coact_apply, AlgHom.comp_toLinearMap]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
  have hφ : φ.toCoalgHom.toLinearMap = (φ : H₁ →ₐ[R] H₂).toLinearMap :=
    (_root_.BialgHom.toAlgHom_toLinearMap φ).symm
  simp only [LinearMap.lTensor_def, hφ]

end Corestrict

section GroupLike

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Coalgebra R H]
  [AddCommMonoid V] [Module R V] [CommSemiring A] [Algebra R A]

/-- On a group-like comodule, a point acts by scalar multiplication by its value on the
group-like element. -/
@[simp]
theorem endOfPoint_groupLike (x : GroupLike R H) (g : H →ₐ[R] A) :
    letI : Comodule R H V := groupLike (R := R) (C := H) (M := V) x
    endOfPoint V g = g x • LinearMap.id := by
  let _ : Comodule R H V := groupLike (R := R) (C := H) (M := V) x
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a v ↦ ?_
  simp only [LinearMap.restrictScalars_apply, endOfPoint_tmul, groupLike_coact_apply,
    LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', smul_eq_mul]
  rw [mul_comm]

end GroupLike

section Bialgebra

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

section Tensor

variable {W : Type*} [AddCommMonoid W] [Module R W] [Comodule R H W]

/-- On pure tensors, acting separately on two comodules and applying the scalar-extension
tensor comparison agrees with acting on any tensor-product comodule whose coaction is the
diagonal one. -/
theorem endOfPoint_tensor_tmul_of_coact_eq [Comodule R H (V ⊗[R] W)]
    (hcoact : coact (R := R) (C := H) (M := V ⊗[R] W) =
      tensorCoact (R := R) (C := H) (M := V) (N := W))
    (g : H →ₐ[R] A) (a b : A) (v : V) (w : W) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        (endOfPoint V g (a ⊗ₜ[R] v) ⊗ₜ[A] endOfPoint W g (b ⊗ₜ[R] w)) =
      endOfPoint (V ⊗[R] W) g ((a * b) ⊗ₜ[R] (v ⊗ₜ[R] w)) := by
  rw [endOfPoint_tmul, endOfPoint_tmul, endOfPoint_tmul, hcoact, tensorCoact_tmul]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  rw [mul_comm b a, ← TensorProduct.smul_tmul', map_smul]
  congr 1
  have h := LinearMap.congr_fun
    (lTensor_comp_tensorCombine (R := R) (C := H) (D := A) (M := V) (N := W) g)
    (coact (R := R) (C := H) (M := V) v ⊗ₜ[R] coact (R := R) (C := H) (M := W) w)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul] at h
  rw [h]
  exact (comm_tensorCombine_eq_distribBaseChange_symm_tmul
    (R := R) (A := A) (M := V) (N := W) _ _).symm

/-- A point action preserves tensor products. Under the canonical comparison
`(A ⊗ M) ⊗[A] (A ⊗ N) ≃ A ⊗ (M ⊗ N)`, acting on the two factors separately
equals acting on any tensor-product comodule whose coaction is the diagonal one. -/
theorem endOfPoint_tensor_of_coact_eq [Comodule R H (V ⊗[R] W)]
    (hcoact : coact (R := R) (C := H) (M := V ⊗[R] W) =
      tensorCoact (R := R) (C := H) (M := V) (N := W)) (g : H →ₐ[R] A) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm.toLinearMap ∘ₗ
        TensorProduct.map (endOfPoint V g) (endOfPoint W g) =
      endOfPoint (V ⊗[R] W) g ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [TensorProduct.zero_tmul, map_zero, map_zero]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add]
      exact congrArg₂ (fun a b ↦ a + b) hx₁ hx₂
  | tmul a v =>
      induction y using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add]
          exact congrArg₂ (fun p q ↦ p + q) hy₁ hy₂
      | tmul b w =>
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe]
          rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
          exact endOfPoint_tensor_tmul_of_coact_eq hcoact g a b v w

attribute [local instance] tensor

/-- On pure tensors, acting separately on two comodules and applying the scalar-extension
tensor comparison agrees with acting on their diagonal tensor-product comodule. -/
theorem endOfPoint_tensor_tmul (g : H →ₐ[R] A) (a b : A) (v : V) (w : W) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        (endOfPoint V g (a ⊗ₜ[R] v) ⊗ₜ[A] endOfPoint W g (b ⊗ₜ[R] w)) =
      endOfPoint (V ⊗[R] W) g ((a * b) ⊗ₜ[R] (v ⊗ₜ[R] w)) :=
  endOfPoint_tensor_tmul_of_coact_eq tensor_coact g a b v w

/-- A point action preserves the diagonal tensor product of two comodules. -/
theorem endOfPoint_tensor (g : H →ₐ[R] A) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm.toLinearMap ∘ₗ
        TensorProduct.map (endOfPoint V g) (endOfPoint W g) =
      endOfPoint (V ⊗[R] W) g ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm.toLinearMap :=
  endOfPoint_tensor_of_coact_eq tensor_coact g

end Tensor

variable (V) in
/-- The convolution unit acts as the identity: the counit law of the comodule. -/
@[simp]
lemma endOfPoint_convOne :
    endOfPoint V ((1 : WithConv (H →ₐ[R] A)).ofConv) = LinearMap.id := by
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a v => ?_
  have hlin : ((1 : WithConv (H →ₐ[R] A)).ofConv).toLinearMap =
      Algebra.linearMap R A ∘ₗ counit := by
    have h := AlgHom.toLinearMap_convOne (R := R) (C := H) (A := A)
    rw [LinearMap.convOne_def] at h
    exact toConv_injective h
  have hcomp : LinearMap.lTensor V ((1 : WithConv (H →ₐ[R] A)).ofConv).toLinearMap ∘ₗ
      coact (R := R) (C := H) =
      LinearMap.lTensor V (Algebra.linearMap R A) ∘ₗ (TensorProduct.mk R V R).flip 1 := by
    rw [hlin, LinearMap.lTensor_comp, LinearMap.comp_assoc, lTensor_counit_comp_coact]
  have hv := DFunLike.congr_fun hcomp v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
    map_one] at hv
  simp [endOfPoint_tmul, hv, TensorProduct.smul_tmul', smul_eq_mul]

omit [Comodule R H V] in
/-- The coact-free shuffle underlying `endOfPoint_convMul`: with the two coaction
columns already peeled off, the two ways of multiplying the pushed coefficients agree,
by commutativity of the value algebra. -/
private lemma shuffle (g h : WithConv (H →ₐ[R] A)) :
    (TensorProduct.lift ((Algebra.lsmul R R (A ⊗[R] V)).toLinearMap)).comp
        ((TensorProduct.comm R (A ⊗[R] V) A).toLinearMap.comp
          ((TensorProduct.map (TensorProduct.comm R V A).toLinearMap LinearMap.id).comp
            ((TensorProduct.map (LinearMap.lTensor V (g.ofConv).toLinearMap)
                LinearMap.id).comp
              (LinearMap.lTensor (V ⊗[R] H) (h.ofConv).toLinearMap)))) =
      (TensorProduct.comm R V A).toLinearMap.comp
        ((LinearMap.lTensor V (LinearMap.mul' R A)).comp
          ((LinearMap.lTensor V
              (TensorProduct.map (g.ofConv).toLinearMap (h.ofConv).toLinearMap)).comp
            (TensorProduct.assoc R V H H).toLinearMap)) := by
  refine TensorProduct.ext (TensorProduct.ext' fun w x => LinearMap.ext fun y => ?_)
  simp [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

/-- Restricting the endomorphism of a point along the flip is scalar collapse against
the one-column form of the action: the pure-tensor characterization of `endOfPoint`,
as a composite. -/
private lemma endOfPoint_comp_comm (g : WithConv (H →ₐ[R] A)) :
    (endOfPoint V g.ofConv).restrictScalars R ∘ₗ (TensorProduct.comm R V A).toLinearMap =
      (TensorProduct.lift ((Algebra.lsmul R R (A ⊗[R] V)).toLinearMap)).comp
        ((TensorProduct.comm R (A ⊗[R] V) A).toLinearMap.comp
          (TensorProduct.map
            ((TensorProduct.comm R V A).toLinearMap.comp
              ((LinearMap.lTensor V (g.ofConv).toLinearMap).comp
                (coact (R := R) (C := H))))
            LinearMap.id)) := by
  refine TensorProduct.ext' fun w c => ?_
  simp [endOfPoint_tmul, Algebra.lsmul_coe]

variable (V) in
/-- Convolution products act as composites: the coassociativity law of the comodule. -/
@[simp]
lemma endOfPoint_convMul (g h : WithConv (H →ₐ[R] A)) :
    endOfPoint V ((g * h).ofConv) = endOfPoint V g.ofConv ∘ₗ endOfPoint V h.ofConv := by
  have hmul : ((g * h).ofConv).toLinearMap =
      LinearMap.mul' R A ∘ₗ
        TensorProduct.map (g.ofConv).toLinearMap (h.ofConv).toLinearMap ∘ₗ comul := by
    have hb := AlgHom.toLinearMap_convMul g h
    rw [LinearMap.convMul_def] at hb
    exact toConv_injective hb
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a v => ?_
  -- the endomorphism of the point `g`, evaluated on the flip of the `h`-column
  have c1 := DFunLike.congr_fun (endOfPoint_comp_comm (V := V) g)
    (LinearMap.lTensor V (h.ofConv).toLinearMap (coact (R := R) (C := H) v))
  -- peel the coaction column off the `g`-leg: a composite of Mathlib's tensor-map
  -- composition lemmas
  have c2 := DFunLike.congr_fun (show
      TensorProduct.map
          ((TensorProduct.comm R V A).toLinearMap.comp
            ((LinearMap.lTensor V (g.ofConv).toLinearMap).comp (coact (R := R) (C := H))))
          LinearMap.id ∘ₗ
        LinearMap.lTensor V (h.ofConv).toLinearMap =
      (TensorProduct.map (TensorProduct.comm R V A).toLinearMap LinearMap.id).comp
          ((TensorProduct.map (LinearMap.lTensor V (g.ofConv).toLinearMap)
              LinearMap.id).comp
            (LinearMap.lTensor (V ⊗[R] H) (h.ofConv).toLinearMap)) ∘ₗ
        (coact (R := R) (C := H) (M := V)).rTensor H from by
    -- Assembled from the tensor-map composition lemmas (`map_comp`, `lTensor_def`,
    -- `rTensor_def`); stated inline as a `show` because it is single-use, and the goal
    -- is not otherwise reachable by rewriting: the composite must be produced before
    -- it can be evaluated at the opaque coaction value below.
    simp only [LinearMap.lTensor_def, LinearMap.rTensor_def, ← TensorProduct.map_comp,
      LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_assoc])
    (coact (R := R) (C := H) v)
  -- the coact-free shuffle at the doubled coaction
  have c3 := DFunLike.congr_fun (shuffle (V := V) g h)
    ((coact (R := R) (C := H) (M := V)).rTensor H (coact (R := R) (C := H) v))
  -- coassociativity, valuewise
  have c4 := DFunLike.congr_fun (coassoc (R := R) (C := H) (M := V)) v
  -- fold the convolution product back together, valuewise at the coaction
  have c5 := DFunLike.congr_fun
    (congrArg (LinearMap.lTensor V) hmul) (coact (R := R) (C := H) v)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap] at c1 c2 c3 c4 c5
  rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at c5
  simp only [LinearMap.coe_comp, Function.comp_apply] at c5
  simp only [LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
    endOfPoint_tmul, map_smul, c1, c2, c3, c4, c5]

variable (V) in
/-- The points action of a comodule, as a representation of the convolution monoid of
points on the scalar extension. -/
noncomputable def pointsRepresentation :
    Representation A (WithConv (H →ₐ[R] A)) (A ⊗[R] V) where
  toFun g := endOfPoint V g.ofConv
  map_one' := endOfPoint_convOne V
  map_mul' g h := endOfPoint_convMul V g h

variable (V) in
@[simp]
lemma pointsRepresentation_apply (g : WithConv (H →ₐ[R] A)) :
    pointsRepresentation V g = endOfPoint V g.ofConv := by
  -- `pointsRepresentation` has no equation lemma to rewrite with; `change` spells out
  -- its definitional unfolding once, explicitly.
  change endOfPoint V g.ofConv = _
  rfl

end Bialgebra

section Trivial

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [AddCommMonoid V] [Module R V] [CommSemiring A] [Algebra R A]

attribute [local instance] trivial

/-- Every point acts as the identity on a trivial comodule. -/
theorem endOfPoint_trivial (g : H →ₐ[R] A) : endOfPoint V g = LinearMap.id := by
  simp only [endOfPoint_groupLike, GroupLike.val_one, map_one, one_smul]

end Trivial

end Comodule

end TauCeti
