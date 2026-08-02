/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Basic
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RepresentationTheory.Basic

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
points.)

This is the comodule-to-representation direction of the "representations = comodules"
dictionary (ReductiveGroups roadmap, Layer 1): it realizes a comodule as an action of
the functor of points on scalar extensions of `V`.

## Main declarations

* `TauCeti.Comodule.endOfPoint`: the endomorphism of `A ⊗[R] V` attached to a point.
* `TauCeti.Comodule.pointsRepresentation`: the action, as a `Representation` of the
  convolution monoid of points on the scalar extension.
* `TauCeti.Comodule.baseChange_comp_endOfPoint`: the action is functorial in the
  comodule.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.1–3.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4.
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
  have hsmul : ∀ (a : A) (z : A ⊗[R] V),
      LinearMap.rTensor V φ.toLinearMap (a • z) =
        φ a • LinearMap.rTensor V φ.toLinearMap z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x v => simp [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add x y hx hy => simp [smul_add, hx, hy]
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
    LinearMap.rTensor_tmul, endOfPoint_tmul, hsmul, hc, AlgHom.toLinearMap_apply]

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

section Bialgebra

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

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

end Comodule

end TauCeti
