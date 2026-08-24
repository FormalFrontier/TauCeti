/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Surjectivity of `Point.toClass`

Mathlib builds `WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup
W.CoordinateRing)` and proves it **injective**, realising the points of an affine Weierstrass
curve as a subgroup of the affine ideal class group. It does not prove surjectivity; this file
proves it by an explicit genus-one Riemann--Roch argument in the affine
coordinate ring.

It first records what surjectivity amounts to: every ideal class is trivial or the class of an
`XYIdeal'` at a nonsingular affine point. It then proves that statement.

## Main results

* `WeierstrassCurve.Affine.Point.toClass_surjective_iff`: `toClass` is surjective exactly when
  every element of `ClassGroup W.CoordinateRing` is trivial or the class of `XYIdeal' h` for a
  nonsingular affine point.
* `WeierstrassCurve.Affine.Point.toClass_surjective`: `toClass` is surjective.
* `WeierstrassCurve.Affine.Point.toClassEquiv`: the resulting additive equivalence between the
  point group and the ideal class group.

## What this is, mathematically

The right-hand side is stated for an arbitrary affine Weierstrass curve; nothing here assumes
smoothness or ellipticity, and no divisor group occurs.

On a smooth genus-1 curve, and under the identification of the affine ideal class group with
degree-zero divisor classes, it becomes the familiar divisor-reduction statement — every such
class is `(P) - (O)` for a rational point `P`. That is the reading which motivates recording the
equivalence, since it turns "prove `toClass` is surjective" into the form the geometric proof
takes; but it is an interpretation under extra hypotheses, not the content of the statement.

The formal equivalence and its proof carry no ellipticity hypothesis. In particular, the
subsequent proof shows that the required invertible ideals cannot occur at singular equation
solutions. No named representability predicate is introduced because
`Function.Surjective` already names the property consumers need.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at the
roadmap's HasseWeil pin `dev/hasse-weil @ 513e83879e2f`, file
`HasseWeil/Pic0/ToClassSurjective.lean` (by Chris Birkbeck). The source states the equivalence
through a named `ClassRepresentableByPoints` predicate, with the two directions as
`toClass_surjective_of_classRepresentableByPoints` and
`classRepresentableByPoints_of_toClass_surjective`; here they are one `iff` with the disjunction
spelled out, so no name is carried over.

The proof ports the source's concrete Riemann--Roch argument while reusing Tau Ceti's existing
`CoordinateRing.finrank_quotient_eq_one_iff` in place of the source's duplicate codimension-one
classification.

The mathematical argument is the affine ideal-class construction of Silverman,
*The Arithmetic of Elliptic Curves*, III.3.4--5.

`Point.toClass_surjective` and `toClassEquiv` are **also** components of D. Angdinata's in-flight
upstream `CoordinateRing` split-out, which `TauCetiRoadmap/EllipticCurves/README.md:1095` lists at
this same hypothesis strength — that bullet's "no ellipticity hypothesis" phrase describes his
split-out, not the AINTLIB source above, whose headline surjectivity theorem is elliptic. ⚠
mathlib-track: dedupe on landing.
-/

public section

open Polynomial Module WeierstrassCurve.Affine
open scoped nonZeroDivisors Polynomial.Bivariate Pointwise

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} [DecidableEq F]

/-- **Surjectivity of `toClass` is exactly representability of every ideal class by a point.**

`toClass` is surjective precisely when each element of `ClassGroup W.CoordinateRing` is either
trivial or the class of `XYIdeal' h` for a nonsingular affine point `(x, y)`. This records what
remains to be proved for full surjectivity.

Stated for an arbitrary affine Weierstrass curve: neither smoothness nor ellipticity is assumed,
and no divisor group appears. Under the hypotheses that make `W` a smooth genus-1 curve, and the
identification of `ClassGroup W.CoordinateRing` with degree-zero divisor classes, the right-hand
side reads as the familiar statement that every such class is `(P) - (O)` for a rational point
`P` — but that reading is an interpretation under extra hypotheses, not part of what is stated
here.

The disjunction is spelled out rather than named: `Function.Surjective` already expresses the
left-hand side, so a separate predicate would only add an unfolding layer for consumers to
cross. -/
theorem toClass_surjective_iff :
    Function.Surjective (toClass (W := W)) ↔ ∀ g : ClassGroup W.CoordinateRing,
      g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
        g = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h) := by
  constructor
  · intro hsurj g
    obtain ⟨P, hP⟩ := hsurj (Additive.ofMul g)
    cases P with
    | zero =>
        left
        rw [← zero_def, toClass_zero] at hP
        exact (Additive.ofMul.injective hP).symm
    | some x y h =>
        right
        refine ⟨x, y, h, ?_⟩
        rw [toClass_some] at hP
        exact (Additive.ofMul.injective hP).symm
  · intro hrep c
    obtain hg | ⟨x, y, h, hg⟩ := hrep (Additive.toMul c)
    · -- `ofMul_one` names the step `Additive.ofMul 1 = 0`, so the trivial branch closes without
      -- appealing to the type synonym at all.
      exact ⟨0, by rw [toClass_zero, ← ofMul_toMul c, hg, ofMul_one]⟩
    · refine ⟨some x y h, ?_⟩
      rw [toClass_some, ← ofMul_toMul c, hg]
      -- What is left is `g = Additive.ofMul g`. `Additive.ofMul` is `Equiv.refl` on the
      -- underlying type and Mathlib names no lemma for it at a general element, so this last
      -- step is the type synonym and nothing else.
      rfl

/-! ## The genus-one codimension argument -/

omit [DecidableEq F] in
/-- Every nonzero ideal of an affine Weierstrass coordinate ring has finite codimension over the
base field. -/
private theorem finiteDimensional_quotient_of_ne_bot
    (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    FiniteDimensional F (W.CoordinateRing ⧸ I) := by
  classical
  let hFin : ∀ i, Module.Finite F
      (F[X] ⧸ Ideal.span ({Ideal.smithCoeffs (CoordinateRing.basis W) I hI i} : Set F[X])) :=
    fun i => inferInstance
  exact Module.Finite.equiv
    (Ideal.quotientEquivDirectSum F (CoordinateRing.basis W) hI).symm

omit [DecidableEq F] in
/-- The integral numerator of an invertible fractional ideal is invertible. -/
private theorem isUnit_num
    {I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField} :
    IsUnit (I.num : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ↔ IsUnit I := by
  let R := W.CoordinateRing
  let K := W.FunctionField
  have hden0 : algebraMap R K I.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.prop
  let u : Kˣ := Units.mk0 (algebraMap R K I.den) hden0
  have hdenUnit : IsUnit (FractionalIdeal.spanSingleton R⁰ (algebraMap R K I.den)) :=
    ⟨toPrincipalIdeal R K u, by simp [u]⟩
  obtain ⟨c, hc⟩ := hdenUnit
  rw [← FractionalIdeal.den_mul_self_eq_num', ← hc, Units.isUnit_units_mul]

omit [DecidableEq F] in
/-- Replacing an invertible fractional ideal by its integral numerator does not change its ideal
class. -/
private theorem mk_num (I : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
    let hnum : IsUnit (I.1.num : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :=
      isUnit_num.mpr I.isUnit
    ClassGroup.mk W.FunctionField hnum.unit = ClassGroup.mk W.FunctionField I := by
  dsimp only
  let R := W.CoordinateRing
  let K := W.FunctionField
  let hnum : IsUnit (I.1.num : FractionalIdeal R⁰ K) := isUnit_num.mpr I.isUnit
  have hden0 : algebraMap R K I.1.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.1.den.prop
  let u : Kˣ := Units.mk0 (algebraMap R K I.1.den) hden0
  let D : (FractionalIdeal R⁰ K)ˣ := toPrincipalIdeal R K u
  have hmul : D * I = hnum.unit := by
    apply Units.ext
    dsimp [D]
    rw [coe_toPrincipalIdeal]
    simpa [u] using FractionalIdeal.den_mul_self_eq_num' R⁰ K I.1
  rw [← hmul, map_mul]
  have hD : ClassGroup.mk K D = 1 := by
    dsimp [D]
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    refine ⟨⟨algebraMap R K I.1.den, ?_⟩⟩
    rw [FractionalIdeal.coe_spanSingleton]
    simp [u]
  rw [hD, one_mul]

omit [DecidableEq F] in
/-- For an invertible integral ideal `I`, base change to `R / J` identifies `I / I J` with
`R / J`. -/
private noncomputable def quotIdealMulEquiv
    {I J : Ideal W.CoordinateRing} [FiniteDimensional F (W.CoordinateRing ⧸ J)]
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :
    ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸
        Submodule.comap (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J : Ideal W.CoordinateRing) : Submodule W.CoordinateRing W.CoordinateRing))
      ≃ₗ[W.CoordinateRing] (W.CoordinateRing ⧸ J) := by
  let R := W.CoordinateRing
  let K := W.FunctionField
  have hinj : Function.Injective (Algebra.linearMap R K) :=
    FaithfulSMul.algebraMap_injective R K
  let U : (FractionalIdeal R⁰ K)ˣ := hIunit.unit
  let IU : (Submodule R K)ˣ := FractionalIdeal.unitsMulEquivSubmodule U
  have hIU : (IU : Submodule R K) =
      (I : FractionalIdeal R⁰ K).coeToSubmodule :=
    congrArg FractionalIdeal.coeToSubmodule hIunit.unit_spec
  have hcoeI : Submodule.map (Algebra.linearMap R K) (I : Submodule R R) =
      (I : FractionalIdeal R⁰ K).coeToSubmodule := by
    rw [FractionalIdeal.coe_coeIdeal]
    rfl
  let eI : (I : Submodule R R) ≃ₗ[R] IU :=
    (Submodule.equivMapOfInjective (Algebra.linearMap R K) hinj
      (I : Submodule R R)).trans
        ((LinearEquiv.ofEq _ _ hcoeI).trans (LinearEquiv.ofEq _ _ hIU.symm))
  letI : Module.Invertible R (I : Submodule R R) := Module.Invertible.congr eI.symm
  let A := R ⧸ J
  letI : Module.Invertible A (TensorProduct R A (I : Submodule R R)) := inferInstance
  letI : IsArtinianRing A := IsArtinianRing.of_finite F A
  letI : Finite (MaximalSpectrum A) := inferInstance
  letI : Module.Free A (TensorProduct R A (I : Submodule R R)) := inferInstance
  let eFree : TensorProduct R A (I : Submodule R R) ≃ₗ[A] A :=
    (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some
  have hsub : J • (⊤ : Submodule R (I : Submodule R R)) =
      Submodule.comap (I : Submodule R R).subtype
        ((I * J : Ideal R) : Submodule R R) := by
    apply Submodule.map_injective_of_injective (I : Submodule R R).subtype_injective
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
      Submodule.map_comap_subtype]
    change J * I = I ⊓ (I * J)
    rw [mul_comm J I, inf_eq_right.mpr Ideal.mul_le_left]
  exact (Submodule.quotEquivOfEq _ _ hsub.symm).trans
    ((TensorProduct.quotTensorEquivQuotSMul (I : Submodule R R) J).symm.trans
      (eFree.restrictScalars R))

omit [DecidableEq F] in
/-- Codimension is additive when the left ideal is nonzero and invertible. -/
private theorem finrank_quotient_mul {I J : Ideal W.CoordinateRing}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :
    Module.finrank F (W.CoordinateRing ⧸ (I * J)) =
      Module.finrank F (W.CoordinateRing ⧸ I) +
        Module.finrank F (W.CoordinateRing ⧸ J) := by
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  have : FiniteDimensional F (W.CoordinateRing ⧸ (I * J)) :=
    finiteDimensional_quotient_of_ne_bot _ hIJ
  have : FiniteDimensional F (W.CoordinateRing ⧸ I) :=
    finiteDimensional_quotient_of_ne_bot _ hI
  have : FiniteDimensional F (W.CoordinateRing ⧸ J) :=
    finiteDimensional_quotient_of_ne_bot _ hJ
  have hIJ_le : I * J ≤ I := Ideal.mul_le_left
  set M : Submodule W.CoordinateRing (W.CoordinateRing ⧸ (I * J)) :=
    Submodule.map (Submodule.mkQ (I * J))
      (I : Submodule W.CoordinateRing W.CoordinateRing) with hM
  have e1 : ((W.CoordinateRing ⧸ (I * J)) ⧸ M) ≃ₗ[W.CoordinateRing]
      W.CoordinateRing ⧸ I :=
    Submodule.quotientQuotientEquivQuotient (I * J) I hIJ_le
  have e2a : M ≃ₗ[W.CoordinateRing]
      ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸
        Submodule.comap (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J : Ideal W.CoordinateRing) : Submodule W.CoordinateRing W.CoordinateRing)) := by
    set R := W.CoordinateRing
    set g : (I : Submodule R R) →ₗ[R] (R ⧸ (I * J)) :=
      (Submodule.mkQ (I * J)).comp (I : Submodule R R).subtype with hg
    have hrange : LinearMap.range g = M := by
      rw [hM, hg, LinearMap.range_comp]
      congr 1
      exact Submodule.range_subtype _
    have hker : LinearMap.ker g =
        Submodule.comap (I : Submodule R R).subtype ((I * J : Ideal R) : Submodule R R) := by
      rw [hg, LinearMap.ker_comp, Submodule.ker_mkQ]
    have e3 : LinearMap.range g ≃ₗ[R] M := LinearEquiv.ofEq _ _ hrange
    exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivRange.trans e3)).symm
  have eM : M ≃ₗ[W.CoordinateRing] (W.CoordinateRing ⧸ J) :=
    e2a.trans (quotIdealMulEquiv hIunit)
  have : FiniteDimensional F M := (eM.restrictScalars F).symm.finiteDimensional
  have key : Module.finrank F ((W.CoordinateRing ⧸ (I * J)) ⧸ M.restrictScalars F) +
      Module.finrank F (M.restrictScalars F) =
        Module.finrank F (W.CoordinateRing ⧸ (I * J)) :=
    Submodule.finrank_quotient_add_finrank (M.restrictScalars F)
  have hA : Module.finrank F ((W.CoordinateRing ⧸ (I * J)) ⧸ M.restrictScalars F) =
      Module.finrank F (W.CoordinateRing ⧸ I) := (e1.restrictScalars F).finrank_eq
  have hB : Module.finrank F (M.restrictScalars F) =
      Module.finrank F (W.CoordinateRing ⧸ J) := (eM.restrictScalars F).finrank_eq
  rw [hA, hB] at key
  omega

omit [DecidableEq F] in
/-- An equation solution whose point ideal is invertible is nonsingular. At a singular solution,
the two coordinate derivations make the cotangent space at least two-dimensional, whereas an
invertible point ideal has one-dimensional cotangent space. -/
private theorem nonsingular_of_isUnit_XYIdeal {x y : F} (heq : W.Equation x y)
    (hunit : IsUnit (CoordinateRing.XYIdeal W x (C y) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :
    W.Nonsingular x y := by
  rw [Nonsingular, and_iff_right heq]
  by_contra hs
  push Not at hs
  let P := F[X][Y]
  let H : Ideal P := Ideal.span {W.polynomial}
  let evalY : P →ₗ[F] F[X] := (Polynomial.leval (C y)).restrictScalars F
  let evalX : F[X] →ₗ[F] F := Polynomial.leval x
  let dX : P →ₗ[F] F := evalX.comp (Polynomial.derivative.comp evalY)
  let dY : P →ₗ[F] F := evalX.comp
    (evalY.comp (Polynomial.derivative.restrictScalars F))
  have hdX_apply (p : P) : dX p = (p.eval (C y)).derivative.eval x := rfl
  have hdY_apply (p : P) : dY p = (p.derivative.eval (C y)).eval x := rfl
  have hWX : dX W.polynomial = 0 := by
    simp only [dX, evalX, evalY, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Polynomial.leval_apply]
    change (W.polynomial.eval (C y)).derivative.eval x = 0
    rw [show (W.polynomial.eval (C y)).derivative.eval x =
        W.polynomialX.evalEval x y by
      simp only [polynomial, polynomialX, evalEval]
      simp [Polynomial.derivative_pow]
      ring]
    exact hs.1
  have hWY : dY W.polynomial = 0 := by
    simp only [dY, evalX, evalY, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Polynomial.leval_apply]
    change (W.polynomial.derivative.eval (C y)).eval x = 0
    rw [show (W.polynomial.derivative.eval (C y)).eval x =
        W.polynomialY.evalEval x y by
      simp only [polynomial, polynomialY, evalEval]
      simp [Polynomial.derivative_pow]]
    exact hs.2
  have hdX_mul (p q : P) : dX (p * q) =
      p.evalEval x y * dX q + q.evalEval x y * dX p := by
    rw [hdX_apply, hdX_apply, hdX_apply]
    simp only [evalEval]
    rw [Polynomial.eval_mul, Polynomial.derivative_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_mul]
    ring
  have hdY_mul (p q : P) : dY (p * q) =
      p.evalEval x y * dY q + q.evalEval x y * dY p := by
    rw [hdY_apply, hdY_apply, hdY_apply]
    simp only [evalEval]
    rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
    ring
  have hHX : H.restrictScalars F ≤ LinearMap.ker dX := by
    intro z hz
    obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [LinearMap.mem_ker, hdX_mul, hWX, show W.polynomial.evalEval x y = 0 by
      simpa only [Equation] using heq, mul_zero, zero_mul, add_zero]
  have hHY : H.restrictScalars F ≤ LinearMap.ker dY := by
    intro z hz
    obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [LinearMap.mem_ker, hdY_mul, hWY, show W.polynomial.evalEval x y = 0 by
      simpa only [Equation] using heq, mul_zero, zero_mul, add_zero]
  let qX : (P ⧸ H.restrictScalars F) →ₗ[F] F :=
    Submodule.liftQ (H.restrictScalars F) dX hHX
  let qY : (P ⧸ H.restrictScalars F) →ₗ[F] F :=
    Submodule.liftQ (H.restrictScalars F) dY hHY
  let eQ : (P ⧸ H.restrictScalars F) ≃ₗ[F] W.CoordinateRing :=
    Submodule.Quotient.restrictScalarsEquiv F H
  let DX : W.CoordinateRing →ₗ[F] F := qX.comp eQ.symm.toLinearMap
  let DY : W.CoordinateRing →ₗ[F] F := qY.comp eQ.symm.toLinearMap
  have DX_mk (p : P) : DX (CoordinateRing.mk W p) = dX p := by rfl
  have DY_mk (p : P) : DY (CoordinateRing.mk W p) = dY p := by rfl
  let I := CoordinateRing.XYIdeal W x (C y)
  let ρ : W.CoordinateRing →+* F := AdjoinRoot.evalEval (by
    simpa only [Equation] using heq)
  have hρ_mk (p : P) : ρ (CoordinateRing.mk W p) = p.evalEval x y :=
    AdjoinRoot.evalEval_mk _ p
  have hρmem {a : W.CoordinateRing} (ha : a ∈ I) : ρ a = 0 := by
    rw [← RingHom.mem_ker]
    apply (show I ≤ RingHom.ker ρ by
      change CoordinateRing.XYIdeal W x (C y) ≤ RingHom.ker ρ
      rw [CoordinateRing.XYIdeal, Ideal.span_le, Set.pair_subset_iff]
      constructor
      · change ρ (CoordinateRing.XClass W x) = 0
        rw [CoordinateRing.XClass, hρ_mk]
        simp [evalEval_C]
      · change ρ (CoordinateRing.YClass W (C y)) = 0
        rw [CoordinateRing.YClass, hρ_mk]
        simp) ha
  have hDX_mul (a b : W.CoordinateRing) :
      DX (a * b) = ρ a * DX b + ρ b * DX a := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
    rw [← map_mul]
    simp only [DX_mk, hρ_mk, hdX_mul]
  have hDY_mul (a b : W.CoordinateRing) :
      DY (a * b) = ρ a * DY b + ρ b * DY a := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
    rw [← map_mul]
    simp only [DY_mk, hρ_mk, hdY_mul]
  let fX : I →ₗ[F] F := DX.comp (I.subtype.restrictScalars F)
  let fY : I →ₗ[F] F := DY.comp (I.subtype.restrictScalars F)
  have hfX (a b : I) : fX (a * b) = 0 := by
    change DX ((a : W.CoordinateRing) * b) = 0
    rw [hDX_mul, hρmem a.2, hρmem b.2, zero_mul, zero_mul, zero_add]
  have hfY (a b : I) : fY (a * b) = 0 := by
    change DY ((a : W.CoordinateRing) * b) = 0
    rw [hDY_mul, hρmem a.2, hρmem b.2, zero_mul, zero_mul, zero_add]
  let δX : I.Cotangent →ₗ[F] F := Ideal.Cotangent.lift fX hfX
  let δY : I.Cotangent →ₗ[F] F := Ideal.Cotangent.lift fY hfY
  let δ : I.Cotangent →ₗ[F] F × F := δX.prod δY
  have hXmem : CoordinateRing.XClass W x ∈ I :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hYmem : CoordinateRing.YClass W (C y) ∈ I :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hDX_X : DX (CoordinateRing.XClass W x) = 1 := by
    rw [CoordinateRing.XClass, DX_mk, hdX_apply]
    simp
  have hDX_Y : DX (CoordinateRing.YClass W (C y)) = 0 := by
    rw [CoordinateRing.YClass, DX_mk, hdX_apply]
    simp
  have hDY_X : DY (CoordinateRing.XClass W x) = 0 := by
    rw [CoordinateRing.XClass, DY_mk, hdY_apply]
    simp
  have hDY_Y : DY (CoordinateRing.YClass W (C y)) = 1 := by
    rw [CoordinateRing.YClass, DY_mk, hdY_apply]
    simp
  have hδsurj : Function.Surjective δ := by
    rintro ⟨a, b⟩
    refine ⟨a • I.toCotangent ⟨CoordinateRing.XClass W x, hXmem⟩ +
      b • I.toCotangent ⟨CoordinateRing.YClass W (C y), hYmem⟩, ?_⟩
    ext <;> simp [δ, δX, δY, fX, fY, hDX_X, hDX_Y, hDY_X, hDY_Y]
  let hquot : Module.Finite F (W.CoordinateRing ⧸ I) := by
    change Module.Finite F
      (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y))
    exact (CoordinateRing.quotientXYIdealEquiv heq).toLinearEquiv.symm.finiteDimensional
  let eI := quotIdealMulEquiv (F := F) (I := I) (J := I) hunit
  have hsquare : I • (⊤ : Submodule W.CoordinateRing I) =
      Submodule.comap I.subtype ((I * I : Ideal W.CoordinateRing) :
        Submodule W.CoordinateRing W.CoordinateRing) := by
    apply Submodule.map_injective_of_injective I.subtype_injective
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
      Submodule.map_comap_subtype]
    change I * I = I ⊓ (I * I)
    rw [inf_eq_right.mpr Ideal.mul_le_left]
  let eCot : I.Cotangent ≃ₗ[F] (W.CoordinateRing ⧸ I) :=
    ((Submodule.quotEquivOfEq _ _ hsquare).trans eI).restrictScalars F
  let hcot : Module.Finite F I.Cotangent := eCot.symm.finiteDimensional
  have hfin : Module.finrank F I.Cotangent = 1 := by
    rw [eCot.finrank_eq]
    change Module.finrank F
      (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) = 1
    exact (CoordinateRing.quotientXYIdealEquiv heq).toLinearEquiv.finrank_eq.trans
      (Module.finrank_self F)
  have hprod : Module.finrank F (F × F) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hle := LinearMap.finrank_le_finrank_of_surjective hδsurj
  rw [hprod, hfin] at hle
  omega

omit [DecidableEq F] in
private theorem two_nsmul_coe (n : ℕ) :
    (2 : ℕ) • (n : WithBot ℕ) = ((2 * n : ℕ) : WithBot ℕ) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

omit [DecidableEq F] in
private theorem two_nsmul_degree_le {p : F[X]} {n : ℕ} (hp : p.degree < (n : ℕ)) :
    2 • p.degree ≤ ((2 * (n - 1) : ℕ) : WithBot ℕ) := by
  classical
  by_cases h0 : p = 0
  · simp [h0]
  · have hnd : p.natDegree ≤ n - 1 := by
      have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp
      omega
    rw [Polynomial.degree_eq_natDegree h0, two_nsmul_coe, Nat.cast_le]
    omega

/-- The bounded-degree basis combinations `(p, q) ↦ p + qY` used in the explicit genus-one
Riemann--Roch dimension count. -/
private noncomputable def basisCombMap (W : WeierstrassCurve.Affine F) (a b : ℕ) :
    (Polynomial.degreeLT F a × Polynomial.degreeLT F b) →ₗ[F] W.CoordinateRing where
  toFun pq := (pq.1 : F[X]) • (1 : W.CoordinateRing) +
    (pq.2 : F[X]) • CoordinateRing.basis W 1
  map_add' x y := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply, smul_add]
    rw [smul_assoc, smul_assoc]

omit [DecidableEq F] in
private theorem natDegree_norm_basisComb_le {p q : F[X]} {da db : ℕ}
    (hp : p.degree < (da : ℕ)) (hq : q.degree < (db : ℕ)) :
    (Algebra.norm F[X]
      (p • (1 : W.CoordinateRing) + q • CoordinateRing.basis W 1)).natDegree ≤
        max (2 * (da - 1)) (2 * db + 1) := by
  rw [CoordinateRing.basis_one, Polynomial.natDegree_le_iff_degree_le,
    CoordinateRing.degree_norm_smul_basis]
  have hmax : ((max (2 * (da - 1)) (2 * db + 1) : ℕ) : WithBot ℕ) =
      max ((2 * (da - 1) : ℕ) : WithBot ℕ) ((2 * db + 1 : ℕ) : WithBot ℕ) := rfl
  rw [hmax]
  apply max_le_max
  · exact two_nsmul_degree_le hp
  · by_cases h0 : q = 0
    · simp [h0]
    · have hqd : q.natDegree ≤ db - 1 := by
        have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hq
        omega
      have hdb1 : 1 ≤ db := by
        by_contra hc
        rw [Nat.lt_one_iff.mp (Nat.not_le.mp hc), Nat.cast_zero] at hq
        exact absurd ((Polynomial.zero_le_degree_iff.mpr h0).trans_lt hq) (by simp)
      rw [Polynomial.degree_eq_natDegree h0, two_nsmul_coe]
      have h3 : (3 : WithBot ℕ) = ((3 : ℕ) : WithBot ℕ) := by norm_cast
      rw [h3, ← Nat.cast_add, Nat.cast_le]
      omega

omit [DecidableEq F] in
private theorem basisCombMap_ne_zero {a b : ℕ}
    (pq : Polynomial.degreeLT F a × Polynomial.degreeLT F b) (h : pq ≠ 0) :
    basisCombMap W a b pq ≠ 0 := by
  intro hz
  apply h
  rw [basisCombMap] at hz
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at hz
  rw [CoordinateRing.basis_one] at hz
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero hz
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)

omit [DecidableEq F] in
/-- Every nonzero ideal contains a nonzero function whose norm degree is at most one more than
the ideal's codimension. This is the concrete genus-one Riemann--Roch inequality. -/
private theorem exists_mem_norm_natDegree_le
    (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    ∃ a ∈ I, a ≠ 0 ∧
      (Algebra.norm F[X] a).natDegree ≤ Module.finrank F (W.CoordinateRing ⧸ I) + 1 := by
  classical
  set R := W.CoordinateRing
  set ℓ := Module.finrank F (R ⧸ I) with hℓ
  have : FiniteDimensional F (R ⧸ I) := finiteDimensional_quotient_of_ne_bot _ hI
  let da := (ℓ + 1) / 2 + 1
  let db := ℓ / 2
  set ψ : (Polynomial.degreeLT F da × Polynomial.degreeLT F db) →ₗ[F] (R ⧸ I) :=
    ((Submodule.mkQ I).restrictScalars F).comp (basisCombMap W da db) with hψ
  have hdimdom :
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) = da + db := by
    rw [Module.finrank_prod, (Polynomial.degreeLTEquiv F da).finrank_eq,
      (Polynomial.degreeLTEquiv F db).finrank_eq, Module.finrank_fin_fun,
      Module.finrank_fin_fun]
  have hdomℓ :
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) = ℓ + 1 := by
    rw [hdimdom]
    dsimp [da, db]
    omega
  have hrn : Module.finrank F (LinearMap.range ψ) + Module.finrank F (LinearMap.ker ψ) =
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) :=
    ψ.finrank_range_add_finrank_ker
  have hrange_le : Module.finrank F (LinearMap.range ψ) ≤ ℓ :=
    le_trans (Submodule.finrank_le _) (le_of_eq hℓ.symm)
  have hker_pos : 0 < Module.finrank F (LinearMap.ker ψ) := by omega
  have : Nontrivial (LinearMap.ker ψ) := Module.nontrivial_of_finrank_pos hker_pos
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker ψ)
  set pq := (z : Polynomial.degreeLT F da × Polynomial.degreeLT F db) with hpq
  have hpq_ne : pq ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨basisCombMap W da db pq, ?_, basisCombMap_ne_zero pq hpq_ne, ?_⟩
  · have hz0 : ψ pq = 0 := z.2
    rw [hψ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz0
    exact hz0
  · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
    rw [Polynomial.mem_degreeLT] at hp hq
    have hbound := natDegree_norm_basisComb_le (W := W) hp hq
    rw [basisCombMap]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine le_trans hbound ?_
    dsimp [da, db]
    omega

omit [DecidableEq F] in
/-- Every invertible integral ideal has an inverse-class representative of codimension at most
one. -/
private theorem exists_codimLEOne_inv_integral
    (I : Ideal W.CoordinateRing)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :
    ∃ (J : Ideal W.CoordinateRing)
      (hJunit : IsUnit (J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)),
      Module.finrank F (W.CoordinateRing ⧸ J) ≤ 1 ∧
        ClassGroup.mk W.FunctionField hJunit.unit =
          (ClassGroup.mk W.FunctionField hIunit.unit)⁻¹ := by
  let R := W.CoordinateRing
  let K := W.FunctionField
  have hIne : I ≠ ⊥ := by
    intro h
    apply hIunit.ne_zero
    simp [h]
  obtain ⟨a, ha_mem, ha, hbound⟩ :=
    exists_mem_norm_natDegree_le (F := F) I hIne
  have hle : Ideal.span {a} ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ha_mem
  let Q : FractionalIdeal R⁰ K :=
    (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹
  have hQ_le : Q ≤ 1 := by
    dsimp [Q]
    calc
      (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ ≤
          (I : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ := by
            gcongr
      _ = 1 := hIunit.mul_val_inv
  obtain ⟨J, hJQ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hQ_le
  have hJ : Ideal.span {a} = I * J := by
    apply FractionalIdeal.coeIdeal_injective (R := R) (K := K)
    change (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K) =
      (I * J : Ideal R)
    rw [FractionalIdeal.coeIdeal_mul, hJQ]
    dsimp [Q]
    rw [mul_left_comm, hIunit.mul_val_inv, mul_one]
  have hspan_ne : Ideal.span ({a} : Set W.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot] at hJ
    exact hspan_ne hJ
  have haK : algebraMap R K a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne ha
  let au : Kˣ := Units.mk0 (algebraMap R K a) haK
  have hspanUnit : IsUnit (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K) := by
    refine ⟨toPrincipalIdeal R K au, ?_⟩
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hJunit : IsUnit (J : FractionalIdeal R⁰ K) := by
    have hIJunit : IsUnit
        ((I : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K)) := by
      rw [← FractionalIdeal.coeIdeal_mul, ← hJ]
      exact hspanUnit
    exact (IsUnit.mul_iff.mp hIJunit).2
  refine ⟨J, hJunit, ?_, ?_⟩
  · have hdim : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) =
        Module.finrank F (W.CoordinateRing ⧸ I) +
          Module.finrank F (W.CoordinateRing ⧸ J) := by
      rw [hJ]
      exact finrank_quotient_mul hIne hJne hIunit
    have hnorm : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) =
        (Algebra.norm F[X] a).natDegree :=
      finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) ha
    omega
  · rw [eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk_eq_one_iff]
    refine ⟨au, ?_⟩
    rw [Units.val_mul, hJunit.unit_spec, hIunit.unit_spec,
      ← FractionalIdeal.coeIdeal_mul, mul_comm J I, ← hJ,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coe_spanSingleton]
    simp [au]

omit [DecidableEq F] in
/-- Every fractional ideal class has an inverse-class integral representative of codimension at
most one. -/
private theorem exists_codimLEOne_inv
    (U : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
    ∃ (J : Ideal W.CoordinateRing)
      (hJunit : IsUnit (J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)),
      Module.finrank F (W.CoordinateRing ⧸ J) ≤ 1 ∧
        ClassGroup.mk W.FunctionField hJunit.unit =
          (ClassGroup.mk W.FunctionField U)⁻¹ := by
  let hIunit : IsUnit (U.1.num :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := isUnit_num.mpr U.isUnit
  obtain ⟨J, hJunit, hfin, hclass⟩ :=
    exists_codimLEOne_inv_integral (F := F) U.1.num hIunit
  refine ⟨J, hJunit, hfin, ?_⟩
  rwa [mk_num U] at hclass

omit [DecidableEq F] in
private theorem mk_eq_one_of_finrank_quotient_eq_zero
    (I : Ideal W.CoordinateRing)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField))
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 0) :
    ClassGroup.mk W.FunctionField hIunit.unit = 1 := by
  have : FiniteDimensional F (W.CoordinateRing ⧸ I) :=
    finiteDimensional_quotient_of_ne_bot _ (by
      intro h
      apply hIunit.ne_zero
      simp [h])
  have hsub : Subsingleton (W.CoordinateRing ⧸ I) := Module.finrank_zero_iff.mp hfin
  have htop : I = ⊤ := by
    rw [Ideal.Quotient.subsingleton_iff] at hsub
    exact hsub
  rw [ClassGroup.mk_eq_one_iff]
  refine ⟨1, ?_⟩
  rw [hIunit.unit_spec, htop]
  change ((⊤ : Ideal W.CoordinateRing) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule = _
  rw [FractionalIdeal.coeIdeal_top, FractionalIdeal.coe_one, Submodule.one_eq_span]

omit [DecidableEq F] in
private theorem mk_eq_mk_XYIdeal'_of_finrank_quotient_eq_one
    (I : Ideal W.CoordinateRing)
    (hIunit : IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField))
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ (x y : F) (h : W.Nonsingular x y),
      ClassGroup.mk W.FunctionField hIunit.unit =
        ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  obtain ⟨x, y, heq, hxy⟩ :=
    TauCeti.WeierstrassCurve.Affine.CoordinateRing.finrank_quotient_eq_one_iff.mp hfin
  have hXYunit : IsUnit (CoordinateRing.XYIdeal W x (C y) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := hxy ▸ hIunit
  have hns : W.Nonsingular x y := nonsingular_of_isUnit_XYIdeal heq hXYunit
  refine ⟨x, y, hns, ?_⟩
  congr 1
  apply Units.ext
  rw [hIunit.unit_spec, CoordinateRing.XYIdeal'_eq hns, hxy]

/-- **The point-to-class map is surjective.** Equivalently, every ideal
class of its affine coordinate ring is represented by a rational point. -/
theorem toClass_surjective : Function.Surjective (toClass (W := W)) := by
  rw [toClass_surjective_iff]
  intro g
  refine ClassGroup.induction W.FunctionField (x := g) ?_
  intro U
  obtain ⟨J, hJunit, hfin, hclass⟩ := exists_codimLEOne_inv (F := F) U⁻¹
  rw [map_inv, inv_inv] at hclass
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfin with hzero | hone
  · left
    have htrivial := mk_eq_one_of_finrank_quotient_eq_zero J hJunit hzero
    exact hclass.symm.trans htrivial
  · right
    obtain ⟨x, y, hns, hpoint⟩ :=
      mk_eq_mk_XYIdeal'_of_finrank_quotient_eq_one J hJunit hone
    exact ⟨x, y, hns, hclass.symm.trans hpoint⟩

/-- **The points are their affine ideal class group.** -/
noncomputable def toClassEquiv :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  AddEquiv.ofBijective toClass ⟨toClass_injective, toClass_surjective⟩

/-- The point-to-class equivalence has underlying map `Point.toClass`. -/
@[simp]
theorem toClassEquiv_apply (P : W.Point) : toClassEquiv P = toClass P :=
  by
    unfold toClassEquiv
    exact AddEquiv.ofBijective_apply toClass _ P

/-- Applying `toClass` to the point corresponding to an ideal class recovers that class. -/
@[simp]
theorem toClass_toClassEquiv_symm (c : Additive (ClassGroup W.CoordinateRing)) :
    toClass (toClassEquiv.symm c) = c := by
  rw [← toClassEquiv_apply]
  exact toClassEquiv.apply_symm_apply c

end WeierstrassCurve.Affine.Point
