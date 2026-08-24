/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Surjectivity of `Point.toClass`

Mathlib builds `WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup
W.CoordinateRing)` and proves it **injective**, realising the points of an affine Weierstrass
curve as a subgroup of the affine ideal class group. It does not prove surjectivity; this file
proves it for elliptic curves by an explicit genus-one Riemann--Roch argument in the affine
coordinate ring.

It first records what surjectivity amounts to: every ideal class is trivial or the class of an
`XYIdeal'` at a nonsingular affine point. It then proves that statement.

## Main results

* `WeierstrassCurve.Affine.Point.toClass_surjective_iff`: `toClass` is surjective exactly when
  every element of `ClassGroup W.CoordinateRing` is trivial or the class of `XYIdeal' h` for a
  nonsingular affine point.
* `WeierstrassCurve.Affine.Point.toClass_surjective`: `toClass` is surjective for an elliptic
  curve.
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

The formal equivalence carries no ellipticity hypothesis. The proof of either side does: it uses
ellipticity both to make the coordinate ring Dedekind and to identify equation solutions with
nonsingular points. No named representability predicate is introduced because
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

local instance coordinateRingIsDedekind [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing :=
  TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing W

omit [DecidableEq F] in
/-- Every nonzero ideal of an elliptic coordinate ring has finite codimension over the base
field. -/
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
private noncomputable def quotComapEquivCoeIdealQuot
    {I J : Ideal W.CoordinateRing}
    (hinj : Function.Injective (Algebra.linearMap W.CoordinateRing W.FunctionField)) :
    ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸ Submodule.comap
        (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J : Ideal W.CoordinateRing) : Submodule W.CoordinateRing W.CoordinateRing))
      ≃ₗ[W.CoordinateRing]
        ((↑I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule ⧸
          Submodule.comap
            (↑I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule.subtype
            ((↑(I * J) : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule)) := by
  set R := W.CoordinateRing
  set K := W.FunctionField
  have hcoeI : Submodule.map (Algebra.linearMap R K) (I : Submodule R R) =
      (↑I : FractionalIdeal R⁰ K).coeToSubmodule := by
    rw [FractionalIdeal.coe_coeIdeal]
    rfl
  let μ : (I : Submodule R R) ≃ₗ[R] (↑I : FractionalIdeal R⁰ K).coeToSubmodule :=
    (Submodule.equivMapOfInjective (Algebra.linearMap R K) hinj
      (I : Submodule R R)).trans (LinearEquiv.ofEq _ _ hcoeI)
  refine Submodule.Quotient.equiv _ _ μ ?_
  apply le_antisymm
  · rintro _ ⟨⟨x, hxI⟩, hxIJ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hxIJ
    rw [Submodule.mem_comap]
    change (μ ⟨x, hxI⟩ : K) ∈ (↑(I * J) : FractionalIdeal R⁰ K).coeToSubmodule
    have hμ : (μ ⟨x, hxI⟩ : K) = algebraMap R K x := by
      simp only [μ, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        Submodule.coe_equivMapOfInjective_apply, Algebra.linearMap_apply]
    rw [hμ, FractionalIdeal.mem_coe]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ hxIJ
  · rintro ⟨y, hyI⟩ hy
    rw [Submodule.mem_comap] at hy
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨r, hrIJ, hry⟩ := hy
    have hrI : r ∈ I := Ideal.mul_le_left hrIJ
    refine ⟨⟨r, hrI⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Submodule.mem_comap]
      exact hrIJ
    · apply Subtype.ext
      change (μ ⟨r, hrI⟩ : K) = y
      simp only [μ, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        Submodule.coe_equivMapOfInjective_apply, Algebra.linearMap_apply]
      exact hry

omit [DecidableEq F] in
private noncomputable def quotEquivOneCoeIdealQuot
    {J : Ideal W.CoordinateRing}
    (hinj : Function.Injective (Algebra.linearMap W.CoordinateRing W.FunctionField)) :
    (W.CoordinateRing ⧸ J) ≃ₗ[W.CoordinateRing]
      ((1 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule ⧸
        Submodule.comap
          (1 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule.subtype
          ((↑J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule)) := by
  set R := W.CoordinateRing
  set K := W.FunctionField
  have hone : LinearMap.range (Algebra.linearMap R K) =
      (1 : FractionalIdeal R⁰ K).coeToSubmodule := by
    rw [FractionalIdeal.coe_one]
    exact (Submodule.one_eq_range).symm
  let ν : R ≃ₗ[R] (1 : FractionalIdeal R⁰ K).coeToSubmodule :=
    (LinearEquiv.ofInjective (Algebra.linearMap R K) hinj).trans
      (LinearEquiv.ofEq _ _ hone)
  refine Submodule.Quotient.equiv (J : Submodule R R) _ ν ?_
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    rw [Submodule.mem_comap]
    change (ν r : K) ∈ (↑J : FractionalIdeal R⁰ K).coeToSubmodule
    have hν : (ν r : K) = algebraMap R K r := by
      rw [show ν r = (LinearEquiv.ofEq _ _ hone)
          (LinearEquiv.ofInjective (Algebra.linearMap R K) hinj r) from rfl,
        LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, Algebra.linearMap_apply]
    rw [hν, FractionalIdeal.mem_coe]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ hr
  · rintro ⟨y, hy1⟩ hy2
    rw [Submodule.mem_comap] at hy2
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hy2
    obtain ⟨r, hr, hry⟩ := hy2
    refine ⟨r, hr, ?_⟩
    apply Subtype.ext
    change (ν r : K) = y
    rw [show ν r = (LinearEquiv.ofEq _ _ hone)
        (LinearEquiv.ofInjective (Algebra.linearMap R K) hinj r) from rfl,
      LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, Algebra.linearMap_apply]
    exact hry

omit [DecidableEq F] in
/-- For nonzero ideals `I` and `J`, multiplication by the invertible ideal `I` identifies
`I / I J` with `R / J`. -/
private noncomputable def quotIdealMulEquiv [W.IsElliptic]
    {I J : Ideal W.CoordinateRing} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸
        Submodule.comap (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J : Ideal W.CoordinateRing) : Submodule W.CoordinateRing W.CoordinateRing))
      ≃ₗ[W.CoordinateRing] (W.CoordinateRing ⧸ J) := by
  set R := W.CoordinateRing
  set K := W.FunctionField
  have hinj : Function.Injective (Algebra.linearMap R K) :=
    FaithfulSMul.algebraMap_injective R K
  have hH : (↑I : FractionalIdeal R⁰ K) * (↑J : FractionalIdeal R⁰ K) =
      (1 : FractionalIdeal R⁰ K) * (↑(I * J) : FractionalIdeal R⁰ K) := by
    rw [one_mul, ← FractionalIdeal.coeIdeal_mul]
  have hle1 : (↑(I * J) : FractionalIdeal R⁰ K) ≤ (↑I : FractionalIdeal R⁰ K) := by
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]
    exact Ideal.mul_le_left
  have hle2 : (↑J : FractionalIdeal R⁰ K) ≤ (1 : FractionalIdeal R⁰ K) :=
    FractionalIdeal.coeIdeal_le_one
  have hJne : (↑J : FractionalIdeal R⁰ K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have hIne : (↑I : FractionalIdeal R⁰ K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have eqe := FractionalIdeal.quotientEquiv (R := R) (K := K)
    (↑I) (↑(I * J)) 1 (↑J) hH hle1 hle2 hJne hIne
  exact (quotComapEquivCoeIdealQuot hinj).trans
    (eqe.trans (quotEquivOneCoeIdealQuot hinj).symm)

omit [DecidableEq F] in
/-- Codimension is additive under multiplication of nonzero ideals of an elliptic coordinate
ring. -/
private theorem finrank_quotient_mul [W.IsElliptic] {I J : Ideal W.CoordinateRing}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
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
    e2a.trans (quotIdealMulEquiv hI hJ)
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
private theorem two_nsmul_degree_le {p : F[X]} {n : ℕ} (hp : p.degree < (n : ℕ)) :
    2 • p.degree ≤ ((2 * (n - 1) : ℕ) : WithBot ℕ) := by
  classical
  by_cases h0 : p = 0
  · simp [h0]
  · have hnd : p.natDegree ≤ n - 1 := by
      have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp
      omega
    rw [Polynomial.degree_eq_natDegree h0,
      show (2 : ℕ) • (p.natDegree : WithBot ℕ) = ((2 * p.natDegree : ℕ) : WithBot ℕ) by
        rw [nsmul_eq_mul]
        push_cast
        ring, Nat.cast_le]
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
  rw [show ((max (2 * (da - 1)) (2 * db + 1) : ℕ) : WithBot ℕ) =
      max ((2 * (da - 1) : ℕ) : WithBot ℕ) ((2 * db + 1 : ℕ) : WithBot ℕ) by rfl]
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
      rw [Polynomial.degree_eq_natDegree h0,
        show (2 : ℕ) • (q.natDegree : WithBot ℕ) = ((2 * q.natDegree : ℕ) : WithBot ℕ) by
          rw [nsmul_eq_mul]
          push_cast
          ring]
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
/-- Every nonzero integral ideal has an inverse-class representative of codimension at most one.
-/
private theorem exists_codimLEOne_inv [W.IsElliptic]
    (I : (Ideal W.CoordinateRing)⁰) :
    ∃ (J : Ideal W.CoordinateRing) (hJ : J ∈ (Ideal W.CoordinateRing)⁰),
      Module.finrank F (W.CoordinateRing ⧸ J) ≤ 1 ∧
        ClassGroup.mk0 ⟨J, hJ⟩ = (ClassGroup.mk0 I)⁻¹ := by
  have hIne : (I : Ideal W.CoordinateRing) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  obtain ⟨a, ha_mem, ha, hbound⟩ :=
    exists_mem_norm_natDegree_le (F := F) (I : Ideal W.CoordinateRing) hIne
  have hle : Ideal.span {a} ≤ (I : Ideal W.CoordinateRing) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ha_mem
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hspan_ne : Ideal.span ({a} : Set W.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot] at hJ
    exact hspan_ne hJ
  have hJmem : J ∈ (Ideal W.CoordinateRing)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hJne
  refine ⟨J, hJmem, ?_, ?_⟩
  · have hdim : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) =
        Module.finrank F (W.CoordinateRing ⧸ (I : Ideal W.CoordinateRing)) +
          Module.finrank F (W.CoordinateRing ⧸ J) := by
      rw [hJ]
      exact finrank_quotient_mul hIne hJne
    have hnorm : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) =
        (Algebra.norm F[X] a).natDegree :=
      finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) ha
    omega
  · rw [eq_inv_iff_mul_eq_one, mul_comm, ← MonoidHom.map_mul ClassGroup.mk0,
      ClassGroup.mk0_eq_one_iff, Submonoid.coe_mul, ← hJ]
    exact ⟨a, rfl⟩

omit [DecidableEq F] in
private theorem mk0_eq_one_of_finrank_quotient_eq_zero [W.IsElliptic]
    (I : Ideal W.CoordinateRing) (hI : I ∈ (Ideal W.CoordinateRing)⁰)
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 0) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 := by
  have : FiniteDimensional F (W.CoordinateRing ⧸ I) :=
    finiteDimensional_quotient_of_ne_bot _ (mem_nonZeroDivisors_iff_ne_zero.mp hI)
  have hsub : Subsingleton (W.CoordinateRing ⧸ I) := Module.finrank_zero_iff.mp hfin
  have htop : I = ⊤ := by
    rw [Ideal.Quotient.subsingleton_iff] at hsub
    exact hsub
  rw [ClassGroup.mk0_eq_one_iff, htop]
  exact top_isPrincipal

omit [DecidableEq F] in
private theorem mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one [W.IsElliptic]
    (I : Ideal W.CoordinateRing) (hI : I ∈ (Ideal W.CoordinateRing)⁰)
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ (x y : F) (h : W.Nonsingular x y),
      ClassGroup.mk0 ⟨I, hI⟩ = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  obtain ⟨x, y, heq, hxy⟩ :=
    TauCeti.WeierstrassCurve.Affine.CoordinateRing.finrank_quotient_eq_one_iff.mp hfin
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp heq
  have hI' : CoordinateRing.XYIdeal W x (C y) ∈ (Ideal W.CoordinateRing)⁰ := hxy ▸ hI
  refine ⟨x, y, hns, ?_⟩
  rw [show (⟨I, hI⟩ : (Ideal W.CoordinateRing)⁰) =
      ⟨CoordinateRing.XYIdeal W x (C y), hI'⟩ from Subtype.ext hxy]
  rw [← ClassGroup.mk_mk0 W.FunctionField]
  congr 1
  apply Units.ext
  rw [FractionalIdeal.coe_mk0, CoordinateRing.XYIdeal'_eq hns]

/-- **The point-to-class map of an elliptic curve is surjective.** Equivalently, every ideal
class of its affine coordinate ring is represented by a rational point. -/
theorem toClass_surjective [W.IsElliptic] : Function.Surjective (toClass (W := W)) := by
  rw [toClass_surjective_iff]
  intro g
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective g⁻¹
  obtain ⟨J, hJ, hfin, hclass⟩ := exists_codimLEOne_inv (F := F) I
  rw [hI, inv_inv] at hclass
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfin with hzero | hone
  · left
    have htrivial := mk0_eq_one_of_finrank_quotient_eq_zero J hJ hzero
    exact hclass.symm.trans htrivial
  · right
    obtain ⟨x, y, hns, hpoint⟩ :=
      mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one J hJ hone
    exact ⟨x, y, hns, hclass.symm.trans hpoint⟩

/-- **The points of an elliptic curve are its affine ideal class group.** -/
noncomputable def toClassEquiv [W.IsElliptic] :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  AddEquiv.ofBijective toClass ⟨toClass_injective, toClass_surjective⟩

/-- The point-to-class equivalence has underlying map `Point.toClass`. -/
@[simp]
theorem toClassEquiv_apply [W.IsElliptic] (P : W.Point) : toClassEquiv P = toClass P :=
  by
    unfold toClassEquiv
    exact AddEquiv.ofBijective_apply toClass _ P

end WeierstrassCurve.Affine.Point
