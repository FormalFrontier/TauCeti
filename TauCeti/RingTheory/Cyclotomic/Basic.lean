/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Computable

/-!
# Computable cyclotomic integers

This file defines `TauCeti.Cyclotomic e`, an exact, computable model of
`ℤ[X] / (Polynomial.cyclotomic e ℤ)`.  Its elements are the `e.totient` coefficients of the
canonical representative, in descending order; `TauCeti.Cyclotomic.coeff` reads off the coordinate
of a single power of `ζ`.  Addition, negation, multiplication, and equality are genuine
computations on finite lists of integers; multiplication convolves coefficient lists with
`TauCeti.Polynomial.mulCoeffList` and then applies the computable cyclotomic reduction from
`TauCeti.RingTheory.Polynomial.Cyclotomic.Computable`.

The ring is identified with Mathlib's `AdjoinRoot (Polynomial.cyclotomic e ℤ)`.  For nonzero `e`,
evaluation at `exp (2 * π * I / e)` then gives the distinguished embedding into `ℂ` used to state
the correctness of exact character-table computations.

The interface followed here is the one blueprinted in the character-theory roadmap
(`RepresentationTheory/CharacterTheory/README.md` in TauCetiRoadmap, Layer 6: "Exact cyclotomic
arithmetic", whose `Suggested.lean` pins `Cyclotomic e` with its `CommRing` instance, the
generator `ζ_e` as the class of `X`, the reduction to `ZMod p`, and the *pinned* embedding into
`ℂ` as a ring homomorphism together with its injectivity).  The choice of `exp (2 * π * I / e)`
for that pin, of descending coefficient lists as the representation, and the identification with
`AdjoinRoot` rather than the roadmap's `CyclotomicRing e ℤ ℚ` are this file's.
-/

public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

/-! ## The exact ring -/

/-- Exact `e`-th cyclotomic integers, represented by the `e.totient` coefficients of the
canonical polynomial representative in descending order. -/
@[expose] def Cyclotomic (e : ℕ) := {l : List ℤ // l.length = e.totient}
  deriving DecidableEq

namespace Cyclotomic

variable {e : ℕ}

/-- The descending list of coefficients representing an exact cyclotomic integer. -/
@[expose] def coeffs (x : Cyclotomic e) : List ℤ := x.1

@[simp]
theorem length_coeffs (x : Cyclotomic e) : x.coeffs.length = e.totient := x.2

@[ext]
theorem ext {x y : Cyclotomic e} (h : x.coeffs = y.coeffs) : x = y := Subtype.ext h

/-- The coordinate of `ζ ^ j` on the power basis `ζ ^ (φ e - 1), …, ζ, 1`.  Since
`TauCeti.Cyclotomic.coeffs` is in descending order this reads it backwards, and it is `0` beyond
the `e.totient` slots the basis has. -/
@[expose] def coeff (x : Cyclotomic e) (j : ℕ) : ℤ := x.coeffs.reverse.getD j 0

/-- There is no coordinate beyond the `e.totient` elements of the power basis. -/
theorem coeff_eq_zero_of_totient_le (x : Cyclotomic e) {j : ℕ} (h : e.totient ≤ j) :
    x.coeff j = 0 := by
  rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h),
    Option.getD_none]

/-- Reduce a descending coefficient list modulo `Φ_e` and regard the result as an exact
cyclotomic integer. -/
@[expose] def ofCoeffList (e : ℕ) (l : List ℤ) : Cyclotomic e :=
  ⟨modByCyclotomic e l, length_modByCyclotomic e l⟩

@[simp]
theorem coeffs_ofCoeffList (e : ℕ) (l : List ℤ) :
    (ofCoeffList e l).coeffs = modByCyclotomic e l := rfl

/-- Zero in the coefficient-vector model. -/
@[expose] def zero (e : ℕ) : Cyclotomic e := ofCoeffList e []

/-- One in the coefficient-vector model. -/
@[expose] def one (e : ℕ) : Cyclotomic e := ofCoeffList e [1]

/-- Addition followed by canonical cyclotomic reduction. -/
@[expose] def add (x y : Cyclotomic e) : Cyclotomic e :=
  ofCoeffList e (List.zipWith (fun a b => a + b) x.coeffs y.coeffs)

/-- Negation followed by canonical cyclotomic reduction. -/
@[expose] def neg (x : Cyclotomic e) : Cyclotomic e :=
  ofCoeffList e (x.coeffs.map (-·))

/-- Polynomial convolution followed by canonical cyclotomic reduction. -/
@[expose] def mul (x y : Cyclotomic e) : Cyclotomic e :=
  ofCoeffList e (mulCoeffList x.coeffs y.coeffs)

instance : Zero (Cyclotomic e) := ⟨zero e⟩
instance : One (Cyclotomic e) := ⟨one e⟩
instance : Add (Cyclotomic e) := ⟨add⟩
instance : Neg (Cyclotomic e) := ⟨neg⟩
instance : Mul (Cyclotomic e) := ⟨mul⟩

instance : Sub (Cyclotomic e) := ⟨fun x y => x + -y⟩
instance : SMul ℕ (Cyclotomic e) := ⟨nsmulRec⟩
instance : SMul ℤ (Cyclotomic e) := ⟨zsmulRec⟩
instance : Pow (Cyclotomic e) ℕ := ⟨fun x n => npowRec n x⟩
instance : NatCast (Cyclotomic e) := ⟨fun n => ofCoeffList e [n]⟩
instance : IntCast (Cyclotomic e) := ⟨fun z => ofCoeffList e [z]⟩

/-! The notation of the classes above, and the fields of the `CommRing` structure assembled below,
are the standalone operations defined here.  The next few lemmas name that identification once, so
that the proofs which need it can rewrite rather than appeal to definitional unfolding.  None of
them is `simp`: they unfold arithmetic into coefficient lists, which is the opposite direction to
the normal form everything else is stated in. -/

/-- Zero is the empty coefficient list. -/
theorem zero_def : (0 : Cyclotomic e) = ofCoeffList e [] := rfl

/-- One is the coefficient list `[1]`. -/
theorem one_def : (1 : Cyclotomic e) = ofCoeffList e [1] := rfl

/-- Addition adds coefficient lists entrywise. -/
theorem add_def (x y : Cyclotomic e) :
    x + y = ofCoeffList e (List.zipWith (fun a b => a + b) x.coeffs y.coeffs) := rfl

/-- Negation negates every coefficient. -/
theorem neg_def (x : Cyclotomic e) : -x = ofCoeffList e (x.coeffs.map (-·)) := rfl

/-- `TauCeti.Cyclotomic.neg` is the negation of the `Neg` instance. -/
theorem neg_eq (x : Cyclotomic e) : neg x = -x := rfl

/-- Multiplication convolves coefficient lists and reduces modulo `Φ_e`. -/
theorem mul_def (x y : Cyclotomic e) :
    x * y = ofCoeffList e (mulCoeffList x.coeffs y.coeffs) := rfl

/-- The polynomial represented by an exact cyclotomic integer. -/
noncomputable def toPolynomial (x : Cyclotomic e) : ℤ[X] :=
  TauCeti.Polynomial.ofCoeffList x.coeffs

/-- The coordinates of an exact cyclotomic integer are the coefficients of its canonical
polynomial representative. -/
@[simp]
theorem coeff_toPolynomial (x : Cyclotomic e) (j : ℕ) : x.toPolynomial.coeff j = x.coeff j := by
  rw [toPolynomial, TauCeti.Polynomial.coeff_ofCoeffList, coeff]

/-- The comparison map from computable cyclotomic integers to Mathlib's quotient by `Φ_e`. -/
noncomputable def toAdjoinRoot (x : Cyclotomic e) : AdjoinRoot (cyclotomic e ℤ) :=
  AdjoinRoot.mk _ x.toPolynomial

private theorem degree_toPolynomial_lt (x : Cyclotomic e) :
    x.toPolynomial.degree < (cyclotomic e ℤ).degree := by
  rw [degree_cyclotomic]
  simpa [toPolynomial] using degree_ofCoeffList_lt x.coeffs

private theorem modByMonic_toPolynomial (x : Cyclotomic e) :
    x.toPolynomial %ₘ cyclotomic e ℤ = x.toPolynomial :=
  (modByMonic_eq_self_iff (cyclotomic.monic e ℤ)).2 x.degree_toPolynomial_lt

/-- The comparison with `AdjoinRoot` is injective. -/
theorem toAdjoinRoot_injective : Function.Injective (toAdjoinRoot : Cyclotomic e → _) := by
  intro x y h
  have h' := congrArg (AdjoinRoot.modByMonicHom (cyclotomic.monic e ℤ)) h
  simp only [toAdjoinRoot, AdjoinRoot.modByMonicHom_mk, modByMonic_toPolynomial] at h'
  exact ext (eq_of_length_eq_of_ofCoeffList_eq (x.length_coeffs.trans y.length_coeffs.symm) h')

/-- The comparison map sends the exact cyclotomic integer built from a coefficient list to the
class of the polynomial with those coefficients: reduction modulo `Φ_e` is invisible in the
quotient. -/
@[simp]
theorem toAdjoinRoot_ofCoeffList (l : List ℤ) :
    toAdjoinRoot (ofCoeffList e l) = AdjoinRoot.mk _ (TauCeti.Polynomial.ofCoeffList l) := by
  rw [toAdjoinRoot, toPolynomial, coeffs_ofCoeffList, ofCoeffList_modByCyclotomic,
    AdjoinRoot.mk_eq_mk]
  rw [modByMonic_eq_sub_mul_div, sub_sub_cancel_left]
  exact dvd_neg.mpr (dvd_mul_right _ _)

@[simp]
theorem toAdjoinRoot_zero : toAdjoinRoot (0 : Cyclotomic e) = 0 := by
  rw [zero_def, toAdjoinRoot_ofCoeffList]
  simp

@[simp]
theorem toAdjoinRoot_one : toAdjoinRoot (1 : Cyclotomic e) = 1 := by
  rw [one_def, toAdjoinRoot_ofCoeffList]
  simp [TauCeti.Polynomial.ofCoeffList_cons]

@[simp]
theorem toAdjoinRoot_add (x y : Cyclotomic e) :
    toAdjoinRoot (x + y) = toAdjoinRoot x + toAdjoinRoot y := by
  rw [add_def, toAdjoinRoot_ofCoeffList, toAdjoinRoot, toAdjoinRoot]
  rw [← map_add]
  congr 1
  simpa [sub_eq_add_neg, toPolynomial] using
    (ofCoeffList_zipWith_sub (-1 : ℤ) (x.length_coeffs.trans y.length_coeffs.symm))

@[simp]
theorem toAdjoinRoot_neg (x : Cyclotomic e) :
    toAdjoinRoot (-x) = -toAdjoinRoot x := by
  rw [neg_def, toAdjoinRoot_ofCoeffList, toAdjoinRoot, toPolynomial, ofCoeffList_map_neg, map_neg]

@[simp]
theorem toAdjoinRoot_mul (x y : Cyclotomic e) :
    toAdjoinRoot (x * y) = toAdjoinRoot x * toAdjoinRoot y := by
  rw [mul_def, toAdjoinRoot_ofCoeffList, toAdjoinRoot, toAdjoinRoot, ← map_mul,
    ofCoeffList_mulCoeffList]
  simp only [toPolynomial]

instance : CommRing (Cyclotomic e) where
  add := add
  add_assoc a b c := toAdjoinRoot_injective (by simp only [toAdjoinRoot_add, add_assoc])
  zero := zero e
  zero_add a := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_add, toAdjoinRoot_zero, zero_add])
  add_zero a := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_add, toAdjoinRoot_zero, add_zero])
  nsmul := @nsmulRec (Cyclotomic e) ⟨zero e⟩ ⟨add⟩
  add_comm a b := toAdjoinRoot_injective (by simp only [toAdjoinRoot_add, add_comm])
  mul := mul
  mul_assoc a b c := toAdjoinRoot_injective (by simp only [toAdjoinRoot_mul, mul_assoc])
  one := one e
  one_mul a := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_mul, toAdjoinRoot_one, one_mul])
  mul_one a := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_mul, toAdjoinRoot_one, mul_one])
  npow := @npowRec (Cyclotomic e) ⟨one e⟩ ⟨mul⟩
  zero_mul a := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_mul, toAdjoinRoot_zero, zero_mul])
  mul_zero a := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_mul, toAdjoinRoot_zero, mul_zero])
  left_distrib a b c := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_add, toAdjoinRoot_mul, left_distrib])
  right_distrib a b c := toAdjoinRoot_injective (by
    simp only [toAdjoinRoot_add, toAdjoinRoot_mul, right_distrib])
  natCast n := ofCoeffList e [n]
  natCast_zero := toAdjoinRoot_injective (by
    rw [toAdjoinRoot_ofCoeffList, toAdjoinRoot_zero]
    simp [TauCeti.Polynomial.ofCoeffList_cons])
  natCast_succ n := toAdjoinRoot_injective (by
    rw [toAdjoinRoot_ofCoeffList, toAdjoinRoot_add, toAdjoinRoot_ofCoeffList,
      toAdjoinRoot_one]
    simp [TauCeti.Polynomial.ofCoeffList_cons])
  neg := neg
  sub := fun x y => add x (neg y)
  zsmul := @zsmulRec (Cyclotomic e) ⟨zero e⟩ ⟨add⟩ ⟨neg⟩
    (@nsmulRec (Cyclotomic e) ⟨zero e⟩ ⟨add⟩)
  sub_eq_add_neg := by intros; rfl
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  neg_add_cancel a := toAdjoinRoot_injective (by
    rw [toAdjoinRoot_add, neg_eq, toAdjoinRoot_neg, toAdjoinRoot_zero, neg_add_cancel])
  intCast z := ofCoeffList e [z]
  intCast_ofNat n := rfl
  intCast_negSucc n := toAdjoinRoot_injective (by
    -- The structure is still being assembled, so spell out its pending cast field.
    change toAdjoinRoot (ofCoeffList e [Int.negSucc n]) =
      toAdjoinRoot (neg (ofCoeffList e [(n + 1 : ℕ)]))
    rw [toAdjoinRoot_ofCoeffList, neg_eq, toAdjoinRoot_neg, toAdjoinRoot_ofCoeffList]
    simp [TauCeti.Polynomial.ofCoeffList_cons])
  mul_comm a b := toAdjoinRoot_injective (by simp only [toAdjoinRoot_mul, mul_comm])

/-! ## Comparison with `AdjoinRoot` -/

/-- The ring homomorphism identifying exact cyclotomic integers with the polynomial quotient. -/
noncomputable def toAdjoinRootRingHom : Cyclotomic e →+* AdjoinRoot (cyclotomic e ℤ) where
  toFun := toAdjoinRoot
  map_zero' := toAdjoinRoot_zero
  map_one' := toAdjoinRoot_one
  map_add' := toAdjoinRoot_add
  map_mul' := toAdjoinRoot_mul

@[simp]
theorem toAdjoinRootRingHom_apply (x : Cyclotomic e) :
    toAdjoinRootRingHom x = toAdjoinRoot x := (rfl)

/-- Every class modulo `Φ_e` has an exact coefficient-vector representative. -/
theorem toAdjoinRoot_surjective : Function.Surjective (toAdjoinRoot : Cyclotomic e → _) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨ofCoeffList e p.coeffList, ?_⟩
  rw [toAdjoinRoot_ofCoeffList, TauCeti.Polynomial.ofCoeffList_coeffList]

private theorem toAdjoinRootRingHom_bijective :
    Function.Bijective (toAdjoinRootRingHom (e := e)) :=
  ⟨fun _ _ h => toAdjoinRoot_injective (by simpa using h),
    fun z => (toAdjoinRoot_surjective z).imp fun _ h => by simpa using h⟩

/-- Exact cyclotomic integers are the quotient `ℤ[X] / (Φ_e)`. -/
noncomputable def equivAdjoinRoot :
    Cyclotomic e ≃+* AdjoinRoot (cyclotomic e ℤ) :=
  RingEquiv.ofBijective toAdjoinRootRingHom toAdjoinRootRingHom_bijective

@[simp]
theorem equivAdjoinRoot_apply (x : Cyclotomic e) : equivAdjoinRoot x = toAdjoinRoot x := by
  rw [equivAdjoinRoot, RingEquiv.ofBijective_apply, toAdjoinRootRingHom_apply]

/-- The distinguished generator `ζ`, represented by the polynomial `X`. -/
@[expose] def zeta (e : ℕ) : Cyclotomic e := ofCoeffList e [1, 0]

@[simp]
theorem toAdjoinRoot_zeta : toAdjoinRoot (zeta e) = AdjoinRoot.root (cyclotomic e ℤ) := by
  have hX : TauCeti.Polynomial.ofCoeffList ([1, 0] : List ℤ) = X := by
    simp [TauCeti.Polynomial.ofCoeffList_cons]
  rw [zeta, toAdjoinRoot_ofCoeffList, hX, AdjoinRoot.mk_X]

@[simp]
theorem equivAdjoinRoot_symm_root :
    (equivAdjoinRoot (e := e)).symm (AdjoinRoot.root (cyclotomic e ℤ)) = zeta e :=
  equivAdjoinRoot.symm_apply_eq.2 (by rw [equivAdjoinRoot_apply, toAdjoinRoot_zeta])

/-- A ring homomorphism out of the exact cyclotomic integers is determined by the image of the
distinguished generator `ζ`: the integers admit a unique ring homomorphism, and `ζ` generates
everything else. -/
theorem ringHom_ext {R : Type*} [CommRing R] {g₁ g₂ : Cyclotomic e →+* R}
    (h : g₁ (zeta e) = g₂ (zeta e)) : g₁ = g₂ := by
  have key : g₁.comp (equivAdjoinRoot (e := e)).symm.toRingHom
      = g₂.comp (equivAdjoinRoot (e := e)).symm.toRingHom :=
    AdjoinRoot.ringHom_ext (RingHom.ext_int _ _) (by simpa using h)
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := equivAdjoinRoot.symm.surjective x
  exact RingHom.congr_fun key y

/-! ## Evaluation and residue maps -/

/-- Evaluate exact cyclotomic integers at a root of the mapped cyclotomic polynomial. -/
noncomputable def evalRingHom {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) : Cyclotomic e →+* R :=
  (AdjoinRoot.lift f r hr).comp toAdjoinRootRingHom

/-- Evaluation at a root of `Φ_e` is evaluation of the canonical polynomial representative. -/
theorem evalRingHom_apply {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (x : Cyclotomic e) :
    evalRingHom f r hr x = x.toPolynomial.eval₂ f r := by
  rw [evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply, toAdjoinRoot,
    AdjoinRoot.lift_mk]

@[simp]
theorem evalRingHom_ofCoeffList {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (l : List ℤ) :
    evalRingHom f r hr (ofCoeffList e l) =
      (TauCeti.Polynomial.ofCoeffList l).eval₂ f r := by
  rw [evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply, toAdjoinRoot_ofCoeffList,
    AdjoinRoot.lift_mk]

/-- Evaluation at a root `r` of `Φ_e` sends the distinguished generator `ζ` to `r`. -/
@[simp]
theorem evalRingHom_zeta {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) : evalRingHom f r hr (zeta e) = r := by
  rw [evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply, toAdjoinRoot_zeta,
    AdjoinRoot.lift_root]

/-- `TauCeti.Cyclotomic.evalRingHom f r hr` is the *only* ring homomorphism sending the
distinguished generator `ζ` to `r`. -/
theorem eq_evalRingHom {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (cyclotomic e ℤ).eval₂ f r = 0) (g : Cyclotomic e →+* R) (hg : g (zeta e) = r) :
    g = evalRingHom f r hr :=
  ringHom_ext (by rw [hg, evalRingHom_zeta])

/-- Evaluate a coefficient vector by Horner's rule.  Unlike `Polynomial.eval₂`, this is a genuine
computation because it works directly on the finite list. -/
@[expose] def evalCoeffs {R : Type*} [Semiring R] (f : ℤ →+* R) (r : R)
    (x : Cyclotomic e) : R :=
  x.coeffs.foldl (fun y a => y * r + f a) 0

private theorem eval₂_ofCoeffList {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (l : List ℤ) :
    (TauCeti.Polynomial.ofCoeffList l).eval₂ f r =
      l.foldl (fun y a => y * r + f a) 0 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [TauCeti.Polynomial.ofCoeffList_concat, eval₂_add, eval₂_mul, eval₂_X, eval₂_C,
      List.foldl_append, ih]
    rfl

/-- Direct coefficient-list evaluation agrees with polynomial evaluation. -/
theorem evalCoeffs_eq_eval₂ {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (x : Cyclotomic e) :
    evalCoeffs f r x = x.toPolynomial.eval₂ f r := by
  rw [evalCoeffs, toPolynomial, eval₂_ofCoeffList]

/-- Reduction of exact cyclotomic integers in `ZMod p`, evaluated at a chosen residue `r`.
When `r` is an `e`-th primitive root, `TauCeti.Cyclotomic.reduceRingHom` packages this as a ring
homomorphism. -/
@[expose] def reduce (p : ℕ) (r : ZMod p) (x : Cyclotomic e) : ZMod p :=
  evalCoeffs (Int.castRingHom (ZMod p)) r x

/-- Reduction at an `e`-th primitive root in a prime field is a ring homomorphism. -/
noncomputable def reduceRingHom (p : ℕ) [Fact p.Prime] [NeZero e]
    (r : ZMod p) (hr : IsPrimitiveRoot r e) : Cyclotomic e →+* ZMod p :=
  evalRingHom (Int.castRingHom (ZMod p)) r <| by
    rw [← eval_map, map_cyclotomic]
    exact hr.isRoot_cyclotomic (NeZero.pos e)

@[simp]
theorem reduceRingHom_apply (p : ℕ) [Fact p.Prime] [NeZero e]
    (r : ZMod p) (hr : IsPrimitiveRoot r e) (x : Cyclotomic e) :
    reduceRingHom p r hr x = reduce p r x := by
  rw [reduceRingHom, reduce, evalRingHom, RingHom.comp_apply, toAdjoinRootRingHom_apply,
    toAdjoinRoot, AdjoinRoot.lift_mk, evalCoeffs_eq_eval₂]

/-- Reduction at an `e`-th primitive root sends the distinguished generator `ζ` to that root. -/
@[simp]
theorem reduce_zeta (p : ℕ) [Fact p.Prime] [NeZero e] (r : ZMod p) (hr : IsPrimitiveRoot r e) :
    reduce p r (zeta e) = r := by
  rw [← reduceRingHom_apply p r hr, reduceRingHom, evalRingHom_zeta]

/-! ## The distinguished complex embedding -/

/-- The distinguished complex primitive `e`-th root `exp (2πi/e)`. -/
noncomputable def complexRoot (e : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)

/-- For nonzero `e`, the distinguished root `TauCeti.Cyclotomic.complexRoot e = exp (2πi/e)` is a
primitive `e`-th root of unity.  This is what pins which complex root `ζ` names, and hence which
embedding `TauCeti.Cyclotomic.complexEmbedding` is. -/
theorem isPrimitiveRoot_complexRoot [NeZero e] : IsPrimitiveRoot (complexRoot e) e :=
  Complex.isPrimitiveRoot_exp e (NeZero.ne e)

/-- The distinguished complex root annihilates the integral cyclotomic polynomial. -/
theorem eval₂_cyclotomic_complexRoot [NeZero e] :
    (cyclotomic e ℤ).eval₂ (Int.castRingHom ℂ) (complexRoot e) = 0 := by
  rw [← eval_map, map_cyclotomic]
  exact (isPrimitiveRoot_complexRoot (e := e)).isRoot_cyclotomic (NeZero.pos e)

/-- The pinned embedding of exact cyclotomic integers into `ℂ`, sending `ζ` to
`exp (2πi/e)`. -/
noncomputable def complexEmbedding [NeZero e] : Cyclotomic e →+* ℂ :=
  evalRingHom (Int.castRingHom ℂ) (complexRoot e) eval₂_cyclotomic_complexRoot

/-- The pinned embedding evaluates the canonical polynomial representative at `exp (2πi/e)`. -/
theorem complexEmbedding_apply [NeZero e] (x : Cyclotomic e) :
    complexEmbedding x = Polynomial.aeval (complexRoot e) x.toPolynomial := by
  rw [complexEmbedding, evalRingHom_apply, aeval_def, algebraMap_int_eq]

@[simp]
theorem complexEmbedding_zeta [NeZero e] : complexEmbedding (zeta e) = complexRoot e := by
  rw [complexEmbedding, zeta, evalRingHom_ofCoeffList]
  simp [TauCeti.Polynomial.ofCoeffList_cons]

/-- The distinguished complex realization of exact cyclotomic integers is injective. -/
theorem complexEmbedding_injective [NeZero e] :
    Function.Injective (complexEmbedding : Cyclotomic e → ℂ) := by
  intro x y hxy
  have hzero : complexEmbedding (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have heval : Polynomial.aeval (complexRoot e) (x - y).toPolynomial = 0 := by
    rw [← complexEmbedding_apply]; exact hzero
  have hdiv : cyclotomic e ℤ ∣ (x - y).toPolynomial := by
    rw [cyclotomic_eq_minpoly isPrimitiveRoot_complexRoot (NeZero.pos e)]
    exact minpoly.isIntegrallyClosed_dvd
      (isPrimitiveRoot_complexRoot.isIntegral (NeZero.pos e)) heval
  have hp : (x - y).toPolynomial = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hdiv (degree_toPolynomial_lt (x - y))
  apply sub_eq_zero.mp
  apply toAdjoinRoot_injective
  rw [toAdjoinRoot, hp, map_zero, toAdjoinRoot_zero]

/-! The exact arithmetic reduces in the kernel.  In `Cyclotomic 5`, `ζ⁵ = 1`; reduction at
`2 : ZMod 5`, a primitive fourth root, sends `ζ + 1` to `3`. -/

example : (zeta 5 ^ 5).coeffs = (1 : Cyclotomic 5).coeffs := by decide

example : reduce 5 2 (zeta 4 + 1) = 3 := by decide

end Cyclotomic

end TauCeti
