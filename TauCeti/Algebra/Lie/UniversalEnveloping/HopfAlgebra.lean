/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Filtration
public import TauCeti.Algebra.Lie.UniversalEnveloping.KostantForm
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# The Hopf algebra structure on a universal enveloping algebra

The standard bialgebra structure on a universal enveloping algebra is a Hopf algebra. Its
antipode reverses products and negates the canonical Lie generators. This file joins the
independently useful bialgebra and antipode constructions and computes the antipode on the two
families used to generate the Kostant integral form.

The Hopf instance uses Mathlib's `HopfAlgebra.ofConvInverse`; multiplication of coalgebra
representations is handled by Mathlib's `Coalgebra.Repr.mul`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.instHopfAlgebra`: the canonical Hopf algebra structure.
* `TauCeti.UniversalEnvelopingAlgebra.hopfAntipode_eq_antipode`: the Hopf antipode is the
  previously constructed universal-enveloping antipode.
* `TauCeti.UniversalEnvelopingAlgebra.antipode_dividedPower_ι`: the antipode of a divided-power
  generator of the Kostant form.
* `TauCeti.UniversalEnvelopingAlgebra.antipode_choose_ι_succ`: the antipode of a Cartan-binomial
  generator, expressed as an integral combination of Cartan-binomial generators.

## Roadmap

This is a prerequisite for the Chevalley--Demazure construction in Layer 9 of the
ReductiveGroups roadmap. The Kostant integral form must be stable under comultiplication, counit,
and antipode before it can supply the integral Hopf data used in that construction.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open Coalgebra HopfAlgebra WithConv
open scoped RingTheory.LinearMap TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

private noncomputable def antipodeConv : WithConv (U →ₗ[R] U) :=
  toConv (antipode R)

private noncomputable def identityConv : WithConv (U →ₗ[R] U) :=
  toConv LinearMap.id

/-- The sum manipulation common to the two convolution computations below: an inner sum that
collapses to a scalar multiple of `1` factors out of the surrounding products. -/
private theorem sum_sum_mul_mul_eq_smul_sum {ια ιβ : Type*} (s : Finset ια) (t : Finset ιβ)
    (F G : ια → U) (P Q : ιβ → U) (r : R)
    (h : ∑ i ∈ s, F i * G i = r • (1 : U)) :
    ∑ j ∈ t, ∑ i ∈ s, P j * F i * (G i * Q j) = r • ∑ j ∈ t, P j * Q j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm (i : ια) : P j * F i * (G i * Q j) = P j * (F i * G i) * Q j := by
    simp only [mul_assoc]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, h, mul_smul_comm, mul_one, smul_mul_assoc]

private theorem antipodeConv_mul_apply (a b : U)
    (ha : (antipodeConv R L * identityConv R L) a =
      (Coalgebra.counit (R := R) a) • (1 : U)) :
    (antipodeConv R L * identityConv R L) (a * b) =
      (Coalgebra.counit (R := R) a) •
        (antipodeConv R L * identityConv R L) b := by
  let ra := Coalgebra.Repr.arbitrary R a
  let rb := Coalgebra.Repr.arbitrary R b
  have hra : ∑ i ∈ ra.index, antipode R (ra.left i) * ra.right i =
      (Coalgebra.counit (R := R) a) • (1 : U) := by
    rw [← ha]
    simpa [antipodeConv, identityConv] using
      (ra.convMul_apply (toConv (antipode R)) (toConv LinearMap.id)).symm
  rw [Coalgebra.Repr.convMul_apply (ra.mul rb)
    (antipodeConv R L) (identityConv R L),
    rb.convMul_apply (antipodeConv R L) (identityConv R L)]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, antipodeConv, identityConv, ofConv_toConv,
    UniversalEnvelopingAlgebra.antipode_mul_antidistrib, LinearMap.id_apply,
    Finset.sum_product]
  rw [Finset.sum_comm]
  exact sum_sum_mul_mul_eq_smul_sum R L ra.index rb.index
    (fun i => antipode R (ra.left i)) ra.right (fun j => antipode R (rb.left j)) rb.right _ hra

private theorem identityConv_mul_apply (a b : U)
    (hb : (identityConv R L * antipodeConv R L) b =
      (Coalgebra.counit (R := R) b) • (1 : U)) :
    (identityConv R L * antipodeConv R L) (a * b) =
      (Coalgebra.counit (R := R) b) •
        (identityConv R L * antipodeConv R L) a := by
  let ra := Coalgebra.Repr.arbitrary R a
  let rb := Coalgebra.Repr.arbitrary R b
  have hrb : ∑ j ∈ rb.index, rb.left j * antipode R (rb.right j) =
      (Coalgebra.counit (R := R) b) • (1 : U) := by
    rw [← hb]
    simpa [antipodeConv, identityConv] using
      (rb.convMul_apply (toConv LinearMap.id) (toConv (antipode R))).symm
  rw [Coalgebra.Repr.convMul_apply (ra.mul rb)
    (identityConv R L) (antipodeConv R L),
    ra.convMul_apply (identityConv R L) (antipodeConv R L)]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, antipodeConv, identityConv, ofConv_toConv,
    UniversalEnvelopingAlgebra.antipode_mul_antidistrib, LinearMap.id_apply,
    Finset.sum_product]
  exact sum_sum_mul_mul_eq_smul_sum R L rb.index ra.index
    rb.left (fun j => antipode R (rb.right j)) ra.left
    (fun i => antipode R (ra.right i)) _ hrb

private theorem antipodeConv_algebraMap (r : R) :
    (antipodeConv R L * identityConv R L) (algebraMap R U r) =
      (Coalgebra.counit (R := R) (algebraMap R U r)) • (1 : U) := by
  simp [antipodeConv, identityConv, LinearMap.convMul_apply, Algebra.smul_def]

private theorem antipodeConv_ι (x : L) :
    (antipodeConv R L * identityConv R L)
        (_root_.UniversalEnvelopingAlgebra.ι R x) =
      (Coalgebra.counit (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x)) • (1 : U) := by
  simp [antipodeConv, identityConv, LinearMap.convMul_apply]

private theorem identityConv_algebraMap (r : R) :
    (identityConv R L * antipodeConv R L) (algebraMap R U r) =
      (Coalgebra.counit (R := R) (algebraMap R U r)) • (1 : U) := by
  simp [antipodeConv, identityConv, LinearMap.convMul_apply, Algebra.smul_def]

private theorem identityConv_ι (x : L) :
    (identityConv R L * antipodeConv R L)
        (_root_.UniversalEnvelopingAlgebra.ι R x) =
      (Coalgebra.counit (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x)) • (1 : U) := by
  simp [antipodeConv, identityConv, LinearMap.convMul_apply]

/-- A linear endomorphism that agrees with `a ↦ ε a • 1` on scalars and on the canonical Lie
generators, and whose agreement set is closed under multiplication, agrees with it everywhere:
the elements where it agrees form a subalgebra, and the generators generate. -/
private theorem eq_counit_smul_one_of_ι (f : U →ₗ[R] U)
    (hmul : ∀ a b : U, f a = (Coalgebra.counit (R := R) a) • (1 : U) →
      f b = (Coalgebra.counit (R := R) b) • (1 : U) →
      f (a * b) = (Coalgebra.counit (R := R) (a * b)) • (1 : U))
    (halg : ∀ r : R, f (algebraMap R U r) =
      (Coalgebra.counit (R := R) (algebraMap R U r)) • (1 : U))
    (hι : ∀ x : L, f (_root_.UniversalEnvelopingAlgebra.ι R x) =
      (Coalgebra.counit (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x)) • (1 : U))
    (a : U) : f a = (Coalgebra.counit (R := R) a) • (1 : U) := by
  let s : Subalgebra R U :=
    { carrier := {a | f a = (Coalgebra.counit (R := R) a) • (1 : U)}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        exact hmul a b ha hb
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        simp only [map_add, ha, hb, add_smul]
      algebraMap_mem' := halg }
  have hs : Algebra.adjoin R
      (Set.range (_root_.UniversalEnvelopingAlgebra.ι R : L → U)) ≤ s := by
    apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    exact hι x
  rw [adjoin_range_ι R L] at hs
  exact hs (Set.mem_univ a)

private theorem antipodeConv_apply (a : U) :
    (antipodeConv R L * identityConv R L) a =
      (Coalgebra.counit (R := R) a) • (1 : U) :=
  eq_counit_smul_one_of_ι R L (antipodeConv R L * identityConv R L).ofConv
    (fun a b ha hb => by
      rw [antipodeConv_mul_apply R L a b ha, hb, Bialgebra.counit_mul]
      simp [smul_smul])
    (antipodeConv_algebraMap R L) (antipodeConv_ι R L) a

private theorem identityConv_apply (a : U) :
    (identityConv R L * antipodeConv R L) a =
      (Coalgebra.counit (R := R) a) • (1 : U) :=
  eq_counit_smul_one_of_ι R L (identityConv R L * antipodeConv R L).ofConv
    (fun a b ha hb => by
      rw [identityConv_mul_apply R L a b hb, ha, Bialgebra.counit_mul]
      simp [smul_smul, mul_comm])
    (identityConv_algebraMap R L) (identityConv_ι R L) a

/-- A universal enveloping algebra with its standard bialgebra structure is a Hopf algebra.

The antipode is the anti-automorphism constructed in
`TauCeti.UniversalEnvelopingAlgebra.Antipode`: it reverses products and negates every canonical Lie
generator. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R U :=
  HopfAlgebra.ofConvInverse (antipode R)
    (by
      apply WithConv.ext
      apply LinearMap.ext
      intro a
      simpa [antipodeConv, identityConv, Algebra.smul_def] using antipodeConv_apply R L a)
    (by
      apply WithConv.ext
      apply LinearMap.ext
      intro a
      simpa [antipodeConv, identityConv, Algebra.smul_def] using identityConv_apply R L a)

/-- The antipode supplied by the Hopf algebra instance is the canonical universal-enveloping
antipode constructed independently of the bialgebra structure. -/
@[simp]
theorem hopfAntipode_eq_antipode :
    HopfAlgebraStruct.antipode R (A := U) =
      UniversalEnvelopingAlgebra.antipode R := rfl

/-- The Hopf antipode negates each canonical Lie generator.

This is not a `simp` lemma: `hopfAntipode_eq_antipode` already rewrites the Hopf antipode to
`UniversalEnvelopingAlgebra.antipode`, after which the `simp` lemmas for that antipode apply. -/
theorem hopfAntipode_ι (x : L) :
    HopfAlgebraStruct.antipode R (_root_.UniversalEnvelopingAlgebra.ι R x) =
      -_root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [hopfAntipode_eq_antipode]
  exact antipode_ι R x

/-- The antipode commutes with the descending Pochhammer polynomial evaluated at an arbitrary
element. Although the antipode reverses products, the factors of `descPochhammer` evaluated at a
single element commute, so the reversal has no effect. -/
theorem antipode_descPochhammer (a : U) (n : ℕ) :
    antipode R ((descPochhammer ℤ n).smeval a) =
      (descPochhammer ℤ n).smeval (antipode R a) := by
  induction n with
  | zero =>
      simp [descPochhammer_zero]
  | succ n ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul,
        antipode_mul_antidistrib, ih, Polynomial.smeval_sub, Polynomial.smeval_X,
        Polynomial.smeval_natCast]
      simp only [map_sub]
      rw [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
        Polynomial.smeval_natCast]
      simp only [pow_one, pow_zero, nsmul_one]
      have hn : antipode R (n : U) = (n : U) := by
        rw [← map_natCast (algebraMap R U) n]
        exact antipode_algebraMap R (n : R)
      rw [hn]
      have hc := Polynomial.smeval_commute ℤ (Polynomial.X - (n : Polynomial ℤ))
        (descPochhammer ℤ n) (Commute.refl (antipode R a))
      have heval :
          (Polynomial.X - (n : Polynomial ℤ)).smeval (antipode R a) =
            antipode R a - (n : U) := by
        simp [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
      rw [heval] at hc
      exact hc.eq

section Rational

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L]

local notation "Uℚ" => _root_.UniversalEnvelopingAlgebra ℚ L

-- The `ℚ≥0`-action restricted along `algebraMap ℚ≥0 ℚ` is what makes the `BinomialRing`
-- machinery available on `Uℚ`; it is the same instance the Kostant form is elaborated with.
attribute [local instance] moduleNNRat BinomialRing.toIsAddTorsionFree

open Polynomial

/-- The antipode commutes with divided powers of an arbitrary element. Although the antipode
reverses products, a power involves only one element, so reversal has no effect. -/
@[simp]
theorem antipode_dividedPower (n : ℕ) (a : Uℚ) :
    antipode ℚ (Associative.dividedPower n a) =
      Associative.dividedPower n (antipode ℚ a) := by
  rw [Associative.dividedPower_def, map_smul, antipode_pow,
    Associative.dividedPower_def]

/-- The antipode of a divided-power Lie generator has the integral coefficient `(-1) ^ n`.
This is the first generator family of the Kostant form. -/
theorem antipode_dividedPower_ι (x : L) (n : ℕ) :
    antipode ℚ
        (Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) =
      (-1 : ℚ) ^ n •
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  rw [antipode_dividedPower, antipode_ι, Associative.dividedPower_neg]

/-- The antipode commutes with the binomial polynomial of an arbitrary element. -/
@[simp]
theorem antipode_choose (a : Uℚ) (n : ℕ) :
    antipode ℚ (Ring.choose a n) = Ring.choose (antipode ℚ a) n := by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← map_nsmul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  exact antipode_descPochhammer ℚ L a n

/-- The antipode of a Cartan-binomial Lie generator, in the standard shifted-binomial form. -/
theorem antipode_choose_ι (x : L) (n : ℕ) :
    antipode ℚ (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) n) =
      Int.negOnePow n •
        Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x + n - 1) n := by
  rw [antipode_choose, antipode_ι, Ring.choose_neg]

/-- The antipode of a positive-degree Cartan-binomial generator is an integral combination of
Cartan-binomial generators. This is the form that proves stability of the second generator family
of the Kostant form: all coefficients are ordinary integer binomial coefficients. -/
theorem antipode_choose_ι_succ (x : L) (n : ℕ) :
    antipode ℚ (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) (n + 1)) =
      Int.negOnePow (n + 1) •
        ∑ ij ∈ Finset.antidiagonal (n + 1),
          Nat.choose n ij.2 •
            Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ij.1 := by
  rw [antipode_choose_ι]
  have hcomm : Commute (_root_.UniversalEnvelopingAlgebra.ι ℚ x) (n : Uℚ) :=
    (Algebra.commutes (n : ℚ) _).symm
  have hshift :
      (_root_.UniversalEnvelopingAlgebra.ι ℚ x + (n + 1 : ℕ) - 1 : Uℚ) =
        _root_.UniversalEnvelopingAlgebra.ι ℚ x + n := by
    rw [Nat.cast_add, Nat.cast_one]
    abel
  rw [hshift]
  rw [Ring.add_choose_eq (n + 1) hcomm]
  apply congrArg (Int.negOnePow (n + 1) • ·)
  apply Finset.sum_congr rfl
  intro ij _
  rw [Ring.choose_natCast]
  rw [← Nat.cast_smul_eq_nsmul ℚ, Algebra.smul_def]
  exact (Algebra.commutes (Nat.choose n ij.2 : ℚ) _).symm

end Rational

end TauCeti.UniversalEnvelopingAlgebra
