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

private theorem antipodeConv_mul_apply (a b : U)
    (ha : (antipodeConv R L * identityConv R L) a =
      (Coalgebra.counit (R := R) a) • (1 : U)) :
    (antipodeConv R L * identityConv R L) (a * b) =
      (Coalgebra.counit (R := R) a) •
        (antipodeConv R L * identityConv R L) b := by
  let ra := Coalgebra.Repr.arbitrary R a
  let rb := Coalgebra.Repr.arbitrary R b
  rw [Coalgebra.Repr.convMul_apply (ra.mul rb)
    (antipodeConv R L) (identityConv R L)]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, antipodeConv, identityConv, ofConv_toConv,
    UniversalEnvelopingAlgebra.antipode_mul_antidistrib, LinearMap.id_apply,
    Finset.sum_product]
  rw [Finset.sum_comm]
  rw [rb.convMul_apply (toConv (antipode R)) (toConv LinearMap.id), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hterm (i : U × U) :
      antipode R (rb.left j) * antipode R (ra.left i) *
          (ra.right i * rb.right j) =
        antipode R (rb.left j) *
          ((antipode R (ra.left i) * ra.right i) * rb.right j) := by
    simp only [mul_assoc]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hra :
      (∑ i ∈ ra.index, antipode R (ra.left i) * ra.right i) =
        (antipodeConv R L * identityConv R L) a := by
    simpa [antipodeConv, identityConv] using
      (ra.convMul_apply (toConv (antipode R)) (toConv LinearMap.id)).symm
  rw [hra, ha]
  simp

private theorem identityConv_mul_apply (a b : U)
    (hb : (identityConv R L * antipodeConv R L) b =
      (Coalgebra.counit (R := R) b) • (1 : U)) :
    (identityConv R L * antipodeConv R L) (a * b) =
      (Coalgebra.counit (R := R) b) •
        (identityConv R L * antipodeConv R L) a := by
  let ra := Coalgebra.Repr.arbitrary R a
  let rb := Coalgebra.Repr.arbitrary R b
  rw [Coalgebra.Repr.convMul_apply (ra.mul rb)
    (identityConv R L) (antipodeConv R L)]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, antipodeConv, identityConv, ofConv_toConv,
    UniversalEnvelopingAlgebra.antipode_mul_antidistrib, LinearMap.id_apply,
    Finset.sum_product]
  rw [ra.convMul_apply (toConv LinearMap.id) (toConv (antipode R)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hterm (j : U × U) :
      ra.left i * rb.left j *
          (antipode R (rb.right j) * antipode R (ra.right i)) =
        ra.left i *
          ((rb.left j * antipode R (rb.right j)) * antipode R (ra.right i)) := by
    simp only [mul_assoc]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hrb :
      (∑ j ∈ rb.index, rb.left j * antipode R (rb.right j)) =
        (identityConv R L * antipodeConv R L) b := by
    simpa [antipodeConv, identityConv] using
      (rb.convMul_apply (toConv LinearMap.id) (toConv (antipode R))).symm
  rw [hrb, hb]
  simp

private theorem adjoin_range_ι :
    Algebra.adjoin R (Set.range (_root_.UniversalEnvelopingAlgebra.ι R : L → U)) = ⊤ := by
  rw [← (UniversalEnvelopingAlgebra.mkAlgHom R L).range_eq_top.mpr
    (RingCon.mk'_surjective (UniversalEnvelopingAlgebra.ringCon R L))]
  rw [← Algebra.map_top, ← TensorAlgebra.adjoin_range_ι, AlgHom.map_adjoin]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨TensorAlgebra.ι R z, ⟨z, rfl⟩,
      by simp [_root_.UniversalEnvelopingAlgebra.ι_apply]⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, by simp [_root_.UniversalEnvelopingAlgebra.ι_apply]⟩

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

private theorem antipodeConv_apply (a : U) :
    (antipodeConv R L * identityConv R L) a =
      (Coalgebra.counit (R := R) a) • (1 : U) := by
  let s : Subalgebra R U :=
    { carrier := {a | (antipodeConv R L * identityConv R L) a =
          (Coalgebra.counit (R := R) a) • (1 : U)}
      mul_mem' := by
        intro a b ha hb
        -- Membership in this local subalgebra is the displayed convolution identity.
        change (antipodeConv R L * identityConv R L) (a * b) = _
        change (antipodeConv R L * identityConv R L) a = _ at ha
        change (antipodeConv R L * identityConv R L) b = _ at hb
        rw [antipodeConv_mul_apply R L a b ha, hb, Bialgebra.counit_mul]
        simp [smul_smul]
      add_mem' := by
        intro a b ha hb
        -- Membership in this local subalgebra is the displayed convolution identity.
        change (antipodeConv R L * identityConv R L) (a + b) = _
        change (antipodeConv R L * identityConv R L) a = _ at ha
        change (antipodeConv R L * identityConv R L) b = _ at hb
        simp only [map_add, ha, hb, add_smul]
      algebraMap_mem' := antipodeConv_algebraMap R L }
  have hs : Algebra.adjoin R
      (Set.range (_root_.UniversalEnvelopingAlgebra.ι R : L → U)) ≤ s := by
    apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    exact antipodeConv_ι R L x
  rw [adjoin_range_ι R L] at hs
  exact hs (Set.mem_univ a)

private theorem identityConv_apply (a : U) :
    (identityConv R L * antipodeConv R L) a =
      (Coalgebra.counit (R := R) a) • (1 : U) := by
  let s : Subalgebra R U :=
    { carrier := {a | (identityConv R L * antipodeConv R L) a =
          (Coalgebra.counit (R := R) a) • (1 : U)}
      mul_mem' := by
        intro a b ha hb
        -- Membership in this local subalgebra is the displayed convolution identity.
        change (identityConv R L * antipodeConv R L) (a * b) = _
        change (identityConv R L * antipodeConv R L) a = _ at ha
        change (identityConv R L * antipodeConv R L) b = _ at hb
        rw [identityConv_mul_apply R L a b hb, ha, Bialgebra.counit_mul]
        simp [smul_smul, mul_comm]
      add_mem' := by
        intro a b ha hb
        -- Membership in this local subalgebra is the displayed convolution identity.
        change (identityConv R L * antipodeConv R L) (a + b) = _
        change (identityConv R L * antipodeConv R L) a = _ at ha
        change (identityConv R L * antipodeConv R L) b = _ at hb
        simp only [map_add, ha, hb, add_smul]
      algebraMap_mem' := identityConv_algebraMap R L }
  have hs : Algebra.adjoin R
      (Set.range (_root_.UniversalEnvelopingAlgebra.ι R : L → U)) ≤ s := by
    apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    exact identityConv_ι R L x
  rw [adjoin_range_ι R L] at hs
  exact hs (Set.mem_univ a)

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

/-- The Hopf antipode negates each canonical Lie generator. -/
@[simp]
theorem hopfAntipode_ι (x : L) :
    HopfAlgebraStruct.antipode R (_root_.UniversalEnvelopingAlgebra.ι R x) =
      -_root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [hopfAntipode_eq_antipode]
  exact antipode_ι R x

section Rational

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L]

local notation "Uℚ" => _root_.UniversalEnvelopingAlgebra ℚ L

noncomputable local instance moduleNNRat : Module ℚ≥0 Uℚ :=
  Module.compHom _ (algebraMap ℚ≥0 ℚ)

attribute [local instance] BinomialRing.toIsAddTorsionFree

open Polynomial

/-- The antipode commutes with divided powers of an arbitrary element. Although the antipode
reverses products, a power involves only one element, so reversal has no effect. -/
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

private theorem antipode_descPochhammer (a : Uℚ) (n : ℕ) :
    antipode ℚ ((descPochhammer ℤ n).smeval a) =
      (descPochhammer ℤ n).smeval (antipode ℚ a) := by
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
      have hn : antipode ℚ (n : Uℚ) = n := by
        simpa using antipode_algebraMap ℚ (L := L) (n : ℚ)
      rw [hn]
      have hc := Polynomial.smeval_commute ℤ (Polynomial.X - (n : ℤ[X]))
        (descPochhammer ℤ n) (Commute.refl (antipode ℚ a))
      have heval :
          (Polynomial.X - (n : ℤ[X])).smeval (antipode ℚ a) =
            antipode ℚ a - (n : Uℚ) := by
        simp [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
      rw [heval] at hc
      exact hc.eq

/-- The antipode commutes with the binomial polynomial of an arbitrary element. -/
theorem antipode_choose (a : Uℚ) (n : ℕ) :
    antipode ℚ (Ring.choose a n) = Ring.choose (antipode ℚ a) n := by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← map_nsmul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  exact antipode_descPochhammer a n

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
