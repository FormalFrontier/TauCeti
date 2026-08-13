/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Filtration

/-!
# The Hopf algebra structure on a universal enveloping algebra

The standard bialgebra structure on a universal enveloping algebra is a Hopf algebra. Its
antipode reverses products and negates the canonical Lie generators. This file joins the
independently useful bialgebra and antipode constructions: the antipode is a two-sided
convolution inverse of the identity.

The Hopf instance uses Mathlib's `HopfAlgebra.ofConvInverse`; multiplication of coalgebra
representations is handled by Mathlib's `Coalgebra.Repr.mul`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.instHopfAlgebra`: the canonical Hopf algebra structure.
* `TauCeti.UniversalEnvelopingAlgebra.hopfAntipode_eq_antipode`: the Hopf antipode is the
  previously constructed universal-enveloping antipode.

## Roadmap

This is a prerequisite for the Chevalley--Demazure construction in Layer 9 of the
ReductiveGroups roadmap. The Kostant integral form must be stable under comultiplication, counit,
and antipode before it can supply the integral Hopf data used in that construction; the ambient
Hopf structure is what those operations restrict from.

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

end TauCeti.UniversalEnvelopingAlgebra
