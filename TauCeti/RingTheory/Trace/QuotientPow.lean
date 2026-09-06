/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.LinearAlgebra.Trace.Exact
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The trace of a quotient by a power of a prime

Let `B` be a Dedekind domain over a commutative ring `A`, let `p` be a maximal ideal of `A` with
residue field `κ = A ⧸ p`, and let `P` be a maximal ideal of `B` with `p · B ⊆ P ^ n`, so that
`B ⧸ P ^ n` is a `κ`-algebra.  This file computes the trace of that algebra:

`Tr_{(B ⧸ P ^ n) / κ} (z) = n · Tr_{(B ⧸ P) / κ} (z)`.

The `P`-adic filtration of `B ⧸ P ^ n` has `n` graded pieces, each of them a copy of the residue
field `B ⧸ P` on which multiplication by `z` acts as multiplication by the residue of `z`; the
trace of an endomorphism of a filtered vector space is the sum of the traces on the pieces, so the
`n` copies contribute `n` equal summands.  The induction runs over one step of the filtration at a
time, through the short exact sequence

`0 → B ⧸ P --· a--> B ⧸ P ^ (n + 1) → B ⧸ P ^ n → 0`,

where `a` is any element of `P ^ n` not in `P ^ (n + 1)`; injectivity of multiplication by `a` and
exactness in the middle are the two Dedekind facts
`Ideal.IsPrime.mem_pow_mul` and `Ideal.exists_mul_add_mem_pow_succ`, and the trace
identity is `LinearMap.trace_eq_add_of_exact`.

The formula is what makes the tame case of Dedekind's different theorem work: it produces an
element of `B ⧸ P ^ e` with nonzero trace as soon as the residue extension is separable and the
characteristic of `κ` does not divide `e` (see
`TauCeti.RingTheory.DedekindDomain.Different`, where it is combined with Mathlib's trace
computation for `B ⧸ p · B`, `Algebra.trace_quotient_eq_of_isDedekindDomain`).

## Main results

* `Algebra.trace_quotient_pow`: the trace formula `Tr_{B ⧸ P ^ n} = n · Tr_{B ⧸ P}`.
-/

public section

open Module

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain B]
variable {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/-- **The trace of a quotient by a prime power.** For `P` a maximal ideal of a Dedekind domain `B`
that is module-finite over `A`, and `p` a maximal ideal of `A` making both `B ⧸ P ^ n` and `B ⧸ P`
algebras over the residue field `A ⧸ p`, the trace of the residue of `z` in `B ⧸ P ^ n` is `n`
times its trace in the residue field `B ⧸ P`.

The two `IsScalarTower` hypotheses pin the algebra structures to the ones induced by `A → B`;
they are what `Ideal.Quotient.algebraQuotientOfLEComap` provides, and they hold for `B ⧸ P ^ n`
exactly when `p · B ⊆ P ^ n`. -/
theorem trace_quotient_pow [Module.Finite A B] (hP : P ≠ ⊥) (n : ℕ)
    [instA : Algebra (A ⧸ p) (B ⧸ P ^ n)] [instT : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n)]
    [Algebra (A ⧸ p) (B ⧸ P)] [IsScalarTower A (A ⧸ p) (B ⧸ P)] (z : B) :
    Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z) =
      n • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z) := by
  induction n generalizing instA instT with
  | zero =>
      have : Subsingleton (B ⧸ P ^ 0) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero]
        exact Ideal.one_eq_top
      rw [Subsingleton.elim (Ideal.Quotient.mk (P ^ 0) z) 0, map_zero, zero_smul]
  | succ n ih =>
      have := Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ (n + 1))
      -- the base ideal is carried into `P ^ (n + 1)`, hence into `P ^ n`
      have hcomap : p ≤ Ideal.comap (algebraMap A B) (P ^ (n + 1)) := by
        intro x hx
        have h0 : algebraMap A (B ⧸ P ^ (n + 1)) x = 0 := by
          rw [IsScalarTower.algebraMap_apply A (A ⧸ p) (B ⧸ P ^ (n + 1)),
            Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
        rwa [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      have hcomap' : p ≤ Ideal.comap (algebraMap A B) (P ^ n) :=
        hcomap.trans (Ideal.comap_mono (Ideal.pow_le_pow_right n.le_succ))
      let instA' : Algebra (A ⧸ p) (B ⧸ P ^ n) := Ideal.Quotient.algebraQuotientOfLEComap hcomap'
      let instT' : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n) := IsScalarTower.of_algebraMap_eq' rfl
      have := Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ n)
      have := Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)
      -- an element generating `P ^ n` modulo `P ^ (n + 1)`
      obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP
        (Ideal.IsPrime.ne_top inferInstance) n
      -- the two maps of the short exact sequence, `B`-linearly
      have hmul : P ≤ Submodule.comap (LinearMap.mulLeft B a) (P ^ (n + 1)) := fun x hx ↦ by
        simpa [pow_succ] using Ideal.mul_mem_mul ha hx
      have hfac : P ^ (n + 1) ≤ Submodule.comap (LinearMap.id (R := B) (M := B)) (P ^ n) :=
        Ideal.pow_le_pow_right n.le_succ
      have hsurj : Function.Surjective (algebraMap A (A ⧸ p)) := Ideal.Quotient.mk_surjective
      set i : (B ⧸ P) →ₗ[A ⧸ p] (B ⧸ P ^ (n + 1)) :=
        ((Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a) hmul).restrictScalars
          A).extendScalarsOfSurjective hsurj with hi_def
      set pi : (B ⧸ P ^ (n + 1)) →ₗ[A ⧸ p] (B ⧸ P ^ n) :=
        ((Submodule.mapQ (P ^ (n + 1)) (P ^ n) LinearMap.id hfac).restrictScalars
          A).extendScalarsOfSurjective hsurj with hpi_def
      have hi_apply (x : B) : i (Ideal.Quotient.mk P x) = Ideal.Quotient.mk (P ^ (n + 1)) (a * x) :=
        rfl
      have hpi_apply (x : B) :
          pi (Ideal.Quotient.mk (P ^ (n + 1)) x) = Ideal.Quotient.mk (P ^ n) x := rfl
      -- the sequence `0 → B ⧸ P → B ⧸ P ^ (n + 1) → B ⧸ P ^ n → 0` is exact
      have hinj : Function.Injective i := by
        rw [injective_iff_map_eq_zero]
        intro y hy
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [hi_apply, Ideal.Quotient.eq_zero_iff_mem] at hy
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact (Ideal.IsPrime.mem_pow_mul P hy).resolve_left ha'
      have hsur : Function.Surjective pi := fun y ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ x, hpi_apply x⟩
      have hex : Function.Exact i pi := by
        intro y
        obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [hpi_apply, Ideal.Quotient.eq_zero_iff_mem]
        constructor
        · intro hu
          obtain ⟨x, w, hw, rfl⟩ :=
            Ideal.exists_mul_add_mem_pow_succ hP a u ha ha' hu
          refine ⟨Ideal.Quotient.mk P x, ?_⟩
          rw [hi_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem, sub_add_cancel_left]
          exact neg_mem hw
        · rintro ⟨y, hy⟩
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [hi_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hy
          rw [← sub_sub_cancel (a * x) u]
          exact sub_mem (Ideal.mul_mem_right x _ ha) (Ideal.pow_le_pow_right n.le_succ hy)
      -- multiplication by `z` is an endomorphism of the whole sequence
      set f : Module.End (A ⧸ p) (B ⧸ P ^ (n + 1)) :=
        Algebra.lmul (A ⧸ p) _ (Ideal.Quotient.mk _ z) with hf
      set fN : Module.End (A ⧸ p) (B ⧸ P) :=
        Algebra.lmul (A ⧸ p) _ (Ideal.Quotient.mk _ z) with hfN
      set fQ : Module.End (A ⧸ p) (B ⧸ P ^ n) :=
        Algebra.lmul (A ⧸ p) _ (Ideal.Quotient.mk _ z) with hfQ
      have hf_apply (y : B ⧸ P ^ (n + 1)) : f y = Ideal.Quotient.mk (P ^ (n + 1)) z * y := rfl
      have hfN_apply (y : B ⧸ P) : fN y = Ideal.Quotient.mk P z * y := rfl
      have hfQ_apply (y : B ⧸ P ^ n) : fQ y = Ideal.Quotient.mk (P ^ n) z * y := rfl
      have hN : f ∘ₗ i = i ∘ₗ fN := by
        refine LinearMap.ext fun y ↦ ?_
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hf_apply, hfN_apply, hi_apply, ← map_mul,
          ← map_mul, hi_apply]
        exact congrArg _ (by ring)
      have hQ : pi ∘ₗ f = fQ ∘ₗ pi := by
        refine LinearMap.ext fun y ↦ ?_
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hf_apply, hfQ_apply, ← map_mul, hpi_apply,
          hpi_apply, map_mul]
      have e1 : Algebra.trace (A ⧸ p) (B ⧸ P ^ (n + 1)) (Ideal.Quotient.mk _ z)
          = LinearMap.trace (A ⧸ p) _ f := Algebra.trace_apply _ _
      have e2 : Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z)
          = LinearMap.trace (A ⧸ p) _ fN := Algebra.trace_apply _ _
      have e3 : Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z)
          = LinearMap.trace (A ⧸ p) _ fQ := Algebra.trace_apply _ _
      rw [e1, LinearMap.trace_eq_add_of_exact hinj hsur hex hN hQ, ← e2, ← e3, ih,
        succ_nsmul']

end Algebra
