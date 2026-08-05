/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Block upper triangular endomorphisms of a product

An endomorphism `F` of `A × C` that preserves the first summand, acting there as `fA`, and covers
`fC` on the second is *block upper triangular*: its only off-diagonal block is the `C → A` map
`fst ∘ F ∘ inr`. This file records that normal form and the resulting trace identity.

## Main results

* `LinearMap.eq_prodMap_add_inl_comp_snd` — the normal form, over an arbitrary semiring.
* `LinearMap.trace_prodMap_add_inl_comp_snd` — the trace of a block upper triangular endomorphism
  is the sum of the traces of its diagonal blocks.

The trace identity needs free finite modules over a commutative ring, since that is what Mathlib's
`LinearMap.trace_prodMap'` and `LinearMap.trace_comp_comm'` require; the normal form itself needs
neither commutativity, finiteness, nor additive inverses.
-/

public section

namespace LinearMap

/-- An endomorphism of `A × C` that preserves the first summand, acting there as `fA`, and covers
`fC` on the second, is block upper triangular: its only off-diagonal block is `C → A`. -/
theorem eq_prodMap_add_inl_comp_snd {R A C : Type*} [Semiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid C] [Module R C]
    {fA : A →ₗ[R] A} {fC : C →ₗ[R] C} (F : (A × C) →ₗ[R] A × C)
    (hinl : F.comp (inl R A C) = (inl R A C).comp fA)
    (hsnd : (snd R A C).comp F = fC.comp (snd R A C)) :
    F = prodMap fA fC + (inl R A C).comp
      (((fst R A C).comp (F.comp (inr R A C))).comp (snd R A C)) := by
  refine prod_ext ?_ ?_
  · -- On the `A` summand the off-diagonal block dies, since `snd ∘ inl = 0`.
    rw [hinl]
    refine ext fun a => ?_
    simp [Prod.mk_zero_zero]
  · -- On the `C` summand the first component is the off-diagonal block by definition, and the
    -- second is `hsnd` read at `inr c`.
    refine ext fun c => Prod.ext ?_ ?_
    · simp
    · simpa using LinearMap.congr_fun hsnd ((inr R A C) c)

/-- The trace of a block upper triangular endomorphism of `A × C` is the sum of the traces of its
diagonal blocks: the off-diagonal `C → A` block composes to zero the other way round, so
`LinearMap.trace_comp_comm'` makes its contribution vanish. -/
theorem trace_prodMap_add_inl_comp_snd {R A C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Free R A] [Module.Finite R A]
    [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
    (fA : A →ₗ[R] A) (fC : C →ₗ[R] C) (u : C →ₗ[R] A) :
    trace R (A × C) (prodMap fA fC + (inl R A C).comp (u.comp (snd R A C)))
      = trace R A fA + trace R C fC := by
  have hoff : trace R (A × C) ((inl R A C).comp (u.comp (snd R A C))) = 0 := by
    rw [trace_comp_comm']
    have hz : (u.comp (snd R A C)).comp (inl R A C) = 0 := by ext a; simp
    rw [hz, map_zero]
  rw [map_add, trace_prodMap', hoff, add_zero]

end LinearMap
