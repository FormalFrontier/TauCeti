/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.Trace.Prod

/-!
# The trace of an endomorphism of a short exact sequence

An endomorphism of a short exact sequence `0 → N → M → Q → 0` of vector spaces, `M`
finite-dimensional, has `trace f = trace fN + trace fQ`.

The typical use is a filtration whose graded pieces are known: iterating the identity along
`M ⊇ M₁ ⊇ ⋯` expresses `trace f` as the sum of the traces on the successive quotients.  That is how
`Algebra.trace_quotient_pow` computes the trace of `B ⧸ P ^ n` from the trace of `B ⧸ P`.

## Main results

* `LinearMap.trace_eq_add_of_exact`: the trace of the middle endomorphism of a short exact sequence
  is the sum of the traces of the outer ones.
-/

public section

open Module

namespace LinearMap

variable {K M N Q : Type*} [Field K]
variable [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q]

/-- **The trace is additive along a short exact sequence.** If `0 → N --i--> M --π--> Q → 0` is
exact and the endomorphisms `fN`, `f`, `fQ` commute with `i` and `π`, then
`trace f = trace fN + trace fQ`.

This generalizes the former private `TauCeti.TensorSquare.trace_eq_add_of_exact` implementation. -/
theorem trace_eq_add_of_exact [FiniteDimensional K M] {i : N →ₗ[K] M} {π : M →ₗ[K] Q}
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : Function.Exact i π)
    {f : M →ₗ[K] M} {fN : N →ₗ[K] N} {fQ : Q →ₗ[K] Q}
    (hN : f ∘ₗ i = i ∘ₗ fN) (hQ : π ∘ₗ f = fQ ∘ₗ π) :
    trace K M f = trace K N fN + trace K Q fQ := by
  have _ : FiniteDimensional K N := FiniteDimensional.of_injective i hi
  have _ : FiniteDimensional K Q := Module.Finite.of_surjective π hπ
  -- choose a linear section of `π`
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (range_eq_top.mpr hπ)
  obtain ⟨E, hiE, hπE⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  have hi_apply (n : N) : E.symm (n, 0) = i n := by
    simpa using congr($hiE n).symm
  -- transport `f` to `N × Q`; it is block upper triangular there
  set F : (N × Q) →ₗ[K] N × Q := E.conj f with hF
  have hFapply (x : N × Q) : F x = E (f (E.symm x)) := by
    simp [hF, LinearEquiv.conj_apply]
  have hsnd (m : M) : (E m).2 = π m := by
    simpa using congr($hπE m).symm
  have hinl : F ∘ₗ (inl K N Q) = (inl K N Q) ∘ₗ fN := by
    refine ext fun n ↦ E.symm.injective ?_
    have hfi : f (i n) = i (fN n) := congr($hN n)
    simp only [comp_apply, inl_apply, hFapply, E.symm_apply_apply, hi_apply]
    exact hfi
  have hsnd' : (snd K N Q) ∘ₗ F = fQ ∘ₗ (snd K N Q) := by
    refine ext fun x ↦ ?_
    have h₃ : π (f (E.symm x)) = fQ (π (E.symm x)) := congr($hQ (E.symm x))
    simp only [comp_apply, snd_apply, hFapply, hsnd, h₃]
    rw [← hsnd (E.symm x), E.apply_symm_apply]
  rw [← LinearMap.trace_conj' f E, ← hF,
    eq_prodMap_add_inl_comp_snd (fA := fN) (fC := fQ) F hinl hsnd',
    trace_prodMap_add_inl_comp_snd]

end LinearMap
