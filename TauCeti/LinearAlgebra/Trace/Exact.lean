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
finite-dimensional, has `trace f = trace fN + trace fQ`.  A linear section of the surjection splits
the sequence as `M ≃ N × Q`, and in that decomposition the endomorphism is block upper triangular
because it preserves the image of `N`, so `LinearMap.trace_prodMap_add_inl_comp_snd` computes its
trace from the two diagonal blocks.

Mathlib has the additivity of the trace over an *internal direct sum*
(`LinearMap.trace_eq_sum_trace_restrict`), which needs the endomorphism to preserve every summand.
An endomorphism of a short exact sequence only respects the filtration, not any splitting of it, so
that result does not apply: the splitting has to be chosen independently of `f`, and the
off-diagonal block is then killed by `LinearMap.trace_comp_comm'` rather than being zero.  Working
over a field is what makes such a splitting available.

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
`trace f = trace fN + trace fQ`. -/
theorem trace_eq_add_of_exact [FiniteDimensional K M] {i : N →ₗ[K] M} {π : M →ₗ[K] Q}
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : Function.Exact i π)
    {f : M →ₗ[K] M} {fN : N →ₗ[K] N} {fQ : Q →ₗ[K] Q}
    (hN : f ∘ₗ i = i ∘ₗ fN) (hQ : π ∘ₗ f = fQ ∘ₗ π) :
    trace K M f = trace K N fN + trace K Q fQ := by
  have _ : FiniteDimensional K N := FiniteDimensional.of_injective i hi
  have _ : FiniteDimensional K Q := Module.Finite.of_surjective π hπ
  -- choose a linear section of `π`
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (range_eq_top.mpr hπ)
  -- the section splits the sequence: `(n, q) ↦ i n + s q` is an isomorphism `N × Q ≃ M`
  have hπs (q : Q) : π (s q) = q := congr($hs q)
  have hπi (n : N) : π (i n) = 0 := hex.apply_apply_eq_zero n
  have hbij : Function.Bijective (i.coprod s) := by
    constructor
    · rintro ⟨n, q⟩ ⟨n', q'⟩ h
      simp only [coprod_apply] at h
      have hq : q = q' := by simpa [hπi, hπs] using congrArg π h
      subst hq
      exact Prod.ext (hi (by simpa using h)) rfl
    · intro m
      obtain ⟨n, hn⟩ := (hex (m - s (π m))).mp (by simp [hπs])
      exact ⟨(n, π m), by simp [hn]⟩
  set E : (N × Q) ≃ₗ[K] M := LinearEquiv.ofBijective (i.coprod s) hbij with hE
  have hEapply (n : N) (q : Q) : E (n, q) = i n + s q := rfl
  -- `snd` reads off the quotient component through `π`
  have hsnd : (snd K N Q) ∘ₗ (E.symm : M →ₗ[K] N × Q) = π := by
    refine ext fun m ↦ ?_
    have : E (E.symm m) = m := E.apply_symm_apply m
    conv_rhs => rw [← this]
    rw [hEapply]
    simp [hπi, hπs]
  -- transport `f` to `N × Q`; it is block upper triangular there
  set F : (N × Q) →ₗ[K] N × Q := E.symm.conj f with hF
  have hFapply (x : N × Q) : F x = E.symm (f (E x)) := by
    simp [hF, LinearEquiv.conj_apply]
  have hsnd₂ (m : M) : (E.symm m).2 = π m := congr($hsnd m)
  have hinl : F ∘ₗ (inl K N Q) = (inl K N Q) ∘ₗ fN := by
    refine ext fun n ↦ E.injective ?_
    have hfi : f (i n) = i (fN n) := congr($hN n)
    simp only [comp_apply, inl_apply, hFapply, E.apply_symm_apply, hEapply, map_zero, add_zero]
    exact hfi
  have hsnd' : (snd K N Q) ∘ₗ F = fQ ∘ₗ (snd K N Q) := by
    refine ext fun x ↦ ?_
    have h₃ : π (f (E x)) = fQ (π (E x)) := congr($hQ (E x))
    simp only [comp_apply, snd_apply, hFapply, hsnd₂, h₃]
    rw [← hsnd₂ (E x), E.symm_apply_apply]
  rw [← LinearMap.trace_conj' f E.symm, ← hF,
    eq_prodMap_add_inl_comp_snd (fA := fN) (fC := fQ) F hinl hsnd',
    trace_prodMap_add_inl_comp_snd]

end LinearMap
