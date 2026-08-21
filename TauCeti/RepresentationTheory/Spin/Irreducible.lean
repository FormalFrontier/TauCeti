/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Structure
-- Private: `IsSimpleModule.toSpanSingleton_surjective` is used only inside proofs.
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Invariant subspaces and intertwiners for the spinor and half-spin actions

The Fock model makes the exterior algebra `S = ⋀·W` of the isotropic summand of a polarization a
module over `CliffordAlgebra Q` (`TauCeti.spinAction`), and that action is onto the full
endomorphism algebra as soon as `W` is finite free (`TauCeti.spinAction_surjective`). A module on
which every endomorphism is realized has no proper nonzero submodule at all, so **the spinor module
is simple**, in every dimension and without any nondegeneracy hypothesis: this is
`TauCeti.exists_spinAction_eq`, that a nonzero spinor is carried to every other one, and
`TauCeti.eq_bot_or_eq_top_of_map_spinAction_le`, its lattice form.

That is not yet the irreducibility the spin representation is named for, because in even dimension
`S` visibly splits, into the two half-spin summands `S⁺` and `S⁻` of `TauCeti.spinPlus` and
`TauCeti.spinMinus`. The splitting is invariant not under the whole Clifford algebra but under its
even subalgebra, and the theorem the splitting deserves is that the even subalgebra sees exactly
those two pieces and nothing finer:

`TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd :`
`  even Q ≃ₐ[K] Module.End K S⁺ × Module.End K S⁻`.

The proof of that structure theorem does not count dimensions a second time. Surjectivity onto the
*product* comes from the full structure theorem `TauCeti.spinAction_bijective` together with the
parity bookkeeping of `TauCeti/RepresentationTheory/Spin/HalfSpin.lean`. This file records its
representation-theoretic consequences: each half-spin summand has no proper nonzero invariant
subspace because its factor is a full endomorphism algebra, and the two even-Clifford actions are
**inequivalent**
(`TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`) because the
element of `even Q` acting as the identity on `S⁺` and as zero on `S⁻` kills any map that
intertwines them.

The invariant-subspace conclusions are stated in lattice form, as "an invariant subspace is `⊥`
or everything", rather than as `IsSimpleModule`: `S⁺` and `S⁻` carry no `Module (even Q)` instance,
and manufacturing one would mean a type synonym for a statement that reads no better through it.

The actions themselves — `TauCeti.spinPlusAction`, `TauCeti.spinMinusAction` and their pair
`TauCeti.evenSpinActionProd` — are defined in
`TauCeti/RepresentationTheory/Spin/HalfSpin.lean`, beside the bundling of the same two summands as
subrepresentations of `spinRep` that the same invariance gives; this file only proves theorems
about them.

The hypothesis `P.line = ⊥` is the even-dimensional case, and it is exactly what makes the parity
splitting a splitting of modules at all;
`TauCeti.SpinPolarizationData.even_finrank_of_line_eq_bot` turns it into the evenness the structure
theorem is stated with, so no separate parity hypothesis is carried. The lattice dichotomy for
`S⁻` needs no further hypothesis, since it also holds vacuously when `S⁻ = 0`. To conclude that
`S⁻` is simple, combine it with `TauCeti.nontrivial_spinMinus`, whose hypothesis `W ≠ ⊥` rules out
only the zero-dimensional quadratic space: there `S = K` is entirely even and `S⁻` is zero. `S⁺`
always contains the scalars, so it needs no such hypothesis, and neither does the inequivalence.

What is *not* proved here is irreducibility of the group representation `TauCeti.spinRep`, which
asks more: that the `K`-span of `spinGroup Q` inside `even Q` is all of it. Nor is the
odd-dimensional splitting of `CliffordAlgebra Q` into its two central summands, for which the
results here are the even-dimensional half.

## Main results

* `TauCeti.exists_spinAction_eq` and `TauCeti.eq_bot_or_eq_top_of_map_spinAction_le`: **the spinor
  module is a simple Clifford module.**
* `TauCeti.mem_even_of_map_spinPlus_le_of_map_spinMinus_le`: a Clifford element whose action
  preserves both half-spin summands is even.
* `TauCeti.eq_bot_or_eq_top_of_map_spinPlusAction_le` and
  `TauCeti.eq_bot_or_eq_top_of_map_spinMinusAction_le`: the two half-spin summands have no proper
  nonzero invariant subspace. Together with `TauCeti.nontrivial_spinPlus` and
  `TauCeti.nontrivial_spinMinus`, respectively, these say that the summands are simple.
* `TauCeti.eq_zero_of_intertwines_spinPlusAction_spinMinusAction` and
  `TauCeti.eq_zero_of_intertwines_spinMinusAction_spinPlusAction`: there is no nonzero map either
  way intertwining the two actions, and hence
  `TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`: **the half-spin summands
  are inequivalent.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9 and
  Proposition 20.15: the Clifford algebra of an even-dimensional space is the endomorphism algebra
  of `⋀·W`, its even subalgebra is the product of the endomorphism algebras of the two halves, and
  the two half-spin modules are irreducible and inequivalent.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The even-dimensional case".
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

private theorem eq_bot_or_eq_top_of_surjective_action {K : Type u} [Field K]
    {A M : Type*} [AddCommGroup M] [Module K M] (F : A → Module.End K M)
    (hF : Function.Surjective F) (N : Submodule K M)
    (hN : ∀ a : A, N.map (F a) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨s, hs, hs0⟩ := N.exists_mem_ne_zero_of_ne_bot hbot
  let _ : Nontrivial M := ⟨s, 0, hs0⟩
  obtain ⟨g, hg⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End K M) hs0 t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hg
  obtain ⟨a, rfl⟩ := hF g
  exact hg ▸ hN a ⟨s, hs, rfl⟩

/-! ### The spinor module is a simple Clifford module

Nothing here needs an even dimension, a nondegenerate form, or an invertible `2`: the Fock action
is onto `Module.End K S` for every polarization whose isotropic summand is finite-dimensional, and
a vector space is a simple module over its own endomorphism ring. -/

section Simple

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) [FiniteDimensional K P.W]

/-- **A nonzero spinor generates the spinor module**: some Clifford element carries it to any
prescribed spinor. The Fock action realizes every endomorphism of `S = ⋀·W`, and a vector space is
a simple module over its endomorphism ring. -/
theorem exists_spinAction_eq {s : ExteriorAlgebra K P.W} (hs : s ≠ 0)
    (t : ExteriorAlgebra K P.W) : ∃ x : CliffordAlgebra Q, spinAction Q P x s = t := by
  obtain ⟨f, hf⟩ := IsSimpleModule.toSpanSingleton_surjective
    (Module.End K (ExteriorAlgebra K P.W)) hs t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hf
  obtain ⟨x, rfl⟩ := spinAction_surjective P f
  exact ⟨x, hf⟩

/-- **The invariant-subspace dichotomy for the spinor module**: a submodule of `S = ⋀·W`
invariant under every Clifford element is `⊥` or the whole of `S`. The spinor module is nonzero,
so this is its simplicity statement for the Clifford action. -/
theorem eq_bot_or_eq_top_of_map_spinAction_le (N : Submodule K (ExteriorAlgebra K P.W))
    (hN : ∀ x : CliffordAlgebra Q, N.map (spinAction Q P x) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  exact eq_bot_or_eq_top_of_surjective_action (spinAction Q P) (spinAction_surjective P) N hN

end Simple

/-! ### Consequences of the even structure theorem -/

section Even

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]


/-! ### Invariant-subspace dichotomies and inequivalence of the two half-spin actions -/

/-- **The invariant-subspace dichotomy for the even half-spin summand**: every subspace of `S⁺`
invariant under the even Clifford subalgebra is `⊥` or all of `S⁺`. Combine this with
`TauCeti.nontrivial_spinPlus` to obtain simplicity. -/
theorem eq_bot_or_eq_top_of_map_spinPlusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinPlus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinPlusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  eq_bot_or_eq_top_of_surjective_action (spinPlusAction Q P hline)
    (spinPlusAction_surjective P hline) N hN

/-- **The invariant-subspace dichotomy for the odd half-spin summand**: every subspace of `S⁻`
invariant under the even Clifford subalgebra is `⊥` or all of `S⁻`. This remains true when `S⁻` is
zero; combine it with `TauCeti.nontrivial_spinMinus` to obtain simplicity when `P.W ≠ ⊥`. -/
theorem eq_bot_or_eq_top_of_map_spinMinusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinMinus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinMinusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  eq_bot_or_eq_top_of_surjective_action (spinMinusAction Q P hline)
    (spinMinusAction_surjective P hline) N hN

/-- **A map intertwining the two half-spin actions is zero.** The even subalgebra contains an
element acting as the identity on `S⁺` and as zero on `S⁻`, and an intertwiner turns the first
statement into the second. -/
theorem eq_zero_of_intertwines_spinPlusAction_spinMinusAction (hline : P.line = ⊥)
    (φ : spinPlus Q P →ₗ[K] spinMinus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
      φ (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (1, 0)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **A map intertwining the odd and even half-spin actions is zero.** -/
theorem eq_zero_of_intertwines_spinMinusAction_spinPlusAction (hline : P.line = ⊥)
    (φ : spinMinus Q P →ₗ[K] spinPlus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinMinus Q P),
      φ (spinMinusAction Q P hline x s) = spinPlusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (0, 1)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **The two half-spin summands are inequivalent.** There is no linear equivalence intertwining
the two actions of the even Clifford subalgebra. -/
theorem not_exists_equiv_intertwines_spinPlusAction_spinMinusAction (hline : P.line = ⊥) :
    ¬ ∃ e : spinPlus Q P ≃ₗ[K] spinMinus Q P,
      ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
        e (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (e s) := by
  rintro ⟨e, he⟩
  have hzero : (e : spinPlus Q P →ₗ[K] spinMinus Q P) = 0 :=
    eq_zero_of_intertwines_spinPlusAction_spinMinusAction P hline _ he
  have := nontrivial_spinPlus P
  obtain ⟨s, hs⟩ := exists_ne (0 : spinPlus Q P)
  have hes : e s = 0 := by simpa using LinearMap.congr_fun hzero s
  exact hs (e.injective (hes.trans (map_zero e).symm))

end Even

end TauCeti
