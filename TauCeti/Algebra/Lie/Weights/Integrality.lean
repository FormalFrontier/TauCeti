/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import TauCeti.Algebra.Lie.Sl2.Spectrum

public section

/-!
# Integrality of the weights of a module over a semisimple Lie algebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `M` be a finite-dimensional
`L`-module. This file proves that the weights of `M` are **integral**: for every weight `χ` of `M`
and every root `α`, the scalar `χ (α^∨)` is an integer.

The proof is the reduction to rank one that organises the whole highest-weight theory. A nonzero
root `α` carries an `sl₂` triple `⟨eₐ, hₐ, fₐ⟩` with `eₐ ∈ Lα`, `fₐ ∈ L₍₋α₎` and, by Mathlib's
`IsSl2Triple.h_eq_coroot`, `hₐ = α^∨`. Restricting `M` along that triple turns `χ (α^∨)` into an
eigenvalue of the Cartan element of an `sl₂` triple on a finite-dimensional module, and those are
integers by `TauCeti.exists_int_of_hasEigenvalue`. There is no route to integrality that avoids the
rank-one subalgebra, which is why the `sl₂` engine is built first.

Two hypotheses that might be expected are absent. The base field is **not** assumed algebraically
closed: only the existence of the root system and of the triple attached to `α` is needed, and both
are available as soon as `H` is splitting (`LieModule.IsTriangularizable K H L`). And the weight
spaces are Mathlib's **generalized** weight spaces, which is all that is available before the
diagonalizability theorem for the Cartan action; a weight `χ` enters the argument only through
`LieModule.Weight.hasEigenvalueAt`, which extracts an honest eigenvector of a single `x : H` from a
nonzero generalized weight space.

The refinements `TauCeti.exists_nat_apply_coroot` and `TauCeti.exists_nat_neg_apply_coroot` replace
`ℤ` by `ℕ` and by `-ℕ` for a vector that is a genuine `H`-eigenvector killed by the root space `Lα`,
respectively by `L₍₋α₎`: that is, for a highest, respectively lowest, weight vector in the `α`
direction. The first is the form in which the classification of the finite-dimensional irreducibles
consumes integrality: restricting a highest weight vector to the `sl₂` of each simple root is what
forces its weight to be dominant integral.

## Main results

* `TauCeti.exists_int_of_hasEigenvalue_coroot`: every eigenvalue of a coroot `α^∨` acting on a
  finite-dimensional module is an integer.
* `TauCeti.exists_int_apply_coroot`: **integrality of weights.** For a weight `χ` of a
  finite-dimensional module and a root `α`, the value `χ (α^∨)` is an integer.
* `TauCeti.exists_int_apply_of_mem_span_coroot`: a weight of a finite-dimensional module is
  `ℤ`-valued on the whole coroot lattice, the `ℤ`-span of the coroots.
* `TauCeti.exists_nat_apply_coroot` and `TauCeti.exists_nat_neg_apply_coroot`: a vector that is an
  `H`-eigenvector of weight `χ` and is killed by the root space `Lα`, respectively `L₍₋α₎`, has
  `χ (α^∨)` a natural number, respectively minus a natural number.
* `TauCeti.genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast`: the generalized eigenspace of a
  coroot at a non-integer scalar vanishes.

## References

This is the "integrality of weights (the `sl₂` reduction)" item of Layer 2 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose target signature
`weight_apply_coroot_isInt` is `TauCeti.exists_int_apply_coroot`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Chapter VI, §20.

`TauCeti.genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast` extracts an honest eigenvector from a
nonzero generalized weight space by the argument of Mathlib's `LieModule.Weight.hasEigenvalueAt`.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-! ### The spectrum of a coroot -/

/-- **The eigenvalues of a coroot are integers.** A nonzero root `α` carries an `sl₂` triple whose
Cartan element is the coroot `α^∨` (`IsSl2Triple.h_eq_coroot`), and the Cartan element of an `sl₂`
triple acts on a finite-dimensional module with integer eigenvalues
(`TauCeti.exists_int_of_hasEigenvalue`). -/
theorem exists_int_of_hasEigenvalue_coroot {α : Weight K H L} (hα : α.IsNonZero) {μ : K}
    (hμ : (toEnd K H M (IsKilling.coroot α)).HasEigenvalue μ) :
    ∃ z : ℤ, μ = (z : K) := by
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  refine exists_int_of_hasEigenvalue (M := M) ht ?_
  rw [ht.h_eq_coroot hα he hf]
  exact hμ

/-- **No generalized eigenvalues of a coroot off the integers.** The generalized eigenspace of the
coroot `α^∨` on a finite-dimensional module vanishes at every scalar that is not an integer.

This is deliberately not a `simp` lemma: the hypothesis `hμ` cannot be discharged by `simp` from the
left-hand side alone. -/
theorem genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast {α : Weight K H L} (hα : α.IsNonZero)
    {μ : K} (hμ : ∀ z : ℤ, μ ≠ (z : K)) :
    genWeightSpaceOf M μ (IsKilling.coroot α) = ⊥ := by
  by_contra hbot
  obtain ⟨k : ℕ, hk : (toEnd K H M (IsKilling.coroot α)).genEigenspace μ k ≠ ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using hbot
  obtain ⟨z, hz⟩ :=
    exists_int_of_hasEigenvalue_coroot hα (Module.End.hasEigenvalue_of_hasGenEigenvalue hk)
  exact hμ z hz

/-! ### Integrality of weights -/

/-- **Integrality of the weights of a finite-dimensional module.** For every weight `χ` of a
finite-dimensional module `M` over a Killing-semisimple Lie algebra and every root `α`, the value
`χ (α^∨)` is an integer.

This is the load-bearing use of the `sl₂` engine: a weight of `M` is in particular an eigenvalue of
the coroot `α^∨` (`LieModule.Weight.hasEigenvalueAt`), and `α^∨` is the Cartan element of the `sl₂`
triple attached to `α`. The nonzero weights `α` of `L` are the roots and carry the content; a zero
weight has zero coroot, and is allowed here only so that no side condition is carried around.

By `LieAlgebra.IsKilling.rootSystem_coroot_apply` the element `α^∨` is the coroot of the Mathlib
root system `LieAlgebra.IsKilling.rootSystem H`, so this is integrality in the sense that the
dominance conditions of the highest-weight classification use. -/
theorem exists_int_apply_coroot (χ : Weight K H M) (α : Weight K H L) :
    ∃ z : ℤ, χ (IsKilling.coroot α) = (z : K) := by
  by_cases hα : α.IsNonZero
  · exact exists_int_of_hasEigenvalue_coroot hα (χ.hasEigenvalueAt _)
  · rw [IsKilling.coroot_eq_zero_iff.2 (not_not.1 hα), ← Weight.toLinear_apply, map_zero]
    exact ⟨0, by simp⟩

/-- **A weight is `ℤ`-valued on the coroot lattice.** The coroots of a Killing-semisimple Lie
algebra span a `ℤ`-lattice in the Cartan subalgebra, and every weight of a finite-dimensional
module takes integer values on it.

The span is over all weights of `L` rather than over the roots alone; the two agree, the coroot of
the zero weight being zero. -/
theorem exists_int_apply_of_mem_span_coroot (χ : Weight K H M) {x : H}
    (hx : x ∈ Submodule.span ℤ (Set.range (IsKilling.coroot (K := K) (L := L) (H := H)))) :
    ∃ z : ℤ, χ x = (z : K) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    exact exists_int_apply_coroot χ α
  | zero => exact ⟨0, by rw [← Weight.toLinear_apply, map_zero]; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    refine ⟨z + w, ?_⟩
    rw [← Weight.toLinear_apply, map_add, Weight.toLinear_apply, Weight.toLinear_apply, hz, hw]
    push_cast
    ring
  | smul n x _ hx =>
    obtain ⟨z, hz⟩ := hx
    refine ⟨n * z, ?_⟩
    rw [← Weight.toLinear_apply, map_zsmul, Weight.toLinear_apply, hz]
    push_cast
    simp

/-! ### Dominance along a root -/

/-- **A highest weight vector in the `α` direction has a natural coroot value.** If a nonzero `v`
is an `H`-eigenvector of weight `χ` and is annihilated by the root space `Lα` of a nonzero root
`α`, then `χ (α^∨)` is a natural number.

Such a `v` is a primitive vector for the `sl₂` triple attached to `α`, and the weight of a
primitive vector is a natural number
(`IsSl2Triple.HasPrimitiveVectorWith.exists_nat`). This is the step that turns the highest weight of
a finite-dimensional irreducible into a dominant integral weight, applied to each simple root in
turn. Note that `χ` is an arbitrary function `H → K`: the hypothesis `hv` is genuine
eigenvector-hood, which is strictly stronger than membership of a generalized weight space. -/
theorem exists_nat_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) {χ : H → K} {v : M}
    (hv0 : v ≠ 0) (hv : ∀ x : H, ⁅(x : L), v⁆ = χ x • v)
    (hve : ∀ e ∈ rootSpace H α, ⁅e, v⁆ = 0) :
    ∃ n : ℕ, χ (IsKilling.coroot α) = (n : K) := by
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hh : h = ((IsKilling.coroot α : H) : L) := ht.h_eq_coroot hα he hf
  have P : ht.HasPrimitiveVectorWith v (χ (IsKilling.coroot α)) :=
    { ne_zero := hv0
      lie_h := by rw [hh]; exact hv _
      lie_e := hve e he }
  exact P.exists_nat

/-- **A lowest weight vector in the `α` direction has a non-positive coroot value.** If a nonzero
`v` is an `H`-eigenvector of weight `χ` and is annihilated by the root space `L₍₋α₎` of a nonzero
root `α`, then `χ (α^∨)` is minus a natural number.

This is `TauCeti.exists_nat_apply_coroot` for the opposite triple `IsSl2Triple.symm`, which swaps
the raising and lowering operators and negates the Cartan element. -/
theorem exists_nat_neg_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) {χ : H → K} {v : M}
    (hv0 : v ≠ 0) (hv : ∀ x : H, ⁅(x : L), v⁆ = χ x • v)
    (hvf : ∀ f ∈ rootSpace H (-α), ⁅f, v⁆ = 0) :
    ∃ n : ℕ, χ (IsKilling.coroot α) = -(n : K) := by
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hh : h = ((IsKilling.coroot α : H) : L) := ht.h_eq_coroot hα he hf
  have P : ht.symm.HasPrimitiveVectorWith v (-χ (IsKilling.coroot α)) :=
    { ne_zero := hv0
      lie_h := by rw [neg_lie, hh, hv, neg_smul]
      lie_e := hvf f hf }
  obtain ⟨n, hn⟩ := P.exists_nat
  exact ⟨n, by rw [← hn, neg_neg]⟩

end TauCeti
