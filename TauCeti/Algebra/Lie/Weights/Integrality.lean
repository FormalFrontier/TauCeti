/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import TauCeti.Algebra.Lie.Sl2.Spectrum

public section

/-!
# Integrality of the weights of a module over a semisimple Lie algebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `M` be a finite-dimensional
`L`-module. This file defines when a linear form is an **integral weight** and proves that module
weights are integral: for every weight `χ` of `M` and every root `α`, the scalar `χ (α^∨)` is an
integer.

The proof here is the standard reduction to rank one that organises the whole highest-weight
theory. A nonzero root `α` carries an `sl₂` triple `⟨eₐ, hₐ, fₐ⟩` with `eₐ ∈ Lα`, `fₐ ∈ L₍₋α₎` and,
by Mathlib's `IsSl2Triple.h_eq_coroot`, `hₐ = α^∨`. Restricting `M` along that triple turns
`χ (α^∨)` into an eigenvalue of the Cartan element of an `sl₂` triple on a finite-dimensional
module, and those are integers by `TauCeti.exists_int_of_hasEigenvalue`.

Two hypotheses that might be expected are absent. The base field is **not** assumed algebraically
closed: only the existence of the root system and of the triple attached to `α` is needed, and both
are available as soon as `H` is splitting (`LieModule.IsTriangularizable K H L`). And the weight
spaces are Mathlib's **generalized** weight spaces, which is all that is available before the
diagonalizability theorem for the Cartan action; a weight `χ` enters the argument only through
`LieModule.Weight.hasEigenvalueAt`, which extracts an honest eigenvector of a single `x : H` from a
nonzero generalized weight space.

The refinements `TauCeti.exists_nat_of_lie_coroot_eq_smul_of_forall_rootSpace_lie_eq_zero` and
`TauCeti.exists_nat_neg_of_lie_coroot_eq_smul_of_forall_rootSpace_neg_lie_eq_zero` replace `ℤ` by
`ℕ` and by `-ℕ` for a vector on which `α^∨` acts by a scalar and which is killed by the root space
`Lα`, respectively by `L₍₋α₎`: that is, for a highest, respectively lowest, weight vector in the
`α` direction. The first is the form in which the classification of the finite-dimensional
irreducibles consumes integrality: restricting a highest weight vector to the `sl₂` of each simple
root is what forces its weight to be dominant integral.

## Main results

* `TauCeti.IsIntegralWeight`: a linear form takes integer values on every coroot. The integral
  weights contain `0` and are closed under addition, negation, subtraction and `ℤ`-scaling
  (`TauCeti.isIntegralWeight_zero`, `TauCeti.IsIntegralWeight.add`,
  `TauCeti.IsIntegralWeight.neg`, `TauCeti.IsIntegralWeight.sub`,
  `TauCeti.IsIntegralWeight.zsmul`).
* `TauCeti.exists_int_of_hasEigenvalue_coroot`: every eigenvalue of a coroot `α^∨` acting on a
  finite-dimensional module is an integer.
* `TauCeti.exists_int_apply_coroot`: **integrality of weights.** For a weight `χ` of a
  finite-dimensional module and a root `α`, the value `χ (α^∨)` is an integer.
* `TauCeti.isIntegralWeight_of_weight`: a weight of a finite-dimensional module is an integral
  weight.
* `TauCeti.exists_int_apply_of_mem_span_coroot`: a weight of a finite-dimensional module is
  `ℤ`-valued on the whole coroot lattice, the `ℤ`-span of the coroots.
* `TauCeti.exists_nat_of_lie_coroot_eq_smul_of_forall_rootSpace_lie_eq_zero` and
  `TauCeti.exists_nat_neg_of_lie_coroot_eq_smul_of_forall_rootSpace_neg_lie_eq_zero`: a nonzero
  vector on which `α^∨` acts by the scalar `μ` and which is killed by the root space `Lα`,
  respectively `L₍₋α₎`, forces `μ` to be a natural number, respectively minus a natural number.
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

/-- **The eigenvalues of a coroot are integers.** Every eigenvalue of the action of a coroot `α^∨`
on a finite-dimensional module is an integer.

The weight `α` is arbitrary: the roots carry the content, while the coroot of a zero weight is zero
and has only the eigenvalue `0`. -/
theorem exists_int_of_hasEigenvalue_coroot {α : Weight K H L} {μ : K}
    (hμ : (toEnd K H M (IsKilling.coroot α)).HasEigenvalue μ) :
    ∃ z : ℤ, μ = (z : K) := by
  by_cases hα : α.IsNonZero
  · obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
    refine exists_int_of_hasEigenvalue (M := M) ht ?_
    rw [ht.h_eq_coroot hα he hf]
    exact hμ
  · rw [IsKilling.coroot_eq_zero_iff.2 (not_not.1 hα)] at hμ
    obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
    have hsmul : μ • v = 0 := by simpa using (Module.End.mem_eigenspace_iff.1 hv).symm
    exact ⟨0, by simpa using (smul_eq_zero.1 hsmul).resolve_right hv0⟩

/-- **No generalized eigenvalues of a coroot off the integers.** The generalized eigenspace of the
coroot `α^∨` on a finite-dimensional module vanishes at every scalar that is not an integer.

This is deliberately not a `simp` lemma: the hypothesis `hμ` cannot be discharged by `simp` from the
left-hand side alone. -/
theorem genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast {α : Weight K H L}
    {μ : K} (hμ : ∀ z : ℤ, μ ≠ (z : K)) :
    genWeightSpaceOf M μ (IsKilling.coroot α) = ⊥ := by
  by_contra hbot
  obtain ⟨k : ℕ, hk : (toEnd K H M (IsKilling.coroot α)).genEigenspace μ k ≠ ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using hbot
  obtain ⟨z, hz⟩ :=
    exists_int_of_hasEigenvalue_coroot (Module.End.hasEigenvalue_of_hasGenEigenvalue hk)
  exact hμ z hz

/-! ### Integrality of weights -/

/-- A weight is **integral** when it takes integer values on every coroot. -/
def IsIntegralWeight (lam : Module.Dual K H) : Prop :=
  ∀ α : Weight K H L, ∃ n : ℤ, lam (IsKilling.coroot α) = (n : K)

omit [CharZero K] [IsTriangularizable K H L] in
/-- A linear form is integral if it takes an integer value on every coroot. -/
theorem isIntegralWeight_of_forall_exists_int_apply_coroot {lam : Module.Dual K H}
    (h : ∀ α : Weight K H L, ∃ n : ℤ, lam (IsKilling.coroot α) = (n : K)) :
    IsIntegralWeight lam :=
  h

omit [CharZero K] [IsTriangularizable K H L] in
/-- An integral weight takes an integer value on each coroot. -/
theorem IsIntegralWeight.exists_int_apply_coroot {lam : Module.Dual K H}
    (hlam : IsIntegralWeight lam) (α : Weight K H L) :
    ∃ n : ℤ, lam (IsKilling.coroot α) = (n : K) :=
  hlam α

omit [CharZero K] [IsTriangularizable K H L] in
/-- **The zero weight is integral.** -/
@[simp]
theorem isIntegralWeight_zero : IsIntegralWeight (0 : Module.Dual K H) :=
  isIntegralWeight_of_forall_exists_int_apply_coroot fun _ ↦ ⟨0, by simp⟩

omit [CharZero K] [IsTriangularizable K H L] in
/-- **A sum of integral weights is integral.** -/
theorem IsIntegralWeight.add {lam mu : Module.Dual K H} (hlam : IsIntegralWeight lam)
    (hmu : IsIntegralWeight mu) : IsIntegralWeight (lam + mu) :=
  isIntegralWeight_of_forall_exists_int_apply_coroot fun α ↦ by
    obtain ⟨m, hm⟩ := hlam.exists_int_apply_coroot α
    obtain ⟨n, hn⟩ := hmu.exists_int_apply_coroot α
    exact ⟨m + n, by rw [LinearMap.add_apply, hm, hn, Int.cast_add]⟩

omit [CharZero K] [IsTriangularizable K H L] in
/-- **The negative of an integral weight is integral.** -/
theorem IsIntegralWeight.neg {lam : Module.Dual K H} (hlam : IsIntegralWeight lam) :
    IsIntegralWeight (-lam) :=
  isIntegralWeight_of_forall_exists_int_apply_coroot fun α ↦ by
    obtain ⟨n, hn⟩ := hlam.exists_int_apply_coroot α
    exact ⟨-n, by rw [LinearMap.neg_apply, hn, Int.cast_neg]⟩

omit [CharZero K] [IsTriangularizable K H L] in
/-- **A difference of integral weights is integral.** -/
theorem IsIntegralWeight.sub {lam mu : Module.Dual K H} (hlam : IsIntegralWeight lam)
    (hmu : IsIntegralWeight mu) : IsIntegralWeight (lam - mu) := by
  rw [sub_eq_add_neg]
  exact hlam.add hmu.neg

omit [CharZero K] [IsTriangularizable K H L] in
/-- **An integer multiple of an integral weight is integral.** -/
theorem IsIntegralWeight.zsmul {lam : Module.Dual K H} (hlam : IsIntegralWeight lam) (z : ℤ) :
    IsIntegralWeight (z • lam) :=
  isIntegralWeight_of_forall_exists_int_apply_coroot fun α ↦ by
    obtain ⟨n, hn⟩ := hlam.exists_int_apply_coroot α
    exact ⟨z * n, by rw [LinearMap.smul_apply, hn, zsmul_eq_mul, Int.cast_mul]⟩

/-- **Integrality of the weights of a finite-dimensional module.** For every weight `χ` of a
finite-dimensional module `M` over a Killing-semisimple Lie algebra and every root `α`, the value
`χ (α^∨)` is an integer.

The nonzero weights `α` of `L` are the roots and carry the content; a zero weight has zero coroot,
and is allowed here only so that no side condition is carried around.

By `LieAlgebra.IsKilling.rootSystem_coroot_apply` the element `α^∨` is the coroot of the Mathlib
root system `LieAlgebra.IsKilling.rootSystem H`, so this is integrality in the sense that the
dominance conditions of the highest-weight classification use. -/
theorem exists_int_apply_coroot (χ : Weight K H M) (α : Weight K H L) :
    ∃ z : ℤ, χ (IsKilling.coroot α) = (z : K) :=
  exists_int_of_hasEigenvalue_coroot (χ.hasEigenvalueAt _)

/-- **The weights of a finite-dimensional module are integral.** -/
theorem isIntegralWeight_of_weight (χ : Weight K H M) :
    IsIntegralWeight (χ : Module.Dual K H) :=
  isIntegralWeight_of_forall_exists_int_apply_coroot fun α ↦ exists_int_apply_coroot χ α

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

/-- **A highest weight vector in the `α` direction has a natural coroot value.** If a nonzero `v` is
an eigenvector of the coroot `α^∨` of a nonzero root `α`, of eigenvalue `μ`, and is annihilated by
the root space `Lα`, then `μ` is a natural number.

This is the step that turns the highest weight of a finite-dimensional irreducible into a dominant
integral weight, applied to each simple root in turn. Only the action of `α^∨` on `v` is
constrained, and it is constrained by a genuine eigenvector equation, which is strictly stronger
than membership of a generalized weight space. -/
theorem exists_nat_of_lie_coroot_eq_smul_of_forall_rootSpace_lie_eq_zero {α : Weight K H L}
    (hα : α.IsNonZero) {μ : K} {v : M}
    (hv0 : v ≠ 0) (hv : ⁅((IsKilling.coroot α : H) : L), v⁆ = μ • v)
    (hve : ∀ e ∈ rootSpace H α, ⁅e, v⁆ = 0) :
    ∃ n : ℕ, μ = (n : K) := by
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have P : ht.HasPrimitiveVectorWith v μ :=
    { ne_zero := hv0
      lie_h := by rw [ht.h_eq_coroot hα he hf]; exact hv
      lie_e := hve e he }
  exact P.exists_nat

/-- **A lowest weight vector in the `α` direction has a non-positive coroot value.** If a nonzero
`v` is an eigenvector of the coroot `α^∨` of a nonzero root `α`, of eigenvalue `μ`, and is
annihilated by the root space `L₍₋α₎`, then `μ` is minus a natural number. -/
theorem exists_nat_neg_of_lie_coroot_eq_smul_of_forall_rootSpace_neg_lie_eq_zero
    {α : Weight K H L} (hα : α.IsNonZero) {μ : K} {v : M}
    (hv0 : v ≠ 0) (hv : ⁅((IsKilling.coroot α : H) : L), v⁆ = μ • v)
    (hvf : ∀ f ∈ rootSpace H (-α), ⁅f, v⁆ = 0) :
    ∃ n : ℕ, μ = -(n : K) := by
  have hv' : ⁅((IsKilling.coroot (-α) : H) : L), v⁆ = (-μ) • v := by
    rw [IsKilling.coroot_neg]
    simp [hv]
  obtain ⟨n, hn⟩ :=
    exists_nat_of_lie_coroot_eq_smul_of_forall_rootSpace_lie_eq_zero (M := M) hα.neg hv0 hv' hvf
  exact ⟨n, by rw [← hn, neg_neg]⟩

end TauCeti
