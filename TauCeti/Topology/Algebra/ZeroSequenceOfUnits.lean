/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Rings with a zero sequence of units

Henkel's open mapping theorem is stated for a topological ring carrying a *zero sequence of
units*: a sequence of units converging to zero. This file isolates that hypothesis and proves the
absorption property it exists for — every element is carried into every neighbourhood of zero by
some term of the sequence, so the dilates of a neighbourhood cover the space acted on.

The class carries no continuity, and this file assumes no continuity *instance* either, so each
result below takes an explicit `hc : ContinuousAt (fun a : A ↦ a • x) 0` — continuity of the
scalar action in the scalar alone, at zero, for the vector in question. Without it the statements
are false for a `MonoidWithZero` with an arbitrary topology. `ContinuousSMul A M` would do but is
joint continuity, strictly more than these proofs use.

Nothing here is Huber-specific, or even ring-specific. The hypothesis is about `A`, but the
absorption and covering results act on a space `M` carrying a zero and a zero-preserving
`A`-action — `[Zero M] [TopologicalSpace M] [MulActionWithZero A M]`, no additive structure on `M`
required, so `M` is *not* assumed to be a module. That is the form Henkel's theorem needs, since
his Baire argument covers the *domain* of the map rather than the base ring; taking `M = A`
recovers the ring statements. The bridge to Huber theory — that the powers of a pseudouniformiser
are such a sequence, so a Tate ring qualifies — is in
`TauCeti/RingTheory/Huber/ZeroSequenceOfUnits.lean`.

The covering is the point, and it must be **countable**. Henkel's proof applies a Baire argument
to the sets `uₙ⁻¹ • U` indexed by `n : ℕ`; a cover indexed by all of `Aˣ` would exhaust `M` just
as well but could not start that argument. Both results are therefore stated for an
arbitrary zero sequence, so that a caller holding a concrete one — the powers of a
pseudouniformiser, say — keeps it rather than trading it for an opaque choice.

## Main definitions

* `TauCeti.HasZeroSequenceOfUnits`: the ring admits a sequence of units tending to zero.

## Main results

All three carry the continuity hypothesis described above; the covering needs it at every vector,
the two pointwise results only at their own.

* `TauCeti.exists_smul_mem_of_tendsto_zero`: along any zero sequence of units, some term carries a
  given element of a space carrying a zero-preserving `A`-action into a given neighbourhood of
  zero.
* `TauCeti.iUnion_inv_smul_eq_univ_of_tendsto_zero`: its dilates `uₙ⁻¹ • U` cover `M`, indexed
  by `ℕ`.
* `TauCeti.HasZeroSequenceOfUnits.exists_unit_smul_mem`: the weaker unit-only form of absorption —
  it produces some `v : Aˣ`, with no sequence and no term index.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647). The hypothesis formalised here, the
  terminology, and the results below are its setup.
-/

public section

open Filter Topology Pointwise

namespace TauCeti

variable (A : Type*) [MonoidWithZero A] [TopologicalSpace A]

/-- Henkel's hypothesis on the base ring: there is a sequence of units converging to zero.

A discrete ring has none unless it is trivial, and that is the intended exclusion: the theorem
needs to shrink a neighbourhood by an invertible factor. -/
class HasZeroSequenceOfUnits : Prop where
  /-- Some sequence of units converges to zero. -/
  exists_tendsto : ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0)

/-- The class unfolds to the existential it wraps. This is its `@[simp]` normal form; a proof
already holding the instance normally reaches the sequence through the field directly, as
`‹HasZeroSequenceOfUnits A›.exists_tendsto`. -/
@[simp]
theorem hasZeroSequenceOfUnits_iff :
    HasZeroSequenceOfUnits A ↔ ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0) :=
  ⟨fun h ↦ h.exists_tendsto, fun h ↦ ⟨h⟩⟩

variable {A}

section Absorption

variable {M : Type*} [Zero M] [TopologicalSpace M] [MulActionWithZero A M]
  {u : ℕ → Aˣ} (hu : Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0))
include hu

/-- **Absorption.** Along a zero sequence of units in `A`, every element of a space `M` carrying a
zero-preserving `A`-action is carried into every neighbourhood of zero by some term of the
sequence.

Stated for an arbitrary such sequence rather than a chosen one, so a caller holding a concrete
sequence — the powers of a pseudouniformiser, say — gets the conclusion for *that* sequence.

The only topological input is `hc`, and it is needed only at the one `x` the conclusion is about
and only at `0 : A`: the proof is `uₙ • x → 0 • x = 0`. It is an unbundled hypothesis because
Mathlib has no class for "continuous in the scalar, vector fixed" — `ContinuousSMul A M` is joint
continuity, which is strictly more than this argument uses. At `M = A` it is discharged by
`(continuous_mul_const x).continuousAt` modulo `smul_eq_mul`. -/
theorem exists_smul_mem_of_tendsto_zero (x : M) (hc : ContinuousAt (fun a : A ↦ a • x) 0)
    {U : Set M} (hU : U ∈ 𝓝 (0 : M)) :
    ∃ n : ℕ, ((u n : A)) • x ∈ U := by
  have hsmul : Tendsto (fun n ↦ ((u n : A)) • x) atTop (𝓝 ((0 : A) • x)) :=
    Filter.Tendsto.comp hc hu
  rw [zero_smul] at hsmul
  exact (hsmul.eventually_mem hU).exists

/-- **The countable covering Henkel's Baire argument runs on**: the dilates `uₙ⁻¹ • U` of a
neighbourhood of zero exhaust `M`. The index is `ℕ`, which is what makes the cover usable in a
Baire argument — a cover by all of `Aˣ` would exhaust `M` too but could not start that argument.
Henkel needs this for the *domain* of the map, which is why `M` is not just the base ring. -/
theorem iUnion_inv_smul_eq_univ_of_tendsto_zero
    (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) {U : Set M} (hU : U ∈ 𝓝 (0 : M)) :
    ⋃ n : ℕ, ((u n)⁻¹ : Aˣ) • U = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
  obtain ⟨n, hn⟩ := exists_smul_mem_of_tendsto_zero hu x (hc x) hU
  exact ⟨n, Set.mem_inv_smul_set_iff.mpr (by rwa [Units.smul_def])⟩

end Absorption

namespace HasZeroSequenceOfUnits

variable {M : Type*} [Zero M] [TopologicalSpace M] [MulActionWithZero A M]
  [HasZeroSequenceOfUnits A]

/-- Some unit of `A` carries a given element of `M` into a given neighbourhood of zero.

Deliberately not phrased with a sequence: quantifying over an unconstrained `u : ℕ → Aˣ` would
say no more than this, since a constant sequence witnesses it. The sequence matters only for
`iUnion_inv_smul_eq_univ_of_tendsto_zero`, which is stated for a given sequence carrying its own
convergence hypothesis rather than restated at class level. -/
theorem exists_unit_smul_mem (x : M) (hc : ContinuousAt (fun a : A ↦ a • x) 0) {U : Set M}
    (hU : U ∈ 𝓝 (0 : M)) : ∃ v : Aˣ, (v : A) • x ∈ U := by
  obtain ⟨u, hu⟩ := ‹HasZeroSequenceOfUnits A›.exists_tendsto
  obtain ⟨n, hn⟩ := exists_smul_mem_of_tendsto_zero hu x hc hU
  exact ⟨u n, hn⟩

end HasZeroSequenceOfUnits

end TauCeti

end
