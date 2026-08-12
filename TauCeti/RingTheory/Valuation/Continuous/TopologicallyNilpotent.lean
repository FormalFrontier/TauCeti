/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import TauCeti.RingTheory.Valuation.CharacteristicGroup
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# A continuous valuation at a topologically nilpotent element

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.10 and Remark 7.11(1), in the
directions that need no Huber-ring hypothesis.**

Continuity says every `{x ; v x < v b}` is open, and topological nilpotence says the powers of
`a` eventually enter every neighbourhood of `0`. Putting the two together bounds `v a`, and this
file records the two bounds Theorem 7.10 asks for — which are *not* the same statement and do not
need the same hypotheses.

* `v a < 1`, at `b = 1`. The threshold `1 = v 1` is a value `v` attains, so the ball is open by
  the definition of continuity alone: no compatibility between the topology and the ring
  operations is used, and the codomain need only be a `LinearOrderedCommMonoidWithZero`.
* `v a` is **cofinal** in the value group `Γ_v`: for every `γ ∈ Γ_v` some power `v a ^ n` falls
  below `γ`. This is strictly stronger and costs strictly more, for the reason below.

## The value group, not the codomain

Cofinality quantifies over `Γ_v`, the subgroup of the codomain *generated* by the attained
values, so a general `γ` is a **ratio** `v r / v t`, which need not be attained. That is what
`Valuation.IsContinuous.isOpen_lt_div` supplies, and it is why this proof reaches for the ratio
form of continuity rather than the attained-value one: `{x ; v x < γ}` has to be open for the
ratios too before topological nilpotence can be applied to it. Mathlib's
`Valuation.exists_div_eq_of_unit` is what puts a general element of `Γ_v` in
that form.

## Why `lt_one` is not just the case `γ = 1`

Cofinality does imply `v a < 1`, through `cofinalValueFor_top_iff` and `CofinalValueFor.lt_one`.
But that route pays for the general `γ`: a group codomain, and continuity of right multiplication
for the ratios. Since `Spv (A, I·A)` membership is a condition on all of `Γ_v` while the second
conjunct of Theorem 7.10 is a condition on `1` alone, the two really are separate obligations,
and the second is recorded at its own — much weaker — hypotheses rather than as a corollary of
the first.

## Main results

* `TauCeti.Valuation.exists_pow_lt_of_isTopologicallyNilpotent`
* `TauCeti.Valuation.IsContinuous.lt_one_of_isTopologicallyNilpotent`
* `TauCeti.Valuation.IsContinuous.cofinalValue_of_isTopologicallyNilpotent`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 7.11 and Theorem 7.10.
* AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, `projects/AdicSpaces/Adic spaces/SpvAITopology.lean`,
  was consulted. Its `cont_to_ideal_le_supp_of_mem_defIdeal` proves the `v a < 1` case over a
  `ValuativeRel`-derived valuation, and its general-`γ` counterpart
  `cont_to_ideal_le_supp_microbial` is an explicit `sorry` gated on a microbiality hypothesis.
  Neither result here needs microbiality, and the hypotheses differ; nothing was copied.
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A]

section Monoid

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]

omit [Nontrivial Γ₀] in
/-- **The shared step.** If the ball of radius `γ` is open and `a` is topologically nilpotent,
some power of `v a` falls below `γ`.

Both bounds in this file are this lemma at a different threshold, so it is stated once, at the
monoid level, with the openness supplied rather than derived: nothing here needs a group codomain
or any compatibility between the topology and the ring operations. -/
theorem exists_pow_lt_of_isTopologicallyNilpotent {v : Valuation A Γ₀} {γ : Γ₀}
    (hγ : γ ≠ 0)
    (hopen : IsOpen {x : A | v x < γ}) {a : A} (ha : IsTopologicallyNilpotent a) :
    ∃ n : ℕ, v a ^ n < γ := by
  obtain ⟨n, hn⟩ :=
    ha.exists_pow_mem_of_mem_nhds (hopen.mem_nhds (by simpa using zero_lt_iff.mpr hγ))
  exact ⟨n, by rwa [Set.mem_ofPred_eq, map_pow] at hn⟩

/-- **The second conjunct of Wedhorn Theorem 7.10.** A continuous valuation is `< 1` at every
topologically nilpotent element.

The threshold `1` is the attained value `v 1`, so the ball `{x ; v x < 1}` is open straight from
the definition of continuity: nothing relates the topology to the ring operations, and the
codomain is only a monoid.

`Nontrivial Γ₀` is not decoration. If `0 = 1` in `Γ₀` then `Γ₀` is trivial, every `{x ; v x < v b}`
is empty and so open, and the conclusion `v a < 1` reads `0 < 0`; a group codomain rules this out
by fiat, a monoid one does not. -/
theorem IsContinuous.lt_one_of_isTopologicallyNilpotent {v : Valuation A Γ₀}
    (hv : v.IsContinuous) {a : A} (ha : IsTopologicallyNilpotent a) : v a < 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent (v := v) (γ := 1) one_ne_zero
    (by simpa using isContinuous_def.mp hv 1) ha
  exact not_le.mp fun h ↦ absurd hn (not_lt.mpr (one_le_pow₀ h))

end Monoid

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Remark 7.11(1), the direction that holds for any topological ring.** A continuous
valuation has cofinal values at every topologically nilpotent element: the powers of `a` are
eventually inside each ball `{x ; v x < γ}`, and continuity is what makes that ball open.

A general `γ ∈ Γ_v` is a ratio `v r / v t` of attained values, which need not be attained, so
the ball is opened by `IsContinuous.isOpen_lt_div` — whence `[ContinuousConstSMul Aᵐᵒᵖ A]`,
which is continuity of right multiplication by a constant and nothing more. -/
theorem IsContinuous.cofinalValue_of_isTopologicallyNilpotent [ContinuousConstSMul Aᵐᵒᵖ A]
    {v : Valuation A Γ₀} (hv : v.IsContinuous) {a : A} (ha : IsTopologicallyNilpotent a) :
    CofinalValue v a := by
  rw [cofinalValue_iff]
  intro γ hγ
  -- a positive element of `Γ_v` is a ratio of attained values (`Valuation.exists_div_eq_of_unit`)
  obtain ⟨r, t, hr, ht, hrt⟩ := v.exists_div_eq_of_unit (Units.mk0 γ hγ.ne')
  simp only [Units.val_mk0] at hrt
  have hemb : ValueGroup₀.embedding γ = v r / v t := by
    rw [← hrt, map_div₀, Valuation.embedding_restrict, Valuation.embedding_restrict]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent (v := v) (div_ne_zero hr.ne' ht.ne')
    (hv.isOpen_lt_div r ht.ne') ha
  exact ⟨n, by rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, hemb, map_pow]; exact hn⟩

end TauCeti.Valuation
