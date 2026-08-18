/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# Continuous valuations

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.7 and Remarks 7.8, 7.9.**

`IsContinuous v` here says every `{a | v a < v b}` is open, the quantifier running over the
values `v` **attains**. Wedhorn's Definition 7.7 instead runs it over the whole value group
`Γ_v`, whose general element is a ratio `v b / v c`. The two say the same thing as soon as
right multiplication is continuous — `isOpen_lt_div` is precisely that step, and carries
`[ContinuousConstSMul Aᵐᵒᵖ A]` for it — but the definition itself asks for no such hypothesis, so
`IsContinuous` is the attained-value predicate and not literally Wedhorn's.

Wedhorn works over a topological ring throughout, but the compatibility is only needed where it
is used, so it is asked for per result rather than up front: the definition itself needs no more
than a topology on `A`, the ratio results need only continuity of right multiplication
(`[ContinuousConstSMul Aᵐᵒᵖ A]`; `isOpen_le_div` also wants the additive side), the translation
results need `[SeparatelyContinuousAdd A]` — only translation by a *fixed* element is ever
used, on either side — and `isContinuous_iff_continuous` needs both. Commutativity is
never used, so `A` is a `Ring`.

The codomain is treated the same way. Mathlib's `Valuation` is valued in a
`LinearOrderedCommMonoidWithZero`, and so is most of this file. A `LinearOrderedCommGroupWithZero`
is needed for two reasons — writing down a ratio `v b / v c`, and `WithZeroTopology`, whose
instance is stated on the group — so the five results that need either are gathered in a section
asking for it.

## The quantifier ranges over the value group, not over the codomain

Wedhorn quantifies `γ` over `Γ_v`, and that is load-bearing rather than incidental. Asking
instead for `{a | v a < γ}` to be open for every `γ` in the ambient codomain `Γ₀` **can be
strictly stronger** once `Γ₀` is larger than `Γ_v ∪ {0}` — not always, since on a discrete `A`
both conditions hold outright — and where it is stronger it is **not an invariant of the
equivalence class** of `v`, so it cannot cut out a subset of `Spv A`.

A witness: take `A = ℤ_p`, and let `w : A → (ℝ_{>0} ×ₗ p^ℤ) ∪ {0}` send `a ≠ 0` to `(1, |a|_p)`,
the order being lexicographic with the first coordinate dominant. Then `w` is equivalent to the
`p`-adic valuation, but for `γ = (1/2, 1)` — nonzero, yet below every value `w` attains — the set
`{a | w a < γ}` is `{0}`, which is not open. The `p`-adic valuation into its own value group has
no such `γ` available.

So `IsContinuous` is stated by quantifying over the **values** `v b`. Nothing of Wedhorn's
condition is lost: every element of `Γ_v` is a ratio `v b / v c`, and `IsContinuous.isOpen_lt_div`
recovers those — though only once right multiplication is continuous, which is why that lemma,
and not the definition, carries `[ContinuousConstSMul Aᵐᵒᵖ A]`. Phrased this way the defining
sets are *literally equal* for equivalent valuations, which is
`Valuation.IsEquiv.isContinuous_iff`.

## Main definitions

* `Valuation.IsContinuous` : continuity of a valuation, in attained-value form. It
  recovers **Definition 7.7** under `[ContinuousConstSMul Aᵐᵒᵖ A]`, via `isOpen_lt_div`.

## Main results

* `Valuation.IsEquiv.isContinuous_iff` : continuity depends only on the equivalence class, so it
  descends to the valuation spectrum.
* `Valuation.IsContinuous.isOpen_lt_div` and
  `Valuation.isContinuous_iff_forall_isOpen_lt_div` : the defining sets for an arbitrary
  element `v b / v c` of the value group — Wedhorn's quantifier in full, as an elimination rule
  and as an equivalence.
* `Valuation.isContinuous_of_continuous` : the easy half of Remark 7.8(1), needing no
  hypothesis on `A` beyond its topology.
* `Valuation.isContinuous_iff_continuous` : **Remark 7.8(1)**, that once the attained
  ratios are coinitial in `Γ₀` — in particular on a codomain no larger than `Γ_v ∪ {0}` —
  continuity is ordinary continuity into `WithZeroTopology`.
* `Valuation.IsContinuous.isOpen_le_div` : **Remark 7.8(3)**, the non-strict sets are
  open too, again over the whole value group; `IsContinuous.isOpen_le` is its attained-value
  case.
* `Valuation.isContinuous_of_discreteTopology` : **Remark 7.8(2)**, every valuation on
  a discrete ring is continuous.
* `Valuation.IsContinuous.comap` : **Remark 7.9**, continuity is inherited along a
  continuous ring homomorphism.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7 and Remarks 7.8, 7.9.

## Provenance

The corresponding development in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch
`dev/adic-spaces` at commit `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, project
`projects/AdicSpaces/`, file `Adic spaces/ContinuousValuations.lean`, was consulted rather than
copied, and the definition here deliberately differs from it.

AINTLIB defines `Valuation.IsContinuous v` as `∀ (γ : Γ₀), IsOpen {a | v a < γ}` — the
ambient-codomain form. By the witness above that is strictly stronger than Definition 7.7 and is
not preserved by `Valuation.IsEquiv`, so it cannot descend to `Spv A`; AINTLIB's own transfer
lemma `isContinuous_ofValuation_of` is correspondingly one-directional. Quantifying over the
attained values instead makes `Valuation.IsEquiv.isContinuous_iff` immediate.
-/

public section

namespace Valuation

open Set Topology

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommMonoidWithZero Γ₀']

/-- **Continuity of a valuation, in attained-value form.** Every set `{a | v a < v b}` is open.

This is *not* literally Wedhorn's Definition 7.7, which quantifies over the whole value group
`Γ_v`: reaching a general element of `Γ_v`, being a ratio `v b / v c`, needs right multiplication
to be continuous, and this definition asks for no compatibility beyond a topology on `A`. Under
`[ContinuousConstSMul Aᵐᵒᵖ A]` the two coincide, which is what `isOpen_lt_div` proves.

Quantifying over attained values rather than over the codomain `Γ₀` is deliberate — see the
module docstring for why the `Γ₀` form is a different, and equivalence-class-dependent,
condition. The `b` with `v b = 0` cost nothing, the set then being empty. -/
def IsContinuous (v : Valuation A Γ₀) : Prop :=
  ∀ b : A, IsOpen {a : A | v a < v b}

/-- Continuity, unfolded to the family of open sets defining it. -/
-- Not a wrapper: `IsContinuous` is not `@[expose]`, so a downstream module cannot unfold it and
-- `simp [IsContinuous]` fails there; rewriting through this lemma is the only route to the
-- quantifier from outside this file.
@[simp]
theorem isContinuous_def {v : Valuation A Γ₀} :
    v.IsContinuous ↔ ∀ b : A, IsOpen {a : A | v a < v b} := Iff.rfl

/-- The `b` in the support may be dropped from the quantifier, contributing as they do only the
empty set. -/
theorem isContinuous_iff_forall_ne_zero (v : Valuation A Γ₀) :
    v.IsContinuous ↔ ∀ b : A, v b ≠ 0 → IsOpen {a : A | v a < v b} :=
  ⟨fun h b _ ↦ h b, fun h b ↦ (eq_or_ne (v b) 0).elim (fun hb ↦ by simp [hb]) (h b)⟩

/-- Openness of `{a | v a < γ}` for every `γ` of the codomain is a sufficient — in general
strictly stronger — condition for continuity. -/
theorem isContinuous_of_forall_isOpen_lt {v : Valuation A Γ₀}
    (h : ∀ γ : Γ₀, IsOpen {a : A | v a < γ}) : v.IsContinuous := fun b ↦ h (v b)

/-- **Continuity is an invariant of the equivalence class.** Equivalent valuations compare the
same pairs of elements, so the sets `{a | v a < v b}` cutting out continuity are not merely
matched up but literally the same sets. This is what lets continuity be imposed on a point of
the valuation spectrum. -/
theorem IsEquiv.isContinuous_iff {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    (h : v.IsEquiv w) : v.IsContinuous ↔ w.IsContinuous :=
  forall_congr' fun _ ↦ iff_of_eq (congrArg IsOpen (Set.ext fun _ ↦ h.lt_iff_lt))

/-- **Wedhorn Remark 7.8(2).** Every valuation on a discrete topological ring is continuous. -/
theorem isContinuous_of_discreteTopology [DiscreteTopology A] (v : Valuation A Γ₀) :
    v.IsContinuous := fun _ ↦ isOpen_discrete _

/-- For a continuous valuation `v` on a ring with separately continuous addition, the valuation ball
`{y | v (y - a) < v b}` is a neighborhood of `a` whenever `v b ≠ 0`. -/
theorem IsContinuous.sub_lt_mem_nhds [SeparatelyContinuousAdd A] {v : Valuation A Γ₀}
    (hv : v.IsContinuous) (a : A) {b : A} (hb : v b ≠ 0) : {y : A | v (y - a) < v b} ∈ 𝓝 a := by
  have hcont : Continuous fun y : A ↦ y - a := by
    simpa only [sub_eq_add_neg] using continuous_add_const (-a)
  refine ((hv b).preimage hcont).mem_nhds ?_
  simpa using zero_lt_iff.mpr hb

/-- **Wedhorn Remark 7.8(3), at an attained value.** The non-strict set `{a | v a ≤ v b}` is
open: it is a union of translates of the open `{a | v a < v b}`, since adding an element of
value `< v b` to one of value `≤ v b` keeps the value `≤ v b`. For an arbitrary element of the
value group — which need not be attained — see `isOpen_le_div`. -/
theorem IsContinuous.isOpen_le [SeparatelyContinuousAdd A] {v : Valuation A Γ₀}
    (hv : v.IsContinuous) {b : A} (hb : v b ≠ 0) : IsOpen {a : A | v a ≤ v b} := by
  refine isOpen_iff_mem_nhds.mpr fun a ha ↦ ?_
  filter_upwards [hv.sub_lt_mem_nhds a hb] with y hy
  simpa using v.map_add_le hy.le ha

/-- **Wedhorn Remark 7.9.** Continuity is inherited along a continuous ring homomorphism. No
compatibility between the topology and the ring operations is needed on either side: because the
quantifier runs over attained values, and `v.comap φ` attains exactly the `v (φ b)`, the sets
cutting out continuity of `v.comap φ` are literally the `φ`-preimages of those cutting out
continuity of `v`. -/
theorem IsContinuous.comap {B : Type*} [Ring B] [TopologicalSpace B] {φ : B →+* A}
    (hφ : Continuous φ) {v : Valuation A Γ₀} (hv : v.IsContinuous) : (v.comap φ).IsContinuous :=
  fun b ↦ (hv (φ b)).preimage hφ

/-! ### Results needing a value **group**

Two things need inverses on the codomain: writing a ratio `v b / v c`, which is how Wedhorn's
quantifier over `Γ_v` is expressed, and Mathlib's `WithZeroTopology`, whose instance is stated on
a `LinearOrderedCommGroupWithZero`. The five results below need one or the other; everything
above works over the monoid.
-/

section ValueGroup

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn's quantifier in full.** Every element of the value group `Γ_v` is a ratio
`v b / v c` with `c` outside the support, and continuity makes `{a | v a < v b / v c}` open for
all of them. -/
theorem IsContinuous.isOpen_lt_div [ContinuousConstSMul Aᵐᵒᵖ A] {v : Valuation A Γ₀}
    (hv : v.IsContinuous)
    (b : A) {c : A} (hc : v c ≠ 0) : IsOpen {a : A | v a < v b / v c} := by
  -- the set is the preimage of `{x | v x < v b}` under multiplication by `c` on the right
  simpa [lt_div_iff₀ (zero_lt_iff.mpr hc)] using
    (hv b).preimage (continuous_const_smul (MulOpposite.op c))

/-- **Wedhorn's quantifier in full, as an equivalence.** Continuity is exactly openness of
`{a | v a < v b / v c}` for every ratio, i.e. for every element of the value group `Γ_v` — which
is Definition 7.7 verbatim. The reverse direction is the case `c = 1`, so this is the named
introduction rule for continuity that `isOpen_lt_div` alone does not provide. -/
theorem isContinuous_iff_forall_isOpen_lt_div [ContinuousConstSMul Aᵐᵒᵖ A]
    {v : Valuation A Γ₀} :
    v.IsContinuous ↔ ∀ b c : A, v c ≠ 0 → IsOpen {a : A | v a < v b / v c} := by
  refine ⟨fun hv b _ hc ↦ hv.isOpen_lt_div b hc, fun h b ↦ ?_⟩
  simpa only [map_one, div_one] using h b 1 (by simp)

/-- **Wedhorn Remark 7.8(3) in full.** Remark 7.8(3) quantifies over the whole value group, and
a general element of it is a ratio `v b / v c` rather than an attained value, so this rather than
`isOpen_le` is the statement Wedhorn makes. As in `isOpen_lt_div` the set is the preimage of the
attained-value one under multiplication by `c`. -/
theorem IsContinuous.isOpen_le_div [SeparatelyContinuousAdd A] [ContinuousConstSMul Aᵐᵒᵖ A]
    {v : Valuation A Γ₀} (hv : v.IsContinuous) {b c : A} (hb : v b ≠ 0) (hc : v c ≠ 0) :
    IsOpen {a : A | v a ≤ v b / v c} := by
  simpa [le_div_iff₀ (zero_lt_iff.mpr hc)] using
    (hv.isOpen_le hb).preimage (continuous_const_smul (MulOpposite.op c))

open scoped WithZeroTopology in
/-- Ordinary continuity into `WithZeroTopology` implies continuity in the sense of Definition
7.7: `Iio γ` is open, so each defining set is a preimage of an open set. This is the easy half of
`isContinuous_iff_continuous`, split off because that equivalence's separate-continuity and
coinitiality hypotheses are irrelevant to this direction — no compatibility with the ring
operations is needed at all. It sits in this section only because naming `WithZeroTopology`
requires the codomain to be a group. -/
theorem isContinuous_of_continuous {v : Valuation A Γ₀} (hv : Continuous v) : v.IsContinuous :=
  isContinuous_of_forall_isOpen_lt fun _ ↦ hv.isOpen_preimage _ WithZeroTopology.isOpen_Iio

open scoped WithZeroTopology in
/-- **Wedhorn Remark 7.8(1).** Continuity in the sense of Definition 7.7 is ordinary continuity
of `v : A → Γ₀` for the topology of Wedhorn's Remark 1.17 — Mathlib's `WithZeroTopology` — as
soon as the attained ratios `v b / v c` are **coinitial** in `Γ₀`, which is the hypothesis `hΓ`.

Coinitiality, not exact representation, is what the proof needs: below any `γ ≠ 0` it has to find
*some* basic ratio ball, not the ball of radius exactly `γ`. It holds in particular whenever the
codomain is no larger than `Γ_v ∪ {0}`, which is Wedhorn's setting.

`hΓ` is not decoration: without it only the reverse implication survives, and the module
docstring's `ℤ_p` valuation is a witness — its attained ratios all exceed `(1/2, 1)`. -/
theorem isContinuous_iff_continuous [SeparatelyContinuousAdd A] [ContinuousConstSMul Aᵐᵒᵖ A]
    {v : Valuation A Γ₀}
    (hΓ : ∀ γ : Γ₀, γ ≠ 0 → ∃ b c : A, v b ≠ 0 ∧ v c ≠ 0 ∧ v b / v c ≤ γ) :
    v.IsContinuous ↔ Continuous v := by
  refine ⟨fun hv ↦ continuous_iff_continuousAt.mpr fun a ↦ ?_, isContinuous_of_continuous⟩
  rcases eq_or_ne (v a) 0 with ha | ha
  · -- at a point of the support, a ratio ball sitting below `γ` is already a neighbourhood
    rw [ContinuousAt, ha, WithZeroTopology.tendsto_zero]
    intro γ hγ
    obtain ⟨b, c, hb, hc, hle⟩ := hΓ γ hγ
    have hpos : (0 : Γ₀) < v b / v c := zero_lt_iff.mpr (div_ne_zero hb hc)
    filter_upwards [(hv.isOpen_lt_div b hc).mem_nhds (by simpa [ha] using hpos)] with x hx
    exact hx.trans_le hle
  · -- off the support `v` is locally constant, by the strict triangle equality
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero ha]
    filter_upwards [hv.sub_lt_mem_nhds a ha] with y hy using v.map_eq_of_sub_lt hy

end ValueGroup

end Valuation
