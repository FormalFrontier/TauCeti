/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.RingTheory.Huber.Basic

/-!
# The `ϖⁿ • M₀` submodules basis, and the `A`-module topology it induces

Let `A` be a Tate ring, `A₀` a ring of definition, `ϖ ∈ A₀` a pseudouniformiser, and `M₀` an
`A₀`-submodule of an `A`-module `M` with `A · M₀ = M`. This file exhibits the family `ϖⁿ • M₀`
as a `SubmodulesBasis`, which is Mathlib's machinery for turning such a family into a topology;
`SubmodulesBasis.topology` and `.nonarchimedean` then apply.

**Two of Proposition 6.18(1)'s clauses are established for the induced topology** — that it is an
`A`-module topology (`powSmulModuleFilterBasis`, since `SubmodulesBasis.toModuleFilterBasis`
gives only an `A₀`-module one) and that it is first countable at `0`
(`isCountablyGenerated_nhds_zero`).

**Completeness and uniqueness are not.** 6.18(1) asserts the topology is the *unique* complete
first-countable `A`-module topology on a finitely generated module; neither half is proved below,
so this is a construction of that topology's neighbourhood basis together with two of its
properties, not an identification with the topology 6.18(1) characterises.

**The hypotheses are weaker than Wedhorn's, deliberately.** Remark 6.19 assumes `A` noetherian
and `M₀` finitely generated. The basis and topology declarations use neither — only `A · M₀ = M`,
and the comparison results below not even that. Finite generation enters only in
`exists_pow_smul_le` and `exists_pow_smul_le_pow_smul`, as a hypothesis on the submodule being
compared, where a single exponent has to serve a whole submodule at once. `A` noetherian is used
nowhere in this file.
Several declarations are weaker still, taking an arbitrary `S : Subring A` rather than a ring of
definition, so a caller holding `powerBoundedSubring A` can use them.

## Main results

* `TauCeti.Huber.PairOfDefinition.exists_pow_smul_mem`: a power of `ϖ` carries any element of
  the `A`-span of `M₀` into `M₀`.
* `TauCeti.Huber.PairOfDefinition.submodulesBasis_pow_smul`: the family is a `SubmodulesBasis`.
* `TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis`: the same family as a filter basis
  for scalars from `A`, not just from `A₀` — Proposition 6.18(1)'s `A`-module clause.
* `TauCeti.Huber.PairOfDefinition.exists_pow_smul_le` and
  `TauCeti.Huber.PairOfDefinition.exists_pow_smul_le_pow_smul`: the family built from a finitely
  generated lattice is cofinal in the one built from `M₀`. This is one direction of the comparison
  behind Remark 6.19's well-definedness; the reverse instance and the equality of topologies are
  not proved here.
* `TauCeti.Huber.PairOfDefinition.isCountablyGenerated_nhds_zero`: the induced topology has a
  countable fundamental system of neighbourhoods of `0` — 6.18(1)'s first-countability clause.

The elementary facts about `rⁿ • M₀` over an arbitrary subring — antitonicity, absorption of
further powers, and the ambient-scalar bridge — carry no Huber content and live in
`TauCeti.Algebra.Module.Submodule.Pointwise`.

## Implementation notes

The neighbourhoods are `A₀`-submodules, not `A`-submodules, so `SubmodulesBasis` is instantiated
at `R := P.ringOfDefinition`: `M` carries its `A₀`-module structure by restriction of scalars
along `A₀ → A`, which typeclass inference supplies unaided.

The family is written out as `ϖⁿ • M₀` rather than wrapped in a definition of its own: Mathlib's
pointwise action on submodules already *is* that operation, and
`TauCeti.Algebra.Module.Submodule.Pointwise` supplies the facts about it.

The family is `ϖⁿ • M₀` rather than `Iⁿ • M₀` for the ideal of definition `I`. That is Wedhorn's
own indexing, and it is what the proofs below run on: both `exists_pow_smul_mem` and
`eventually_smul_mem_pow_smul` consume the pseudouniformiser's own neighbourhood basis,
`TauCeti.Huber.IsPseudoUniformizer.hasBasis_nhds_zero`. This is a choice of presentation and not
a constraint — nothing here shows an `I`-indexed family would fail.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.18 and
  Remark 6.19.
-/

public section

open Filter
open scoped Topology Pointwise

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M]


/-- **A power of `s` carries any element of `M = A · M₀` into `M₀`.** This is where the
hypothesis `A · M₀ = M` is spent, and it is what makes the `smul` condition of
`SubmodulesBasis` an identity inside `A₀`. -/
theorem exists_pow_smul_mem (P : PairOfDefinition A) {s : A} (hs : IsTopologicallyNilpotent s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M) {m : M}
    (hm : m ∈ Submodule.span A (M₀ : Set M)) :
    ∃ k : ℕ, s ^ k • m ∈ M₀ := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨kx, hkx⟩ := ihx; obtain ⟨ky, hky⟩ := ihy
      refine ⟨max kx ky, ?_⟩
      have hx' : s ^ (max kx ky) • x ∈ M₀ := by
        have he : max kx ky = (max kx ky - kx) + kx := by omega
        rw [he]; exact M₀.pow_add_smul_mem hs0 _ _ _ hkx
      have hy' : s ^ (max kx ky) • y ∈ M₀ := by
        have he : max kx ky = (max kx ky - ky) + ky := by omega
        rw [he]; exact M₀.pow_add_smul_mem hs0 _ _ _ hky
      rw [smul_add]; exact M₀.add_mem hx' hy'
  | smul c x _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨i, hi⟩ := P.exists_pow_mul_mem hs c
      refine ⟨i + k, ?_⟩
      have he : s ^ (i + k) • (c • x) = (⟨s ^ i * c, hi⟩ : P.ringOfDefinition) • (s ^ k • x) := by
        rw [smul_smul, Subring.smul_def, ← smul_assoc, smul_eq_mul]
        congr 1
        push_cast
        rw [pow_add]; ring
      rw [he]; exact M₀.smul_mem _ hk

/-- **The `smul` half of `SubmodulesBasis`**: every scalar close enough to `0` in `A₀` carries a
given `m` into `ϖⁿ • M₀`.

`m` is carried into `M₀` by `ϖᵏ` for some `k` (`exists_pow_smul_mem`), and `ϖⁿ⁺ᵏ A₀` is a
neighbourhood of `0`; the two combine by arithmetic inside `A₀`. -/
theorem eventually_smul_mem_pow_smul (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M) {m : M}
    (hm : m ∈ Submodule.span A (M₀ : Set M)) (n : ℕ) :
    ∀ᶠ a in 𝓝 (0 : P.ringOfDefinition), a • m ∈ (⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ := by
  obtain ⟨k, hk⟩ := P.exists_pow_smul_mem hs.isTopologicallyNilpotent hs0 M₀ hm
  have hnhd : ∀ᶠ a : P.ringOfDefinition in 𝓝 0,
      (a : A) ∈ (s ^ (n + k)) • (P.ringOfDefinition : Set A) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (by simpa using (hs.hasBasis_nhds_zero P).mem_of_mem (i := n + k) trivial)
  filter_upwards [hnhd] with a ha
  obtain ⟨b, hb, hab⟩ := ha
  -- `a` is an `A₀`-scalar while the shared lemma speaks the ambient `A`; the two actions on `M`
  -- agree because the `A₀`-action is restriction of scalars along `A₀ → A`.
  rw [Subring.smul_def]
  exact M₀.smul_mem_pow_smul hs0 hb hab hk

/-- **The `ϖⁿ • M₀` family is a `SubmodulesBasis`**, for a pseudouniformiser `ϖ` in a ring of
definition `A₀` and an `A₀`-submodule `M₀` spanning `M` over `A`.

`SubmodulesBasis.topology` then makes `M` a topological `A₀`-module for which this family is a
neighbourhood basis of `0`, and `SubmodulesBasis.nonarchimedean` makes it a nonarchimedean
additive group.

This is the basis half of Wedhorn's Remark 6.19. He states it for `A` noetherian and `M₀`
finitely generated, and identifies the resulting topology with the one of his Proposition
6.18(1); neither hypothesis is used here, and no such identification is proved here. -/
theorem submodulesBasis_pow_smul (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    SubmodulesBasis ((⟨s, hs0⟩ : P.ringOfDefinition) ^ · • M₀) where
  inter i j :=
    ⟨max i j, le_inf (M₀.pow_smul_antitone (le_max_left i j))
      (M₀.pow_smul_antitone (le_max_right i j))⟩
  smul _ i := P.eventually_smul_mem_pow_smul hs hs0 M₀ (hspan ▸ Submodule.mem_top) i

/-- **The A-module filter basis.** `SubmodulesBasis.toModuleFilterBasis` only ever produces a
filter basis over `A₀`; Wedhorn's Proposition 6.18(1) is about an `A`-module topology, so the
three `ModuleFilterBasis` axioms are re-established with scalars from `A`.

Exposed because `TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis_topology` states an
equation between this basis's topology and the `SubmodulesBasis` one, which no proof can
establish without unfolding this body. -/
@[expose]
def powSmulModuleFilterBasis (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) : ModuleFilterBasis A M where
  __ := (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).toModuleFilterBasis.toAddGroupFilterBasis
  smul' := by
    -- `V = A₀` works because each `ϖⁿ • M₀` is an `A₀`-submodule; Mathlib's `A₀`-level
    -- construction can take `V = univ` for the same reason one level down.
    rintro _ ⟨n, rfl⟩
    refine ⟨(P.ringOfDefinition : Set A),
      P.isOpen_ringOfDefinition.mem_nhds P.ringOfDefinition.zero_mem, _, ⟨n, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, m, hm, rfl⟩
    exact ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀).smul_mem ⟨a, ha⟩ hm
  smul_left' := by
    rintro a _ ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := P.exists_pow_mul_mem hs.isTopologicallyNilpotent a
    refine ⟨_, ⟨n + k, rfl⟩, fun x hx ↦ ?_⟩
    simp only [SetLike.mem_coe, Set.mem_preimage, Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(⟨s ^ k * a, hk⟩ : P.ringOfDefinition) • y, M₀.smul_mem _ hy, ?_⟩
    -- Both sides scale `y`; `Subring.smul_def` puts the `A₀`-scalars into `A` so that the two
    -- can be compared there.
    simp only [Subring.smul_def]
    rw [smul_smul, smul_smul]
    congr 1
    push_cast
    rw [pow_add]; ring
  smul_right' := by
    rintro m _ ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := P.exists_pow_smul_mem hs.isTopologicallyNilpotent hs0 M₀
      (hspan ▸ Submodule.mem_top)
    filter_upwards [(hs.hasBasis_nhds_zero P).mem_of_mem (i := n + k) trivial] with c hc
    obtain ⟨b, hb, hcb⟩ := hc
    rw [SetLike.mem_coe]
    exact M₀.smul_mem_pow_smul hs0 hb hcb hk

/-- **Membership in the filter basis is the `ϖⁿ • M₀` family**, in normal form, so a consumer
never unfolds `TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis`. -/
@[simp]
theorem mem_powSmulModuleFilterBasis (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤)
    {U : Set M} :
    U ∈ (P.powSmulModuleFilterBasis hs hs0 M₀ hspan).toFilterBasis ↔
      ∃ n : ℕ, U = ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ : Submodule _ M) :=
  Iff.rfl

/-- **The `A`-module topology is the `A₀`-level one.** Widening the scalars from `A₀` to `A`
re-establishes the `ModuleFilterBasis` axioms but leaves the underlying `AddGroupFilterBasis`
untouched, hence the topology too. This is what lets a consumer transport
`SubmodulesBasis.nonarchimedean` and the rest of the `A₀`-level API across. -/
@[simp]
theorem powSmulModuleFilterBasis_topology (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (P.powSmulModuleFilterBasis hs hs0 M₀ hspan).topology
      = (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).topology :=
  rfl

/-- **The topology has a countable fundamental system of neighbourhoods of `0`.** The family is
indexed by `ℕ`, so this is `Filter.HasBasis.isCountablyGenerated` once the basis is transported
off `SubmodulesBasis`'s `Set`-indexed form. -/
theorem isCountablyGenerated_nhds_zero (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (@nhds M (P.powSmulModuleFilterBasis hs hs0 M₀ hspan).topology
      0).IsCountablyGenerated := by
  set B := P.powSmulModuleFilterBasis hs hs0 M₀ hspan with hB
  let _ := B.topology
  have hbasis : (𝓝 (0 : M)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ : Set M) := by
    refine B.toAddGroupFilterBasis.nhds_zero_hasBasis.to_hasBasis ?_ ?_
    · intro U hU
      obtain ⟨n, rfl⟩ := (P.mem_powSmulModuleFilterBasis hs hs0 M₀ hspan).mp hU
      exact ⟨n, trivial, subset_rfl⟩
    · rintro n -
      exact ⟨_, (P.mem_powSmulModuleFilterBasis hs hs0 M₀ hspan).mpr ⟨n, rfl⟩, subset_rfl⟩
  exact hbasis.isCountablyGenerated

/-- **A power of `ϖ` carries a finitely generated `A₀`-submodule into `M₀` wholesale.**

A *single* exponent serves all of `M₁` at once. That uniformity is exactly what finite generation
buys: without it `exists_pow_smul_mem` still gives an exponent for each element separately, but
those exponents need not be bounded, and no power of `ϖ` need carry the whole submodule.

`M₀` is not required to span `M`; only `M₁` need lie in its span. -/
theorem exists_pow_smul_le (P : PairOfDefinition A) {s : A} (hs : IsTopologicallyNilpotent s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ M₁ : Submodule P.ringOfDefinition M)
    (hspan : (M₁ : Set M) ⊆ Submodule.span A (M₀ : Set M)) (hfg : M₁.FG) :
    ∃ k : ℕ, (⟨s, hs0⟩ : P.ringOfDefinition) ^ k • M₁ ≤ M₀ := by
  obtain ⟨G, hG⟩ := hfg
  choose! f hf using fun (z : M) (hz : z ∈ Submodule.span A (M₀ : Set M)) ↦
    P.exists_pow_smul_mem hs hs0 M₀ hz
  have hGmem : ∀ g ∈ (G : Set M), g ∈ Submodule.span A (M₀ : Set M) := fun g hg ↦
    hspan (hG ▸ Submodule.subset_span hg)
  refine ⟨G.sup f, ?_⟩
  have key : ∀ x ∈ M₁, s ^ G.sup f • x ∈ M₀ := by
    intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := f) hg)
        rw [hd, Nat.add_comm]
        exact M₀.pow_add_smul_mem hs0 d (f g) g (hf g (hGmem g hg))
    | zero => simp
    | add x y _ _ ihx ihy => simpa [smul_add] using M₀.add_mem ihx ihy
    | smul a x _ ih =>
        rw [smul_comm]
        exact M₀.smul_mem _ ih
  rintro _ ⟨x, hx, rfl⟩
  simp only [DistribSMul.toLinearMap_apply]
  have hcast : (((⟨s, hs0⟩ : P.ringOfDefinition) ^ G.sup f : P.ringOfDefinition) : A) • x
      = s ^ G.sup f • x := by
    rw [SubmonoidClass.coe_pow]
  exact hcast ▸ key x hx

/-- **One-sided cofinality of the two `ϖ`-adic filtrations.** Every member of the family built
from `M₀` contains a member of the family built from a finitely generated `M₁`.

This is the comparison Remark 6.19's well-definedness rests on, in one direction only: it gives
the inclusion of the induced neighbourhood filters, not their equality. The reverse inclusion is
this same theorem with the roles of `M₀` and `M₁` exchanged, which asks instead that `M₀` lie in
the `A`-span of `M₁` and that `M₀` be finitely generated. Note it is not that `M₁` spans `M`:
the hypothesis is one containment, not a spanning condition. Neither that instance nor the
resulting equality of topologies is proved here.

`submodulesBasis_pow_smul` proves the basis half of Remark 6.19 without finite generation; this is
where `M₁.FG` does its work. -/
theorem exists_pow_smul_le_pow_smul (P : PairOfDefinition A) {s : A}
    (hs : IsTopologicallyNilpotent s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ M₁ : Submodule P.ringOfDefinition M) (hspan : (M₁ : Set M) ⊆ Submodule.span A (M₀ : Set M))
    (hfg : M₁.FG) (n : ℕ) : ∃ k : ℕ, (⟨s, hs0⟩ : P.ringOfDefinition) ^ k • M₁
      ≤ (⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ := by
  obtain ⟨k, hk⟩ := P.exists_pow_smul_le hs hs0 M₀ M₁ hspan hfg
  refine ⟨n + k, ?_⟩
  have hsplit : (⟨s, hs0⟩ : P.ringOfDefinition) ^ (n + k) • M₁
      = (⟨s, hs0⟩ : P.ringOfDefinition) ^ n • ((⟨s, hs0⟩ : P.ringOfDefinition) ^ k • M₁) := by
    rw [pow_add, mul_smul]
  rw [hsplit]
  exact smul_mono_right ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) hk

end TauCeti.Huber.PairOfDefinition
