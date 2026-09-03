/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Find

/-!
# Lifting a convergent family along a surjection

A family `g : ι → N` converges to `n₀` along the cofinite filter when all but finitely many of its
members lie in any given neighbourhood of `n₀`. This file shows that a surjection which carries the
neighbourhood filter of `m₀` into that of `n₀` lifts such a family to one converging to `m₀`: the
lift can be chosen convergent, not merely made to exist.

**Openness is not the hypothesis, and would not suffice on its own.** `IsOpenMap φ` puts the image
of a neighbourhood of `m₀` around `φ m₀`, which is a neighbourhood of `n₀` only when `φ m₀ = n₀`.
The hypothesis used here is `𝓝 n₀ ≤ Filter.map φ (𝓝 m₀)`, which is exactly what the proof consumes;
a zero-preserving open surjection — an `A`-linear map, say — is one way to supply it, and that is
the form `TauCeti.Huber` uses it in.

That the lifts exist pointwise is only surjectivity. The content is that they can be chosen
*uniformly enough to still converge*, and this genuinely needs a construction: choosing a preimage
of `g α` for each `α` independently can leave the lifts spread out even when the `g α` collapse to
`n₀`. The fix is to choose the preimage of `g α` from a neighbourhood whose index grows with `α`,
so that convergence is forced by the choice rather than hoped for.

## Main results

* `exists_lift_tendsto_cofinite_nhds`: the lifting statement.

## Implementation notes

Countability of `𝓝 m₀` enters only through `Filter.exists_antitone_basis`, which supplies the
antitone basis the lifts are drawn from. It is taken as an instance rather than as a basis in the
statement, so a caller neither has to produce a basis nor to re-prove the image condition index by
index: `𝓝 n₀ ≤ Filter.map φ (𝓝 m₀)` gives the latter uniformly.

The index of the neighbourhood a lift is drawn from is
`Nat.findGreatest (fun m ↦ g α ∈ φ '' V m) (r α)`, where `r` is an injection of `ι` into `ℕ` —
one exists because `ι` is countable, and it tends to infinity cofinitely because `cofinite` is
`atTop` on `ℕ`. **The cap by `r α` is what makes the definition total.** Without it the natural
index is the largest `m` with `g α ∈ φ '' V m`, and no largest one need exist: the set of such `m`
can be empty, which is the common case, and it can equally be unbounded, when `g α` lies in every
`φ '' V m`. `Nat.findGreatest` returns a usable index in both cases, so capping removes them
rather than splitting on them.

No algebraic structure is used: `M` and `N` carry only a topology and a distinguished point. In
particular the neighbourhoods drawn from are not assumed to be subgroups, which the argument would
need if it ever added two lifts — it never does, choosing each independently. Nothing about `m₀`
and `n₀` is used beyond their neighbourhood filters — no zero, and no algebra.
-/

namespace TauCeti

open Filter Topology Set

public section

variable {ι : Type*} [Countable ι] {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

omit [Countable ι] [TopologicalSpace M] [TopologicalSpace N] in
/-- Preimages chosen inside a prescribed neighbourhood **whenever one is available there**, and
arbitrary otherwise. Surjectivity gives a preimage in every case; the second component is the part
that matters, and it is vacuous exactly on the finitely many indices the main proof discards. -/
private theorem exists_preimage_mem_of_mem_image (φ : M → N) (hsurj : Function.Surjective φ)
    (V : ℕ → Set M) (g : ι → N) (n : ι → ℕ) :
    ∃ f : ι → M, ∀ α, φ (f α) = g α ∧ (g α ∈ φ '' V (n α) → f α ∈ V (n α)) := by
  classical
  have pick : ∀ α, ∃ x : M, φ x = g α ∧ (g α ∈ φ '' V (n α) → x ∈ V (n α)) := by
    intro α
    by_cases h : g α ∈ φ '' V (n α)
    · obtain ⟨x, hxV, hxg⟩ := h
      exact ⟨x, hxg, fun _ ↦ hxV⟩
    · obtain ⟨x, hx⟩ := hsurj (g α)
      exact ⟨x, hx, fun hc ↦ absurd hc h⟩
  choose f hf1 hf2 using pick
  exact ⟨f, fun α ↦ ⟨hf1 α, hf2 α⟩⟩

/-- **A convergent family lifts to a convergent family.** If `φ` is surjective and carries the
neighbourhood filter of `m₀` into that of `n₀`, then any family tending to `n₀` cofinitely has a
`φ`-preimage family tending to `m₀` cofinitely.

Pointwise lifting is surjectivity alone; the statement is that a *single* choice of lifts can be
made to converge. Note that `IsOpenMap φ` supplies the filter hypothesis only together with
`φ m₀ = n₀`; openness by itself places the images around `φ m₀`, not around `n₀`.

**Two countability hypotheses are essential**, and both are instance arguments rather than
explicit ones. `[(𝓝 m₀).IsCountablyGenerated]` is what produces the antitone basis the lifts are
drawn from, and `[Countable ι]` — from the variable block — is what supplies the injection
`ι ↪ ℕ` that caps the construction. Neither is bookkeeping: without the first there is no
sequence of neighbourhoods to index, and without the second the cap has nothing to grow along. -/
theorem exists_lift_tendsto_cofinite_nhds {m₀ : M} {n₀ : N} [(𝓝 m₀).IsCountablyGenerated]
    (φ : M → N) (hsurj : Function.Surjective φ) (hmap : 𝓝 n₀ ≤ Filter.map φ (𝓝 m₀))
    (g : ι → N) (hg : Tendsto g (Filter.cofinite : Filter ι) (𝓝 n₀)) :
    ∃ f : ι → M, (∀ α, φ (f α) = g α) ∧ Tendsto f (Filter.cofinite : Filter ι) (𝓝 m₀) := by
  classical
  obtain ⟨V, hV⟩ := (𝓝 m₀).exists_antitone_basis
  have hVmem : ∀ i, φ '' V i ∈ 𝓝 n₀ := fun i ↦ hmap (Filter.image_mem_map (hV.mem i))
  obtain ⟨r, hr⟩ := exists_injective_nat ι
  replace hr : Tendsto r (Filter.cofinite : Filter ι) atTop :=
    Nat.cofinite_eq_atTop ▸ hr.tendsto_cofinite
  obtain ⟨f, hf⟩ := exists_preimage_mem_of_mem_image φ hsurj V g
    (fun α ↦ Nat.findGreatest (fun m ↦ g α ∈ φ '' V m) (r α))
  refine ⟨f, fun α ↦ (hf α).1, ?_⟩
  rw [hV.toHasBasis.tendsto_right_iff]
  intro i _
  have hfin : {α | g α ∉ φ '' V i}.Finite := by
    simpa [Filter.eventually_cofinite] using hg.eventually_mem (hVmem i)
  have hfin2 : {α | r α < i}.Finite := by
    simpa [Filter.eventually_cofinite, not_le] using hr.eventually_ge_atTop i
  rw [Filter.eventually_cofinite]
  refine (hfin.union hfin2).subset fun α hα ↦ ?_
  by_cases h1 : g α ∈ φ '' V i
  · by_cases h2 : i ≤ r α
    · have hle : i ≤ Nat.findGreatest (fun m ↦ g α ∈ φ '' V m) (r α) := Nat.le_findGreatest h2 h1
      have hspec : g α ∈ φ '' V (Nat.findGreatest (fun m ↦ g α ∈ φ '' V m) (r α)) :=
        Nat.findGreatest_spec (P := fun m ↦ g α ∈ φ '' V m) h2 h1
      have hmem : f α ∈ V i := hV.antitone hle ((hf α).2 hspec)
      exact absurd hmem hα
    · exact Or.inr (not_le.mp h2)
  · exact Or.inl h1

end

end TauCeti
