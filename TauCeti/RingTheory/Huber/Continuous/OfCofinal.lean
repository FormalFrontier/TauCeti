/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Continuous.Valuation
public import TauCeti.RingTheory.Valuation.CharacteristicGroup
import TauCeti.RingTheory.Valuation.SpanPow

/-!
# Cofinal values on a generating set make a valuation continuous

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), the engine of Theorem 7.10's `⊇` direction.**

A valuation on a Huber ring is continuous as soon as it is bounded by `1` on an ideal of
definition `I` and has cofinal values on a generating set of `I`. That is exactly what the
right-hand side of Theorem 7.10 supplies: membership in `Spv (A, IA)` gives the cofinality, by
Wedhorn Lemma 7.4, and `v a < 1` on `I` gives the bound.

## What the argument actually needs

Continuity is tested against the basic neighbourhoods `Iⁿ` of zero
(`TauCeti.Huber.PairOfDefinition.isContinuous_iff_forall_exists_idealImage_subset`), so given `b`
with `v b ≠ 0` the task is to find one `n` with `v < v b` on the image of `Iⁿ`.

Only **one** generator has to be cofinal: one whose value dominates the others. Cofinality there
produces an `n` with `v t₀ ⁿ < v b`, the valuation bound on a power of a spanned ideal
(`Valuation.map_le_pow_of_mem_span_pow_succ`) gives `v ≤ v t₀ ⁿ` on `Iⁿ⁺¹`, and the two
inequalities compose. That is `isContinuous_of_forall_le_of_cofinalValue`, which asks for no
finiteness at all.

The form a call site actually holds — a *finite* generating set with *every* generator cofinal, as
Lemma 7.4 hands over — is the corollary `isContinuous_of_forall_cofinalValue`. Finiteness enters
there and only there, to produce the dominating generator as a maximum.

## Why the bound is taken over `A₀`

The valuation bound is applied through `v.comap P.ringOfDefinition.subtype`, over the ring of
definition rather than over `A`. That is forced rather than cosmetic. An element of `Iⁿ⁺¹` is a
sum of terms `c * t₀ * ⋯ * tₙ` whose coefficient `c` ranges over `A₀`, so the coefficient can be
absorbed into a generator — `c * t₀` lies in `I`, where `v ≤ 1` is available. Over the extension
`I · A` the coefficients range over all of `A` instead, and `v ≤ 1` on `I · A` does not follow
from these hypotheses.

## Main results

* `TauCeti.Huber.PairOfDefinition.isContinuous_of_forall_le_of_cofinalValue` : the engine, needing
  cofinality at a single dominating generator.
* `TauCeti.Huber.PairOfDefinition.isContinuous_of_forall_cofinalValue` : its call-site form, for a
  finite generating set with every generator cofinal.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Theorem 7.10 and Lemma 7.4.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

open TauCeti TauCeti.Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **A single dominating cofinal generator makes a valuation continuous.** If `v ≤ 1` on an ideal
of definition `I`, and `I` is spanned by a set whose values `v` bounds by that of some `t₀` with
cofinal value, then `v` is continuous.

No finiteness is needed: the spanning set is an arbitrary `Set`, cofinality is asked of `t₀`
alone, and `t₀` need not even lie in the spanning set — dominating it is enough.
`isContinuous_of_forall_cofinalValue` below is the reading a call site usually holds. -/
theorem isContinuous_of_forall_le_of_cofinalValue (P : PairOfDefinition A) (v : Valuation A Γ₀)
    {s : Set P.ringOfDefinition} {t₀ : P.ringOfDefinition}
    (hgen : Ideal.span s = P.idealOfDefinition)
    (hle : ∀ t ∈ s, v ((t : P.ringOfDefinition) : A) ≤ v ((t₀ : P.ringOfDefinition) : A))
    (h1 : ∀ a ∈ P.idealOfDefinition, v ((a : P.ringOfDefinition) : A) ≤ 1)
    (hcof : CofinalValue v ((t₀ : P.ringOfDefinition) : A)) :
    v.IsContinuous := by
  rw [isContinuous_iff_forall_exists_idealImage_subset P]
  intro b hb
  obtain ⟨n, hn⟩ :=
    cofinalValue_iff.mp hcof (v.restrict b) (by simpa using zero_lt_iff.mpr hb)
  have hlt : v ((t₀ : P.ringOfDefinition) : A) ^ n < v b := by
    have hemb := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hn
    simpa only [map_pow, _root_.Valuation.embedding_restrict] using hemb
  refine ⟨n + 1, fun x hx ↦ ?_⟩
  -- The bound on `Iⁿ⁺¹`, taken over `A₀` so that the coefficients stay inside `I`.
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage (n + 1)).mp hx
  set w := v.comap P.ringOfDefinition.subtype with hw
  have hsw : ∀ t ∈ s, w t ≤ v ((t₀ : P.ringOfDefinition) : A) := by
    simpa only [hw, _root_.Valuation.comap_apply, Subring.coe_subtype] using hle
  have h1w : ∀ a ∈ Ideal.span s, w a ≤ 1 := by
    rw [hgen]
    simpa only [hw, _root_.Valuation.comap_apply, Subring.coe_subtype] using h1
  have hbound : w y ≤ v ((t₀ : P.ringOfDefinition) : A) ^ n :=
    _root_.Valuation.map_le_pow_of_mem_span_pow_succ w hsw h1w (by rwa [hgen])
  exact lt_of_le_of_lt
    (by simpa only [hw, _root_.Valuation.comap_apply, Subring.coe_subtype] using hbound) hlt

/-- **Cofinal values on a finite generating set make a valuation continuous.** If `v ≤ 1` on an
ideal of definition `I` and `v` has cofinal values at every member of a finite generating set of
`I`, then `v` is continuous.

This is the engine above with the dominating generator produced as a maximum, which is the only
thing finiteness is used for. The empty generating set is allowed: it forces `I = ⊥`, whose first
basic neighbourhood is already `{0}`.

It is the form Wedhorn Theorem 7.10's `⊇` direction hands over: membership in `Spv (A, IA)`
supplies the cofinality through Lemma 7.4, and `v a < 1` on `I` supplies the bound. -/
theorem isContinuous_of_forall_cofinalValue (P : PairOfDefinition A) (v : Valuation A Γ₀)
    {s : Finset P.ringOfDefinition}
    (hgen : Ideal.span (s : Set P.ringOfDefinition) = P.idealOfDefinition)
    (h1 : ∀ a ∈ P.idealOfDefinition, v ((a : P.ringOfDefinition) : A) ≤ 1)
    (hcof : ∀ t ∈ s, CofinalValue v ((t : P.ringOfDefinition) : A)) :
    v.IsContinuous := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- `I = ⊥`, so the first basic neighbourhood is `{0}` and every `v b ≠ 0` dominates it.
    rw [isContinuous_iff_forall_exists_idealImage_subset P]
    intro b hb
    refine ⟨1, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage 1).mp hx
    rw [← hgen] at hy
    simp only [Finset.coe_empty, Ideal.span_empty, pow_one, Ideal.mem_bot] at hy
    simpa [hy] using zero_lt_iff.mpr hb
  · obtain ⟨t₀, ht₀s, ht₀max⟩ := s.exists_max_image (fun t ↦ v ((t : P.ringOfDefinition) : A)) hne
    exact isContinuous_of_forall_le_of_cofinalValue P v hgen
      (fun t ht ↦ ht₀max t (Finset.mem_coe.mp ht)) h1 (hcof t₀ ht₀s)

end TauCeti.Huber.PairOfDefinition

end
