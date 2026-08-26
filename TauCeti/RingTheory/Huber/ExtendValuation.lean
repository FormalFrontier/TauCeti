/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Valuation.ExtendOfPowMulMem

/-!
# Extending a valuation from a ring of definition to the whole Huber ring

A ring of definition `A₀` of a Huber ring `A` is open, so a topologically nilpotent `s`
multiplies every element of `A` into it: `TauCeti.Huber.PairOfDefinition.exists_pow_mul_mem`
gives an `n` with `sⁿ * a ∈ A₀`. That is exactly the hypothesis under which
`Valuation.extendOfPowMulMem` extends a valuation of a subring to the whole ring, so a valuation
`w` of `A₀` that does not vanish at `s` has a unique extension to `A`,

`v a = w (sⁿ * a) * (w s)⁻ⁿ`.

This file is that specialisation. `PairOfDefinition.extendValuation` is
`Valuation.extendOfPowMulMem` with `exists_pow_mul_mem` fed in as the hypothesis, and each
interface theorem below restates the corresponding one of the general layer for a pair of
definition. Topology enters only through `exists_pow_mul_mem`, to produce the exponents; the
construction itself, its well-definedness and its uniqueness live in
`TauCeti.RingTheory.Valuation.ExtendOfPowMulMem`.

## Why this is not `Valuation.extendToLocalization`

Topological nilpotence of `s` does not make `s` invertible in `A`, so the localisation `A₀[1/s]`
along which Mathlib's `Valuation.extendToLocalization` would extend need not map to `A` at all.
Take `A = ℤ_[p]` with `A₀ = A` and `s = p`, where `A₀[1/s] = ℚ_[p]`. What does hold, and is all
the construction needs, is the one-sided statement that a power of `s` carries each element of
`A` into `A₀`.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.extendValuation` : the extension of a valuation of the ring
  of definition to `A`.

## Main results

* `TauCeti.Huber.PairOfDefinition.extendValuation_apply` : the defining formula, at **every**
  exponent that works, not just the chosen one. This is the interface; the definition goes
  through `Classical.choose` and is not meant to be unfolded.
* `TauCeti.Huber.PairOfDefinition.extendValuation_coe` : the extension restricts to `w`.
* `TauCeti.Huber.PairOfDefinition.eq_extendValuation` : **uniqueness** — any valuation of `A`
  restricting to `w` *is* this one, so the extension is canonical.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(3), which is where
  this extension is used.

## Provenance

Adapted from [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch
`dev/adic-spaces`, commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/Lemma745.lean`,
declaration `exists_valuation_extension`, which states this Huber-ring case existentially, as
`∃ v_ext, …`. Here it is a `def`, obtained by specialising the general construction of
`TauCeti.RingTheory.Valuation.ExtendOfPowMulMem`, whose provenance note records the rest of the
adaptation.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **The extension of `w` from the ring of definition to `A`.** For any `n` with
`sⁿ * a ∈ A₀` — one exists because `A₀` is open and `s` is topologically nilpotent — the value
is `w (sⁿ * a) * (w s)⁻ⁿ`, and `extendValuation_apply` says so at every such `n`. -/
noncomputable def extendValuation (P : PairOfDefinition A) (w : Valuation P.ringOfDefinition Γ₀)
    {s : A} (hs : s ∈ P.ringOfDefinition) (hnil : IsTopologicallyNilpotent s)
    (hw : w ⟨s, hs⟩ ≠ 0) : Valuation A Γ₀ :=
  w.extendOfPowMulMem hs (P.exists_pow_mul_mem hnil) hw

/-- **The defining formula**, at every exponent that carries `a` into the ring of definition. -/
theorem extendValuation_apply (P : PairOfDefinition A) (w : Valuation P.ringOfDefinition Γ₀)
    {s : A} (hs : s ∈ P.ringOfDefinition) (hnil : IsTopologicallyNilpotent s)
    (hw : w ⟨s, hs⟩ ≠ 0) (a : A) {n : ℕ} (hn : s ^ n * a ∈ P.ringOfDefinition) :
    P.extendValuation w hs hnil hw a = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n :=
  w.extendOfPowMulMem_apply hs _ hw a hn

/-- **The extension restricts to `w`** on the ring of definition. -/
@[simp]
theorem extendValuation_coe (P : PairOfDefinition A) (w : Valuation P.ringOfDefinition Γ₀)
    {s : A} (hs : s ∈ P.ringOfDefinition) (hnil : IsTopologicallyNilpotent s)
    (hw : w ⟨s, hs⟩ ≠ 0) (a : P.ringOfDefinition) :
    P.extendValuation w hs hnil hw (a : A) = w a :=
  w.extendOfPowMulMem_coe hs _ hw a

/-- **The extension is the only one**: a valuation of `A` restricting to `w` on the ring of
definition is `P.extendValuation`. -/
theorem eq_extendValuation (P : PairOfDefinition A) (w : Valuation P.ringOfDefinition Γ₀)
    {s : A} (hs : s ∈ P.ringOfDefinition) (hnil : IsTopologicallyNilpotent s)
    (hw : w ⟨s, hs⟩ ≠ 0) (v : Valuation A Γ₀)
    (hv : ∀ a : P.ringOfDefinition, v (a : A) = w a) :
    v = P.extendValuation w hs hnil hw :=
  w.eq_extendOfPowMulMem hs _ hw v hv

end TauCeti.Huber.PairOfDefinition
