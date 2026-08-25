/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits

/-!
# A Tate ring has a zero sequence of units

Henkel's open mapping theorem is stated for a topological ring carrying a *zero sequence of
units*. That hypothesis and the absorption property it exists for are generic, and live in
`TauCeti/Topology/Algebra/ZeroSequenceOfUnits.lean`; this file supplies the bridge from Huber
theory, namely that the powers of a pseudouniformiser are such a sequence.

This is where the Tate condition enters Henkel's theorem: a Huber ring that is not Tate need not
admit such a sequence, `ℤ_[p]` being the example.

## Main results

* `TauCeti.Huber.IsPseudoUniformizer.tendsto_pow_unit`: the powers of a pseudouniformiser
  converge to zero, as units. This is the concrete sequence, kept nameable so a caller holding
  `ϖ` can feed *it* to the generic results instead of destructing an existential.
* `TauCeti.Huber.IsPseudoUniformizer.hasZeroSequenceOfUnits` and
  `TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`: a pseudouniformiser — hence a Tate ring, by
  instance search — satisfies the hypothesis.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647), whose hypothesis this discharges.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16 and Propositions 6.17–6.18, which are
  proved from Henkel's theorem; downstream context for this file rather than its source.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable {A : Type*} [MonoidWithZero A] [TopologicalSpace A]

/-- **The powers of a pseudouniformiser converge to zero, as units.** This is the concrete zero
sequence, kept nameable so a caller holding `ϖ` can feed *it* to the absorption and covering
results instead of destructing an existential. -/
theorem IsPseudoUniformizer.tendsto_pow_unit {a : A} (ha : IsPseudoUniformizer a) :
    Tendsto (fun n ↦ ((ha.isUnit.unit ^ n : Aˣ) : A)) atTop (𝓝 0) := by
  -- `IsTopologicallyNilpotent` is a `def`, so ascribe its `Tendsto` form for `simp` to see.
  have hnil : Tendsto (fun n ↦ a ^ n) atTop (𝓝 0) := ha.isTopologicallyNilpotent
  simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hnil

/-- **A pseudouniformiser makes the ring admit a zero sequence of units.** No Huber or Tate
hypothesis is needed: a topologically nilpotent unit *supplies* the class, through its powers.
It is sufficient, not equivalent — the class asks only for some sequence of units tending to
zero, and such a sequence need not consist of the powers of a single unit. The witness here is
`TauCeti.Huber.IsPseudoUniformizer.tendsto_pow_unit`, which a caller wanting the powers
themselves should use instead. -/
theorem IsPseudoUniformizer.hasZeroSequenceOfUnits {a : A} (ha : IsPseudoUniformizer a) :
    HasZeroSequenceOfUnits A :=
  ⟨_, ha.tendsto_pow_unit⟩

/-- **A Tate ring satisfies Henkel's hypothesis on the base ring**, via the powers of a
pseudouniformiser.

This is where the Tate condition enters Henkel's theorem: a Huber ring that is not Tate need not
admit such a sequence, `ℤ_[p]` being the example. -/
instance IsTateRing.hasZeroSequenceOfUnits {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] : HasZeroSequenceOfUnits A :=
  let ⟨_, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  ha.hasZeroSequenceOfUnits

end TauCeti.Huber

end
