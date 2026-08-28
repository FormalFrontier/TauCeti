/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbit-stabiliser for a transitive action

Mathlib's `MulAction.ofQuotientStabilizer` sends the coset of `g` in `G ⧸ stabilizer G b` to
`g • b`; it is injective by `MulAction.injective_ofQuotientStabilizer`, and its image is the orbit
of `b`, which is the orbit-stabiliser theorem. When the action is transitive that orbit is all of
`X`, so the map is a bijection. This file records that specialisation, together with the
equivariance -- Mathlib's `MulAction.ofQuotientStabilizer_smul` -- that makes it an isomorphism of
`G`-sets rather than a bare bijection.

## Main definitions

* `TauCeti.quotientStabilizerEquiv`: for a transitive action of `G` on `X` and a point `b : X`,
  the equivalence `G ⧸ stabilizer G b ≃ X` sending the coset of `g` to `g • b`.

## Main results

* `TauCeti.quotientStabilizerEquiv_mk`: its value on a coset, and
  `TauCeti.quotientStabilizerEquiv_smul`: its equivariance.

## Implementation notes

The equivalence is unbundled -- an `Equiv` of types together with a separate equivariance lemma --
because that is the shape the constructions consuming it take their argument in, for instance
`TauCeti.ofMulActionEquivCongr`, which builds the induced equivalence of permutation
representations.
-/

public section

open MulAction

namespace TauCeti

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]

/-- **Orbit-stabiliser for a transitive action**: the coset space of the stabiliser of a point is
the set acted on, the coset of `g` corresponding to `g • b`.  This is
`MulAction.ofQuotientStabilizer`, which transitivity makes surjective. -/
noncomputable def quotientStabilizerEquiv (b : X) : G ⧸ stabilizer G b ≃ X :=
  Equiv.ofBijective (ofQuotientStabilizer G b)
    ⟨injective_ofQuotientStabilizer G b, fun x => by
      obtain ⟨g, hg⟩ := exists_smul_eq G b x
      exact ⟨QuotientGroup.mk g, (ofQuotientStabilizer_mk G b g).trans hg⟩⟩

/-- The computation rule for `TauCeti.quotientStabilizerEquiv`: on the coset represented by `g` it
takes the value `g • b`. -/
@[simp]
theorem quotientStabilizerEquiv_mk (b : X) (g : G) :
    quotientStabilizerEquiv G b (QuotientGroup.mk g) = g • b :=
  ofQuotientStabilizer_mk G b g

/-- The identification of the coset space with the set acted on is equivariant. -/
@[simp]
theorem quotientStabilizerEquiv_smul (b : X) (g : G) (q : G ⧸ stabilizer G b) :
    quotientStabilizerEquiv G b (g • q) = g • quotientStabilizerEquiv G b q :=
  ofQuotientStabilizer_smul G b g q

end TauCeti
