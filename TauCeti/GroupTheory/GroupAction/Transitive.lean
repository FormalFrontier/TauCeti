/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbit-stabiliser for a transitive action

Mathlib's orbit-stabiliser theorem `MulAction.orbitEquivQuotientStabilizer` identifies the orbit
of a point with the coset space of its stabiliser. When the action is transitive there is only
one orbit, so that identification is between the coset space and the acted-on set itself. This
file records that specialisation, together with the equivariance that makes it an isomorphism of
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
the set acted on, the coset of `g` corresponding to `g • b`. -/
noncomputable def quotientStabilizerEquiv (b : X) : G ⧸ stabilizer G b ≃ X :=
  (orbitEquivQuotientStabilizer G b).symm.trans
    ((Equiv.setCongr (orbit_eq_univ G b)).trans (Equiv.Set.univ X))

@[simp]
theorem quotientStabilizerEquiv_mk (b : X) (g : G) :
    quotientStabilizerEquiv G b (QuotientGroup.mk g) = g • b :=
  (rfl)

/-- The identification of the coset space with the set acted on is equivariant. -/
theorem quotientStabilizerEquiv_smul (b : X) (g : G) (q : G ⧸ stabilizer G b) :
    quotientStabilizerEquiv G b (g • q) = g • quotientStabilizerEquiv G b q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Quotient.smul_mk, quotientStabilizerEquiv_mk, quotientStabilizerEquiv_mk, smul_eq_mul,
      mul_smul]

end TauCeti
