/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Separation of the quotient of a topological ring by an ideal

The quotient `R ⧸ I` of a topological ring by an ideal is `T1` exactly when `I` is closed, and
hence `T0`.

Mathlib proves the corresponding statement for the quotient of a topological group by a
subgroup, as `QuotientGroup.t1Space_iff` and `QuotientGroup.instT1Space`. Those are stated for
`G ⧸ N` with `N : AddSubgroup G` in the additive case, whereas `R ⧸ I` is the quotient by an
`Ideal`. The two quotients are definitionally equal — Mathlib's own
`Ideal.topologicalRing_quotient` builds the additive structure of `R ⧸ I` out of
`QuotientAddGroup.instIsTopologicalAddGroup` — but reaching the group statement from an ideal
still means presenting `I` as `I.toAddSubgroup` and transporting the closedness hypothesis along
that presentation, which unification does not do on its own: with only `IsClosed (I : Set R)` in
context, `T1Space (R ⧸ I)` is not synthesized. So the results below are that transport, and
their proofs delegate to Mathlib rather than reproving anything.

Only separate continuity of addition is needed, matching the hypotheses of the group statements
these delegate to; no ring topology and no multiplicative continuity is used.

## Main results

* `Ideal.Quotient.t1Space_iff`: `T1Space (R ⧸ I) ↔ IsClosed (I : Set R)`.
* `Ideal.Quotient.instT1Space`: the instance form, so that `T0Space (R ⧸ I)` is found
  automatically once `I` is known to be closed.
* `Ideal.Quotient.continuous_lift`: a continuous ring homomorphism annihilating `I` induces a
  *continuous* homomorphism on `R ⧸ I`, with no hypothesis on `I`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.38, where a rational localisation is
  presented as a quotient `C ⧸ 𝔞` and its Hausdorff completion is taken.
-/

public section

variable {R : Type*} [TopologicalSpace R] [CommRing R] [SeparatelyContinuousAdd R] (I : Ideal R)

namespace Ideal.Quotient

/-- The quotient of a topological ring by an ideal is `T1` exactly when the ideal is closed.
This is `QuotientAddGroup.t1Space_iff` read through the identification of `R ⧸ I` with the
quotient of `R` by `I.toAddSubgroup`. -/
theorem t1Space_iff : T1Space (R ⧸ I) ↔ IsClosed (I : Set R) :=
  QuotientAddGroup.t1Space_iff (N := I.toAddSubgroup)

/-- The quotient of a topological ring by a closed ideal is `T1`, hence `T0`. Stated as an
instance, with the closedness of `I` as an instance argument, so that the separation of `R ⧸ I`
is available to instance search wherever `I` is known to be closed; this follows
`Ideal.Quotient.normedCommRing`, which takes `IsClosed (I : Set R)` the same way. -/
instance instT1Space [IsClosed (I : Set R)] : T1Space (R ⧸ I) := (t1Space_iff I).mpr ‹_›

omit [SeparatelyContinuousAdd R] in
/-- **A continuous ring homomorphism that kills `I` lifts to a continuous map on `R ⧸ I`.**

No hypothesis on `I` is needed: closedness of `I` is what makes `R ⧸ I` separated
(`Ideal.Quotient.instT1Space` above), which matters for maps *into* `R ⧸ I`, not for maps out
of it. -/
theorem continuous_lift {S : Type*} [Semiring S] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) (hI : ∀ a ∈ I, f a = 0) :
    Continuous (Ideal.Quotient.lift I f hI) :=
  -- `R ⧸ I` carries the coinduced topology, so continuity of a map out of it is continuity of its
  -- composite with the quotient map, which is `f`.
  continuous_coinduced_dom.mpr hf

end Ideal.Quotient
