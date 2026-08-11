/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.Basic

/-!
# The orbit quotient of a regular open map is homeomorphic to the base

For a regular deck action, `Deck.IsRegular.orbitQuotientEquivBase` already identifies the
deck-orbit quotient `E / Deck p` with the base `B` as a bare equivalence. This file upgrades
that equivalence to a homeomorphism when `p` is continuous and open.

This is the abstract form of the universal-covers identity `UniversalCover x₀ / π₁(X, x₀) ≃ X`,
stated for an arbitrary regular open map rather than the specific based-path cover. The
covering-map application supplies the continuity and openness hypotheses from
`IsCoveringMap.continuous` and `IsCoveringMap.isOpenMap`; the total space is not assumed
preconnected.

## Main declarations

* `TauCeti.Deck.continuous_orbitQuotientToBase`: a continuous map induces a continuous map
  `E / Deck p → B`.
* `TauCeti.Deck.isOpenMap_orbitQuotientToBase`: that map is open.
* `TauCeti.Deck.IsRegular.orbitQuotientHomeomorphBase`: for a regular continuous open map,
  `E / Deck p` is homeomorphic to the base.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 1, where
`UniversalCover x₀ / π₁(X, x₀) ≃ X` follows from the deck-group identification via Mathlib's
`IsQuotientCoveringMap`; the present statement is its base-independent regular-cover form.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- A continuous map induces a continuous map from the deck-orbit quotient to the base. -/
lemma continuous_orbitQuotientToBase (hp : Continuous p) :
    Continuous (orbitQuotientToBase p) :=
  hp.quotient_lift fun _ _ h => eq_proj_of_orbitRel h

/-- An open map induces an open map from the deck-orbit quotient to the base. -/
lemma isOpenMap_orbitQuotientToBase (hp : IsOpenMap p) :
    IsOpenMap (orbitQuotientToBase p) :=
  IsOpenMap.of_comp (f := Quotient.mk'') continuous_quotient_mk' Quotient.mk''_surjective
    (by simpa [Function.comp_def] using hp)

namespace IsRegular

/-- For a regular continuous open map, the deck-orbit quotient `E / Deck p` is homeomorphic to
the base. -/
@[expose] noncomputable def orbitQuotientHomeomorphBase (hreg : IsRegular p) (hcont : Continuous p)
    (hopen : IsOpenMap p) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ₜ B :=
  hreg.orbitQuotientEquivBase.toHomeomorphOfContinuousOpen
    (continuous_orbitQuotientToBase hcont) (isOpenMap_orbitQuotientToBase hopen)

/-- On the underlying equivalence, the orbit-quotient homeomorphism is
`orbitQuotientEquivBase`. -/
@[simp]
lemma orbitQuotientHomeomorphBase_apply (hreg : IsRegular p) (hcont : Continuous p)
    (hopen : IsOpenMap p) (x : MulAction.orbitRel.Quotient (Deck p) E) :
    hreg.orbitQuotientHomeomorphBase hcont hopen x = hreg.orbitQuotientEquivBase x :=
  rfl

/-- The orbit-quotient homeomorphism evaluates on representatives by the projection map. -/
@[simp]
lemma orbitQuotientHomeomorphBase_mk (hreg : IsRegular p) (hcont : Continuous p)
    (hopen : IsOpenMap p) (e : E) :
    hreg.orbitQuotientHomeomorphBase hcont hopen
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = p e :=
  hreg.orbitQuotientEquivBase_mk e

/-- The inverse orbit-quotient homeomorphism sends a projected point to the class of any
lift. -/
@[simp]
lemma orbitQuotientHomeomorphBase_symm_apply_proj (hreg : IsRegular p) (hcont : Continuous p)
    (hopen : IsOpenMap p) (e : E) : (hreg.orbitQuotientHomeomorphBase hcont hopen).symm (p e) =
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) :=
  hreg.orbitQuotientEquivBase_symm_apply_proj e

end IsRegular

end Deck

end TauCeti
