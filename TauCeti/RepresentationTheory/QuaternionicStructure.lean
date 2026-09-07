/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# Quaternionic structures on a complex representation

A **quaternionic structure** on a representation `ρ` of `G` on a complex vector space `V` is a
conjugate-linear map `J : V →ₗ⋆[ℂ] V` with `J (J v) = -v` that commutes with the action.  It is the
`-1` case of the Frobenius-Schur reality trichotomy; the `1` case is a real structure, a
conjugate-linear *involution* commuting with the action, `Representation.IsRealStructure` in
`TauCeti/RepresentationTheory/RealForm.lean`.

The two predicates differ only in the sign of the square, and the constructions in
`TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean` treat them together.  What separates
them is that a quaternionic structure has no nonzero fixed vector
(`Representation.IsQuaternionicStructure.eq_zero_of_apply_eq_self`), so, unlike a real structure,
it cuts out no real form; that is why the real-form theory lives beside
`Representation.IsRealStructure` while this predicate stands on its own.

Only the predicate and the two facts that follow from its definition alone are here, so that
stating a quaternionic structure costs no invariant-form or finite-dimensional machinery.  Its
equivalence with a nondegenerate invariant alternating form, and the reading of the Frobenius-Schur
value `-1` off it, are in
`TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean` and
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/StructureMap.lean`.

## Main definitions

* `Representation.IsQuaternionicStructure`: a conjugate-linear `J` with `J (J v) = -v` commuting
  with the action.

## Main results

* `Representation.IsQuaternionicStructure.bijective`: a quaternionic structure is bijective.
* `Representation.IsQuaternionicStructure.eq_zero_of_apply_eq_self`: a quaternionic structure has no
  nonzero fixed vector.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §6.
-/

public section

namespace Representation

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

variable (ρ) in
/-- A **quaternionic structure** on a complex representation: a conjugate-linear map `J` of the
underlying space that squares to `-1` and commutes with the action.  It is the `-1` case of the
Frobenius-Schur reality trichotomy, `Representation.IsRealStructure` being the `1` case.

The two predicates differ only in the sign of the square, and the constructions of
`TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean` treat them together; what separates
them is that a quaternionic structure has no nonzero fixed vector
(`Representation.IsQuaternionicStructure.eq_zero_of_apply_eq_self`), so no real form attaches to it.
The map is carried unbundled, matching `Representation.IsRealStructure` and
`TauCeti.Representation.IsInvariantForm`. -/
structure IsQuaternionicStructure (J : V →ₛₗ[starRingEnd ℂ] V) : Prop where
  /-- The map squares to `-1`. -/
  sq_eq_neg (v : V) : J (J v) = -v
  /-- The map intertwines the action with itself. -/
  isIntertwining (g : G) (v : V) : J (ρ g v) = ρ g (J v)

-- `grind` splits a witness in the context into its two fields, so both defining equations are
-- available to it without the projections being invoked by hand.  `sq_eq_neg` cannot be registered
-- as a rewrite rule on its own: neither `G` nor `ρ` occurs in it, so `grind =` rejects it.
attribute [grind cases] IsQuaternionicStructure

-- The intertwining equation moves `J` past the action, which is the normal form the constructions
-- downstream use; `ρ` occurs in its left-hand side, so `simp` can instantiate it.  `sq_eq_neg`
-- cannot be tagged for the reason `grind =` rejects it: its left-hand side `J (J v)` mentions
-- neither `G` nor `ρ`, so `simpNF` reports that the lemma "will never apply".  It is passed
-- explicitly, `simp [h.sq_eq_neg]`, as `Representation.IsRealStructure.involutive` is.
attribute [simp] IsQuaternionicStructure.isIntertwining

namespace IsQuaternionicStructure

variable {J : V →ₛₗ[starRingEnd ℂ] V} (h : IsQuaternionicStructure ρ J)

include h

/-- **A quaternionic structure is bijective**, with `-J` as its two-sided inverse -- the analogue
of the bijectivity a real structure has as an involution. -/
theorem bijective : Function.Bijective ⇑J :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun v => -J v, fun v => by simp [h.sq_eq_neg], fun v => by simp [map_neg, h.sq_eq_neg]⟩

/-- **A quaternionic structure has no nonzero fixed vector**: a fixed vector satisfies `v = -v`.
So, unlike a real structure, it cuts out no real form; its fixed points are `0`. -/
theorem eq_zero_of_apply_eq_self {v : V} (hv : J v = v) : v = 0 := by
  have hneg : v = -v := by
    have hsq := h.sq_eq_neg v
    rwa [hv, hv] at hsq
  have h2 : (2 : ℂ) • v = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end IsQuaternionicStructure

end Representation
