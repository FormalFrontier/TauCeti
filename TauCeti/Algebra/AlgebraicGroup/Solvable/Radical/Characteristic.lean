/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction

/-!
# When the solvable radical is the whole group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. The
solvable radical of `H` is the whole represented group exactly when `H` itself is geometrically
connected, smooth, and has a solvable group of geometric points. In Hopf coordinates, the whole
closed subgroup is cut out by the zero Hopf ideal, so this criterion says that
`solvableRadicalDefiningIdeal H = ⊥`.

Applying the criterion to the solvable radical itself shows that the construction is idempotent:
the solvable radical of `R(H)` is all of `R(H)`.

## Main declarations

* `TauCeti.HopfIdeal.isSolvableRadicalCandidate_bot_iff`: the whole group is a
  solvable-radical candidate exactly under the expected three conditions.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_bot_iff`: the solvable
  radical is the whole group exactly when the ambient group is connected, smooth, and solvable.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_solvableRadical_eq_bot`:
  taking the solvable radical twice does not shrink it further.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This supplies the characteristic and idempotence API for the solvable-radical construction in
Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- The zero Hopf ideal is a solvable-radical candidate exactly when the whole represented group
is geometrically connected, smooth, and has a solvable group of geometric points. -/
@[simp] theorem isSolvableRadicalCandidate_bot_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsSolvableRadicalCandidate H ⊥ ↔
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
        Algebra.Smooth k H ∧
        geometricallySolvablePointsCommHopfAlgProperty k H.obj := by
  let e := FiniteTypeCommHopfAlgCat.quotientBotIso H
  let e' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (_root_.CommHopfAlgCat.{u} k)).mapIso e
  constructor
  · intro h
    exact ⟨
      (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e' h.geometricallyConnected,
      (smoothCommHopfAlgProperty_iff _).mp <|
        (smoothCommHopfAlgProperty k).prop_of_iso e'
          ((smoothCommHopfAlgProperty_iff _).mpr h.smooth),
      (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e'
        h.geometricallySolvable⟩
  · rintro ⟨hconnected, hsmooth, hsolvable⟩
    exact IsSolvableRadicalCandidate.mk HopfIdeal.isNormal_bot
      ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e'.symm hconnected)
      ((smoothCommHopfAlgProperty_iff _).mp <|
        (smoothCommHopfAlgProperty k).prop_of_iso e'.symm
          ((smoothCommHopfAlgProperty_iff _).mpr hsmooth))
      ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e'.symm hsolvable)

end HopfIdeal

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The solvable radical is the whole represented group exactly when the ambient finite-type
affine group is geometrically connected, smooth, and has a solvable group of geometric points.

The equality is stated on defining Hopf ideals: the zero ideal cuts out the whole group. -/
@[simp] theorem solvableRadicalDefiningIdeal_eq_bot_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    solvableRadicalDefiningIdeal H = ⊥ ↔
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
        Algebra.Smooth k H ∧
        geometricallySolvablePointsCommHopfAlgProperty k H.obj := by
  constructor
  · intro h
    have hcandidate := isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H
    rw [h, HopfIdeal.isSolvableRadicalCandidate_bot_iff] at hcandidate
    exact hcandidate
  · intro h
    apply le_antisymm
    · exact solvableRadicalDefiningIdeal_le H ⊥
        ((HopfIdeal.isSolvableRadicalCandidate_bot_iff H).2 h)
    · exact bot_le

/-- The solvable radical of the solvable radical is the whole solvable radical. Equivalently,
the solvable-radical construction is idempotent on defining ideals. -/
@[simp] theorem solvableRadicalDefiningIdeal_solvableRadical_eq_bot
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    solvableRadicalDefiningIdeal (solvableRadical H) = ⊥ := by
  rw [solvableRadicalDefiningIdeal_eq_bot_iff]
  exact ⟨geometricallyConnected_solvableRadical H, smooth_solvableRadical H,
    geometricallySolvable_solvableRadical H⟩

end FiniteTypeCommHopfAlgCat

end

end TauCeti
