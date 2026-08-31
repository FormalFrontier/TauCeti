/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# When the unipotent radical is the whole group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. The
unipotent radical of `H` is the whole represented group exactly when `H` itself is geometrically
connected, smooth, and unipotent. In Hopf coordinates, the whole closed subgroup is cut out by
the zero Hopf ideal, so this criterion says that `unipotentRadicalDefiningIdeal H = ⊥`.

Applying the criterion to the unipotent radical itself shows that the construction is
idempotent: the unipotent radical of `R_u(H)` is all of `R_u(H)`. The corresponding coordinate
quotient map is therefore an isomorphism.

## Main declarations

* `TauCeti.HopfIdeal.isUnipotentRadicalCandidate_bot_iff`: the whole group is a
  unipotent-radical candidate exactly under the expected three conditions.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_bot_iff`: the unipotent
  radical is the whole group exactly when the ambient group is connected, smooth, and
  unipotent.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_unipotentRadical_eq_bot`:
  taking the unipotent radical twice does not shrink it further.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This supplies the characteristic and idempotence API for the unipotent-radical construction in
Layer 5, "The unipotent radical", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- The zero Hopf ideal is a unipotent-radical candidate exactly when the whole represented
group is geometrically connected, smooth, and unipotent. -/
@[simp] theorem isUnipotentRadicalCandidate_bot_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsUnipotentRadicalCandidate H ⊥ ↔
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
        smoothUnipotentCommHopfAlgProperty k H := by
  let e := FiniteTypeCommHopfAlgCat.quotientBotIso H
  constructor
  · intro h
    exact ⟨
      (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso e) h.geometricallyConnected,
      (smoothUnipotentCommHopfAlgProperty k).prop_of_iso e h.smoothUnipotent⟩
  · rintro ⟨hconnected, hunipotent⟩
    exact IsUnipotentRadicalCandidate.mk HopfIdeal.isNormal_bot
      ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso e.symm) hconnected)
      ((smoothUnipotentCommHopfAlgProperty k).prop_of_iso e.symm hunipotent)

end HopfIdeal

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The unipotent radical is the whole represented group exactly when the ambient finite-type
affine group is geometrically connected, smooth, and unipotent.

The equality is stated on defining Hopf ideals: the zero ideal cuts out the whole group. -/
@[simp] theorem unipotentRadicalDefiningIdeal_eq_bot_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal H = ⊥ ↔
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
        smoothUnipotentCommHopfAlgProperty k H := by
  constructor
  · intro h
    have hcandidate := isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H
    rw [h, HopfIdeal.isUnipotentRadicalCandidate_bot_iff] at hcandidate
    exact hcandidate
  · intro h
    apply le_antisymm
    · exact unipotentRadicalDefiningIdeal_le H ⊥
        ((HopfIdeal.isUnipotentRadicalCandidate_bot_iff H).2 h)
    · exact bot_le

/-- The unipotent radical of the unipotent radical is the whole unipotent radical. Equivalently,
the unipotent-radical construction is idempotent on defining ideals. -/
@[simp] theorem unipotentRadicalDefiningIdeal_unipotentRadical_eq_bot
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (unipotentRadical H) = ⊥ := by
  rw [unipotentRadicalDefiningIdeal_eq_bot_iff]
  exact ⟨geometricallyConnected_unipotentRadical H, smoothUnipotent_unipotentRadical H⟩

end FiniteTypeCommHopfAlgCat

end

end TauCeti
