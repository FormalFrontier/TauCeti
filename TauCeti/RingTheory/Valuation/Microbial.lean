/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Group.ConvexSubgroup

/-!
# Microbial valuations

Wedhorn's Definition 5.46(v) calls a valuation *microbial* when some convex subgroup of its value
group has height-one quotient. This module records that condition.

What consumes it is the coarsening `Valuation.coarsenByUnits` of
`TauCeti/RingTheory/Valuation/Coarsen.lean`, which is the vertical generization `v/H` of Wedhorn's
Remark 4.12(1): the subgroup a microbial valuation supplies is exactly the one to coarsen by. That
direction of use is downstream, so this module does not import the coarsening.

## Height one, without a height theory

"Height one" is not formalised as a number. A linearly ordered commutative group has height at
most one exactly when its only convex subgroups are `⊥` and `⊤`, and that is
`TauCeti.ConvexSubgroup.mulArchimedean_iff_forall_eq_bot_or_eq_top`; height *exactly* one adds
that the group is not trivial. So `MulArchimedean` together with `Nontrivial` is the height-one
condition, and no rank or height development is needed.

## Main definitions

* `Valuation.IsMicrobial` : Wedhorn 5.46(v), a condition on the valuation's own value group.

## Main results

* `Valuation.isMicrobial_iff` : the characteristic lemma, restating the predicate as its defining
  existential so that consumers need not unfold it.
* `Valuation.isMicrobial_of_mulArchimedean` and `Valuation.not_isMicrobial_of_subsingleton` : the
  predicate holds of every rank-one valuation and fails of every trivial one.

## Implementation notes

Declared in the root `Valuation` namespace, not in `TauCeti.Valuation`, matching
`TauCeti/RingTheory/Valuation/Coarsen.lean`. `Valuation` is a Mathlib type, so nesting it under
`TauCeti` shadows it and dot-notation on a valuation stops elaborating; the repository's
dot-notation guard rejects that.

The condition is stated over `(ValueGroup₀ (.ofClass v))ˣ`, the units of the value monoid `v`
actually attains, which is Wedhorn's `Γ_v`. It is deliberately *not* stated over the ambient
`Γ₀ˣ`: that reading depends only on the codomain and not on `v`, so a trivial valuation into a
large enough `Γ₀` would satisfy it while its own value group is trivial, hence not of height one.

Spelling `Γ_v` as `(ValueGroup₀ (.ofClass v))ˣ` rather than as `valueGroup (.ofClass v)` is what
makes the witness directly usable. The two are identified by
`OrderMonoidIso.unitsWithZero`, but only the former is a `LinearOrderedCommGroupWithZero`'s unit
group, so only it carries the ordered-monoid instances that `ConvexSubgroup`'s quotient order
needs; and it is exactly what `Valuation.restrict` takes values in, so the subgroup the
definition supplies is the one the coarsening consumes, with no transport in between.

The *characteristic* subgroup `cΓ_v` of Wedhorn 4.13 is a different notion and lives in
`TauCeti/RingTheory/Valuation/CharacteristicGroup.lean`, which says so explicitly.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 5.46(v) and
  Remark 4.12(1).
-/

public section

namespace Valuation

open TauCeti MonoidWithZeroHom

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Definition 5.46(v)**: `v` is *microbial* when some convex subgroup `H` of its value
group `Γ_v` has height-one quotient — nontrivial, and archimedean in the sense that `⊥` and `⊤`
are its only convex subgroups.

Stated over `(ValueGroup₀ (.ofClass v))ˣ`, the values `v` actually attains, and not over the
ambient `Γ₀ˣ`: the latter does not mention `v`, so a trivial valuation into a large enough `Γ₀`
would satisfy it although its own value group is trivial, hence not of height one. -/
def IsMicrobial (v : Valuation R Γ₀) : Prop :=
  ∃ H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ,
    Nontrivial ((ValueGroup₀ (.ofClass v))ˣ ⧸ H.toSubgroup) ∧
      MulArchimedean ((ValueGroup₀ (.ofClass v))ˣ ⧸ H.toSubgroup)

/-- The `Iff.rfl` proof of `isMicrobial_iff`, kept private because it unfolds the sealed
`IsMicrobial`, which an exported theorem may not do. -/
private theorem isMicrobial_iff_aux {v : Valuation R Γ₀} :
    v.IsMicrobial ↔ ∃ H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ,
      Nontrivial ((ValueGroup₀ (.ofClass v))ˣ ⧸ H.toSubgroup) ∧
        MulArchimedean ((ValueGroup₀ (.ofClass v))ˣ ⧸ H.toSubgroup) := Iff.rfl

/-- **The characteristic lemma for `IsMicrobial`**: it is exactly its defining existential, so a
consumer can obtain the convex subgroup from it, or supply one to build it, without unfolding the
predicate. Since `IsMicrobial` is sealed, this is the whole of its introduction and elimination
interface outside this module.

Deliberately not `@[simp]`: the right-hand side is the strictly larger term, so rewriting in this
direction takes a named predicate out of normal form rather than into it. -/
theorem isMicrobial_iff {v : Valuation R Γ₀} :
    v.IsMicrobial ↔ ∃ H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ,
      Nontrivial ((ValueGroup₀ (.ofClass v))ˣ ⧸ H.toSubgroup) ∧
        MulArchimedean ((ValueGroup₀ (.ofClass v))ˣ ⧸ H.toSubgroup) := isMicrobial_iff_aux

/-- **A valuation whose value group is trivial is not microbial.** The definition is therefore not
vacuously satisfied: it genuinely constrains `v`.

This is the degenerate case that distinguishes `IsMicrobial` from the condition read on the
ambient `Γ₀ˣ`, which a trivial valuation into a large enough `Γ₀` would satisfy. -/
theorem not_isMicrobial_of_subsingleton {v : Valuation R Γ₀}
    (h : Subsingleton (ValueGroup₀ (.ofClass v))ˣ) : ¬ v.IsMicrobial := by
  intro hv
  obtain ⟨H, hnt, -⟩ := isMicrobial_iff.mp hv
  exact (not_nontrivial_iff_subsingleton.mpr
    (Function.Surjective.subsingleton QuotientGroup.mk_surjective)) hnt

/-- **A rank-one valuation is microbial**, witnessed by `H = ⊥`. "Rank one" is `Γ_v` nontrivial and
archimedean, exactly as in the module docstring, so the quotient `Γ_v ⧸ ⊥ ≃ Γ_v` already has
height one and no proper convex subgroup is needed.

With `not_isMicrobial_of_subsingleton` this pins the predicate from both sides: it holds of every
rank-one valuation and fails of every trivial one. -/
theorem isMicrobial_of_mulArchimedean {v : Valuation R Γ₀}
    [Nontrivial (ValueGroup₀ (.ofClass v))ˣ] [MulArchimedean (ValueGroup₀ (.ofClass v))ˣ] :
    v.IsMicrobial :=
  isMicrobial_iff.mpr
    ⟨⊥, Function.Surjective.nontrivial ConvexSubgroup.quotientBotOrderIso.surjective,
      ConvexSubgroup.quotientBotOrderIso.symm.mulArchimedean⟩

end Valuation
