/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Transitive `G`-sets

A `G`-set, in the categorical sense of an object of `Action (Type u) G`, is *transitive* when it
is nonempty and `G` acts transitively on its underlying type. This file records that condition as
an `ObjectProperty`, shows it is closed under isomorphisms, and names the resulting full
subcategory.

The action referred to is the one `Action.instMulAction` puts on the underlying type `ToType A`,
so both conjuncts are read through that instance rather than through `A.ρ`.
Following Mathlib's convention, `MulAction.IsPretransitive` allows the empty set, so nonemptiness
is a genuine extra condition and is imposed separately.

The property is named `TauCeti.isTransitiveAction` rather than being placed in a
`TauCeti.Action` namespace: `Action` is a Mathlib type, and `scripts/lint-dot-notation.py`
rejects a Mathlib type's namespace nested inside `namespace TauCeti`, because dot notation on
that type then fails to elaborate.

## Main declarations

* `TauCeti.isTransitiveAction`: the property of being a transitive `G`-set.
* `TauCeti.isTransitiveAction_iff`: its two conjuncts.
* `TauCeti.smul_eq_ρ_apply`: the scalar multiplication both conjuncts refer to is evaluation of
  the representation.
* `TauCeti.TransitiveAction`: transitive `G`-sets as a full subcategory of all `G`-sets, with
  `TauCeti.TransitiveAction.mk`, `TauCeti.TransitiveAction.forget`,
  `TauCeti.TransitiveAction.isTransitiveAction` and
  `TauCeti.TransitiveAction.fullyFaithfulForget`.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable (G : Type v) [Monoid G]

/-- A `G`-set is *transitive* when `G` acts pretransitively on it and it is nonempty. -/
def isTransitiveAction : ObjectProperty (Action (Type u) G) :=
  fun A => MulAction.IsPretransitive G (ToType A) ∧ Nonempty (ToType A)

variable {G}

/-- The scalar multiplication that `Action.instMulAction` puts on the underlying type of a `G`-set
is evaluation of its representation. -/
theorem smul_eq_ρ_apply (A : Action (Type u) G) (g : G) (x : ToType A) : g • x = A.ρ g x :=
  rfl

variable (G)

/-- Transitivity of a `G`-set is preserved by isomorphisms of `G`-sets: an isomorphism is an
equivariant bijection on underlying types. -/
instance : (isTransitiveAction G).IsClosedUnderIsomorphisms where
  of_iso {A B} e h :=
    ⟨h.1.of_surjective_map
        (f := (⟨ConcreteCategory.hom e.hom.hom, fun g x => by
          simp only [id_eq, smul_eq_ρ_apply, ← types_comp_apply, e.hom.comm]⟩ :
            MulActionHom (id : G → G) (ToType A) (ToType B)))
        ((Action.forget _ G).mapIso e).toEquiv.surjective,
      ⟨ConcreteCategory.hom e.hom.hom h.2.some⟩⟩

variable {G}

/-- Membership in the transitivity property of `G`-sets. -/
@[simp]
theorem isTransitiveAction_iff (A : Action (Type u) G) :
    isTransitiveAction G A ↔ MulAction.IsPretransitive G (ToType A) ∧ Nonempty (ToType A) :=
  Iff.rfl

variable (G)

/-- Transitive `G`-sets, as a full subcategory of all `G`-sets. -/
abbrev TransitiveAction : Type _ :=
  (isTransitiveAction G).FullSubcategory

namespace TransitiveAction

/-- The fully faithful inclusion of transitive `G`-sets into all `G`-sets. -/
abbrev forget : TransitiveAction G ⥤ Action (Type u) G :=
  ObjectProperty.ι _

/-- The inclusion of transitive `G`-sets into all `G`-sets is fully faithful. -/
def fullyFaithfulForget : (forget G).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {G}

/-- Construct a transitive `G`-set from a `G`-set and a proof of transitivity. -/
def mk (A : Action (Type u) G) (hA : isTransitiveAction G A) : TransitiveAction G :=
  ⟨A, hA⟩

/-- The underlying `G`-set of a transitive `G`-set is transitive. -/
theorem isTransitiveAction (A : TransitiveAction G) : TauCeti.isTransitiveAction G A.obj :=
  A.property

end TransitiveAction

end TauCeti
