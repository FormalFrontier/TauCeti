/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Actions on an essentially small category are essentially small

An object of `CategoryTheory.Action V G` is an object of `V` together with an action of `G` on it,
so the objects of `Action V G` form a type one universe above `V` even when `V` itself is only
essentially small. This file records that the size does not really grow: if `V` is equivalent to a
small category, then so is `Action V G`.

The proof is a transport, not a construction. Mathlib's
`CategoryTheory.Action.functorCategoryEquivalence` identifies `Action V G` with the functor
category `SingleObj G ⥤ V`, whose source category has a *single* object; replacing `V` by
`CategoryTheory.SmallModel V` along `CategoryTheory.equivSmallModel` therefore leaves a functor
category which is literally small, one functor being no more data than its single value together
with the induced monoid homomorphism on endomorphisms. Smallness then transports back along
`CategoryTheory.essentiallySmall_congr`.

The bound `max v z` is the honest one, `z` being the universe in which `V` is essentially small:
the group contributes its own universe `v`, since a functor out of `SingleObj G` carries a map
defined on the morphisms `G`, and that map is data, while the single value of that functor is an
object of the small model, of size `z`.

That universe `z` is left independent of the morphism universe `w` of `V`. A category essentially
small at all is normally so at its own morphism universe — `FGModuleCat.{u} k` for `k : Type u`,
the instance used here, is — but nothing in the transport needs the two to agree.

This supplies the smallness hypothesis that
`TauCeti/CategoryTheory/GrothendieckGroup/Split.lean` asks of a category before its split
Grothendieck group is defined, in the case of `FDRep k G`, whose representation-ring
instantiation is `TauCeti/RepresentationTheory/RepresentationRing/Basic.lean`.

## Main statements

* `CategoryTheory.Action.essentiallySmall`: actions of a monoid on an essentially small category
  form an essentially small category.
-/

public section

universe u v w z

namespace CategoryTheory

namespace Action

/-- **Actions on an essentially small category are essentially small.** The equivalence with the
functor category out of `CategoryTheory.SingleObj G` turns an action into a single object of a
small model of `V` together with a monoid homomorphism from `G` into its endomorphisms, which is
data of size `max v z`. -/
instance essentiallySmall {V : Type u} [Category.{w} V] [EssentiallySmall.{z} V] (G : Type v)
    [Monoid G] : EssentiallySmall.{max v z} (Action V G) :=
  (essentiallySmall_congr ((Action.functorCategoryEquivalence V G).trans
    (Equivalence.congrRight (equivSmallModel V)))).2 inferInstance

end Action

end CategoryTheory
