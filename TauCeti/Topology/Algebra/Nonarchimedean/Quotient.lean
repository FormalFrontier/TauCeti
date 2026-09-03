/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# A quotient of a nonarchimedean group is nonarchimedean

`NonarchimedeanGroup G` asks that every neighbourhood of `1` contain an *open subgroup*. That
property passes to `G ⧸ N`, and the proof is the one-line reason it should: the quotient map is
open, so it carries an open subgroup at `1` to one downstairs.

This is a statement about topological groups, not about rings: nothing in it uses
multiplication on a ring or the ideal structure of `I`. It is therefore proved at the group
level and transported with `@[to_additive]`, and the ring statement is derived from the additive
one rather than reproved — the same way Mathlib derives `NonarchimedeanRing (R × S)` from the
additive group instance on a product.

Both instances factor through one transport lemma,
`NonarchimedeanGroup.nonarchimedean_of_isOpenMap` in
`TauCeti.Topology.Algebra.Nonarchimedean.Basic`: the property passes along *any* open homomorphism
continuous at the identity, which is all the quotient map is ever used for here. The group
instance applies it to `QuotientGroup.mk'`, and the ring instance applies
its additive form to `Ideal.Quotient.mk` through `QuotientRing.isOpenMap_coe` — so no
identification of `R ⧸ I` with a quotient by `I.toAddSubgroup` is involved.

The consumer is the universal property of a rational localisation
(`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`), which
requires `[NonarchimedeanRing B]` on its target. Wedhorn's Example 6.38 presents a rational
localisation as a quotient `C ⧸ a` of a ring of restricted power series, so applying that
universal property to `C ⧸ a` needs exactly the ring instance below.

## Main results

* `QuotientGroup.instNonarchimedeanGroup`, and its additive form
  `QuotientAddGroup.instNonarchimedeanAddGroup`: `G ⧸ N` is nonarchimedean when `G` is.
* `Ideal.Quotient.instNonarchimedeanRing`: `R ⧸ I` is nonarchimedean when `R` is.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.38.
-/

public section

open Topology

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G] (N : Subgroup G)
  [N.Normal]

/-- A quotient of a nonarchimedean group is nonarchimedean: the quotient map is continuous and
open, so this is `NonarchimedeanGroup.nonarchimedean_of_isOpenMap`. -/
@[to_additive /-- A quotient of a nonarchimedean additive group is nonarchimedean. -/]
instance instNonarchimedeanGroup : NonarchimedeanGroup (G ⧸ N) :=
  .nonarchimedean_of_isOpenMap (QuotientGroup.mk' N) continuous_mk.continuousAt isOpenMap_coe

end QuotientGroup

namespace Ideal.Quotient

variable {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R] (I : Ideal R)

/-- A quotient of a nonarchimedean ring by an ideal is nonarchimedean. The quotient map is
continuous and open, so the additive transport lemma applies directly; the nonarchimedean field is
then inherited, as for `NonarchimedeanRing (R × S)` in Mathlib. -/
instance instNonarchimedeanRing : NonarchimedeanRing (R ⧸ I) :=
  haveI : NonarchimedeanAddGroup (R ⧸ I) :=
    .nonarchimedean_of_isOpenMap (Ideal.Quotient.mk I).toAddMonoidHom
      continuous_quot_mk.continuousAt (QuotientRing.isOpenMap_coe I)
  { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }

end Ideal.Quotient
