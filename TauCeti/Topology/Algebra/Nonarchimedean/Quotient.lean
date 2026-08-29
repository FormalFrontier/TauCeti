/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
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

Deriving it does take one step, because `R ⧸ I` and `R ⧸ I.toAddSubgroup` are *definitionally*
equal but not syntactically so: Mathlib's `Ideal.topologicalRing_quotient` already builds the
topological-ring structure of `R ⧸ I` out of `QuotientAddGroup.instIsTopologicalAddGroup`, yet
instance search does not see through the two `HasQuotient` instances on its own. Naming
`I.toAddSubgroup` once is what lets the additive instance apply.

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

/-- A quotient of a nonarchimedean group is nonarchimedean: the image of an open subgroup
contained in the preimage of `U` is an open subgroup contained in `U`, because the quotient map
is open. -/
@[to_additive]
instance instNonarchimedeanGroup : NonarchimedeanGroup (G ⧸ N) where
  is_nonarchimedean U hU := by
    have hpre : ((↑) : G → G ⧸ N) ⁻¹' U ∈ 𝓝 (1 : G) := (continuous_mk.tendsto (1 : G)) hU
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ hpre
    refine ⟨⟨V.toSubgroup.map (QuotientGroup.mk' N), ?_⟩, ?_⟩
    · -- `OpenSubgroup` asks for openness of the bundled subgroup's `carrier`; naming it as the
      -- subgroup's coercion is what lets `Subgroup.coe_map` rewrite it to an image.
      change IsOpen ((V.toSubgroup.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      rw [Subgroup.coe_map]
      exact isOpenMap_coe _ V.isOpen
    · rintro _ ⟨x, hx, rfl⟩
      exact hV hx

end QuotientGroup

namespace Ideal.Quotient

variable {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R] (I : Ideal R)

/-- A quotient of a nonarchimedean ring by an ideal is nonarchimedean. This is the additive
group statement `QuotientAddGroup.instNonarchimedeanAddGroup`, applied to `I.toAddSubgroup` and
combined with the topological ring structure Mathlib already puts on `R ⧸ I`; the nonarchimedean
field is inherited unchanged. -/
instance instNonarchimedeanRing : NonarchimedeanRing (R ⧸ I) :=
  haveI : NonarchimedeanAddGroup (R ⧸ I) :=
    QuotientAddGroup.instNonarchimedeanAddGroup I.toAddSubgroup
  { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }

end Ideal.Quotient
