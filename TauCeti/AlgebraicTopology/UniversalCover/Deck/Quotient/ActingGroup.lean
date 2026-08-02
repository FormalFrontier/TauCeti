/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Basic

/-!
# The acting group of a quotient covering map is its deck group

Let `f : E → X` be a quotient covering map for a group `G` acting on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`. Every group element then acts on `E` by a homeomorphism
over `X`, so translation gives a group homomorphism `G →* Deck f`.

This homomorphism is injective as soon as `E` is nonempty, because the action of a quotient
covering map is free. It is surjective when `E` is preconnected: a deck transformation agrees
at one point with some translation, and two deck transformations of a preconnected covering
that agree at a point agree everywhere (and if `E` is empty there is nothing to prove). So
for preconnected nonempty `E` the acting group *is* the deck group, `G ≃* Deck f`.

Neither hypothesis is needed to see that the deck action of a quotient covering map is
regular; that consequence is recorded in
`TauCeti/AlgebraicTopology/UniversalCover/Deck/Quotient/Covering.lean`, where it generalizes
the previous statement for the acting group `Deck f` itself.

## Main declarations

* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom`: translation by a group element, as a
  homomorphism from the acting group to the deck group.
* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom_injective`: it is injective on a nonempty
  total space.
* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom_surjective`: it is surjective on a
  preconnected total space.
* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom_bijective`: it is bijective on a preconnected
  nonempty total space.
* `TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`: for a preconnected nonempty total space,
  the acting group is isomorphic to the deck group.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 1 and Stage 4:
a cover presented as a quotient by a group action has that group as its deck group, which is
how the deck group of a concrete cover such as `Sⁿ → RPⁿ` is computed. The quotient covering
map API it consumes (`Mathlib/Topology/Covering/Quotient.lean`) is due to Junyan Xu.
Surjectivity rests on uniqueness of lifts through a covering map,
`IsCoveringMap.eq_of_comp_eq` in `Mathlib/Topology/Covering/Basic.lean`, due to Thomas
Browning after Hatcher, *Algebraic Topology*, Proposition 1.34; it is used here through the
Tau Ceti wrapper `TauCeti.Deck.eq_of_apply_eq`.
-/

public section

namespace TauCeti

namespace Deck

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
variable [Group G] [MulAction G E]

namespace IsQuotientCoveringMap

variable (hf : IsQuotientCoveringMap f G)
include hf

/-- Translation by a group element, as a homomorphism from the group of a quotient covering
map to the deck transformation group of that map. Each translation is a homeomorphism
because the action is continuous, and it lies over the base because the fibres of `f` are
the orbits. -/
def toDeckHom : G →* Deck f :=
  letI := hf.toContinuousConstSMul
  { toFun := fun g => ⟨Homeomorph.smul g, fun _ => hf.map_smul g⟩
    map_one' := Subtype.ext (Homeomorph.ext fun e => one_smul G e)
    map_mul' := fun g g' => Subtype.ext (Homeomorph.ext fun e => mul_smul g g' e) }

/-- On points, the deck transformation attached to a group element is translation by that
element. -/
@[simp]
lemma toDeckHom_apply (g : G) (e : E) : (toDeckHom hf g).1 e = g • e := by
  letI := hf.toContinuousConstSMul
  rw [toDeckHom, MonoidHom.coe_mk, OneHom.coe_mk, Homeomorph.smul_apply]

/-- On points, the inverse of the deck transformation attached to a group element is
translation by the inverse element. -/
@[simp]
lemma toDeckHom_symm_apply (g : G) (e : E) : (toDeckHom hf g).1.symm e = g⁻¹ • e := by
  rw [Homeomorph.symm_apply_eq, toDeckHom_apply, smul_inv_smul]

/-- Passing from a group element to a deck transformation is injective, because the action
of a quotient covering map is free. -/
lemma toDeckHom_injective [Nonempty E] : Function.Injective (toDeckHom hf) := by
  have := hf.isCancelSMul
  intro g g' hgg
  obtain ⟨e⟩ := ‹Nonempty E›
  have hsmul : g • e = g' • e := by
    simpa using congrArg (fun φ : Deck f => φ.1 e) hgg
  exact IsCancelSMul.right_cancel _ _ _ hsmul

/-- Every deck transformation of a quotient covering map with preconnected total space is
translation by a group element: it agrees with one such translation at a point, and deck
transformations of a preconnected covering are determined by one value. -/
lemma toDeckHom_surjective [PreconnectedSpace E] : Function.Surjective (toDeckHom hf) := by
  intro φ
  rcases isEmpty_or_nonempty E with hE | hne
  · exact ⟨1, Subtype.ext (Homeomorph.ext fun e => (hE.false e).elim)⟩
  · obtain ⟨e₀⟩ := hne
    obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.mp (Deck.map_proj φ e₀)
    exact ⟨g, Deck.eq_of_apply_eq hf.isCoveringMap _ _
      (by rw [toDeckHom_apply]; exact hg)⟩

/-- On a preconnected nonempty total space, passing from a group element to a deck
transformation is bijective. -/
lemma toDeckHom_bijective [PreconnectedSpace E] [Nonempty E] :
    Function.Bijective (toDeckHom hf) :=
  ⟨toDeckHom_injective hf, toDeckHom_surjective hf⟩

/-- **The acting group of a quotient covering map with preconnected nonempty total space is
its deck transformation group.** The isomorphism is translation. -/
noncomputable def deckMulEquiv [PreconnectedSpace E] [Nonempty E] : G ≃* Deck f :=
  MulEquiv.ofBijective (toDeckHom hf) (toDeckHom_bijective hf)

/-- On points, the isomorphism between the acting group and the deck group is translation. -/
@[simp]
lemma deckMulEquiv_apply [PreconnectedSpace E] [Nonempty E] (g : G) (e : E) :
    (deckMulEquiv hf g).1 e = g • e := by
  rw [deckMulEquiv, MulEquiv.ofBijective_apply, toDeckHom_apply]

/-- The inverse isomorphism returns the group element whose translation is the given deck
transformation. -/
@[simp]
lemma deckMulEquiv_symm_apply [PreconnectedSpace E] [Nonempty E] (φ : Deck f) (e : E) :
    (deckMulEquiv hf).symm φ • e = φ.1 e :=
  congrArg (fun ψ : Deck f => ψ.1 e) ((deckMulEquiv hf).apply_symm_apply φ)

end IsQuotientCoveringMap

end Deck

end TauCeti
