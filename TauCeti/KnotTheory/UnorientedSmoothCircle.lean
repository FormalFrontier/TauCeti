/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothCircle

/-!
# Unoriented smooth circle presentations

An embedding of the standard circle carries an orientation through its parametrization.  Forgetting
that orientation identifies a presentation with the presentation obtained by precomposing with
complex conjugation.  This file packages that identification as a quotient, rather than introducing
a second kind of embedded-circle structure.

The relation records the two canonical choices of orientation supplied by `SmoothCircle`: two
representatives are related when they are equal or when one is the reverse of the other.  Since
`reverse` is an involution, this is an equivalence relation.  The quotient therefore has a small,
canonical API: a projection from
oriented presentations, an exact equality criterion for quotient classes, and the image of an
unoriented presentation in the ambient manifold.  The image is well defined because reversing a
circle parametrization does not change its range.

This is the orientation-forgetting step in Layer 4 of the geometric-topology roadmap.  Framing,
multi-component links, and the comparison with diagram presentations are separate constructions.

## Main definitions

* `TauCeti.UnorientedSmoothCircleEmbedding`: smooth circle embeddings modulo orientation reversal.
* `TauCeti.SmoothCircleEmbedding.forgetOrientation`: the quotient projection.
* `TauCeti.UnorientedSmoothCircleEmbedding.range`: the underlying embedded circle as a set.

## Main results

* `SmoothCircleEmbedding.forgetOrientation_eq_iff`: the quotient equality criterion.
* `SmoothCircleEmbedding.forgetOrientation_reverse`: reversing orientation does not change the
  unoriented presentation.
* `UnorientedSmoothCircleEmbedding.range_forgetOrientation`: the quotient image is the range of
  any oriented representative.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace SmoothCircleEmbedding

/-- Two oriented smooth circle presentations represent the same unoriented presentation when they
are equal or differ by the orientation-reversing circle reparametrization. -/
def UnorientedRel (f g : SmoothCircleEmbedding I M) : Prop := f = g ∨ f = g.reverse

private theorem unorientedRel_refl (f : SmoothCircleEmbedding I M) : UnorientedRel f f :=
  Or.inl rfl

private theorem unorientedRel_symm {f g : SmoothCircleEmbedding I M}
    (h : UnorientedRel f g) : UnorientedRel g f := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (by rw [h, reverse_reverse])

private theorem unorientedRel_trans {f g h : SmoothCircleEmbedding I M}
    (hfg : UnorientedRel f g) (hgh : UnorientedRel g h) : UnorientedRel f h := by
  rcases hfg with hfg | hfg
  · rcases hgh with hgh | hgh
    · exact Or.inl (hfg.trans hgh)
    · exact Or.inr (hfg.trans hgh)
  · rcases hgh with hgh | hgh
    · exact Or.inr (hfg.trans (congrArg reverse hgh))
    · exact Or.inl (hfg.trans (by rw [hgh, reverse_reverse]))

/-- The setoid of oriented smooth circle presentations modulo reversal. -/
def unorientedSetoid : Setoid (SmoothCircleEmbedding I M) where
  r := UnorientedRel
  iseqv := ⟨unorientedRel_refl, unorientedRel_symm, unorientedRel_trans⟩

end SmoothCircleEmbedding

/-- A smooth circle presentation with its orientation forgotten. -/
abbrev UnorientedSmoothCircleEmbedding
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  Quotient (SmoothCircleEmbedding.unorientedSetoid (I := I) (M := M))

namespace SmoothCircleEmbedding

variable {f g : SmoothCircleEmbedding I M}

/-- The quotient map forgetting the orientation of a smooth circle presentation. -/
def forgetOrientation (f : SmoothCircleEmbedding I M) :
    UnorientedSmoothCircleEmbedding I M :=
  Quotient.mk (unorientedSetoid (I := I) (M := M)) f

/-- Two oriented presentations have the same unoriented class exactly when they agree up to
orientation reversal. -/
theorem forgetOrientation_eq_iff :
    forgetOrientation f = forgetOrientation g ↔ UnorientedRel f g := by
  exact Quotient.eq

/-- Reversing the orientation does not change the unoriented presentation. -/
@[simp]
theorem forgetOrientation_reverse (f : SmoothCircleEmbedding I M) :
    forgetOrientation f.reverse = forgetOrientation f := by
  apply forgetOrientation_eq_iff.2
  exact Or.inr rfl

end SmoothCircleEmbedding

namespace UnorientedSmoothCircleEmbedding

/-- The embedded circle underlying an unoriented presentation. -/
def range (u : UnorientedSmoothCircleEmbedding I M) : Set M :=
  Quotient.lift (fun f : SmoothCircleEmbedding I M => Set.range f)
    (by
      intro f g h
      change SmoothCircleEmbedding.UnorientedRel f g at h
      rcases h with rfl | h
      · rfl
      · rw [h, SmoothCircleEmbedding.range_reverse]) u

/-- The underlying set of an unoriented presentation is the range of any representative. -/
@[simp]
theorem range_forgetOrientation (f : SmoothCircleEmbedding I M) :
    range (SmoothCircleEmbedding.forgetOrientation f) = Set.range f :=
  by simp [range, SmoothCircleEmbedding.forgetOrientation]

/-- Reversing a representative does not change the underlying unoriented embedded circle. -/
@[simp]
theorem range_forgetOrientation_reverse (f : SmoothCircleEmbedding I M) :
    range (SmoothCircleEmbedding.forgetOrientation f.reverse) = Set.range f := by
  rw [range_forgetOrientation, SmoothCircleEmbedding.range_reverse]

/-- To prove a property of an unoriented presentation, it suffices to prove it for every oriented
representative. -/
@[elab_as_elim]
protected theorem inductionOn {motive : UnorientedSmoothCircleEmbedding I M → Prop}
    (u : UnorientedSmoothCircleEmbedding I M)
    (h : ∀ f : SmoothCircleEmbedding I M, motive (SmoothCircleEmbedding.forgetOrientation f)) :
    motive u :=
  Quotient.inductionOn u h

end UnorientedSmoothCircleEmbedding

end TauCeti
