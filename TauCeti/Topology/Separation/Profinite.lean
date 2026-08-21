/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Basic

import Mathlib.Topology.Category.LightProfinite.Injective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuous extension from a closed subspace of a profinite space

Let `X` be a profinite space — compact, Hausdorff and totally disconnected — and let `Y` be a
discrete space. This file proves that a continuous map into `Y` defined on a *closed* subspace
`s ⊆ X` extends to a continuous map on all of `X`, as soon as one of `s` and `Y` is nonempty;
equivalently, that restriction `C(X, Y) → C(s, Y)` is surjective for every closed `s ⊆ X` when
`Y` is nonempty.

This is the zero-dimensional analogue of the Tietze extension theorem. Nothing can be averaged
here, since `Y` is a bare discrete space; instead the map has only finitely many fibres, because a
compact subset of a discrete space is finite, and those fibres are separated by a clopen
partition of `X`. Mathlib's `Profinite.exists_lift_of_finite_of_injective_of_surjective` packages
that separation as a lifting property — this is where total disconnectedness is used — and the
work below is the passage from a lifting square to an extension.

## Main results

* `TauCeti.exists_continuous_eqOn_range_subset_image`: for a nonempty closed `s`, a map
  continuous on `s` extends to a continuous map on `X` whose range is still contained in the
  image of `s`.
* `TauCeti.exists_continuous_eqOn`: the same for an arbitrary closed `s` and a nonempty target.
* `ContinuousMap.exists_restrict_eq_of_discrete` and
  `ContinuousMap.restrict_surjective_of_discrete`: the bundled form, for a closed set.
* `ContinuousMap.exists_extension_of_discrete`: the bundled form, for a closed embedding.

## Implementation notes

The statements come both for a bare function together with `ContinuousOn` and for bundled
`ContinuousMap`s. The unbundled form is the one continuous cochains are written in, and the bundled
form mirrors Mathlib's Tietze API; it lives in the root `ContinuousMap` namespace, so that dot
notation on a `C(s, Y)` reaches it, and carries an `_of_discrete` suffix to distinguish it from
Mathlib's `TietzeExtension` form of the same statement.

The nonemptiness hypotheses are not decoration. If `s` is empty and `Y` is empty while `X` is not,
there is a continuous map on `s` and none on `X`, so one of `s` and `Y` has to be assumed nonempty.

Total disconnectedness of `X` is not decoration either. On the compact Hausdorff space
`[0, 1] ⊆ ℝ` no map into a discrete space separates the two points of the closed subspace
`{0, 1}`, so a map taking two distinct values there has no continuous extension; this is spelled
out as an example in `TauCeti/Topology/LocallyConstant/Preconnected.lean`, where the
preconnectedness that drives it lives. Discreteness of `Y` is what makes the fibres clopen, and it
is likewise essential.
-/

public section

open Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Profinite

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [DiscreteTopology Y]
variable {s : Set X}

/-- **Continuous extension from a closed subspace of a profinite space.** A map continuous on a
nonempty closed subset `s` of a profinite space, with values in a discrete space, extends to a
continuous map on the whole space, and the extension can be chosen to take no value that is not
already taken on `s`.

That last clause is what lets a consumer keep the extension inside a subgroup, a submodule, or any
other set the original values lie in. -/
theorem exists_continuous_eqOn_range_subset_image {f : X → Y} (hs : IsClosed s)
    (hsne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ g : X → Y, Continuous g ∧ EqOn g f s ∧ range g ⊆ f '' s := by
  -- The image of `s` is finite: `s` is compact and `Y` is discrete.
  have : Finite (f '' s) :=
    ((hs.isCompact.image_of_continuousOn hf).finite_of_discrete).to_subtype
  have : Nonempty (f '' s) := (hsne.image f).to_subtype
  have : CompactSpace s := isCompact_iff_compactSpace.1 hs.isCompact
  -- Fill in the square whose top edge is the inclusion `s → X`, whose left edge is `f`
  -- corestricted to its image and whose bottom edge is the surjection `f '' s → PUnit`; the
  -- diagonal is the extension, and it lands in `f '' s` by construction.
  obtain ⟨g, hg, -, hgf⟩ :=
    Profinite.exists_lift_of_finite_of_injective_of_surjective (S := f '' s) (T := PUnit.{1})
      Subtype.val continuous_subtype_val Subtype.val_injective
      (fun _ => PUnit.unit) (fun _ => ⟨Classical.arbitrary _, rfl⟩)
      (fun x : s => ⟨f x, mem_image_of_mem f x.2⟩)
      ((continuousOn_iff_continuous_domRestrict.1 hf).subtype_mk _)
      (fun _ => PUnit.unit) continuous_const rfl
  exact ⟨fun x => (g x : Y), continuous_subtype_val.comp hg,
    fun x hx => congrArg Subtype.val (congrFun hgf ⟨x, hx⟩),
    by rintro _ ⟨x, rfl⟩; exact (g x).2⟩

/-- **Continuous extension from a closed subspace of a profinite space**, for an arbitrary closed
subset and a nonempty discrete target. -/
theorem exists_continuous_eqOn [Nonempty Y] {f : X → Y} (hs : IsClosed s)
    (hf : ContinuousOn f s) : ∃ g : X → Y, Continuous g ∧ EqOn g f s := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ => Classical.arbitrary Y, continuous_const, by simp⟩
  · obtain ⟨g, hg, hgf, -⟩ := exists_continuous_eqOn_range_subset_image hs hsne hf
    exact ⟨g, hg, hgf⟩

end Profinite

end TauCeti

/-! ### The bundled form

These live in the root `ContinuousMap` namespace, next to Mathlib's Tietze extension theorems and
within reach of dot notation on a `C(s, Y)`. -/

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [DiscreteTopology Y]
variable {s : Set X}

/-- **Continuous extension from a closed subspace of a profinite space**, bundled: a continuous map
on a closed subspace of a profinite space, with values in a nonempty discrete space, is the
restriction of a continuous map on the whole space.

This is the zero-dimensional counterpart of Mathlib's `ContinuousMap.exists_restrict_eq`, whose
`TietzeExtension` hypothesis on the target no discrete space with more than one point
satisfies. -/
theorem exists_restrict_eq_of_discrete [Nonempty Y] (hs : IsClosed s) (f : C(s, Y)) :
    ∃ g : C(X, Y), g.restrict s = f := by
  classical
  -- Spread `f` out to a map on `X` by an arbitrary value off `s`; only its continuity on `s`
  -- matters.
  have hF (x : s) :
      Function.extend Subtype.val f (fun _ => Classical.arbitrary Y) (x : X) = f x :=
    Subtype.val_injective.extend_apply _ _ x
  obtain ⟨g, hg, hgf⟩ :=
    TauCeti.exists_continuous_eqOn
      (f := Function.extend Subtype.val f fun _ => Classical.arbitrary Y)
      hs (continuousOn_iff_continuous_domRestrict.2 (f.continuous.congr fun x => (hF x).symm))
  refine ⟨⟨g, hg⟩, ?_⟩
  ext x
  simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk]
  exact (hgf x.2).trans (hF x)

/-- Restriction of continuous maps to a closed subspace of a profinite space is surjective, when
the target is discrete and nonempty. -/
theorem restrict_surjective_of_discrete [Nonempty Y] (hs : IsClosed s) :
    Function.Surjective fun g : C(X, Y) => g.restrict s :=
  fun f => exists_restrict_eq_of_discrete hs f

/-- **Continuous extension along a closed embedding into a profinite space.**

The statement and the deduction of this form from the closed-subset form follow Mathlib's
`ContinuousMap.exists_extension` in `Mathlib/Topology/TietzeExtension.lean`. -/
theorem exists_extension_of_discrete [Nonempty Y] {Z : Type*} [TopologicalSpace Z] {e : Z → X}
    (he : IsClosedEmbedding e) (f : C(Z, Y)) :
    ∃ g : C(X, Y), g.comp ⟨e, he.continuous⟩ = f := by
  -- `he.isEmbedding.toHomeomorph : Z ≃ₜ range e` identifies `Z` with the closed subspace
  -- `range e`, so `f` transports to a continuous map on `range e`.
  obtain ⟨g, hg⟩ := exists_restrict_eq_of_discrete he.isClosed_range
    (f.comp ⟨he.isEmbedding.toHomeomorph.symm, he.isEmbedding.toHomeomorph.symm.continuous⟩)
  refine ⟨g, ?_⟩
  ext x
  have hx := congr($(hg) ⟨e x, x, rfl⟩)
  simp only [restrict_apply, comp_apply, coe_mk,
    he.isEmbedding.toHomeomorph_symm_apply] at hx
  rw [comp_apply, coe_mk]
  exact hx

end ContinuousMap
