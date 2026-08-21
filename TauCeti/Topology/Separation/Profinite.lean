/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Profinite

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Continuous extension from a closed subspace of a profinite space

Let `X` be a profinite space — compact, Hausdorff and totally disconnected — and let `Y` be a
discrete space. This file proves that a continuous map into `Y` defined on a *closed* subspace of
`X` extends to a continuous map on all of `X`; equivalently, that restriction
`C(X, Y) → C(s, Y)` is surjective for every closed `s ⊆ X`.

This is the zero-dimensional analogue of the Tietze extension theorem. Nothing can be averaged
here, since `Y` is a bare discrete space; instead the map has only finitely many fibres, because a
compact subset of a discrete space is finite, and those fibres are separated by a clopen
partition of `X`. Mathlib's `exists_clopen_partition_of_clopen_cover` supplies that partition —
this is where total disconnectedness is used — and the work below is the passage from the
partition to a function.

## Main results

* `TauCeti.exists_continuous_eqOn_range_subset_image`: for a nonempty closed `s`, a map
  continuous on `s` extends to a continuous map on `X` whose range is still contained in the
  image of `s`.
* `TauCeti.exists_continuous_eqOn`: the same for an arbitrary closed `s` and a nonempty target.
* `TauCeti.ContinuousMap.exists_restrict_eq` and `TauCeti.ContinuousMap.restrict_surjective`: the
  bundled form, for a closed set.
* `TauCeti.ContinuousMap.exists_extension`: the bundled form, for a closed embedding.

## Implementation notes

The statements come both for a bare function together with `ContinuousOn` and for bundled
`ContinuousMap`s. The unbundled form is the one continuous cochains are written in, and the bundled
form mirrors Mathlib's Tietze API.

The nonemptiness hypotheses are not decoration. If `s` is empty and `Y` is empty while `X` is not,
there is a continuous map on `s` and none on `X`, so one of `s` and `Y` has to be assumed nonempty.

Total disconnectedness of `X` is not decoration either:
`TauCeti.not_exists_continuousOn_Icc_of_ne` records that on the compact Hausdorff space
`[0, 1] ⊆ ℝ` no map into a discrete space separates the two points of the closed subspace
`{0, 1}`, so a map taking two distinct values there has no continuous extension. Discreteness of
`Y` is what makes the fibres clopen, and it is likewise essential.
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
  classical
  -- The image of `s` is finite: `s` is compact and `Y` is discrete.
  have hTfin : (f '' s).Finite := (hs.isCompact.image_of_continuousOn hf).finite_of_discrete
  have : Finite (f '' s) := hTfin.to_subtype
  have : Nonempty (f '' s) := (hsne.image f).to_subtype
  -- The fibres of `f` over `s`, indexed by the image of `s`, are pairwise disjoint.
  have Z_disj : (univ : Set (f '' s)).PairwiseDisjoint fun i => s ∩ f ⁻¹' {(i : Y)} := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun x hxi hxj => hij (Subtype.ext ?_)
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hxi hxj
    rw [← hxi.2, hxj.2]
  -- Separate them by a clopen partition of `X`.
  obtain ⟨C, C_clopen, Z_sub_C, -, C_cover, C_disj⟩ :=
    exists_clopen_partition_of_clopen_cover (X := X) (I := (f '' s))
      (Z := fun i => s ∩ f ⁻¹' {(i : Y)}) (D := fun _ => univ)
      (fun _ => hf.preimage_isClosed_of_isClosed hs isClosed_singleton)
      (fun _ => isClopen_univ) (fun _ => subset_univ _) Z_disj
  have hmem (x : X) : ∃ i, x ∈ C i :=
    mem_iUnion.1 (C_cover (mem_iUnion.2 ⟨Classical.arbitrary _, mem_univ x⟩))
  choose i₀ hi₀ using hmem
  -- Each point lies in exactly one part, so `i₀` is determined by membership.
  have huniq {x : X} {i : f '' s} (hx : x ∈ C i) : i = i₀ x := by
    by_contra hne
    exact Set.disjoint_left.1 (C_disj (mem_univ i) (mem_univ (i₀ x)) hne) hx (hi₀ x)
  -- The extension sends `x` to the index of the part containing it.
  refine ⟨fun x => (i₀ x : Y), ?_, fun x hx => ?_, ?_⟩
  · rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_exists_open]
    exact fun x => ⟨C (i₀ x), (C_clopen _).isOpen, hi₀ x,
      fun _ hx' => congrArg Subtype.val (huniq hx').symm⟩
  · have hxZ : x ∈ s ∩ f ⁻¹' {((⟨f x, mem_image_of_mem f hx⟩ : f '' s) : Y)} :=
      ⟨hx, rfl⟩
    exact congrArg Subtype.val (huniq (Z_sub_C _ hxZ)).symm
  · rintro _ ⟨x, rfl⟩
    exact (i₀ x).2

/-- **Continuous extension from a closed subspace of a profinite space**, for an arbitrary closed
subset and a nonempty discrete target. -/
theorem exists_continuous_eqOn [Nonempty Y] {f : X → Y} (hs : IsClosed s)
    (hf : ContinuousOn f s) : ∃ g : X → Y, Continuous g ∧ EqOn g f s := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ => Classical.arbitrary Y, continuous_const, by simp⟩
  · obtain ⟨g, hg, hgf, -⟩ := exists_continuous_eqOn_range_subset_image hs hsne hf
    exact ⟨g, hg, hgf⟩

namespace ContinuousMap

/-- **Continuous extension from a closed subspace of a profinite space**, bundled: a continuous map
on a closed subspace of a profinite space, with values in a nonempty discrete space, is the
restriction of a continuous map on the whole space.

This is the zero-dimensional counterpart of Mathlib's `ContinuousMap.exists_restrict_eq`, whose
`TietzeExtension` hypothesis on the target no discrete space with more than one point
satisfies. -/
theorem exists_restrict_eq [Nonempty Y] (hs : IsClosed s) (f : C(s, Y)) :
    ∃ g : C(X, Y), g.restrict s = f := by
  classical
  -- Spread `f` out to a map on `X` by an arbitrary value off `s`; only its continuity on `s`
  -- matters.
  have hF (x : s) :
      Function.extend Subtype.val f (fun _ => Classical.arbitrary Y) (x : X) = f x :=
    Subtype.val_injective.extend_apply _ _ x
  obtain ⟨g, hg, hgf⟩ :=
    exists_continuous_eqOn (f := Function.extend Subtype.val f fun _ => Classical.arbitrary Y)
      hs (continuousOn_iff_continuous_domRestrict.2 (f.continuous.congr fun x => (hF x).symm))
  refine ⟨⟨g, hg⟩, ?_⟩
  ext x
  simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk]
  exact (hgf x.2).trans (hF x)

/-- Restriction of continuous maps to a closed subspace of a profinite space is surjective, when
the target is discrete and nonempty. -/
theorem restrict_surjective [Nonempty Y] (hs : IsClosed s) :
    Function.Surjective fun g : C(X, Y) => g.restrict s :=
  fun f => exists_restrict_eq hs f

/-- **Continuous extension along a closed embedding into a profinite space.**

The statement and the deduction of this form from the closed-subset form follow Mathlib's
`ContinuousMap.exists_extension` in `Mathlib/Topology/TietzeExtension.lean`. -/
theorem exists_extension [Nonempty Y] {Z : Type*} [TopologicalSpace Z] {e : Z → X}
    (he : IsClosedEmbedding e) (f : C(Z, Y)) :
    ∃ g : C(X, Y), g.comp ⟨e, he.continuous⟩ = f := by
  -- `e'` identifies `Z` with the closed subspace `range e`.
  let e' : Z ≃ₜ range e := he.isEmbedding.toHomeomorph
  obtain ⟨g, hg⟩ :=
    exists_restrict_eq he.isClosed_range (f.comp ⟨e'.symm, e'.symm.continuous⟩)
  exact ⟨g, by ext x; simpa [e'] using congr($(hg) ⟨e x, x, rfl⟩)⟩

end ContinuousMap

end Profinite

/-- **Total disconnectedness cannot be dropped** from `TauCeti.exists_continuous_eqOn`.

The subspace `[0, 1] ⊆ ℝ` is compact and Hausdorff, and `{0, 1}` is a closed subset of it on
which every map into a discrete space is continuous. Nevertheless a map into a discrete space
that is continuous on `[0, 1]` takes the same value at `0` and at `1`, so the map sending `0` to
`a` and `1` to a different `b` admits no continuous extension. -/
theorem not_exists_continuousOn_Icc_of_ne [DiscreteTopology Y] {a b : Y} (hab : a ≠ b) :
    ¬ ∃ g : ℝ → Y, ContinuousOn g (Icc 0 1) ∧ g 0 = a ∧ g 1 = b := by
  rintro ⟨g, hg, rfl, rfl⟩
  have h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ u in nhdsWithin t (Icc (0 : ℝ) 1), g u = g t :=
    fun t ht => by
      simpa [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure] using hg t ht
  exact hab (isPreconnected_Icc.apply_eq_of_eventually_eq h (by norm_num) (by norm_num))

end TauCeti
