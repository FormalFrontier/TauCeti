/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The closed and open arcs of the circle

Mathlib's `Circle.exp` parametrizes the circle by angles. This file reads a *closed arc*
`Circle.exp '' Set.Icc a b` off a subset of the circle and identifies its complement: a nonempty
closed preconnected proper subset of the circle is such an arc, and the complement of a closed arc
is the open arc `Circle.exp '' Set.Ioo b (a + 2 * π)` spanning the complementary angles.

Nothing here is specific to any curve theory; as with `TauCeti/Topology/Circle/Metric.lean`, these
are facts about the model circle, and the transport of them to a Jordan curve — where a compact
connected subset of the curve is thereby classified — is
`TauCeti/Topology/JordanCurve/Subcontinuum.lean`.

## The argument

The argument is the one for `ℝ`, run on a period of angles. Let `T ⊆ Circle` be closed,
preconnected and not the whole circle, and pick `z ∉ T`. Cutting the circle at `z` — that is,
reading it as `Circle.exp` on the period `[t, t + 2π]` for `Circle.exp t = z` — turns `T` into
`K = Circle.exp ⁻¹' T ∩ Icc t (t + 2 * π)`, a compact subset of `ℝ` avoiding *both* endpoints of
that period, so `K ⊆ Ioo t (t + 2 * π)` and `Circle.exp` is injective on `K`. A continuous injection
of a compact space into a Hausdorff one is a closed embedding (`Continuous.isClosedEmbedding`),
hence inducing, and an inducing map reflects preconnectedness
(`Topology.IsInducing.isPreconnected_image`), which carries preconnectedness of
`T = Circle.exp '' K` back to `K`; a compact connected subset of `ℝ` is then a closed interval
(`eq_Icc_of_connected_compact`).
Hence `T = Circle.exp '' Icc a b` with `b - a < 2 * π`, the degenerate case `a = b` being a point.

The complement is read off the same period, moved to `Ioc b (b + 2 * π)` so that the closed arc
becomes `Icc (a + 2 * π) (b + 2 * π)` and injectivity of `Circle.exp` applies to the difference.

## Main results

* `TauCeti.exists_eq_circleExp_image_Icc` — a nonempty closed preconnected proper subset of the
  circle is `Circle.exp '' Set.Icc a b` for a pair of angles less than a full turn apart.
* `TauCeti.compl_circleExp_image_Icc` — the complement of such a closed arc is the open arc
  `Circle.exp '' Set.Ioo b (a + 2 * π)`.
-/

public section

namespace TauCeti

open Real Set

/-! Both statements below are about a *closed arc* `Circle.exp '' Set.Icc a b` of angular width
`b - a` less than a full turn. Nothing ties the angles to a period, so a consumer may translate them
by any multiple of `2 * π`. -/

/-- Translating the angles by a full turn does not change a closed arc. -/
private lemma circleExp_image_Icc_add_period (a b : ℝ) :
    Circle.exp '' Icc (a + 2 * π) (b + 2 * π) = Circle.exp '' Icc a b := by
  rw [← image_add_const_Icc, ← image_comp]
  exact image_congr fun x _ => Circle.exp_add_two_pi x

/-- **Preconnectedness pulls back along a continuous injection on a compact set.** If `f` is
continuous and injective on a compact `K` and its image in a Hausdorff space is preconnected, then
`K` itself is preconnected. -/
private lemma isPreconnected_of_injOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {K : Set X} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hinj : InjOn f K) (hpre : IsPreconnected (f '' K)) : IsPreconnected K := by
  -- On the subtype the restriction is a closed embedding, so it reflects preconnectedness.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hginj : Function.Injective fun x : K => f (x : X) :=
    fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  have hgc : Continuous fun x : K => f (x : X) := continuousOn_iff_continuous_domRestrict.mp hf
  have hrange : range (fun x : K => f (x : X)) = f '' K := (image_eq_range f K).symm
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_univ,
    ← (hgc.isClosedEmbedding hginj).isInducing.isPreconnected_image, image_univ, hrange]
  exact hpre

/-- **A nonempty closed preconnected proper subset of the circle is a closed arc.** The two angles
are less than a full turn apart, so `Circle.exp` is injective on the interval carrying them, and the
degenerate case `a = b` is a single point.

Closedness is what forces the arc to be closed: the set is compact, `Circle` being compact, and a
compact connected subset of the line is a closed interval. -/
theorem exists_eq_circleExp_image_Icc {T : Set Circle} (hT : IsClosed T) (hpre : IsPreconnected T)
    (hne : T.Nonempty) (hTuniv : T ≠ univ) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < 2 * π ∧ T = Circle.exp '' Icc a b := by
  obtain ⟨z, hz⟩ : ∃ z, z ∉ T := by
    by_contra hcon
    exact hTuniv (eq_univ_of_forall (by simpa using hcon))
  set t : ℝ := z.val.arg
  have hexpt : Circle.exp t = z := Circle.exp_arg z
  set K : Set ℝ := Circle.exp ⁻¹' T ∩ Icc t (t + 2 * π) with hK
  have hKcompact : IsCompact K := isCompact_Icc.inter_left (hT.preimage Circle.exp.continuous)
  have himg : Circle.exp '' K = T := by
    rw [hK, image_preimage_inter, Circle.periodic_exp.image_Icc two_pi_pos,
      Circle.exp_surjective.range_eq, inter_univ]
  have hKsub : K ⊆ Ioo t (t + 2 * π) := by
    rintro x ⟨hxT, hxI⟩
    refine ⟨lt_of_le_of_ne hxI.1 fun hxt => hz ?_, lt_of_le_of_ne hxI.2 fun hxt => hz ?_⟩
    · rw [← hexpt, hxt]; exact hxT
    · rw [← hexpt, ← Circle.exp_add_two_pi, ← hxt]; exact hxT
  have hinj : InjOn Circle.exp K :=
    (Circle.exp_injOn_Ioc (a := t) (b := t + 2 * π) (by simp)).mono
      (hKsub.trans Ioo_subset_Ioc_self)
  have hKne : K.Nonempty := by
    rw [← image_nonempty (f := Circle.exp), himg]
    exact hne
  have hKpre : IsPreconnected K :=
    isPreconnected_of_injOn hKcompact Circle.exp.continuous.continuousOn hinj (himg ▸ hpre)
  have hKeq : K = Icc (sInf K) (sSup K) := eq_Icc_of_connected_compact ⟨hKne, hKpre⟩ hKcompact
  have hIsub : Icc (sInf K) (sSup K) ⊆ Ioo t (t + 2 * π) := hKeq ▸ hKsub
  have hle : sInf K ≤ sSup K := by
    obtain ⟨x, hx⟩ := hKne
    rw [hKeq] at hx
    exact hx.1.trans hx.2
  refine ⟨sInf K, sSup K, hle, ?_, ?_⟩
  · have h₁ := (hIsub (left_mem_Icc.mpr hle)).1
    have h₂ := (hIsub (right_mem_Icc.mpr hle)).2
    linarith
  · rw [← himg]
    exact congrArg _ hKeq

/-- **The complement of a closed arc of the circle is the complementary open arc.** The two arcs
share their endpoints' angles: `Circle.exp '' Set.Icc a b` is complemented by
`Circle.exp '' Set.Ioo b (a + 2 * π)`, which is nonempty exactly because the closed arc is not the
whole circle. Read left to right this removes a complement, so it is the normal form a consumer
should reach for: `simp [hab, hlt]` rewrites with it. -/
@[simp]
theorem compl_circleExp_image_Icc {a b : ℝ} (hab : a ≤ b) (hlt : b - a < 2 * π) :
    (Circle.exp '' Icc a b)ᶜ = Circle.exp '' Ioo b (a + 2 * π) := by
  have hbsub : Icc (a + 2 * π) (b + 2 * π) ⊆ Ioc b (b + 2 * π) := fun x hx =>
    ⟨by linarith [hx.1], hx.2⟩
  have hdiff : Ioc b (b + 2 * π) \ Icc (a + 2 * π) (b + 2 * π) = Ioo b (a + 2 * π) := by
    ext x
    simp only [mem_sdiff, mem_Ioc, mem_Icc, mem_Ioo, not_and, not_le]
    refine ⟨fun h => ⟨h.1.1, ?_⟩, fun h => ⟨⟨h.1, by linarith⟩, fun hx => by linarith⟩⟩
    by_contra hcon
    exact absurd h.1.2 (not_le.mpr (h.2 (not_lt.mp hcon)))
  have himage : Circle.exp '' (Ioc b (b + 2 * π) \ Icc (a + 2 * π) (b + 2 * π)) =
      Circle.exp '' Ioc b (b + 2 * π) \ Circle.exp '' Icc (a + 2 * π) (b + 2 * π) :=
    (Circle.exp_injOn_Ioc (a := b) (b := b + 2 * π) (by simp)).image_sdiff_subset hbsub
  rw [← circleExp_image_Icc_add_period a b, compl_eq_univ_sdiff,
    ← Circle.exp_surjective.range_eq, ← Circle.periodic_exp.image_Ioc two_pi_pos b,
    ← himage, hdiff]

end TauCeti
