/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic

/-!
# A proper subcontinuum of a Jordan curve is an arc

`TauCeti/Topology/JordanCurve/Separation.lean` cuts a Jordan curve at one or two *given* points.
This file describes the pieces from the other side: it classifies the compact connected subsets of
a Jordan curve. Every one of them other than the curve itself is a point or an **arc** — the range
of an injective path — and its complement in the curve is again path connected. In particular a
compact connected subset that is *nowhere dense in the curve* is a single point, which is the form
in which the classification is spent.

## The argument

Everything is transported from the model curve `Circle`, so the work is on the circle, and the
transport is the parametrization `TauCeti.jordanParam` of `TauCeti/Topology/JordanCurve/Basic.lean`.

On the circle the argument is the one for `ℝ`. Let `T ⊆ Circle` be closed, preconnected and not the
whole circle, and pick `z ∉ T`. Cutting the circle at `z` — that is, reading it as `Circle.exp` on
the period `[t, t + 2π]` for `Circle.exp t = z` — turns `T` into
`K = Circle.exp ⁻¹' T ∩ Icc t (t + 2 * π)`, a compact subset of `ℝ` avoiding *both* endpoints of
that period, so `K ⊆ Ioo t (t + 2 * π)` and `Circle.exp` is injective on `K`. A continuous injection
of a compact space into a Hausdorff one is a closed map, so
`IsPreconnected.preimage_of_isClosedMap` carries preconnectedness of `T = Circle.exp '' K` back to
`K`, and a compact connected subset of `ℝ` is a closed interval
(`eq_Icc_of_connected_compact`). Hence `T = Circle.exp '' Icc a b` with `b - a < 2 * π`, the two
degenerate cases `a = b` and `T = ∅` being the point and the empty set.

The complement is then read off the same period, moved to `Ioc b (b + 2 * π)` so that the closed
arc becomes `Icc (a + 2 * π) (b + 2 * π)` and injectivity of `Circle.exp` applies to the difference:
`(Circle.exp '' Icc a b)ᶜ = Circle.exp '' Ioo b (a + 2 * π)`, an *open* arc, path connected as the
continuous image of an interval.

Nowhere density is the same computation once more. If `a < b` then the midpoint `(a + b) / 2` names
a point of the curve that lies outside the compact set `Circle.exp '' Icc b (a + 2 * π)`, which
contains the whole complement of `T`; so that point of `T` is not adherent to the complement, and
`T` is not nowhere dense. Contrapositively, a nowhere dense compact connected subset has `a = b`
and is a point.

## Why this is a layer-L5 prerequisite

Layer **L5** of the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`) is
Carathéodory's boundary correspondence for a Jordan domain, and its open direction is the assertion
that the boundary cluster sets of a Riemann map are singletons. Those cluster sets are already known
to be *continua contained in the image boundary*
(`TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded` together with
`TauCeti.clusterSetOn_subset_frontier_image`), so for a Jordan domain each of them is a compact
connected subset of a Jordan curve, and the results here say what such a set can be: a point, an
arc, or the whole curve. The milestone is thereby reduced to excluding the last two, and
`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` performs that exclusion from a
hypothesis about the curve alone — that the cluster set is nowhere dense in it. That reduction is
carried out on the conformal side in `TauCeti/Analysis/Complex/Conformal/ClusterSet.lean`.

## Generality

The statements are for a subset of an arbitrary topological space, as in
`TauCeti/Topology/JordanCurve/Separation.lean`; the subcontinuum is asked to be *compact* rather
than closed, which is what transports along the parametrization without a separation axiom. Only
`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` needs the ambient space to be
Hausdorff, because it speaks of a closure taken in that space.

## Main results

* `TauCeti.exists_eq_circleExp_image_Icc` — a nonempty closed preconnected proper subset of the
  circle is `Circle.exp '' Set.Icc a b` for a pair of angles less than a full turn apart.
* `TauCeti.compl_circleExp_image_Icc` — the complement of such a closed arc is the open arc
  `Circle.exp '' Set.Ioo b (a + 2 * π)`.
* `TauCeti.IsJordanCurve.subsingleton_or_exists_injective_path` — **a proper subcontinuum of a
  Jordan curve is a point or an arc**: it is either a subsingleton or the range of an injective
  path.
* `TauCeti.IsJordanCurve.isPathConnected_sdiff` — the complement of a proper subcontinuum in the
  curve is path connected; for a singleton this is
  `TauCeti.IsJordanCurve.isPathConnected_sdiff_singleton`.
* `TauCeti.IsJordanCurve.exists_notMem_closure_sdiff` — a proper subcontinuum with more than one
  point is not nowhere dense: one of its points is not adherent to the rest of the curve.
* `TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` — the contrapositive, and the form
  the boundary correspondence consumes: a compact connected subset of a Jordan curve every point of
  which is adherent to the complement is a single point.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Real Set Topology

variable {X : Type*} [TopologicalSpace X] {C S : Set X}

/-! ## The model curve

Both circle statements below are about a *closed arc* `Circle.exp '' Set.Icc a b` of angular width
`b - a` less than a full turn. Nothing ties the angles to a period, so a consumer may translate them
by any multiple of `2 * π`. -/

/-- A full period of angles covers the circle. -/
private lemma circleExp_image_Icc_add_two_pi (a : ℝ) : Circle.exp '' Icc a (a + 2 * π) = univ := by
  rw [Circle.periodic_exp.image_Icc two_pi_pos]
  exact Circle.exp_surjective.range_eq

/-- A full period of angles, taken half open, covers the circle. -/
private lemma circleExp_image_Ioc_add_two_pi (a : ℝ) : Circle.exp '' Ioc a (a + 2 * π) = univ := by
  rw [Circle.periodic_exp.image_Ioc two_pi_pos]
  exact Circle.exp_surjective.range_eq

/-- `Circle.exp` is injective on a full period of angles taken half open. -/
private lemma circleExp_injOn_Ioc (a : ℝ) : InjOn Circle.exp (Ioc a (a + 2 * π)) :=
  Circle.exp_injOn_Ioc (by ring_nf; exact le_rfl)

/-- Translating the angles by a full turn does not change a closed arc. -/
private lemma circleExp_image_Icc_add_period (a b : ℝ) :
    Circle.exp '' Icc (a + 2 * π) (b + 2 * π) = Circle.exp '' Icc a b := by
  rw [← image_add_const_Icc, ← image_comp]
  exact image_congr fun x _ => Circle.exp_add_two_pi x

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
    rw [hK, image_preimage_inter, circleExp_image_Icc_add_two_pi, inter_univ]
  have hKsub : K ⊆ Ioo t (t + 2 * π) := by
    rintro x ⟨hxT, hxI⟩
    refine ⟨lt_of_le_of_ne hxI.1 fun hxt => hz ?_, lt_of_le_of_ne hxI.2 fun hxt => hz ?_⟩
    · rw [← hexpt, hxt]; exact hxT
    · rw [← hexpt, ← Circle.exp_add_two_pi, ← hxt]; exact hxT
  have hinj : InjOn Circle.exp K := (circleExp_injOn_Ioc t).mono (hKsub.trans Ioo_subset_Ioc_self)
  have hKne : K.Nonempty := by
    rw [← image_nonempty (f := Circle.exp), himg]
    exact hne
  have hKpre : IsPreconnected K := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    have hginj : Function.Injective fun x : K => Circle.exp (x : ℝ) :=
      fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
    have hgc : Continuous fun x : K => Circle.exp (x : ℝ) :=
      Circle.exp.continuous.comp continuous_subtype_val
    have hrange : range (fun x : K => Circle.exp (x : ℝ)) = T := by
      rw [← himg]
      refine subset_antisymm ?_ ?_
      · rintro _ ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have hpre' := hpre.preimage_of_isClosedMap hginj hgc.isClosedMap hrange.ge
    rw [show (fun x : K => Circle.exp (x : ℝ)) ⁻¹' T = univ from
      eq_univ_of_forall fun x => x.2.1] at hpre'
    exact isPreconnected_iff_preconnectedSpace.mpr ⟨hpre'⟩
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
whole circle. -/
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
    (circleExp_injOn_Ioc b).image_sdiff_subset hbsub
  rw [← circleExp_image_Icc_add_period a b, compl_eq_univ_sdiff,
    ← circleExp_image_Ioc_add_two_pi b, ← himage, hdiff]

/-! ## Subcontinua of a Jordan curve

Each statement below transports its circle counterpart along the parametrization
`TauCeti.jordanParam e`, which is a continuous injection with range the curve. The two private
lemmas carry the closed arc and its complement across it once and for all; the theorems then read
off the consequences. -/

/-- The transport of `TauCeti.exists_eq_circleExp_image_Icc` to a Jordan curve: a nonempty compact
preconnected proper subset of the curve is the image of a closed arc of angles under the
parametrization. -/
private lemma exists_eq_jordanParam_image (e : C ≃ₜ Circle) (hSC : S ⊆ C) (hS : IsCompact S)
    (hpre : IsPreconnected S) (hne : S.Nonempty) (hSne : S ≠ C) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < 2 * π ∧ S = jordanParam e '' (Circle.exp '' Icc a b) := by
  set g : Circle → X := jordanParam e
  have hginj : Function.Injective g := jordanParam_injective e
  have hgrange : range g = C := range_jordanParam e
  set T : Set Circle := g ⁻¹' S
  have himg : g '' T = S := image_preimage_eq_of_subset (hgrange ▸ hSC)
  have hTcompact : IsCompact T := (isInducing_jordanParam e).isCompact_iff.mpr (himg ▸ hS)
  have hTpre : IsPreconnected T :=
    ((isInducing_jordanParam e).isPreconnected_image).mp (himg ▸ hpre)
  have hTne : T.Nonempty := by
    rw [← image_nonempty (f := g), himg]
    exact hne
  have hTuniv : T ≠ univ := fun hcon => hSne (by rw [← himg, hcon, image_univ, hgrange])
  obtain ⟨a, b, hab, hlt, hTeq⟩ :=
    exists_eq_circleExp_image_Icc hTcompact.isClosed hTpre hTne hTuniv
  exact ⟨a, b, hab, hlt, by rw [← himg, hTeq]⟩

/-- **A proper subcontinuum of a Jordan curve is a point or an arc.** A compact preconnected subset
of a Jordan curve other than the curve itself is either a subsingleton — the empty set or a single
point — or the range of an injective path, which is what it means for it to be an arc.

The path is the closed arc of angles produced by `TauCeti.exists_eq_circleExp_image_Icc`, carried to
the curve; it is injective because `Circle.exp` is injective on an interval shorter than a full turn
and the parametrization of the curve is injective outright. Its endpoints, `γ 0` and `γ 1`, are the
two endpoints of the arc. -/
theorem IsJordanCurve.subsingleton_or_exists_injective_path (h : IsJordanCurve C) (hSC : S ⊆ C)
    (hS : IsCompact S) (hpre : IsPreconnected S) (hSne : S ≠ C) :
    S.Subsingleton ∨ ∃ (p q : X) (γ : Path p q), Function.Injective γ ∧ range γ = S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl subsingleton_empty
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨a, b, hab, hlt, hSeq⟩ := exists_eq_jordanParam_image e hSC hS hpre hne hSne
  rcases eq_or_lt_of_le hab with rfl | hab'
  · refine Or.inl ?_
    rw [hSeq, Icc_self, image_singleton, image_singleton]
    exact subsingleton_singleton
  refine Or.inr ⟨_, _,
    ((Path.segment a b).map Circle.exp.continuous).map (continuous_jordanParam e), ?_, ?_⟩
  · have hseg : range (Path.segment a b) = Icc a b := by
      rw [Path.range_segment, segment_eq_Icc hab]
    intro x y hxy
    rw [Path.map_coe, Path.map_coe] at hxy
    have h₁ : Circle.exp (Path.segment a b x) = Circle.exp (Path.segment a b y) :=
      jordanParam_injective e hxy
    have h₂ : (Path.segment a b) x = (Path.segment a b) y :=
      Circle.exp_injOn_Icc hlt (hseg ▸ mem_range_self x) (hseg ▸ mem_range_self y) h₁
    exact Path.segment_injective_of_ne hab'.ne h₂
  · rw [Path.map_coe, Path.map_coe, range_comp, range_comp, Path.range_segment,
      segment_eq_Icc hab, hSeq]

/-- The complement in the curve of the image of a closed arc of angles is the image of the
complementary open arc, by `TauCeti.compl_circleExp_image_Icc` and injectivity of the
parametrization. -/
private lemma sdiff_eq_jordanParam_image (e : C ≃ₜ Circle) {a b : ℝ} (hab : a ≤ b)
    (hlt : b - a < 2 * π) (hSeq : S = jordanParam e '' (Circle.exp '' Icc a b)) :
    C \ S = jordanParam e '' (Circle.exp '' Ioo b (a + 2 * π)) := by
  rw [← compl_circleExp_image_Icc hab hlt, compl_eq_univ_sdiff, hSeq,
    (jordanParam_injective e).injOn.image_sdiff_subset (subset_univ _), image_univ,
    range_jordanParam]

/-- **The complement of a proper subcontinuum in a Jordan curve is path connected.** Removing a
compact connected piece other than the whole curve leaves an open arc, in particular a nonempty path
connected set. The case of a single point is
`TauCeti.IsJordanCurve.isPathConnected_sdiff_singleton`. -/
theorem IsJordanCurve.isPathConnected_sdiff (h : IsJordanCurve C) (hSC : S ⊆ C) (hS : IsCompact S)
    (hpre : IsPreconnected S) (hSne : S ≠ C) : IsPathConnected (C \ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [sdiff_empty]
    exact h.isPathConnected
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨a, b, hab, hlt, hSeq⟩ := exists_eq_jordanParam_image e hSC hS hpre hne hSne
  rw [sdiff_eq_jordanParam_image e hab hlt hSeq]
  refine IsPathConnected.image' ?_ (continuous_jordanParam e).continuousOn
  exact ((convex_Ioo b (a + 2 * π)).isPathConnected
    (nonempty_Ioo.mpr (by linarith))).image' Circle.exp.continuous.continuousOn

/-! ## Nowhere density

A proper subcontinuum with more than one point occupies a relatively open piece of the curve, so it
is not nowhere dense there. Stated in the contrapositive this is what identifies a nowhere dense
subcontinuum as a single point, and it is the form the Carathéodory boundary correspondence spends:
a boundary cluster set of a conformal map is a continuum on the image boundary, and this is what
degenerates it. Both statements are about a closure taken in the ambient space, so that space is
asked to be Hausdorff here. -/

/-- **A proper subcontinuum of a Jordan curve with more than one point is not nowhere dense in it**:
one of its points is not adherent to the rest of the curve.

The witness is the midpoint of the arc of angles carrying the subcontinuum. The complement of the
subcontinuum in the curve is the open arc of `TauCeti.compl_circleExp_image_Icc`, whose closure is
contained in the compact — hence closed — image of the corresponding closed arc, and the midpoint
misses that image because `Circle.exp` is injective on a period. -/
theorem IsJordanCurve.exists_notMem_closure_sdiff [T2Space X] (h : IsJordanCurve C) (hSC : S ⊆ C)
    (hS : IsCompact S) (hpre : IsPreconnected S) (hSne : S ≠ C) (hnsub : ¬ S.Subsingleton) :
    ∃ p ∈ S, p ∉ closure (C \ S) := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨x, hx, y, hy, hxy⟩ := not_subsingleton_iff.mp hnsub
  obtain ⟨a, b, hab, hlt, hSeq⟩ := exists_eq_jordanParam_image e hSC hS hpre ⟨x, hx⟩ hSne
  have hab' : a < b := by
    rcases eq_or_lt_of_le hab with rfl | hab'
    · rw [hSeq, Icc_self, image_singleton, image_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · exact hab'
  have hLclosed : IsClosed (jordanParam e '' (Circle.exp '' Icc b (a + 2 * π))) :=
    ((isCompact_Icc.image Circle.exp.continuous).image (continuous_jordanParam e)).isClosed
  have hsub : C \ S ⊆ jordanParam e '' (Circle.exp '' Icc b (a + 2 * π)) := by
    rw [sdiff_eq_jordanParam_image e hab hlt hSeq]
    exact image_mono (image_mono Ioo_subset_Icc_self)
  have hmmem : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hpS : jordanParam e (Circle.exp ((a + b) / 2)) ∈ S := by
    rw [hSeq]
    exact mem_image_of_mem _ (mem_image_of_mem _ hmmem)
  refine ⟨_, hpS, fun hcon => ?_⟩
  obtain ⟨u, ⟨s, hs, hsu⟩, hu⟩ := closure_minimal hsub hLclosed hcon
  have hsm : s = (a + b) / 2 := by
    refine circleExp_injOn_Ioc a ⟨by linarith [hs.1], hs.2⟩ ⟨by linarith, by linarith⟩ ?_
    rw [hsu]
    exact jordanParam_injective e hu
  linarith [hs.1, hsm ▸ hs.1]

/-- **A nowhere dense subcontinuum of a Jordan curve is a single point.** If every point of a
compact preconnected subset of a Jordan curve is adherent to the complement of that subset in the
curve, then the subset is a subsingleton.

This is the contrapositive of `TauCeti.IsJordanCurve.exists_notMem_closure_sdiff`; no properness
hypothesis is needed, because a nonempty subset satisfying the density hypothesis already has a
nonempty complement in the curve. -/
theorem IsJordanCurve.subsingleton_of_subset_closure_sdiff [T2Space X] (h : IsJordanCurve C)
    (hSC : S ⊆ C) (hS : IsCompact S) (hpre : IsPreconnected S) (hdense : S ⊆ closure (C \ S)) :
    S.Subsingleton := by
  by_contra hnsub
  obtain ⟨x, hx, _, _, _⟩ := not_subsingleton_iff.mp hnsub
  have hSne : S ≠ C := by
    rintro rfl
    rw [sdiff_self, closure_empty] at hdense
    exact hdense hx
  obtain ⟨p, hp, hpn⟩ := h.exists_notMem_closure_sdiff hSC hS hpre hSne hnsub
  exact hpn (hdense hp)

end TauCeti
