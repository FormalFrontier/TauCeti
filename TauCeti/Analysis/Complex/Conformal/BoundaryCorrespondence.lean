/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
public import TauCeti.Analysis.Complex.Conformal.InverseFunction

/-!
# The boundary correspondence of a conformal map

A conformal map — a holomorphic injection `f` on an open set `U ⊆ ℂ` — is a *proper* map onto its
image: the preimage of a compact subset of `f '' U` is a compact subset of `U`. Properness is the
mechanism that forces the boundary to go to the boundary, and it is the first step of the
Carathéodory boundary correspondence, layer **L5** of the conformal-mapping roadmap. This file
proves it, deduces that a point approached from inside `U` is carried out of every compact subset
of `f '' U`, and packages the consequences for a map that *does* extend continuously to `closure U`:
such an extension carries `frontier U` into `frontier (f '' U)`, and — when `U` is in addition
bounded and the extension is injective on `closure U` — is a homeomorphism of the closures carrying
`frontier U` *onto* `frontier (f '' U)`.

The existence of the continuous extension is the hard, hypothesis-laden half of Carathéodory's
theorem (it needs the boundary of the image to be a Jordan curve, or at least locally connected),
and it is **not** proved here; the L5 milestone is that existence statement. What is proved here is
everything that holds unconditionally, plus the packaging that turns the extension, once it is
available, into the boundary homeomorphism the milestone asks for.

## The argument

Properness is the holomorphic inverse function theorem in disguise. `Function.invFunOn f U` is
holomorphic on `f '' U` (`TauCeti.DifferentiableOn.invFunOn`), and `U ∩ f ⁻¹' K` is exactly its
image of `K`, so it is compact as the continuous image of a compact set. Everything else follows
from that one fact. If `z i → w` with `z i ∈ U` and `w ∉ U`, then `f (z i)` cannot lie in a compact
`K ⊆ f '' U` frequently: otherwise `z i` would frequently lie in the compact — hence closed — set
`U ∩ f ⁻¹' K`, which would then contain the limit `w`.

For a boundary point `w ∈ frontier U`, the filter `𝓝[U] w` is the one to run this along: it is
`NeBot` precisely because `w ∈ closure U`. If a continuous extension `F` had `F w` inside the open
set `f '' U`, then a small closed ball around `F w` would be a compact subset of `f '' U` that
`f = F` enters eventually along `𝓝[U] w` by continuity, and leaves eventually by properness —
impossible on a nontrivial filter. Hence `F w ∉ f '' U`, while `F w ∈ closure (f '' U)` because `F`
is continuous on `closure U`; that is membership in `frontier (f '' U)`.

The argument beyond the two holomorphic inputs — the open mapping theorem, through
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, and the holomorphic inverse function theorem —
is purely topological, and no continuity hypothesis on the inverse of `f` appears precisely because
those two supply it. In accordance with the generality bar of `ConformalMapping/README.md`, which
fixes scalar `ℂ` for every theorem added in layers L0–L6, the results are stated for conformal maps
of `ℂ` rather than for an abstract proper map.

## Main results

* `TauCeti.isCompact_inter_preimage_of_differentiableOn_of_injOn` — a conformal map is proper onto
  its image: `U ∩ f ⁻¹' K` is compact for compact `K ⊆ f '' U`.
* `TauCeti.eventually_notMem_of_tendsto_of_notMem` — a family in `U` converging to a point outside
  `U`, in particular to a boundary point, is carried out of every compact subset of the image.
* `TauCeti.notMem_image_of_mem_frontier` — a continuous extension to `closure U` sends `frontier U`
  outside `f '' U`.
* `TauCeti.image_closure_eq_closure_image` — for bounded `U`, a continuous extension carries
  `closure U` onto `closure (f '' U)`.
* `TauCeti.image_frontier_subset_frontier_image` — a continuous extension carries `frontier U` into
  `frontier (f '' U)`; no boundedness is needed.
* `TauCeti.bijOn_closure_closure_image`, `TauCeti.closureHomeomorph` and
  `TauCeti.image_frontier_eq_frontier_image` — for bounded `U`, an extension injective on
  `closure U` is a homeomorphism `closure U ≃ₜ closure (f '' U)`, and it carries `frontier U` onto
  `frontier (f '' U)`.

## Coordination with upstream Mathlib

Mathlib has no boundary correspondence for conformal maps, and — unlike the L0–L3 material — layer
L5 is absent from [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the
in-progress human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself.
So this file is new Lean formalization rather than a temporary shim. It does consume the L0–L3 shims
`TauCeti.isOpen_image_of_differentiableOn_of_injOn` and `TauCeti.DifferentiableOn.invFunOn`, which
are to be refactored onto Mathlib once the upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {U K : Set ℂ} {f F : ℂ → ℂ}

/-! ## Properness -/

/-- **A conformal map is proper onto its image.** If `f` is holomorphic and injective on an open
set `U` and `K ⊆ f '' U` is compact, then the part of the preimage of `K` lying in `U` is compact.

Properness is what distinguishes `f '' U` as the *whole* image: the preimage cannot escape to the
boundary of `U` while its image stays in a compact part of `f '' U`. -/
theorem isCompact_inter_preimage_of_differentiableOn_of_injOn (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hK : IsCompact K) (hKf : K ⊆ f '' U) :
    IsCompact (U ∩ f ⁻¹' K) := by
  -- `U ∩ f ⁻¹' K` is the image of `K` under the holomorphic inverse `Function.invFunOn f U`.
  have hinv : DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) :=
    TauCeti.DifferentiableOn.invFunOn hfd hUo hfi
  have hset : U ∩ f ⁻¹' K = Function.invFunOn f U '' K := by
    ext z
    constructor
    · rintro ⟨hzU, hzK⟩
      exact ⟨f z, hzK, hfi.leftInvOn_invFunOn hzU⟩
    · rintro ⟨w, hwK, rfl⟩
      exact ⟨Function.invFunOn_mem (hKf hwK), by
        simpa only [mem_preimage, Function.invFunOn_eq (hKf hwK)] using hwK⟩
  rw [hset]
  exact hK.image_of_continuousOn (hinv.continuousOn.mono hKf)

/-- **A conformal map carries a family converging out of `U` out of every compact subset of the
image.** If `z i ∈ U` eventually, `z i → w` and `w ∉ U`, then eventually `f (z i)` avoids any
compact `K ⊆ f '' U`. -/
theorem eventually_notMem_of_tendsto_of_notMem {ι : Type*} {l : Filter ι} {z : ι → ℂ} {w : ℂ}
    (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hz : ∀ᶠ i in l, z i ∈ U) (hlim : Tendsto z l (𝓝 w)) (hwU : w ∉ U)
    (hK : IsCompact K) (hKf : K ⊆ f '' U) :
    ∀ᶠ i in l, f (z i) ∉ K := by
  -- Otherwise `z i` frequently lies in the compact — hence closed — set `U ∩ f ⁻¹' K`, which would
  -- therefore contain the limit `w`.
  have hC := isCompact_inter_preimage_of_differentiableOn_of_injOn hUo hfd hfi hK hKf
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_not] at hcon
  have hfreq : ∃ᶠ i in l, z i ∈ U ∩ f ⁻¹' K :=
    (hcon.and_eventually hz).mono fun i hi => ⟨hi.2, hi.1⟩
  exact hwU (hC.isClosed.mem_of_frequently_of_tendsto hfreq hlim).1

/-! ## Continuous extensions to the closure -/

/-- **A continuous extension of a conformal map sends the boundary off the image.** If `F` is
continuous on `closure U` and agrees with `f` on `U`, then `F` maps no boundary point of `U` into
the open set `f '' U`.

For open `U` the hypothesis `w ∈ frontier U` is `w ∈ closure U` together with `w ∉ U`; both halves
are used, the first to make the filter `𝓝[U] w` nontrivial and the second to invoke
`TauCeti.eventually_notMem_of_tendsto_of_notMem`. -/
theorem notMem_image_of_mem_frontier (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    {w : ℂ} (hw : w ∈ frontier U) : F w ∉ f '' U := by
  -- If `F w` were in the open set `f '' U`, a small closed ball `K` around it would be a compact
  -- subset of `f '' U` that `f = F` both enters eventually along `𝓝[U] w`, by continuity of `F`
  -- at `w`, and avoids eventually, by properness — impossible on a nontrivial filter.
  intro hmem
  have hVo : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo _ hmem
  have hwc : w ∈ closure U := frontier_subset_closure hw
  have hwU : w ∉ U := (hUo.frontier_eq.subset hw).2
  haveI : (𝓝[U] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hwc
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hlim : Tendsto (fun x : ℂ => x) (𝓝[U] w) (𝓝 w) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hesc : ∀ᶠ x in 𝓝[U] w, f x ∉ closedBall (F w) (δ / 2) :=
    eventually_notMem_of_tendsto_of_notMem hUo hfd hfi self_mem_nhdsWithin hlim hwU
      (isCompact_closedBall _ _) ((closedBall_subset_ball (by linarith)).trans hball)
  have hFlim : Tendsto F (𝓝[U] w) (𝓝 (F w)) := (hFc w hwc).mono subset_closure
  have hnear : ∀ᶠ x in 𝓝[U] w, f x ∈ closedBall (F w) (δ / 2) := by
    filter_upwards [hFlim.eventually_mem (closedBall_mem_nhds (F w) hδ2), self_mem_nhdsWithin]
      with x hx hxU
    rwa [← hFf hxU]
  obtain ⟨x, hx1, hx2⟩ := (hesc.and hnear).exists
  exact hx1 hx2

/-- **A continuous extension of a conformal map carries the closure onto the closure of the
image**, for a bounded `U`. Only boundedness and continuity are used; no holomorphy hypothesis
appears. -/
theorem image_closure_eq_closure_image (hUb : Bornology.IsBounded U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) :
    F '' closure U = closure (f '' U) := by
  rw [image_closure_of_isCompact hUb.isCompact_closure hFc, hFf.image_eq]

/-- **A continuous extension of a conformal map carries the boundary into the boundary.** No
boundedness is needed. -/
theorem image_frontier_subset_frontier_image (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) :
    F '' frontier U ⊆ frontier (f '' U) := by
  -- A boundary point lands in `closure (f '' U)` by continuity and outside `f '' U` by
  -- `TauCeti.notMem_image_of_mem_frontier`; `f '' U` is open, so its frontier is the difference.
  have hcl : F '' closure U ⊆ closure (f '' U) := by
    rw [← hFf.image_eq]
    exact hFc.image_closure
  rintro _ ⟨w, hw, rfl⟩
  rw [(isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi).frontier_eq]
  exact ⟨hcl ⟨w, frontier_subset_closure hw, rfl⟩,
    notMem_image_of_mem_frontier hUo hfd hfi hFc hFf hw⟩

/-! ## The boundary homeomorphism -/

/-- **An injective continuous extension of a conformal map is a bijection of the closures.** The
set-level form of `TauCeti.closureHomeomorph`: injectivity is the hypothesis, and surjectivity onto
`closure (f '' U)` is `TauCeti.image_closure_eq_closure_image`. -/
theorem bijOn_closure_closure_image (hUb : Bornology.IsBounded U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U)) :
    BijOn F (closure U) (closure (f '' U)) :=
  (image_closure_eq_closure_image hUb hFc hFf) ▸ hFi.bijOn_image

/-- **The boundary homeomorphism of a conformal map with an injective continuous extension.** If
`F` is continuous on `closure U` for a bounded open `U`, agrees with the conformal map `f` on `U`,
and is injective on `closure U`, then `F` is a homeomorphism of `closure U` onto
`closure (f '' U)`.

This is the conclusion the Carathéodory correspondence (layer **L5**) asks for; what that milestone
adds is the *existence* of such an `F` for a Riemann map of a Jordan domain, which is not proved
here. Continuity of the inverse is free: `closure U` is compact and `ℂ` is Hausdorff.

The definition is not exposed; `TauCeti.coe_closureHomeomorph_apply` and
`TauCeti.coe_closureHomeomorph_symm_apply` are its characterizations. -/
noncomputable def closureHomeomorph (hUb : Bornology.IsBounded U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U)) :
    closure U ≃ₜ closure (f '' U) :=
  haveI : CompactSpace (closure U) := isCompact_iff_compactSpace.mp hUb.isCompact_closure
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (fun x : closure U =>
        (⟨F x, (bijOn_closure_closure_image hUb hFc hFf hFi).mapsTo x.2⟩ : closure (f '' U)))
      ⟨fun a b hab => Subtype.ext (hFi a.2 b.2 (congrArg Subtype.val hab)), fun y => by
        obtain ⟨x, hx, hxy⟩ := (bijOn_closure_closure_image hUb hFc hFf hFi).surjOn y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩)
    (Continuous.subtype_mk hFc.restrict _)

/-- The boundary homeomorphism is the extension `F` itself. -/
@[simp]
lemma coe_closureHomeomorph_apply (hUb : Bornology.IsBounded U) (hFc : ContinuousOn F (closure U))
    (hFf : EqOn F f U) (hFi : InjOn F (closure U)) (x : closure U) :
    (closureHomeomorph hUb hFc hFf hFi x : ℂ) = F x := (rfl)

/-- The inverse of the boundary homeomorphism is the set-level inverse
`Function.invFunOn F (closure U)`. -/
@[simp]
lemma coe_closureHomeomorph_symm_apply (hUb : Bornology.IsBounded U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U))
    (y : closure (f '' U)) :
    ((closureHomeomorph hUb hFc hFf hFi).symm y : ℂ) = Function.invFunOn F (closure U) y := by
  -- Both sides lie in `closure U` and are carried to `y` by `F`, which is injective there.
  have hFsymm : F ((closureHomeomorph hUb hFc hFf hFi).symm y : ℂ) = (y : ℂ) := by
    rw [← coe_closureHomeomorph_apply hUb hFc hFf hFi, Homeomorph.apply_symm_apply]
  have hex : ∃ x ∈ closure U, F x = (y : ℂ) :=
    ⟨_, ((closureHomeomorph hUb hFc hFf hFi).symm y).2, hFsymm⟩
  exact hFi ((closureHomeomorph hUb hFc hFf hFi).symm y).2 (Function.invFunOn_mem hex)
    (by rw [hFsymm, Function.invFunOn_eq hex])

/-- **A conformal map with an injective continuous extension carries the boundary onto the
boundary.** For a bounded `U` and an injective `F` the inclusion of
`TauCeti.image_frontier_subset_frontier_image` is an equality: `frontier U = closure U \ U` and
`frontier (f '' U) = closure (f '' U) \ f '' U` are images of each other because injectivity lets
`F` be removed from a set difference. Injectivity of `f` on `U` is not assumed: it follows from
that of `F` on `closure U`. -/
theorem image_frontier_eq_frontier_image (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (hFi : InjOn F (closure U)) :
    F '' frontier U = frontier (f '' U) := by
  have hfi : InjOn f U := fun x hx y hy hxy =>
    hFi (subset_closure hx) (subset_closure hy) (by rw [hFf hx, hFf hy]; exact hxy)
  calc F '' frontier U = F '' (closure U \ U) := by rw [hUo.frontier_eq]
    _ = F '' closure U \ F '' U := hFi.image_sdiff_subset subset_closure
    _ = closure (f '' U) \ f '' U := by
        rw [image_closure_eq_closure_image hUb hFc hFf, hFf.image_eq]
    _ = frontier (f '' U) :=
        ((isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi).frontier_eq).symm

end TauCeti
