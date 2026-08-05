/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.SubgroupQuotient

/-!
# The covering associated to a subgroup

For a subgroup `H ≤ π₁(X, x₀)`, `UniversalCover.SubgroupQuotient x₀ H` is already defined as
the orbit quotient of the universal cover by `H`, and `UniversalCover.subgroupQuotientProj`
is its descended endpoint projection. This file proves that the descended projection is a
covering map.

The proof descends the standard sheet decomposition of the universal cover. Over a connected
good neighbourhood `U`, the `H`-orbits of the sheets are exactly the sheets of the quotient.
The only bookkeeping needed is that a fundamental-group element carries the sheet through a
point of one fibre onto the sheet through its translate.

## Main declaration

* `TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj`: the cover associated to
  `H ≤ π₁(X, x₀)` is a covering space of `X`.

## References

This completes the existence half in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 7: construct the pointed connected cover `UniversalCover x₀ / H`. It uses the
based-path sheet construction adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) and Mathlib's
quotient-covering-map interface due to Junyan Xu.
-/

public section
noncomputable section

open Topology

variable {X : Type*} [TopologicalSpace X] {x₀ x : X}

namespace TauCeti.UniversalCover

/-- A point in a fibre of the universal cover determines a homotopy class with the fibre's
fixed endpoint. -/
private def fiberPath (e : (proj : UniversalCover x₀ → X) ⁻¹' {x}) :
    Path.Homotopic.Quotient x₀ x :=
  e.1.path.cast rfl (Set.mem_singleton_iff.mp e.2).symm

/-- Rebuilding a point of a fibre from its endpoint-adjusted path class returns that point. -/
private theorem mk_fiberPath (e : (proj : UniversalCover x₀ → X) ⁻¹' {x}) :
    mk x (fiberPath e) = e.1 := by
  let he := (Set.mem_singleton_iff.mp e.2).symm
  apply UniversalCover.ext he
  exact Path.Homotopic.Quotient.cast_heq rfl he

/-- The canonical point of a fibre associated to a path class. -/
private def fiberPoint (q : Path.Homotopic.Quotient x₀ x) :
    (proj : UniversalCover x₀ → X) ⁻¹' {x} :=
  ⟨mk x q, rfl⟩

/-- Extracting the path class from its canonical fibre point returns that class. -/
@[simp]
private theorem fiberPath_fiberPoint (q : Path.Homotopic.Quotient x₀ x) :
    fiberPath (fiberPoint q) = q := by
  simp only [fiberPath, fiberPoint, Path.Homotopic.Quotient.cast_rfl_rfl]

/-- The point represented by a path class belongs to the sheet indexed by that class. -/
private theorem mk_mem_sheet (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : mk x q ∈ sheet U hxU q := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep q
  rw [← hp]
  have hq : (⟦p⟧ : Path.Homotopic.Quotient x₀ x) =
      Path.Homotopic.Quotient.mk p :=
    Path.Homotopic.Quotient.mk''_eq_mk p
  rw [hq, ← ofBasedPath_ofPath]
  exact mem_sheet_self (x₀ := x₀) hxU p

/-- Every sheet over a path-connected good neighbourhood is path-connected. -/
private theorem isPathConnected_sheet [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (U : Set X) (hU_open : IsOpen U)
    (hU_pathConn : IsPathConnected U) (hU_slsc : IsPathHomotopyTrivial U) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : IsPathConnected (sheet U hxU q) := by
  let f : sheet U hxU q → U :=
    Subtype.map proj (sheet_subset_proj_preimage U hxU q)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro e₁ e₂ he
      apply Subtype.ext
      exact proj_injOn_sheet hU_slsc hxU q e₁.2 e₂.2 (congrArg Subtype.val he)
    · intro y
      obtain ⟨e, he, hey⟩ := proj_surjOn_sheet hU_pathConn hxU q y.2
      exact ⟨⟨e, he⟩, Subtype.ext hey⟩
  let e : sheet U hxU q ≃ U := Equiv.ofBijective f hf_bij
  have hf_cont : Continuous f :=
    ((continuous_proj x₀).comp continuous_subtype_val).subtype_mk _
  have hf_open : IsOpenMap f :=
    ((isOpenMap_proj x₀).domRestrict (isOpen_sheet U hU_open hxU q)).subtype_mk _
  let h : sheet U hxU q ≃ₜ U := e.toHomeomorphOfContinuousOpen hf_cont hf_open
  rw [isPathConnected_iff_pathConnectedSpace]
  let : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU_pathConn
  exact h.symm.surjective.pathConnectedSpace h.symm.continuous

/-- A preconnected subset of the preimage of a good neighbourhood which meets one sheet is
contained in that sheet. -/
private theorem subset_sheet_of_isPreconnected [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] {C : Set (UniversalCover x₀)}
    {V : Set X} (hV_open : IsOpen V) (hV_pathConn : IsPathConnected V) (hxV : x ∈ V)
    (hV_slsc : IsPathHomotopyTrivial V) (q : Path.Homotopic.Quotient x₀ x)
    (hC : IsPreconnected C) (hCV : C ⊆ proj ⁻¹' V)
    (hCq : (C ∩ sheet V hxV q).Nonempty) : C ⊆ sheet V hxV q := by
  let otherSheets : Set (UniversalCover x₀) :=
    ⋃ q' : {q' : Path.Homotopic.Quotient x₀ x // q' ≠ q}, sheet V hxV q'.1
  have hother_open : IsOpen otherSheets :=
    isOpen_iUnion fun q' ↦ isOpen_sheet V hV_open hxV q'.1
  have hdisjoint : Disjoint (sheet V hxV q) otherSheets := by
    refine Set.disjoint_left.mpr ?_
    intro e heq heother
    rcases Set.mem_iUnion.mp heother with ⟨q', heq'⟩
    exact Set.disjoint_left.mp (pairwise_disjoint_sheet hV_slsc hxV q'.2.symm) heq heq'
  have hcover : C ⊆ sheet V hxV q ∪ otherSheets := by
    intro e heC
    rcases Set.mem_iUnion.mp (sheet_exhaustive hV_pathConn hxV (hCV heC)) with ⟨q', heq'⟩
    by_cases hq' : q' = q
    · exact Set.mem_union_left _ (hq' ▸ heq')
    · exact Set.mem_union_right _ (Set.mem_iUnion_of_mem ⟨q', hq'⟩ heq')
  rcases hC.subset_or_subset (isOpen_sheet V hV_open hxV q)
      hother_open hdisjoint hcover with h | h
  · exact h
  · obtain ⟨e, heC, heq⟩ := hCq
    exact (Set.disjoint_left.mp hdisjoint heq (h heC)).elim

/-- A fundamental-group element carries a sheet to the sheet through the translated point in
the fibre. -/
private theorem smul_sheet [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (U : Set X) (hU_open : IsOpen U)
    (hU_pathConn : IsPathConnected U) (hU_slsc : IsPathHomotopyTrivial U) (hxU : x ∈ U)
    (g : FundamentalGroup X x₀) (e : (proj : UniversalCover x₀ → X) ⁻¹' {x}) :
    letI := (isQuotientCoveringMap (x₀ := x₀)).mulActionFiber x
    (g • ·) '' sheet U hxU (fiberPath e) = sheet U hxU (fiberPath (g • e)) := by
  let hquot := isQuotientCoveringMap (x₀ := x₀)
  let := hquot.mulActionFiber x
  have map_subset (g : FundamentalGroup X x₀)
      (e : (proj : UniversalCover x₀ → X) ⁻¹' {x}) :
      (g • ·) '' sheet U hxU (fiberPath e) ⊆ sheet U hxU (fiberPath (g • e)) := by
    have hcenter : (e : UniversalCover x₀) ∈ sheet U hxU (fiberPath e) := by
      rw [← mk_fiberPath e]
      exact mk_mem_sheet U hxU (fiberPath e)
    have htranslated : ((g • e : (proj : UniversalCover x₀ → X) ⁻¹' {x}) :
        UniversalCover x₀) ∈ sheet U hxU (fiberPath (g • e)) := by
      rw [← mk_fiberPath (g • e)]
      exact mk_mem_sheet U hxU (fiberPath (g • e))
    refine subset_sheet_of_isPreconnected
      (C := (g • ·) '' sheet U hxU (fiberPath e)) hU_open hU_pathConn hxU hU_slsc
      (fiberPath (g • e)) ?_ ?_ ?_
    · exact ((isPathConnected_sheet U hU_open hU_pathConn hU_slsc hxU (fiberPath e)).image
        (continuous_const_smul g)).isConnected.isPreconnected
    · rintro _ ⟨z, hz, rfl⟩
      simpa only [Set.mem_preimage, proj_smul] using
        sheet_subset_proj_preimage U hxU (fiberPath e) hz
    · refine ⟨g • (e : UniversalCover x₀), ⟨⟨e, hcenter, rfl⟩, ?_⟩⟩
      simpa only [hquot.coe_mulActionFiber_smul] using htranslated
  apply Set.Subset.antisymm (map_subset g e)
  have hinv := map_subset g⁻¹ (g • e)
  have hinv' : (g⁻¹ • ·) '' sheet U hxU (fiberPath (g • e)) ⊆
      sheet U hxU (fiberPath e) := by
    simpa only [inv_smul_smul] using hinv
  intro z hz
  exact ⟨g⁻¹ • z, hinv' ⟨z, hz, rfl⟩, by simp⟩

/-- The endpoint projection on the quotient of the universal cover by `H` is a covering map. -/
theorem isCoveringMap_subgroupQuotientProj [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    IsCoveringMap (subgroupQuotientProj x₀ H) := by
  intro x
  obtain ⟨U, hU_open, hxU, hU_pathConn, hU_slsc⟩ :=
    exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  let hq := isQuotientCoveringMap_subgroupQuotientMap x₀ H
  let hfull := isQuotientCoveringMap (x₀ := x₀)
  let := hfull.mulActionFiber x
  let I := MulAction.orbitRel.Quotient H ((proj : UniversalCover x₀ → X) ⁻¹' {x})
  let S (a : I) : Set (SubgroupQuotient x₀ H) :=
    subgroupQuotientMap x₀ H '' sheet U hxU (fiberPath a.out)
  let eₓ : (proj : UniversalCover x₀ → X) ⁻¹' {x} :=
    fiberPoint (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x))
  have : Nonempty I := ⟨Quotient.mk'' eₓ⟩
  let : TopologicalSpace I := ⊥
  have : DiscreteTopology I := ⟨rfl⟩
  have : Nonempty (X → SubgroupQuotient x₀ H) :=
    ⟨fun _ ↦ SubgroupQuotient.basepoint x₀ H⟩
  have hopen_r : IsOpenMap (subgroupQuotientProj x₀ H) := by
    apply IsOpenMap.of_comp (f := subgroupQuotientMap x₀ H)
      hq.isCoveringMap.continuous hq.surjective
    simpa only [subgroupQuotientProj_comp_subgroupQuotientMap] using isOpenMap_proj x₀
  have hrq (e : UniversalCover x₀) :
      subgroupQuotientProj x₀ H (subgroupQuotientMap x₀ H e) = proj e :=
    congrFun (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) e
  have hS_open (a : I) : IsOpen (S a) :=
    hq.isOpenQuotientMap.isOpenMap _ (isOpen_sheet U hU_open hxU (fiberPath a.out))
  have hS_inj (a : I) : (S a).InjOn (subgroupQuotientProj x₀ H) := by
    rintro z₁ ⟨e₁, he₁, rfl⟩ z₂ ⟨e₂, he₂, rfl⟩ heq
    apply congrArg (subgroupQuotientMap x₀ H)
    apply proj_injOn_sheet hU_slsc hxU (fiberPath a.out) he₁ he₂
    simpa only [hrq] using heq
  have hS_surj (a : I) : (S a).SurjOn (subgroupQuotientProj x₀ H) U := by
    intro y hyU
    obtain ⟨e, he, hey⟩ := proj_surjOn_sheet hU_pathConn hxU (fiberPath a.out) hyU
    refine ⟨subgroupQuotientMap x₀ H e, ⟨e, he, rfl⟩, ?_⟩
    calc
      subgroupQuotientProj x₀ H (subgroupQuotientMap x₀ H e) = proj e := hrq e
      _ = y := hey
  have hq_smul (g : H) (e : UniversalCover x₀) :
      subgroupQuotientMap x₀ H (g • e) = subgroupQuotientMap x₀ H e := by
    apply (subgroupQuotientMap_eq_iff x₀ H).2
    exact ⟨g, rfl⟩
  have hS_eq_of_orbit
      {e₁ e₂ : (proj : UniversalCover x₀ → X) ⁻¹' {x}} (he : e₁ ∈ MulAction.orbit H e₂) :
      subgroupQuotientMap x₀ H '' sheet U hxU (fiberPath e₁) =
        subgroupQuotientMap x₀ H '' sheet U hxU (fiberPath e₂) := by
    rcases he with ⟨g, hg⟩
    have hg' : (g.1 • e₂ : (proj : UniversalCover x₀ → X) ⁻¹' {x}) = e₁ := by
      simpa only [Subgroup.smul_def] using hg
    rw [← hg', ← smul_sheet U hU_open hU_pathConn hU_slsc hxU g.1 e₂]
    ext z
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, (hq_smul g e).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨g • e, ⟨e, he, rfl⟩, hq_smul g e⟩
  have hS_disjoint : Pairwise fun a b : I ↦ Disjoint (S a) (S b) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    intro z hza hzb
    rcases hza with ⟨e₁, he₁, rfl⟩
    rcases hzb with ⟨e₂, he₂, heq⟩
    have he_orbit : e₁ ∈ MulAction.orbit H e₂ :=
      (subgroupQuotientMap_eq_iff x₀ H).1 heq.symm
    rcases he_orbit with ⟨g, hg⟩
    have hge₂ : g.1 • e₂ ∈ sheet U hxU
        (fiberPath (g.1 • b.out : (proj : UniversalCover x₀ → X) ⁻¹' {x})) := by
      rw [← smul_sheet U hU_open hU_pathConn hU_slsc hxU g.1 b.out]
      exact ⟨e₂, he₂, rfl⟩
    have hpaths : fiberPath a.out =
        fiberPath (g.1 • b.out : (proj : UniversalCover x₀ → X) ⁻¹' {x}) := by
      by_contra hne
      exact Set.disjoint_left.mp (pairwise_disjoint_sheet hU_slsc hxU hne)
        he₁ (hg ▸ hge₂)
    have hcenters : a.out =
        (g.1 • b.out : (proj : UniversalCover x₀ → X) ⁻¹' {x}) := by
      apply Subtype.ext
      rw [← mk_fiberPath a.out,
        ← mk_fiberPath (g.1 • b.out : (proj : UniversalCover x₀ → X) ⁻¹' {x}), hpaths]
    have hout_eq : (Quotient.mk'' a.out : I) = Quotient.mk'' b.out := by
      rw [Quotient.eq'', MulAction.orbitRel_apply]
      exact ⟨g, by simpa only [Subgroup.smul_def] using hcenters.symm⟩
    apply hab
    calc
      a = Quotient.mk'' a.out := (Quotient.out_eq' a).symm
      _ = Quotient.mk'' b.out := hout_eq
      _ = b := Quotient.out_eq' b
  have hS_exhaustive : subgroupQuotientProj x₀ H ⁻¹' U ⊆ ⋃ a, S a := by
    intro z hz
    induction z using Quotient.inductionOn' with
    | h e =>
      have heU : proj e ∈ U := by
        rw [Set.mem_preimage, subgroupQuotientProj_mk] at hz
        exact hz
      rcases Set.mem_iUnion.mp (sheet_exhaustive hU_pathConn hxU heU) with ⟨qₓ, heqₓ⟩
      let center : (proj : UniversalCover x₀ → X) ⁻¹' {x} := fiberPoint qₓ
      let a : I := Quotient.mk'' center
      have ha_orbit : a.out ∈ MulAction.orbit H center := by
        rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
        exact (Quotient.out_eq' a).trans rfl
      have heqₓ' : e ∈ sheet U hxU (fiberPath center) := by
        simpa only [center, fiberPath_fiberPoint] using heqₓ
      refine Set.mem_iUnion_of_mem a ?_
      rw [← subgroupQuotientMap_apply]
      -- Expose the let-bound definition of `S` so `hS_eq_of_orbit` can match its left side.
      rw [show S a = subgroupQuotientMap x₀ H '' sheet U hxU (fiberPath a.out) from rfl,
        hS_eq_of_orbit ha_orbit]
      exact ⟨e, heqₓ', rfl⟩
  have hopen_iff (a : I) {W : Set X} (hWU : W ⊆ U) :
      IsOpen W ↔ IsOpen (subgroupQuotientProj x₀ H ⁻¹' W ∩ S a) := by
    constructor
    · intro hW
      exact (hW.preimage (continuous_subgroupQuotientProj x₀ H)).inter (hS_open a)
    · intro hopen
      have himage_open := hopen_r _ hopen
      have himage : subgroupQuotientProj x₀ H ''
          (subgroupQuotientProj x₀ H ⁻¹' W ∩ S a) = W := by
        ext y
        constructor
        · rintro ⟨z, ⟨hzW, -⟩, rfl⟩
          exact hzW
        · intro hyW
          obtain ⟨z, hzS, hzy⟩ := hS_surj a (hWU hyW)
          refine ⟨z, ⟨?_, hzS⟩, hzy⟩
          simpa only [Set.mem_preimage, hzy] using hyW
      rwa [himage] at himage_open
  refine ((IsEvenlyCovered.of_trivialization (t :=
    IsOpen.trivializationDiscrete S U hU_open hopen_iff hS_inj hS_surj hS_disjoint
      hS_exhaustive) hxU).to_isEvenlyCovered_preimage)

end TauCeti.UniversalCover
