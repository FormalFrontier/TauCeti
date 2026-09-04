/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Covering.Basic

/-!
# A map of covering spaces with locally connected target is a covering map

Let `p : E → X` and `q : F → X` be covering maps and let `g : E → F` be a continuous map over
`X`, that is, `q ∘ g = p`. This file proves that `g` is itself a covering map as soon as `F` is
locally connected.

The proof is the standard sheet comparison. Around a point `f₀` of `F`, choose a connected open
neighbourhood in `F` whose image `V` lies inside the intersection of evenly covered
neighbourhoods for `p` and `q`, and trivialize both projections over `V`. A sheet of `p` over `V`
is the image of `V` under
`v ↦ tp.symm (v, i)`, so it is connected, and the sheet index of its image under `g` is a
continuous map from `V` to a discrete space, hence constant. So `g` carries each sheet of `p`
over `V` onto a single sheet of `q`, and injectively, because `p = q ∘ g` is injective on it.
The sheet `W` of `q` through `f₀` is therefore evenly covered by `g`, with fibre the set of
sheets of `p` that land in `W`.

Local connectedness of `F` produces the connected neighbourhood whose open, connected image is
`V`. It is used exactly once, to make the sheet index locally constant.

Neither total space is assumed connected and `g` is not assumed surjective. That is consistent
because `IsCoveringMap` allows empty fibres: over a sheet of `q` missed by `g` the fibre of `g`
is empty.

## Main declarations

* `IsCoveringMap.of_comp_eq`: **a continuous map between covering spaces, with locally connected
  target and commuting with the projections, is a covering map.**
-/

public section

namespace TauCeti

open Bundle Set Topology

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {g : E → F}

/-- The evenly covered neighbourhood of `f₀` for a map `g` over `X` between two trivialized
projections, cut out by a connected open set `V` of the base lying inside both base sets.

The neighbourhood is the sheet of `q` over `V` through `f₀`, and the fibre over it is the set of
sheet indices of `p` that `g` sends into that sheet. -/
private theorem isEvenlyCovered_of_trivialization (hq : Continuous q) (hg : Continuous g)
    (hqg : ∀ e, q (g e) = p e) {I J : Type*} [TopologicalSpace I] [DiscreteTopology I]
    [TopologicalSpace J] [DiscreteTopology J] (tp : Trivialization I p) (tq : Trivialization J q)
    (f₀ : F) {V : Set X} (hVopen : IsOpen V) (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) (hf₀V : q f₀ ∈ V) :
    IsEvenlyCovered g f₀ (g ⁻¹' {f₀}) := by
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := {i : I // (tq (g (tp.toOpenPartialHomeomorph.symm (q f₀, i)))).2 = (tq f₀).2}) ?_
  -- Points of a sheet of `p` over `V` land in `tq.source`, so their sheet index is defined.
  have hmem : ∀ (i : I) {v : X}, v ∈ V →
      g (tp.toOpenPartialHomeomorph.symm (v, i)) ∈ tq.source := by
    intro i v hv
    rw [tq.mem_source, hqg, tp.proj_symm_apply' (hVsub hv).1]
    exact (hVsub hv).2
  have hsnd : ContinuousOn (fun f : F => (tq f).2) tq.source :=
    continuous_snd.comp_continuousOn tq.continuousOn_toFun
  -- That index varies continuously along the sheet,
  have hcont : ∀ i : I,
      ContinuousOn (fun v => (tq (g (tp.toOpenPartialHomeomorph.symm (v, i)))).2) V := by
    intro i
    have h1 : ContinuousOn (fun v => g (tp.toOpenPartialHomeomorph.symm (v, i))) V :=
      hg.comp_continuousOn (tp.continuousOn_symm_prodMk_left.mono fun v hv => (hVsub hv).1)
    exact hsnd.comp h1 fun v hv => hmem i hv
  -- hence is constant, `V` being preconnected and `J` discrete.
  have hcv : ∀ (i : I) {v : X}, v ∈ V →
      (tq (g (tp.toOpenPartialHomeomorph.symm (v, i)))).2 =
        (tq (g (tp.toOpenPartialHomeomorph.symm (q f₀, i)))).2 :=
    fun i _ hv => hVconn.constant (hcont i) hv hf₀V
  set j₀ : J := (tq f₀).2 with hj₀
  set W : Set F := {f | q f ∈ V ∧ (tq f).2 = j₀} with hWdef
  have hf₀W : f₀ ∈ W := ⟨hf₀V, rfl⟩
  have hWopen : IsOpen W := by
    have hW : W = q ⁻¹' V ∩ (tq.source ∩ (fun f => (tq f).2) ⁻¹' {j₀}) := by
      ext f
      exact ⟨fun h => ⟨h.1, tq.mem_source.mpr (hVsub h.1).2, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [hW]
    exact (hVopen.preimage hq).inter
      (hsnd.isOpen_inter_preimage tq.open_source (isOpen_discrete {j₀}))
  -- Membership in `g ⁻¹' W` is read off the sheet index of `p`.
  have hgW : ∀ e : E, g e ∈ W ↔
      p e ∈ V ∧ (tq (g (tp.toOpenPartialHomeomorph.symm (q f₀, (tp e).2)))).2 = j₀ := by
    intro e
    constructor
    · rintro ⟨h1, h2⟩
      rw [hqg] at h1
      refine ⟨h1, ?_⟩
      rw [← hcv (tp e).2 h1, tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub h1).1), h2]
    · rintro ⟨h1, h2⟩
      have h3 := hcv (tp e).2 h1
      rw [tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub h1).1)] at h3
      exact ⟨by rw [hqg]; exact h1, by rw [h3, h2]⟩
  have hfwd : ∀ e : E, g e ∈ W →
      (tq (g (tp.toOpenPartialHomeomorph.symm (q f₀, (tp e).2)))).2 = j₀ :=
    fun e he => ((hgW e).mp he).2
  -- The sheet of `p` through a point of `W` is carried onto that point.
  have hbwd : ∀ (w : F) (i : I), w ∈ W →
      (tq (g (tp.toOpenPartialHomeomorph.symm (q f₀, i)))).2 = j₀ →
      g (tp.toOpenPartialHomeomorph.symm (q w, i)) = w := by
    intro w i hw hi
    have hwV : q w ∈ V := hw.1
    have h1 : q (g (tp.toOpenPartialHomeomorph.symm (q w, i))) = q w := by
      rw [hqg, tp.proj_symm_apply' (hVsub hwV).1]
    refine tq.injOn (hmem i hwV) (tq.mem_source.mpr (hVsub hwV).2) (Prod.ext ?_ ?_)
    · simp only [Trivialization.coe_coe]
      rw [tq.coe_fst (hmem i hwV), tq.coe_fst (tq.mem_source.mpr (hVsub hwV).2), h1]
    · simp only [Trivialization.coe_coe]
      rw [hcv i hwV, hi, hw.2]
  refine ⟨inferInstance, W, hf₀W, hWopen, hWopen.preimage hg,
    { toFun := fun e => (⟨g e.1, e.2⟩, ⟨(tp e.1).2, hfwd e.1 e.2⟩)
      invFun := fun wi => ⟨tp.toOpenPartialHomeomorph.symm (q wi.1.1, wi.2.1), by
        refine (hgW _).mpr ⟨?_, ?_⟩
        · rw [tp.proj_symm_apply' (hVsub wi.1.2.1).1]
          exact wi.1.2.1
        · rw [tp.apply_symm_apply' (hVsub wi.1.2.1).1]
          exact wi.2.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        refine Subtype.ext ?_
        dsimp only
        rw [hqg e]
        exact tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub ((hgW e).mp he).1).1)
      right_inv := by
        rintro ⟨⟨w, hw⟩, ⟨i, hi⟩⟩
        dsimp only
        refine Prod.ext (Subtype.ext (hbwd w i hw hi)) (Subtype.ext ?_)
        dsimp only
        rw [tp.apply_symm_apply' (hVsub hw.1).1]
      continuous_toFun := by
        refine Continuous.prodMk (Continuous.subtype_mk (hg.comp continuous_subtype_val) _)
          (Continuous.subtype_mk ?_ _)
        refine continuous_snd.comp_continuousOn tp.continuousOn_toFun
          |>.comp_continuous continuous_subtype_val fun e => ?_
        exact tp.mem_source.mpr (hVsub ((hgW e.1).mp e.2).1).1
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        refine tp.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ fun wi => ?_
        · exact ((hq.comp continuous_subtype_val).comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd)
        · exact tp.mem_target.mpr (hVsub wi.1.2.1).1 },
    fun _ => rfl⟩

/-- **A map of covering spaces with locally connected target is a covering map.** If `p : E → X`
and `q : F → X` are covering maps and `g : E → F` is continuous with `q ∘ g = p`, then `g` is a
covering map provided `F` is locally connected.

Neither total space needs to be connected and `g` need not be surjective; the fibre of `g` over
a point outside its range is empty, which `IsCoveringMap` permits. -/
theorem _root_.IsCoveringMap.of_comp_eq [LocallyConnectedSpace F] (hp : IsCoveringMap p)
    (hq : IsCoveringMap q) (hg : Continuous g) (hgp : q ∘ g = p) : IsCoveringMap g := by
  have hqg : ∀ e, q (g e) = p e := congrFun hgp
  intro f₀
  rcases isEmpty_or_nonempty (p ⁻¹' {q f₀} : Set E) with hemp | hne
  · -- `p` misses `q f₀`, so `g` misses a whole evenly covered neighbourhood of `f₀`.
    obtain ⟨-, U, hxU, hU, -, Hp, -⟩ := hp (q f₀)
    have hpU : p ⁻¹' U = ∅ := Set.isEmpty_coe_sort.mp (Function.isEmpty ⇑Hp)
    have hgU : g ⁻¹' (q ⁻¹' U) = ∅ := by
      rw [← Set.preimage_comp, hgp]
      exact hpU
    have : IsEmpty (g ⁻¹' {f₀} : Set E) := by
      refine Set.isEmpty_coe_sort.mpr (Set.eq_empty_of_subset_empty ?_)
      rw [← hgU]
      rintro e he
      rw [Set.mem_preimage, Set.mem_singleton_iff] at he
      simpa only [Set.mem_preimage, he] using hxU
    exact IsEvenlyCovered.of_preimage_eq_empty _ ((hU.preimage hq.continuous).mem_nhds hxU) hgU
  · have : Nonempty (q ⁻¹' {q f₀} : Set F) := ⟨⟨f₀, rfl⟩⟩
    have := (hp (q f₀)).discreteTopology_fiber
    have := (hq (q f₀)).discreteTopology_fiber
    set tp := (hp (q f₀)).toTrivialization
    set tq := (hq (q f₀)).toTrivialization
    obtain ⟨W, hWsub, hWopen, hf₀W, hWconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp ‹LocallyConnectedSpace F› f₀
        (q ⁻¹' (tp.baseSet ∩ tq.baseSet))
        ((tp.open_baseSet.inter tq.open_baseSet).preimage hq.continuous |>.mem_nhds
          ⟨(hp (q f₀)).mem_toTrivialization_baseSet,
            (hq (q f₀)).mem_toTrivialization_baseSet⟩)
    exact isEvenlyCovered_of_trivialization hq.continuous hg hqg tp tq f₀
      (hq.isOpenMap W hWopen) (hWconn.isPreconnected.image q hq.continuous.continuousOn)
      (fun x ⟨f, hf, hfx⟩ => hfx ▸ hWsub hf) ⟨f₀, hf₀W, rfl⟩

end TauCeti
