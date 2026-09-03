/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient

/-!
# The balanced product of a quotient covering map with a discrete set

Let a group `G` act on a space `E` so that `q : E → X` presents `X` as the quotient `E / G` in
the strong sense of Mathlib's `IsQuotientCoveringMap`: the fibres of `q` are the orbits, and every
point of `E` has a neighbourhood whose `G`-translates are pairwise disjoint. For a discrete
`G`-set `A`, the *balanced product* `BalancedProduct G E A` is the quotient of `E × A` by the
diagonal action of `G`. Since `q` is invariant along the first factor it descends to

`BalancedProduct.proj A : BalancedProduct G E A → X`,

and the theorem of this file is that this projection is a covering map, with fibre `A`.

Neither space is assumed connected, and no local connectedness of `X` is needed. Over the base
set `q '' U` cut out by a set `U` whose `G`-translates are pairwise disjoint, the sheets of the
projection are the images of `U ×ˢ {a}`, one for each `a : A`, and each defining property of a
sheet comes straight from the disjointness of those translates: two points of `U` with the same
class differ by a group element carrying `U` into itself, hence by the identity.

The intended reading is the cover of `X` attached to a set acted on by the deck group of a
regular cover. For `E` the universal cover of `X` and `G` its fundamental group, this is the
covering space attached to an arbitrary `π₁(X, x₀)`-set; no transitivity, and hence no
connectedness of the resulting cover, is assumed. The transitive case `A = G ⧸ H`, where the
balanced product is `E / H`, is `TauCeti.IsQuotientCoveringMap.isCoveringMap_of_comp`, proved
there for an abstract presentation of `E / H` rather than for a fixed model.

## Main declarations

* `TauCeti.BalancedProduct`: the quotient of `E × A` by the diagonal action of `G`.
* `TauCeti.isQuotientCoveringMap_quotientMk_of_smul_disjoint`: an action with locally pairwise
  disjoint translates presents its orbit space as a quotient covering map.
* `TauCeti.BalancedProduct.isQuotientCoveringMap_mk`: the class map `E × A → E ×_G A` is one such.
* `TauCeti.BalancedProduct.isCoveringMap_proj`: **the balanced product of a quotient covering map
  with a discrete set is a covering map.**
* `TauCeti.BalancedProduct.fiberEquiv`: its fibre over `q e` is `A`, through `a ↦ ⟦(e, a)⟧`. This
  last bijection is purely algebraic: it uses no topology, only that the action on `E` is free and
  that the fibres of `q` are its orbits.

## References

The `IsQuotientCoveringMap` interface used here — the predicate itself, its `disjoint` and
`apply_eq_iff_mem_orbit` fields, `IsQuotientCoveringMap.isOpenQuotientMap`, and
`IsOpen.trivializationDiscrete` — is Junyan Xu's, in `Mathlib/Topology/Covering/Quotient.lean`
and `Mathlib/Topology/Covering/Basic.lean`. The sheet bookkeeping follows the subgroup case in
`TauCeti/Topology/Covering/Quotient.lean`.
-/

public section

namespace TauCeti

open Pointwise Topology

section OrbitQuotient

variable {E : Type*} [TopologicalSpace E] {G : Type*} [Group G] [MulAction G E]

/-- **An action whose translates are locally pairwise disjoint presents its orbit space as a
quotient covering map.** This is the free, not necessarily properly discontinuous, form of
Mathlib's `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`: no local compactness
or separation of `E` is assumed. -/
theorem isQuotientCoveringMap_quotientMk_of_smul_disjoint [ContinuousConstSMul G E]
    (hdisj : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G E)) G where
  __ := isQuotientMap_quotient_mk'
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := hdisj

end OrbitQuotient

variable {E X A : Type*} {G : Type*} [Group G] [MulAction G E] [MulAction G A] {q : E → X}

/-- The **balanced product** `E ×_G A` of a `G`-space `E` and a `G`-set `A`: the quotient of
`E × A` by the diagonal action of `G`. -/
abbrev BalancedProduct (G E A : Type*) [Group G] [MulAction G E] [MulAction G A] : Type _ :=
  Quotient (MulAction.orbitRel G (E × A))

namespace BalancedProduct

/-- The class of a pair in the balanced product. -/
abbrev mk (G : Type*) [Group G] [MulAction G E] [MulAction G A] (e : E) (a : A) :
    BalancedProduct G E A :=
  Quotient.mk (MulAction.orbitRel G (E × A)) (e, a)

/-- Moving a point of `E × A` by `g` in the first coordinate is the same as moving it by `g⁻¹`
in the second. -/
@[simp]
theorem mk_smul_left (g : G) (e : E) (a : A) : mk G (g • e) a = mk G e (g⁻¹ • a) :=
  Quotient.sound ⟨g, by simp⟩

variable (hq : ∀ (g : G) (e : E), q (g • e) = q e)

variable (A) in
/-- A `G`-invariant map `q : E → X` descends to the balanced product. -/
def proj : BalancedProduct G E A → X :=
  Quotient.lift (fun p => q p.1) fun _ _ h => by
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact hq g _

variable (A) in
@[simp]
theorem proj_mk (e : E) (a : A) : proj A hq (mk G e a) = q e :=
  (rfl)

section Covering

variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]

variable (A) in
/-- The descended projection is continuous when `q` is. -/
theorem continuous_proj (hqc : Continuous q) : Continuous (proj A hq) :=
  (hqc.comp continuous_fst).quotient_lift _

variable (A) in
/-- The class map onto the balanced product is a quotient covering map for the diagonal action,
as soon as the action on `E` is one and the action on `A` is continuous: a neighbourhood `U` of
`e` with pairwise disjoint translates gives the neighbourhood `U ×ˢ univ` of `(e, a)`, whose
translates are again pairwise disjoint. -/
theorem isQuotientCoveringMap_mk [ContinuousConstSMul G A]
    (hqc : IsQuotientCoveringMap q G) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel G (E × A)) : E × A → BalancedProduct G E A) G := by
  have : ContinuousConstSMul G E := hqc.toContinuousConstSMul
  refine isQuotientCoveringMap_quotientMk_of_smul_disjoint fun p => ?_
  obtain ⟨U, hU, hdisj⟩ := hqc.disjoint p.1
  refine ⟨U ×ˢ Set.univ, prod_mem_nhds hU Filter.univ_mem, fun g hg => hdisj g ?_⟩
  obtain ⟨z, ⟨w, hw, hwz⟩, hz⟩ := hg
  exact ⟨z.1, ⟨w.1, hw.1, congrArg Prod.fst hwz⟩, hz.1⟩

variable [DiscreteTopology A]

variable (A) in
/-- The evenly covered neighbourhood of `q e` cut out by a set `U` around `e` whose `G`-translates
are pairwise disjoint. Its sheets are the classes of `U ×ˢ {a}`, indexed by `a : A`. -/
private theorem isEvenlyCovered_of_smul_disjoint [Nonempty A] (hqc : IsQuotientCoveringMap q G)
    {U : Set E} (hUo : IsOpen U) (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) {e : E}
    (heU : e ∈ U) :
    IsEvenlyCovered (proj A hq) (q e) (proj A hq ⁻¹' {q e}) := by
  let _ : ContinuousConstSMul G A := ⟨fun _ => continuous_of_discreteTopology⟩
  have hcsG : ContinuousConstSMul G E := hqc.toContinuousConstSMul
  have ht := isQuotientCoveringMap_mk A hqc
  have hrc : Continuous (proj A hq) := continuous_proj A hq hqc.continuous
  have hVo : IsOpen (q '' U) := hqc.isOpenQuotientMap.isOpenMap _ hUo
  set S : A → Set (BalancedProduct G E A) :=
    fun a => Quotient.mk (MulAction.orbitRel G (E × A)) '' (U ×ˢ {a}) with hS
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    ht.isOpenQuotientMap.isOpenMap _ (hUo.prod (isOpen_discrete _))
  -- A point of the sheet indexed by `a` is the class of `(u, a)` for a unique `u ∈ U`.
  have hmemS : ∀ (a : A) (z : BalancedProduct G E A), z ∈ S a ↔ ∃ u ∈ U, mk G u a = z := by
    intro a z
    simp only [hS]
    constructor
    · rintro ⟨⟨u, a'⟩, ⟨hu, ha'⟩, rfl⟩
      obtain rfl : a' = a := ha'
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, a), ⟨hu, rfl⟩, rfl⟩
  -- Two points of `U` with the same class agree, together with their labels.
  have hkey : ∀ {u u' : E} {a a' : A}, u ∈ U → u' ∈ U → mk G u a = mk G u' a' →
      u = u' ∧ a = a' := by
    intro u u' a a' hu hu' hEq
    obtain ⟨g, hg⟩ := Quotient.eq''.mp hEq
    have hg1 : g • (u', a') = (u, a) := hg
    have hgu : g • u' = u := congrArg Prod.fst hg1
    rw [hdisj g ⟨u, ⟨u', hu', hgu⟩, hu⟩, one_smul] at hg1
    exact ⟨(Prod.ext_iff.mp hg1).1.symm, (Prod.ext_iff.mp hg1).2.symm⟩
  have : Nonempty (X → BalancedProduct G E A) := ⟨fun _ => mk G e (Classical.arbitrary A)⟩
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (IsEvenlyCovered.of_trivialization (f := proj A hq)
      (t := hVo.trivializationDiscrete S (q '' U) ?_ ?_ ?_ ?_ ?_) ⟨e, heU, rfl⟩)
  · -- Openness inside the base set is detected on any single sheet.
    intro a W hWV
    refine ⟨fun hW => (hW.preimage hrc).inter (hSo a), fun hW => ?_⟩
    -- The slice at `a` of the preimage of that open set, cut down to `U`, is `q ⁻¹' W ∩ U`.
    have hslice : IsOpen (q ⁻¹' W ∩ U) := by
      have hopen : IsOpen (Quotient.mk (MulAction.orbitRel G (E × A)) ⁻¹'
          (proj A hq ⁻¹' W ∩ S a)) := hW.preimage continuous_quotient_mk'
      have hcont : Continuous fun u : E => (u, a) := continuous_id.prodMk continuous_const
      have heq : q ⁻¹' W ∩ U = ((fun u : E => (u, a)) ⁻¹'
          (Quotient.mk (MulAction.orbitRel G (E × A)) ⁻¹' (proj A hq ⁻¹' W ∩ S a))) ∩ U := by
        ext u
        constructor
        · rintro ⟨hqu, hu⟩
          exact ⟨⟨hqu, (hmemS a _).mpr ⟨u, hu, rfl⟩⟩, hu⟩
        · rintro ⟨⟨hw, -⟩, hu⟩
          exact ⟨hw, hu⟩
      rw [heq]
      exact (hopen.preimage hcont).inter hUo
    rw [← hqc.toIsQuotientMap.isOpen_preimage]
    -- The preimage of `W` is covered by the translates of that slice, because `W ⊆ q '' U`.
    have hcover : q ⁻¹' W = ⋃ k : G, k • (q ⁻¹' W ∩ U) := by
      refine Set.Subset.antisymm (fun w hw => ?_) (Set.iUnion_subset fun k w hw => ?_)
      · obtain ⟨u, hu, hqu⟩ := hWV hw
        obtain ⟨m, hm⟩ := hqc.apply_eq_iff_mem_orbit.mp hqu.symm
        refine Set.mem_iUnion.mpr ⟨m, Set.mem_smul_set.mpr ⟨u, ⟨?_, hu⟩, hm⟩⟩
        rw [Set.mem_preimage, hqu]
        exact hw
      · obtain ⟨w', ⟨hw', -⟩, rfl⟩ := Set.mem_smul_set.mp hw
        rw [Set.mem_preimage, hqc.map_smul]
        exact hw'
    rw [hcover]
    exact isOpen_iUnion fun k => hslice.smul k
  · -- The projection is injective on each sheet.
    intro a z hz z' hz' hzz'
    obtain ⟨u, hu, rfl⟩ := (hmemS a z).mp hz
    obtain ⟨u', hu', rfl⟩ := (hmemS a z').mp hz'
    rw [proj_mk, proj_mk] at hzz'
    obtain ⟨m, hm⟩ := hqc.apply_eq_iff_mem_orbit.mp hzz'
    have hm1 : m • u' = u := hm
    rw [hdisj m ⟨u, ⟨u', hu', hm1⟩, hu⟩, one_smul] at hm1
    rw [hm1]
  · -- Each sheet surjects onto the base set.
    rintro a v ⟨u, hu, rfl⟩
    exact ⟨mk G u a, (hmemS a _).mpr ⟨u, hu, rfl⟩, proj_mk A hq u a⟩
  · -- Distinct sheets are disjoint.
    intro a a' hne
    refine Set.disjoint_left.mpr fun z hz hz' => hne ?_
    obtain ⟨u, hu, rfl⟩ := (hmemS a z).mp hz
    obtain ⟨u', hu', hEq⟩ := (hmemS a' _).mp hz'
    exact (hkey hu' hu hEq).2.symm
  · -- The sheets exhaust the preimage of the base set.
    intro z hz
    obtain ⟨⟨w, b⟩, rfl⟩ := ht.surjective z
    rw [Set.mem_preimage] at hz
    obtain ⟨u, hu, hqu⟩ := hz
    obtain ⟨m, hm⟩ := hqc.apply_eq_iff_mem_orbit.mp hqu.symm
    have hmu : m • u = w := hm
    refine Set.mem_iUnion.mpr ⟨m⁻¹ • b, (hmemS _ _).mpr ⟨u, hu, ?_⟩⟩
    rw [← mk_smul_left m u b, hmu]

variable (A) in
/-- **The balanced product of a quotient covering map with a discrete set is a covering map.**

If `q : E → X` presents `X` as the quotient of `E` by a group `G` in the sense of
`IsQuotientCoveringMap`, and `A` is a discrete `G`-set, then the descended projection of the
balanced product `E ×_G A` to `X` is a covering map. -/
theorem isCoveringMap_proj (hqc : IsQuotientCoveringMap q G) : IsCoveringMap (proj A hq) := by
  let _ : ContinuousConstSMul G A := ⟨fun _ => continuous_of_discreteTopology⟩
  cases isEmpty_or_nonempty A with
  | inl _ =>
    have : IsEmpty (BalancedProduct G E A) := ⟨fun z => by
      obtain ⟨p, -⟩ := (isQuotientCoveringMap_mk A hqc).surjective z
      exact isEmptyElim p.2⟩
    exact IsCoveringMap.of_isEmpty _
  | inr _ =>
    intro x
    obtain ⟨e, rfl⟩ := hqc.surjective x
    obtain ⟨U, hU, hdisj⟩ := hqc.disjoint e
    refine isEvenlyCovered_of_smul_disjoint A hq hqc isOpen_interior (fun g hg => hdisj g ?_)
      (mem_interior_iff_mem_nhds.mpr hU)
    exact hg.mono (Set.inter_subset_inter (Set.image_mono interior_subset) interior_subset)

end Covering

section Fiber

variable (A) in
/-- **The fibre of the balanced product over `x` is `A`.** The bijection sends `a` to the class
of `(e, a)`; it depends on the chosen point `e` of the fibre of `q`.

Only two consequences of `q` being a quotient covering map are used, and neither involves a
topology: the action on `E` is free, and points of `E` with the same image lie in one orbit. -/
noncomputable def fiberEquiv [IsCancelSMul G E]
    (hfiber : ∀ {e₁ e₂ : E}, q e₁ = q e₂ → e₁ ∈ MulAction.orbit G e₂) {x : X} (e : q ⁻¹' {x}) :
    A ≃ proj A hq ⁻¹' {x} := by
  refine Equiv.ofBijective (fun a => ⟨mk G (e : E) a, ?_⟩) ⟨?_, ?_⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff, proj_mk]
    exact e.2
  · intro a a' hEq
    obtain ⟨g, hg⟩ := Quotient.eq''.mp (congrArg Subtype.val hEq)
    have hg1 : g • ((e : E), a') = ((e : E), a) := hg
    rw [IsCancelSMul.eq_one_of_smul (congrArg Prod.fst hg1), one_smul] at hg1
    exact (Prod.ext_iff.mp hg1).2.symm
  · rintro ⟨z, hz⟩
    obtain ⟨⟨w, b⟩, rfl⟩ := Quotient.mk''_surjective z
    rw [Set.mem_preimage, Set.mem_singleton_iff, proj_mk] at hz
    obtain ⟨g, hg⟩ := hfiber (hz.trans e.2.symm)
    have hge : g • (e : E) = w := hg
    refine ⟨g⁻¹ • b, Subtype.ext ?_⟩
    -- `fiberEquiv_apply_coe` is only available after this `Equiv.ofBijective` construction.
    -- Here `change` exposes its defining map after `Subtype.ext` removes the fibre wrapper.
    change mk G (e : E) (g⁻¹ • b) = mk G w b
    rw [← mk_smul_left g (e : E) b, hge]

variable (A) in
/-- The fibre bijection of the balanced product sends `a` to the class of `(e, a)`. -/
@[simp]
theorem fiberEquiv_apply_coe [IsCancelSMul G E]
    (hfiber : ∀ {e₁ e₂ : E}, q e₁ = q e₂ → e₁ ∈ MulAction.orbit G e₂) {x : X} (e : q ⁻¹' {x})
    (a : A) :
    (fiberEquiv A hq hfiber e a : BalancedProduct G E A) = mk G (e : E) a :=
  (rfl)

end Fiber

end BalancedProduct

end TauCeti
