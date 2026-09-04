/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP

/-!
# The maximal pro-`p` quotient of a profinite group

The **pro-`p` kernel** `proPKernel p G` of a topological group `G` is the intersection of the
open normal subgroups whose quotient is a `p`-group, and the **maximal pro-`p` quotient** is
`maximalProPQuotient p G = G ⧸ proPKernel p G`. For a profinite `G` this quotient is the
universal pro-`p` group receiving a continuous homomorphism from `G`.

The one substantial step is that `G(p)` really is pro-`p`. This is a compactness argument
rather than a formal one: an open normal subgroup `M` of `G` containing `proPKernel p G`
already contains one member `U` of the defining family, because the sets `U \ M` form a
downward directed family of closed subsets of the compact space `G` with empty intersection,
so one of them is empty. Directedness of the family is where `IsPGroup.quotient_inf` enters.
Once that is known, `G ⧸ M` is a quotient of `G ⧸ U` and hence a `p`-group, and the open
normal subgroups of `G(p)` are exactly the images of such `M`.

The universal property goes the other way and needs no compactness: if `P` is profinite and
pro-`p` and `f : G →* P` is continuous, then for each open normal `V ≤ P` the preimage
`V.comap f` is an open normal subgroup of `G` with `p`-group quotient, so `f` maps
`proPKernel p G` into every `V`, and the open normal subgroups of a profinite group intersect
in `1`.

Everything before the compactness lemma is stated for an arbitrary topological group: the
kernel, its normality, its closedness and its behaviour under continuous homomorphisms all
hold there. Compactness of `G` is assumed exactly where it is used.

## Main definitions

* `TauCeti.proPKernel`: the intersection of the open normal subgroups with `p`-group quotient.
* `TauCeti.maximalProPQuotient`: the quotient `G ⧸ proPKernel p G`, written `G(p)` in prose.
* `TauCeti.maximalProPQuotient.mk`: the canonical quotient homomorphism.
* `TauCeti.maximalProPQuotient.map`: the functorial action on continuous homomorphisms.
* `TauCeti.maximalProPQuotient.lift`: the canonical factorisation of a continuous homomorphism
  to a profinite pro-`p` group.

## Main results

* `TauCeti.isClosed_proPKernel`: the pro-`p` kernel is closed, so `G(p)` is profinite again.
* `TauCeti.proPKernel_eq_top_iff`: the pro-`p` kernel is the whole group exactly when every
  relevant `p`-group quotient is trivial.
* `TauCeti.exists_openNormalSubgroup_isPGroup_le`: an open subgroup containing the pro-`p`
  kernel contains a member of the defining family.
* `TauCeti.isProP_maximalProPQuotient`: `G(p)` is pro-`p`.
* `TauCeti.existsUnique_continuousMonoidHom_maximalProPQuotient`: a continuous homomorphism
  from `G` to a profinite pro-`p` group factors uniquely and continuously through `G(p)`.
* `TauCeti.maximalProPQuotient.lift_comp_map` and `TauCeti.maximalProPQuotient.comp_lift`: that
  factorisation is natural in the source and in the target.
* `TauCeti.proPKernel_eq_bot_iff`: `G` is pro-`p` if and only if its pro-`p` kernel is trivial;
  with `TauCeti.proPKernel_maximalProPQuotient_eq_bot` this is idempotence of `G ↦ G(p)`.
* `TauCeti.map_proPKernel_eq`: continuous multiplicative equivalences preserve the pro-`p`
  kernel.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*.
-/

public section

namespace TauCeti

universe u v w

section Defs

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]

/-- The **pro-`p` kernel** of a topological group `G`: the intersection of the open normal
subgroups of `G` whose quotient is a `p`-group. For profinite `G` it is the kernel of the
universal continuous homomorphism from `G` to a pro-`p` group. -/
def proPKernel : Subgroup G :=
  ⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.1.toSubgroup

/-- The pro-`p` kernel is a normal subgroup. -/
instance proPKernel_normal : (proPKernel p G).Normal :=
  Subgroup.normal_iInf_normal fun U ↦ U.1.isNormal'

/-- The **maximal pro-`p` quotient** `G(p) = G ⧸ proPKernel p G`. -/
abbrev maximalProPQuotient : Type u := G ⧸ proPKernel p G

/-- The canonical homomorphism from `G` to its maximal pro-`p` quotient. -/
abbrev maximalProPQuotient.mk : G →* maximalProPQuotient p G :=
  QuotientGroup.mk' (proPKernel p G)

/-- The canonical quotient homomorphism sends an element to its quotient class. -/
@[simp]
theorem maximalProPQuotient.mk_apply (x : G) :
    maximalProPQuotient.mk p G x = QuotientGroup.mk x :=
  rfl

/-- The canonical homomorphism to the maximal pro-`p` quotient is surjective. -/
theorem maximalProPQuotient.mk_surjective :
    Function.Surjective (maximalProPQuotient.mk p G) :=
  QuotientGroup.mk'_surjective (proPKernel p G)

/-- The canonical homomorphism to the maximal pro-`p` quotient is continuous. -/
theorem maximalProPQuotient.continuous_mk : Continuous (maximalProPQuotient.mk p G) :=
  QuotientGroup.continuous_mk

end Defs

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- Membership in the pro-`p` kernel, unfolded over the defining family. -/
theorem mem_proPKernel_iff {x : G} :
    x ∈ proPKernel p G ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → x ∈ U.toSubgroup := by
  rw [proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The pro-`p` kernel is contained in every open normal subgroup with `p`-group quotient. -/
theorem proPKernel_le {U : OpenNormalSubgroup G} (hU : IsPGroup p (G ⧸ U.toSubgroup)) :
    proPKernel p G ≤ U.toSubgroup :=
  fun _ hx ↦ mem_proPKernel_iff.mp hx U hU

/-- The pro-`p` kernel is closed, so its quotient is profinite when `G` is profinite. -/
instance isClosed_proPKernel [IsTopologicalGroup G] :
    IsClosed ((proPKernel p G : Subgroup G) : Set G) := by
  rw [proPKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun U ↦ U.1.toOpenSubgroup.isClosed

/-! ### Trivial maximal quotients -/

/-- The pro-`p` kernel is the whole group exactly when every open normal subgroup with
`p`-group quotient is the whole group. Equivalently, `G` has no nontrivial continuous
`p`-group quotient. -/
theorem proPKernel_eq_top_iff : proPKernel p G = ⊤ ↔
    ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → U.toSubgroup = ⊤ := by
  rw [proPKernel, iInf_eq_top]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The maximal pro-`p` quotient is trivial exactly when the pro-`p` kernel is the whole
group. -/
theorem maximalProPQuotient.subsingleton_iff :
    Subsingleton (maximalProPQuotient p G) ↔ proPKernel p G = ⊤ :=
  QuotientGroup.subsingleton_iff

/-- If `p` does not divide the cardinality of `G`, then its pro-`p` kernel is the whole group.
For prime `p` this hypothesis forces `G` to be finite. -/
theorem proPKernel_eq_top_of_not_dvd_card [Fact p.Prime]
    (hcard : ¬ p ∣ Nat.card G) : proPKernel p G = ⊤ := by
  rw [proPKernel_eq_top_iff]
  intro U hU
  rw [← QuotientGroup.subsingleton_iff]
  apply (Nat.card_eq_one_iff_unique.mp ?_).1
  exact hU.card_eq_or_dvd.resolve_right fun hp ↦
    hcard (hp.trans (Subgroup.card_quotient_dvd_card U.toSubgroup))

/-- If `p` does not divide the cardinality of `G`, then its maximal pro-`p` quotient is
trivial. For prime `p` this hypothesis forces `G` to be finite. -/
theorem maximalProPQuotient.subsingleton_of_not_dvd_card [Fact p.Prime]
    (hcard : ¬ p ∣ Nat.card G) : Subsingleton (maximalProPQuotient p G) :=
  maximalProPQuotient.subsingleton_iff.mpr (proPKernel_eq_top_of_not_dvd_card hcard)

/-! ### Functoriality -/

/-- A continuous homomorphism carries the pro-`p` kernel into the pro-`p` kernel. -/
theorem proPKernel_le_comap (f : G →* H) (hf : Continuous f) :
    proPKernel p G ≤ (proPKernel p H).comap f := by
  intro x hx
  rw [Subgroup.mem_comap, mem_proPKernel_iff]
  intro V hV
  exact mem_proPKernel_iff.mp hx
    ⟨V.toOpenSubgroup.comap f hf, V.isNormal'.comap f⟩ (hV.quotient_comap f)

/-- The image of the pro-`p` kernel under a continuous homomorphism lies in the pro-`p`
kernel of the target. -/
theorem map_proPKernel_le (f : G →* H) (hf : Continuous f) :
    (proPKernel p G).map f ≤ proPKernel p H :=
  Subgroup.map_le_iff_le_comap.mpr (proPKernel_le_comap f hf)

/-- Continuous multiplicative equivalences identify the pro-`p` kernels of their source and
target. In particular, the pro-`p` kernel is characteristic under continuous automorphisms. -/
theorem map_proPKernel_eq (e : G ≃ₜ* H) :
    (proPKernel p G).map e.toMulEquiv.toMonoidHom = proPKernel p H := by
  refine le_antisymm (map_proPKernel_le _ e.continuous) fun x hx ↦ ?_
  have hsymm : e.symm x ∈ proPKernel p G :=
    map_proPKernel_le e.symm.toMulEquiv.toMonoidHom e.symm.continuous
      (Subgroup.mem_map_of_mem _ hx)
  exact ⟨e.symm x, hsymm, e.apply_symm_apply x⟩

/-- The map induced on maximal pro-`p` quotients by a continuous homomorphism. -/
def maximalProPQuotient.map (f : G →* H) (hf : Continuous f) :
    maximalProPQuotient p G →* maximalProPQuotient p H :=
  QuotientGroup.map (proPKernel p G) (proPKernel p H) f (proPKernel_le_comap f hf)

/-- The induced map on maximal pro-`p` quotients is computed on classes by `f`. -/
@[simp]
theorem maximalProPQuotient.map_mk (f : G →* H) (hf : Continuous f) (x : G) :
    maximalProPQuotient.map (p := p) f hf (x : maximalProPQuotient p G) =
      maximalProPQuotient.mk p H (f x) := by
  rfl

/-- The induced map on maximal pro-`p` quotients is continuous. -/
theorem maximalProPQuotient.continuous_map (f : G →* H) (hf : Continuous f) :
    Continuous (maximalProPQuotient.map (p := p) f hf) :=
  (QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hf)

/-- Functoriality: the identity induces the identity. -/
@[simp]
theorem maximalProPQuotient.map_id :
    maximalProPQuotient.map (p := p) (MonoidHom.id G) continuous_id = MonoidHom.id _ := by
  ext x
  rfl

/-- Functoriality: the induced maps compose. -/
@[simp]
theorem maximalProPQuotient.map_comp {K : Type w} [Group K] [TopologicalSpace K] (f : G →* H)
    (hf : Continuous f) (g : H →* K) (hg : Continuous g) :
    maximalProPQuotient.map (p := p) (g.comp f) (hg.comp hf) =
      (maximalProPQuotient.map g hg).comp (maximalProPQuotient.map f hf) := by
  ext x
  rfl

/-! ### The compactness step -/

section Compact

variable [IsTopologicalGroup G] [CompactSpace G]

/-- An open subgroup containing the pro-`p` kernel contains an open normal subgroup with
`p`-group quotient. -/
theorem exists_openNormalSubgroup_isPGroup_le {M : Subgroup G} (hM : IsOpen (M : Set G))
    (hKM : proPKernel p G ≤ M) :
    ∃ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) ∧ U.toSubgroup ≤ M := by
  -- The defining family, and the closed sets it cuts out outside `M`.
  let S : Type u := {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}
  let t : S → Set G := fun U ↦ (U.1 : Set G) \ (M : Set G)
  -- The family contains the whole group, so it is nonempty.
  let topU : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }
  let _ : topU.toSubgroup.Normal := topU.isNormal'
  have _ : Subsingleton (G ⧸ topU.toSubgroup) := QuotientGroup.subsingleton_quotient_top
  have htopP : IsPGroup p (G ⧸ topU.toSubgroup) := .of_subsingleton p _
  have htop : S := ⟨topU, htopP⟩
  have hne : Nonempty S := ⟨htop⟩
  suffices h : ∃ U : S, t U = ∅ by
    obtain ⟨U, hU⟩ := h
    exact ⟨U.1, U.2, fun _ hx ↦ Set.sdiff_eq_empty.mp hU hx⟩
  by_contra hcon
  have hnonempty : ∀ U : S, (t U).Nonempty := fun U ↦ by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h ↦ hcon ⟨U, h⟩
  have hclosed : ∀ U : S, IsClosed (t U) := fun U ↦ (U.1.toOpenSubgroup.isClosed).sdiff hM
  -- The family is closed under intersection, so the sets `t U` are downward directed.
  have hdirected : Directed (· ⊇ ·) t := fun U V ↦
    ⟨⟨U.1 ⊓ V.1, U.2.quotient_inf V.2⟩,
      Set.sdiff_subset_sdiff_left (SetLike.coe_subset_coe.mpr inf_le_left),
      Set.sdiff_subset_sdiff_left (SetLike.coe_subset_coe.mpr inf_le_right)⟩
  -- Cantor: their intersection is nonempty, yet it lies in `proPKernel p G \ M = ∅`.
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    hdirected hnonempty (fun U ↦ (hclosed U).isCompact) hclosed
  rw [Set.mem_iInter] at hx
  exact (hx htop).2 (hKM (mem_proPKernel_iff.mpr fun U hU ↦ (hx ⟨U, hU⟩).1))

/-- An open normal subgroup containing the pro-`p` kernel has `p`-group quotient. -/
theorem isPGroup_quotient_of_proPKernel_le {U : OpenNormalSubgroup G}
    (hU : proPKernel p G ≤ U.toSubgroup) : IsPGroup p (G ⧸ U.toSubgroup) := by
  obtain ⟨V, hV, hVU⟩ := exists_openNormalSubgroup_isPGroup_le U.toOpenSubgroup.isOpen hU
  have hle : V.toSubgroup ≤ (U.toSubgroup).comap (MonoidHom.id G) := by
    simpa using hVU
  refine hV.of_surjective (QuotientGroup.map V.toSubgroup U.toSubgroup (MonoidHom.id G) hle) ?_
  exact QuotientGroup.map_surjective_of_surjective V.toSubgroup U.toSubgroup (MonoidHom.id G)
    (QuotientGroup.mk'_surjective U.toSubgroup) hle

/-- For an open normal subgroup of a compact group, containing the pro-`p` kernel is the same
as having a `p`-group quotient. -/
theorem proPKernel_le_iff_isPGroup_quotient {U : OpenNormalSubgroup G} :
    proPKernel p G ≤ U.toSubgroup ↔ IsPGroup p (G ⧸ U.toSubgroup) :=
  ⟨isPGroup_quotient_of_proPKernel_le, proPKernel_le⟩

/-- **The maximal pro-`p` quotient is pro-`p`.** -/
theorem isProP_maximalProPQuotient : IsProP p (maximalProPQuotient p G) := by
  refine isProP_iff.mpr fun M ↦ ?_
  let π : G →* maximalProPQuotient p G := maximalProPQuotient.mk p G
  let M' : OpenNormalSubgroup G :=
    { toOpenSubgroup := M.toOpenSubgroup.comap π QuotientGroup.continuous_mk
      isNormal' := M.isNormal'.comap π }
  let _ : M'.toSubgroup.Normal := M'.isNormal'
  have hmem : ∀ x : G, x ∈ M'.toSubgroup ↔ π x ∈ M.toSubgroup := fun _ ↦ Iff.rfl
  have hKM' : proPKernel p G ≤ M'.toSubgroup := by
    intro x hx
    rw [hmem]
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact one_mem _
  have hM' : IsPGroup p (G ⧸ M'.toSubgroup) := isPGroup_quotient_of_proPKernel_le hKM'
  let q := (QuotientGroup.mk' M.toSubgroup).comp π
  have hq : M'.toSubgroup ≤ q.ker := fun x hx ↦
    (QuotientGroup.eq_one_iff (π x)).mpr ((hmem x).mp hx)
  refine hM'.of_surjective (QuotientGroup.lift M'.toSubgroup q hq) ?_
  exact QuotientGroup.lift_surjective_of_surjective M'.toSubgroup q
    ((QuotientGroup.mk'_surjective M.toSubgroup).comp
      (maximalProPQuotient.mk_surjective p G)) hq

end Compact

/-! ### The universal property -/

section UniversalProperty

variable {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- A continuous homomorphism to a profinite pro-`p` group kills the pro-`p` kernel. -/
theorem proPKernel_le_ker (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    proPKernel p G ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun V ↦ ?_
  exact mem_proPKernel_iff.mp hx ⟨V.toOpenSubgroup.comap f hf, V.isNormal'.comap f⟩
    ((isProP_iff.mp hP V).quotient_comap f)

/-- The canonical factorisation of a continuous homomorphism to a profinite pro-`p` group
through the maximal pro-`p` quotient. -/
def maximalProPQuotient.lift (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    maximalProPQuotient p G →* P :=
  QuotientGroup.lift (proPKernel p G) f fun _ hx ↦ proPKernel_le_ker hP f hf hx

/-- The factorisation through the maximal pro-`p` quotient computes as `f` on classes. -/
@[simp]
theorem maximalProPQuotient.lift_mk (hP : IsProP p P) (f : G →* P) (hf : Continuous f) (x : G) :
    maximalProPQuotient.lift hP f hf (x : maximalProPQuotient p G) = f x := by
  rfl

/-- The factorisation through the maximal pro-`p` quotient recovers `f`. -/
@[simp]
theorem maximalProPQuotient.lift_comp_mk (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    (maximalProPQuotient.lift hP f hf).comp (maximalProPQuotient.mk p G) = f := by
  ext x
  rfl

/-- The factorisation through the maximal pro-`p` quotient is continuous. -/
theorem maximalProPQuotient.continuous_lift (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    Continuous (maximalProPQuotient.lift hP f hf) :=
  (QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr hf

/-- The factorisation through the maximal pro-`p` quotient is the only homomorphism restricting
to `f` along the quotient map. -/
theorem maximalProPQuotient.lift_unique (hP : IsProP p P) (f : G →* P) (hf : Continuous f)
    {g : maximalProPQuotient p G →* P} (hg : ∀ x : G, g (maximalProPQuotient.mk p G x) = f x) :
    g = maximalProPQuotient.lift hP f hf := by
  ext x
  exact hg x

/-- Naturality in the source: the factorisation of `f ∘ u` is the factorisation of `f`
precomposed with the map induced by `u`. -/
theorem maximalProPQuotient.lift_comp_map {G' : Type w} [Group G'] [TopologicalSpace G']
    (hP : IsProP p P) (f : G →* P) (hf : Continuous f) (u : G' →* G) (hu : Continuous u) :
    (maximalProPQuotient.lift hP f hf).comp (maximalProPQuotient.map (p := p) u hu) =
      maximalProPQuotient.lift hP (f.comp u) (hf.comp hu) := by
  ext x
  rfl

/-- Naturality in the target: postcomposing the factorisation of `f` with a continuous
homomorphism of profinite pro-`p` groups gives the factorisation of the composite. -/
theorem maximalProPQuotient.comp_lift {Q : Type w} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProP p P)
    (hQ : IsProP p Q) (f : G →* P) (hf : Continuous f) (v : P →* Q) (hv : Continuous v) :
    v.comp (maximalProPQuotient.lift hP f hf) =
      maximalProPQuotient.lift hQ (v.comp f) (hv.comp hf) := by
  ext x
  rfl

/-- **The universal property of the maximal pro-`p` quotient.** A continuous homomorphism to a
profinite pro-`p` group factors uniquely and continuously through the canonical quotient map. -/
theorem existsUnique_continuousMonoidHom_maximalProPQuotient (hP : IsProP p P) (f : G →* P)
    (hf : Continuous f) :
    ∃! g : maximalProPQuotient p G →* P,
      Continuous g ∧ ∀ x : G, g (maximalProPQuotient.mk p G x) = f x :=
  ⟨maximalProPQuotient.lift hP f hf,
    ⟨maximalProPQuotient.continuous_lift hP f hf, maximalProPQuotient.lift_mk hP f hf⟩,
    fun _ hg ↦ maximalProPQuotient.lift_unique hP f hf hg.2⟩

end UniversalProperty

/-! ### Pro-`p` groups and idempotence -/

section Idempotence

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A profinite group is pro-`p` exactly when its pro-`p` kernel is trivial. -/
theorem proPKernel_eq_bot_iff : proPKernel p G = ⊥ ↔ IsProP p G := by
  refine ⟨fun h ↦ isProP_iff.mpr fun U ↦
      isPGroup_quotient_of_proPKernel_le (h.trans_le bot_le), fun hG ↦ ?_⟩
  refine le_antisymm ?_ bot_le
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := G)]
  exact le_iInf fun U ↦ proPKernel_le (isProP_iff.mp hG U)

/-- The pro-`p` kernel of a profinite pro-`p` group is trivial. -/
theorem IsProP.proPKernel_eq_bot (hG : IsProP p G) : proPKernel p G = ⊥ :=
  proPKernel_eq_bot_iff.mpr hG

/-- The canonical continuous multiplicative equivalence from the maximal pro-`p` quotient of a
profinite pro-`p` group to the group itself. -/
def maximalProPQuotient.equivOfIsProP (hG : IsProP p G) :
    maximalProPQuotient p G ≃ₜ* G :=
  ContinuousMulEquiv.mk
    ((QuotientGroup.quotientMulEquivOfEq hG.proPKernel_eq_bot).trans
      QuotientGroup.quotientBot)
    ((QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr continuous_id)
    (maximalProPQuotient.continuous_mk p G)

/-- The canonical equivalence from a pro-`p` group's maximal pro-`p` quotient sends each class
to its representative. -/
@[simp]
theorem maximalProPQuotient.equivOfIsProP_mk (hG : IsProP p G) (x : G) :
    maximalProPQuotient.equivOfIsProP hG (x : maximalProPQuotient p G) = x :=
  (rfl)

/-- **Idempotence.** The pro-`p` kernel of a maximal pro-`p` quotient is trivial. -/
theorem proPKernel_maximalProPQuotient_eq_bot :
    proPKernel p (maximalProPQuotient p G) = ⊥ :=
  proPKernel_eq_bot_iff.mpr isProP_maximalProPQuotient

/-- **Idempotence.** Applying the maximal pro-`p` quotient construction twice gives a group
canonically continuously equivalent to applying it once. -/
def maximalProPQuotient.idempotentEquiv :
    maximalProPQuotient p (maximalProPQuotient p G) ≃ₜ* maximalProPQuotient p G :=
  maximalProPQuotient.equivOfIsProP isProP_maximalProPQuotient

/-- The idempotence equivalence sends each class to its representative. -/
@[simp]
theorem maximalProPQuotient.idempotentEquiv_mk (x : maximalProPQuotient p G) :
    maximalProPQuotient.idempotentEquiv
      (x : maximalProPQuotient p (maximalProPQuotient p G)) = x :=
  (rfl)

end Idempotence

end TauCeti
