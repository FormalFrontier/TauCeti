/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Discrete modules over a profinite group

A *discrete `G`-module* is an abelian group `M` with a continuous action of a topological group
`G`, where `M` carries the discrete topology. These are the coefficients of continuous cochain
cohomology. This file develops the two facts about them that every later statement rests on: the
action of a profinite group on a discrete module is locally trivial, and the invariants of an open
normal subgroup form a module over the finite quotient.

The unbundled classes `[AddGroup M] [DistribMulAction G M] [DiscreteTopology M]
[ContinuousSMul G M]` are the hypotheses used throughout, rather than a new bundling structure, so
that instance search composes them freely and each statement carries exactly the classes it needs.
Profiniteness is likewise `[CompactSpace G] [TotallyDisconnectedSpace G]` on a topological group and
not the category `ProfiniteGrp`.

The invariant subgroup `M ^ H` is Mathlib's `FixedPoints.addSubgroup H M`; no second name for it is
introduced here. What is new is its `G`-module structure for normal `H`, the descent of that
structure to `G ⧸ H`, and the finite-quotient theory below.

## Main results

* `TauCeti.exists_openNormalSubgroup_smul_eq`: over a profinite group, every point of a discrete
  `G`-set is fixed by an open normal subgroup.
* `TauCeti.actionKernel`: the kernel of an action on a *finite* discrete `G`-set, as an open normal
  subgroup, together with `TauCeti.quotientToPermHom` exhibiting the action as one of the finite
  group `G ⧸ actionKernel G X`.
* `TauCeti.iUnion_coe_fixedPoints_addSubgroup_eq_univ` and
  `TauCeti.iSup_fixedPoints_addSubgroup_eq_top`: a discrete module over a profinite group is the
  union of the invariants of the open normal subgroups, and
  `TauCeti.directed_fixedPoints_addSubgroup` says that union is directed.
* `TauCeti.distribMulActionFixedPoints` and `TauCeti.distribMulActionQuotientFixedPoints`: the
  `G`- and `G ⧸ H`-module structures on `M ^ H` for normal `H`, the additive counterparts of
  Mathlib's `MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α)`.
* `TauCeti.invariantsInclusion` and `TauCeti.invariantsMap`: the coefficient half of the transition
  maps of the finite-quotient tower, with its equivariance, and the functoriality of `M ^ H` in the
  coefficient module.

## Roadmap

This is the discrete-module half of Layer 0 of `TauCetiRoadmap/ProfiniteCohomology/README.md`,
whose "Openness" and "Constructions" bullets it discharges. The remaining half of that layer is the
continuous section of `G ⧸ K → G ⧸ H` for closed subgroups (Ribes-Zalesskii Prop. 2.2.2) and the
internal hom `M →+ N` with its conjugation action. Layer 4's description of continuous cohomology as
a colimit over the finite quotients consumes the directed union and the transition maps below.
-/

public section

open MulAction

namespace TauCeti

section Kernel

variable (G : Type*) [Group G] (X : Type*) [MulAction G X]

/-- An element of `G` lies in the kernel of the permutation representation exactly when it fixes
every point. -/
theorem mem_ker_toPermHom {g : G} : g ∈ (toPermHom G X).ker ↔ ∀ x : X, g • x = x := by
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  rfl

/-- The kernel of the permutation representation is the intersection of the point stabilizers. -/
theorem ker_toPermHom_eq_iInf_stabilizer :
    (toPermHom G X).ker = ⨅ x : X, stabilizer G x := by
  ext g
  rw [mem_ker_toPermHom, Subgroup.mem_iInf]
  simp [mem_stabilizer_iff]

end Kernel

section DiscreteAction

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (X : Type*) [TopologicalSpace X] [DiscreteTopology X] [MulAction G X] [ContinuousSMul G X]

/-- The kernel of a continuous action on a *finite* discrete space is open: it is the intersection
of the finitely many point stabilizers, each of which is open. Compactness of `G` plays no part. -/
theorem isOpen_ker_toPermHom [Finite X] : IsOpen ((toPermHom G X).ker : Set G) := by
  rw [ker_toPermHom_eq_iInf_stabilizer, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun x ↦ stabilizer_isOpen G x

/-- The subgroup acting trivially on a finite discrete `G`-set, as an open normal subgroup. It is
normal because it is the kernel of the permutation representation, and open by
`TauCeti.isOpen_ker_toPermHom`. -/
def actionKernel [Finite X] : OpenNormalSubgroup G where
  toSubgroup := (toPermHom G X).ker
  isOpen' := isOpen_ker_toPermHom G X

/-- `TauCeti.actionKernel` is the kernel of the permutation representation, by construction. -/
@[simp]
theorem actionKernel_toSubgroup [Finite X] :
    (actionKernel G X).toSubgroup = (toPermHom G X).ker :=
  (rfl)

/-- Membership in `TauCeti.actionKernel` is acting trivially on every point. -/
@[simp]
theorem mem_actionKernel [Finite X] {g : G} : g ∈ actionKernel G X ↔ ∀ x : X, g • x = x :=
  mem_ker_toPermHom G X

/-- A continuous action on a finite discrete set factors through the permutation representation of
the quotient by `TauCeti.actionKernel`. Over a compact `G` that quotient is a finite group, by
Mathlib's `Finite (G ⧸ U.toSubgroup)` instance for an open subgroup `U`. -/
def quotientToPermHom [Finite X] :
    G ⧸ (actionKernel G X).toSubgroup →* Equiv.Perm X :=
  QuotientGroup.lift _ (toPermHom G X) fun _ hg ↦ hg

/-- The descended permutation representation still acts by the original action. -/
@[simp]
theorem quotientToPermHom_mk [Finite X] (g : G) (x : X) :
    quotientToPermHom G X (QuotientGroup.mk g) x = g • x :=
  (rfl)

/-- The descended permutation representation is faithful. -/
theorem quotientToPermHom_injective [Finite X] :
    Function.Injective (quotientToPermHom G X) := by
  change Function.Injective
    (QuotientGroup.lift (toPermHom G X).ker (toPermHom G X) le_rfl)
  exact (QuotientGroup.injective_lift_iff (toPermHom G X).ker (toPermHom G X) le_rfl).2 rfl

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Local triviality of a discrete action.** Over a profinite group every point of a discrete
`G`-set is fixed by an open *normal* subgroup: its stabilizer is an open neighbourhood of `1`, and
a profinite group has a basis of open normal subgroups at `1`. -/
theorem exists_openNormalSubgroup_smul_eq (x : X) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, u • x = x := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (one_mem _)
  exact ⟨U, fun _ hu ↦ hU hu⟩

end DiscreteAction

section Invariants

variable {G : Type*} [Group G] {M : Type*} [AddGroup M] [DistribMulAction G M]

/-- Membership in `M ^ H`, in the subgroup-membership form the statements below use. -/
theorem mem_fixedPoints_addSubgroup {H : Subgroup G} {m : M} :
    m ∈ FixedPoints.addSubgroup H M ↔ ∀ g ∈ H, g • m = m := by
  simp [Subtype.forall]

variable (M) in
/-- The invariants shrink as the subgroup grows. This is the order-theoretic content of the
transition maps of the finite-quotient tower. -/
theorem fixedPoints_addSubgroup_antitone :
    Antitone fun H : Subgroup G ↦ FixedPoints.addSubgroup H M := by
  intro H K hHK m hm
  rw [mem_fixedPoints_addSubgroup] at hm ⊢
  exact fun g hg ↦ hm g (hHK hg)

variable (M) in
/-- The trivial subgroup fixes everything. -/
@[simp]
theorem fixedPoints_addSubgroup_bot : FixedPoints.addSubgroup (⊥ : Subgroup G) M = ⊤ := by
  ext m
  simp

variable (G M) in
/-- The invariants of the whole group, reached through the subgroup `⊤`. -/
@[simp]
theorem fixedPoints_addSubgroup_top :
    FixedPoints.addSubgroup (⊤ : Subgroup G) M = FixedPoints.addSubgroup G M := by
  ext m
  simp

section Normal

variable {H : Subgroup G} [H.Normal]

/-- `M ^ H` is a `G`-submodule when `H` is normal: this is the additive counterpart of Mathlib's
`MulAction G (fixedPoints H α)`, whose underlying `MulAction` it reuses. -/
instance distribMulActionFixedPoints : DistribMulAction G (FixedPoints.addSubgroup H M) where
  __ := (inferInstance : MulAction G (fixedPoints H M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g a b := Subtype.ext (smul_add g (a : M) (b : M))

/-- `H` acts trivially on `M ^ H`, so the `G`-module structure descends to the quotient `G ⧸ H`.
This is the coefficient module of the finite-level cocycles. -/
instance distribMulActionQuotientFixedPoints :
    DistribMulAction (G ⧸ H) (FixedPoints.addSubgroup H M) where
  __ := (inferInstance : MulAction (G ⧸ H) (fixedPoints H M))
  smul_zero q := q.induction_on fun g ↦ Subtype.ext (smul_zero g)
  smul_add q a b := q.induction_on fun g ↦ Subtype.ext (smul_add g (a : M) (b : M))

/-- The `G`-action on `M ^ H` is the restriction of the action on `M`. -/
@[simp]
theorem coe_smul_fixedPoints_addSubgroup (g : G) (m : FixedPoints.addSubgroup H M) :
    ((g • m : FixedPoints.addSubgroup H M) : M) = g • (m : M) :=
  rfl

/-- The `G ⧸ H`-action on `M ^ H` is computed by any representative. -/
@[simp]
theorem quotientMk_smul_fixedPoints_addSubgroup (g : G) (m : FixedPoints.addSubgroup H M) :
    (QuotientGroup.mk g : G ⧸ H) • m = g • m :=
  rfl

end Normal

variable {H K : Subgroup G}

/-- The coefficient half of a transition map of the finite-quotient tower: for `K ≤ H` the
invariants of `H` include into the invariants of `K`. -/
def invariantsInclusion (h : K ≤ H) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup K M :=
  AddSubgroup.inclusion (fixedPoints_addSubgroup_antitone M h)

/-- The transition inclusion does not move an element of `M`. -/
@[simp]
theorem coe_invariantsInclusion (h : K ≤ H) (m : FixedPoints.addSubgroup H M) :
    (invariantsInclusion h m : M) = (m : M) :=
  (rfl)

/-- The transition inclusion is `G`-equivariant. -/
@[simp]
theorem invariantsInclusion_smul [H.Normal] [K.Normal] (h : K ≤ H) (g : G)
    (m : FixedPoints.addSubgroup H M) :
    invariantsInclusion h (g • m) = g • invariantsInclusion h m :=
  (rfl)

/-- The transition inclusion is equivariant for the two finite-level actions, along the quotient
homomorphism `G ⧸ K → G ⧸ H`. This is the equivariance that types the transition pair of the
finite-quotient system. -/
@[simp]
theorem invariantsInclusion_quotientMk_smul [H.Normal] [K.Normal] (h : K ≤ H) (g : G)
    (m : FixedPoints.addSubgroup H M) :
    invariantsInclusion h ((QuotientGroup.mk g : G ⧸ H) • m) =
      (QuotientGroup.mk g : G ⧸ K) • invariantsInclusion h m :=
  (rfl)

variable (M) in
/-- The transition inclusions are functorial in the subgroup: the identity inclusion is the
identity. -/
@[simp]
theorem invariantsInclusion_refl (H : Subgroup G) :
    invariantsInclusion (M := M) (le_refl H) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext (rfl)

/-- The transition inclusions are functorial in the subgroup: they compose. -/
@[simp]
theorem invariantsInclusion_comp {L : Subgroup G} (h : K ≤ H) (h' : L ≤ K) :
    (invariantsInclusion (M := M) h').comp (invariantsInclusion h) =
      invariantsInclusion (h'.trans h) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext (rfl)

section Map

variable {N : Type*} [AddGroup N] [DistribMulAction G N]

/-- A `G`-equivariant additive map restricts to the invariants of any subgroup. This is the
functoriality of `M ^ H` in the coefficients. -/
def invariantsMap (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (H : Subgroup G) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup H N where
  toFun m := ⟨f (m : M), mem_fixedPoints_addSubgroup.2 fun g hg ↦ by
    rw [← hf g, mem_fixedPoints_addSubgroup.1 m.2 g hg]⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' a b := Subtype.ext (f.map_add (a : M) (b : M))

/-- The restricted map is the original map on underlying elements. -/
@[simp]
theorem coe_invariantsMap (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (H : Subgroup G) (m : FixedPoints.addSubgroup H M) :
    (invariantsMap f hf H m : N) = f (m : M) :=
  (rfl)

/-- Restriction to the invariants is equivariant for the `G`-actions of a normal subgroup. -/
@[simp]
theorem invariantsMap_smul (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (H : Subgroup G) [H.Normal] (g : G) (m : FixedPoints.addSubgroup H M) :
    invariantsMap f hf H (g • m) = g • invariantsMap f hf H m :=
  Subtype.ext (hf g (m : M))

/-- Restriction to the invariants commutes with the transition inclusions. -/
theorem invariantsMap_comp_invariantsInclusion (f : M →+ N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (h : K ≤ H) :
    (invariantsMap f hf K).comp (invariantsInclusion h) =
      (invariantsInclusion h).comp (invariantsMap f hf H) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext (rfl)

end Map

end Invariants

section FiniteLevel

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddGroup M] [DistribMulAction G M]

/-- The finite-level invariants form a directed family: the open normal subgroups are closed under
intersection, and the invariants grow as the subgroup shrinks. Layer 4's colimit is filtered for
this reason. -/
theorem directed_fixedPoints_addSubgroup :
    Directed (· ≤ ·) fun U : OpenNormalSubgroup G ↦ FixedPoints.addSubgroup U.toSubgroup M := by
  intro U V
  refine ⟨⟨⟨U.toSubgroup ⊓ V.toSubgroup, U.isOpen.inter V.isOpen⟩, inferInstance⟩, ?_, ?_⟩
  · exact fixedPoints_addSubgroup_antitone M inf_le_left
  · exact fixedPoints_addSubgroup_antitone M inf_le_right

variable [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]

/-- For an open normal subgroup `U` the invariant coefficients `M ^ U` are again discrete, and the
action of the discrete quotient group `G ⧸ U` on them is continuous. -/
theorem continuousSMul_quotient_fixedPoints (U : OpenNormalSubgroup G) :
    ContinuousSMul (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) :=
  ⟨continuous_of_discreteTopology⟩

end FiniteLevel

section ProfiniteInvariants

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable (M : Type*) [AddGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Every element of a discrete module over a profinite group is invariant under some open normal
subgroup. -/
theorem exists_openNormalSubgroup_mem_fixedPoints (m : M) :
    ∃ U : OpenNormalSubgroup G, m ∈ FixedPoints.addSubgroup U.toSubgroup M := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq G M m
  exact ⟨U, mem_fixedPoints_addSubgroup.2 hU⟩

/-- **A discrete module over a profinite group is the union of its finite-level invariants.** -/
theorem iUnion_coe_fixedPoints_addSubgroup_eq_univ :
    ⋃ U : OpenNormalSubgroup G, (FixedPoints.addSubgroup U.toSubgroup M : Set M) = Set.univ := by
  refine Set.eq_univ_of_forall fun m ↦ ?_
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_mem_fixedPoints G M m
  exact Set.mem_iUnion.2 ⟨U, hU⟩

/-- The subgroup-lattice form of `TauCeti.iUnion_coe_fixedPoints_addSubgroup_eq_univ`. -/
theorem iSup_fixedPoints_addSubgroup_eq_top :
    ⨆ U : OpenNormalSubgroup G, FixedPoints.addSubgroup U.toSubgroup M = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_mem_fixedPoints G M m
  exact le_iSup (fun U : OpenNormalSubgroup G ↦ FixedPoints.addSubgroup U.toSubgroup M) U hU

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- A *finite* discrete module with a continuous `G`-action is already the invariants of a single
open normal subgroup, namely the kernel of the action. -/
theorem exists_openNormalSubgroup_fixedPoints_addSubgroup_eq_top [Finite M] :
    ∃ U : OpenNormalSubgroup G, FixedPoints.addSubgroup U.toSubgroup M = ⊤ := by
  refine ⟨actionKernel G M, eq_top_iff.2 fun m _ ↦ ?_⟩
  exact mem_fixedPoints_addSubgroup.2 fun g hg ↦ (mem_actionKernel G M).1 hg m

end ProfiniteInvariants

end TauCeti
