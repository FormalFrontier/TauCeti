/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.MulAction

/-!
# Discrete modules over profinite groups

This file develops the openness properties of a continuous action on a discrete additive group.
For a finite coefficient group, the kernel of the action is open and the action is therefore an
action of a finite quotient. For an arbitrary discrete coefficient group, the corresponding
statement holds one element at a time: every element is fixed by an open normal subgroup.

The latter statement is recorded both as an elementwise factorization of the orbit map and as the
fact that the fixed-point subgroups over all open normal subgroups exhaust the coefficient group.
These are the forms used by the finite-quotient system for continuous cohomology.

Mathlib already supplies the two principal ingredients: point stabilizers are open for continuous
actions on discrete spaces, and every neighbourhood of the identity in a profinite group contains
an open normal subgroup. It also supplies `MulAction.fixedPoints` and the quotient action on the
fixed points of a normal subgroup; this file uses those definitions rather than introducing a
parallel invariants object.
-/

public section

namespace TauCeti

universe u v

section Elementwise

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {M : Type v} [TopologicalSpace M] [DiscreteTopology M] [MulAction G M] [ContinuousSMul G M]

/-- Every element of a discrete continuous module over a profinite group is fixed by an open
normal subgroup. -/
theorem exists_openNormalSubgroup_smul_eq_self (m : M) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, u • m = m := by
  have hOpen : IsOpen (MulAction.stabilizer G m : Set G) := stabilizer_isOpen G m
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOpen
      (by simp)
  exact ⟨U, fun u hu ↦ MulAction.mem_stabilizer_iff.mp (hU hu)⟩

/-- A finite set in a discrete continuous module over a profinite group is fixed pointwise by a
single open normal subgroup. -/
theorem Set.Finite.exists_openNormalSubgroup_smul_eq_self {s : Set M} (hs : s.Finite) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∀ m ∈ s, u • m = m := by
  let V : Set G := ⋂ m ∈ s, (MulAction.stabilizer G m : Set G)
  have hOpen : IsOpen V :=
    hs.isOpen_biInter fun m _ ↦ stabilizer_isOpen G m
  have hOne : (1 : G) ∈ V := by
    simp only [V, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, one_smul,
      implies_true]
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOpen hOne
  refine ⟨U, fun u hu m hm ↦ ?_⟩
  exact MulAction.mem_stabilizer_iff.mp (Set.mem_iInter₂.mp (hU hu) m hm)

/-- A finite family in a discrete continuous module over a profinite group has a common open
normal stabilizer. This is the form used for the finite image of a locally constant cochain. -/
theorem exists_openNormalSubgroup_smul_eq_self_range {ι : Type*} [Finite ι] (f : ι → M) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∀ i, u • f i = f i := by
  have hrange : (Set.range f).Finite := Set.finite_range f
  obtain ⟨U, hU⟩ :=
    Set.Finite.exists_openNormalSubgroup_smul_eq_self (G := G) hrange
  exact ⟨U, fun u hu i ↦ hU u hu (f i) ⟨i, rfl⟩⟩

/-- The orbit map of an element of a discrete profinite module factors through a finite quotient.
The factor is obtained from Mathlib's quotient action on the fixed points of a normal subgroup. -/
theorem exists_orbitMap_quotient (m : M) :
    ∃ (U : OpenNormalSubgroup G) (f : G ⧸ U.toSubgroup → M),
      ∀ g : G, f (QuotientGroup.mk g) = g • m := by
  obtain ⟨U, hm⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) m
  let mU : MulAction.fixedPoints U.toSubgroup M := ⟨m, fun u ↦ hm u u.2⟩
  refine ⟨U, fun q ↦ (q • mU : MulAction.fixedPoints U.toSubgroup M), fun g ↦ ?_⟩
  exact congrArg Subtype.val (MulAction.coe_quotient_smul_fixedPoints g mU)

end Elementwise

section Kernel

variable (G : Type u) [Group G] (M : Type v) [MulAction G M]

/-- The kernel of a group action, regarded as a subgroup of the acting group. -/
abbrev actionKernel : Subgroup G := (MulAction.toPermHom G M).ker

/-- Membership in the action kernel means fixing every element. -/
theorem mem_actionKernel_iff {g : G} :
    g ∈ actionKernel G M ↔ ∀ m : M, g • m = m := by
  simp only [actionKernel, MonoidHom.mem_ker, Equiv.ext_iff, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Equiv.Perm.one_apply]

/-- The action kernel is the intersection of all point stabilizers. -/
theorem actionKernel_eq_iInf_stabilizer :
    actionKernel G M = ⨅ m : M, MulAction.stabilizer G m := by
  ext g
  simp only [mem_actionKernel_iff, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

/-- The action kernel is the whole group exactly when the action is trivial. -/
theorem actionKernel_eq_top_iff :
    actionKernel G M = ⊤ ↔ ∀ (g : G) (m : M), g • m = m := by
  constructor
  · intro h g m
    apply (mem_actionKernel_iff G M).mp
    rw [h]
    exact Subgroup.mem_top g
  · intro h
    rw [eq_top_iff]
    intro g _
    exact (mem_actionKernel_iff G M).mpr (h g)

/-- The permutation representation factors faithfully through the quotient by its kernel. -/
theorem action_factors_through_quotient :
    ∃ ρ : G ⧸ actionKernel G M →* Equiv.Perm M,
      Function.Injective ρ ∧
        ∀ (g : G) (m : M), ρ (QuotientGroup.mk g) m = g • m := by
  refine ⟨QuotientGroup.kerLift (MulAction.toPermHom G M),
    QuotientGroup.kerLift_injective (MulAction.toPermHom G M), fun g m ↦ ?_⟩
  rw [QuotientGroup.kerLift_mk]
  rfl

/-- An action on a finite space factors through a finite quotient. -/
theorem actionQuotient_finite [Finite M] : Finite (G ⧸ actionKernel G M) := by
  exact Finite.of_equiv (MulAction.toPermHom G M).range
    (QuotientGroup.quotientKerEquivRange (MulAction.toPermHom G M)).symm.toEquiv

variable [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The kernel of a continuous action on a finite discrete space is open. -/
theorem actionKernel_isOpen [Finite M] : IsOpen (actionKernel G M : Set G) := by
  rw [show (actionKernel G M : Set G) =
    ⋂ m : M, (MulAction.stabilizer G m : Set G) by
      ext g
      simp only [Set.mem_iInter, SetLike.mem_coe, mem_actionKernel_iff,
        MulAction.mem_stabilizer_iff]]
  exact isOpen_iInter_of_finite fun m ↦ stabilizer_isOpen G m

/-- The open normal subgroup given by the kernel of a finite discrete action. -/
def openActionKernel [Finite M] : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := actionKernel G M
      isOpen' := actionKernel_isOpen G M }
  isNormal' := (MulAction.toPermHom G M).normal_ker

@[simp]
theorem openActionKernel_toSubgroup [Finite M] :
    (openActionKernel G M).toSubgroup = actionKernel G M := by
  ext
  simp only [openActionKernel]

/-- A finite discrete module is fixed pointwise by an open normal subgroup. The subgroup can be
taken to be the kernel of the action. -/
theorem openActionKernel_smul_eq_self [Finite M] (g : openActionKernel G M) (m : M) :
    (g : G) • m = m :=
  (mem_actionKernel_iff G M).mp g.2 m

end Kernel

section FiniteCoefficients

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]

/-- The fixed points of the action kernel on a finite discrete module are the whole module. This
is the levelwise stabilization of the invariant coefficient system. -/
theorem fixedPoints_openActionKernel_eq_top :
    FixedPoints.addSubgroup (openActionKernel G M).toSubgroup M = ⊤ := by
  rw [eq_top_iff]
  intro m _ g
  exact openActionKernel_smul_eq_self G M g m

end FiniteCoefficients

section Exhaustion

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The fixed-point subgroups over the open normal subgroups exhaust a discrete module. -/
theorem iSup_fixedPoints_openNormal_eq_top :
    (⨆ U : OpenNormalSubgroup G, FixedPoints.addSubgroup U.toSubgroup M) = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨U, hm⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) m
  apply (le_iSup (fun V : OpenNormalSubgroup G ↦ FixedPoints.addSubgroup V.toSubgroup M) U)
  exact fun u ↦ hm u u.2

end Exhaustion

end TauCeti
