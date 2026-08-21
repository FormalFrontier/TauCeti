/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Invariants of a discrete module as a module over a finite quotient

For a normal subgroup `H` of `G` acting distributively on an additive group `M`, the invariants
`M ^ H` carry a distributive action of `G ⧸ H`. Over a profinite `G` with `H` open normal this is
the coefficient system of the finite-level tower computing continuous cohomology: the finite group
`G ⧸ H` acts on the discrete module `M ^ H`, and shrinking `H` enlarges `M ^ H` along transition
inclusions.

The invariant subgroup `M ^ H` is Mathlib's `FixedPoints.addSubgroup H M`; no second name for it is
introduced here. What is new is its distributive `G`-action for normal `H`, the descent of that
action to `G ⧸ H`, the transition inclusions of the finite-quotient tower with their equivariance
and functoriality, and the functoriality of `M ^ H` in the coefficient module.

The declarations below work for an additive group with a distributive `G`-action; specializing to
an abelian group gives the usual discrete-module theory. The unbundled classes `[AddGroup M]
[DistribMulAction G M]`, with `[TopologicalSpace M] [DiscreteTopology M]` added only where the
topology is used, are the hypotheses throughout, rather than a new bundling structure, so that
instance search composes them freely.

## Main results

* `TauCeti.distribMulActionFixedPoints` and `TauCeti.distribMulActionQuotientFixedPoints`: the
  distributive `G`- and `G ⧸ H`-actions on `M ^ H` for normal `H`, the additive counterparts of
  Mathlib's `MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α)`.
* `TauCeti.invariantsInclusion`: the coefficient half of a transition map of the finite-quotient
  tower, with its equivariance along `G ⧸ K →* G ⧸ H` and its identity and composition laws.
* `TauCeti.invariantsMap`: the functoriality of `M ^ H` in the coefficient module.
* `TauCeti.directed_fixedPoints_addSubgroup` and `TauCeti.continuousSMul_quotient_fixedPoints`:
  the invariants over the open normal subgroups form a directed family, and each carries a
  continuous action of the discrete quotient group.

## Roadmap

This file addresses the "Constructions" bullet of Layer 0 of
`TauCetiRoadmap/ProfiniteCohomology/README.md`, which asks for the invariants `M ^ U` as a
`G ⧸ U`-module with their induced discrete action, and with it milestones 2, 3, 5 and 6 of Layer
4's transition system, which that layer draws from Layer 0. The "Openness" bullet of Layer 0 is
already in `TauCeti/RepresentationTheory/Homological/ContCohomology/Discrete.lean`; it is used,
not restated, here. Directedness is what makes Layer 4's colimit over the finite quotients
filtered.
-/

public section

open MulAction

namespace TauCeti

section Invariants

variable {G : Type*} [Group G] {M : Type*} [AddGroup M] [DistribMulAction G M]

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

/-- `M ^ H` has a distributive `G`-action when `H` is normal: this is the additive counterpart of
Mathlib's `MulAction G (fixedPoints H α)`, whose underlying `MulAction` it reuses. -/
instance distribMulActionFixedPoints : DistribMulAction G (FixedPoints.addSubgroup H M) where
  __ := (inferInstance : MulAction G (fixedPoints H M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g a b := Subtype.ext (smul_add g (a : M) (b : M))

/-- `H` acts trivially on `M ^ H`, so the distributive `G`-action descends to the quotient `G ⧸ H`.
For an abelian `M`, this is the coefficient module of the finite-level cocycles. -/
instance distribMulActionQuotientFixedPoints :
    DistribMulAction (G ⧸ H) (FixedPoints.addSubgroup H M) where
  __ := (inferInstance : MulAction (G ⧸ H) (fixedPoints H M))
  smul_zero q := q.induction_on fun g ↦ Subtype.ext (smul_zero g)
  smul_add q a b := q.induction_on fun g ↦ Subtype.ext (smul_add g (a : M) (b : M))

end Normal

variable {H K : Subgroup G}

/-- The coefficient half of a transition map of the finite-quotient tower: for `K ≤ H` the
invariants of `H` include into the invariants of `K`. -/
def invariantsInclusion (h : K ≤ H) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup K M :=
  AddSubgroup.inclusion (fixedPoints_subgroup_antitone G M h)

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

/-- The transition inclusion is equivariant along Mathlib's canonical quotient homomorphism
`G ⧸ K →* G ⧸ H`. Without this the quotient map and the coefficient inclusion are not a
compatible pair. -/
@[simp]
theorem invariantsInclusion_quotient_smul [H.Normal] [K.Normal] (h : K ≤ H) (q : G ⧸ K)
    (m : FixedPoints.addSubgroup H M) :
    invariantsInclusion h
        ((QuotientGroup.map K H (MonoidHom.id G) (fun _ hg ↦ h hg) q) • m) =
      q • invariantsInclusion h m := by
  induction q using QuotientGroup.induction_on
  rfl

variable (M) in
/-- The transition inclusions are functorial in the subgroup: the identity inclusion is the
identity. -/
@[simp]
theorem invariantsInclusion_refl (H : Subgroup G) :
    invariantsInclusion (M := M) (le_refl H) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

/-- The transition inclusions are functorial in the subgroup: they compose. -/
@[simp]
theorem invariantsInclusion_comp {L : Subgroup G} (h : K ≤ H) (h' : L ≤ K) :
    (invariantsInclusion (M := M) h').comp (invariantsInclusion h) =
      invariantsInclusion (h'.trans h) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

section Map

variable {N : Type*} [AddGroup N] [DistribMulAction G N]

/-- A `G`-equivariant additive map restricts to the invariants of any subgroup. This is the
functoriality of `M ^ H` in the coefficients. -/
def invariantsMap (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (H : Subgroup G) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup H N where
  toFun m := ⟨f (m : M), (FixedPoints.mem_addSubgroup _ _ _).2 fun g ↦ by
    rw [Subgroup.smul_def, ← hf, ← Subgroup.smul_def,
      (FixedPoints.mem_addSubgroup _ _ _).1 m.2 g]⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' a b := Subtype.ext (f.map_add (a : M) (b : M))

/-- Restriction to invariants preserves the identity map. -/
@[simp]
theorem invariantsMap_id (H : Subgroup G) :
    invariantsMap (AddMonoidHom.id M) (fun _ _ ↦ rfl) H = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

/-- Restriction to invariants preserves composition. -/
@[simp]
theorem invariantsMap_comp {P : Type*} [AddGroup P] [DistribMulAction G P]
    (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (f' : N →+ P) (hf' : ∀ (g : G) (n : N), f' (g • n) = g • f' n)
    (H : Subgroup G) :
    (invariantsMap f' hf' H).comp (invariantsMap f hf H) =
      invariantsMap (f'.comp f) (fun g m ↦ by
        simp only [AddMonoidHom.comp_apply]
        calc
          f' (f (g • m)) = f' (g • f m) := congrArg f' (hf g m)
          _ = g • f' (f m) := hf' g (f m)) H :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

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

/-- Restriction to the invariants is equivariant for the finite-level `G ⧸ H`-actions. -/
@[simp]
theorem invariantsMap_quotient_smul (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (H : Subgroup G) [H.Normal] (q : G ⧸ H) (m : FixedPoints.addSubgroup H M) :
    invariantsMap f hf H (q • m) = q • invariantsMap f hf H m := by
  induction q using QuotientGroup.induction_on with
  | H g => exact Subtype.ext (hf g (m : M))

/-- Restriction to the invariants commutes with the transition inclusions. -/
theorem invariantsMap_comp_invariantsInclusion (f : M →+ N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (h : K ≤ H) :
    (invariantsMap f hf K).comp (invariantsInclusion h) =
      (invariantsInclusion h).comp (invariantsMap f hf H) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

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
  · exact fixedPoints_subgroup_antitone G M inf_le_left
  · exact fixedPoints_subgroup_antitone G M inf_le_right

variable [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]

/-- For an open normal subgroup `U` the invariant coefficients `M ^ U` are again discrete, and the
action of the discrete quotient group `G ⧸ U` on them is continuous. -/
theorem continuousSMul_quotient_fixedPoints (U : OpenNormalSubgroup G) :
    ContinuousSMul (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) :=
  ⟨continuous_of_discreteTopology⟩

end FiniteLevel

end TauCeti
