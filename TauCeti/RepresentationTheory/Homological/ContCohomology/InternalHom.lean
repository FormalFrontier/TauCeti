/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Discrete

/-!
# The internal hom of two discrete modules over a profinite group

Let a group `G` act on an additive monoid `M` and an additive commutative monoid `N`. The
additive homomorphisms
`M →+ N` carry the *conjugation* action

`homAction g φ : m ↦ g • φ (g⁻¹ • m)`,

which is the action for which evaluation `(φ, m) ↦ φ m` is equivariant, in the form
`homAction g φ (g • m) = g • φ m`. This file constructs that action and proves that it is again a
continuous action on a discrete module when `M` is finite discrete and `N` is discrete: the set of
group elements fixing a given `φ` is open, and over a profinite `G` it contains an open normal
subgroup.

This implements the internal-hom half of the "Constructions" milestone of Layer 0 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`. The evaluation pairing
that roadmap's duality package feeds to the cup products is evaluation at this action, and its
equivariance is `homAction_apply_smul` below.

## Main definitions

* `TauCeti.homAction`: the conjugation action of `G` on `M →+ N`, with the action laws
  `homAction_one` and `homAction_mul` and the additivity laws `homAction_zero` and
  `homAction_add`.
* `TauCeti.InternalHom`: the carrier `M →+ N` equipped with that action, as a `DistribMulAction`
  instance. Its `TauCeti.InternalHom.of` and `TauCeti.InternalHom.toAddMonoidHom` translate to and
  from `M →+ N`.

## Main results

* `TauCeti.homAction_apply_smul`: evaluation is equivariant; on the carrier this is
  `TauCeti.InternalHom.smul_apply_smul`.
* `TauCeti.homAction_eq_self_iff`: `g` fixes `φ` exactly when `φ` commutes with the action of `g`;
  so `φ` is fixed by all of `G` exactly when it is `G`-equivariant
  (`TauCeti.forall_homAction_eq_self_iff`).
* `TauCeti.isOpen_setOf_homAction_eq_self`: for finite discrete `M` and discrete `N` the set of
  group elements fixing `φ` is open. This is what makes `TauCeti.InternalHom` a discrete `G`-module:
  it carries a `DiscreteTopology` and a `ContinuousSMul G` instance.
* `TauCeti.exists_openNormalSubgroup_homAction_eq_self`: over a profinite group that set contains
  an open normal subgroup.

## Implementation notes

Mathlib already puts the codomain-pointwise action `(g • φ) m = g • φ m` on `M →+ N`, as the
instance in `Mathlib/Algebra/GroupWithZero/Action/Hom.lean`, and that action is not the conjugation
one, so the conjugation action cannot be registered on `M →+ N` itself: instance search would be
incoherent, and continuous cohomology of `M →+ N` would silently pick up the pointwise action.
The conjugation action is therefore introduced twice over. It is first the plain function
`homAction` of `g`, whose action and additivity laws are the four lemmas listed above; this is the
form in which the roadmap names it and the form in which the lemmas about evaluation read. It is
then registered as a genuine `DistribMulAction` on the wrapper `InternalHom G M N`, which is
the object downstream cohomology is meant to be applied to. The two actions on `M →+ N` agree when
`G` acts trivially on the source (`homAction_eq_smul`).

`Representation.linHom` is the same conjugation construction for `k`-linear maps `V →ₗ[k] W` of
bundled representations. It is not used as the definition here for two reasons. Its carrier is
`V →ₗ[k] W`, a type distinct from the `M →+ N` in which the roadmap's cochains take values, so
routing through it would still need a bespoke definition round-tripping along
`AddMonoidHom.toIntLinearMap` and `LinearMap.toAddMonoidHom`; and taking `k = ℤ` forces
`Module ℤ M` and `Module ℤ N`, hence `AddCommGroup` on both sides, whereas everything below needs
only `AddMonoid M` and `AddCommMonoid N`. The identification of the two constructions, in the
generality where `Representation.linHom` is available, is `toIntLinearMap_homAction`.

Mathlib puts no topology on `M →+ N`. Discreteness of the internal hom enters here through the
discreteness of the ambient function space `M → N`, which is what
`isOpen_setOf_homAction_eq_self` rests on; `InternalHom G M N` then carries the discrete topology
outright, and finiteness of `M` is what its `ContinuousSMul` instance needs.
-/

public section

namespace TauCeti

section Action

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- The conjugation action of `G` on the internal hom `M →+ N`, sending `φ` to
`m ↦ g • φ (g⁻¹ • m)`. This is the action making evaluation equivariant; see
`homAction_apply_smul`. It is assembled from Mathlib's `DistribSMul.toAddMonoidHom`, which bundles
each `g • ·` as an additive homomorphism, so that additivity comes from `AddMonoidHom.comp`. -/
def homAction (g : G) (φ : M →+ N) : M →+ N :=
  (DistribSMul.toAddMonoidHom N g).comp (φ.comp (DistribSMul.toAddMonoidHom M g⁻¹))

@[simp]
theorem homAction_apply (g : G) (φ : M →+ N) (m : M) : homAction g φ m = g • φ (g⁻¹ • m) := (rfl)

@[simp]
theorem homAction_one (φ : M →+ N) : homAction (1 : G) φ = φ := by
  ext m
  simp

theorem homAction_mul (g h : G) (φ : M →+ N) :
    homAction (g * h) φ = homAction g (homAction h φ) := by
  ext m
  simp [mul_smul, mul_inv_rev]

@[simp]
theorem homAction_zero (g : G) : homAction g (0 : M →+ N) = 0 := by
  ext m
  simp

@[simp]
theorem homAction_add (g : G) (φ ψ : M →+ N) :
    homAction g (φ + ψ) = homAction g φ + homAction g ψ := by
  ext m
  simp

/-- Evaluation `(φ, m) ↦ φ m` is equivariant for the conjugation action on `M →+ N`. This is the
equivariance that makes the duality cup pairings well typed, and it is what fixes the direction of
the conjugation action. -/
theorem homAction_apply_smul (g : G) (φ : M →+ N) (m : M) : homAction g φ (g • m) = g • φ m := by
  simp

/-- A group element fixes `φ` for the conjugation action exactly when `φ` commutes with its
action. -/
theorem homAction_eq_self_iff {g : G} {φ : M →+ N} :
    homAction g φ = φ ↔ ∀ m : M, φ (g • m) = g • φ m := by
  constructor
  · intro h m
    have hm := homAction_apply_smul g φ m
    rwa [h] at hm
  · intro h
    ext m
    rw [homAction_apply, ← h, smul_inv_smul]

/-- The invariants of the conjugation action are the `G`-equivariant homomorphisms: this computes
the degree-zero cohomology of the internal hom. -/
theorem forall_homAction_eq_self_iff {φ : M →+ N} :
    (∀ g : G, homAction g φ = φ) ↔ ∀ (g : G) (m : M), φ (g • m) = g • φ m :=
  forall_congr' fun _ => homAction_eq_self_iff

@[simp]
theorem homAction_id (g : G) : homAction g (AddMonoidHom.id N) = AddMonoidHom.id N :=
  homAction_eq_self_iff.mpr fun _ => rfl

/-- The conjugation action is functorial for composition of homomorphisms. -/
theorem homAction_comp {P : Type*} [AddCommMonoid P] [DistribMulAction G P] (g : G) (φ : M →+ N)
    (ψ : N →+ P) : homAction g (ψ.comp φ) = (homAction g ψ).comp (homAction g φ) := by
  ext m
  simp

/-- When `G` acts trivially on the source, the conjugation action on `M →+ N` is Mathlib's
codomain-pointwise action. -/
theorem homAction_eq_smul (h : ∀ (g : G) (m : M), g • m = m) (g : G) (φ : M →+ N) :
    homAction g φ = g • φ := by
  ext m
  simp [h]

end Action

section IntLinearMap

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
  {N : Type*} [AddCommGroup N] [DistribMulAction G N]

/-- The conjugation action on `M →+ N` is Mathlib's conjugation action `Representation.linHom` on
`ℤ`-linear maps, transported along `AddMonoidHom.toIntLinearMap`. -/
theorem toIntLinearMap_homAction (g : G) (φ : M →+ N) :
    (homAction g φ).toIntLinearMap =
      Representation.linHom (Representation.ofDistribMulAction ℤ G M)
        (Representation.ofDistribMulAction ℤ G N) g φ.toIntLinearMap := by
  ext m
  simp

end IntLinearMap

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
  {M : Type*} [AddMonoid M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M]
  {N : Type*} [AddCommMonoid N] [TopologicalSpace N] [DistribMulAction G N] [ContinuousSMul G N]

/-- Each value of the conjugation action is continuous in the group variable. Only the source `M`
is required to be discrete: `φ` is then automatically continuous, and the two actions occurring in
`g • φ (g⁻¹ • m)` are continuous by hypothesis. -/
theorem continuous_homAction_apply (φ : M →+ N) (m : M) :
    Continuous fun g : G => homAction g φ m := by
  simp only [homAction_apply]
  exact continuous_id.smul
    ((continuous_of_discreteTopology (f := φ)).comp (continuous_inv.smul continuous_const))

/-- The conjugation action is continuous into the ambient function space `M → N`. -/
theorem continuous_homAction_coe (φ : M →+ N) :
    Continuous fun g : G => ((homAction g φ : M →+ N) : M → N) :=
  continuous_pi fun m => continuous_homAction_apply φ m

/-- For a finite discrete `M` and a discrete `N` the set of group elements fixing `φ` is open.
Since `M →+ N` is discrete as a subspace of `M → N`, this openness is what continuity of the
conjugation action amounts to; it is fed to `continuousSMul_iff_stabilizer_isOpen` to produce the
`ContinuousSMul G (InternalHom G M N)` instance below. -/
theorem isOpen_setOf_homAction_eq_self [Finite M] [DiscreteTopology N] (φ : M →+ N) :
    IsOpen {g : G | homAction g φ = φ} := by
  have hset : {g : G | homAction g φ = φ}
      = (fun g : G => ((homAction g φ : M →+ N) : M → N)) ⁻¹' {(φ : M → N)} := by
    ext g
    simp [DFunLike.coe_fn_eq]
  rw [hset]
  exact (continuous_homAction_coe φ).isOpen_preimage _ (isOpen_discrete _)

end Topology

/-- The internal hom of two `G`-modules: the additive homomorphisms `M →+ N` carrying the
conjugation action `g • φ = homAction g φ`. It is a one-field wrapper around `M →+ N` rather than
`M →+ N` itself because Mathlib registers the codomain-pointwise action on the latter; this is the
type on which continuous cohomology of the internal hom is to be taken. -/
structure InternalHom (G : Type*) [Group G] (M : Type*) [AddMonoid M] [DistribMulAction G M]
    (N : Type*) [AddCommMonoid N] [DistribMulAction G N] where
  /-- Regard an additive homomorphism as an element of the internal hom. -/
  of (G) ::
  /-- Regard an element of the internal hom as an additive homomorphism, forgetting the action. -/
  toAddMonoidHom : M →+ N

namespace InternalHom

variable (G : Type*) [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- The internal hom and `M →+ N` have the same elements; they differ only in their `G`-action. -/
@[expose]
def equivAddMonoidHom : InternalHom G M N ≃ (M →+ N) where
  toFun := toAddMonoidHom
  invFun := of G
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommMonoid (InternalHom G M N) := (equivAddMonoidHom G).addCommMonoid

variable {G}

@[simp]
theorem of_toAddMonoidHom (φ : InternalHom G M N) : of G φ.toAddMonoidHom = φ := rfl

theorem toAddMonoidHom_inj {φ ψ : InternalHom G M N} :
    φ.toAddMonoidHom = ψ.toAddMonoidHom ↔ φ = ψ :=
  ⟨fun h => by rw [← of_toAddMonoidHom φ, ← of_toAddMonoidHom ψ, h], fun h => h ▸ rfl⟩

@[simp]
theorem toAddMonoidHom_zero : (0 : InternalHom G M N).toAddMonoidHom = 0 := rfl

@[simp]
theorem toAddMonoidHom_add (φ ψ : InternalHom G M N) :
    (φ + ψ).toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom := rfl

@[simp]
theorem of_zero : of G (0 : M →+ N) = 0 := rfl

@[simp]
theorem of_add (φ ψ : M →+ N) : of G (φ + ψ) = of G φ + of G ψ := rfl

/-- The conjugation action of `G` on the internal hom. -/
instance : SMul G (InternalHom G M N) where
  smul g φ := of G (homAction g φ.toAddMonoidHom)

@[simp]
theorem toAddMonoidHom_smul (g : G) (φ : InternalHom G M N) :
    (g • φ).toAddMonoidHom = homAction g φ.toAddMonoidHom := rfl

@[simp]
theorem smul_of (g : G) (φ : M →+ N) : g • of G φ = of G (homAction g φ) := rfl

instance : DistribMulAction G (InternalHom G M N) where
  one_smul φ := by simp [← toAddMonoidHom_inj]
  mul_smul g h φ := by simp [← toAddMonoidHom_inj, homAction_mul]
  smul_zero g := by simp [← toAddMonoidHom_inj]
  smul_add g φ ψ := by simp [← toAddMonoidHom_inj]

/-- Evaluation is equivariant for the action on the internal hom. This is the roadmap's evaluation
pairing, in the form in which the duality cup products consume it. -/
theorem smul_apply_smul (g : G) (φ : InternalHom G M N) (m : M) :
    (g • φ).toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m :=
  homAction_apply_smul g _ m

/-- The invariants of the internal hom are the `G`-equivariant homomorphisms. -/
theorem forall_smul_eq_self_iff {φ : InternalHom G M N} :
    (∀ g : G, g • φ = φ) ↔
      ∀ (g : G) (m : M), φ.toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m := by
  simp only [← toAddMonoidHom_inj, toAddMonoidHom_smul]
  exact forall_homAction_eq_self_iff

/-- The internal hom of discrete modules is discrete. -/
instance : TopologicalSpace (InternalHom G M N) := ⊥

instance : DiscreteTopology (InternalHom G M N) := ⟨rfl⟩

/-- For a finite discrete `M` and a discrete `N` over a topological group, the conjugation action
on the internal hom is continuous: this is the statement that `InternalHom G M N` is again a
discrete `G`-module. -/
instance [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] [Finite M] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul G N] : ContinuousSMul G (InternalHom G M N) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun φ => ?_
  have hset : (MulAction.stabilizer G φ : Set G)
      = {g : G | homAction g φ.toAddMonoidHom = φ.toAddMonoidHom} := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_ofPred_eq,
      ← toAddMonoidHom_inj, toAddMonoidHom_smul]
  rw [hset]
  exact isOpen_setOf_homAction_eq_self _

end InternalHom

section Profinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {M : Type*} [AddMonoid M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Finite M]
  {N : Type*} [AddCommMonoid N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [ContinuousSMul G N]

/-- Over a profinite group, a homomorphism from a finite discrete module to a discrete module is
fixed by an open normal subgroup. This is `exists_openNormalSubgroup_smul_eq_self` for the discrete
`G`-module `InternalHom G M N`, read back on `M →+ N`; it is the form used by the finite-quotient
system for continuous cohomology. -/
theorem exists_openNormalSubgroup_homAction_eq_self (φ : M →+ N) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, homAction u φ = φ := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) (M := InternalHom G M N)
    (InternalHom.of G φ)
  exact ⟨U, fun u hu => by simpa using congrArg InternalHom.toAddMonoidHom (hU u hu)⟩

end Profinite

end TauCeti
