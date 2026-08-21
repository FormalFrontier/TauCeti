/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.MulAction

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

## Main results

* `TauCeti.homAction_apply_smul`: evaluation is equivariant.
* `TauCeti.homAction_eq_self_iff`: `g` fixes `φ` exactly when `φ` commutes with the action of `g`;
  so `φ` is fixed by all of `G` exactly when it is `G`-equivariant
  (`TauCeti.forall_homAction_eq_self_iff`).
* `TauCeti.isOpen_setOf_homAction_eq_self`: for finite discrete `M` and discrete `N` the set of
  group elements fixing `φ` is open, which is continuity of the conjugation action on the discrete
  module `M →+ N`.
* `TauCeti.exists_openNormalSubgroup_homAction_eq_self`: over a profinite group that set contains
  an open normal subgroup.

## Implementation notes

Mathlib already puts the codomain-pointwise action `(g • φ) m = g • φ m` on `M →+ N`, as the
instance in `Mathlib/Algebra/GroupWithZero/Action/Hom.lean`, so the conjugation action cannot be
registered as an instance on the same type; it is a plain function of `g`, and its action and
additivity laws are the four lemmas listed above. The two actions agree when `G` acts trivially on
the source (`homAction_eq_smul`).

`Representation.linHom` is the same conjugation construction for `k`-linear maps `V →ₗ[k] W` of
bundled representations. It is not used as the definition here because the coefficient theory of
the roadmap is written in the unbundled classes `[AddCommGroup M] [DistribMulAction G M]` and its
cochains take values in `M →+ N`, a type distinct from `M →ₗ[ℤ] N`; the identification of the two
constructions is `toIntLinearMap_homAction`.

Mathlib puts no topology on `M →+ N`. Discreteness of the internal hom enters here through the
discreteness of the ambient function space `M → N`, which is what
`isOpen_setOf_homAction_eq_self` rests on.
-/

public section

namespace TauCeti

section Action

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- The conjugation action of `G` on the internal hom `M →+ N`, sending `φ` to
`m ↦ g • φ (g⁻¹ • m)`. This is the action making evaluation equivariant; see
`homAction_apply_smul`. -/
def homAction (g : G) (φ : M →+ N) : M →+ N where
  toFun m := g • φ (g⁻¹ • m)
  map_zero' := by simp
  map_add' m₁ m₂ := by simp

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
conjugation action amounts to; compare `continuousSMul_iff_stabilizer_isOpen`, which cannot be
applied literally because the conjugation action is not an instance. -/
theorem isOpen_setOf_homAction_eq_self [Finite M] [DiscreteTopology N] (φ : M →+ N) :
    IsOpen {g : G | homAction g φ = φ} := by
  have hset : {g : G | homAction g φ = φ}
      = (fun g : G => ((homAction g φ : M →+ N) : M → N)) ⁻¹' {(φ : M → N)} := by
    ext g
    simp [DFunLike.coe_fn_eq]
  rw [hset]
  exact (continuous_homAction_coe φ).isOpen_preimage _ (isOpen_discrete _)

end Topology

section Profinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {M : Type*} [AddMonoid M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Finite M]
  {N : Type*} [AddCommMonoid N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [ContinuousSMul G N]

/-- Over a profinite group, a homomorphism from a finite discrete module to a discrete module is
fixed by an open normal subgroup. This is the statement that the internal hom is again a discrete
`G`-module, in the form used by the finite-quotient system for continuous cohomology. -/
theorem exists_openNormalSubgroup_homAction_eq_self (φ : M →+ N) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, homAction u φ = φ := by
  have h1 : (1 : G) ∈ {g : G | homAction g φ = φ} := homAction_one φ
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_setOf_homAction_eq_self φ) h1
  exact ⟨U, fun u hu => hU hu⟩

end Profinite

end TauCeti
