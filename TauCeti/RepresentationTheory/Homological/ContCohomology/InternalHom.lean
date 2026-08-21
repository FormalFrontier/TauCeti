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
equivariance is `homAction_apply_smul` below. The design is not original here: the name `homAction`
and the definition below are adapted from the human-owned roadmap formalization in the accompanying
`TauCetiRoadmap/ProfiniteCohomology/Suggested.lean`, where they are pinned as a target signature
(with `sorry`ed proofs) by the roadmap's authors; the adaptation weakens the typeclass hypotheses to
those the proofs use, adds the carrier `InternalHom` on which the action can be an instance, and
discharges the proofs.

## Main definitions

* `TauCeti.homAction`: the conjugation action of `G` on `M →+ N`, with the action laws
  `homAction_one` and `homAction_mul` and the additivity laws `homAction_zero` and
  `homAction_add`.
* `TauCeti.InternalHom`: the carrier `M →+ N` equipped with that action, as a `DistribMulAction`
  instance. Its `TauCeti.InternalHom.of` and `TauCeti.InternalHom.toAddMonoidHom` translate to and
  from `M →+ N`, and `TauCeti.InternalHom.addEquivAddMonoidHom` bundles that translation as an
  additive equivalence, forgetting the action.
* `TauCeti.InternalHom.evalPairing`: evaluation out of the internal hom,
  `InternalHom G M N →+ (M →+ N)`, which is the roadmap's `evalPairing` on the carrier that carries
  the conjugation action; its equivariance is `TauCeti.InternalHom.evalPairing_equivariant`.

## Main results

* `TauCeti.homAction_apply_smul`: evaluation is equivariant; on the carrier this is
  `TauCeti.InternalHom.smul_apply_smul`.
* `TauCeti.homAction_eq_self_iff`: `g` fixes `φ` exactly when `φ` commutes with the action of `g`;
  so `φ` is fixed by all of `G` exactly when it is `G`-equivariant
  (`TauCeti.forall_homAction_eq_self_iff`).
* `TauCeti.isOpen_setOf_homAction_eq_self`: for finite discrete `M` and discrete `N` the set of
  group elements fixing `φ` is open. This is what the `ContinuousSMul G` instance on
  `TauCeti.InternalHom` rests on; with the discrete topology that carrier has by definition, it is
  what makes it again a discrete `G`-module in that setting.
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
assembled from Mathlib's `DistribSMul.toAddMonoidHom`, which bundles each `g • ·` as an additive
homomorphism, so that its additivity comes from `AddMonoidHom.comp`. It is then registered as a
genuine `DistribMulAction` on the wrapper `InternalHom G M N`, which is the object downstream
cohomology is meant to be applied to. The two actions on `M →+ N` agree when `G` acts trivially on
the source (`homAction_eq_smul_of_smul_eq_self`).

The additive structure on `InternalHom G M N` is transported from `M →+ N` along the equivalence
`equivAddMonoidHom`, as an `AddCommMonoid` in general and as an `AddCommGroup` when `N` is one.
The lemmas describing the transported structure (`toAddMonoidHom_zero`, `toAddMonoidHom_add`,
`of_zero`, `of_add`, their group-level counterparts, and the application lemmas of
`addEquivAddMonoidHom` and `evalPairing`) hold by `Equiv.add_def`/`Equiv.zero_def` on the
transported instance, hence definitionally; they are written `(rfl)` rather than `rfl` because the
module system rejects the latter for an *exported* theorem whose proof unfolds a definition that is
not `@[expose]`d, and neither equivalence needs to be exposed. Those lemmas are the intended
interface, so nothing downstream should need to unfold the transported instance itself.

Continuity in the group variable (`continuous_homAction_apply`) needs only a discrete source: `φ`
is then automatically continuous, and the two actions occurring in `g • φ (g⁻¹ • m)` are continuous
by hypothesis.

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
`isOpen_setOf_homAction_eq_self` rests on. `InternalHom G M N` carries the discrete topology by
definition, with no hypothesis on `M` or `N`: that is the intended topology precisely in the
discrete setting this file is written for, namely finite discrete `M` and discrete `N`, which is
also exactly where the action is continuous. For infinite `M` the internal hom in the category of
discrete `G`-modules is the sub-object of homomorphisms with open stabilizer, which is not
`InternalHom G M N`; nothing here claims otherwise.
-/

public section

namespace TauCeti

section Action

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N : Type*} [AddMonoid N] [DistribMulAction G N]

/-- The conjugation action of `G` on the internal hom `M →+ N`, sending `φ` to
`m ↦ g • φ (g⁻¹ • m)`. This is the action making evaluation equivariant; see
`homAction_apply_smul`. -/
def homAction (g : G) (φ : M →+ N) : M →+ N :=
  (DistribSMul.toAddMonoidHom N g).comp (φ.comp (DistribSMul.toAddMonoidHom M g⁻¹))

@[simp]
theorem homAction_apply (g : G) (φ : M →+ N) (m : M) : homAction g φ m = g • φ (g⁻¹ • m) := (rfl)

@[simp]
theorem homAction_one (φ : M →+ N) : homAction (1 : G) φ = φ := by
  ext m
  simp

@[simp]
theorem homAction_mul (g h : G) (φ : M →+ N) :
    homAction (g * h) φ = homAction g (homAction h φ) := by
  ext m
  simp [mul_smul, mul_inv_rev]

@[simp]
theorem homAction_zero (g : G) : homAction g (0 : M →+ N) = 0 := by
  ext m
  simp

section AddCommMonoid

variable {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- The conjugation action is additive in the homomorphism. This is the only one of the four laws
that needs the pointwise addition on `M →+ N`, hence a commutative codomain. -/
@[simp]
theorem homAction_add (g : G) (φ ψ : M →+ N) :
    homAction g (φ + ψ) = homAction g φ + homAction g ψ := by
  ext m
  simp

end AddCommMonoid

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

/-- The fixed points of the conjugation action are exactly the `G`-equivariant homomorphisms. -/
theorem forall_homAction_eq_self_iff {φ : M →+ N} :
    (∀ g : G, homAction g φ = φ) ↔ ∀ (g : G) (m : M), φ (g • m) = g • φ m :=
  forall_congr' fun _ => homAction_eq_self_iff

@[simp]
theorem homAction_id (g : G) : homAction g (AddMonoidHom.id N) = AddMonoidHom.id N :=
  homAction_eq_self_iff.mpr fun _ => rfl

/-- The conjugation action is functorial for composition of homomorphisms. -/
theorem homAction_comp {P : Type*} [AddMonoid P] [DistribMulAction G P] (g : G) (φ : M →+ N)
    (ψ : N →+ P) : homAction g (ψ.comp φ) = (homAction g ψ).comp (homAction g φ) := by
  ext m
  simp

/-- When `G` acts trivially on the source, the conjugation action on `M →+ N` is Mathlib's
codomain-pointwise action. -/
theorem homAction_eq_smul_of_smul_eq_self (h : ∀ (g : G) (m : M), g • m = m) (g : G) (φ : M →+ N) :
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
  {N : Type*} [AddMonoid N] [TopologicalSpace N] [DistribMulAction G N] [ContinuousSMul G N]

/-- Each value of the conjugation action is continuous in the group variable. Only the source `M`
is required to be discrete. -/
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
This is what the `ContinuousSMul G (InternalHom G M N)` instance below rests on, through
`continuousSMul_iff_stabilizer_isOpen`. -/
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
type on which continuous cohomology of the internal hom is to be taken. It carries the discrete
topology unconditionally, and is the internal hom of *discrete* `G`-modules exactly in the setting
this file is written for: `M` finite discrete and `N` discrete, which is also where the action is
continuous. -/
@[ext]
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
def equivAddMonoidHom : InternalHom G M N ≃ (M →+ N) where
  toFun := toAddMonoidHom
  invFun := of G
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommMonoid (InternalHom G M N) := fast_instance% (equivAddMonoidHom G).addCommMonoid

/-- The internal hom and `M →+ N` are the same additive monoid; they differ only in their
`G`-action. This is the additive carrier equivalence, forgetting the action. -/
def addEquivAddMonoidHom : InternalHom G M N ≃+ (M →+ N) :=
  { equivAddMonoidHom G with map_add' := fun _ _ => rfl }

/-- Evaluation out of the internal hom, bundled as an additive homomorphism: this is the roadmap's
`evalPairing`, on the carrier that carries the conjugation action. Its equivariance is
`evalPairing_equivariant`. -/
def evalPairing : InternalHom G M N →+ (M →+ N) := (addEquivAddMonoidHom G).toAddMonoidHom

variable {G}

@[simp]
theorem addEquivAddMonoidHom_apply (φ : InternalHom G M N) :
    addEquivAddMonoidHom G φ = φ.toAddMonoidHom := (rfl)

@[simp]
theorem addEquivAddMonoidHom_symm_apply (φ : M →+ N) :
    (addEquivAddMonoidHom G).symm φ = of G φ := (rfl)

@[simp]
theorem evalPairing_apply (φ : InternalHom G M N) : evalPairing G φ = φ.toAddMonoidHom := (rfl)

@[simp]
theorem of_toAddMonoidHom (φ : InternalHom G M N) : of G φ.toAddMonoidHom = φ := rfl

@[simp]
theorem toAddMonoidHom_inj {φ ψ : InternalHom G M N} :
    φ.toAddMonoidHom = ψ.toAddMonoidHom ↔ φ = ψ :=
  InternalHom.ext_iff.symm

@[simp]
theorem toAddMonoidHom_zero : (0 : InternalHom G M N).toAddMonoidHom = 0 := (rfl)

@[simp]
theorem toAddMonoidHom_add (φ ψ : InternalHom G M N) :
    (φ + ψ).toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom := (rfl)

@[simp]
theorem of_zero : of G (0 : M →+ N) = 0 := (rfl)

@[simp]
theorem of_add (φ ψ : M →+ N) : of G (φ + ψ) = of G φ + of G ψ := (rfl)

section AddCommGroup

variable {N : Type*} [AddCommGroup N] [DistribMulAction G N]

/-- For a codomain that is an additive commutative group, so is the internal hom; together with the
discrete topology below this is the `G`-module structure the roadmap's coefficients require. -/
instance : AddCommGroup (InternalHom G M N) := fast_instance% (equivAddMonoidHom G).addCommGroup

@[simp]
theorem toAddMonoidHom_neg (φ : InternalHom G M N) :
    (-φ).toAddMonoidHom = -φ.toAddMonoidHom := (rfl)

@[simp]
theorem toAddMonoidHom_sub (φ ψ : InternalHom G M N) :
    (φ - ψ).toAddMonoidHom = φ.toAddMonoidHom - ψ.toAddMonoidHom := (rfl)

@[simp]
theorem of_neg (φ : M →+ N) : of G (-φ) = -of G φ := (rfl)

@[simp]
theorem of_sub (φ ψ : M →+ N) : of G (φ - ψ) = of G φ - of G ψ := (rfl)

end AddCommGroup

/-- The conjugation action of `G` on the internal hom. -/
instance : SMul G (InternalHom G M N) where
  smul g φ := of G (homAction g φ.toAddMonoidHom)

@[simp]
theorem toAddMonoidHom_smul (g : G) (φ : InternalHom G M N) :
    (g • φ).toAddMonoidHom = homAction g φ.toAddMonoidHom := rfl

@[simp]
theorem smul_of (g : G) (φ : M →+ N) : g • of G φ = of G (homAction g φ) := rfl

instance : DistribMulAction G (InternalHom G M N) where
  one_smul φ := by ext m; simp
  mul_smul g h φ := by ext m; simp [homAction_mul]
  smul_zero g := by ext m; simp
  smul_add g φ ψ := by ext m; simp

/-- Evaluation is equivariant for the action on the internal hom; the carrier form of
`homAction_apply_smul`. Its restatement through the bundled pairing is
`evalPairing_equivariant`. -/
theorem smul_apply_smul (g : G) (φ : InternalHom G M N) (m : M) :
    (g • φ).toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m :=
  homAction_apply_smul g _ m

/-- The evaluation pairing is `G`-equivariant: this is the roadmap's `evalPairing_equivariant`,
`smul_apply_smul` read through the bundled `evalPairing`. -/
theorem evalPairing_equivariant (g : G) (φ : InternalHom G M N) (m : M) :
    evalPairing G (g • φ) (g • m) = g • evalPairing G φ m := by
  simp only [evalPairing_apply]
  exact smul_apply_smul g φ m

/-- The invariants of the internal hom are the `G`-equivariant homomorphisms. -/
theorem forall_smul_eq_self_iff {φ : InternalHom G M N} :
    (∀ g : G, g • φ = φ) ↔
      ∀ (g : G) (m : M), φ.toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m := by
  simp only [InternalHom.ext_iff, toAddMonoidHom_smul]
  exact forall_homAction_eq_self_iff

/-- The fixed points of the internal hom are the `G`-equivariant homomorphisms; the same statement
as `forall_smul_eq_self_iff`, phrased through Mathlib's `MulAction.fixedPoints`, which is the
invariants object the surrounding development uses. -/
theorem mem_fixedPoints_iff {φ : InternalHom G M N} :
    φ ∈ MulAction.fixedPoints G (InternalHom G M N) ↔
      ∀ (g : G) (m : M), φ.toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m :=
  MulAction.mem_fixedPoints.trans forall_smul_eq_self_iff

/-- The internal hom always carries the discrete topology, by definition; see the implementation
notes for when that is the intended topology. -/
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
      InternalHom.ext_iff, toAddMonoidHom_smul]
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
