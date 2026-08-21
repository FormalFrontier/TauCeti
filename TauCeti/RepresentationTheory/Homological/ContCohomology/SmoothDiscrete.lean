/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.Algebra.MulAction

/-!
# Smooth discrete topological representations

An object `X : TopRep R G` carries one continuous operator `X.ρ g` per group element, and nothing
in that data forces the assignment `g ↦ X.ρ g` to be continuous in the group variable. So an
object whose underlying module happens to be discrete can still have non-open point stabilizers,
and there is no dictionary between all of `TopRep R G` and the discrete `G`-modules of Mathlib's
unbundled classes.

This file cuts out the subcategory where such a dictionary does exist. `TauCeti.IsSmoothDiscrete`
says that the underlying module is discrete and that every set `{g | X.ρ g x = x}` is open, which
for a discrete module is exactly continuity of the action; `TauCeti.ofDiscreteModule` turns a
discrete `G`-module into an object of `TopRep R G`; and the two translations are shown to be
mutually inverse there, both on objects and on morphisms.

## Main definitions

* `TauCeti.ofDiscreteModule`: a discrete `G`-module as an object of `TopRep R G`.
* `TauCeti.IsSmoothDiscrete`: the objects of `TopRep R G` in the image of that dictionary.
* `TopRep.distribMulAction`: the `G`-action on the underlying module of an object of
  `TopRep R G`, read off from its operators.
* `TauCeti.ofDiscreteModuleMap`: a `G`-equivariant `R`-linear map of discrete modules as a
  morphism of `TopRep R G`.

## Main results

* `TauCeti.isSmoothDiscrete_iff_continuousSMul`: for a topological group, smoothness of a discrete
  object is continuity of the action map `G × X.V → X.V`.
* `TauCeti.ofDiscreteModule_isSmoothDiscrete`: the dictionary lands in the subcategory.
* `TauCeti.ofDiscreteModule_eq_self`: conversely, a discrete object *is* the image of its own
  underlying module.
* `TauCeti.ofDiscreteModuleHomEquiv`: morphisms between objects in the image are exactly the
  `G`-equivariant `R`-linear maps.
* `TauCeti.IsSmoothDiscrete.res`: smoothness is inherited by restriction along a continuous
  homomorphism.

This implements the "smooth discrete objects" and "the categorical dictionary" milestones of
Layer 1 of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`. The
carrier `TopRep` and its functoriality are Mathlib's, and are consumed rather than restated.
-/

public section

/-! ### The action on the underlying module

`TopRep` is Mathlib's type, so its namespace is Mathlib's: the derived action and its companions
sit in the root `TopRep` namespace, not under `TauCeti`, which is what makes `X.distribMulAction`
elaborate as dot notation. -/

namespace TopRep

variable {R : Type*} [Ring R] [TopologicalSpace R] {G : Type*} [Monoid G]

/-- The `G`-action on the underlying module of an object of `TopRep R G`, read off from its
operators. This is the object half of the translation back to Mathlib's unbundled classes. It is
not a global instance: `X.V` is a projection, so instance search would attempt it on every action
goal. Files that need it declare it a `local instance`, as this one does below. Its whole public
behaviour is `TopRep.distribMulAction_smul`, so consumers never need the body. -/
@[instance_reducible] def distribMulAction (X : TopRep R G) : DistribMulAction G X.V where
  smul g x := X.ρ g x
  one_smul x := congr($(map_one X.ρ) x)
  mul_smul g h x := congr($(map_mul X.ρ g h) x)
  smul_zero g := map_zero (X.ρ g)
  smul_add g x y := map_add (X.ρ g) x y

attribute [local instance] distribMulAction

@[simp] lemma distribMulAction_smul (X : TopRep R G) (g : G) (x : X.V) :
    g • x = X.ρ g x := (rfl)

/-- The derived `G`-action commutes with the scalars, because every operator is `R`-linear. -/
lemma smulCommClass (X : TopRep R G) : SMulCommClass G R X.V :=
  ⟨fun g r x ↦ map_smul (X.ρ g) r x⟩

end TopRep

namespace TauCeti

open CategoryTheory ContRepresentation

universe u v w

/-! ### Discrete modules as topological representations -/

section OfDiscreteModule

variable (R : Type u) [Ring R] [TopologicalSpace R] (G : Type v) [Monoid G]
  (M : Type w) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G R M] [ContinuousSMul R M]

/-- A discrete `G`-module, in Mathlib's unbundled classes, as an object of `TopRep R G`. Every
operator is continuous because the module is discrete; continuity in the group variable is
`TauCeti.ofDiscreteModule_isSmoothDiscrete`, and needs `ContinuousSMul G M`.

This is the continuous counterpart of `Rep.ofDistribMulAction`. The body is `@[expose]`d because a
consumer must see that the underlying module of the result is `M` itself before it can state
anything about the elements of that module. -/
@[expose] def ofDiscreteModule : TopRep R G :=
  .of (ContRepresentation.ofMonoidHom
    { toFun g := ⟨Representation.ofDistribMulAction R G M g, continuous_of_discreteTopology⟩
      map_one' := by ext m; exact one_smul G m
      map_mul' g h := by ext m; exact mul_smul g h m })

@[simp] lemma ofDiscreteModule_V : (ofDiscreteModule R G M).V = M := (rfl)

variable {R G M}

@[simp] lemma ofDiscreteModule_ρ_apply (g : G) (m : M) :
    (ofDiscreteModule R G M).ρ g m = g • m := (rfl)

end OfDiscreteModule

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Smooth discrete objects -/

section IsSmoothDiscrete

variable (R : Type u) [Ring R] [TopologicalSpace R]
  {G : Type v} [Monoid G] [TopologicalSpace G]

/-- An object of `TopRep R G` is **smooth discrete** when its underlying module is discrete and
every point stabilizer `{g | X.ρ g x = x}` is open. For a discrete module over a topological group
the second condition is exactly continuity of the action in the group variable
(`TauCeti.isSmoothDiscrete_iff_continuousSMul`), which the data of `TopRep` does not supply. -/
structure IsSmoothDiscrete (X : TopRep R G) : Prop where
  /-- the underlying module is discrete -/
  discreteTopology : DiscreteTopology X.V
  /-- every point stabilizer is open -/
  stabilizer_isOpen (x : X.V) : IsOpen {g : G | X.ρ g x = x}

variable {R}

omit [TopologicalSpace G] in
/-- A discrete object is the image of its own underlying module under the dictionary; openness of
the stabilizers plays no part, and a smooth discrete object supplies the discreteness through
`TauCeti.IsSmoothDiscrete.discreteTopology`. With `TauCeti.ofDiscreteModule_isSmoothDiscrete` this
is the object half of the equivalence between the discrete `G`-modules and the smooth discrete
objects of `TopRep R G`. -/
@[simp] lemma ofDiscreteModule_eq_self (X : TopRep R G) [DiscreteTopology X.V] :
    ofDiscreteModule R G X.V = X := by
  have h : (ofDiscreteModule R G X.V).ρ = X.ρ :=
    DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun (x : X.V) ↦
      (ofDiscreteModule_ρ_apply g x).trans (TopRep.distribMulAction_smul X g x)
  -- The two objects have the same underlying module by construction, and `X` is `TopRep.of X.ρ`
  -- by structure eta, so they agree as soon as their operators do.
  exact congrArg (TopRep.of (X := X.V)) h

variable (R G)

/-- The dictionary lands in the smooth discrete subcategory: the point stabilizer of `m` is the
preimage of the open set `{m}` under the continuous map `g ↦ g • m`. -/
lemma ofDiscreteModule_isSmoothDiscrete (M : Type w) [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [SMulCommClass G R M]
    [ContinuousSMul R M] [ContinuousSMul G M] :
    IsSmoothDiscrete R (ofDiscreteModule R G M) :=
  ⟨‹DiscreteTopology M›, fun (m : M) ↦
    IsOpen.preimage (f := fun g : G ↦ g • m) (by fun_prop) (isOpen_discrete {m})⟩

end IsSmoothDiscrete

section SmoothOverGroup

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G]

/-- Smoothness is inherited by restriction along a continuous homomorphism: the stabilizers of
`TopRep.res φ X` are the preimages under `φ` of the stabilizers of `X`. Only `TopRep.res`, which
Mathlib states for a group, forces `G` to be one here; `H` may be any monoid. -/
lemma IsSmoothDiscrete.res {H : Type*} [Monoid H] [TopologicalSpace H] {φ : H →* G}
    (hφ : Continuous φ) {X : TopRep R G} (hX : IsSmoothDiscrete R X) :
    IsSmoothDiscrete R (TopRep.res φ X) :=
  ⟨hX.discreteTopology, fun x ↦ (hX.stabilizer_isOpen x).preimage hφ⟩

variable [IsTopologicalGroup G]

/-- For a discrete object of `TopRep R G`, smoothness is continuity of the action map
`G × X.V → X.V`. -/
lemma isSmoothDiscrete_iff_continuousSMul (X : TopRep R G) [DiscreteTopology X.V] :
    IsSmoothDiscrete R X ↔ ContinuousSMul G X.V := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  exact ⟨fun h x ↦ h.stabilizer_isOpen x, fun h ↦ ⟨‹_›, h⟩⟩

/-- The derived action on a smooth discrete object is continuous, so the underlying module of such
an object is a discrete `G`-module in the unbundled classes. -/
lemma IsSmoothDiscrete.continuousSMul {X : TopRep R G} (hX : IsSmoothDiscrete R X) :
    haveI := hX.discreteTopology
    ContinuousSMul G X.V :=
  haveI := hX.discreteTopology
  (isSmoothDiscrete_iff_continuousSMul X).1 hX

end SmoothOverGroup

/-! ### The dictionary on objects and morphisms -/

section Dictionary

variable (R : Type u) [Ring R] [TopologicalSpace R] (G : Type v) [Monoid G]
  (M : Type w) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G R M] [ContinuousSMul R M]

variable (N : Type w) [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [SMulCommClass G R N] [ContinuousSMul R N]

variable {R G M N}

/-- A `G`-equivariant `R`-linear map of discrete modules as a morphism of `TopRep R G`.
Continuity is automatic, the source being discrete. -/
def ofDiscreteModuleMap (f : M →ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    ofDiscreteModule R G M ⟶ ofDiscreteModule R G N :=
  TopRep.ofHom
    { toContinuousLinearMap := ⟨f, continuous_of_discreteTopology⟩
      isIntertwining' g := by ext m; exact hf g m }

@[simp] lemma ofDiscreteModuleMap_hom_apply (f : M →ₗ[R] N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (m : M) :
    (ofDiscreteModuleMap f hf).hom m = f m := (rfl)

@[simp] lemma ofDiscreteModuleMap_id :
    ofDiscreteModuleMap (LinearMap.id (R := R) (M := M)) (fun _ _ ↦ rfl) =
      𝟙 (ofDiscreteModule R G M) := by
  -- Both sides fix `m`: `ofDiscreteModuleMap_hom_apply` on the left, `TopRep.id_apply` on the
  -- right.
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) ↦ ?_)
  exact (ofDiscreteModuleMap_hom_apply _ _ m).trans
    (TopRep.id_apply (ofDiscreteModule R G M) m).symm

@[simp] lemma ofDiscreteModuleMap_comp {P : Type w} [AddCommGroup P] [Module R P]
    [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction G P] [SMulCommClass G R P]
    [ContinuousSMul R P]
    (f : M →ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (f' : N →ₗ[R] P) (hf' : ∀ (g : G) (n : N), f' (g • n) = g • f' n) :
    ofDiscreteModuleMap (f'.comp f) (fun g m ↦ by simp only [LinearMap.comp_apply, hf, hf']) =
      ofDiscreteModuleMap f hf ≫ ofDiscreteModuleMap f' hf' := by
  -- Both sides send `m` to `f' (f m)`: `ofDiscreteModuleMap_hom_apply` on each factor, and
  -- `TopRep.comp_apply` for the composite on the right.
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) ↦ ?_)
  exact (ofDiscreteModuleMap_hom_apply _ _ m).trans <|
    (congrArg (⇑f') (ofDiscreteModuleMap_hom_apply f hf m).symm).trans <|
      (ofDiscreteModuleMap_hom_apply f' hf' _).symm.trans
        (TopRep.comp_apply (ofDiscreteModuleMap f hf) (ofDiscreteModuleMap f' hf') m).symm

variable (R G M N)

/-- Morphisms between objects in the image of the dictionary are exactly the `G`-equivariant
`R`-linear maps: continuity of such a map is automatic on discrete modules. This is the morphism
half of the equivalence between the discrete `G`-modules and the smooth discrete objects. -/
def ofDiscreteModuleHomEquiv :
    (ofDiscreteModule R G M ⟶ ofDiscreteModule R G N) ≃+
      Representation.IntertwiningMap (Representation.ofDistribMulAction R G M)
        (Representation.ofDistribMulAction R G N) where
  toFun φ := (φ.hom.toContinuousLinearMap.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _
    fun g m ↦ φ.hom.isIntertwining g m
  invFun f := ofDiscreteModuleMap f.toLinearMap fun g m ↦ f.isIntertwining _ _ g m
  -- Both round trips rewrap the *same* underlying function, so it is enough to compare the two
  -- sides at a point, where `TauCeti.ofDiscreteModuleMap_hom_apply` identifies them.
  left_inv φ := by
    ext (m : M); exact ofDiscreteModuleMap_hom_apply (G := G) _ _ m
  right_inv f := by
    ext (m : M)
    exact ofDiscreteModuleMap_hom_apply (G := G) f.toLinearMap
      (fun g m ↦ f.isIntertwining _ _ g m) m
  -- Addition of morphisms of `TopRep` is addition of the underlying intertwining maps
  -- (`TopRep.hom_add`), so the translation is additive pointwise.
  map_add' φ ψ := by
    ext (m : M); exact congr($(TopRep.hom_add _ _ φ ψ) m)

variable {R G M N}

@[simp] lemma ofDiscreteModuleHomEquiv_apply
    (φ : ofDiscreteModule R G M ⟶ ofDiscreteModule R G N) (m : M) :
    ofDiscreteModuleHomEquiv R G M N φ m = φ.hom m := (rfl)

@[simp] lemma ofDiscreteModuleHomEquiv_symm_apply
    (f : Representation.IntertwiningMap (Representation.ofDistribMulAction R G M)
      (Representation.ofDistribMulAction R G N)) (m : M) :
    ((ofDiscreteModuleHomEquiv R G M N).symm f).hom m = f m := (rfl)

end Dictionary

/-! ### The smooth discrete subcategory is proper -/

section NotSmooth

/-- The coefficients of the non-example below carry the discrete topology. -/
local instance instTopologicalSpaceZModThree : TopologicalSpace (ZMod 3) := ⊥

/-- The topology chosen just above is by definition the discrete one. -/
local instance instDiscreteTopologyZModThree : DiscreteTopology (ZMod 3) := ⟨rfl⟩

/-- The group of the non-example below carries the indiscrete topology, whose only open sets are
`∅` and the whole group. -/
local instance instTopologicalSpaceUnitsZModThree : TopologicalSpace (ZMod 3)ˣ := ⊤

/-- An object of `TopRep R G` whose underlying module is discrete need not be smooth. Here the
two-element group `(ZMod 3)ˣ` acts on the discrete module `ZMod 3` by multiplication, so the
stabilizer of `1` is the singleton `{1}`; giving the group the indiscrete topology makes that
singleton non-open. This is why the dictionary above is an equivalence with the smooth discrete
objects and not with all of `TopRep`, and it is what the hypothesis `ContinuousSMul G M` of
`TauCeti.ofDiscreteModule_isSmoothDiscrete` rules out. -/
lemma not_isSmoothDiscrete_ofDiscreteModule_units_zmod :
    ¬ IsSmoothDiscrete ℤ (ofDiscreteModule ℤ (ZMod 3)ˣ (ZMod 3)) := by
  intro h
  have hopen : IsOpen {g : (ZMod 3)ˣ | g • (1 : ZMod 3) = 1} := h.stabilizer_isOpen (1 : ZMod 3)
  rcases (TopologicalSpace.isOpen_top_iff _).1 hopen with h₀ | h₁
  · exact Set.eq_empty_iff_forall_notMem.1 h₀ 1 (one_smul _ _)
  · have hneg : (-1 : (ZMod 3)ˣ) • (1 : ZMod 3) = 1 := Set.eq_univ_iff_forall.1 h₁ (-1)
    revert hneg
    decide

end NotSmooth

end TauCeti
