/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Continuous.TopRep
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
for a discrete module over a topological *group* is exactly continuity of the action;
`TauCeti.ofDiscreteModule` turns a discrete `G`-module into an object of `TopRep R G`; and on the
discrete `G`-modules whose `G`-action is continuous — not on all of them — the two translations are
shown to be mutually inverse, both on objects and on morphisms.

The construction `TauCeti.ofDiscreteModule` itself is available for *every* discrete `G`-module,
since a discrete module makes each operator continuous whatever the action does in the group
variable. It is only its *smoothness* that needs `ContinuousSMul G M`, and that hypothesis cannot
be dropped: `TauCeti.not_isSmoothDiscrete_ofDiscreteModule_units_zmod` exhibits a discrete module
with a discontinuous action whose object is discrete but not smooth. So the source side of the
dictionary is the discrete `G`-modules with continuous `G`-action, and the image of the
unrestricted construction is larger than the smooth discrete subcategory.

## Main definitions

* `TauCeti.ofDiscreteModule`: a discrete `G`-module as an object of `TopRep R G`.
* `TauCeti.IsSmoothDiscrete`: the objects of `TopRep R G` whose underlying module is discrete and
  whose point stabilizers are open.
* `TopRep.distribMulAction`: the `G`-action on the underlying module of an object of
  `TopRep R G`, read off from its operators.
* `TauCeti.ofDiscreteModuleMap`: a `G`-equivariant `R`-linear map of discrete modules as a
  morphism of `TopRep R G`.
* `TauCeti.SmoothDiscreteTopRep`: the smooth discrete objects as a full subcategory of
  `TopRep R G`.
* `TauCeti.DiscreteRep`, `TauCeti.DiscreteRepHom`: the discrete `G`-modules with continuous
  `G`-action as a category, the source side of the dictionary in bundled form.
* `TauCeti.toSmoothDiscrete`, `TauCeti.ofSmoothDiscrete`: the two translations as functors.

## Main results

* `TauCeti.isSmoothDiscrete_iff_continuousSMul`: for a topological group, smoothness of a discrete
  object is continuity of the action map `G × X.V → X.V`.
* `TauCeti.isSmoothDiscrete_iff_isContinuous`: the predicate is Mathlib's `Action.IsContinuous`
  together with discreteness, read on `Action (TopModuleCat R) G` through
  `TopRep.toActionTopModFunc`, so the subcategory below is Mathlib's `DiscreteContAction` carried
  across `TopRep.TopRepEquivActionTop` rather than a second notion.
* `TauCeti.ofDiscreteModule_isSmoothDiscrete`: a discrete `G`-module with continuous `G`-action
  lands in the subcategory.
* `TauCeti.ofDiscreteModule_eq_self`: conversely, a discrete object *is* the image of its own
  underlying module.
* `TauCeti.ofDiscreteModuleHomAddEquiv`: morphisms between objects in the image are exactly the
  `G`-equivariant `R`-linear maps.
* `TauCeti.IsSmoothDiscrete.res`: smoothness is inherited by restriction along a continuous
  homomorphism.
* `TauCeti.discreteRepEquivSmoothTopRep`: the two translations are an equivalence of categories
  between `TauCeti.DiscreteRep R G` and `TauCeti.SmoothDiscreteTopRep R G`.
* `TauCeti.not_isSmoothDiscrete_ofDiscreteModule_units_zmod`: a discrete object that is not
  smooth, so the subcategory is proper and the continuity hypothesis above is needed.

## Roadmap

This serves Layer 1 of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`,
whose "smooth discrete objects" and "the categorical dictionary" bullets it addresses. What is
delivered here is the predicate `TauCeti.IsSmoothDiscrete`, its closure under restriction, and the
dictionary in both directions up to the equivalence of categories; the closure of the smooth
discrete objects under finite products, subobjects and quotients, which the first of those bullets
also asks for, is not yet statable, because Mathlib's `TopRep` carries no limit, subobject or
quotient API to state it against.

The names, signatures and structure fields below follow the human-authored
`TauCetiRoadmap/ProfiniteCohomology/Suggested.lean`, which fixes `TauCeti.IsSmoothDiscrete` and its
two fields, `TauCeti.ofDiscreteModule`, `TauCeti.ofDiscreteModule_isSmoothDiscrete`,
`TauCeti.ofDiscreteModuleMap`, `TauCeti.SmoothDiscreteTopRep`, `TauCeti.DiscreteRep` and its field
list, `TauCeti.DiscreteRepHom`, `TauCeti.toSmoothDiscrete`, `TauCeti.ofSmoothDiscrete` and
`TauCeti.discreteRepEquivSmoothTopRep`. The carrier `TopRep` and its functoriality are Mathlib's,
and are consumed rather than restated.
-/

public section

/-! ### The action on the underlying module

`TopRep` is Mathlib's type, so its namespace is Mathlib's: the derived action and its companions
sit in the root `TopRep` namespace, not under `TauCeti`, which is what makes `X.distribMulAction`
elaborate as dot notation. -/

namespace TopRep

section Monoid

variable {R : Type*} [Ring R] [TopologicalSpace R] {G : Type*} [Monoid G]

/-- The `G`-action on the underlying module of an object of `TopRep R G`, read off from its
operators. This is the object half of the translation back to Mathlib's unbundled classes. It is
not a global instance: `X.V` is a projection, so instance search would attempt it on every action
goal. Files that need it declare it a `local instance`, as this one does below. Its behaviour is
`TopRep.distribMulAction_smul`; the body is `@[expose]`d only because the round trip of the
dictionary below (`TauCeti.discreteRepEquivSmoothTopRep`) returns an object carrying this very
instance, and identifying it with the one it started from is a definitional step. -/
@[expose, instance_reducible] def distribMulAction (X : TopRep R G) : DistribMulAction G X.V where
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

end Monoid

section Group

variable {R : Type*} [Ring R] [TopologicalSpace R] {G : Type*} [Group G]

attribute [local instance] distribMulAction

/-- The point stabilizers of the derived action, as sets, are the sets `{g | X.ρ g x = x}` that
`TauCeti.IsSmoothDiscrete` is phrased with. This is the bridge between Mathlib's
`MulAction.stabilizer`, in which `continuousSMul_iff_stabilizer_isOpen` is stated, and that
phrasing. -/
lemma coe_stabilizer (X : TopRep R G) (x : X.V) :
    (MulAction.stabilizer G x : Set G) = {g : G | X.ρ g x = x} := by
  ext g
  simp [MulAction.mem_stabilizer_iff]

end Group

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
operator is continuous because the module is discrete, which is all this construction needs;
continuity in the group variable is a separate hypothesis `ContinuousSMul G M`, carried by
`TauCeti.ofDiscreteModule_isSmoothDiscrete`. So the result is a discrete object of `TopRep R G`
for any discrete module, and a *smooth* discrete one as soon as that hypothesis is available;
`TauCeti.not_isSmoothDiscrete_ofDiscreteModule_units_zmod` is a module where it is not.

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

@[simp] lemma ofDiscreteModule_ρ_apply_apply (g : G) (m : M) :
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

/-- Smoothness is inherited by restriction along a continuous homomorphism: the stabilizers of
the restricted object are the preimages under `φ` of the stabilizers of `X`. The restriction is
written `TopRep.of (X.ρ.restrict φ)` rather than `TopRep.res φ X` only so that `G` may be a
monoid: Mathlib declares `TopRep.res` under a `[Group G]` section variable. Nothing is lost,
because `TopRep.res` is a reducible abbreviation for exactly this object, so for a group `G` this
lemma proves the goal `IsSmoothDiscrete R (TopRep.res φ X)` verbatim. -/
lemma IsSmoothDiscrete.res {H : Type*} [Monoid H] [TopologicalSpace H] {φ : H →* G}
    (hφ : Continuous φ) {X : TopRep R G} (hX : IsSmoothDiscrete R X) :
    IsSmoothDiscrete R (TopRep.of (X.ρ.restrict φ)) := by
  refine ⟨hX.discreteTopology, fun x ↦ ?_⟩
  have hpre : {h : H | (TopRep.of (X.ρ.restrict φ)).ρ h x = x} = φ ⁻¹' {g : G | X.ρ g x = x} := by
    ext h
    simp
  rw [hpre]
  exact (hX.stabilizer_isOpen x).preimage hφ

omit [TopologicalSpace G] in
/-- A discrete object is the image of its own underlying module under the dictionary; openness of
the stabilizers plays no part, and a smooth discrete object supplies the discreteness through
`TauCeti.IsSmoothDiscrete.discreteTopology`. Read on a *smooth* discrete `X`, whose underlying
module then has a continuous action by `TauCeti.IsSmoothDiscrete.continuousSMul`, this and
`TauCeti.ofDiscreteModule_isSmoothDiscrete` are the object half of the equivalence between the
discrete `G`-modules with continuous `G`-action and the smooth discrete objects of `TopRep R G`.
Read on an arbitrary discrete `X` it says less: the image of `TauCeti.ofDiscreteModule` over all
discrete modules is every discrete object, smooth or not
(`TauCeti.not_isSmoothDiscrete_ofDiscreteModule_units_zmod`). -/
@[simp] lemma ofDiscreteModule_eq_self (X : TopRep R G) [DiscreteTopology X.V] :
    ofDiscreteModule R G X.V = X := by
  have h : (ofDiscreteModule R G X.V).ρ = X.ρ :=
    DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun (x : X.V) ↦
      (ofDiscreteModule_ρ_apply_apply g x).trans (TopRep.distribMulAction_smul X g x)
  -- The two objects have the same underlying module by construction, and `X` is `TopRep.of X.ρ`
  -- by structure eta, so they agree as soon as their operators do.
  exact congrArg (TopRep.of (X := X.V)) h

variable (R G)

/-- The dictionary lands in the smooth discrete subcategory: the point stabilizer of `m` is the
preimage of the open set `{m}` under the continuous map `g ↦ g • m`. -/
lemma ofDiscreteModule_isSmoothDiscrete (M : Type w) [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [SMulCommClass G R M]
    [ContinuousSMul R M] [ContinuousSMul G M] :
    IsSmoothDiscrete R (ofDiscreteModule R G M) := by
  refine ⟨‹DiscreteTopology M›, fun (m : M) ↦ ?_⟩
  have hpre : {g : G | (ofDiscreteModule R G M).ρ g m = m} = (fun g : G ↦ g • m) ⁻¹' {m} := by
    ext g
    -- After `ofDiscreteModule_ρ_apply_apply` both sides read `g • m = m`; the last step is the
    -- membership in the singleton, which `simp` leaves at reducible transparency.
    simp
    rfl
  rw [hpre]
  exact (isOpen_discrete {m}).preimage (by fun_prop)

end IsSmoothDiscrete

section SmoothOverGroup

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a discrete object of `TopRep R G`, smoothness is continuity of the action map
`G × X.V → X.V`. -/
lemma isSmoothDiscrete_iff_continuousSMul (X : TopRep R G) [DiscreteTopology X.V] :
    IsSmoothDiscrete R X ↔ ContinuousSMul G X.V := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  simp only [X.coe_stabilizer]
  exact ⟨fun h x ↦ h.stabilizer_isOpen x, fun h ↦ ⟨‹_›, h⟩⟩

/-- The derived action on a smooth discrete object is continuous, so the underlying module of such
an object is a discrete `G`-module in the unbundled classes. -/
lemma IsSmoothDiscrete.continuousSMul {X : TopRep R G} (hX : IsSmoothDiscrete R X) :
    haveI := hX.discreteTopology
    ContinuousSMul G X.V :=
  haveI := hX.discreteTopology
  (isSmoothDiscrete_iff_continuousSMul X).1 hX

/-- Smoothness is Mathlib's continuity condition on the corresponding object of
`Action (TopModuleCat R) G`, transported along `TopRep.toActionTopModFunc`: the two conditions of
`TauCeti.IsSmoothDiscrete` are exactly `ContAction.IsDiscrete` and `Action.IsContinuous` there. So
the smooth discrete objects of `TopRep R G` are the objects `TopRep.TopRepEquivActionTop` carries
into `DiscreteContAction (TopModuleCat R) G`, and this file introduces no second notion. The
predicate is nonetheless stated on `TopRep R G` directly, because that is the carrier
`continuousCohomology` is defined on. -/
lemma isSmoothDiscrete_iff_isContinuous (X : TopRep.{w} R G) :
    IsSmoothDiscrete R X ↔
      DiscreteTopology X.V ∧ (TopRep.toActionTopModFunc.obj X).IsContinuous := by
  constructor
  · intro h
    have := h.discreteTopology
    exact ⟨h.discreteTopology, (isSmoothDiscrete_iff_continuousSMul X).1 h⟩
  · rintro ⟨hd, hc⟩
    have := hd
    exact (isSmoothDiscrete_iff_continuousSMul X).2 hc

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
Continuity is automatic, the source being discrete. The body is `@[expose]`d for the same reason
as `TauCeti.ofDiscreteModule`'s: the equivalence of categories below is built from this
constructor, and an exposed definition may only be built from exposed ones. -/
@[expose] def ofDiscreteModuleMap (f : M →ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    ofDiscreteModule R G M ⟶ ofDiscreteModule R G N :=
  TopRep.ofHom
    { toContinuousLinearMap := ⟨f, continuous_of_discreteTopology⟩
      isIntertwining' g := by ext m; exact hf g m }

@[simp] lemma ofDiscreteModuleMap_hom_apply (f : M →ₗ[R] N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (m : M) :
    (ofDiscreteModuleMap f hf).hom m = f m := (rfl)

/-- The morphism half of the dictionary preserves identities: the identity linear map of a discrete
module becomes the identity morphism of the object it names. -/
@[simp] lemma ofDiscreteModuleMap_id :
    ofDiscreteModuleMap (LinearMap.id (R := R) (M := M)) (fun _ _ ↦ rfl) =
      𝟙 (ofDiscreteModule R G M) := by
  -- Both sides fix `m`: `ofDiscreteModuleMap_hom_apply` on the left, `TopRep.id_apply` on the
  -- right.
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) ↦ ?_)
  exact (ofDiscreteModuleMap_hom_apply _ _ m).trans
    (TopRep.id_apply (ofDiscreteModule R G M) m).symm

/-- The morphism half of the dictionary preserves composition: the composite of two `G`-equivariant
`R`-linear maps becomes the composite of the two morphisms they name. -/
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
`R`-linear maps: continuity of such a map is automatic on discrete modules. Restricted to modules
with continuous `G`-action, where the two objects are smooth, this is the morphism half of the
equivalence between the discrete `G`-modules with continuous `G`-action and the smooth discrete
objects; continuity in the group variable is irrelevant to the statement, so it is proved here
without that hypothesis. -/
def ofDiscreteModuleHomAddEquiv :
    (ofDiscreteModule R G M ⟶ ofDiscreteModule R G N) ≃+
      Representation.IntertwiningMap (Representation.ofDistribMulAction R G M)
        (Representation.ofDistribMulAction R G N) where
  toFun φ := φ.hom.toIntertwiningMap
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

@[simp] lemma ofDiscreteModuleHomAddEquiv_apply_apply
    (φ : ofDiscreteModule R G M ⟶ ofDiscreteModule R G N) (m : M) :
    ofDiscreteModuleHomAddEquiv R G M N φ m = φ.hom m := (rfl)

@[simp] lemma ofDiscreteModuleHomAddEquiv_symm_apply_hom_apply
    (f : Representation.IntertwiningMap (Representation.ofDistribMulAction R G M)
      (Representation.ofDistribMulAction R G N)) (m : M) :
    ((ofDiscreteModuleHomAddEquiv R G M N).symm f).hom m = f m := (rfl)

end Dictionary

/-! ### The two coefficient categories -/

section CoefficientCategories

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Monoid G] [TopologicalSpace G]

/-- The full subcategory of `TopRep R G` on the smooth discrete objects: the half of `TopRep R G`
that the dictionary is an equivalence with. Its inclusion into `TopRep R G`, which is how such an
object reaches `continuousCohomology n` and `ContinuousCohomology.map`, is
`ObjectProperty.ι (fun X : TopRep R G ↦ IsSmoothDiscrete R X)`. -/
abbrev SmoothDiscreteTopRep : Type _ :=
  ObjectProperty.FullSubcategory (fun X : TopRep.{w} R G ↦ IsSmoothDiscrete R X)

/-- A discrete `G`-module with continuous `G`-action, bundled: the source side of the dictionary
as a category, so that the dictionary can be an equivalence rather than a constructor. The fields
are exactly the instances `TauCeti.ofDiscreteModule` and
`TauCeti.ofDiscreteModule_isSmoothDiscrete` ask for. -/
structure DiscreteRep where
  /-- the underlying module -/
  V : Type w
  [addCommGroup : AddCommGroup V]
  [module : Module R V]
  [topologicalSpace : TopologicalSpace V]
  [discreteTopology : DiscreteTopology V]
  [distribMulAction : DistribMulAction G V]
  [smulCommClass : SMulCommClass G R V]
  [continuousSMulRing : ContinuousSMul R V]
  [continuousSMul : ContinuousSMul G V]

attribute [instance] DiscreteRep.addCommGroup DiscreteRep.module DiscreteRep.topologicalSpace
  DiscreteRep.discreteTopology DiscreteRep.distribMulAction DiscreteRep.smulCommClass
  DiscreteRep.continuousSMulRing DiscreteRep.continuousSMul

variable {R G}

/-- A morphism of discrete `G`-modules: a `G`-equivariant `R`-linear map. Continuity, which the
roadmap lists as a third field, is automatic on discrete modules
(`continuous_of_discreteTopology`), so it is not carried here. -/
@[ext] structure DiscreteRepHom (X Y : DiscreteRep.{u, v, w} R G) where
  /-- the underlying linear map -/
  toLinearMap : X.V →ₗ[R] Y.V
  /-- equivariance -/
  equivariant : ∀ (g : G) (x : X.V), toLinearMap (g • x) = g • toLinearMap x

/-- The discrete `G`-modules with continuous `G`-action form a category under the `G`-equivariant
`R`-linear maps. Unlike a category structure transported from `TopRep R G`, this makes the
dictionary's full faithfulness (`TauCeti.ofDiscreteModuleHomAddEquiv`) a theorem rather than a
definitional identity. -/
instance : Category.{w} (DiscreteRep.{u, v, w} R G) where
  Hom X Y := DiscreteRepHom X Y
  id X := ⟨LinearMap.id, fun _ _ ↦ rfl⟩
  comp f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, fun a x ↦ by
    simp only [LinearMap.comp_apply, f.equivariant, g.equivariant]⟩

/-- Two morphisms of discrete `G`-modules agree as soon as their underlying linear maps do. -/
@[ext] lemma DiscreteRep.hom_ext {X Y : DiscreteRep.{u, v, w} R G} {f g : X ⟶ Y}
    (h : DiscreteRepHom.toLinearMap f = DiscreteRepHom.toLinearMap g) : f = g :=
  DiscreteRepHom.ext h

@[simp] lemma DiscreteRep.id_toLinearMap (X : DiscreteRep.{u, v, w} R G) :
    DiscreteRepHom.toLinearMap (𝟙 X) = LinearMap.id := (rfl)

@[simp] lemma DiscreteRep.comp_toLinearMap {X Y Z : DiscreteRep.{u, v, w} R G} (f : X ⟶ Y)
    (g : Y ⟶ Z) : (f ≫ g).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := (rfl)

variable (R G)

/-- The dictionary going in, as a functor: a discrete `G`-module with continuous `G`-action goes
to the smooth discrete object it names, and an equivariant map to the morphism it names. -/
@[expose] def toSmoothDiscrete :
    DiscreteRep.{u, v, w} R G ⥤ SmoothDiscreteTopRep.{u, v, w} R G where
  obj X := ⟨ofDiscreteModule R G X.V, ofDiscreteModule_isSmoothDiscrete R G X.V⟩
  map f := ObjectProperty.homMk (ofDiscreteModuleMap f.toLinearMap f.equivariant)
  map_id _ := ObjectProperty.hom_ext _ ofDiscreteModuleMap_id
  map_comp f g := ObjectProperty.hom_ext _
    (ofDiscreteModuleMap_comp f.toLinearMap f.equivariant g.toLinearMap g.equivariant)

@[simp] lemma toSmoothDiscrete_obj_obj (X : DiscreteRep.{u, v, w} R G) :
    ((toSmoothDiscrete R G).obj X).obj = ofDiscreteModule R G X.V := (rfl)

@[simp] lemma toSmoothDiscrete_map_hom_apply {X Y : DiscreteRep.{u, v, w} R G} (f : X ⟶ Y)
    (x : X.V) : ((toSmoothDiscrete R G).map f).hom.hom x = f.toLinearMap x := (rfl)

end CoefficientCategories

/-! ### The equivalence of coefficient categories -/

/-- The underlying module of a smooth discrete object is discrete. Recording this as a local
instance is what lets `TauCeti.ofDiscreteModule` be applied to it below. -/
local instance instDiscreteTopologyOfSmoothDiscrete {R : Type u} [Ring R] [TopologicalSpace R]
    {G : Type v} [Monoid G] [TopologicalSpace G] (X : SmoothDiscreteTopRep.{u, v, w} R G) :
    DiscreteTopology X.obj.V :=
  X.property.discreteTopology

/-- The derived action on a smooth discrete object is continuous. -/
local instance instContinuousSMulOfSmoothDiscrete {R : Type u} [Ring R] [TopologicalSpace R]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : SmoothDiscreteTopRep.{u, v, w} R G) : ContinuousSMul G X.obj.V :=
  X.property.continuousSMul

section CoefficientEquivalence

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The dictionary coming back, as a functor: a smooth discrete object goes to its underlying
module, with the action read off from its operators by `TopRep.distribMulAction`. -/
@[expose] def ofSmoothDiscrete :
    SmoothDiscreteTopRep.{u, v, w} R G ⥤ DiscreteRep.{u, v, w} R G where
  obj X := { V := X.obj.V }
  -- Equivariance for the derived actions is `TopRep.distribMulAction_smul` on each side of the
  -- intertwining identity that `φ` already carries.
  map {X Y} φ :=
    { toLinearMap := φ.hom.hom.toContinuousLinearMap.toLinearMap
      equivariant := fun g x ↦ (congrArg _ (TopRep.distribMulAction_smul X.obj g x)).trans
        ((φ.hom.hom.isIntertwining g x).trans
          (TopRep.distribMulAction_smul Y.obj g (φ.hom.hom x)).symm) }
  map_id _ := DiscreteRepHom.ext (LinearMap.ext fun _ ↦ rfl)
  map_comp _ _ := DiscreteRepHom.ext (LinearMap.ext fun _ ↦ rfl)

@[simp] lemma ofSmoothDiscrete_obj_V (X : SmoothDiscreteTopRep.{u, v, w} R G) :
    ((ofSmoothDiscrete R G).obj X).V = X.obj.V := (rfl)

@[simp] lemma ofSmoothDiscrete_map_toLinearMap_apply {X Y : SmoothDiscreteTopRep.{u, v, w} R G}
    (φ : X ⟶ Y) (x : X.obj.V) :
    ((ofSmoothDiscrete R G).map φ).toLinearMap x = φ.hom.hom x := (rfl)

/-- The action carried by the module read off a smooth discrete object is the object's own
action. -/
@[simp] lemma ofSmoothDiscrete_obj_smul (X : SmoothDiscreteTopRep.{u, v, w} R G) (g : G)
    (x : ((ofSmoothDiscrete R G).obj X).V) : g • x = X.obj.ρ g x := (rfl)

/-- **The dictionary is an equivalence of categories** between the discrete `G`-modules with
continuous `G`-action and the smooth discrete objects of `TopRep R G`. It is the identity on
underlying modules in both directions, the action being read off by `TopRep.distribMulAction`, so
every component of the unit and of the counit is an identity morphism. -/
@[expose] def discreteRepEquivSmoothTopRep :
    DiscreteRep.{u, v, w} R G ≌ SmoothDiscreteTopRep.{u, v, w} R G where
  functor := toSmoothDiscrete R G
  inverse := ofSmoothDiscrete R G
  -- Both round trips return the module, or the object, they started from, so every component is
  -- an identity morphism and naturality is the dictionary's own morphism laws at a point.
  unitIso := NatIso.ofComponents (fun X ↦ Iso.refl X) fun _ ↦
    DiscreteRep.hom_ext (LinearMap.ext fun _ ↦ rfl)
  counitIso := NatIso.ofComponents (fun X ↦ Iso.refl X) fun _ ↦
    ObjectProperty.hom_ext _ (TopRep.hom_ext (DFunLike.ext _ _ fun _ ↦ rfl))

@[simp] lemma discreteRepEquivSmoothTopRep_functor :
    (discreteRepEquivSmoothTopRep R G).functor = toSmoothDiscrete R G := (rfl)

@[simp] lemma discreteRepEquivSmoothTopRep_inverse :
    (discreteRepEquivSmoothTopRep R G).inverse = ofSmoothDiscrete R G := (rfl)

@[simp] lemma discreteRepEquivSmoothTopRep_unitIso_hom_app (X : DiscreteRep.{u, v, w} R G) :
    (discreteRepEquivSmoothTopRep R G).unitIso.hom.app X = 𝟙 X := (rfl)

@[simp] lemma discreteRepEquivSmoothTopRep_counitIso_hom_app
    (X : SmoothDiscreteTopRep.{u, v, w} R G) :
    (discreteRepEquivSmoothTopRep R G).counitIso.hom.app X = 𝟙 X := (rfl)

end CoefficientEquivalence

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
singleton non-open. This is why the dictionary above has the discrete `G`-modules *with continuous
`G`-action* as its source, and it is what the hypothesis `ContinuousSMul G M` of
`TauCeti.ofDiscreteModule_isSmoothDiscrete` rules out. Stating it needs `TauCeti.ofDiscreteModule`
to be available without that hypothesis, which is why the hypothesis sits on the results that use
it rather than on the construction. -/
lemma not_isSmoothDiscrete_ofDiscreteModule_units_zmod :
    ¬ IsSmoothDiscrete ℤ (ofDiscreteModule ℤ (ZMod 3)ˣ (ZMod 3)) := by
  intro h
  have hopen := h.stabilizer_isOpen (1 : ZMod 3)
  simp only [ofDiscreteModule_ρ_apply_apply] at hopen
  rcases (TopologicalSpace.isOpen_top_iff _).1 hopen with h₀ | h₁
  · exact Set.eq_empty_iff_forall_notMem.1 h₀ 1 (one_smul _ _)
  · have hneg : (-1 : (ZMod 3)ˣ) • (1 : ZMod 3) = 1 := Set.eq_univ_iff_forall.1 h₁ (-1)
    revert hneg
    decide

end NotSmooth

end TauCeti
