/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Examples
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.FundamentalGroupAction
public import TauCeti.CategoryTheory.Action.FintypeCat
public import TauCeti.CategoryTheory.Galois.Transport
public import TauCeti.Topology.Covering.Finite

/-!
# Finite covering spaces form a Galois category

Let `X` be path connected, locally path connected and semilocally simply connected, and fix a
basepoint `x₀`. This file proves that the finite covering spaces of `X` form a Galois category in
the sense of SGA1, with fibre functor the fibre over `x₀`:

  `TauCeti.FiniteCoveringSpace.fiberFunctor x₀ : FiniteCoveringSpace X ⥤ FintypeCat`.

This is the Galois-category lens on the classification of covering spaces, the third of the three
routes the roadmap asks for; the fundamental-groupoid lens is
`TauCeti.CoveringSpace.monodromyEquivalence` and the `π₁(X, x₀)`-set lens is
`TauCeti.CoveringSpace.fiberActionEquivalence`.

Nothing here re-proves the axioms for covering spaces. The classification already identifies
covering spaces of `X` with `π₁(X, x₀)`-sets, and that identification restricts to finite covers
on one side and finite `π₁(X, x₀)`-sets on the other, because the fibre-action functor sends a
cover to its fibre over `x₀`. Finiteness of *all* fibres is not an extra condition to carry
across: over a path-connected base, one finite fibre forces the rest, which is
`TauCeti.hasFiniteFibers_of_finite_fiber`. Mathlib proves that finite `G`-sets, in the form
`Action FintypeCat G`, are a Galois category, and the axioms transport along an equivalence by
`TauCeti.preGaloisCategory_of_equivalence` and `TauCeti.fiberFunctor_comp_of_equivalence`.

The resulting `PreGaloisCategory` and `GaloisCategory` instances are stated without reference to
a basepoint, which is possible because both are propositions: the proof picks a point of the
path-connected base and transports along the equivalence attached to it.

## Main declarations

* `TauCeti.FiniteCoveringSpace.finiteFiberActionFunctor`: the fibre over `x₀` with its monodromy
  action, as a functor to finite `π₁(X, x₀)`-sets, with `finiteFiberActionFunctor_obj_obj`,
  `finiteFiberActionFunctor_obj_obj_ρ_apply`, `finiteFiberActionFunctor_obj_obj_mulAction` and
  `finiteFiberActionFunctor_map_hom_hom` computing it.
* `TauCeti.FiniteCoveringSpace.finiteFiberActionEquivalence`: **finite covering spaces of `X` are
  equivalent to finite `π₁(X, x₀)`-sets.**
* `TauCeti.FiniteCoveringSpace.fiberActionFintypeCatEquivalence`: the same equivalence, valued in
  Mathlib's `Action FintypeCat`.
* `TauCeti.FiniteCoveringSpace.fiberFunctor`: the fibre over `x₀`, as a functor to `FintypeCat`,
  with `fiberFunctor_obj` and `fiberFunctor_map_hom` computing it.
* `TauCeti.FiniteCoveringSpace.instPreGaloisCategory` and
  `TauCeti.FiniteCoveringSpace.instGaloisCategory`: **the finite covering spaces of `X` form a
  Galois category.**
* `TauCeti.FiniteCoveringSpace.instFiberFunctor`: **the fibre over `x₀` is a fibre functor.**

## References

This is the Galois-category lens named in Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, which asks for the classification of covers to be
phrased through `Mathlib/CategoryTheory/Galois`; see also SGA1, Exposé V, and Lenstra, *Galois
theory for schemes*, Section 3. It consumes the `π₁(X, x₀)`-set classification of
`TauCeti.AlgebraicTopology.UniversalCover.Classification.FundamentalGroupAction`.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.FiniteCoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

private theorem cast_apply_of_heq {α α' β β' : Type u} (hα : α = α') (hβ : β = β')
    {f : α → β} {f' : α' → β'} (hf : HEq f f') (x : α') :
    cast hβ (f (cast hα.symm x)) = f' x := by
  subst α'
  subst β'
  exact congrFun (eq_of_heq hf) x

private theorem heq_of_cast_apply {α α' β β' : Type u} (hα : α = α') (hβ : β = β')
    {f : α → β} {f' : α' → β'}
    (h : ∀ x, cast hβ (f (cast hα.symm x)) = f' x) : HEq f f' := by
  subst α'
  subst β'
  exact heq_of_eq (funext h)

private theorem cast_mulAction_of_action_eq {G : Type u} [Monoid G]
    {A B : Action (Type u) G} (h : A = B) :
    cast (congrArg (fun T : Action (Type u) G => MulAction G T.V) h)
        (Action.instMulAction A) =
      Action.instMulAction B := by
  subst B
  rfl

/-- The functor taking a finite covering space of `X` to the fibre over `x₀`, a finite set with
the monodromy action of `π₁(X, x₀)`. -/
def finiteFiberActionFunctor :
    FiniteCoveringSpace X ⥤ FiniteAction.{u} (FundamentalGroup X x₀) :=
  ObjectProperty.lift _ (forget X ⋙ CoveringSpace.fiberActionFunctor x₀) fun p =>
    (isFiniteAction_iff _).2 (finite_fiber p x₀)

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
@[simp]
theorem finiteFiberActionFunctor_obj_obj (p : FiniteCoveringSpace X) :
    ((finiteFiberActionFunctor x₀).obj p).obj =
      (CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p) :=
  (rfl)

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- The underlying type of the finite action attached to a finite cover is its fibre over the
basepoint. -/
theorem finiteFiberActionFunctor_obj_obj_V (p : FiniteCoveringSpace X) :
    ((finiteFiberActionFunctor x₀).obj p).obj.V =
      ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p)).V :=
  congrArg Action.V (finiteFiberActionFunctor_obj_obj x₀ p)

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- A loop class acts on the fibre of a finite cover over `x₀` by monodromy. -/
@[simp]
theorem finiteFiberActionFunctor_obj_obj_ρ_apply (p : FiniteCoveringSpace X)
    (g : FundamentalGroup X x₀) (e : ⇑p.proj ⁻¹' {x₀}) :
    cast (finiteFiberActionFunctor_obj_obj_V x₀ p)
        (((finiteFiberActionFunctor x₀).obj p).obj.ρ g
          (cast (finiteFiberActionFunctor_obj_obj_V x₀ p).symm e)) =
      p.isCoveringMap_proj.monodromy g e := by
  exact (cast_apply_of_heq
    (finiteFiberActionFunctor_obj_obj_V x₀ p)
    (finiteFiberActionFunctor_obj_obj_V x₀ p)
    (f' := ConcreteCategory.hom
      (((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p)).ρ g)) (by
        cases finiteFiberActionFunctor_obj_obj x₀ p
        rfl) e).trans
    (CoveringSpace.fiberActionFunctor_obj_ρ_apply x₀ ((forget X).obj p) g e)

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- The `MulAction` carried by the fibre of a finite cover over `x₀` is Mathlib's monodromy
action. -/
theorem finiteFiberActionFunctor_obj_obj_mulAction (p : FiniteCoveringSpace X) :
    cast (congrArg (fun A : Action (Type u) (FundamentalGroup X x₀) =>
      MulAction (FundamentalGroup X x₀) A.V)
      (finiteFiberActionFunctor_obj_obj x₀ p))
      (Action.instMulAction ((finiteFiberActionFunctor x₀).obj p).obj) =
      p.isCoveringMap_proj.fundamentalGroupMulAction x₀ :=
  by
    exact (cast_mulAction_of_action_eq
      (finiteFiberActionFunctor_obj_obj x₀ p)).trans
        (CoveringSpace.fiberActionFunctor_obj_mulAction x₀ ((forget X).obj p))

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem finiteFiberActionFunctor_map_hom_hom_heq
    {p q : FiniteCoveringSpace X} (f : p ⟶ q) :
    HEq (fun x => ConcreteCategory.hom ((finiteFiberActionFunctor x₀).map f).hom.hom x)
      (fun x => ConcreteCategory.hom
        ((CoveringSpace.fiberActionFunctor x₀).map ((forget X).map f)).hom x) := by
  unfold finiteFiberActionFunctor
  rfl

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- A map of finite covering spaces acts on the fibre over `x₀` by restriction. -/
@[simp]
theorem finiteFiberActionFunctor_map_hom_hom {p q : FiniteCoveringSpace X} (f : p ⟶ q)
    (e : ⇑p.proj ⁻¹' {x₀}) :
    cast (finiteFiberActionFunctor_obj_obj_V x₀ q)
        (((finiteFiberActionFunctor x₀).map f).hom.hom
          (cast (finiteFiberActionFunctor_obj_obj_V x₀ p).symm e)) =
      (↾(IsCoveringMap.fiberMap f.hom.left.hom
        (CoveringSpace.proj_hom_comp_hom_left_hom ((forget X).map f)) x₀)) e := by
  exact (cast_apply_of_heq
    (finiteFiberActionFunctor_obj_obj_V x₀ p)
    (finiteFiberActionFunctor_obj_obj_V x₀ q)
    (f' := fun x => ConcreteCategory.hom
      ((CoveringSpace.fiberActionFunctor x₀).map ((forget X).map f)).hom x)
    (finiteFiberActionFunctor_map_hom_hom_heq x₀ f) e).trans
    (congrArg (fun k :
        ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p)).V ⟶
          ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj q)).V =>
        ConcreteCategory.hom k e)
      (CoveringSpace.fiberActionFunctor_map_hom x₀ ((forget X).map f)))

/-- The fibre-action functor of finite covers, followed by the inclusion of finite `π₁(X, x₀)`-sets
into all of them, is the fibre-action functor of covers restricted to finite ones. -/
def finiteFiberActionFunctorCompForgetIso :
    finiteFiberActionFunctor x₀ ⋙ FiniteAction.forget (FundamentalGroup X x₀) ≅
      forget X ⋙ CoveringSpace.fiberActionFunctor x₀ :=
  ObjectProperty.liftCompιIso _ _ _

instance finiteFiberActionFunctor_faithful : (finiteFiberActionFunctor x₀).Faithful :=
  Functor.Faithful.of_comp_iso (finiteFiberActionFunctorCompForgetIso x₀)

instance finiteFiberActionFunctor_full : (finiteFiberActionFunctor x₀).Full :=
  Functor.Full.of_comp_faithful_iso (finiteFiberActionFunctorCompForgetIso x₀)

/-- **Every finite `π₁(X, x₀)`-set is the fibre action of a finite covering space.**

The cover realising it as a `π₁(X, x₀)`-set is one of the classification; its fibre over `x₀` is
finite because it is isomorphic to the given set, and then all of its fibres are finite because
the base is path connected. -/
instance finiteFiberActionFunctor_essSurj : (finiteFiberActionFunctor x₀).EssSurj where
  mem_essImage A := by
    let q := (CoveringSpace.fiberActionFunctor x₀).objPreimage A.obj
    let e := (CoveringSpace.fiberActionFunctor x₀).objObjPreimageIso A.obj
    have hq : isFiniteAction (FundamentalGroup X x₀)
        ((CoveringSpace.fiberActionFunctor x₀).obj q) :=
      (isFiniteAction _).prop_of_iso e.symm A.property
    exact ⟨⟨q.obj, ⟨q.property,
        hasFiniteFibers_of_finite_fiber q x₀ ((isFiniteAction_iff _).1 hq)⟩⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩

instance finiteFiberActionFunctor_isEquivalence :
    (finiteFiberActionFunctor x₀).IsEquivalence where

/-- **Finite covering spaces of `X` are equivalent to finite `π₁(X, x₀)`-sets.**

This is the restriction of `TauCeti.CoveringSpace.fiberActionEquivalence` to finite covers. -/
def finiteFiberActionEquivalence :
    FiniteCoveringSpace X ≌ FiniteAction.{u} (FundamentalGroup X x₀) :=
  (finiteFiberActionFunctor x₀).asEquivalence

@[simp]
theorem finiteFiberActionEquivalence_functor :
    (finiteFiberActionEquivalence x₀).functor = finiteFiberActionFunctor x₀ :=
  (rfl)

/-- **Finite covering spaces of `X` are equivalent to actions of `π₁(X, x₀)` on finite sets**, in
Mathlib's `Action FintypeCat` form. -/
def fiberActionFintypeCatEquivalence :
    FiniteCoveringSpace X ≌ Action FintypeCat.{u} (FundamentalGroup X x₀) :=
  (finiteFiberActionEquivalence x₀).trans (FiniteAction.equivalenceActionFintypeCat _)

@[simp]
theorem fiberActionFintypeCatEquivalence_functor :
    (fiberActionFintypeCatEquivalence x₀).functor =
      finiteFiberActionFunctor x₀ ⋙
        FiniteAction.toActionFintypeCat (FundamentalGroup X x₀) :=
  by
    unfold fiberActionFintypeCatEquivalence
    rw [Equivalence.trans_functor, finiteFiberActionEquivalence_functor,
      FiniteAction.equivalenceActionFintypeCat_functor]

/-- The fibre of a finite covering space over `x₀`, as a functor to finite sets. -/
def fiberFunctor : FiniteCoveringSpace X ⥤ FintypeCat.{u} :=
  (fiberActionFintypeCatEquivalence x₀).functor ⋙ Action.forget FintypeCat _

theorem fiberFunctor_eq :
    fiberFunctor x₀ =
      (finiteFiberActionFunctor x₀ ⋙
        FiniteAction.toActionFintypeCat (FundamentalGroup X x₀)) ⋙
          Action.forget FintypeCat _ :=
  by
    unfold fiberFunctor
    rw [fiberActionFintypeCatEquivalence_functor]

@[simp]
theorem fiberFunctor_obj (p : FiniteCoveringSpace X) :
    ((fiberFunctor x₀).obj p).obj = ↥(⇑p.proj ⁻¹' {x₀}) :=
  by
    rw [fiberFunctor_eq]
    exact (FiniteAction.toActionFintypeCat_obj_V _ _).trans
      (finiteFiberActionFunctor_obj_obj_V x₀ p)

private theorem fiberFunctor_map_hom_heq {p q : FiniteCoveringSpace X} (f : p ⟶ q) :
    HEq (fun x => ((fiberFunctor x₀).map f) x)
      (fun x => ConcreteCategory.hom (↾(IsCoveringMap.fiberMap f.hom.left.hom
        (CoveringSpace.proj_hom_comp_hom_left_hom ((forget X).map f)) x₀)) x) := by
  have h₁ : HEq (fun x => ((fiberFunctor x₀).map f) x)
      (fun x => ConcreteCategory.hom
        ((FiniteAction.toActionFintypeCat (FundamentalGroup X x₀)).map
          ((finiteFiberActionFunctor x₀).map f)).hom x) := by
    unfold fiberFunctor fiberActionFintypeCatEquivalence
    rw [Equivalence.trans_functor, finiteFiberActionEquivalence_functor,
      FiniteAction.equivalenceActionFintypeCat_functor]
    simp only [Functor.comp_map, Action.forget_map]
    rfl
  have h₂ : HEq
      (fun x => ConcreteCategory.hom
        ((FiniteAction.toActionFintypeCat (FundamentalGroup X x₀)).map
          ((finiteFiberActionFunctor x₀).map f)).hom x)
      (fun x => ConcreteCategory.hom ((finiteFiberActionFunctor x₀).map f).hom.hom x) := by
    simpa only using heq_of_cast_apply
      (FiniteAction.toActionFintypeCat_obj_V _ ((finiteFiberActionFunctor x₀).obj p))
      (FiniteAction.toActionFintypeCat_obj_V _ ((finiteFiberActionFunctor x₀).obj q))
      (FiniteAction.toActionFintypeCat_map_hom_apply _ ((finiteFiberActionFunctor x₀).map f))
  have h₃ := finiteFiberActionFunctor_map_hom_hom_heq x₀ f
  have h₄ : HEq
      (fun x => ConcreteCategory.hom
        ((CoveringSpace.fiberActionFunctor x₀).map ((forget X).map f)).hom x)
      (fun x => ConcreteCategory.hom (↾(IsCoveringMap.fiberMap f.hom.left.hom
        (CoveringSpace.proj_hom_comp_hom_left_hom ((forget X).map f)) x₀)) x) :=
    heq_of_eq (congrArg (fun k :
        ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p)).V ⟶
          ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj q)).V =>
        fun x => ConcreteCategory.hom k x)
      (CoveringSpace.fiberActionFunctor_map_hom x₀ ((forget X).map f)))
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- A map of finite covering spaces acts on the fibre over `x₀` by restriction. -/
@[simp]
theorem fiberFunctor_map_hom {p q : FiniteCoveringSpace X} (f : p ⟶ q)
    (e : ⇑p.proj ⁻¹' {x₀}) :
    cast (fiberFunctor_obj x₀ q)
        (((fiberFunctor x₀).map f) (cast (fiberFunctor_obj x₀ p).symm e)) =
      (↾(IsCoveringMap.fiberMap f.hom.left.hom
        (CoveringSpace.proj_hom_comp_hom_left_hom ((forget X).map f)) x₀)) e := by
  exact cast_apply_of_heq (fiberFunctor_obj x₀ p) (fiberFunctor_obj x₀ q)
    (fiberFunctor_map_hom_heq x₀ f) e

/-- **The finite covering spaces of `X` satisfy the axioms (G1)–(G3) of a Galois category.**

They are equivalent to the finite `π₁(X, x₀)`-sets, which Mathlib proves are a pre-Galois
category. The statement does not mention a basepoint; the proof picks one. -/
instance instPreGaloisCategory : PreGaloisCategory (FiniteCoveringSpace X) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (X : Type u))
  exact preGaloisCategory_of_equivalence (fiberActionFintypeCatEquivalence x₀)

/-- **The fibre over `x₀` is a fibre functor**: it satisfies the axioms (G4)–(G6). -/
instance instFiberFunctor : PreGaloisCategory.FiberFunctor (fiberFunctor x₀) :=
  fiberFunctor_comp_of_equivalence (fiberActionFintypeCatEquivalence x₀) _

/-- **The finite covering spaces of a path-connected, locally path-connected, semilocally simply
connected space form a Galois category.** -/
instance instGaloisCategory : GaloisCategory (FiniteCoveringSpace X) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (X : Type u))
  exact galoisCategory_of_equivalence (fiberActionFintypeCatEquivalence x₀)

end TauCeti.FiniteCoveringSpace
