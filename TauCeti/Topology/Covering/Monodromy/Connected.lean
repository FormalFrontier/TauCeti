/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Covering.Monodromy.Full
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Monodromy of connected covering spaces

For a locally path-connected base `X`, the monodromy functor of a connected covering space is
pretransitive on every fibre: any two points over the same basepoint differ by transport along a
loop. This file packages that condition as a full subcategory of fundamental-groupoid actions and
lifts covering-space monodromy to it.

The word *pretransitive* follows Mathlib's convention: the condition allows an empty fibre. This
matters over a disconnected base, since a connected cover can have image in only one component.
On every nonempty fibre the condition is ordinary transitivity. Keeping the fibrewise formulation,
rather than evaluating at one chosen basepoint, also retains the full information of a cover when
the base is disconnected.

## Main declarations

* `TauCeti.FundamentalGroupoidAction.isFiberwisePretransitive`: the property that the loop
  morphisms at each object act pretransitively on that object's value.
* `TauCeti.PretransitiveFundamentalGroupoidAction`: the full subcategory of functors satisfying
  that property.
* `TauCeti.ConnectedCoveringSpace.monodromyFunctor`: monodromy of connected covers, valued in
  fibrewise pretransitive fundamental-groupoid actions.
* `TauCeti.ConnectedCoveringSpace.monodromyFunctor_faithful` and
  `monodromyFunctor_full`: the lifted functor remains fully faithful.

## References

This is the connected/transitive restriction in Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`. It uses Mathlib's local-homeomorphism charts and Tau
Ceti's existing monodromy transitivity and full-faithfulness results. No Mathlib proof is
vendored.
-/

public section

open CategoryTheory Topology

universe u

namespace TauCeti

namespace FundamentalGroupoidAction

/-- A fundamental-groupoid action is fibrewise pretransitive if, at every basepoint, its loop
morphisms carry any element of the fibre to any other element of that fibre. -/
def isFiberwisePretransitive (X : TopCat.{u}) :
    ObjectProperty (FundamentalGroupoid X ⥤ Type u) :=
  fun F => ∀ (x : FundamentalGroupoid X) (a b : F.obj x),
    ∃ γ : x ⟶ x, F.map γ a = b

/-- Membership in the fibrewise pretransitive fundamental-groupoid action property. -/
@[simp]
theorem isFiberwisePretransitive_iff (X : TopCat.{u})
    (F : FundamentalGroupoid X ⥤ Type u) :
    isFiberwisePretransitive X F ↔
      ∀ (x : FundamentalGroupoid X) (a b : F.obj x),
        ∃ γ : x ⟶ x, F.map γ a = b :=
  Iff.rfl

/-- Fibrewise pretransitivity is preserved by natural isomorphisms of actions. -/
instance (X : TopCat.{u}) :
    (isFiberwisePretransitive X).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro F G e hF
    rw [isFiberwisePretransitive_iff] at hF ⊢
    intro x a b
    obtain ⟨γ, hγ⟩ := hF x (e.inv.app x a) (e.inv.app x b)
    refine ⟨γ, ?_⟩
    calc
      G.map γ a = G.map γ (e.hom.app x (e.inv.app x a)) := by simp
      _ = e.hom.app x (F.map γ (e.inv.app x a)) :=
        (e.hom.naturality_apply γ _).symm
      _ = e.hom.app x (e.inv.app x b) := by rw [hγ]
      _ = b := by simp

end FundamentalGroupoidAction

/-- Fundamental-groupoid actions that are pretransitive on every fibre. Morphisms are arbitrary
natural transformations between the underlying functors. -/
abbrev PretransitiveFundamentalGroupoidAction (X : TopCat.{u}) :=
  (FundamentalGroupoidAction.isFiberwisePretransitive X).FullSubcategory

namespace PretransitiveFundamentalGroupoidAction

variable {X : TopCat.{u}}

/-- The fully faithful inclusion into all fundamental-groupoid actions. -/
noncomputable abbrev forget (X : TopCat.{u}) :
    PretransitiveFundamentalGroupoidAction X ⥤ (FundamentalGroupoid X ⥤ Type u) :=
  ObjectProperty.ι _

/-- Construct a fibrewise pretransitive fundamental-groupoid action from an action and a proof
of fibrewise pretransitivity. -/
noncomputable def mk (F : FundamentalGroupoid X ⥤ Type u)
    (hF : FundamentalGroupoidAction.isFiberwisePretransitive X F) :
    PretransitiveFundamentalGroupoidAction X :=
  ⟨F, hF⟩

/-- The underlying action of a fibrewise pretransitive fundamental-groupoid action satisfies
fibrewise pretransitivity. -/
theorem isFiberwisePretransitive (F : PretransitiveFundamentalGroupoidAction X) :
    FundamentalGroupoidAction.isFiberwisePretransitive X F.obj :=
  F.property

/-- The inclusion into all fundamental-groupoid actions is fully faithful. -/
noncomputable def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end PretransitiveFundamentalGroupoidAction

namespace ConnectedCoveringSpace

variable {X : TopCat.{u}}

/-- A local homeomorphism with locally path-connected codomain has locally path-connected
domain. This local form passes local path-connectedness from the base to the total space of a
covering. -/
private theorem locallyPathConnectedSpace_of_isLocalHomeomorph
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    [LocallyPathConnectedSpace B] {p : E → B} (hp : IsLocalHomeomorph p) :
    LocallyPathConnectedSpace E := by
  constructor
  intro e
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨W, hWU, hWopen, heW⟩ := mem_nhds_iff.mp hU
  let φ := hp.localInverseAt e
  have hpe_source : p e ∈ φ.source := hp.apply_self_mem_localInverseAt_source
  have hsource : IsOpen (φ.source ∩ φ ⁻¹' W) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hWopen
  have hpe : p e ∈ φ.source ∩ φ ⁻¹' W := by
    refine ⟨hpe_source, ?_⟩
    simpa only [Set.mem_preimage, φ, hp.localInverseAt_apply_self] using heW
  obtain ⟨V, ⟨hVopen, hpeV, hVpath⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis (p e)).mem_iff.mp (hsource.mem_nhds hpe)
  refine ⟨φ '' V, ?_, hVpath.image' (φ.continuousOn_toFun.mono fun _ hv => (hVsub hv).1), ?_⟩
  · exact (φ.isOpen_image_of_subset_source hVopen
      (hVsub.trans Set.inter_subset_left)).mem_nhds ⟨p e, hpeV, by simp [φ]⟩
  · rintro z ⟨y, hyV, rfl⟩
    exact hWU (hVsub hyV).2

/-- The ordinary monodromy functor of a connected cover is pretransitive on every fibre. -/
theorem monodromy_isFiberwisePretransitive [LocallyPathConnectedSpace X]
    (p : ConnectedCoveringSpace X) :
    FundamentalGroupoidAction.isFiberwisePretransitive X
      ((CoveringSpace.monodromyFunctor X).obj ((forget X).obj p)) := by
  rw [FundamentalGroupoidAction.isFiberwisePretransitive_iff]
  rw [CoveringSpace.monodromyFunctor_obj]
  intro x e e'
  rcases x with ⟨x⟩
  let _ : LocallyPathConnectedSpace (p : TopCat) :=
    locallyPathConnectedSpace_of_isLocalHomeomorph p.isCoveringMap_proj.isLocalHomeomorph
  let _ : PathConnectedSpace (p : TopCat) := PathConnectedSpace.of_locallyPathConnectedSpace
  exact IsCoveringMap.exists_monodromy_eq p.isCoveringMap_proj e e'

/-- Monodromy as a functor from connected covering spaces over `X` to fibrewise pretransitive
fundamental-groupoid actions.

The underlying action is the ordinary covering-space monodromy functor, and the underlying map
of every morphism is its fibrewise natural transformation. -/
noncomputable def monodromyFunctor (X : TopCat.{u}) [LocallyPathConnectedSpace X] :
    ConnectedCoveringSpace X ⥤ PretransitiveFundamentalGroupoidAction X :=
  ObjectProperty.lift _ (forget X ⋙ CoveringSpace.monodromyFunctor X)
    monodromy_isFiberwisePretransitive

/-- Forgetting fibrewise pretransitivity recovers the ordinary monodromy functor after including
connected covers into all covers. -/
noncomputable def monodromyFunctorCompForgetIso [LocallyPathConnectedSpace X] :
    monodromyFunctor X ⋙ PretransitiveFundamentalGroupoidAction.forget X ≅
      forget X ⋙ CoveringSpace.monodromyFunctor X :=
  ObjectProperty.liftCompιIso _ _ _

/-- The underlying action of connected-cover monodromy is the ordinary monodromy action. -/
@[simp]
theorem monodromyFunctor_obj_obj [LocallyPathConnectedSpace X]
    (p : ConnectedCoveringSpace X) :
    ((monodromyFunctor X).obj p).obj =
      (CoveringSpace.monodromyFunctor X).obj ((forget X).obj p) :=
  by
    simpa only [monodromyFunctor, ObjectProperty.ι_obj, Functor.comp_obj] using
      ObjectProperty.ι_obj_lift_obj
        (FundamentalGroupoidAction.isFiberwisePretransitive X)
        (forget X ⋙ CoveringSpace.monodromyFunctor X)
        monodromy_isFiberwisePretransitive p

/-- The underlying natural transformation assigned to a map of connected covers is the one
assigned by ordinary covering-space monodromy. -/
@[simp]
theorem monodromyFunctor_map_hom [LocallyPathConnectedSpace X]
    {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    ((monodromyFunctor X).map f).hom =
      eqToHom (monodromyFunctor_obj_obj p) ≫
        (CoveringSpace.monodromyFunctor X).map ((forget X).map f) ≫
        eqToHom (monodromyFunctor_obj_obj q).symm :=
  by
    convert ObjectProperty.ι_obj_lift_map
      (FundamentalGroupoidAction.isFiberwisePretransitive X)
      (forget X ⋙ CoveringSpace.monodromyFunctor X)
      monodromy_isFiberwisePretransitive f using 1 <;> rfl

/-- Connected-cover monodromy is faithful. -/
instance monodromyFunctor_faithful [LocallyPathConnectedSpace X] :
    (monodromyFunctor X).Faithful :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Faithful

/-- Over a locally path-connected base, connected-cover monodromy is full. -/
instance monodromyFunctor_full [LocallyPathConnectedSpace X] :
    (monodromyFunctor X).Full :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Full

end ConnectedCoveringSpace

end TauCeti
