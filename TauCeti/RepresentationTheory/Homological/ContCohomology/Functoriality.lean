/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Restriction, inflation and coefficient maps in continuous cohomology

Mathlib's `ContinuousCohomology.map` is functoriality for a *compatible pair*: a continuous
homomorphism `φ : H →ₜ* G` together with a morphism `f : TopRep.res φ X ⟶ Y` induces
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`. This file names the three instances of that construction which the rest of
the continuous-cohomology theory uses, each with its composition law:

* **coefficient maps**, at `φ = id`, which package the carrier as a functor
  `continuousCohomologyFunctor`;
* **restriction** along the inclusion of an arbitrary subgroup, carrying the subspace topology;
* **inflation** along a quotient map `G → G ⧸ N` for a normal subgroup `N`, with the invariants
  `Xᴺ` of `TopRep.quotientToInvariants` as coefficients.

Each of the three carries its defining equation — `coeffMap_def`, `res_def` and `infl_def` — which
identifies it with the compatible pair it specialises `ContinuousCohomology.map` at.

Restriction and inflation are natural in the coefficients, and this is recorded by the two natural
transformations `resNatTrans` and `inflNatTrans`, matching the shape of Mathlib's discrete
`groupCohomology.resNatTrans` and `groupCohomology.infNatTrans`.

## Main definitions

* `TauCeti.ContinuousCohomology.coeffMap`, `TauCeti.ContinuousCohomology.res`,
  `TauCeti.ContinuousCohomology.infl`: the three named instances of `ContinuousCohomology.map`.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctor`: `Hⁿ(G, -)` as a functor.
* `TauCeti.ContinuousCohomology.resNatTrans`, `TauCeti.ContinuousCohomology.inflNatTrans`.

## Main results

* `TauCeti.ContinuousCohomology.coeffMap_comp`,
  `TauCeti.ContinuousCohomology.res_comp_res` and
  `TauCeti.ContinuousCohomology.infl_comp_infl`: the composition laws of the three named maps.
* `TauCeti.ContinuousCohomology.coeffMap_comp_res` and
  `TauCeti.ContinuousCohomology.coeffMap_comp_infl`: naturality of restriction and of inflation in
  the coefficients.
* `TauCeti.ContinuousCohomology.map_congr`: two compatible pairs that agree induce the same map.
-/

public section

open CategoryTheory

namespace TauCeti

namespace ContinuousCohomology

open _root_.ContinuousCohomology

universe u v

variable (R : Type u) [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {R} in
/-- Two compatible pairs with equal homomorphisms and equal coefficient maps induce the same map on
continuous cohomology; the continuous counterpart of `groupCohomology.map_congr`. -/
theorem map_congr {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {X : TopRep R G} {Y : TopRep R H} {φ ψ : H →ₜ* G} (hφ : φ = ψ)
    {f : TopRep.res (φ : H →* G) X ⟶ Y} {g : TopRep.res (ψ : H →* G) X ⟶ Y} (hfg : HEq f g)
    (n : ℕ) :
    _root_.ContinuousCohomology.map φ f n = _root_.ContinuousCohomology.map ψ g n := by
  subst hφ
  rw [eq_of_heq hfg]

section CoeffMap

variable {R}

/-- A coefficient map: the map on continuous cohomology induced by a morphism of topological
`G`-representations. It is the instance of `ContinuousCohomology.map` at `φ = id`. -/
noncomputable def coeffMap {X Y : TopRep R G} (f : X ⟶ Y) (n : ℕ) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  _root_.ContinuousCohomology.map (X := X) (ContinuousMonoidHom.id G) f n

-- Not `@[simp]`: `coeffMap` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `coeffMap`: it is `ContinuousCohomology.map` at `φ = id`. -/
theorem coeffMap_def {X Y : TopRep R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap f n = _root_.ContinuousCohomology.map (X := X) (ContinuousMonoidHom.id G) f n :=
  (rfl)

@[simp]
theorem coeffMap_id (X : TopRep R G) (n : ℕ) : coeffMap (𝟙 X) n = 𝟙 _ :=
  _root_.ContinuousCohomology.map_id X n

/-- Coefficient maps preserve composition. -/
@[reassoc]
theorem coeffMap_comp {X Y Z : TopRep R G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    coeffMap (f ≫ g) n = coeffMap f n ≫ coeffMap g n :=
  _root_.ContinuousCohomology.map_comp (X := X) (ContinuousMonoidHom.id G)
    (ContinuousMonoidHom.id G) f g n

end CoeffMap

variable (G)

-- Exposed: the generated `@[simps]` field lemmas are `rfl`-proofs about this body.
/-- The `n`-th continuous cohomology of a topological group `G` as a functor in the coefficients.
Its action on morphisms is `coeffMap`; the continuous counterpart of `groupCohomology.functor`. -/
@[expose, simps]
noncomputable def continuousCohomologyFunctor (n : ℕ) : TopRep R G ⥤ TopModuleCat R where
  obj X := continuousCohomology n X
  map f := coeffMap f n
  map_id X := coeffMap_id X n
  map_comp f g := coeffMap_comp f g n

variable {G}

section Res

variable (S : Subgroup G)

variable {R}

/-- Restriction to a subgroup, the first named instance of `ContinuousCohomology.map`. -/
noncomputable def res (X : TopRep R G) (n : ℕ) :
    continuousCohomology n X ⟶
      continuousCohomology n (TopRep.res (S.subtype : S →* G) X) :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

-- Not `@[simp]`: `res` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `res`: it is `ContinuousCohomology.map` for the compatible pair
consisting of the inclusion `S ↪ G` and the identity of the coefficients. -/
theorem res_def (X : TopRep R G) (n : ℕ) :
    res S X n = _root_.ContinuousCohomology.map (X := X)
      (ContinuousMonoidHom.subgroupSubtype S) (𝟙 (TopRep.res (S.subtype : S →* G) X)) n :=
  (rfl)

/-- Restriction is natural in the coefficients. -/
@[reassoc]
theorem coeffMap_comp_res {X Y : TopRep R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap f n ≫ res S Y n = res S X n ≫ coeffMap ((TopRep.resFunctor S.subtype).map f) n :=
  (_root_.ContinuousCohomology.map_comp (X := X) (ContinuousMonoidHom.id G)
        (ContinuousMonoidHom.subgroupSubtype S) f (𝟙 _) n).symm.trans
    (_root_.ContinuousCohomology.map_comp (X := X) (ContinuousMonoidHom.subgroupSubtype S)
      (ContinuousMonoidHom.id S) (𝟙 _) ((TopRep.resFunctor S.subtype).map f) n)

variable (R) in
/-- Restriction to a subgroup, as a natural transformation of functors on `TopRep R G`; the
continuous counterpart of `groupCohomology.resNatTrans`. -/
noncomputable def resNatTrans (n : ℕ) :
    continuousCohomologyFunctor R G n ⟶
      TopRep.resFunctor (S.subtype : S →* G) ⋙ continuousCohomologyFunctor R S n where
  app X := res S X n
  naturality _ _ f := coeffMap_comp_res S f n

@[simp]
theorem resNatTrans_app (X : TopRep R G) (n : ℕ) : (resNatTrans R S n).app X = res S X n :=
  (rfl)

/-- Restricting to `S` and then to a subgroup `T` of `S` is restriction along the composite
inclusion. -/
@[reassoc]
theorem res_comp_res (T : Subgroup S) (X : TopRep R G) (n : ℕ) :
    res S X n ≫ res T (TopRep.res (S.subtype : S →* G) X) n =
      _root_.ContinuousCohomology.map (X := X)
        ((ContinuousMonoidHom.subgroupSubtype S).comp (ContinuousMonoidHom.subgroupSubtype T))
        (𝟙 (TopRep.res (T.subtype : T →* S) (TopRep.res (S.subtype : S →* G) X))) n := by
  refine (_root_.ContinuousCohomology.map_comp (X := X) (ContinuousMonoidHom.subgroupSubtype S)
      (ContinuousMonoidHom.subgroupSubtype T) (𝟙 _) (𝟙 _) n).symm.trans
    (map_congr rfl (heq_of_eq ?_) n)
  ext v
  rfl

end Res

section Infl

variable (N : Subgroup G) [N.Normal]

variable {R}

/-- Inflation along `G → G ⧸ N`, the second named instance of `ContinuousCohomology.map`: the
coefficients on the quotient are the `N`-invariants `Xᴺ`, and the compatible pair is the quotient
homomorphism together with the inclusion `Xᴺ ↪ X`. -/
noncomputable def infl (X : TopRep R G) (n : ℕ) :
    continuousCohomology n (TopRep.quotientToInvariants X N) ⟶ continuousCohomology n X :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.quotientMk N)
    (TopRep.quotientToInvariantsι X N) n

-- Not `@[simp]`: `infl` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `infl`: it is `ContinuousCohomology.map` for the compatible pair
consisting of the quotient homomorphism `G → G ⧸ N` and the inclusion `Xᴺ ↪ X`. -/
theorem infl_def (X : TopRep R G) (n : ℕ) :
    infl N X n = _root_.ContinuousCohomology.map (ContinuousMonoidHom.quotientMk N)
      (TopRep.quotientToInvariantsι X N) n :=
  (rfl)

/-- Inflation is natural in the coefficients. -/
@[reassoc]
theorem coeffMap_comp_infl {X Y : TopRep R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap (TopRep.quotientToInvariantsMap f N) n ≫ infl N Y n = infl N X n ≫ coeffMap f n := by
  refine ((_root_.ContinuousCohomology.map_comp (X := TopRep.quotientToInvariants X N)
      (Y := TopRep.quotientToInvariants Y N) (Z := Y) (ContinuousMonoidHom.id (G ⧸ N))
      (ContinuousMonoidHom.quotientMk N) (TopRep.quotientToInvariantsMap f N)
      (TopRep.quotientToInvariantsι Y N) n).symm.trans (Eq.trans ?_
    (_root_.ContinuousCohomology.map_comp (X := TopRep.quotientToInvariants X N) (Y := X) (Z := Y)
      (ContinuousMonoidHom.quotientMk N) (ContinuousMonoidHom.id G)
      (TopRep.quotientToInvariantsι X N) f n)))
  exact map_congr rfl
    (heq_of_eq (TopRep.quotientToInvariantsMap_comp_quotientToInvariantsι N f)) n

variable (R) in
/-- Inflation, as a natural transformation of functors on `TopRep R G`; the continuous counterpart
of `groupCohomology.infNatTrans`. -/
noncomputable def inflNatTrans (n : ℕ) :
    TopRep.quotientToInvariantsFunctor R G N ⋙ continuousCohomologyFunctor R (G ⧸ N) n ⟶
      continuousCohomologyFunctor R G n where
  app X := infl N X n
  naturality _ _ f := coeffMap_comp_infl N f n

@[simp]
theorem inflNatTrans_app (X : TopRep R G) (n : ℕ) : (inflNatTrans R N n).app X = infl N X n :=
  (rfl)

/-- Inflating from `(G ⧸ N) ⧸ P` to `G ⧸ N` and then from `G ⧸ N` to `G` is the map induced by the
composite quotient homomorphism together with the composite inclusion `(Xᴺ)ᴾ ↪ Xᴺ ↪ X` of
coefficients. -/
@[reassoc]
theorem infl_comp_infl (P : Subgroup (G ⧸ N)) [P.Normal] (X : TopRep R G) (n : ℕ) :
    infl P (TopRep.quotientToInvariants X N) n ≫ infl N X n =
      _root_.ContinuousCohomology.map
        ((ContinuousMonoidHom.quotientMk P).comp (ContinuousMonoidHom.quotientMk N))
        ((TopRep.resFunctor (ContinuousMonoidHom.quotientMk N : G →* G ⧸ N)).map
            (TopRep.quotientToInvariantsι (TopRep.quotientToInvariants X N) P) ≫
          TopRep.quotientToInvariantsι X N) n :=
  (_root_.ContinuousCohomology.map_comp (ContinuousMonoidHom.quotientMk P)
    (ContinuousMonoidHom.quotientMk N)
    (TopRep.quotientToInvariantsι (TopRep.quotientToInvariants X N) P)
    (TopRep.quotientToInvariantsι X N) n).symm

end Infl

end ContinuousCohomology

end TauCeti
