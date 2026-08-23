/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# The finite-quotient system of a group cohomology tower

For a normal subgroup `U` of a group `G` and a `G`-representation `A`, Mathlib's
`Rep.quotientToInvariants` makes the invariants `A^U` a representation of `G ⧸ U`, so that
`Hⁿ(G ⧸ U, A^U)` is defined. As `U` shrinks these groups form a directed system: for `V ≤ U` the
quotient homomorphism `G ⧸ V →* G ⧸ U` and the coefficient inclusion `A^U ↪ A^V` are a compatible
pair in the sense of `groupCohomology.map`, and so induce

`Hⁿ(G ⧸ U, A^U) ⟶ Hⁿ(G ⧸ V, A^V)`.

The transition maps therefore run *opposite* to the quotient homomorphisms, and the system is a
functor on the opposite of the index poset. This file builds it over the open normal subgroups of
a topological group, which is the index poset the profinite colimit theorem uses. That theorem —
that the colimit of this system computes the continuous cohomology of `G` — needs `G` profinite
and the coefficients discrete, and is not stated here: no construction or law below assumes
either hypothesis, and no comparison map to continuous cohomology is constructed.

The finite-level tower built here is the one the standard accounts of profinite cohomology
describe; the references below state the colimit theorem this system is the source of.

## Main definitions

* `TauCeti.finiteQuotientMap hVU`: the quotient homomorphism `G ⧸ V →* G ⧸ U` for `V ≤ U`.
* `TauCeti.invariantsInclusion A hVU`: the inclusion `A^U ↪ A^V` for `V ≤ U`.
* `TauCeti.transitionPair A hVU`: the compatible pair assembled from the two.
* `TauCeti.finiteLevelTransition A hVU n`: the induced map `Hⁿ(G ⧸ U, A^U) ⟶ Hⁿ(G ⧸ V, A^V)`.
* `TauCeti.finiteLevelFunctor k U n`: the `U`-level `A ↦ Hⁿ(G ⧸ U, A^U)` as a functor of the
  coefficient representation.
* `TauCeti.finiteQuotientSystem A n`: the system as a functor
  `(OpenNormalSubgroup G)ᵒᵖ ⥤ ModuleCat k`.
* `TauCeti.finiteQuotientSystemFunctor k G n`: the same system, as a functor of the coefficient
  representation.

## Main statements

* `TauCeti.toFiniteQuotientFunctor_map_hom_hom`: the group half of the system is exactly the
  tower of Mathlib's `ProfiniteGrp.toFiniteQuotientFunctor`.
* `TauCeti.invariantsInclusion_equivariant`: the coefficient inclusion is equivariant after
  restriction along `finiteQuotientMap`, which is what makes `transitionPair` a compatible pair.
* `TauCeti.finiteLevelTransition_refl` and `TauCeti.finiteLevelTransition_comp`: the two functor
  laws, which are what make the transition maps a system on the opposite poset.
* `TauCeti.transitionPair_naturality` and `TauCeti.finiteLevelTransition_naturality`: a morphism
  of coefficients commutes with the transition pairs, and hence with the transition maps.

## Implementation notes

Everything except the two `OpenNormalSubgroup`-indexed functors and the comparison theorem is
stated for arbitrary normal subgroups `V ≤ U` of an arbitrary group, since that is all the proofs
use. Openness enters only through the index poset `OpenNormalSubgroup G`. Profiniteness enters
only in `TauCeti.toFiniteQuotientFunctor_map_hom_hom`, which quantifies over an object of
`ProfiniteGrp` because it compares with a functor Mathlib defines on that category; it is a
hypothesis of no construction and of no transition law here. What the later colimit theorem adds,
over this same index poset, is profiniteness of `G` as an unbundled hypothesis together with
discreteness of the coefficients, in order to identify the colimit with continuous cohomology.

`finiteQuotientMap` is Mathlib's `QuotientGroup.map` at the identity of `G`, the same map
`ProfiniteGrp.toFiniteQuotientFunctor` uses. It is named here because `QuotientGroup.map` asks for
`V ≤ Subgroup.comap (MonoidHom.id G) U` rather than `V ≤ U`, and the two are equal only up to
unfolding; naming the specialization keeps the compatible pairs below rewritable.

`finiteQuotientMap`, `invariantsInclusion`, `transitionPair` and `finiteLevelTransition` keep
their bodies sealed: each is characterized by its `_mk`, `_apply_coe`, `_hom_toLinearMap` and
functor-law lemmas, and those lemmas are proved as `(rfl)`, so no consumer unfolds a body. The
three functors are `@[expose]` instead, because the *statement* of a functor's `map` lemma does
not elaborate with the body sealed: the left-hand side lives in `F.obj A ⟶ F.obj B` and the
right-hand side in the type the `obj` field reduces to, so without the body the characteristic
lemma cannot even be written down.

This implements the six milestones of the "The system" bullet of Layer 4 of the human-authored
roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, together with the functoriality of the
whole system in the coefficients that the same bullet asks for. The colimit theorem of that same
layer is separate, and stays out: it is stated on the explicit low-degree complex and compared
with the canonical object, so it consumes the roadmap's Layers 2 and 3, neither of which the
system built here uses — every ingredient below is Mathlib's.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Cor. 6.5.6(a).
-/

public section

namespace TauCeti

open CategoryTheory Representation

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-! ### The two halves of a transition pair -/

section Pair

variable {U V W : Subgroup G}

/-- The group half of a transition pair of the finite-quotient system: the quotient homomorphism
`G ⧸ V →* G ⧸ U` for normal subgroups `V ≤ U`. This is Mathlib's `QuotientGroup.map` at the
identity of `G`, the map `ProfiniteGrp.toFiniteQuotientFunctor` sends `V ≤ U` to. -/
def finiteQuotientMap [U.Normal] [V.Normal] (hVU : V ≤ U) : G ⧸ V →* G ⧸ U :=
  QuotientGroup.map V U (.id G) fun _ hv => hVU hv

@[simp]
theorem finiteQuotientMap_mk [U.Normal] [V.Normal] (hVU : V ≤ U) (g : G) :
    finiteQuotientMap hVU (g : G ⧸ V) = (g : G ⧸ U) :=
  (rfl)

@[simp]
theorem finiteQuotientMap_refl [U.Normal] :
    finiteQuotientMap (le_refl U) = MonoidHom.id (G ⧸ U) :=
  QuotientGroup.map_id U _

@[simp]
theorem finiteQuotientMap_comp [U.Normal] [V.Normal] [W.Normal] (hWV : W ≤ V) (hVU : V ≤ U) :
    (finiteQuotientMap hVU).comp (finiteQuotientMap hWV) = finiteQuotientMap (hWV.trans hVU) :=
  QuotientGroup.map_comp_map W V U (.id G) (.id G) _ _ _

/-- Invariants grow as the subgroup shrinks: a vector fixed by `U` is fixed by every `V ≤ U`. -/
theorem invariants_le (hVU : V ≤ U) :
    invariants (A.ρ.comp U.subtype) ≤ invariants (A.ρ.comp V.subtype) :=
  fun _ hm v => hm ⟨v.1, hVU v.2⟩

/-- The coefficient half of a transition pair of the finite-quotient system: the inclusion
`A^U ↪ A^V` for `V ≤ U`. -/
noncomputable def invariantsInclusion (hVU : V ≤ U) :
    invariants (A.ρ.comp U.subtype) →ₗ[k] invariants (A.ρ.comp V.subtype) :=
  Submodule.inclusion (invariants_le A hVU)

@[simp]
theorem invariantsInclusion_apply_coe (hVU : V ≤ U) (m : invariants (A.ρ.comp U.subtype)) :
    (invariantsInclusion A hVU m : A) = (m : A) :=
  (rfl)

@[simp]
theorem invariantsInclusion_refl : invariantsInclusion A (le_refl U) = LinearMap.id :=
  (rfl)

@[simp]
theorem invariantsInclusion_comp (hWV : W ≤ V) (hVU : V ≤ U) :
    (invariantsInclusion A hWV).comp (invariantsInclusion A hVU) =
      invariantsInclusion A (hWV.trans hVU) :=
  (rfl)

end Pair

/-! ### The transition maps of the system -/

section Transition

variable {U V W : Subgroup G} [U.Normal] [V.Normal] [W.Normal]

/-- Equivariance of the coefficient inclusion after restriction along `finiteQuotientMap`: the
`G ⧸ U`-action on `A^U`, pulled back along `G ⧸ V →* G ⧸ U`, agrees with the `G ⧸ V`-action on
`A^V`. This holds because the action of `g` on `A^U` depends only on the class of `g` modulo any
subgroup of `U`, and it is what makes `TauCeti.transitionPair` well typed. -/
theorem invariantsInclusion_equivariant (hVU : V ≤ U) (x : G ⧸ V)
    (m : invariants (A.ρ.comp U.subtype)) :
    invariantsInclusion A hVU
        ((A.quotientToInvariants U).ρ (finiteQuotientMap hVU x) m) =
      (A.quotientToInvariants V).ρ x (invariantsInclusion A hVU m) := by
  induction x using QuotientGroup.induction_on with
  | _ g => ext; simp

/-- A transition pair of the finite-quotient system, assembled from `TauCeti.finiteQuotientMap`
and `TauCeti.invariantsInclusion`. -/
noncomputable def transitionPair (hVU : V ≤ U) :
    Rep.res (finiteQuotientMap hVU) (A.quotientToInvariants U) ⟶ A.quotientToInvariants V :=
  Rep.ofHom ⟨invariantsInclusion A hVU,
    fun x ↦ LinearMap.ext (invariantsInclusion_equivariant A hVU x)⟩

@[simp]
theorem transitionPair_hom_toLinearMap (hVU : V ≤ U) :
    (transitionPair A hVU).hom.toLinearMap = invariantsInclusion A hVU :=
  (rfl)

/-- The transition map of the finite-quotient system: `Hⁿ(G ⧸ U, A^U) ⟶ Hⁿ(G ⧸ V, A^V)` for
normal subgroups `V ≤ U`, induced by `TauCeti.transitionPair`. -/
noncomputable def finiteLevelTransition (hVU : V ≤ U) (n : ℕ) :
    groupCohomology (A.quotientToInvariants U) n ⟶
      groupCohomology (A.quotientToInvariants V) n :=
  groupCohomology.map (finiteQuotientMap hVU) (transitionPair A hVU) n

/-- The first functor law: the transition map from a level to itself is the identity. -/
@[simp]
theorem finiteLevelTransition_refl (U : Subgroup G) [U.Normal] (n : ℕ) :
    finiteLevelTransition A (le_refl U) n = 𝟙 _ := by
  rw [finiteLevelTransition, ← groupCohomology.map_id (B := A.quotientToInvariants U) (n := n)]
  exact groupCohomology.map_congr finiteQuotientMap_refl rfl n

/-- The second functor law: for `W ≤ V ≤ U` the transition from the `U`-level to the `W`-level is
the composite through the `V`-level. With `TauCeti.finiteLevelTransition_refl` this says the
finite-quotient system is a functor on the opposite of the poset of normal subgroups. -/
@[reassoc]
theorem finiteLevelTransition_comp (hWV : W ≤ V) (hVU : V ≤ U) (n : ℕ) :
    finiteLevelTransition A (hWV.trans hVU) n =
      finiteLevelTransition A hVU n ≫ finiteLevelTransition A hWV n := by
  rw [finiteLevelTransition, finiteLevelTransition, finiteLevelTransition,
    ← groupCohomology.map_comp]
  exact groupCohomology.map_congr (finiteQuotientMap_comp hWV hVU).symm rfl n

end Transition

/-! ### Functoriality in the coefficients -/

section Coefficients

variable {A} {B C : Rep k G} {U V : Subgroup G} [U.Normal] [V.Normal]

variable (k) in
/-- The `U`-level of the finite-quotient system, as a functor of the coefficients: the composite
of Mathlib's `Rep.quotientToInvariantsFunctor` with `groupCohomology.functor`, sending a
`G`-representation `A` to `Hⁿ(G ⧸ U, A^U)`. Its `map` is the coefficient half of the
functoriality of the whole system, and it is the source of Mathlib's inflation natural
transformation `groupCohomology.infNatTrans`. -/
@[expose] noncomputable def finiteLevelFunctor (U : Subgroup G) [U.Normal] (n : ℕ) :
    Rep k G ⥤ ModuleCat.{u} k :=
  Rep.quotientToInvariantsFunctor k U ⋙ groupCohomology.functor k (G ⧸ U) n

@[simp]
theorem finiteLevelFunctor_obj (U : Subgroup G) [U.Normal] (n : ℕ) (A : Rep k G) :
    (finiteLevelFunctor k U n).obj A = groupCohomology (A.quotientToInvariants U) n :=
  (rfl)

@[simp]
theorem finiteLevelFunctor_map (U : Subgroup G) [U.Normal] (n : ℕ) (f : A ⟶ B) :
    (finiteLevelFunctor k U n).map f =
      groupCohomology.map (MonoidHom.id (G ⧸ U))
        ((Rep.quotientToInvariantsFunctor k U).map f) n :=
  (rfl)

/-- The coefficient square of the finite-quotient system: a transition pair is natural in the
coefficients. Applying a morphism `f : A ⟶ B` on `V`-invariants after the inclusion `A^U ↪ A^V`
is applying it on `U`-invariants and then including `B^U ↪ B^V`; both composites send `m : A^U`
to `f m`. It is stated on the underlying linear maps because that is the form in which
`groupCohomology.map_congr` compares two compatible pairs, and it is the substance of
`TauCeti.finiteLevelTransition_naturality`. -/
theorem transitionPair_naturality (f : A ⟶ B) (hVU : V ≤ U) :
    ((Rep.resFunctor (MonoidHom.id (G ⧸ V))).map (transitionPair A hVU) ≫
          (Rep.quotientToInvariantsFunctor k V).map f).hom.toLinearMap =
      ((Rep.resFunctor (finiteQuotientMap hVU)).map ((Rep.quotientToInvariantsFunctor k U).map f) ≫
          transitionPair B hVU).hom.toLinearMap := by
  simp only [Rep.res_obj_ρ, Rep.quotientToInvariantsFunctor, Rep.invariantsFunctor_map_hom,
    Rep.resMap_hom_toLinearMap, Rep.hom_comp, ConcreteCategory.hom_ofHom,
    IntertwiningMap.comp_toLinearMap, transitionPair_hom_toLinearMap]
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, IntertwiningMap.coe_toLinearMap,
    Submodule.coe_subtype, Function.comp_apply, invariantsInclusion_apply_coe]

/-- A morphism of coefficients commutes with the transition maps of the finite-quotient system.
This is the naturality of `TauCeti.finiteQuotientSystem` in the coefficient representation. -/
theorem finiteLevelTransition_naturality (f : A ⟶ B) (hVU : V ≤ U) (n : ℕ) :
    finiteLevelTransition A hVU n ≫ (finiteLevelFunctor k V n).map f =
      (finiteLevelFunctor k U n).map f ≫ finiteLevelTransition B hVU n := by
  rw [finiteLevelFunctor_map, finiteLevelFunctor_map, finiteLevelTransition, finiteLevelTransition]
  refine Eq.trans (groupCohomology.map_comp (finiteQuotientMap hVU) (MonoidHom.id (G ⧸ V))
      (transitionPair A hVU) _ n).symm ?_
  refine Eq.trans ?_ (groupCohomology.map_comp (MonoidHom.id (G ⧸ U)) (finiteQuotientMap hVU) _
      (transitionPair B hVU) n)
  -- The two compatible pairs have the same group half, and the same coefficient half by the
  -- square above.
  exact groupCohomology.map_congr
    (((finiteQuotientMap hVU).comp_id).trans ((finiteQuotientMap hVU).id_comp).symm)
    (transitionPair_naturality f hVU) n

end Coefficients

/-! ### The system over the open normal subgroups -/

section System

variable [TopologicalSpace G]

/-- The tower of quotient homomorphisms of the finite-quotient system is Mathlib's
`ProfiniteGrp.toFiniteQuotientFunctor`. Its arrows run from the smaller subgroup to the larger
one, which is why the cohomological system below is indexed by the opposite category. -/
theorem toFiniteQuotientFunctor_map_hom_hom (P : ProfiniteGrp.{u})
    {U V : OpenNormalSubgroup P} (f : V ⟶ U) :
    (P.toFiniteQuotientFunctor.map f).hom.hom = finiteQuotientMap (leOfHom f) :=
  (rfl)

/-- The finite-quotient system of a `G`-representation `A`: the functor sending an open normal
subgroup `U` of `G` to `Hⁿ(G ⧸ U, A^U)`, with `TauCeti.finiteLevelTransition` for its arrows.

The index category is the *opposite* of `OpenNormalSubgroup G` because the transition maps run
from the `U`-level to the `V`-level for `V ≤ U`, opposite to the quotient homomorphisms
`G ⧸ V → G ⧸ U` of `ProfiniteGrp.toFiniteQuotientFunctor`. -/
@[expose] noncomputable def finiteQuotientSystem (n : ℕ) :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := groupCohomology (A.quotientToInvariants U.unop.toSubgroup) n
  map f := finiteLevelTransition A (leOfHom f.unop) n
  map_id _ := finiteLevelTransition_refl A _ n
  map_comp f g := finiteLevelTransition_comp A (leOfHom g.unop) (leOfHom f.unop) n

@[simp]
theorem finiteQuotientSystem_obj (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (finiteQuotientSystem A n).obj U =
      groupCohomology (A.quotientToInvariants U.unop.toSubgroup) n :=
  (rfl)

@[simp]
theorem finiteQuotientSystem_map (n : ℕ) {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    (finiteQuotientSystem A n).map f = finiteLevelTransition A (leOfHom f.unop) n :=
  (rfl)

variable (k G) in
/-- The finite-quotient system as a functor of the coefficient representation: this packages
`TauCeti.finiteQuotientSystem` together with the naturality of its transition maps in the
coefficients. -/
@[expose] noncomputable def finiteQuotientSystemFunctor (n : ℕ) :
    Rep k G ⥤ ((OpenNormalSubgroup G)ᵒᵖ ⥤ ModuleCat.{u} k) where
  obj A := finiteQuotientSystem A n
  map f := { app U := (finiteLevelFunctor k U.unop.toSubgroup n).map f
             naturality _ _ g := finiteLevelTransition_naturality f (leOfHom g.unop) n }
  map_id A := NatTrans.ext <| funext fun U => (finiteLevelFunctor k U.unop.toSubgroup n).map_id A
  map_comp f g :=
    NatTrans.ext <| funext fun U => (finiteLevelFunctor k U.unop.toSubgroup n).map_comp f g

@[simp]
theorem finiteQuotientSystemFunctor_obj (n : ℕ) (A : Rep k G) :
    (finiteQuotientSystemFunctor k G n).obj A = finiteQuotientSystem A n :=
  (rfl)

@[simp]
theorem finiteQuotientSystemFunctor_map_app (n : ℕ) {A B : Rep k G} (f : A ⟶ B)
    (U : (OpenNormalSubgroup G)ᵒᵖ) :
    ((finiteQuotientSystemFunctor k G n).map f).app U =
      (finiteLevelFunctor k U.unop.toSubgroup n).map f :=
  (rfl)

end System

end TauCeti
