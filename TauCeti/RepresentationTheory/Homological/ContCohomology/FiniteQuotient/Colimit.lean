/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Invariants

/-!
# The first continuous cohomology of a profinite group as a colimit over its finite quotients

For a profinite group `G` and a discrete `G`-module `M`, the explicit first continuous cohomology
group `H¹(G, M)` is the colimit of the finite-level groups `H¹(G ⧸ U, M ^ U)` over the open normal
subgroups `U` of `G`. This file builds that system in degree one, the comparison maps into
`H¹(G, M)`, and proves the comparison cocone universal.

The two halves of the theorem are proved separately and are both available on their own. The
surjectivity half is *strict*: a continuous `1`-cocycle on `G` **is** the inflation of a continuous
`1`-cocycle at a finite level, with no coboundary subtracted, because a single open normal subgroup
both translates the cocycle to itself and fixes its (finitely many) values. A coboundary enters only
in the injectivity half, where a finite-level class that dies in `H¹(G, M)` is exhibited as dying
already at a deeper finite level: its primitive is a single element of `M`, and that element becomes
invariant far enough down the tower.

Compactness of `G` is used twice in the surjectivity half — through the tube lemma, for uniform
local constancy, and through finiteness of the range of a continuous map into a discrete space — and
total disconnectedness is used to produce open *normal* subgroups inside a neighbourhood of `1`.

## Main definitions

* `TauCeti.ContCohomology.explicitFiniteQuotientTransition1`: the transition map
  `H¹(G ⧸ U, M ^ U) →+ H¹(G ⧸ V, M ^ V)` for `V ≤ U`, defined directly by `explicitMap1` from the
  compatible pair `(G ⧸ V → G ⧸ U, M ^ U ↪ M ^ V)`.
* `TauCeti.ContCohomology.explicitFiniteQuotientSystem1`: the resulting functor on
  `(OpenNormalSubgroup G)ᵒᵖ` with values in `AddCommGrpCat`.
* `TauCeti.ContCohomology.explicitFiniteQuotientComparison1`: the comparison map
  `H¹(G ⧸ U, M ^ U) →+ H¹(G, M)`, inflation along `G → G ⧸ U` paired with `M ^ U ↪ M`, and
  `TauCeti.ContCohomology.explicitFiniteQuotientCocone1`, the cocone it assembles into.

## Main statements

* `TauCeti.ContCohomology.exists_openNormalSubgroup_forall_mul_eq`: a continuous map from a
  profinite group to a discrete space is uniformly locally constant.
* `TauCeti.ContCohomology.exists_openNormalSubgroup_eq_comp_mk`: strict finite-level descent of a
  continuous `1`-cocycle.
* `TauCeti.ContCohomology.exists_explicitFiniteQuotientComparison1_eq` and
  `TauCeti.ContCohomology.exists_le_explicitFiniteQuotientTransition1_eq_zero`: the comparison maps
  are jointly surjective, and their kernels are exhausted by the transition maps.
* `TauCeti.ContCohomology.explicitFiniteQuotientColimit1`: the comparison cocone is a colimit,
  which is the statement `H¹(G, M) ≅ colim_U H¹(G ⧸ U, M ^ U)`.

## Implementation notes

The system is indexed by the *opposite* of `OpenNormalSubgroup G` because the transition maps run
from the `U`-level to the `V`-level for `V ≤ U`, against the direction of Mathlib's
`ProfiniteGrp.toFiniteQuotientFunctor`; see the sibling file `FiniteQuotient/Basic.lean`, which
builds the same system for Mathlib's discrete `groupCohomology` in all degrees.

Universality is proved by hand rather than by comparing with an abstract filtered colimit: the two
halves above say exactly that the legs are jointly surjective and that their kernels are exhausted,
and those two facts determine the universal map directly. The auxiliary choice of a level for each
class is kept `private`; the public interface is the cocone and its universality.

This implements the degree-one case of the "colimit theorem" bullet of Layer 4 of the human-authored
roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`. Degrees `0` and `2` have the same shape,
with `H0` and `H2` in place of `H1`, and are not built here.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Cor. 6.5.6(a).
* H. Koch, *Galois Theory of p-Extensions*, Thm. 3.16.
-/

public section

namespace TauCeti.ContCohomology

open CategoryTheory MulAction

universe u

section UniformlyLocallyConstant

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {M : Type*} [TopologicalSpace M] [DiscreteTopology M]

/-- A continuous map from a profinite group to a discrete space is *uniformly* locally constant:
one open normal subgroup works at every point, so the map factors through a finite quotient as a
map of sets. -/
theorem exists_openNormalSubgroup_forall_mul_eq {c : G → M} (hc : Continuous c) :
    ∃ U : OpenNormalSubgroup G, ∀ (g x : G), x ∈ U → c (g * x) = c g := by
  have hcont : Continuous fun p : G × G ↦ (c (p.1 * p.2), c p.1) :=
    (hc.comp continuous_mul).prodMk (hc.comp continuous_fst)
  have hopen : IsOpen {p : G × G | c (p.1 * p.2) = c p.1} :=
    hcont.isOpen_preimage {q : M × M | q.1 = q.2} (isOpen_discrete _)
  obtain ⟨s, t, -, ht, hs, h1t, hst⟩ :=
    generalized_tube_lemma (isCompact_univ (X := G)) (isCompact_singleton (x := (1 : G))) hopen
      (fun p hp ↦ by simp [Set.mem_singleton_iff.1 hp.2])
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht (h1t rfl)
  exact ⟨U, fun g x hx ↦ @hst (g, x) ⟨hs (Set.mem_univ g), hU hx⟩⟩

variable [MulAction G M] [ContinuousSMul G M]

/-- One open normal subgroup serves a continuous map twice: it translates the map to itself and it
fixes every one of its values. This is the finite level at which a continuous cochain is defined,
and both halves use compactness of `G`, the first through uniform local constancy and the second
through finiteness of the range. -/
theorem exists_openNormalSubgroup_forall_mul_eq_and_smul_eq {c : G → M} (hc : Continuous c) :
    ∃ U : OpenNormalSubgroup G,
      (∀ (g x : G), x ∈ U → c (g * x) = c g) ∧ ∀ x ∈ U, ∀ g : G, x • c g = c g := by
  obtain ⟨U₁, hU₁⟩ := exists_openNormalSubgroup_forall_mul_eq hc
  obtain ⟨U₂, hU₂⟩ :=
    Set.Finite.exists_openNormalSubgroup_smul_eq_self (G := G)
      (((IsLocallyConstant.iff_continuous c).2 hc).range_finite)
  exact ⟨U₁ ⊓ U₂, fun g x hx ↦ hU₁ g x hx.1, fun x hx g ↦ hU₂ x hx.2 (c g) ⟨g, rfl⟩⟩

end UniformlyLocallyConstant

section Descent

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **Strict finite-level descent of a continuous `1`-cocycle.** A continuous `1`-cocycle on a
profinite group with discrete coefficients *is* the inflation of a continuous `1`-cocycle at some
finite level: there are an open normal subgroup `U` and a continuous `1`-cocycle `b` on `G ⧸ U`
with values in the invariants `M ^ U` whose composite with `G → G ⧸ U` is the given cocycle on the
nose. No coboundary is subtracted; a coboundary enters only in
`TauCeti.ContCohomology.exists_le_explicitFiniteQuotientTransition1_eq_zero`. -/
theorem exists_openNormalSubgroup_eq_comp_mk (c : Z1 G M) :
    ∃ (U : OpenNormalSubgroup G)
      (b : Z1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)),
      (fun g : G ↦ ((b.1 (g : G ⧸ U.toSubgroup) : FixedPoints.addSubgroup U.toSubgroup M) : M)) =
        (c : G → M) := by
  obtain ⟨U, htrans, hfix⟩ :=
    exists_openNormalSubgroup_forall_mul_eq_and_smul_eq (mem_Z1_iff.1 c.2).1
  -- The value of the descended cochain at a coset is the value of `c` at any representative.
  have hval : ∀ g : G, (c : G → M) (Quotient.out (g : G ⧸ U.toSubgroup)) = (c : G → M) g := by
    intro g
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup g
    rw [hx]
    exact htrans g x x.2
  have hmem : ∀ q : G ⧸ U.toSubgroup,
      (c : G → M) (Quotient.out q) ∈ FixedPoints.addSubgroup U.toSubgroup M :=
    fun q x ↦ hfix x x.2 _
  refine ⟨U, ⟨fun q ↦ ⟨(c : G → M) (Quotient.out q), hmem q⟩, mem_Z1_iff.2
    ⟨continuous_of_discreteTopology, ?_⟩⟩, funext fun g ↦ hval g⟩
  intro x y
  induction x using QuotientGroup.induction_on with
  | _ g =>
    induction y using QuotientGroup.induction_on with
    | _ h =>
      refine Subtype.ext ?_
      rw [← QuotientGroup.mk_mul]
      simp only [AddSubgroup.coe_add, coe_quotient_smul_fixedPoints_addSubgroup,
        coe_smul_fixedPoints_addSubgroup, hval]
      exact (mem_Z1_iff.1 c.2).2 g h

end Descent

section System

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- `TauCeti.finiteQuotientMap` as a continuous homomorphism. Continuity is automatic here: the
quotient of a topological group by an open subgroup is discrete. -/
def finiteQuotientContinuousMap {U V : OpenNormalSubgroup G} (hVU : V ≤ U) :
    (G ⧸ V.toSubgroup) →ₜ* (G ⧸ U.toSubgroup) where
  __ := finiteQuotientMap (U := U.toSubgroup) (V := V.toSubgroup) hVU
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem coe_finiteQuotientContinuousMap {U V : OpenNormalSubgroup G} (hVU : V ≤ U) :
    (finiteQuotientContinuousMap G hVU : (G ⧸ V.toSubgroup) →* (G ⧸ U.toSubgroup)) =
      finiteQuotientMap (U := U.toSubgroup) (V := V.toSubgroup) hVU :=
  (rfl)

@[simp]
theorem finiteQuotientContinuousMap_mk {U V : OpenNormalSubgroup G} (hVU : V ≤ U) (g : G) :
    finiteQuotientContinuousMap G hVU (g : G ⧸ V.toSubgroup) = (g : G ⧸ U.toSubgroup) :=
  finiteQuotientMap_mk (U := U.toSubgroup) (V := V.toSubgroup) hVU g

@[simp]
theorem finiteQuotientContinuousMap_refl (U : OpenNormalSubgroup G) :
    finiteQuotientContinuousMap G (le_refl U) = ContinuousMonoidHom.id (G ⧸ U.toSubgroup) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | _ g => simp

@[simp]
theorem finiteQuotientContinuousMap_comp {U V W : OpenNormalSubgroup G} (hWV : W ≤ V)
    (hVU : V ≤ U) :
    (finiteQuotientContinuousMap G hVU).comp (finiteQuotientContinuousMap G hWV) =
      finiteQuotientContinuousMap G (hWV.trans hVU) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | _ g => simp

/-- **The explicit degree-1 transition map of the finite-quotient system.** For `V ≤ U` it is the
pullback along the compatible pair consisting of the quotient homomorphism `G ⧸ V → G ⧸ U` and the
coefficient inclusion `M ^ U ↪ M ^ V`. It is defined directly by
`TauCeti.ContCohomology.explicitMap1`, hence is universe-polymorphic and does not pass through the
comparison with Mathlib's `groupCohomology`. -/
noncomputable def explicitFiniteQuotientTransition1 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
      H1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  explicitMap1 (G ⧸ U.toSubgroup) _ (G ⧸ V.toSubgroup) _ (finiteQuotientContinuousMap G hVU)
    -- `TauCeti.fixedPointsInclusion` is the same map on the additive *submonoid* carrier, whose
    -- `AddZeroClass` instance is not the one an `AddSubgroup` carries; the whole system lives on
    -- `AddSubgroup`s, so the inclusion is taken there.
    (AddSubgroup.inclusion (fixedPoints_addSubgroup_le M hVU))
    continuous_of_discreteTopology
    fun q m ↦ by
      induction q using QuotientGroup.induction_on with
      | _ g =>
        -- Both sides are the class of `g • m`: the inclusion of invariants and the two quotient
        -- actions are all induced by the action on `M`.
        rw [finiteQuotientContinuousMap_mk]
        rfl

omit [ContinuousSMul G M] in
/-- The characteristic property of the transition map: it leaves the underlying `M`-valued cochain
of a cocycle alone, so any continuous `1`-cocycle at the deeper level with the same values
represents the image class. -/
theorem explicitFiniteQuotientTransition1_mk (U V : OpenNormalSubgroup G) (hVU : V ≤ U)
    (c : Z1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (b : Z1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M))
    (h : ∀ g : G, (b.1 (g : G ⧸ V.toSubgroup) : M) = (c.1 (g : G ⧸ U.toSubgroup) : M)) :
    explicitFiniteQuotientTransition1 G M U V hVU (c : H1 _ _) = (b : H1 _ _) := by
  rw [explicitFiniteQuotientTransition1, explicitMap1_mk]
  congr 1
  refine Subtype.ext (funext fun q ↦ ?_)
  induction q using QuotientGroup.induction_on with
  | _ g =>
    refine Subtype.ext ?_
    rw [cocyclesMap1_apply, AddSubgroup.coe_inclusion, finiteQuotientContinuousMap_mk]
    exact (h g).symm

omit [ContinuousSMul G M] in
/-- The first functor law of the finite-quotient system: the transition from a level to itself is
the identity. -/
theorem explicitFiniteQuotientTransition1_id (U : OpenNormalSubgroup G) :
    explicitFiniteQuotientTransition1 G M U U le_rfl = AddMonoidHom.id _ := by
  have hf : (AddSubgroup.inclusion (fixedPoints_addSubgroup_le M (le_refl U.toSubgroup)) :
      FixedPoints.addSubgroup U.toSubgroup M →+ FixedPoints.addSubgroup U.toSubgroup M) =
      AddMonoidHom.id _ := AddMonoidHom.ext fun _ ↦ Subtype.ext rfl
  rw [explicitFiniteQuotientTransition1]
  exact (explicitMap1_congr _ _ _ _ (finiteQuotientContinuousMap_refl G U) hf).trans
    (explicitMap1_id _ _ fun _ _ ↦ rfl)

omit [ContinuousSMul G M] in
/-- The second functor law of the finite-quotient system: for `W ≤ V ≤ U` the transition from the
`U`-level to the `W`-level is the composite through the `V`-level. -/
theorem explicitFiniteQuotientTransition1_comp (U V W : OpenNormalSubgroup G) (hVU : V ≤ U)
    (hWV : W ≤ V) :
    explicitFiniteQuotientTransition1 G M U W (hWV.trans hVU) =
      (explicitFiniteQuotientTransition1 G M V W hWV).comp
        (explicitFiniteQuotientTransition1 G M U V hVU) := by
  rw [explicitFiniteQuotientTransition1, explicitFiniteQuotientTransition1,
    explicitFiniteQuotientTransition1, ← explicitMap1_comp]
  · exact explicitMap1_congr _ _ _ _ (finiteQuotientContinuousMap_comp G hWV hVU).symm
      (AddMonoidHom.ext fun _ ↦ Subtype.ext rfl)
  · intro k m
    induction k using QuotientGroup.induction_on with
    | _ g =>
      rw [finiteQuotientContinuousMap_comp, finiteQuotientContinuousMap_mk,
        AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      exact Subtype.ext rfl

omit [IsTopologicalGroup G] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The inclusion `M ^ U ↪ M` of the invariants is continuous. It is stated on the bundled
`AddSubgroup.subtype` rather than on `Subtype.val` because that is the form the compatible pair
below is built from. -/
theorem continuous_invariantsSubtype (U : OpenNormalSubgroup G) :
    Continuous ⇑(FixedPoints.addSubgroup U.toSubgroup M).subtype :=
  continuous_subtype_val

omit [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The inclusion `M ^ U ↪ M` is equivariant along the projection `G → G ⧸ U`, which is what makes
the pair `(G → G ⧸ U, M ^ U ↪ M)` a compatible pair. -/
theorem invariantsSubtype_quotientMk_smul (U : OpenNormalSubgroup G) (g : G)
    (m : FixedPoints.addSubgroup U.toSubgroup M) :
    (FixedPoints.addSubgroup U.toSubgroup M).subtype
        (ContinuousMonoidHom.quotientMk U.toSubgroup g • m) =
      g • (FixedPoints.addSubgroup U.toSubgroup M).subtype m := by
  simp

/-- **The comparison map of the finite-quotient system in degree 1**: inflation along the
projection `G → G ⧸ U`, paired with the coefficient inclusion `M ^ U ↪ M`. The colimit theorem
below says that *these* maps are universal, not merely that some isomorphism exists. -/
noncomputable def explicitFiniteQuotientComparison1 (U : OpenNormalSubgroup G) :
    H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+ H1 G M :=
  explicitMap1 (G ⧸ U.toSubgroup) _ G M (ContinuousMonoidHom.quotientMk U.toSubgroup)
    (FixedPoints.addSubgroup U.toSubgroup M).subtype (continuous_invariantsSubtype G M U)
    (invariantsSubtype_quotientMk_smul G M U)

/-- The characteristic property of the comparison map: inflation leaves the underlying `M`-valued
cochain of a cocycle alone, so any continuous `1`-cocycle on `G` with the same values represents
the image class. -/
theorem explicitFiniteQuotientComparison1_mk (U : OpenNormalSubgroup G)
    (c : Z1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) (d : Z1 G M)
    (h : ∀ g : G, (d : G → M) g = (c.1 (g : G ⧸ U.toSubgroup) : M)) :
    explicitFiniteQuotientComparison1 G M U (c : H1 _ _) = (d : H1 G M) := by
  rw [explicitFiniteQuotientComparison1, explicitMap1_mk]
  congr 1
  refine Subtype.ext (funext fun g ↦ ?_)
  rw [cocyclesMap1_apply, AddSubgroup.coe_subtype, ContinuousMonoidHom.quotientMk_apply]
  exact (h g).symm

/-- The comparison maps are the legs of a cocone: comparing at a deeper level after the transition
map is comparing at the original level. -/
theorem explicitFiniteQuotientComparison1_comp_transition1 (U V : OpenNormalSubgroup G)
    (hVU : V ≤ U) :
    (explicitFiniteQuotientComparison1 G M V).comp
        (explicitFiniteQuotientTransition1 G M U V hVU) =
      explicitFiniteQuotientComparison1 G M U := by
  refine AddMonoidHom.ext fun x ↦ ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [AddMonoidHom.comp_apply, explicitFiniteQuotientTransition1,
      explicitFiniteQuotientComparison1, explicitMap1_mk]
    congr 1
    refine Subtype.ext (funext fun g ↦ ?_)
    simp only [cocyclesMap1_apply, AddSubgroup.coe_subtype,
      ContinuousMonoidHom.quotientMk_apply, finiteQuotientContinuousMap_mk]
    -- Both sides are now the value of `c` at the class of `g`, read in `M` through the inclusion
    -- of invariants, which does not move an element.
    rfl

/-- **The explicit finite-quotient system in degree 1**, as a functor on
`(OpenNormalSubgroup G)ᵒᵖ`. The index category is the opposite one because the transition maps run
from the `U`-level to the `V`-level for `V ≤ U`, against the direction of Mathlib's
`ProfiniteGrp.toFiniteQuotientFunctor`; the two functor laws are
`TauCeti.ContCohomology.explicitFiniteQuotientTransition1_id` and
`TauCeti.ContCohomology.explicitFiniteQuotientTransition1_comp`. -/
@[expose] noncomputable def explicitFiniteQuotientSystem1 :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of
    (H1 (G ⧸ U.unop.toSubgroup) (FixedPoints.addSubgroup U.unop.toSubgroup M))
  map f := AddCommGrpCat.ofHom
    (explicitFiniteQuotientTransition1 G M _ _ (leOfHom f.unop))
  map_id U := by
    rw [explicitFiniteQuotientTransition1_id]
    exact AddCommGrpCat.ofHom_id
  map_comp f g := by
    rw [explicitFiniteQuotientTransition1_comp G M _ _ _ (leOfHom f.unop) (leOfHom g.unop),
      AddCommGrpCat.ofHom_comp]

omit [ContinuousSMul G M] in
/-- The value of the explicit degree-1 system at a level, which is what makes the colimit statement
a statement about `H¹(G ⧸ U, M ^ U)` rather than about an unnamed functor. -/
@[simp]
theorem explicitFiniteQuotientSystem1_obj (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (explicitFiniteQuotientSystem1 G M).obj U = AddCommGrpCat.of
      (H1 (G ⧸ U.unop.toSubgroup) (FixedPoints.addSubgroup U.unop.toSubgroup M)) :=
  (rfl)

omit [ContinuousSMul G M] in
/-- The arrow of the explicit degree-1 system is the direct explicit transition map. This rules out
silently transporting a transition through a universe-restricted comparison. -/
@[simp]
theorem explicitFiniteQuotientSystem1_map {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    (explicitFiniteQuotientSystem1 G M).map f = AddCommGrpCat.ofHom
      (explicitFiniteQuotientTransition1 G M U.unop V.unop (leOfHom f.unop)) :=
  (rfl)

/-- **The comparison cocone of the finite-quotient system in degree 1**, whose point is
`H¹(G, M)` itself and whose legs are the comparison maps. -/
@[expose] noncomputable def explicitFiniteQuotientCocone1 :
    Limits.Cocone (explicitFiniteQuotientSystem1 G M) where
  pt := AddCommGrpCat.of (H1 G M)
  ι :=
    { app U := AddCommGrpCat.ofHom (explicitFiniteQuotientComparison1 G M U.unop)
      naturality U V f := by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y ↦ ?_)
        exact DFunLike.congr_fun
          (explicitFiniteQuotientComparison1_comp_transition1 G M U.unop V.unop
            (leOfHom f.unop)) y }

@[simp]
theorem explicitFiniteQuotientCocone1_pt :
    (explicitFiniteQuotientCocone1 G M).pt = AddCommGrpCat.of (H1 G M) :=
  (rfl)

@[simp]
theorem explicitFiniteQuotientCocone1_ι_app (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (explicitFiniteQuotientCocone1 G M).ι.app U =
      AddCommGrpCat.ofHom (explicitFiniteQuotientComparison1 G M U.unop) :=
  (rfl)

end System

section Universality

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **The comparison maps are jointly surjective.** Every class in `H¹(G, M)` is inflated from a
finite level, and by `TauCeti.ContCohomology.exists_openNormalSubgroup_eq_comp_mk` already at the
level of cocycles: no coboundary is subtracted. -/
theorem exists_explicitFiniteQuotientComparison1_eq (x : H1 G M) :
    ∃ (U : OpenNormalSubgroup G)
      (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)),
      explicitFiniteQuotientComparison1 G M U y = x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    obtain ⟨U, b, hb⟩ := exists_openNormalSubgroup_eq_comp_mk c
    exact ⟨U, (b : H1 _ _),
      explicitFiniteQuotientComparison1_mk G M U b c fun g ↦ (congrFun hb g).symm⟩

/-- **The kernel of the comparison is exhausted level by level.** A finite-level class that dies in
`H¹(G, M)` already dies at some deeper finite level. This is the injectivity half of the colimit
theorem, and the only place where a coboundary enters: the primitive of the inflated cocycle is a
single element of `M`, and it becomes invariant at a small enough level. -/
theorem exists_le_explicitFiniteQuotientTransition1_eq_zero (U : OpenNormalSubgroup G)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (hy : explicitFiniteQuotientComparison1 G M U y = 0) :
    ∃ (V : OpenNormalSubgroup G) (hVU : V ≤ U),
      explicitFiniteQuotientTransition1 G M U V hVU y = 0 := by
  induction y using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitFiniteQuotientComparison1, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hy
    obtain ⟨m, hm⟩ := hy
    obtain ⟨W, hW⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) m
    have hmem : m ∈ FixedPoints.addSubgroup (U ⊓ W : OpenNormalSubgroup G).toSubgroup M :=
      fun x ↦ hW x x.2.2
    refine ⟨U ⊓ W, inf_le_left, ?_⟩
    rw [explicitFiniteQuotientTransition1, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨⟨m, hmem⟩, fun q ↦ ?_⟩
    induction q using QuotientGroup.induction_on with
    | _ g =>
      refine Subtype.ext ?_
      have := hm g
      simp only [cocyclesMap1_apply, AddSubgroup.coe_subtype,
        ContinuousMonoidHom.quotientMk_apply] at this
      simp only [AddSubgroup.coe_sub, coe_quotient_smul_fixedPoints_addSubgroup,
        coe_smul_fixedPoints_addSubgroup, cocyclesMap1_apply, finiteQuotientContinuousMap_mk]
      rw [this]
      -- What is left is the inclusion of invariants, which does not move an element of `M`.
      rfl

variable {G M}

/-- The leg of a cocone over the finite-quotient system at a level, as an additive map. -/
private noncomputable def coconeLeg (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M))
    (U : OpenNormalSubgroup G) :
    H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+ s.pt :=
  (s.ι.app (Opposite.op U)).hom

omit [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G M] in
private theorem coconeLeg_transition (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M))
    {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    coconeLeg s V (explicitFiniteQuotientTransition1 G M U V hVU y) = coconeLeg s U y :=
  congrArg (fun t : _ ⟶ s.pt ↦ t.hom y) (s.w (homOfLE hVU).op)

private theorem coconeLeg_eq_zero (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M))
    (U : OpenNormalSubgroup G)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (hy : explicitFiniteQuotientComparison1 G M U y = 0) : coconeLeg s U y = 0 := by
  obtain ⟨V, hVU, hV⟩ := exists_le_explicitFiniteQuotientTransition1_eq_zero G M U y hy
  rw [← coconeLeg_transition s hVU y, hV, map_zero]

private theorem coconeLeg_eq (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M))
    {U V : OpenNormalSubgroup G}
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (z : H1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M))
    (h : explicitFiniteQuotientComparison1 G M U y =
      explicitFiniteQuotientComparison1 G M V z) : coconeLeg s U y = coconeLeg s V z := by
  have key : coconeLeg s (U ⊓ V)
      (explicitFiniteQuotientTransition1 G M U (U ⊓ V) inf_le_left y -
        explicitFiniteQuotientTransition1 G M V (U ⊓ V) inf_le_right z) = 0 := by
    refine coconeLeg_eq_zero s _ _ ?_
    rw [map_sub, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
      explicitFiniteQuotientComparison1_comp_transition1,
      explicitFiniteQuotientComparison1_comp_transition1, h, sub_self]
  rw [map_sub, coconeLeg_transition, coconeLeg_transition, sub_eq_zero] at key
  exact key

variable (G M)

/-- A finite level at which a given class of `H¹(G, M)` is already defined. -/
private noncomputable def descLevel (x : H1 G M) : OpenNormalSubgroup G :=
  (exists_explicitFiniteQuotientComparison1_eq G M x).choose

/-- A finite-level class comparing to a given class of `H¹(G, M)`. -/
private noncomputable def descRep (x : H1 G M) :
    H1 (G ⧸ (descLevel G M x).toSubgroup)
      (FixedPoints.addSubgroup (descLevel G M x).toSubgroup M) :=
  (exists_explicitFiniteQuotientComparison1_eq G M x).choose_spec.choose

private theorem explicitFiniteQuotientComparison1_descRep (x : H1 G M) :
    explicitFiniteQuotientComparison1 G M (descLevel G M x) (descRep G M x) = x :=
  (exists_explicitFiniteQuotientComparison1_eq G M x).choose_spec.choose_spec

variable {G M}

/-- The universal map out of `H¹(G, M)` attached to a cocone: the value of the cocone's leg on any
finite-level class comparing to the given one. -/
private noncomputable def descFun (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M))
    (x : H1 G M) : s.pt :=
  coconeLeg s (descLevel G M x) (descRep G M x)

private theorem descFun_eq (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M)) {x : H1 G M}
    (U : OpenNormalSubgroup G)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (h : explicitFiniteQuotientComparison1 G M U y = x) : descFun s x = coconeLeg s U y :=
  coconeLeg_eq s _ _ (by rw [explicitFiniteQuotientComparison1_descRep, h])

private noncomputable def descHom (s : Limits.Cocone (explicitFiniteQuotientSystem1 G M)) :
    H1 G M →+ s.pt where
  toFun := descFun s
  map_zero' := coconeLeg_eq_zero s _ _ (explicitFiniteQuotientComparison1_descRep G M 0)
  map_add' x x' := by
    set U := descLevel G M x
    set V := descLevel G M x'
    rw [descFun_eq s U (descRep G M x) (explicitFiniteQuotientComparison1_descRep G M x),
      descFun_eq s V (descRep G M x') (explicitFiniteQuotientComparison1_descRep G M x'),
      ← coconeLeg_transition s (inf_le_left : U ⊓ V ≤ U) (descRep G M x),
      ← coconeLeg_transition s (inf_le_right : U ⊓ V ≤ V) (descRep G M x'), ← map_add]
    refine descFun_eq s (U ⊓ V) _ ?_
    rw [map_add, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
      explicitFiniteQuotientComparison1_comp_transition1,
      explicitFiniteQuotientComparison1_comp_transition1,
      explicitFiniteQuotientComparison1_descRep, explicitFiniteQuotientComparison1_descRep]

variable (G M)

/-- **The colimit theorem in degree 1**: for a profinite group `G` and a discrete `G`-module `M`,
`H¹(G, M) ≅ colim_U H¹(G ⧸ U, M ^ U)` over the open normal subgroups, in the form that says the
named comparison cocone is universal rather than that some isomorphism exists. -/
noncomputable def explicitFiniteQuotientColimit1 :
    Limits.IsColimit (explicitFiniteQuotientCocone1 G M) where
  desc s := AddCommGrpCat.ofHom (descHom s)
  fac s U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y ↦ ?_)
    -- The level and representative chosen for `explicitFiniteQuotientComparison1 G M U.unop y` are
    -- named explicitly: leaving them to unification makes the elaborator unfold the choice.
    exact descFun_eq (x := explicitFiniteQuotientComparison1 G M U.unop y) s U.unop y rfl
  uniq s m hm := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_)
    conv_lhs => rw [← explicitFiniteQuotientComparison1_descRep G M x]
    exact congrArg (fun t : _ ⟶ s.pt ↦ t.hom (descRep G M x))
      (hm (Opposite.op (descLevel G M x)))

end Universality

end TauCeti.ContCohomology
