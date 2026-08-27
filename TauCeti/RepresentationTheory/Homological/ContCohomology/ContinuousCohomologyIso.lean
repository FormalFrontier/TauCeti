/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# The explicit model against the canonical object, in degree zero

The explicit low-degree complex presents `H⁰(G, M)` as the invariant subgroup `M^G` of a discrete
`G`-module, while the canonical object is Mathlib's `continuousCohomology 0 X` for `X` a
topological representation. This file identifies the two in degree zero, for `X` the image
`TauCeti.ofDiscreteModule ℤ G M` of `M` under the coefficient dictionary, and transports the
operations that exist in that degree across the identification.

The comparison is an isomorphism in `TopModuleCat ℤ`, not merely an additive one: `H⁰(G, M)` is a
subgroup of the discrete `M`, so it is discrete already and needs no separate discrete synonym,
and Mathlib's `ContinuousCohomology.zeroIso` exhibits the canonical carrier as homeomorphic to the
invariant subspace of the same module. The identity on underlying elements of `M` is therefore
already an isomorphism of topological `ℤ`-modules between `H⁰(G, M)` and those invariants, which is
`TauCeti.ContCohomology.H0ContinuousLinearEquivInvariants`; composing it with the inverse of
`zeroIso` gives `TauCeti.ContCohomology.explicitH0IsoContinuousCohomology`, whose value at an
invariant `m` is the degree-zero cohomology class of `m` in the sense of
`TauCeti.ContinuousCohomology.degreeZeroClass`.

Degree zero needs no hypothesis beyond the ones that make the two sides exist. In particular it
needs neither profiniteness of `G` nor continuity of the action `G × M → M`: a `0`-cochain is a
single element of `M`, so no continuity condition constrains it, and `ContinuousCohomology.zeroIso`
holds for every object of `TopRep ℤ G`. The comparison is nevertheless stated only for objects in
the image of `TauCeti.ofDiscreteModule`, as Layer 3 of the roadmap requires: a general object of
`TopRep ℤ G` need not be discrete, and the explicit complex is not a description of its cohomology.

## Main definitions

* `TauCeti.ContCohomology.H0ContinuousLinearEquivInvariants`: the explicit `H⁰(G, M) = M^G` is the
  invariant submodule of `TauCeti.ofDiscreteModule ℤ G M`, as an isomorphism of topological
  `ℤ`-modules.
* `TauCeti.ContCohomology.explicitH0IsoContinuousCohomology`: the comparison
  `H⁰(G, M) ≅ continuousCohomology 0 (ofDiscreteModule ℤ G M)` in `TopModuleCat ℤ`.

## Main results

* `TauCeti.ContCohomology.explicitH0Iso_map`: the comparison is natural in compatible pairs.
* `TauCeti.ContCohomology.explicitH0Iso_res`, `TauCeti.ContCohomology.explicitH0Iso_coeffMap`: its
  two named instances, carrying the explicit restriction and coefficient maps of degree zero to
  the canonical ones. The restriction square is typed by `TauCeti.res_ofDiscreteModule`, which
  identifies the restriction of a canonical object with the canonical object of the restriction.

## Roadmap

This implements the degree-zero part of the "comparison isomorphisms" milestone of Layer 3 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean`
fixes the name `explicitH0IsoContinuousCohomology`, together with the degree-zero rows of the
transport table in its §2. The names of the three transports carry the degree explicitly, because
`Suggested.lean` pins the unsuffixed `explicitIso_map`, `explicitIso_res` and `explicitIso_coeffMap`
to degree one. Degrees one and two of the comparison need the passage between the canonical
homogeneous cochains `C(G, C(G, …))` and functions on `Gⁿ`, hence the compact-open exponential law
and profiniteness of `G`, and are not in this file.

The sibling file `GroupCohomologyIso.lean` compares the same explicit model with Mathlib's
*discrete* `groupCohomology`; this file compares it with the *continuous* carrier, which is the
canonical object the roadmap fixes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  identification of the inhomogeneous description of continuous cohomology, which the explicit
  model here follows, with the homogeneous one computing the canonical object. The isomorphism
  built in this file is the degree-zero case of that identification.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u v

section Carriers

/-! The carriers are the invariants of a single element, so they need no inverses in `G` and no
topology on it. -/

variable (G : Type u) [Monoid G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]

/-- An element of a discrete `G`-module is invariant for the canonical object it names exactly
when it lies in the explicit `H⁰(G, M) = M^G`. -/
theorem mem_invariants_ofDiscreteModule_iff_mem_H0 (m : M) :
    m ∈ (ofDiscreteModule ℤ G M).ρ.invariants ↔ m ∈ H0 G M :=
  (ContRepresentation.mem_invariants m).trans (FixedPoints.mem_addSubgroup G M m).symm

/-- **Degree zero, on the carriers.** The explicit `H⁰(G, M) = M^G` is the invariant submodule of
the canonical object `TauCeti.ofDiscreteModule ℤ G M`, by the identity on underlying elements.
Both carry the subspace topology of the discrete `M`, so the identification is a homeomorphism as
well as an isomorphism of `ℤ`-modules. -/
def H0ContinuousLinearEquivInvariants :
    H0 G M ≃L[ℤ] (ofDiscreteModule ℤ G M).ρ.invariants where
  toFun m := ⟨m.1, (mem_invariants_ofDiscreteModule_iff_mem_H0 G M m.1).2 m.2⟩
  invFun m := ⟨m.1, (mem_invariants_ofDiscreteModule_iff_mem_H0 G M m.1).1 m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

@[simp]
theorem H0ContinuousLinearEquivInvariants_val (m : H0 G M) :
    (H0ContinuousLinearEquivInvariants G M m).1 = m.1 :=
  (rfl)

@[simp]
theorem H0ContinuousLinearEquivInvariants_symm_val
    (m : (ofDiscreteModule ℤ G M).ρ.invariants) :
    ((H0ContinuousLinearEquivInvariants G M).symm m).1 = m.1 :=
  (rfl)

end Carriers

section Comparison

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]

/-- **Layer 3, degree zero against the canonical object.** The explicit `H⁰(G, M)` is Mathlib's
`continuousCohomology 0` of the canonical object attached to `M`, as an isomorphism in
`TopModuleCat ℤ`.

Unlike the comparisons in degrees one and two this needs no profiniteness: it is
`ContinuousCohomology.zeroIso`, which holds over an arbitrary topological group, composed with the
identification of the invariants above. -/
noncomputable def explicitH0IsoContinuousCohomology :
    TopModuleCat.of ℤ (H0 G M) ≅ continuousCohomology 0 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso (H0ContinuousLinearEquivInvariants G M) ≪≫
    (ContinuousCohomology.zeroIso (ofDiscreteModule ℤ G M)).symm

-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
/-- The defining formula of the comparison: it is the inverse of `ContinuousCohomology.zeroIso`
applied to the invariant element itself. -/
theorem explicitH0IsoContinuousCohomology_hom_apply (m : H0 G M) :
    (explicitH0IsoContinuousCohomology G M).hom m =
      (ContinuousCohomology.zeroIso (ofDiscreteModule ℤ G M)).inv
        (H0ContinuousLinearEquivInvariants G M m) :=
  (rfl)

/-- The comparison sends an invariant element to its degree-zero class, in the sense of
`TauCeti.ContinuousCohomology.degreeZeroClass`. -/
theorem explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass (m : H0 G M) :
    (explicitH0IsoContinuousCohomology G M).hom m =
      TauCeti.ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ G M) m.1
        (fun g => (FixedPoints.mem_addSubgroup G M m.1).1 m.2 g) := by
  have hval : (ContinuousCohomology.zeroIso (ofDiscreteModule ℤ G M)).hom
      (TauCeti.ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ G M) m.1
        (fun g => (FixedPoints.mem_addSubgroup G M m.1).1 m.2 g)) =
      H0ContinuousLinearEquivInvariants G M m :=
    Subtype.ext ((TauCeti.ContinuousCohomology.coe_zeroIso_hom_degreeZeroClass
      (X := ofDiscreteModule ℤ G M) m.1
      (fun g => (FixedPoints.mem_addSubgroup G M m.1).1 m.2 g)).trans
      (H0ContinuousLinearEquivInvariants_val G M m).symm)
  rw [explicitH0IsoContinuousCohomology_hom_apply, ← hval, Iso.hom_inv_id_apply]

/-- The inverse of the comparison reads off the invariant element that
`ContinuousCohomology.zeroIso` assigns to a degree-zero class. -/
@[simp]
theorem coe_explicitH0IsoContinuousCohomology_inv_apply
    (y : continuousCohomology 0 (ofDiscreteModule ℤ G M)) :
    (((explicitH0IsoContinuousCohomology G M).inv y : H0 G M) : M) =
      ((ContinuousCohomology.zeroIso (ofDiscreteModule ℤ G M)).hom y).1 :=
  (rfl)

end Comparison

section Transport

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]

/-- **Layer 3, transport of the compatible-pair pullback in degree zero.** The comparison carries
the explicit pullback `TauCeti.ContCohomology.explicitMap0` along a compatible pair to Mathlib's
`ContinuousCohomology.map` along the same pair. The two transports below are its instances at the
inclusion of a subgroup and at the identity of the group. -/
theorem explicitH0Iso_map (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DiscreteTopology N] [DistribMulAction H N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : H0 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m => hf h m) 0
        ((explicitH0IsoContinuousCohomology G M).hom x) =
      (explicitH0IsoContinuousCohomology H N).hom
        (explicitMap0 G M (φ : H →* G) f hf x) := by
  rw [explicitH0IsoContinuousCohomology_hom_apply, explicitH0IsoContinuousCohomology_hom_apply]
  have hsq := congr($(TauCeti.ContinuousCohomology.zeroIso_inv_comp_map φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m => hf h m))
      (H0ContinuousLinearEquivInvariants G M x))
  simp only [ConcreteCategory.comp_apply] at hsq
  rw [hsq]
  refine congrArg _ (Subtype.ext ?_)
  simp only [TopRep.invariantsResMap, TopModuleCat.hom_ofHom,
    ContIntertwiningMap.mapInvariantsOfRes_apply, H0ContinuousLinearEquivInvariants_val]
  exact (ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap
      (fun h m => hf h m) x.1).trans (coe_explicitMap0 G M (φ : H →* G) f hf x).symm

/-- **Layer 3, transport of restriction in degree zero.** The comparison carries the explicit
inclusion `M^G ⊆ M^S` to the canonical restriction. The two sides land in the same object because
`TauCeti.res_ofDiscreteModule` identifies the restriction of the canonical object of `M` with the
canonical object of `M` over the subgroup. -/
theorem explicitH0Iso_res (S : Subgroup G) (x : H0 G M) :
    TauCeti.ContinuousCohomology.res S (ofDiscreteModule ℤ G M) 0
        ((explicitH0IsoContinuousCohomology G M).hom x) =
      (explicitH0IsoContinuousCohomology S M).hom (explicitRes0 G M S x) := by
  -- The coefficient datum of the restriction pair is the identity morphism, which the general
  -- transport square sees as the compatible pair on the identity map of `M`.
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype S : S →* G)
      (AddMonoidHom.id M).toIntLinearMap (fun _ _ => rfl) =
      𝟙 (TopRep.res (S.subtype : S →* G) (ofDiscreteModule ℤ G M)) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ => rfl
  rw [TauCeti.ContinuousCohomology.res_def, explicitRes0_eq_explicitMap0, ← hpair]
  exact explicitH0Iso_map G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
    (fun _ _ => rfl) x

/-- **Layer 3, transport of coefficient maps in degree zero.** The comparison carries the explicit
coefficient map to the canonical one attached to the same equivariant homomorphism; the canonical
coefficient morphism is the compatible pair at the identity, by
`TauCeti.ofDiscreteModulePair_id`. -/
theorem explicitH0Iso_coeffMap (N : Type u) [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DiscreteTopology N] [DistribMulAction G N] (f : M →+[G] N)
    (x : H0 G M) :
    TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m => map_smul f g m) 0
        ((explicitH0IsoContinuousCohomology G M).hom x) =
      (explicitH0IsoContinuousCohomology G N).hom (explicitCoeff0 G M f x) := by
  -- At the identity homomorphism the compatible pair is the coefficient morphism itself; this is
  -- `TauCeti.ofDiscreteModulePair_id`, restated at the coerced identity `ContinuousMonoidHom`.
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      f.toAddMonoidHom.toIntLinearMap (fun g m => map_smul f g m) =
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m => map_smul f g m :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ => rfl
  rw [TauCeti.ContinuousCohomology.coeffMap_def, explicitCoeff0_eq_explicitMap0, ← hpair]
  exact explicitH0Iso_map G M G N (ContinuousMonoidHom.id G) f.toAddMonoidHom
    (fun g m => map_smul f g m) x

end Transport

end TauCeti.ContCohomology
