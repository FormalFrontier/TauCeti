/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# The explicit model against the canonical object, in degrees zero and one

The explicit low-degree complex presents `H⁰(G, M)` as the invariant subgroup `M^G` of a discrete
`G`-module and `H¹(G, M)` as `Z¹/B¹`, while the canonical object is Mathlib's
`continuousCohomology n X` for `X` a topological representation. This file identifies the two in
degrees zero and one, for `X` the image `TauCeti.ofDiscreteModule ℤ G M` of `M` under the
coefficient dictionary, and transports the operations that exist in degree zero across the
identification.

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

Degree one is the first degree where the two descriptions genuinely differ. A homogeneous
`1`-cochain is a `G`-invariant element of `C(G, C(G, M))`, an inhomogeneous one a continuous
`c : G → M`, and the classical dictionary between them is `σ (g₀, g₁) = g₀ • c (g₀⁻¹ * g₁)` with
inverse `c g = σ (1, g)`. Passing from `c` to `σ` is `ContinuousMap.curry`, which carries no
hypothesis, and passing back is evaluation at `1`; so — unlike degree two, where the inverse of
currying is needed and hence `[LocallyCompactSpace G]` — the *additive* comparison
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` holds over an arbitrary topological
group. Compactness of `G` enters only to make the comparison an isomorphism in `TopModuleCat ℤ`:
it is what makes the canonical side discrete, by
`TauCeti.discreteTopology_continuousCohomology`. Total disconnectedness is not used in this degree.

The explicit side has to be *given* the discrete topology rather than left with the quotient of the
pointwise topology on `G → M`, which need not be discrete for an infinite profinite `G`; that is
what `TauCeti.ContCohomology.DiscreteH1` is for, and the categorical statement below is stated
against it.

## Main definitions

* `TauCeti.ContCohomology.H0ContinuousLinearEquivInvariants`: the explicit `H⁰(G, M) = M^G` is the
  invariant submodule of `TauCeti.ofDiscreteModule ℤ G M`, as an isomorphism of topological
  `ℤ`-modules.
* `TauCeti.ContCohomology.explicitH0IsoContinuousCohomology`: the comparison
  `H⁰(G, M) ≅ continuousCohomology 0 (ofDiscreteModule ℤ G M)` in `TopModuleCat ℤ`.
* `TauCeti.ContCohomology.homogeneousCochainEquiv₀`, `homogeneousCochainEquiv₁`: the chain-level
  dictionary in degrees zero and one, together with the readers
  `TauCeti.ContCohomology.homogeneousFun₀`, `homogeneousFun₁`, `homogeneousFun₂` that turn a
  homogeneous cochain into a function of one, two or three variables.
* `TauCeti.ContCohomology.homogeneousCocycleEquiv₁`: `Z¹(G, M)` is the kernel of the homogeneous
  degree-one differential.
* `TauCeti.ContCohomology.continuousCohomologyIsoCoker₁`: the quotient presentation of the
  canonical side, `continuousCohomology 1 X` as an honest cokernel `ker d ⧸ im d` in
  `TopModuleCat k`. It concerns the canonical side alone, so it is stated for an arbitrary
  `X : TopRep k G`, and only used at `X = ofDiscreteModule ℤ G M`.
* `TauCeti.ContCohomology.explicitH1AddEquivCoker`: the explicit `H¹(G, M) = Z¹/B¹` is that
  cokernel, the cocycle dictionary passed to the quotients.
* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology`,
  `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology`: the comparison in degree one, as an
  additive equivalence over an arbitrary topological group and as an isomorphism in
  `TopModuleCat ℤ` over a compact one.

## Main results

* `TauCeti.ContCohomology.explicitH0Iso_map`: the comparison is natural in compatible pairs.
* `TauCeti.ContCohomology.explicitH0Iso_res`, `TauCeti.ContCohomology.explicitH0Iso_coeffMap`: its
  two named instances, carrying the explicit restriction and coefficient maps of degree zero to
  the canonical ones. The restriction square is typed by `TauCeti.res_ofDiscreteModule`, which
  identifies the restriction of a canonical object with the canonical object of the restriction.
* `TauCeti.ContCohomology.homogeneousCochainEquiv₀_d`,
  `TauCeti.ContCohomology.homogeneousCochainEquiv₁_mem_ker_iff`: the dictionary is a map of
  complexes in the range of degrees that degree-one homology sees — it carries `d⁰` to the
  homogeneous differential and the `1`-cocycle condition to the vanishing of the homogeneous one.

## Roadmap

This implements the degree-zero and degree-one parts of the "comparison isomorphisms" milestone of
Layer 3 of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose
`Suggested.lean` fixes the names `explicitH0IsoContinuousCohomology`,
`explicitH1IsoContinuousCohomology` and `explicitH1AddEquivContinuousCohomology`, together with the
degree-zero rows of the transport table in its §2. The names of the three degree-zero transports
carry the degree explicitly, because `Suggested.lean` pins the unsuffixed `explicitIso_map`,
`explicitIso_res` and `explicitIso_coeffMap` to degree one. Degree two of the comparison needs the
passage from the canonical homogeneous cochains `C(G, C(G, C(G, M)))` back to functions on `G × G`,
hence the compact-open exponential law, and is not in this file; neither are the degree-one
transports, which are separate milestones of the same layer.

The sibling file `GroupCohomologyIso.lean` compares the same explicit model with Mathlib's
*discrete* `groupCohomology`; this file compares it with the *continuous* carrier, which is the
canonical object the roadmap fixes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  identification of the inhomogeneous description of continuous cohomology, which the explicit
  model here follows, with the homogeneous one computing the canonical object. The isomorphisms
  built in this file are the degree-zero and degree-one cases of that identification.
* `Mathlib/RepresentationTheory/Homological/ContCohomology/LowDegree.lean` by Richard Hill,
  Andrew Yang and Edison Xie: the formal precedent. Its `ContinuousCohomology.d₀kerIso` and
  `ContinuousCohomology.zeroIso` compute the canonical side in degree zero; the degree-zero
  comparison below is built directly from `zeroIso`, and the degree-one one follows the same
  shape, replacing `zeroIso` by the quotient presentation
  `TauCeti.ContCohomology.continuousCohomologyIsoCoker₁`.
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

section HomogeneousCochains

/-! ### The homogeneous cochains in coordinates

A homogeneous `n`-cochain of `TauCeti.ofDiscreteModule ℤ G M` is a `G`-invariant element of the
`(n+1)`-fold iterated function space `C(G, C(G, …, M))`. The three readers below turn such a
cochain into a plain function of `n + 1` variables, which is the form in which the dictionary with
the inhomogeneous complex is stated. They are separate declarations rather than one `n`-ary reader
because Mathlib's canonical complex is built by iterating `C(G, -)` and not by currying, so there
is no uniform `Gⁿ⁺¹ → M` reader without the compact-open exponential law. -/

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]

/-- The function underlying a homogeneous `0`-cochain. -/
def homogeneousFun₀ (f : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 0) : G → M :=
  fun x => f.1 x

/-- The function of two variables underlying a homogeneous `1`-cochain. -/
def homogeneousFun₁ (σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 1) : G → G → M :=
  fun x y => σ.1 x y

/-- The function of three variables underlying a homogeneous `2`-cochain. -/
def homogeneousFun₂ (σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 2) :
    G → G → G → M :=
  fun x y z => σ.1 x y z

variable {G M}

/-- The homogeneity of a `0`-cochain. The coinduced action on `C(G, M)` is
`(g • f) x = g • f (g⁻¹ * x)` by `ContRepresentation.coind₁_apply_apply`, so evaluating the
invariance `f.2 g` at `x` gives exactly this. -/
theorem homogeneousFun₀_invariant (f : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 0)
    (g x : G) : homogeneousFun₀ G M f x = g • homogeneousFun₀ G M f (g⁻¹ * x) :=
  (congrArg (fun F => F x) (f.2 g)).symm

/-- The homogeneity of a `1`-cochain, `σ (x, y) = g • σ (g⁻¹ * x, g⁻¹ * y)`, in the form obtained
by evaluating the invariance at a single group element. -/
theorem homogeneousFun₁_invariant (σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 1)
    (g x y : G) :
    homogeneousFun₁ G M σ x y = g • homogeneousFun₁ G M σ (g⁻¹ * x) (g⁻¹ * y) :=
  (congrArg (fun F => F x y) (σ.2 g)).symm

/-- A homogeneous `1`-cochain is determined by its underlying function. -/
theorem homogeneousFun₁_injective : Function.Injective (homogeneousFun₁ G M) := fun _ _ h =>
  Subtype.ext (ContinuousMap.ext fun x => ContinuousMap.ext fun y => congrFun (congrFun h x) y)

/-- A homogeneous `2`-cochain vanishes exactly when its underlying function does. -/
theorem homogeneousFun₂_eq_zero_iff
    (σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 2) :
    σ = 0 ↔ ∀ x y z : G, homogeneousFun₂ G M σ x y z = 0 :=
  ⟨fun h _ _ _ => by rw [h]; rfl,
   fun h => Subtype.ext (ContinuousMap.ext fun x => ContinuousMap.ext fun y =>
     ContinuousMap.ext fun z => h x y z)⟩

/-- The homogeneous differential `C⁰ → C¹` is `(d f) (x, y) = f y - f x`. -/
theorem homogeneousFun₁_d (f : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 0)
    (x y : G) :
    homogeneousFun₁ G M (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 0 1).hom f) x y
      = homogeneousFun₀ G M f y - homogeneousFun₀ G M f x := by
  simp only [homogeneousFun₁, homogeneousFun₀]
  rw [TopRep.homogeneousCochains.d_apply]
  rfl

/-- The homogeneous differential `C¹ → C²` is
`(d σ) (x, y, z) = σ (y, z) - σ (x, z) + σ (x, y)`. -/
theorem homogeneousFun₂_d (σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 1)
    (x y z : G) :
    homogeneousFun₂ G M (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom σ) x y z
      = homogeneousFun₁ G M σ y z - homogeneousFun₁ G M σ x z + homogeneousFun₁ G M σ x y := by
  -- the inductive definition of Mathlib's differential produces the bracketing `a - (b - c)`
  have h : homogeneousFun₂ G M
      (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom σ) x y z
      = homogeneousFun₁ G M σ y z - (homogeneousFun₁ G M σ x z - homogeneousFun₁ G M σ x y) := by
    simp only [homogeneousFun₂, homogeneousFun₁]
    rw [TopRep.homogeneousCochains.d_apply]
    rfl
  rw [h]
  abel

end HomogeneousCochains

section ChainLevel

/-! ### The chain-level dictionary in degrees zero and one -/

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **Degree zero of the chain-level dictionary.** A homogeneous `0`-cochain is `x ↦ x • m` for a
unique `m ∈ M`, namely its value at `1`. -/
noncomputable def homogeneousCochainEquiv₀ :
    M ≃+ (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 0 where
  toFun m :=
    ⟨(⟨fun x : G => x • m, continuous_id.smul continuous_const⟩ : C(G, M)),
      fun g => ContinuousMap.ext fun x => by
        -- `change` spells out the coinduced action on `C(G, M)`, which holds definitionally by
        -- `ContRepresentation.coind₁_apply_apply`; there is no rewrite for it at this iterate
        change (g • ((g⁻¹ * x) • m) : M) = x • m
        rw [smul_smul, mul_inv_cancel_left]⟩
  invFun f := homogeneousFun₀ G M f 1
  left_inv m := one_smul G m
  right_inv f := Subtype.ext (ContinuousMap.ext fun x => by
    -- as above, `change` is what exposes the value of the constructed cochain at `x`
    change (x • homogeneousFun₀ G M f 1 : M) = homogeneousFun₀ G M f x
    rw [homogeneousFun₀_invariant f x x, inv_mul_cancel])
  map_add' m m' := Subtype.ext (ContinuousMap.ext fun x => smul_add x m m')

-- Not `@[simp]`: the cochain type `(TopRep.homogeneousCochains _).X 0` is itself reducible by
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so this left-hand side is not in simp
-- normal form. It is used through explicit rewrites.
/-- The function underlying the homogeneous `0`-cochain attached to `m` is `x ↦ x • m`. -/
theorem homogeneousFun₀_homogeneousCochainEquiv₀ (m : M) (x : G) :
    homogeneousFun₀ G M (homogeneousCochainEquiv₀ G M m) x = x • m := (rfl)

/-- **Degree one of the chain-level dictionary.** The continuous inhomogeneous `1`-cochains are the
homogeneous ones, by `σ (x, y) = x • c (x⁻¹ * y)` with inverse `c g = σ (1, g)`.

The forward direction is `ContinuousMap.curry`, which needs no hypothesis on `G`; this is why
degree one, unlike degree two, does not need local compactness. -/
noncomputable def homogeneousCochainEquiv₁ :
    C1 G M ≃+ (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 1 where
  toFun c :=
    ⟨(ContinuousMap.curry ⟨fun p : G × G => p.1 • (c : G → M) (p.1⁻¹ * p.2),
        continuous_fst.smul ((mem_C1_iff.1 c.2).comp
          (continuous_fst.inv.mul continuous_snd))⟩ : C(G, C(G, M))),
      fun g => ContinuousMap.ext fun x => ContinuousMap.ext fun y => by
        -- `change` spells out the twice-iterated coinduced action together with the value of the
        -- curried map; both hold definitionally and neither has a rewrite at this iterate
        change (g • ((g⁻¹ * x) • (c : G → M) ((g⁻¹ * x)⁻¹ * (g⁻¹ * y))) : M) =
          x • (c : G → M) (x⁻¹ * y)
        rw [smul_smul]
        group⟩
  invFun σ := ⟨homogeneousFun₁ G M σ 1, mem_C1_iff.2 ((σ.1 : C(G, C(G, M))) 1).continuous⟩
  left_inv c := Subtype.ext (funext fun g => by
    -- as above
    change (1 : G) • (c : G → M) ((1 : G)⁻¹ * g) = (c : G → M) g
    rw [one_smul, inv_one, one_mul])
  right_inv σ := Subtype.ext (ContinuousMap.ext fun x => ContinuousMap.ext fun y => by
    -- as above
    change x • homogeneousFun₁ G M σ 1 (x⁻¹ * y) = homogeneousFun₁ G M σ x y
    rw [homogeneousFun₁_invariant σ x x y, inv_mul_cancel])
  map_add' c c' := Subtype.ext (ContinuousMap.ext fun x => ContinuousMap.ext fun y =>
    (smul_add x ((c : G → M) (x⁻¹ * y)) ((c' : G → M) (x⁻¹ * y)) : _))

-- Not `@[simp]`, for the reason recorded at
-- `TauCeti.ContCohomology.homogeneousFun₀_homogeneousCochainEquiv₀`.
/-- The function of two variables underlying the homogeneous `1`-cochain attached to `c` is
`(x, y) ↦ x • c (x⁻¹ * y)`. -/
theorem homogeneousFun₁_homogeneousCochainEquiv₁ (c : C1 G M) (x y : G) :
    homogeneousFun₁ G M (homogeneousCochainEquiv₁ G M c) x y = x • (c : G → M) (x⁻¹ * y) :=
  (rfl)

-- Not `@[simp]`, for the reason recorded at
-- `TauCeti.ContCohomology.homogeneousFun₀_homogeneousCochainEquiv₀`.
/-- The continuous `1`-cochain attached to a homogeneous one is `g ↦ σ (1, g)`. -/
theorem coe_homogeneousCochainEquiv₁_symm
    (σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 1) (g : G) :
    (((homogeneousCochainEquiv₁ G M).symm σ : C1 G M) : G → M) g = homogeneousFun₁ G M σ 1 g :=
  (rfl)

/-- **The dictionary is a chain map in degree zero.** It carries the explicit `d⁰` to the
homogeneous differential `C⁰ → C¹`. -/
theorem homogeneousCochainEquiv₀_d (m : M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 0 1).hom
        (homogeneousCochainEquiv₀ G M m)
      = homogeneousCochainEquiv₁ G M ⟨d0 G M m, mem_C1_iff.2 (continuous_d0_apply m)⟩ :=
  homogeneousFun₁_injective (funext fun x => funext fun y => by
    rw [homogeneousFun₁_d, homogeneousFun₁_homogeneousCochainEquiv₁,
      homogeneousFun₀_homogeneousCochainEquiv₀, homogeneousFun₀_homogeneousCochainEquiv₀]
    simp only [d0_apply, smul_sub, smul_smul, mul_inv_cancel_left])

/-- **The dictionary is a chain map in degree one.** A continuous `1`-cochain is a `1`-cocycle
exactly when the homogeneous cochain attached to it is killed by the homogeneous differential. -/
theorem homogeneousCochainEquiv₁_mem_ker_iff (c : C1 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom
        (homogeneousCochainEquiv₁ G M c) = 0 ↔ (c : G → M) ∈ Z1 G M := by
  rw [homogeneousFun₂_eq_zero_iff, mem_Z1_iff]
  refine ⟨fun h => ⟨mem_C1_iff.1 c.2, d1_apply_eq_zero_iff.1 (funext fun q => ?_)⟩,
    fun h x y z => ?_⟩
  · -- the inhomogeneous cocycle identity at `(g, h)` is the homogeneous one at `(1, g, g * h)`
    obtain ⟨g, h'⟩ := q
    have hg := h 1 g (g * h')
    rw [homogeneousFun₂_d] at hg
    simp only [homogeneousFun₁_homogeneousCochainEquiv₁, inv_one, one_mul, one_smul,
      inv_mul_cancel_left] at hg
    simpa only [d1_apply, Pi.zero_apply] using hg
  · -- conversely the homogeneous identity at `(x, y, z)` is the inhomogeneous one at
    -- `(x⁻¹ * y, y⁻¹ * z)`, translated by `x`
    rw [homogeneousFun₂_d]
    simp only [homogeneousFun₁_homogeneousCochainEquiv₁]
    have hcy : y = x * (x⁻¹ * y) := by group
    have hkey : (c : G → M) (x⁻¹ * z) =
        (x⁻¹ * y) • (c : G → M) (y⁻¹ * z) + (c : G → M) (x⁻¹ * y) := by
      have hcocycle := h.2 (x⁻¹ * y) (y⁻¹ * z)
      rwa [show (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z by group] at hcocycle
    rw [hkey, smul_add, smul_smul]
    nth_rewrite 1 [hcy]
    rw [mul_inv_cancel_left]
    abel

end ChainLevel

section CanonicalDegreeOne

/-! ### The canonical side in degree one, as a quotient

Nothing here mentions the explicit model, or even discreteness: for an arbitrary topological
representation, degree-one continuous cohomology is the homology of `C⁰ → C¹ → C²`, hence an
honest quotient of the homogeneous `1`-cocycles. -/

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G)

/-- The short complex `C⁰ → C¹ → C²` of homogeneous cochains whose homology is
`continuousCohomology 1`. It is spelled with the explicit indices `0, 1, 2` rather than through
`HomologicalComplex.sc`, whose neighbours are computed by `ComplexShape.prev` and `next`. -/
noncomputable abbrev homogeneousSc₁ : ShortComplex (TopModuleCat k) :=
  ShortComplex.mk ((TopRep.homogeneousCochains X).d 0 1)
    ((TopRep.homogeneousCochains X).d 1 2)
    ((TopRep.homogeneousCochains X).d_comp_d 0 1 2)

/-- **The quotient presentation of the canonical side.** Continuous cohomology in degree one is the
cokernel, in `TopModuleCat k`, of the degree-zero differential corestricted to the homogeneous
`1`-cocycles: the honest `ker d ⧸ im d`, with the subspace topology on the numerator and the
quotient topology on the whole. -/
noncomputable def continuousCohomologyIsoCoker₁ :
    continuousCohomology 1 X
      ≅ TopModuleCat.coker (homogeneousSc₁ X).topModuleCatLeftHomologyData.f' :=
  (TopRep.homogeneousCochains X).homologyIsoSc' 0 1 2 (by simp) (by simp)
    ≪≫ (homogeneousSc₁ X).topModuleCatHomologyIso

/-- The additive equivalence underlying the inverse of the quotient presentation is its `inv`.

Mathlib's `CategoryTheory.Iso.toContinuousLinearEquiv` is built from `Iso.hom` and has no
application lemma, so this records the reading once, in the form the comparison below rewrites
with. -/
theorem continuousCohomologyIsoCoker₁_symm_toAddEquiv_apply
    (y : TopModuleCat.coker (homogeneousSc₁ X).topModuleCatLeftHomologyData.f') :
    (continuousCohomologyIsoCoker₁ X).symm.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv y
      = (continuousCohomologyIsoCoker₁ X).inv y := (rfl)

end CanonicalDegreeOne

section DegreeOne

/-! ### The comparison in degree one

The dictionary with the explicit side needs continuity of the action, because
`TauCeti.ContCohomology.homogeneousCochainEquiv₁` sends `c` to the *continuous* map
`(x, y) ↦ x • c (x⁻¹ * y)`. -/

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- The explicit continuous `1`-cocycles `Z¹(G, M)` are the kernel of the homogeneous degree-one
differential. -/
noncomputable def homogeneousCocycleEquiv₁ :
    Z1 G M ≃+ TopModuleCat.ker (homogeneousSc₁ (ofDiscreteModule ℤ G M)).g where
  toFun z := ⟨homogeneousCochainEquiv₁ G M ⟨(z : G → M), Z1_le_C1 G M z.2⟩,
    (homogeneousCochainEquiv₁_mem_ker_iff G M _).2 z.2⟩
  invFun τ := ⟨(((homogeneousCochainEquiv₁ G M).symm τ.1 : C1 G M) : G → M),
    (homogeneousCochainEquiv₁_mem_ker_iff G M _).1
      ((congrArg (fun σ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X 1 =>
          ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom σ)
        ((homogeneousCochainEquiv₁ G M).apply_symm_apply τ.1)).trans
        (LinearMap.mem_ker.1 τ.2))⟩
  left_inv z := by
    refine Subtype.ext ?_
    -- `dsimp only` peels off the two anonymous constructors so that the round trip is visible
    dsimp only
    rw [(homogeneousCochainEquiv₁ G M).symm_apply_apply]
  right_inv τ := by
    refine Subtype.ext ?_
    exact (homogeneousCochainEquiv₁ G M).apply_symm_apply τ.1
  map_add' _ _ := by
    refine Subtype.ext ?_
    -- after `map_add` the two sides differ only in the membership proofs carried by `C¹`
    rw [Submodule.coe_add, ← map_add]
    congr 1

/-- The homogeneous `1`-cocycle attached to a continuous one is its image under the chain-level
dictionary.

Not `@[simp]`: the homogeneous cochain types are spelled through
`CategoryTheory.Functor.mapHomologicalComplex_obj_X`, which `simp` reduces further, so this
left-hand side is not in simp normal form. The same obstruction keeps the rules below that bind a
homogeneous cochain off `@[simp]`. -/
theorem coe_homogeneousCocycleEquiv₁ (z : Z1 G M) :
    (homogeneousCocycleEquiv₁ G M z).1
      = homogeneousCochainEquiv₁ G M ⟨(z : G → M), Z1_le_C1 G M z.2⟩ := (rfl)

/-- The continuous `1`-cocycle attached to a homogeneous one is the underlying function of its
image under the inverse of the chain-level dictionary.

Not `@[simp]`, for the reason recorded at
`TauCeti.ContCohomology.coe_homogeneousCocycleEquiv₁`. -/
theorem coe_homogeneousCocycleEquiv₁_symm
    (τ : TopModuleCat.ker (homogeneousSc₁ (ofDiscreteModule ℤ G M)).g) :
    (((homogeneousCocycleEquiv₁ G M).symm τ : Z1 G M) : G → M)
      = (((homogeneousCochainEquiv₁ G M).symm τ.1 : C1 G M) : G → M) := (rfl)

/-- The cocycle dictionary carries the explicit `1`-coboundaries onto the image of the homogeneous
degree-zero differential. This is the statement that makes the two quotients agree. -/
theorem map_homogeneousCocycleEquiv₁_B1 :
    AddSubgroup.map (homogeneousCocycleEquiv₁ G M).toAddMonoidHom
        ((B1 G M).addSubgroupOf (Z1 G M))
      = (LinearMap.range (homogeneousSc₁
          (ofDiscreteModule ℤ G M)).topModuleCatLeftHomologyData.f'.hom.toLinearMap).toAddSubgroup
          := by
  ext τ
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_addSubgroupOf,
    Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · intro hτ
    obtain ⟨m, hm⟩ := mem_B1_iff.1 hτ
    refine ⟨homogeneousCochainEquiv₀ G M m, Subtype.ext ?_⟩
    rw [ShortComplex.coe_topModuleCatLeftHomologyData_f']
    have h1 : (⟨d0 G M m, mem_C1_iff.2 (continuous_d0_apply m)⟩ : C1 G M)
        = (homogeneousCochainEquiv₁ G M).symm τ.1 := by
      refine Subtype.ext ?_
      rw [← coe_homogeneousCocycleEquiv₁_symm]
      exact funext fun g => (d0_apply m g).trans (hm g)
    rw [homogeneousCochainEquiv₀_d, h1, AddEquiv.apply_symm_apply]
  · rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ : ∃ m, homogeneousCochainEquiv₀ G M m = w :=
      ⟨(homogeneousCochainEquiv₀ G M).symm w, (homogeneousCochainEquiv₀ G M).apply_symm_apply w⟩
    have hw' : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 0 1).hom
        (homogeneousCochainEquiv₀ G M m) = τ.1 := by
      rw [← ShortComplex.coe_topModuleCatLeftHomologyData_f'
        (S := homogeneousSc₁ (ofDiscreteModule ℤ G M)), hw]
    have h3 : (homogeneousCochainEquiv₁ G M).symm τ.1
        = ⟨d0 G M m, mem_C1_iff.2 (continuous_d0_apply m)⟩ := by
      rw [← hw', homogeneousCochainEquiv₀_d, AddEquiv.symm_apply_apply]
    rw [coe_homogeneousCocycleEquiv₁_symm, h3]
    exact d0_mem_B1 m

/-- **The two quotients agree.** The explicit `H¹(G, M) = Z¹/B¹` is the cokernel that presents
the canonical side, the cocycle dictionary passed to the quotients by
`TauCeti.ContCohomology.map_homogeneousCocycleEquiv₁_B1`.

Its codomain is spelled as the cokernel `TopModuleCat.coker`, a quotient by a submodule, where
`QuotientAddGroup.congr` produces the quotient by the underlying additive subgroup; the two are the
same type, and giving the equivalence this type once here is what keeps the composite below free of
a coercion between them.

The comparison with `continuousCohomology 1` is this followed by
`TauCeti.ContCohomology.continuousCohomologyIsoCoker₁`. -/
noncomputable def explicitH1AddEquivCoker :
    H1 G M ≃+
      TopModuleCat.coker
        (homogeneousSc₁ (ofDiscreteModule ℤ G M)).topModuleCatLeftHomologyData.f' :=
  QuotientAddGroup.congr _ _ (homogeneousCocycleEquiv₁ G M) (map_homogeneousCocycleEquiv₁_B1 G M)

/-- The class of a continuous `1`-cocycle goes to the class of the homogeneous `1`-cocycle attached
to it.

This is the value of `QuotientAddGroup.congr` on a class, whose multiplicative form
`QuotientGroup.congr_mk` carries no `@[to_additive]`, read through the `Submodule.Quotient.mk` of
the cokernel; both readings are definitional.

Not `@[simp]`, for the reason recorded at
`TauCeti.ContCohomology.coe_homogeneousCocycleEquiv₁`: the cokernel this lands in is spelled
through the ambient cochain types, which reduce further, so this left-hand side is not in simp
normal form. -/
theorem explicitH1AddEquivCoker_mk (z : Z1 G M) :
    explicitH1AddEquivCoker G M (z : H1 G M)
      = Submodule.Quotient.mk (homogeneousCocycleEquiv₁ G M z) := (rfl)

/-- **Layer 3, degree one against the canonical object, additively.** The explicit `H¹(G, M)` is
Mathlib's `continuousCohomology 1` of the canonical object attached to `M`.

Only the two hypotheses that make the two sides exist are needed: `G` is an arbitrary topological
group and `M` a discrete `G`-module with a continuous action. Compactness of `G` is what upgrades
this to an isomorphism of *topological* modules, in
`TauCeti.ContCohomology.explicitH1IsoContinuousCohomology`. -/
noncomputable def explicitH1AddEquivContinuousCohomology :
    H1 G M ≃+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  (explicitH1AddEquivCoker G M).trans
    (continuousCohomologyIsoCoker₁
      (ofDiscreteModule ℤ G M)).symm.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv

/-- The comparison sends the class of a continuous `1`-cocycle to the class of the homogeneous
`1`-cocycle attached to it. `TauCeti.ContCohomology.H1pi` is `QuotientAddGroup.mk'`, which `simp`
unfolds by `QuotientAddGroup.mk'_apply`, so the class is spelled here as the coercion, which is the
form the rest of the explicit `H¹` API — `TauCeti.ContCohomology.H1pi_eq_iff` and
`TauCeti.ContCohomology.H1pi_eq_zero_iff` — is stated in. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_mk (z : Z1 G M) :
    explicitH1AddEquivContinuousCohomology G M (z : H1 G M)
      = (continuousCohomologyIsoCoker₁ (ofDiscreteModule ℤ G M)).inv
          (Submodule.Quotient.mk (homogeneousCocycleEquiv₁ G M z)) := by
  rw [explicitH1AddEquivContinuousCohomology, AddEquiv.trans_apply, explicitH1AddEquivCoker_mk,
    continuousCohomologyIsoCoker₁_symm_toAddEquiv_apply]

/-- The inverse comparison sends the class of a homogeneous `1`-cocycle to the class of the
continuous one attached to it.

Not `@[simp]`, for the reason recorded at
`TauCeti.ContCohomology.coe_homogeneousCocycleEquiv₁`: the homogeneous `1`-cocycle `τ` is
typed through the ambient cochain types, which reduce further, so this left-hand side is not in
simp normal form. The forward rule above has no such binder and is `@[simp]`. -/
theorem explicitH1AddEquivContinuousCohomology_symm_mk
    (τ : TopModuleCat.ker (homogeneousSc₁ (ofDiscreteModule ℤ G M)).g) :
    (explicitH1AddEquivContinuousCohomology G M).symm
        ((continuousCohomologyIsoCoker₁ (ofDiscreteModule ℤ G M)).inv (Submodule.Quotient.mk τ))
      = (((homogeneousCocycleEquiv₁ G M).symm τ : Z1 G M) : H1 G M) := by
  rw [AddEquiv.symm_apply_eq, explicitH1AddEquivContinuousCohomology_mk,
    (homogeneousCocycleEquiv₁ G M).apply_symm_apply]

/-- **Degree one, as topological `ℤ`-modules.** Both sides are discrete — the explicit side by
construction, the canonical side by `TauCeti.discreteTopology_continuousCohomology` — so the
additive comparison is automatically continuous in both directions. -/
noncomputable def explicitH1ContinuousLinearEquiv [CompactSpace G] :
    DiscreteH1 G M ≃L[ℤ] continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  haveI : DiscreteTopology (ofDiscreteModule ℤ G M).V := ‹DiscreteTopology M›
  { toLinearEquiv :=
      { __ := (discreteH1Equiv G M).trans (explicitH1AddEquivContinuousCohomology G M)
        -- an additive map into a `ℤ`-module object is `ℤ`-linear
        map_smul' := fun n a => by
          simpa using map_intCast_smul
            ((discreteH1Equiv G M).trans
              (explicitH1AddEquivContinuousCohomology G M)).toAddMonoidHom ℤ ℤ n a }
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- **Layer 3, degree one against the canonical object.** The explicit `H¹(G, M)`, carried by the
discrete object `TauCeti.ContCohomology.DiscreteH1`, is Mathlib's `continuousCohomology 1` of the
canonical object attached to `M`, as an isomorphism in `TopModuleCat ℤ`.

Compactness of `G` is used, and only used, to know that the canonical side is discrete. Total
disconnectedness is not needed in this degree: the chain-level dictionary rests on
`ContinuousMap.curry`, which carries no hypothesis, whereas degree two needs its inverse. -/
noncomputable def explicitH1IsoContinuousCohomology [CompactSpace G] :
    TopModuleCat.of ℤ (DiscreteH1 G M) ≅ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso (explicitH1ContinuousLinearEquiv G M)

/-- The comparison in `TopModuleCat ℤ` is the additive comparison. -/
@[simp] theorem explicitH1IsoContinuousCohomology_hom_apply [CompactSpace G] (x : DiscreteH1 G M) :
    (explicitH1IsoContinuousCohomology G M).hom x
      = explicitH1AddEquivContinuousCohomology G M (discreteH1Equiv G M x) := by
  simp only [explicitH1IsoContinuousCohomology, TopModuleCat.ofIso, TopModuleCat.hom_ofHom,
    ContinuousLinearEquiv.coe_coe]
  exact AddEquiv.trans_apply (discreteH1Equiv G M) (explicitH1AddEquivContinuousCohomology G M) x

/-- The inverse of the comparison in `TopModuleCat ℤ` is the inverse of the additive comparison,
read back into `TauCeti.ContCohomology.DiscreteH1`. -/
@[simp] theorem explicitH1IsoContinuousCohomology_inv_apply [CompactSpace G]
    (y : continuousCohomology 1 (ofDiscreteModule ℤ G M)) :
    (explicitH1IsoContinuousCohomology G M).inv y
      = (discreteH1Equiv G M).symm ((explicitH1AddEquivContinuousCohomology G M).symm y) := by
  simp only [explicitH1IsoContinuousCohomology, TopModuleCat.ofIso, TopModuleCat.hom_ofHom,
    ContinuousLinearEquiv.coe_coe]
  exact AddEquiv.symm_trans_apply (discreteH1Equiv G M)
    (explicitH1AddEquivContinuousCohomology G M) y

/-- The inverse comparison in `TopModuleCat ℤ` sends the class of a homogeneous `1`-cocycle to the
class, in `TauCeti.ContCohomology.DiscreteH1`, of the continuous one attached to it.

Not `@[simp]`, for the reason recorded at
`TauCeti.ContCohomology.coe_homogeneousCocycleEquiv₁`: the homogeneous `1`-cocycle `τ` is typed
through the ambient cochain types, which reduce further, so this left-hand side is not in simp
normal form. It is the composite of the `@[simp]` rule
`TauCeti.ContCohomology.explicitH1IsoContinuousCohomology_inv_apply` with
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_symm_mk`, which is what a consumer
rewrites with. -/
theorem explicitH1IsoContinuousCohomology_inv_mk [CompactSpace G]
    (τ : TopModuleCat.ker (homogeneousSc₁ (ofDiscreteModule ℤ G M)).g) :
    (explicitH1IsoContinuousCohomology G M).inv
        ((continuousCohomologyIsoCoker₁ (ofDiscreteModule ℤ G M)).inv (Submodule.Quotient.mk τ))
      = (discreteH1Equiv G M).symm
          (((homogeneousCocycleEquiv₁ G M).symm τ : Z1 G M) : H1 G M) := by
  rw [explicitH1IsoContinuousCohomology_inv_apply,
    explicitH1AddEquivContinuousCohomology_symm_mk]

end DegreeOne

end TauCeti.ContCohomology
