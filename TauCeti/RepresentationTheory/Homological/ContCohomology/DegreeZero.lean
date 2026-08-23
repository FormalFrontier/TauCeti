/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Degree zero of continuous cohomology, and compatible pairs

Mathlib computes one degree of continuous cohomology: `ContinuousCohomology.zeroIso` identifies
`H⁰_cont(G, X)` with the invariants `X^G`. That identification is only usable once it is known to
transport the *maps*, and this file supplies exactly that. For a continuous homomorphism
`φ : H →ₜ* G` and a morphism `f : TopRep.res φ X ⟶ Y` of topological `H`-representations, the
square

```
H⁰_cont(G, X) --map φ f 0--> H⁰_cont(H, Y)
     |                             |
  zeroIso X                     zeroIso Y
     v                             v
    X^G  ----invariantsResMap---->  Y^H
```

commutes (`TauCeti.ContinuousCohomology.map_comp_zeroIso_hom`), and the three named instances of
`ContinuousCohomology.map` — coefficient maps, restriction and inflation — inherit it.

Two consequences are recorded because later layers use them rather than the square itself. First,
`H⁰_cont(G, -)` and the invariants functor are naturally isomorphic
(`TauCeti.ContinuousCohomology.zeroIsoNatIso`). Second, inflation is an isomorphism in degree zero
(`TauCeti.ContinuousCohomology.isIso_infl_zero`): `(X^N)^{G/N}` and `X^G` are canonically
isomorphic by explicit mutually inverse maps that preserve the underlying vector. Restriction is a
monomorphism in degree zero (`TauCeti.ContinuousCohomology.mono_res_zero`) because `X^G ⊆ X^S`.

The route to the square is the explicit evaluation formula
`TauCeti.ContinuousCohomology.coe_zeroIso_hom_π`: a `0`-cocycle of the homogeneous complex is an
invariant element of `C(G, X)`, and `zeroIso` reads off its value at `1`. Compatible-pair
functoriality precomposes with `φ`, and `φ 1 = 1`, which is the whole content.

This implements the "Degree 0" milestone of Layer 1, "the canonical carrier and its
functoriality", of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`,
together with the invariant-class constructor `degreeZeroClass` that the same layer names.

## Main definitions

* `TauCeti.ContinuousCohomology.degreeZeroClass`: the degree-zero class of an invariant vector.
* `TauCeti.ContinuousCohomology.zeroIsoNatIso`: `H⁰_cont(G, -) ≅ (-)^G` as functors.

## Main results

* `TauCeti.ContinuousCohomology.map_comp_zeroIso_hom`: compatible-pair functoriality commutes with
  `zeroIso`.
* `TauCeti.ContinuousCohomology.coeffMap_comp_zeroIso_hom`,
  `TauCeti.ContinuousCohomology.res_comp_zeroIso_hom`,
  `TauCeti.ContinuousCohomology.infl_comp_zeroIso_hom`: the same for the three named instances.
* `TauCeti.ContinuousCohomology.map_degreeZeroClass`: compatible-pair functoriality on classes of
  invariant vectors.
* `TauCeti.ContinuousCohomology.isIso_infl_zero`, `TauCeti.ContinuousCohomology.mono_res_zero`:
  the degree-zero edge of inflation-restriction.
-/

public section

open CategoryTheory

namespace TauCeti

namespace ContinuousCohomology

open _root_.ContinuousCohomology TopRep

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section Evaluation

/-- The comparison of the categorical cocycles with the concrete kernel is the inclusion of the
cocycles into the cochains. -/
private theorem cocycles₀Iso_hom_comp_kerι (X : TopRep R G) :
    (cocycles₀Iso X).hom ≫ TopModuleCat.kerι _ = (homogeneousCochains X).iCycles 0 := by
  rw [cocycles₀Iso, Limits.KernelFork.mapIsoOfIsLimit_hom]
  exact (Limits.KernelFork.mapOfIsLimit_ι _ (TopModuleCat.isLimitKer _) _).trans
    (Category.comp_id _)

/-- `cocycles₀Iso` read on elements: it does nothing to the underlying cochain. -/
private theorem coe_cocycles₀Iso_hom (X : TopRep R G) (σ : cocycles X 0) :
    ((cocycles₀Iso X).hom σ : (homogeneousCochains X).X 0) =
      (homogeneousCochains X).iCycles 0 σ :=
  congr($(cocycles₀Iso_hom_comp_kerι X) σ)

/-- In degree zero the cocycles already are the cohomology, so `zeroIso` may be read off on
cocycles. -/
private theorem π_comp_zeroIso_hom (X : TopRep R G) :
    π X 0 ≫ (zeroIso X).hom = (cocycles₀Iso X).hom ≫ (TopModuleCat.ofIso (d₀kerIso X)).hom := by
  simp [zeroIso]

/-- **The evaluation formula for `zeroIso`.** A homogeneous `0`-cochain of `X` is a `G`-invariant
element of `C(G, X)`; `zeroIso` sends the class of a `0`-cocycle to its value at `1`. Every
compatible-pair square below, including its coefficient, restriction, and inflation
specializations, follows from this formula together with `φ 1 = 1`. -/
theorem coe_zeroIso_hom_π (X : TopRep R G) (σ : cocycles X 0) :
    (((zeroIso X).hom (π X 0 σ)) : X.V) = ((homogeneousCochains X).iCycles 0 σ).1 1 := by
  have h := congr($(π_comp_zeroIso_hom X) σ)
  simp only [ConcreteCategory.comp_apply] at h
  rw [h, ← coe_cocycles₀Iso_hom]
  rfl

end Evaluation

section CompatiblePair

/-- **Degree zero is compatible with compatible pairs.** For a continuous homomorphism
`φ : H →ₜ* G` and a morphism `f : TopRep.res φ X ⟶ Y`, the map `ContinuousCohomology.map φ f 0`
becomes, under `ContinuousCohomology.zeroIso`, the map `X^G ⟶ Y^H` induced by `f`. This is what
makes Layer 3's low-degree comparisons checkable at `n = 0`. -/
@[reassoc]
theorem map_comp_zeroIso_hom (φ : H →ₜ* G) {X : TopRep R G} {Y : TopRep R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.map φ f 0 ≫ (zeroIso Y).hom =
      (zeroIso X).hom ≫ TopRep.invariantsResMap (φ : H →* G) f := by
  rw [← cancel_epi (π X 0), _root_.ContinuousCohomology.π_map_assoc]
  ext σ
  simp only [ConcreteCategory.comp_apply]
  have hcyc : (homogeneousCochains Y).iCycles 0 (cocyclesMap φ f 0 σ)
      = (cochainsMap φ f).f 0 ((homogeneousCochains X).iCycles 0 σ) :=
    congr($(HomologicalComplex.cyclesMap_i (cochainsMap φ f) 0) σ)
  rw [coe_zeroIso_hom_π Y, hcyc]
  simp only [TopRep.invariantsResMap, TopModuleCat.hom_ofHom,
    ContIntertwiningMap.mapInvariantsOfRes_apply]
  rw [coe_zeroIso_hom_π X, cochainsMap_f, resolutionMap_succ]
  set v := ((homogeneousCochains X).iCycles 0 σ : (homogeneousCochains X).X 0)
  -- `coind₁ResMap_apply` exposes that the cochain pullback precomposes with `φ`.
  simp only [TopRep.invariantsResMap, TopModuleCat.hom_ofHom, TopRep.hom_ofHom,
    resolutionMap_zero]
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply,
    ContRepresentation.coind₁ResMap_apply, map_one φ]

/-- Coefficient maps in degree zero are the maps induced on invariants. -/
@[reassoc]
theorem coeffMap_comp_zeroIso_hom {X Y : TopRep R G} (f : X ⟶ Y) :
    coeffMap f 0 ≫ (zeroIso Y).hom =
      (zeroIso X).hom ≫ (TopRep.invariantsFunctor R G).map f := by
  rw [coeffMap_def]
  exact map_comp_zeroIso_hom (ContinuousMonoidHom.id G) f

variable (R G) in
/-- **Degree-zero continuous cohomology is the invariants functor.** The functorial form of
`ContinuousCohomology.zeroIso`; its naturality is `coeffMap_comp_zeroIso_hom`. -/
noncomputable def zeroIsoNatIso :
    continuousCohomologyFunctor R G 0 ≅ TopRep.invariantsFunctor R G :=
  NatIso.ofComponents (fun X ↦ zeroIso X) fun f ↦ coeffMap_comp_zeroIso_hom f

/-- The components of `zeroIsoNatIso` are Mathlib's `ContinuousCohomology.zeroIso`. -/
@[simp]
theorem zeroIsoNatIso_hom_app (X : TopRep R G) :
    (zeroIsoNatIso R G).hom.app X = (zeroIso X).hom :=
  (rfl)

/-- The inverse components of `zeroIsoNatIso` are the inverses of Mathlib's
`ContinuousCohomology.zeroIso`. -/
@[simp]
theorem zeroIsoNatIso_inv_app (X : TopRep R G) :
    (zeroIsoNatIso R G).inv.app X = (zeroIso X).inv :=
  (rfl)

/-- Restriction in degree zero is the inclusion `X^G ⊆ X^S` of invariants. -/
@[reassoc]
theorem res_comp_zeroIso_hom (S : Subgroup G) (X : TopRep R G) :
    TauCeti.ContinuousCohomology.res S X 0 ≫
        (zeroIso (TopRep.res (S.subtype : S →* G) X)).hom =
      (zeroIso X).hom ≫
        TopRep.invariantsResMap (S.subtype : S →* G)
          (𝟙 (TopRep.res (S.subtype : S →* G) X)) := by
  rw [res_def]
  exact map_comp_zeroIso_hom (ContinuousMonoidHom.subgroupSubtype S)
    (𝟙 (TopRep.res (S.subtype : S →* G) X))

/-- Inflation in degree zero is the inclusion `(X^N)^{G/N} ⊆ X^G` of invariants. -/
@[reassoc]
theorem infl_comp_zeroIso_hom (N : Subgroup G) [N.Normal] (X : TopRep R G) :
    TauCeti.ContinuousCohomology.infl N X 0 ≫ (zeroIso X).hom =
      (zeroIso (TopRep.quotientToInvariants X N)).hom ≫
        TopRep.invariantsResMap (QuotientGroup.mk' N : G →* G ⧸ N)
          (TopRep.quotientToInvariantsι X N) := by
  rw [infl_def]
  exact map_comp_zeroIso_hom (ContinuousMonoidHom.quotientMk N)
    (TopRep.quotientToInvariantsι X N)

end CompatiblePair

section Class

variable {X : TopRep R G} {Y : TopRep R H}

/-- The inverse form of `map_comp_zeroIso_hom`, which is what acts on classes. -/
@[reassoc]
theorem zeroIso_inv_comp_map (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    (zeroIso X).inv ≫ _root_.ContinuousCohomology.map φ f 0 =
      TopRep.invariantsResMap (φ : H →* G) f ≫ (zeroIso Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact map_comp_zeroIso_hom φ f

/-- **The degree-zero class of an invariant vector.** Degree zero is the invariants, so an
invariant element of `X` has a continuous cohomology class; this is `zeroIso` read backwards on
elements. -/
noncomputable def degreeZeroClass (X : TopRep R G) (u : X.V) (hu : ∀ g : G, X.ρ g u = u) :
    continuousCohomology 0 X :=
  (zeroIso X).inv ⟨u, (ContRepresentation.mem_invariants u).2 hu⟩

/-- `zeroIso` recovers the invariant vector a degree-zero class was built from. -/
@[simp]
theorem coe_zeroIso_hom_degreeZeroClass (u : X.V) (hu : ∀ g : G, X.ρ g u = u) :
    (((zeroIso X).hom (degreeZeroClass X u hu)) : X.V) = u := by
  simp [degreeZeroClass]

/-- Every degree-zero class is the class of an invariant vector. -/
theorem exists_degreeZeroClass_eq (x : continuousCohomology 0 X) :
    ∃ (u : X.V) (hu : ∀ g : G, X.ρ g u = u), degreeZeroClass X u hu = x :=
  ⟨((zeroIso X).hom x : X.V), (ContRepresentation.mem_invariants _).1 ((zeroIso X).hom x).2,
    congr($((zeroIso X).hom_inv_id) x)⟩

/-- **Compatible-pair functoriality on the class of an invariant vector.** -/
@[simp]
theorem map_degreeZeroClass (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y) (u : X.V)
    (hu : ∀ g : G, X.ρ g u = u) :
    _root_.ContinuousCohomology.map φ f 0 (degreeZeroClass X u hu) =
      degreeZeroClass Y (f.hom u) fun h ↦ by
        rw [← f.hom.isIntertwining h u, ContRepresentation.restrict_apply_apply, hu] :=
  congr($(zeroIso_inv_comp_map φ f) ⟨u, (ContRepresentation.mem_invariants u).2 hu⟩)

end Class

section Edge

/-- **Restriction is a monomorphism in degree zero.** This is the degree-zero left edge of the
inflation-restriction sequence: `X^G ⊆ X^S`. -/
theorem mono_res_zero (S : Subgroup G) (X : TopRep R G) :
    Mono (TauCeti.ContinuousCohomology.res S X 0) := by
  have hinjective : Function.Injective (TopRep.invariantsResMap (S.subtype : S →* G)
      (𝟙 (TopRep.res (S.subtype : S →* G) X))) := by
    intro a b hab
    ext
    exact congrArg
      (fun w : (TopRep.res (S.subtype : S →* G) X).ρ.invariants ↦ (w : X.V)) hab
  have : Mono (TopRep.invariantsResMap (S.subtype : S →* G)
      (𝟙 (TopRep.res (S.subtype : S →* G) X))) :=
    ConcreteCategory.mono_of_injective _ hinjective
  exact mono_of_mono_fac (res_comp_zeroIso_hom S X)

variable (N : Subgroup G) [N.Normal] (X : TopRep R G)

/-- **Inflation is an isomorphism in degree zero**: `H⁰(G ⧸ N, X^N)`, `(X^N)^{G/N}`, and
`X^G` are canonically isomorphic, with the coefficient comparison preserving the underlying
vector. This is the degree-zero edge of the inflation-restriction sequence. -/
theorem isIso_infl_zero : IsIso (TauCeti.ContinuousCohomology.infl N X 0) := by
  have := TopRep.isIso_invariantsResMap_quotientToInvariantsι X N
  exact IsIso.of_isIso_fac_right (infl_comp_zeroIso_hom N X)

end Edge

end ContinuousCohomology

end TauCeti
