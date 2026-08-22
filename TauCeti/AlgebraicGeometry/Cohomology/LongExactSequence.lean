/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# The long exact cohomology sequence of a short exact sequence of sheaves of modules

`TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` defines the cohomology `Hⁿ(X, M)` of a sheaf
of modules on a scheme. This file adds the long exact sequence attached to a short exact
sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules,

`0 ⟶ H⁰(X, M₁) ⟶ H⁰(X, M₂) ⟶ H⁰(X, M₃) ⟶ H¹(X, M₁) ⟶ H¹(X, M₂) ⟶ ⋯`

together with its consequences for global sections. Where
`TauCeti/AlgebraicGeometry/Cohomology/MayerVietoris.lean` varies the open subset, this file
varies the coefficients.

## Main declarations

* `Scheme.Modules.cohomologyMap`, a morphism of sheaves of modules as a map on cohomology;
* `Scheme.Modules.cohomologyδ`, the connecting map `Hⁿ⁰(X, M₃) ⟶ Hⁿ¹(X, M₁)`, together with the
  three exactness statements `Scheme.Modules.exact_cohomologyMap_cohomologyMap`,
  `Scheme.Modules.exact_cohomologyMap_cohomologyδ` and
  `Scheme.Modules.exact_cohomologyδ_cohomologyMap`;
* `Scheme.Modules.cohomologyMap_injective`, the injectivity in degree zero at which the sequence
  starts, and `Scheme.Modules.cohomologyMap_surjective`, the surjectivity it gives when the next
  cohomology group of `M₁` vanishes;
* `Scheme.Modules.subsingleton_cohomology_X₂`, `Scheme.Modules.subsingleton_cohomology_X₃` and
  `Scheme.Modules.subsingleton_cohomology_X₁`, the vanishing consequences;
* `Scheme.Modules.exact_sections` and `Scheme.Modules.sections_injective`: global sections are
  left exact, and `Scheme.Modules.sections_surjective`: they are exact on the right as soon as
  `H¹(X, M₁)` vanishes. This last statement is the form in which the sequence is normally used;
* `Scheme.Modules.cohomologyδ_naturality`, the naturality of the connecting map in the short
  exact sequence, and the linearity it gives: `Scheme.Modules.cohomologyδLinear` over the ring
  of global functions and `Scheme.Modules.cohomologyδBaseLinear` over the base ring of a scheme
  over a commutative ring. The maps induced by morphisms of sheaves are already linear, so this
  makes the whole long exact sequence one of modules; a dimension count in it needs that.

Additivity of the Euler characteristic, and with it Riemann-Roch, rest on this sequence, so it
is Layer B infrastructure for `TauCetiRoadmap/JacobianChallenge/README.md`. No formalization is
vendored: the sequence itself is
`TauCeti/CategoryTheory/Sites/SheafCohomology/LongExactSequence.lean`, exactness of forgetting
the module structures is `TauCeti/AlgebraicGeometry/Modules/Sheaf.lean`, and the comparison of
degree-zero cohomology with global sections is `Scheme.Modules.cohomologyZeroEquiv`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of sheaves of modules on a scheme, as a map on degree-`n` cohomology. -/
def cohomologyMap {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    Cohomology M n →+ Cohomology N n :=
  CategoryTheory.Sheaf.H.map ((toSheaf X).map f) n

@[simp]
lemma cohomologyFunctor_map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (cohomologyFunctor X n).map f = AddCommGrpCat.ofHom (cohomologyMap f n) :=
  by
    rw [cohomologyMap.eq_def]
    rfl

/-- Under the identification of degree-zero cohomology with global sections, the map induced on
cohomology by a morphism of sheaves of modules is the map induced on global sections. -/
@[simp]
lemma cohomologyZeroEquiv_cohomologyMap {M N : X.Modules} (f : M ⟶ N) (x : Cohomology M 0) :
    cohomologyZeroEquiv N (cohomologyMap f 0 x) = f.app ⊤ (cohomologyZeroEquiv M x) :=
  by
    have hx : (cohomologyFunctor X 0).map f x = cohomologyMap f 0 x := by
      exact congrArg
        (fun g : (cohomologyFunctor X 0).obj M ⟶ (cohomologyFunctor X 0).obj N ↦ g x)
        (cohomologyFunctor_map f 0)
    rw [← hx]
    exact cohomologyZeroEquiv_naturality f x

private lemma sections_ladder {M N : X.Modules} (f : M ⟶ N) :
    (f.app ⊤).hom.comp (cohomologyZeroEquiv M) =
      (cohomologyZeroEquiv N : Cohomology N 0 →+ Γ(N, ⊤)).comp (cohomologyMap f 0) := by
  ext x
  exact (cohomologyZeroEquiv_cohomologyMap f x).symm

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

/-- The connecting map `Hⁿ⁰(X, M₃) →+ Hⁿ¹(X, M₁)` of the long exact cohomology sequence of a
short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules. -/
def cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →+ Cohomology S.X₁ n₁ :=
  TauCeti.CategoryTheory.Sheaf.H.δ (shortExact_map_toSheaf hS) n₀ n₁ h

/-- The long exact cohomology sequence is exact at `Hⁿ(X, M₂)`. -/
theorem exact_cohomologyMap_cohomologyMap (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) :=
  TauCeti.CategoryTheory.Sheaf.H.exact_map_map (shortExact_map_toSheaf hS) n

/-- The long exact cohomology sequence is exact at `Hⁿ⁰(X, M₃)`. -/
theorem exact_cohomologyMap_cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) :=
  TauCeti.CategoryTheory.Sheaf.H.exact_map_δ (shortExact_map_toSheaf hS) n₀ n₁ h

/-- The long exact cohomology sequence is exact at `Hⁿ¹(X, M₁)`. -/
theorem exact_cohomologyδ_cohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) :=
  TauCeti.CategoryTheory.Sheaf.H.exact_δ_map (shortExact_map_toSheaf hS) n₀ n₁ h

omit hS in
/-- A monomorphism of sheaves of modules is injective on cohomology in degree zero. -/
theorem cohomologyMap_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (cohomologyMap f 0) :=
  TauCeti.CategoryTheory.Sheaf.H.map_injective ((toSheaf X).map f)

/-- If `Hⁿ¹(X, M₁)` vanishes, then `Hⁿ⁰(X, M₂) →+ Hⁿ⁰(X, M₃)` is surjective. -/
theorem cohomologyMap_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (Cohomology S.X₁ n₁)) :
    Function.Surjective (cohomologyMap S.g n₀) :=
  TauCeti.CategoryTheory.Sheaf.H.map_g_surjective (shortExact_map_toSheaf hS) n₀ n₁ h h₁

/-- If `Hⁿ(X, M₁)` and `Hⁿ(X, M₃)` vanish, then so does `Hⁿ(X, M₂)`. -/
theorem subsingleton_cohomology_X₂ (n : ℕ) (h₁ : Subsingleton (Cohomology S.X₁ n))
    (h₃ : Subsingleton (Cohomology S.X₃ n)) : Subsingleton (Cohomology S.X₂ n) :=
  TauCeti.CategoryTheory.Sheaf.H.subsingleton_X₂ (shortExact_map_toSheaf hS) n h₁ h₃

/-- If `Hⁿ⁰(X, M₂)` and `Hⁿ¹(X, M₁)` vanish, then so does `Hⁿ⁰(X, M₃)`. -/
theorem subsingleton_cohomology_X₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (Cohomology S.X₂ n₀)) (h₁ : Subsingleton (Cohomology S.X₁ n₁)) :
    Subsingleton (Cohomology S.X₃ n₀) :=
  TauCeti.CategoryTheory.Sheaf.H.subsingleton_X₃ (shortExact_map_toSheaf hS) n₀ n₁ h h₂ h₁

/-- If `Hⁿ⁰(X, M₃)` and `Hⁿ¹(X, M₂)` vanish, then so does `Hⁿ¹(X, M₁)`. -/
theorem subsingleton_cohomology_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₃ : Subsingleton (Cohomology S.X₃ n₀)) (h₂ : Subsingleton (Cohomology S.X₂ n₁)) :
    Subsingleton (Cohomology S.X₁ n₁) :=
  TauCeti.CategoryTheory.Sheaf.H.subsingleton_X₁ (shortExact_map_toSheaf hS) n₀ n₁ h h₃ h₂

/-- Global sections are left exact: the sections of `M₁` are exactly the sections of `M₂` that
die in `M₃`. -/
theorem exact_sections : Function.Exact ⇑(S.f.app ⊤) ⇑(S.g.app ⊤) :=
  Function.Exact.of_ladder_addEquiv_of_exact (cohomologyZeroEquiv S.X₁)
    (cohomologyZeroEquiv S.X₂) (cohomologyZeroEquiv S.X₃) (sections_ladder S.f)
    (sections_ladder S.g) (exact_cohomologyMap_cohomologyMap hS 0)

omit hS in
/-- Global sections are left exact: a monomorphism of sheaves of modules is injective on global
sections. -/
theorem sections_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective ⇑(f.app ⊤) := by
  intro a b hab
  apply (cohomologyZeroEquiv M).symm.injective
  apply cohomologyMap_injective f
  apply (cohomologyZeroEquiv N).injective
  rw [cohomologyZeroEquiv_cohomologyMap, cohomologyZeroEquiv_cohomologyMap,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hab]

/-- If `H¹(X, M₁)` vanishes, then every global section of `M₃` lifts to a global section of `M₂`.
This is the form in which the long exact sequence is normally used. -/
theorem sections_surjective (h₁ : Subsingleton (Cohomology S.X₁ 1)) :
    Function.Surjective ⇑(S.g.app ⊤) := by
  intro y
  obtain ⟨x, hx⟩ := cohomologyMap_surjective hS 0 1 rfl h₁
    ((cohomologyZeroEquiv S.X₃).symm y)
  refine ⟨cohomologyZeroEquiv S.X₂ x, ?_⟩
  rw [← cohomologyZeroEquiv_cohomologyMap, hx, AddEquiv.apply_symm_apply]

omit hS in
/-- Multiplication by a global function on cohomology is the map induced by multiplication by
that function on the coefficient sheaf. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMap_globalSectionsSmul_apply (M : X.Modules)
    (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    cohomologyMap (globalSectionsSmul M r) i x = r • x := by
  rw [cohomology_smul, cohomologyFunctor_map]
  rfl

omit hS in
/-- The connecting map is natural in the short exact sequence: a morphism `φ : S₁ ⟶ S₂` of short
exact sequences of sheaves of modules makes the square formed by the two connecting maps and the
maps induced by `φ.τ₃` and `φ.τ₁` commute. -/
theorem cohomologyδ_naturality {S₁ S₂ : ShortComplex X.Modules} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Cohomology S₁.X₃ n₀) :
    cohomologyMap φ.τ₁ n₁ (cohomologyδ h₁ n₀ n₁ h x) =
      cohomologyδ h₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) :=
  TauCeti.CategoryTheory.Sheaf.H.δ_naturality (shortExact_map_toSheaf h₁)
    (shortExact_map_toSheaf h₂) ((toSheaf X).mapShortComplex.map φ) n₀ n₁ h x

/-- The connecting map of the long exact cohomology sequence is linear over the ring of global
functions. -/
def cohomologyδLinear (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →ₗ[Γ(X, ⊤)] Cohomology S.X₁ n₁ where
  toFun := cohomologyδ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' r x := by
    -- `Module.compHom` exposes its action definitionally, so the goal is the naturality of the
    -- connecting map for multiplication by `r` on all three terms.
    change cohomologyδ hS n₀ n₁ h (r • x) = r • cohomologyδ hS n₀ n₁ h x
    rw [← cohomologyMap_globalSectionsSmul_apply, ← cohomologyMap_globalSectionsSmul_apply]
    -- Multiplication by `r` on all three terms is an endomorphism of the short complex.
    exact (cohomologyδ_naturality hS hS
      { τ₁ := globalSectionsSmul S.X₁ r
        τ₂ := globalSectionsSmul S.X₂ r
        τ₃ := globalSectionsSmul S.X₃ r
        comm₁₂ := globalSectionsSmul_naturality S.f r
        comm₂₃ := globalSectionsSmul_naturality S.g r } n₀ n₁ h x).symm

@[simp]
lemma cohomologyδLinear_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Cohomology S.X₃ n₀) :
    cohomologyδLinear hS n₀ n₁ h x = cohomologyδ hS n₀ n₁ h x :=
  (rfl)

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
  {S : ShortComplex X.Modules}

omit hS in
/-- For a scheme over a commutative ring, the connecting map of the long exact cohomology
sequence is linear over the base ring. -/
def cohomologyδBaseLinear (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →ₗ[R] Cohomology S.X₁ n₁ where
  toFun := cohomologyδ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' r x := by
    rw [base_smul_cohomology]
    -- As for `cohomologyMapBaseLinear`, normalize the restricted action to the action of global
    -- functions and apply the linearity already proved there.
    change cohomologyδLinear hS n₀ n₁ h ((baseRingToGlobalSections R X r) • x) =
      (baseRingToGlobalSections R X r) • cohomologyδLinear hS n₀ n₁ h x
    exact (cohomologyδLinear hS n₀ n₁ h).map_smul _ x

omit hS in
@[simp]
lemma cohomologyδBaseLinear_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Cohomology S.X₃ n₀) :
    cohomologyδBaseLinear R X hS n₀ n₁ h x = cohomologyδ hS n₀ n₁ h x :=
  (rfl)

end Base

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
