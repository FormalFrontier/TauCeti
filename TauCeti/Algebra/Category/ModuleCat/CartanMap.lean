/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.CategoryTheory.GrothendieckGroup.ProjectiveResolution
public import TauCeti.LinearAlgebra.Dimension.Finite

/-!
# The Cartan map of a ring

For a ring `R`, the finitely generated `R`-modules and the finitely generated projective
`R`-modules are two full subcategories of `ModuleCat R`, each extension closed for the canonical
exact structure of the abelian category `ModuleCat R`. This file equips them with the induced
exact structures and constructs the homomorphism of exact Grothendieck groups

```text
c_R : K₀(proj R) ⟶ G₀(mod R)
```

induced by the inclusion of the first into the second. Following the standard notation,
`K₀(proj R)` is the exact `K₀` of the finitely generated projectives and `G₀(mod R)` is the exact
`K₀` of the finitely generated modules; the first structure is the split one, by
`TauCeti.finiteProjectiveModulesExactStructure_eq_split`, because a short exact sequence of
modules with projective quotient splits.

The two subcategories are essentially small — every finitely generated module is a quotient of
some `Rⁿ` — which is what makes their Grothendieck groups small types, and the Cartan map lives
in the same universe as `R`.

The main theorem is the module form of the resolution theorem: if every finitely generated
`R`-module admits a finite resolution by finitely generated projectives, then `c_R` is an
isomorphism, with inverse the alternating class of any such resolution. This is deduced from the
categorical resolution theorem `TauCeti.ExactStructure.resolutionEquiv` by factoring the Cartan
map through the modules admitting finite resolutions by finitely generated projectives. Over a
division ring the hypothesis holds for the trivial reason that every module is projective, which is
recorded as
`TauCeti.cartanEquivOfDivisionRing`.

Nothing here computes a Cartan matrix: that needs bases of the two groups, hence the
Krull--Schmidt hypotheses of a finite-dimensional algebra, and is left to the sequel. The
dictionary between the object property used here and the finite-dimensionality condition in which
that sequel is stated is `TauCeti.finite_iff_finiteDimensional`.

## Main definitions

* `TauCeti.finiteModules` and `TauCeti.finiteProjectiveModules`: the two object properties.
* `TauCeti.finiteModulesExactStructure`, `TauCeti.finiteProjectiveModulesExactStructure` and
  `TauCeti.finiteProjectiveDimensionExactStructure`: the exact structures induced on them, and on
  the modules admitting finite resolutions by finitely generated projectives, by the canonical
  exact structure of `ModuleCat R`.
* `TauCeti.cartanMap`: the Cartan map `K₀(proj R) ⟶ G₀(mod R)`.
* `TauCeti.moduleResolutionEquiv`: the resolution theorem in `ModuleCat R`, comparing `K₀(proj R)`
  with the Grothendieck group of the modules admitting finite resolutions by finitely generated
  projectives.
* `TauCeti.fromFiniteProjectiveDimension` and `TauCeti.toFiniteProjectiveDimension`: the two
  comparison maps between that group and `G₀(mod R)`.
* `TauCeti.moduleEulerClass` and `TauCeti.moduleEulerClassOf`: the alternating class in
  `K₀(proj R)` of a particular finite resolution by finitely generated projectives, and the class
  determined by any such resolution.
* `TauCeti.cartanInverse` and `TauCeti.cartanEquiv`: the inverse of the Cartan map and the
  resulting isomorphism, under the hypothesis that every finitely generated module has a finite
  resolution by finitely generated projectives.

## Main results

* `TauCeti.finiteModulesExactStructure_conflation_iff` and
  `TauCeti.finiteProjectiveModulesExactStructure_conflation_iff`, and
  `TauCeti.finiteProjectiveDimensionExactStructure_conflation_iff`: the conflations of the three
  structures are the short exact sequences of modules with terms in the subcategory.
* `TauCeti.finiteProjectiveModulesExactStructure_eq_split`: the exact structure of the finitely
  generated projectives is the split one.
* `TauCeti.cartanMap_apply`: the Cartan map factors through the Grothendieck group of the modules
  admitting finite resolutions by finitely generated projectives, by the resolution theorem.
* `TauCeti.moduleEulerClassOf_eq`: every finite projective resolution computes the module Euler
  class.
* `TauCeti.cartanMap_bijective`: the module form of the resolution theorem, and
  `TauCeti.cartanMap_bijective_of_divisionRing` for the division-ring instance of its hypothesis.
* `TauCeti.finite_iff_finiteDimensional`: over a finite-dimensional algebra the finitely generated
  modules are the finite-dimensional ones.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Sections 6
  and 7, for `K₀(proj R)`, `G₀(mod R)` and the resolution theorem.
* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the Cartan map of a finite-dimensional
  algebra.
* [The Tau Ceti Grothendieck groups, Cartan maps, and Euler forms roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/GrothendieckEulerForms/README.md),
  Layer 4, whose "two groups", "Cartan map and matrix" and "finite projective resolutions"
  bullets this file begins.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

variable (R : Type u) [Ring R]

/-! ### The finitely generated modules and the finitely generated projectives -/

/-- The object property of being a finitely generated module. -/
def finiteModules : ObjectProperty (ModuleCat.{u} R) := fun M => Module.Finite R M

/-- The object property of being a finitely generated projective module. -/
def finiteProjectiveModules : ObjectProperty (ModuleCat.{u} R) :=
  fun M => Module.Finite R M ∧ Module.Projective R M

variable {R}

@[simp] theorem finiteModules_iff {M : ModuleCat.{u} R} :
    finiteModules R M ↔ Module.Finite R M := Iff.rfl

@[simp] theorem finiteProjectiveModules_iff {M : ModuleCat.{u} R} :
    finiteProjectiveModules R M ↔ Module.Finite R M ∧ Module.Projective R M := Iff.rfl

variable (R)

theorem finiteProjectiveModules_le_finiteModules :
    finiteProjectiveModules R ≤ finiteModules R := fun _ h =>
  finiteModules_iff.mpr (finiteProjectiveModules_iff.mp h).1

instance : (finiteModules R).IsClosedUnderIsomorphisms where
  of_iso {M N} e h := by
    have : Module.Finite R M := finiteModules_iff.mp h
    exact finiteModules_iff.mpr (Module.Finite.equiv e.toLinearEquiv)

instance : (finiteProjectiveModules R).IsClosedUnderIsomorphisms where
  of_iso {M N} e h := by
    have : Module.Finite R M := (finiteProjectiveModules_iff.mp h).1
    have : Module.Projective R M := (finiteProjectiveModules_iff.mp h).2
    exact finiteProjectiveModules_iff.mpr
      ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv⟩

/-- The trivial module is finitely generated, being the image of `R`. -/
private theorem finite_pUnit : Module.Finite R (PUnit.{u + 1}) :=
  Module.Finite.of_surjective (0 : R →ₗ[R] PUnit) fun _ => ⟨0, Subsingleton.elim _ _⟩

instance : (finiteModules R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    finiteModules_iff.mpr (finite_pUnit R)⟩

instance : (finiteProjectiveModules R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    finiteProjectiveModules_iff.mpr ⟨finite_pUnit R, inferInstance⟩⟩

/-! ### Essential smallness -/

/-- **The finitely generated modules are essentially small**: each of them is a quotient of some
`Rⁿ`, and the quotients of the modules `Rⁿ` are indexed by the small type of pairs consisting of
an `n : ℕ` and a submodule of `Rⁿ`. -/
instance : ObjectProperty.EssentiallySmall.{u} (finiteModules R) where
  exists_small_le' := by
    refine ⟨ObjectProperty.ofObj (fun p : Σ n : ℕ, Submodule R (Fin n → R) =>
      ModuleCat.of R ((Fin p.1 → R) ⧸ p.2)), inferInstance, fun M hM => ?_⟩
    have : Module.Finite R M := finiteModules_iff.mp hM
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (M : Type u)
    exact ⟨ModuleCat.of R ((Fin n → R) ⧸ LinearMap.ker f),
      (ObjectProperty.ofObj_iff _ _).2 ⟨⟨n, LinearMap.ker f⟩, rfl⟩,
      ⟨(f.quotKerEquivOfSurjective hf).symm.toModuleIso⟩⟩

instance : ObjectProperty.EssentiallySmall.{u} (finiteProjectiveModules R) :=
  ObjectProperty.EssentiallySmall.of_le (finiteProjectiveModules_le_finiteModules R)

/-! ### The two exact structures -/

/-- **The finitely generated modules are extension closed**: the middle term of a short exact
sequence with finitely generated ends is finitely generated. -/
theorem isExtensionClosed_finiteModules :
    (ExactStructure.abelian (ModuleCat.{u} R)).IsExtensionClosed (finiteModules R) where
  prop_X₂ {S} hS h₁ h₃ := by
    rw [ExactStructure.abelian_conflation] at hS
    have : Module.Finite R S.X₁ := finiteModules_iff.mp h₁
    have : Module.Finite R S.X₃ := finiteModules_iff.mp h₃
    exact finiteModules_iff.mpr <| Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
      hS.moduleCat_surjective_g

/-- A finitely generated projective module is a projective object for the canonical exact
structure of `ModuleCat R`. -/
theorem finiteProjectiveModules_le_isProjective :
    finiteProjectiveModules R ≤ (ExactStructure.abelian (ModuleCat.{u} R)).isProjective := by
  intro M hM
  have : Module.Projective R M := (finiteProjectiveModules_iff.mp hM).2
  exact (ExactStructure.abelian_isProjective_iff M).2 inferInstance

instance : (finiteModules R).IsClosedUnderBinaryProducts :=
  (isExtensionClosed_finiteModules R).isClosedUnderBinaryProducts

instance : (finiteProjectiveModules R).IsClosedUnderBinaryProducts := by
  refine ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN => ?_
  have hproj := (ExactStructure.abelian_isProjective_iff (M ⊞ N)).1
    (ExactStructure.isProjective_biprod (finiteProjectiveModules_le_isProjective R M hM)
      (finiteProjectiveModules_le_isProjective R N hN))
  apply finiteProjectiveModules_iff.mpr
  exact ⟨finiteModules_iff.mp ((finiteModules R).prop_biprod_of_isClosedUnderBinaryProducts
    (finiteProjectiveModules_le_finiteModules R M hM)
    (finiteProjectiveModules_le_finiteModules R N hN)), inferInstance⟩

/-- **The exact structure of the finitely generated modules**: the short exact sequences of
`R`-modules all of whose terms are finitely generated. -/
noncomputable def finiteModulesExactStructure :
    ExactStructure (finiteModules R).FullSubcategory :=
  (ExactStructure.abelian (ModuleCat.{u} R)).fullSubcategory _ (isExtensionClosed_finiteModules R)

/-- **The exact structure of the finitely generated projective modules**, induced from the
canonical exact structure of `ModuleCat R`. It is the split one, by
`TauCeti.finiteProjectiveModulesExactStructure_eq_split`. -/
noncomputable def finiteProjectiveModulesExactStructure :
    ExactStructure (finiteProjectiveModules R).FullSubcategory :=
  (ExactStructure.abelian (ModuleCat.{u} R)).fullSubcategory _
    (ExactStructure.isExtensionClosed_of_le_isProjective
      (finiteProjectiveModules_le_isProjective R))

/-- **The Grothendieck group of the finitely generated projectives is the split one**: a short
exact sequence of modules whose quotient is projective splits, so the induced exact structure has
exactly the split conflations. -/
theorem finiteProjectiveModulesExactStructure_eq_split :
    finiteProjectiveModulesExactStructure R =
      ExactStructure.split (finiteProjectiveModules R).FullSubcategory :=
  ExactStructure.fullSubcategory_eq_split (finiteProjectiveModules_le_isProjective R)

/-- The conflations of finitely generated modules are the short exact sequences of `R`-modules
whose three terms are finitely generated. -/
@[simp] theorem finiteModulesExactStructure_conflation_iff
    (S : ShortComplex (finiteModules R).FullSubcategory) :
    (finiteModulesExactStructure R).Conflation S ↔ (S.map (finiteModules R).ι).ShortExact :=
  (ExactStructure.fullSubcategory_conflation_iff (E := ExactStructure.abelian (ModuleCat.{u} R))
    (P := finiteModules R) (isExtensionClosed_finiteModules R) S).trans
    (ExactStructure.abelian_conflation _)

/-- The conflations of finitely generated projective modules are the short exact sequences of
`R`-modules whose three terms are finitely generated projective; by
`TauCeti.finiteProjectiveModulesExactStructure_eq_split` these are exactly the split ones. -/
@[simp] theorem finiteProjectiveModulesExactStructure_conflation_iff
    (S : ShortComplex (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModulesExactStructure R).Conflation S ↔
      (S.map (finiteProjectiveModules R).ι).ShortExact :=
  (ExactStructure.fullSubcategory_conflation_iff (E := ExactStructure.abelian (ModuleCat.{u} R))
    (P := finiteProjectiveModules R) (ExactStructure.isExtensionClosed_of_le_isProjective
      (finiteProjectiveModules_le_isProjective R)) S).trans
    (ExactStructure.abelian_conflation _)

/-! ### The Cartan map -/

/-- **The Cartan map** `c_R : K₀(proj R) ⟶ G₀(mod R)`, induced by the inclusion of the finitely
generated projective modules into the finitely generated modules. The inclusion is
conflation-exact because a split short exact sequence of modules is a short exact sequence. -/
noncomputable def cartanMap :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) →+
      ExactK0.{u} (finiteModulesExactStructure R) :=
  ExactK0.map _ (ExactStructure.isConflationExact_ιOfLE _ (isExtensionClosed_finiteModules R)
    (finiteProjectiveModules_le_finiteModules R))

@[simp] theorem cartanMap_of {M : ModuleCat.{u} R} (hM : finiteProjectiveModules R M) :
    cartanMap R (ExactK0.of ⟨M, hM⟩) =
      ExactK0.of ⟨M, finiteModules_iff.mpr (finiteProjectiveModules_iff.mp hM).1⟩ :=
  ExactK0.map_of _ _ _

/-! ### The resolution theorem -/

/-- A module admitting a finite resolution by finitely generated projectives is itself finitely
generated: each step of the resolution presents it as a quotient of a finitely generated
module. -/
theorem admitsFiniteResolution_le_finiteModules :
    (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution (finiteProjectiveModules R) ≤
      finiteModules R := by
  intro M hM
  refine (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution_induction
    (finiteProjectiveModules R) (finiteProjectiveModules_le_finiteModules R)
    (fun {K Q X} hQ {i p zero} hconf _ => ?_) hM
  rw [ExactStructure.abelian_conflation] at hconf
  have : Module.Finite R Q := (finiteProjectiveModules_iff.mp hQ).1
  exact finiteModules_iff.mpr <|
    Module.Finite.of_surjective p.hom hconf.moduleCat_surjective_g

instance : ObjectProperty.EssentiallySmall.{u}
    ((ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R)) :=
  ObjectProperty.EssentiallySmall.of_le (admitsFiniteResolution_le_finiteModules R)

/-- **The exact structure of the modules admitting finite resolutions by finitely generated
projectives**: the short exact sequences of `R`-modules all of whose terms admit such a
resolution. -/
noncomputable def finiteProjectiveDimensionExactStructure :
    ExactStructure ((ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R)).FullSubcategory :=
  (ExactStructure.abelian (ModuleCat.{u} R)).fullSubcategory _
    (ExactStructure.isExtensionClosed_admitsFiniteResolution
      (finiteProjectiveModules_le_isProjective R))

/-- The conflations of modules admitting finite resolutions by finitely generated projectives are
the short exact sequences of modules whose three terms admit such resolutions. -/
@[simp] theorem finiteProjectiveDimensionExactStructure_conflation_iff
    (S : ShortComplex ((ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R)).FullSubcategory) :
    (finiteProjectiveDimensionExactStructure R).Conflation S ↔
      (S.map ((ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)).ι).ShortExact :=
  (ExactStructure.fullSubcategory_conflation_iff
    (E := ExactStructure.abelian (ModuleCat.{u} R))
    (P := (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R))
    (ExactStructure.isExtensionClosed_admitsFiniteResolution
      (finiteProjectiveModules_le_isProjective R)) S).trans
    (ExactStructure.abelian_conflation _)

/-- **The resolution theorem for modules admitting finite resolutions by finitely generated
projectives**: their exact `K₀` is the exact `K₀` of the finitely generated projective modules.
This is `TauCeti.ExactStructure.resolutionEquiv` in `ModuleCat R`; its inverse sends the class of a
module to the alternating class of any such resolution. -/
noncomputable def moduleResolutionEquiv :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) ≃+
      ExactK0.{u} (finiteProjectiveDimensionExactStructure R) :=
  ExactStructure.resolutionEquiv.{u, u, u + 1} (finiteProjectiveModules_le_isProjective R)

@[simp] theorem moduleResolutionEquiv_of {M : ModuleCat.{u} R}
    (hM : finiteProjectiveModules R M) :
    moduleResolutionEquiv R (ExactK0.of ⟨M, hM⟩) =
      ExactK0.of ⟨M, ExactStructure.le_admitsFiniteResolution _ _ M hM⟩ :=
  ExactStructure.resolutionEquiv_of.{u, u, u + 1} _ _

/-- **The alternating class of a finite projective resolution**, as an element of `K₀(proj R)`:
`TauCeti.ExactStructure.eulerClassOf` for the finitely generated projective modules. Any finite
resolution of `M` by finitely generated projectives computes it, by
`TauCeti.ExactStructure.eulerClassOf_eq`. -/
noncomputable def moduleEulerClassOf {M : ModuleCat.{u} R}
    (hM : (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R) M) :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  ExactStructure.eulerClassOf.{u, u, u + 1}
    (ExactStructure.isExtensionClosed_of_le_isProjective
      (finiteProjectiveModules_le_isProjective R)) hM

/-- The alternating class of a particular finite resolution by finitely generated projectives. -/
noncomputable def moduleEulerClass {M : ModuleCat.{u} R}
    (r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
      (finiteProjectiveModules R) M) :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  r.eulerClassFullSubcategory.{u, u, u + 1}
    (ExactStructure.isExtensionClosed_of_le_isProjective
      (finiteProjectiveModules_le_isProjective R))

/-- The alternating class of the length-zero resolution of a finitely generated projective module
is the class of that module. -/
@[simp] theorem moduleEulerClass_base {M : ModuleCat.{u} R}
    (hM : finiteProjectiveModules R M) :
    moduleEulerClass R (.base hM) = ExactK0.of ⟨M, hM⟩ := by
  change (ExactStructure.FiniteResolution.base hM).eulerClassFullSubcategory.{u, u, u + 1} _ = _
  exact ExactStructure.FiniteResolution.eulerClassFullSubcategory_base.{u, u, u + 1} _ hM

/-- Prepending a resolving term to a finite resolution subtracts the remaining alternating
class from the class of that term. -/
@[simp] theorem moduleEulerClass_step {K Q M : ModuleCat.{u} R}
    (hQ : finiteProjectiveModules R Q) (i : K ⟶ Q) (p : Q ⟶ M) (zero : i ≫ p = 0)
    (hp : (ExactStructure.abelian (ModuleCat.{u} R)).Conflation (ShortComplex.mk i p zero))
    (r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
      (finiteProjectiveModules R) K) :
    moduleEulerClass R (.step hQ i p zero hp r) =
      ExactK0.of ⟨Q, hQ⟩ - moduleEulerClass R r := by
  change
    (ExactStructure.FiniteResolution.step hQ i p zero hp r).eulerClassFullSubcategory.{u, u, u + 1}
        _ =
      ExactK0.of ⟨Q, hQ⟩ - r.eulerClassFullSubcategory.{u, u, u + 1} _
  exact ExactStructure.FiniteResolution.eulerClassFullSubcategory_step.{u, u, u + 1}
    _ hQ i p zero hp r

/-- Every finite resolution of a module by finitely generated projectives computes its alternating
class. -/
theorem moduleEulerClassOf_eq {M : ModuleCat.{u} R}
    (hM : (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R) M)
    (r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
      (finiteProjectiveModules R) M) :
    moduleEulerClassOf R hM = moduleEulerClass R r :=
  by
    change ExactStructure.eulerClassOf.{u, u, u + 1} _ hM =
      r.eulerClassFullSubcategory.{u, u, u + 1} _
    exact ExactStructure.eulerClassOf_eq.{u, u, u + 1}
      (finiteProjectiveModules_le_isProjective R) hM r

/-- A finitely generated projective module is its own resolution, so its alternating class is its
own class. -/
@[simp] theorem moduleEulerClassOf_of_prop {M : ModuleCat.{u} R}
    (hM : Module.Finite R M ∧ Module.Projective R M) :
    moduleEulerClassOf R (ExactStructure.le_admitsFiniteResolution _ _ M
      (finiteProjectiveModules_iff.mpr hM)) =
      ExactK0.of ⟨M, finiteProjectiveModules_iff.mpr hM⟩ :=
  ExactStructure.eulerClassOf_of_prop.{u, u, u + 1}
    (finiteProjectiveModules_le_isProjective R) (finiteProjectiveModules_iff.mpr hM)

@[simp] theorem moduleResolutionEquiv_symm_of {M : ModuleCat.{u} R}
    (hM : (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R) M) :
    (moduleResolutionEquiv R).symm (ExactK0.of ⟨M, hM⟩) = moduleEulerClassOf R hM :=
  ExactStructure.resolutionEquiv_symm_of.{u, u, u + 1} _ _

/-- The comparison map from the Grothendieck group of the modules admitting finite resolutions by
finitely generated projectives to `G₀(mod R)`. -/
noncomputable def fromFiniteProjectiveDimension :
    ExactK0.{u} (finiteProjectiveDimensionExactStructure R) →+
      ExactK0.{u} (finiteModulesExactStructure R) :=
  ExactK0.map _ (ExactStructure.isConflationExact_ιOfLE _ (isExtensionClosed_finiteModules R)
    (admitsFiniteResolution_le_finiteModules R))

@[simp] theorem fromFiniteProjectiveDimension_of {M : ModuleCat.{u} R}
    (hM : (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
      (finiteProjectiveModules R) M) :
    fromFiniteProjectiveDimension R (ExactK0.of ⟨M, hM⟩) =
      ExactK0.of ⟨M, admitsFiniteResolution_le_finiteModules R M hM⟩ :=
  ExactK0.map_of _ _ _

/-- **The Cartan map factors through the modules admitting finite resolutions by finitely
generated projectives**, where the resolution theorem `TauCeti.moduleResolutionEquiv` has already
made it an isomorphism. All that is left of the Cartan map is therefore the comparison of these
modules with all finitely generated modules. -/
theorem cartanMap_apply (x : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) :
    cartanMap R x = fromFiniteProjectiveDimension R (moduleResolutionEquiv R x) := by
  refine DFunLike.congr_fun (ExactK0.hom_ext (f := cartanMap R)
    (g := (fromFiniteProjectiveDimension R).comp
      (moduleResolutionEquiv R).toAddMonoidHom) fun M => ?_) x
  rcases M with ⟨M, hM⟩
  simp

section Inverse

variable (h : finiteModules R ≤
  (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution (finiteProjectiveModules R))

/-- Under the hypothesis that every finitely generated module admits a finite resolution by
finitely generated projectives, the comparison map from `G₀(mod R)` to the Grothendieck group of
the modules admitting such resolutions. -/
noncomputable def toFiniteProjectiveDimension :
    ExactK0.{u} (finiteModulesExactStructure R) →+
      ExactK0.{u} (finiteProjectiveDimensionExactStructure R) :=
  ExactK0.map _ (ExactStructure.isConflationExact_ιOfLE (isExtensionClosed_finiteModules R)
    (ExactStructure.isExtensionClosed_admitsFiniteResolution
      (finiteProjectiveModules_le_isProjective R)) h)

@[simp] theorem toFiniteProjectiveDimension_of {M : ModuleCat.{u} R} (hM : finiteModules R M) :
    toFiniteProjectiveDimension R h (ExactK0.of ⟨M, hM⟩) = ExactK0.of ⟨M, h M hM⟩ :=
  ExactK0.map_of _ _ _

/-- The two comparison maps with the modules admitting finite resolutions by finitely generated
projectives are inverse to one another, since under the hypothesis the two object properties
agree. -/
@[simp] theorem fromFiniteProjectiveDimension_toFiniteProjectiveDimension
    (y : ExactK0.{u} (finiteModulesExactStructure R)) :
    fromFiniteProjectiveDimension R (toFiniteProjectiveDimension R h y) = y := by
  refine DFunLike.congr_fun (ExactK0.hom_ext
    (f := (fromFiniteProjectiveDimension R).comp (toFiniteProjectiveDimension R h))
    (g := AddMonoidHom.id _) fun M => ?_) y
  rcases M with ⟨M, hM⟩
  simp

@[simp] theorem toFiniteProjectiveDimension_fromFiniteProjectiveDimension
    (y : ExactK0.{u} (finiteProjectiveDimensionExactStructure R)) :
    toFiniteProjectiveDimension R h (fromFiniteProjectiveDimension R y) = y := by
  refine DFunLike.congr_fun (ExactK0.hom_ext
    (f := (toFiniteProjectiveDimension R h).comp (fromFiniteProjectiveDimension R))
    (g := AddMonoidHom.id _) fun M => ?_) y
  rcases M with ⟨M, hM⟩
  simp

/-- The inverse of the Cartan map, under the hypothesis that every finitely generated module
admits a finite resolution by finitely generated projectives: the class of a module is sent to the
alternating class of any such resolution. -/
noncomputable def cartanInverse :
    ExactK0.{u} (finiteModulesExactStructure R) →+
      ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  (moduleResolutionEquiv R).symm.toAddMonoidHom.comp (toFiniteProjectiveDimension R h)

@[simp] theorem cartanInverse_of {M : ModuleCat.{u} R} (hM : finiteModules R M) :
    cartanInverse R h (ExactK0.of ⟨M, hM⟩) = moduleEulerClassOf R (h M hM) := by
  simp [cartanInverse]

/-- **The resolution theorem for modules.** If every finitely generated `R`-module admits a finite
resolution by finitely generated projective modules, then the Cartan map
`K₀(proj R) ⟶ G₀(mod R)` is an isomorphism; its inverse sends the class of a module to the
alternating class of any such resolution. -/
noncomputable def cartanEquiv :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) ≃+
      ExactK0.{u} (finiteModulesExactStructure R) where
  toFun := cartanMap R
  invFun := cartanInverse R h
  map_add' _ _ := map_add _ _ _
  left_inv x := by
    simp [cartanMap_apply, cartanInverse]
  right_inv y := by
    simp [cartanInverse, cartanMap_apply]

@[simp] theorem cartanEquiv_apply (x : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) :
    cartanEquiv R h x = cartanMap R x := (rfl)

/-- The inverse of the Cartan equivalence is the alternating-resolution homomorphism. -/
@[simp] theorem cartanEquiv_symm_apply (x : ExactK0.{u} (finiteModulesExactStructure R)) :
    (cartanEquiv R h).symm x = cartanInverse R h x := (rfl)

include h in
/-- **The Cartan map is an isomorphism** whenever every finitely generated `R`-module admits a
finite resolution by finitely generated projective modules; this is the bijectivity statement of
`TauCeti.cartanEquiv`. -/
theorem cartanMap_bijective : Function.Bijective (cartanMap R) :=
  (cartanEquiv R h).bijective

end Inverse

/-! ### The division-ring case -/

section DivisionRing

variable (K : Type u) [DivisionRing K]

/-- Over a division ring every module is projective, so the finitely generated projective modules
are exactly the finitely generated ones. -/
theorem finiteModules_le_finiteProjectiveModules :
    finiteModules K ≤ finiteProjectiveModules K := by
  intro M hM
  have : Module.Free K (M : Type u) := Module.Free.of_divisionRing K M
  exact finiteProjectiveModules_iff.mpr
    ⟨finiteModules_iff.mp hM, Module.Projective.of_free⟩

/-- Over a division ring every finitely generated module is its own finite projective resolution,
so the hypothesis of the resolution theorem holds. -/
theorem finiteModules_le_admitsFiniteResolution :
    finiteModules K ≤ (ExactStructure.abelian (ModuleCat.{u} K)).admitsFiniteResolution
      (finiteProjectiveModules K) :=
  (finiteModules_le_finiteProjectiveModules K).trans
    (ExactStructure.le_admitsFiniteResolution _ _)

/-- **The Cartan map of a division ring is an isomorphism**, because every finitely generated
module is already projective. -/
noncomputable def cartanEquivOfDivisionRing :
    ExactK0.{u} (finiteProjectiveModulesExactStructure K) ≃+
      ExactK0.{u} (finiteModulesExactStructure K) :=
  cartanEquiv K (finiteModules_le_admitsFiniteResolution K)

@[simp] theorem cartanEquivOfDivisionRing_apply
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure K)) :
    cartanEquivOfDivisionRing K x = cartanMap K x := by
  change cartanEquiv K (finiteModules_le_admitsFiniteResolution K) x = cartanMap K x
  exact cartanEquiv_apply K (finiteModules_le_admitsFiniteResolution K) x

/-- The inverse of the division-ring Cartan equivalence is the alternating-resolution map. -/
@[simp] theorem cartanEquivOfDivisionRing_symm_apply
    (x : ExactK0.{u} (finiteModulesExactStructure K)) :
    (cartanEquivOfDivisionRing K).symm x =
      cartanInverse K (finiteModules_le_admitsFiniteResolution K) x := by
  change (cartanEquiv K (finiteModules_le_admitsFiniteResolution K)).symm x =
    cartanInverse K (finiteModules_le_admitsFiniteResolution K) x
  exact cartanEquiv_symm_apply K (finiteModules_le_admitsFiniteResolution K) x

/-- **The Cartan map of a division ring is bijective**, with no hypothesis: over a division ring
every finitely generated module is projective, hence its own finite projective resolution. -/
theorem cartanMap_bijective_of_divisionRing : Function.Bijective (cartanMap K) :=
  cartanMap_bijective K (finiteModules_le_admitsFiniteResolution K)

end DivisionRing

end TauCeti
