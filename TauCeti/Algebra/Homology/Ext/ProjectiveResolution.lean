/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# `Ext` out of a resolution whose `Hom`-complex has zero differentials

Mathlib computes `Extⁿ(X, Y)` from a projective resolution `R` of `X` as the `n`-th cohomology of
the complex `Hom(R, Y)`: `CategoryTheory.ProjectiveResolution.extMk` builds a class from a cocycle,
`extMk_surjective` says every class arises that way, and `extMk_eq_zero_iff` identifies the
coboundaries.

This file records the degenerate case of that computation. If the two differentials of `R`
adjacent to a degree `n + 1` die against `Y` -- that is, if `d (n + 2) (n + 1) ≫ f = 0` for every
`f : Rₙ₊₁ ⟶ Y` and `d (n + 1) n ≫ g = 0` for every `g : Rₙ ⟶ Y` -- then in that degree no cocycle
condition and no coboundary survives, and `Extⁿ⁺¹(X, Y)` *is* the term `Hom(Rₙ₊₁, Y)`, linearly
over the coefficient ring.

Degree `0` is deliberately excluded: there `Ext⁰(X, Y)` is `Hom(X, Y)`, which need not be
`Hom(R₀, Y)`.

## Main definitions

* `CategoryTheory.ProjectiveResolution.extLinearEquiv`: the linear equivalence
  `Hom(Rₙ₊₁, Y) ≃ₗ Extⁿ⁺¹(X, Y)`, sending `f` to its class.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5, for `Ext` computed from a
  projective resolution.
-/

public section

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Abelian

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [CommRing k] [Linear k C]
  [HasExt.{w} C] {X Y : C}

/-- If the two differentials of a projective resolution `R` of `X` adjacent to degree `n + 1`
become zero after applying `Hom(-, Y)`, then `Extⁿ⁺¹(X, Y)` is the degree `n + 1` term of that
`Hom`-complex, `k`-linearly. The class of `f` is `CategoryTheory.ProjectiveResolution.extMk f`. -/
noncomputable def extLinearEquiv (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0) :
    (R.complex.X (n + 1) ⟶ Y) ≃ₗ[k] Ext.{w} X Y (n + 1) := by
  refine LinearEquiv.ofBijective
    { toFun := fun f => R.extMk f (n + 2) rfl (h₁ f)
      map_add' := fun f g => (R.add_extMk f g (n + 2) rfl (h₁ f) (h₁ g)).symm
      map_smul' := fun c f => ?_ } ⟨?_, ?_⟩
  · dsimp
    rw [Ext.smul_eq_comp_mk₀, R.extMk_comp_mk₀]
    congr 1
    rw [Linear.comp_smul, Category.comp_id]
  · rw [← LinearMap.ker_eq_bot]
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_bot, LinearMap.coe_mk, AddHom.coe_mk]
    rw [R.extMk_eq_zero_iff f (n + 2) rfl (h₁ f) n rfl]
    exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ h₂ g, fun hf ↦ ⟨0, by simp [hf]⟩⟩
  · intro α
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 2) rfl
    exact ⟨f, rfl⟩

@[simp]
theorem extLinearEquiv_apply (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0)
    (f : R.complex.X (n + 1) ⟶ Y) :
    extLinearEquiv (k := k) R n h₁ h₂ f = R.extMk f (n + 2) rfl (h₁ f) :=
  (rfl)

end CategoryTheory.ProjectiveResolution
