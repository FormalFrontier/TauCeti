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

This file records the degenerate case of that computation. When *every* differential of `R` dies
against `Y` — that is, when `Hom(R, Y)` has zero differentials, which is what minimality of `R`
relative to `Y` amounts to — no cocycle condition and no coboundary survives, and `Extⁿ⁺¹(X, Y)`
*is* the term `Hom(Rₙ₊₁, Y)`, linearly over the coefficient ring.

Degree `0` is deliberately excluded: there `Ext⁰(X, Y)` is `Hom(X, Y)`, which is a proper subobject
of `Hom(R₀, Y)` unless `R₀ ⟶ X` is an isomorphism.

## Main definitions

* `TauCeti.extLinearEquivOfProjectiveResolution`: the linear equivalence
  `Hom(Rₙ₊₁, Y) ≃ₗ Extⁿ⁺¹(X, Y)`, sending `f` to its class.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5, for `Ext` computed from a
  projective resolution.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [CommRing k] [Linear k C]
  [HasExt.{w} C] {X Y : C}

/-- If every differential of a projective resolution `R` of `X` becomes zero after applying
`Hom(-, Y)`, then `Extⁿ⁺¹(X, Y)` is the degree `n + 1` term of that `Hom`-complex, `k`-linearly.
The class of `f` is `CategoryTheory.ProjectiveResolution.extMk f`. -/
noncomputable def extLinearEquivOfProjectiveResolution (R : ProjectiveResolution X)
    (hR : ∀ (p q : ℕ) (f : R.complex.X q ⟶ Y), R.complex.d p q ≫ f = 0) (n : ℕ) :
    (R.complex.X (n + 1) ⟶ Y) ≃ₗ[k] Ext.{w} X Y (n + 1) := by
  refine LinearEquiv.ofBijective
    { toFun := fun f => R.extMk f (n + 2) rfl (hR _ _ f)
      map_add' := fun f g => (R.add_extMk f g (n + 2) rfl (hR _ _ f) (hR _ _ g)).symm
      map_smul' := fun c f => ?_ } ⟨?_, ?_⟩
  · dsimp
    rw [Ext.smul_eq_comp_mk₀, R.extMk_comp_mk₀]
    congr 1
    rw [Linear.comp_smul, Category.comp_id]
  · rw [← LinearMap.ker_eq_bot]
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_bot, LinearMap.coe_mk, AddHom.coe_mk]
    rw [R.extMk_eq_zero_iff f (n + 2) rfl (hR _ _ f) n rfl]
    exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ hR _ _ g, fun hf ↦ ⟨0, by simp [hf]⟩⟩
  · intro α
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 2) rfl
    exact ⟨f, rfl⟩

@[simp]
theorem extLinearEquivOfProjectiveResolution_apply (R : ProjectiveResolution X)
    (hR : ∀ (p q : ℕ) (f : R.complex.X q ⟶ Y), R.complex.d p q ≫ f = 0) (n : ℕ)
    (f : R.complex.X (n + 1) ⟶ Y) :
    extLinearEquivOfProjectiveResolution (k := k) R hR n f =
      R.extMk f (n + 2) rfl (hR _ _ f) :=
  (rfl)

end TauCeti
