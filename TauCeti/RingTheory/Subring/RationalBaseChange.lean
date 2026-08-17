/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Extending the scalars of a subring of a rational algebra

Let `A` be a `ℚ`-algebra and `R` a subring of `A`. Because `R` is a ring and not a `ℚ`-subalgebra,
it can be a genuine lattice: an integral structure whose rational span is all of `A`. This file
builds the comparison map

```text
ratBaseChange R : ℚ ⊗[ℤ] R →ₐ[ℚ] A,     q ⊗ₜ r ↦ q • r
```

records that its range is exactly the `ℚ`-span of `R`, and proves that it is always injective.
Consequently it is an isomorphism exactly when that span is everything, which is what it means for
`R` to be a `ℤ`-form of `A`.

Injectivity holds with no hypothesis on `R` and is the reason the file exists: every element of
`ℚ ⊗[ℤ] M`, for any additive group `M`, has a common denominator, so it is a single elementary
tensor `(n : ℚ)⁻¹ ⊗ₜ m` rather than a sum of them. That normal form,
`TauCeti.exists_tmul_inv_natCast`, is proved first and is purely module-theoretic. It also turns
the spanning hypothesis into the concrete statement `Subring.exists_natCast_smul_mem`, that every
element of `A` is carried into `R` by some nonzero natural number.

## Main definitions

* `Subring.ratBaseChange`: the canonical `ℚ`-algebra map `ℚ ⊗[ℤ] R → A`.
* `Subring.ratBaseChangeEquiv`: that map as an isomorphism, given a spanning subring.

## Main results

* `TauCeti.exists_tmul_inv_natCast`: an element of `ℚ ⊗[ℤ] M` has a common denominator.
* `Subring.ratBaseChange_injective`: the comparison map is injective.
* `Subring.range_ratBaseChange`: its range is the `ℚ`-span of `R`.
* `Subring.span_eq_top_iff_exists_natCast_smul_mem`: a subring spans exactly when denominators can
  be cleared.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-! ## A common denominator in `ℚ ⊗[ℤ] M` -/

section Denominator

variable {M : Type*} [AddCommGroup M]

/-- Every element of `ℚ ⊗[ℤ] M` is a single elementary tensor with a natural-number denominator:
the rational coefficients of a finite sum can be put over a common denominator, and the numerators
absorbed into the right-hand factor.

This is `IsLocalizedModule.mk'_surjective` read through
`IsLocalization.tensorProduct_isLocalizedModule`, which exhibits `ℚ ⊗[ℤ] M` as the localization of
`M` at the positive integers; the denominator produced there is a positive integer, and its
absolute value is the natural number below. -/
theorem exists_tmul_inv_natCast (z : ℚ ⊗[ℤ] M) :
    ∃ n : ℕ, ∃ m : M, n ≠ 0 ∧ z = (n : ℚ)⁻¹ ⊗ₜ[ℤ] m := by
  have : IsLocalizedModule (Submonoid.pos ℤ) (_root_.TensorProduct.mk ℤ ℚ M 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (Submonoid.pos ℤ) ℚ
  obtain ⟨⟨m, s⟩, hs⟩ :=
    IsLocalizedModule.mk'_surjective (Submonoid.pos ℤ) (_root_.TensorProduct.mk ℤ ℚ M 1) z
  simp only [Function.uncurry_apply_pair] at hs
  -- The denominator produced by the localization is a positive integer; its absolute value is the
  -- natural number asked for, and equals it as a rational number.
  have hn : s.1.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt s.2)
  have hn_rat : ((s.1.natAbs : ℕ) : ℚ) = (s.1 : ℚ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (le_of_lt s.2)]
  refine ⟨s.1.natAbs, m, hn, hs.symm.trans (IsLocalizedModule.mk'_eq_iff.mpr ?_)⟩
  rw [_root_.TensorProduct.mk_apply, Submonoid.smul_def, _root_.TensorProduct.smul_tmul',
    zsmul_eq_mul, ← hn_rat, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)]

end Denominator

end TauCeti

namespace Subring

/-! ## The comparison map -/

section BaseChange

variable {A : Type*} [Ring A] [Algebra ℚ A] (R : Subring A)

/-- The canonical `ℚ`-algebra map `ℚ ⊗[ℤ] R → A` extending the inclusion of a subring of a
`ℚ`-algebra. It sends `q ⊗ₜ r` to `q • r`. -/
noncomputable def ratBaseChange : ℚ ⊗[ℤ] R →ₐ[ℚ] A :=
  AlgHom.liftEquiv ℤ ℚ R A R.subtype.toIntAlgHom

@[simp]
theorem ratBaseChange_tmul (q : ℚ) (r : R) : ratBaseChange R (q ⊗ₜ[ℤ] r) = q • (r : A) := by
  simp [ratBaseChange]

/-- The comparison map is injective for every subring: a common denominator can be cleared, and a
nonzero rational scalar acts injectively on the `ℚ`-algebra `A`. -/
theorem ratBaseChange_injective : Function.Injective (ratBaseChange R) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, r, hn, rfl⟩ := TauCeti.exists_tmul_inv_natCast z
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [ratBaseChange_tmul] at hz
  have hr : (r : A) = 0 := by
    have := congrArg (fun a : A => (n : ℚ) • a) hz
    simpa [smul_smul, mul_inv_cancel₀ hn'] using this
  have hr0 : r = 0 := Subtype.ext hr
  rw [hr0, TensorProduct.tmul_zero]

/-- The range of the comparison map is the `ℚ`-span of the subring: the map is the base change of
the inclusion of `R`, whose range is `R` itself. -/
theorem range_ratBaseChange :
    LinearMap.range (ratBaseChange R).toLinearMap = Submodule.span ℚ (R : Set A) := by
  -- Both sides of `hlift` are base-change lifts, so they agree once they agree on `1 ⊗ₜ r`.
  have hlift : (ratBaseChange R).toLinearMap =
      LinearMap.liftBaseChange ℚ R.subtype.toIntAlgHom.toLinearMap := by
    apply (LinearMap.liftBaseChangeEquiv ℚ).symm.injective
    ext r
    simp [ratBaseChange]
  rw [hlift, LinearMap.range_liftBaseChange]
  -- The range of the inclusion of `R` is `R`.
  congr 1
  ext a
  simp

/-- The comparison map is surjective exactly when the subring spans the ambient algebra over `ℚ`. -/
theorem ratBaseChange_surjective_iff :
    Function.Surjective (ratBaseChange R) ↔ Submodule.span ℚ (R : Set A) = ⊤ := by
  rw [← range_ratBaseChange, LinearMap.range_eq_top]
  exact Iff.rfl

/-- The comparison map is bijective for a spanning subring. -/
theorem ratBaseChange_bijective (h : Submodule.span ℚ (R : Set A) = ⊤) :
    Function.Bijective (ratBaseChange R) :=
  ⟨ratBaseChange_injective R, (ratBaseChange_surjective_iff R).2 h⟩

/-- A spanning subring is a `ℤ`-form of the ambient `ℚ`-algebra: extending its scalars to `ℚ`
recovers that algebra. -/
noncomputable def ratBaseChangeEquiv (h : Submodule.span ℚ (R : Set A) = ⊤) :
    ℚ ⊗[ℤ] R ≃ₐ[ℚ] A :=
  AlgEquiv.ofBijective (ratBaseChange R) (ratBaseChange_bijective R h)

@[simp]
theorem ratBaseChangeEquiv_tmul (h : Submodule.span ℚ (R : Set A) = ⊤) (q : ℚ) (r : R) :
    ratBaseChangeEquiv R h (q ⊗ₜ[ℤ] r) = q • (r : A) := by
  rw [ratBaseChangeEquiv, AlgEquiv.ofBijective_apply, ratBaseChange_tmul]

/-- Denominators can be cleared in a spanning subring: every element of the ambient algebra is
carried into it by some nonzero natural number. -/
theorem exists_natCast_smul_mem (h : Submodule.span ℚ (R : Set A) = ⊤) (a : A) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • a ∈ R := by
  obtain ⟨z, rfl⟩ := (ratBaseChange_surjective_iff R).2 h a
  obtain ⟨n, r, hn, rfl⟩ := TauCeti.exists_tmul_inv_natCast z
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨n, hn, ?_⟩
  rw [ratBaseChange_tmul, smul_smul, mul_inv_cancel₀ hn', one_smul]
  exact r.2

/-- A subring spans its ambient `ℚ`-algebra exactly when denominators can be cleared: every
element is carried into the subring by some nonzero natural number. This is the form of the
spanning hypothesis that a consumer checks in practice. -/
theorem span_eq_top_iff_exists_natCast_smul_mem :
    Submodule.span ℚ (R : Set A) = ⊤ ↔ ∀ a : A, ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • a ∈ R := by
  refine ⟨fun h a => exists_natCast_smul_mem R h a, fun h => top_le_iff.mp fun a _ => ?_⟩
  obtain ⟨n, hn, hmem⟩ := h a
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have ha : a = (n : ℚ)⁻¹ • ((n : ℚ) • a) := by
    rw [smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [ha]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end BaseChange

end Subring
