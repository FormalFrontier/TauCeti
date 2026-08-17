/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ScalarExtension

/-!
# Restricting additive automorphisms to invariant subgroups

An additive automorphism of an abelian group which preserves an additive subgroup restricts to an
integral linear automorphism of that subgroup. Base change gives an automorphism of every scalar
extension of the subgroup, compatibly with further scalar extension.

## Main declarations

* `TauCeti.GeneralLinearGroup.invariantRestrict`: restriction to an invariant additive subgroup.
* `TauCeti.GeneralLinearGroup.baseChangeInvariantRestrictUnit`: the induced automorphism after
  scalar extension.
* `TauCeti.GeneralLinearGroup.baseChangeInvariantRestrictUnit_pow_eq_one`: transport of an
  exponent bound to scalar extensions.
* `TauCeti.GeneralLinearGroup.mapScalarExtensionAutomorphisms_baseChangeInvariantRestrictUnit`:
  compatibility with further scalar extension.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.GeneralLinearGroup

universe u v w

variable {V : Type u} [AddCommGroup V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-! ## Restriction to an invariant subgroup -/

/-- An additive automorphism of `V` that restricts to a bijection of an additive subgroup `M`,
viewed as an integral linear automorphism of `M`. -/
def invariantRestrict (θ : V ≃+ V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) : M ≃ₗ[ℤ] M where
  toFun v := ⟨θ v, (hθ v).2 v.2⟩
  invFun v := ⟨θ.symm v, (hθ _).1 (by rw [θ.apply_symm_apply]; exact v.2)⟩
  left_inv v := Subtype.ext (θ.symm_apply_apply _)
  right_inv v := Subtype.ext (θ.apply_symm_apply _)
  map_add' v w := Subtype.ext (map_add θ _ _)
  map_smul' t v := Subtype.ext (map_zsmul θ _ _)

/-- The restriction of `θ` to an invariant subgroup acts by `θ`. -/
@[simp]
theorem coe_invariantRestrict_apply (θ : V ≃+ V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (v : M) : ((invariantRestrict θ M hθ v : M) : V) = θ (v : V) :=
  by rfl

/-- The inverse of the restriction of `θ` acts by `θ.symm`. -/
@[simp]
theorem coe_invariantRestrict_symm_apply (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (v : M) :
    (((invariantRestrict θ M hθ).symm v : M) : V) = θ.symm (v : V) :=
  by rfl

/-- Restriction commutes with taking the inverse automorphism. -/
theorem invariantRestrict_symm (θ : V ≃+ V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) :
    (invariantRestrict θ M hθ).symm = invariantRestrict θ.symm M
      (fun v => by simpa only [θ.apply_symm_apply] using (hθ (θ.symm v)).symm) := by
  ext v
  rfl

/-- Powers of the restriction of `θ` act by the corresponding powers of `θ`. -/
theorem coe_invariantRestrict_pow_apply (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (n : ℕ) (v : M) :
    (((invariantRestrict θ M hθ ^ n) v : M) : V) =
      (θ.toIntLinearEquiv ^ n) (v : V) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply,
        coe_invariantRestrict_apply]
      simp only [AddEquiv.coe_toIntLinearEquiv]

/-! ## Base change -/

attribute [local instance high] Algebra.toModule

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- The automorphism of `R ⊗[ℤ] M` obtained by base-changing the restriction of `θ`. -/
noncomputable def baseChangeInvariantRestrictUnit (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) :
    LinearMap.GeneralLinearGroup R (R ⊗[ℤ] M) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv ((invariantRestrict θ M hθ).baseChange ℤ R M M)

/-- The induced automorphism is the base change of the restriction of `θ`. -/
theorem val_baseChangeInvariantRestrictUnit_apply (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (z : R ⊗[ℤ] M) :
    (baseChangeInvariantRestrictUnit (R := R) θ M hθ).val z =
      (invariantRestrict θ M hθ).baseChange ℤ R M M z := by
  exact congrFun (LinearMap.GeneralLinearGroup.coe_ofLinearEquiv _) z

/-- The induced automorphism acts on a pure tensor through the restriction of `θ`. -/
@[simp]
theorem val_baseChangeInvariantRestrictUnit_tmul (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (r : R) (v : M) :
    (baseChangeInvariantRestrictUnit (R := R) θ M hθ).val (r ⊗ₜ[ℤ] v) =
      r ⊗ₜ[ℤ] invariantRestrict θ M hθ v := by
  rw [val_baseChangeInvariantRestrictUnit_apply, LinearEquiv.baseChange_tmul]

/-- The inverse induced automorphism acts on a pure tensor through the inverse restriction. -/
@[simp]
theorem val_baseChangeInvariantRestrictUnit_inv_tmul (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (r : R) (v : M) :
    ((baseChangeInvariantRestrictUnit (R := R) θ M hθ)⁻¹).val (r ⊗ₜ[ℤ] v) =
      r ⊗ₜ[ℤ] (invariantRestrict θ M hθ).symm v := by
  rw [baseChangeInvariantRestrictUnit, ← LinearMap.GeneralLinearGroup.ofLinearEquiv_inv,
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, ← LinearEquiv.baseChange_inv,
    LinearEquiv.baseChange_tmul]
  simp only [LinearEquiv.coe_inv]

/-- An exponent bound on `θ` is preserved by restriction and scalar extension. -/
theorem baseChangeInvariantRestrictUnit_pow_eq_one (θ : V ≃+ V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) {n : ℕ}
    (hn : ∀ v, (θ.toIntLinearEquiv ^ n) v = v) :
    baseChangeInvariantRestrictUnit (R := R) θ M hθ ^ n = 1 := by
  have h1 : invariantRestrict θ M hθ ^ n = 1 :=
    LinearEquiv.ext fun v => Subtype.ext ((coe_invariantRestrict_pow_apply θ M hθ n v).trans
      (hn (v : V)))
  rw [baseChangeInvariantRestrictUnit]
  calc
    LinearMap.GeneralLinearGroup.ofLinearEquiv
          ((invariantRestrict θ M hθ).baseChange ℤ R M M) ^ n =
        LinearMap.GeneralLinearGroup.ofLinearEquiv
          ((invariantRestrict θ M hθ).baseChange ℤ R M M ^ n) :=
      (map_pow (LinearMap.GeneralLinearGroup.generalLinearEquiv R (R ⊗[ℤ] M)).symm _ n).symm
    _ = 1 := by
      rw [← LinearEquiv.baseChange_pow, h1, LinearEquiv.baseChange_one]
      rfl

/-- Further scalar extension leaves the base-changed restriction unchanged. -/
theorem mapScalarExtensionAutomorphisms_baseChangeInvariantRestrictUnit
    {A B : CommAlgCat.{w} ℤ} (θ : V ≃+ V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (φ : A ⟶ B) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := M) φ
        (baseChangeInvariantRestrictUnit (R := A) θ M hθ) =
      baseChangeInvariantRestrictUnit (R := B) θ M hθ := by
  refine (GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    φ _ _ fun z => ?_).symm
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [GeneralLinear.scalarExtensionMap_tmul, val_baseChangeInvariantRestrictUnit_tmul,
        val_baseChangeInvariantRestrictUnit_tmul, GeneralLinear.scalarExtensionMap_tmul]
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

end TauCeti.GeneralLinearGroup
