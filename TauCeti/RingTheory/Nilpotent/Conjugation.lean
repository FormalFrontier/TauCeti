/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# Conjugating an integral nilpotent exponential by an intertwining automorphism

Let `V` be a module over a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and let
`θ : V ≃ₗ[ℚ] V` be a `ℚ`-linear automorphism restricting to a bijection of `M`. If `θ` carries the
action of `x : A` to the action of `y : A`, in the sense that `θ (x • v) = y • θ v`, then it carries
every divided power of `x` to the corresponding divided power of `y`, and hence conjugates the
base-changed divided-power exponential of `x` into that of `y`:

```text
θ_R ∘ E_R(x, t) = E_R(y, t) ∘ θ_R,     θ_R = R ⊗ θ|_M.
```

The intertwining hypothesis is imposed only on `x` itself. Divided powers divide by factorials in
`A`, so `θ` must be `ℚ`-linear for the transported statement to make sense; the *conclusion* is
nonetheless an identity of integral operators on `R ⊗[ℤ] M` over an arbitrary commutative ring `R`.

This is a mechanism used to construct graph automorphisms of Chevalley groups: a symmetry of the
ambient Lie-algebra data that permutes the distinguished root vectors conjugates the corresponding
root subgroups into one another, permuted the same way. Its application to Kostant root subgroups
is in `TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/NumberedSymmetry.lean`.

## Main definitions and results

* `TauCeti.invariantRestrict`: a `ℚ`-linear automorphism restricted to an invariant additive
  subgroup, as an integral automorphism of that subgroup.
* `TauCeti.apply_pow_smul_of_intertwines` and `TauCeti.apply_dividedPower_smul_of_intertwines`:
  an intertwiner for `x` and `y` intertwines their powers and their divided powers.
* `TauCeti.pow_eq_zero_of_intertwines`: over a faithful module, nilpotency transfers along an
  intertwiner.
* `TauCeti.invariantRestrictUnit`: the resulting automorphism of the scalar extension `R ⊗[ℤ] M`,
  with `TauCeti.invariantRestrictUnit_pow_eq_one` transporting an `n`th-power-one relation of `θ`.
* `TauCeti.baseChange_invariantRestrict_baseChangeExp`: the conjugation formula for the
  base-changed exponential.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
-/

public section

namespace TauCeti

open TensorProduct

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module ℚ V] [Module A V] [IsScalarTower ℚ A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-! ## Restricting an automorphism to an invariant subgroup -/

/-- A `ℚ`-linear automorphism of `V` that restricts to a bijection of an additive subgroup `M`,
viewed as an integral automorphism of `M`.

The subgroup `M` is not a `ℚ`-submodule — in the intended application it is a lattice — so this is
genuinely a restriction of scalars to `ℤ` and not an instance of `LinearEquiv.ofSubmodule'`. -/
def invariantRestrict (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) : M ≃ₗ[ℤ] M where
  toFun v := ⟨θ v, (hθ v).2 v.2⟩
  invFun v := ⟨θ.symm v, (hθ _).1 (by rw [θ.apply_symm_apply]; exact v.2)⟩
  left_inv v := Subtype.ext (θ.symm_apply_apply _)
  right_inv v := Subtype.ext (θ.apply_symm_apply _)
  map_add' v w := Subtype.ext (map_add θ _ _)
  map_smul' t v := Subtype.ext (map_zsmul θ _ _)

/-- The restriction of `θ` to an invariant subgroup acts by `θ`. -/
@[simp]
theorem coe_invariantRestrict_apply (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (v : M) :
    ((invariantRestrict θ M hθ v : M) : V) = θ (v : V) :=
  (rfl)

/-- The inverse of the restriction of `θ` to an invariant subgroup acts by `θ.symm`. -/
@[simp]
theorem coe_invariantRestrict_symm_apply (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (v : M) :
    (((invariantRestrict θ M hθ).symm v : M) : V) = θ.symm (v : V) :=
  (rfl)

/-- Powers of the restriction of `θ` act by the corresponding powers of `θ`. -/
theorem coe_invariantRestrict_pow_apply (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (n : ℕ) (v : M) :
    (((invariantRestrict θ M hθ ^ n) v : M) : V) = (θ ^ n) (v : V) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply,
        coe_invariantRestrict_apply]

/-! ## Transporting powers and divided powers -/

variable (θ : V →ₗ[ℚ] V) {x y : A}

omit [Algebra ℚ A] [IsScalarTower ℚ A V] in
/-- A linear map intertwining the actions of `x` and `y` intertwines the actions of their
powers. -/
theorem apply_pow_smul_of_intertwines (hxy : ∀ v, θ (x • v) = y • θ v) (n : ℕ) (v : V) :
    θ (x ^ n • v) = y ^ n • θ v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ x n, mul_smul, ih (x • v), hxy, pow_succ y n, mul_smul]

/-- A linear map intertwining the actions of `x` and `y` intertwines the actions of their
divided powers.

The divided powers involve division by factorials, which is why the intertwiner is required to be
`ℚ`-linear rather than merely additive. -/
theorem apply_dividedPower_smul_of_intertwines (hxy : ∀ v, θ (x • v) = y • θ v) (n : ℕ) (v : V) :
    θ (Associative.dividedPower n x • v) = Associative.dividedPower n y • θ v := by
  rw [Associative.dividedPower_def, Associative.dividedPower_def, smul_assoc, smul_assoc,
    map_smul, apply_pow_smul_of_intertwines θ hxy]

variable (θ : V ≃ₗ[ℚ] V)

omit [Algebra ℚ A] [IsScalarTower ℚ A V] in
/-- Over a faithful module, nilpotency transfers along an intertwiner: if `θ` carries the action of
`x` to the action of `y`, then a vanishing power of `x` forces the same power of `y` to vanish. -/
theorem pow_eq_zero_of_intertwines [FaithfulSMul A V] (hxy : ∀ v, θ (x • v) = y • θ v) {k : ℕ}
    (hkx : x ^ k = 0) : y ^ k = 0 := by
  refine eq_of_smul_eq_smul (α := V) fun v => ?_
  have hv := apply_pow_smul_of_intertwines θ.toLinearMap hxy k (θ.symm v)
  simp only [LinearEquiv.coe_toLinearMap] at hv
  rw [hkx, zero_smul, map_zero, θ.apply_symm_apply] at hv
  rw [zero_smul]
  exact hv.symm

/-! ## Conjugating the base-changed exponential -/

-- Use the module structure carried by the explicit `ℤ`-algebra, matching `baseChangeExp`.
attribute [local instance high] Algebra.toModule

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- The automorphism of the scalar extension `R ⊗[ℤ] M` induced by a `ℚ`-linear automorphism of `V`
preserving `M`.

Only the integral restriction of `θ` is used, so this is defined over every commutative ring `R`,
just like the exponentials it conjugates. -/
noncomputable def invariantRestrictUnit (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) :
    LinearMap.GeneralLinearGroup R (R ⊗[ℤ] M) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv ((invariantRestrict θ M hθ).baseChange ℤ R M M)

/-- The induced automorphism of a scalar extension is the base change of the restriction of `θ`. -/
theorem val_invariantRestrictUnit_apply (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (z : R ⊗[ℤ] M) :
    (invariantRestrictUnit (R := R) θ M hθ).val z =
      (invariantRestrict θ M hθ).baseChange ℤ R M M z :=
  (rfl)

/-- The induced automorphism of a scalar extension acts on a pure tensor through the restriction
of `θ`. -/
@[simp]
theorem val_invariantRestrictUnit_tmul (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (r : R) (v : M) :
    (invariantRestrictUnit (R := R) θ M hθ).val (r ⊗ₜ[ℤ] v) =
      r ⊗ₜ[ℤ] invariantRestrict θ M hθ v :=
  (rfl)

private theorem val_invariantRestrictUnit_pow_tmul (θ : V ≃ₗ[ℚ] V) (M : S)
    (hθ : ∀ v, θ v ∈ M ↔ v ∈ M) (n : ℕ) (r : R) (v : M) :
    (invariantRestrictUnit (R := R) θ M hθ ^ n).val (r ⊗ₜ[ℤ] v) =
      r ⊗ₜ[ℤ] ((invariantRestrict θ M hθ ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, val_invariantRestrictUnit_tmul, ih,
        pow_succ, LinearEquiv.mul_apply]

/-- If an automorphism has `n`th power one, then the induced automorphism on every scalar extension
also has `n`th power one.

Thus the order of the induced automorphism divides `n`; restriction or scalar extension may lower
the exact order. -/
theorem invariantRestrictUnit_pow_eq_one (θ : V ≃ₗ[ℚ] V) (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    {n : ℕ} (hn : ∀ v, (θ ^ n) v = v) :
    invariantRestrictUnit (R := R) θ M hθ ^ n = 1 := by
  refine Units.ext (LinearMap.ext fun z => ?_)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      rw [val_invariantRestrictUnit_pow_tmul, Units.val_one, Module.End.one_apply]
      exact congrArg (fun w : M => r ⊗ₜ[ℤ] w)
        (Subtype.ext ((coe_invariantRestrict_pow_apply θ M hθ n v).trans (hn (v : V))))
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- Conjugating the base-changed divided-power exponential of `x` by an intertwiner produces the
base-changed divided-power exponential of `y`, with the same parameter.

Both exponentials are truncated at a common bound `k`, which is available in practice because
nilpotency transfers along the intertwiner (`pow_eq_zero_of_intertwines`). -/
theorem baseChange_invariantRestrict_baseChangeExp (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (hxy : ∀ v, θ (x • v) = y • θ v)
    (hx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    {k : ℕ} (hkx : x ^ k = 0) (hky : y ^ k = 0) (t : R) (z : R ⊗[ℤ] M) :
    (invariantRestrict θ M hθ).baseChange ℤ R M M (baseChangeExp x M hx t z) =
      baseChangeExp y M hy t ((invariantRestrict θ M hθ).baseChange ℤ R M M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      rw [baseChangeExp_tmul_of_pow_eq_zero x M hx hkx, map_sum,
        LinearEquiv.baseChange_tmul, baseChangeExp_tmul_of_pow_eq_zero y M hy hky]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LinearEquiv.baseChange_tmul]
      congr 1
      refine Subtype.ext ?_
      rw [coe_invariantRestrict_apply, coe_integralDividedPower_apply,
        coe_integralDividedPower_apply, coe_invariantRestrict_apply]
      simpa only [LinearEquiv.coe_toLinearMap] using
        apply_dividedPower_smul_of_intertwines θ.toLinearMap hxy n (v : V)
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

end TauCeti
