/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.LinearAlgebra.GeneralLinearGroup.InvariantRestrict
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

* `TauCeti.apply_pow_smul_of_intertwines` and `TauCeti.apply_dividedPower_smul_of_intertwines`:
  an intertwiner for `x` and `y` intertwines their powers and their divided powers.
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

/-! ## Transporting powers and divided powers -/

section Powers

variable {B X Y : Type*} [Monoid B] [MulAction B X] [MulAction B Y]
variable (f : X → Y) {x y : B}

/-- A map intertwining the actions of `x` and `y` intertwines the actions of their powers. -/
theorem apply_pow_smul_of_intertwines (hxy : ∀ v, f (x • v) = y • f v) (n : ℕ) (v : X) :
    f (x ^ n • v) = y ^ n • f v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ x n, mul_smul, ih (x • v), hxy, pow_succ y n, mul_smul]

end Powers

variable (θ : V →ₗ[ℚ] V) {x y : A}

/-- A linear map intertwining the actions of `x` and `y` intertwines the actions of their
divided powers.

The divided powers involve division by factorials, which is why the intertwiner is required to be
`ℚ`-linear rather than merely additive. -/
theorem apply_dividedPower_smul_of_intertwines (hxy : ∀ v, θ (x • v) = y • θ v) (n : ℕ) (v : V) :
    θ (Associative.dividedPower n x • v) = Associative.dividedPower n y • θ v := by
  rw [Associative.dividedPower_def, Associative.dividedPower_def, smul_assoc, smul_assoc,
    map_smul, apply_pow_smul_of_intertwines θ hxy]

variable (θ : V ≃ₗ[ℚ] V)

/-! ## Conjugating the base-changed exponential -/

-- Use the module structure carried by the explicit `ℤ`-algebra, matching `baseChangeExp`.
attribute [local instance high] Algebra.toModule

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- Conjugating the base-changed divided-power exponential of `x` by an intertwiner produces the
base-changed divided-power exponential of `y`, with the same parameter.

Both exponentials are truncated at a common bound `k`; in the intended application, the second
bound follows structurally by conjugating the first nilpotent endomorphism. -/
theorem baseChange_invariantRestrict_baseChangeExp (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (hxy : ∀ v, θ (x • v) = y • θ v)
    (hx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    {k : ℕ} (hkx : x ^ k = 0) (hky : y ^ k = 0) (t : R) (z : R ⊗[ℤ] M) :
    (GeneralLinearGroup.invariantRestrict θ.toAddEquiv M hθ).baseChange ℤ R M M
        (baseChangeExp x M hx t z) =
      baseChangeExp y M hy t
        ((GeneralLinearGroup.invariantRestrict θ.toAddEquiv M hθ).baseChange ℤ R M M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      rw [baseChangeExp_tmul_of_pow_eq_zero x M hx hkx, map_sum,
        LinearEquiv.baseChange_tmul, baseChangeExp_tmul_of_pow_eq_zero y M hy hky]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LinearEquiv.baseChange_tmul]
      congr 1
      refine Subtype.ext ?_
      rw [GeneralLinearGroup.coe_invariantRestrict_apply, coe_integralDividedPower_apply,
        coe_integralDividedPower_apply, GeneralLinearGroup.coe_invariantRestrict_apply]
      change θ (Associative.dividedPower n x • (v : V)) =
        Associative.dividedPower n y • θ (v : V)
      simpa only [LinearEquiv.coe_toLinearMap] using
        apply_dividedPower_smul_of_intertwines θ.toLinearMap hxy n (v : V)
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

end TauCeti
