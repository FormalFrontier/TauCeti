/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Dual lattices under form scaling

Scaling the form of an integral lattice `L` by a nonzero integer `n` scales its dual carrier by
`n⁻¹` in the common rational ambient space:

```text
(nL)ᵛ = n⁻¹ Lᵛ.
```

Equivalently, multiplication by `n` is an integral-linear equivalence from `(nL)ᵛ` to `Lᵛ`.
The carrier of `L` itself is unchanged by form scaling; it is only the integrality condition on
pairings that changes.  The final theorem records that the integral dual pairing is compatible
with this equivalence.

## Main declarations

* `TauCeti.IntegralLattice.mem_dualCarrier_smul_iff`: membership in the scaled dual carrier.
* `TauCeti.IntegralLattice.dualCarrier_smul`: `(nL)ᵛ = n⁻¹ Lᵛ` as submodules of the ambient
  rational vector space.
* `TauCeti.IntegralLattice.dualCarrierScaleEquiv`: multiplication by `n` as an equivalence
  `(nL)ᵛ ≃ Lᵛ`.
* `TauCeti.IntegralLattice.dualPairing_smul`: compatibility with the integral dual pairing.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 2, compatibility of dual lattices with
  scaling.
-/

public section

open scoped Pointwise

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- A vector belongs to the dual carrier for the form scaled by `n` exactly when its multiple by
`n` belongs to the original dual carrier. -/
@[simp]
theorem mem_dualCarrier_smul_iff (n : ℤ) (L : IntegralLattice V) (x : V) :
    x ∈ (n • L).dualCarrier ↔ (n : ℚ) • x ∈ L.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx y hy
    simpa only [smul_carrier, smul_form, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.BilinForm.smul_left] using hx y hy
  · intro hx y hy
    simpa only [smul_carrier, smul_form, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.BilinForm.smul_left] using hx y hy

/-- **Scaling a form by `n` scales its dual carrier by `n⁻¹`.**

The scalar on the right is a rational unit, and its action on the `ℤ`-submodule is Mathlib's
pointwise scalar action.  The equality itself does not require nondegeneracy. -/
theorem dualCarrier_smul {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V) :
    (n • L).dualCarrier =
      (Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn))⁻¹ • L.dualCarrier := by
  let u : ℚˣ := Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn)
  -- Name the rational unit so the submodule action has a readable scalar.
  change (n • L).dualCarrier = u⁻¹ • L.dualCarrier
  ext x
  rw [mem_dualCarrier_smul_iff]
  -- Pointwise submodule membership reduces to Mathlib's set-action membership criterion.
  change (n : ℚ) • x ∈ L.dualCarrier ↔ x ∈ u⁻¹ • (L.dualCarrier : Set V)
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [inv_inv, u, Units.smul_def]
  rfl

/-- Multiplication by a nonzero integer identifies the dual carrier of the scaled form with the
original dual carrier. -/
def dualCarrierScaleEquiv {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V) :
    (n • L).dualCarrier ≃ₗ[ℤ] L.dualCarrier where
  toFun x := ⟨(n : ℚ) • (x : V), (mem_dualCarrier_smul_iff n L x).mp x.property⟩
  invFun y := ⟨(n : ℚ)⁻¹ • (y : V), (mem_dualCarrier_smul_iff n L _).mpr (by
    rw [smul_smul, mul_inv_cancel₀ (show (n : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hn), one_smul]
    exact y.property)⟩
  left_inv x := by
    apply Subtype.ext
    simp only [smul_smul,
      inv_mul_cancel₀ (show (n : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hn), one_smul]
  right_inv y := by
    apply Subtype.ext
    simp only [smul_smul,
      mul_inv_cancel₀ (show (n : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hn), one_smul]
  map_add' x y := by
    apply Subtype.ext
    exact smul_add (n : ℚ) (x : V) y
  map_smul' k x := by
    apply Subtype.ext
    exact smul_comm (n : ℚ) k (x : V)

/-- The dual-carrier scaling equivalence acts by multiplication by `n` in the ambient rational
vector space. -/
@[simp]
theorem coe_dualCarrierScaleEquiv_apply {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V)
    (x : (n • L).dualCarrier) :
    (L.dualCarrierScaleEquiv hn x : V) = (n : ℚ) • (x : V) :=
  (rfl)

/-- The inverse dual-carrier scaling equivalence acts by multiplication by `n⁻¹`. -/
@[simp]
theorem coe_dualCarrierScaleEquiv_symm_apply {n : ℤ} (hn : n ≠ 0)
    (L : IntegralLattice V) (x : L.dualCarrier) :
    ((L.dualCarrierScaleEquiv hn).symm x : V) = (n : ℚ)⁻¹ • (x : V) :=
  (rfl)

/-- The integral dual pairing for a scaled form agrees with the original dual pairing after
multiplying the dual vector by the scale factor. -/
theorem dualPairing_smul {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V)
    (x : (n • L).dualCarrier) (y : L) :
    (n • L).dualPairing x y = L.dualPairing (L.dualCarrierScaleEquiv hn x) y := by
  apply Int.cast_injective (α := ℚ)
  rw [(n • L).dualPairing_cast, L.dualPairing_cast, smul_form, LinearMap.smul_apply,
    coe_dualCarrierScaleEquiv_apply, LinearMap.BilinForm.smul_left]
  exact smul_eq_mul (n : ℚ) (L.form x y)

end TauCeti.IntegralLattice
