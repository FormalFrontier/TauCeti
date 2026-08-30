/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import TauCeti.RepresentationTheory.Spin.IntegralLattice
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Basic

/-!
# Simple-root bivectors for the type-D spin representation

Let `P` be a polarization of a rational quadratic space and let `b` be a basis of its first
isotropic summand, indexed by `Fin n`. The span of `b` and its polar dual is a split quadratic
subspace of rank `2 * n`, so its quadratic Lie subalgebra is a copy of `Dₙ` inside the quadratic
Lie algebra of `Q`. This file gives integral Clifford representatives of the positive and negative
Bourbaki simple roots of that `Dₙ`. For a chain root `eᵢ - eᵢ₊₁` they are

```text
Eᵢ = ι(bᵢ) ι(b'ᵢ₊₁),        Fᵢ = ι(bᵢ₊₁) ι(b'ᵢ),
```

and at the fork root `eₙ₋₂ + eₙ₋₁` they are

```text
Eₙ₋₁ = ι(bₙ₋₂) ι(bₙ₋₁),    Fₙ₋₁ = ι(b'ₙ₋₁) ι(b'ₙ₋₂).
```

Here `b'` is polar-dual to `b`. Orthogonality makes each displayed product equal to the
half-normalized Clifford bivector of its two factors. Consequently the representatives belong to
the quadratic Lie subalgebra. Their brackets with the diagonal bivectors have exactly the
coordinates of `TauCeti.DynkinType.typeDSimpleRoot`, fixing both the Bourbaki numbering and the
sign convention.

Each representative is a product of integral creation or annihilation operators, so its spin
action preserves the coordinate integral lattice. It also squares to zero, and hence acts by a
square-zero endomorphism on the rational spinor module.

Nothing here needs the polarization to be even: the representatives, their weights and their
Chevalley bracket are the same whatever the orthogonal remainder `P.line` is. What the remainder
controls is how the `Dₙ` sits in the quadratic Lie algebra of `Q`. For an even polarization,
`P.line = ⊥`, the two exhaust each other and these are the simple-root generators of the ambient
type-`Dₙ` spin carrier; for a polarization with a nonzero remainder the very same elements
generate a `Dₙ` subalgebra of the larger, type-`Bₙ` algebra of `Q`.

## Main definitions and results

* `TauCeti.SpinPolarizationData.typeDPositiveSimpleRootBivector` and
  `TauCeti.SpinPolarizationData.typeDNegativeSimpleRootBivector`: the integral Clifford
  representatives.
* `TauCeti.SpinPolarizationData.lie_diagonalBivector_typeDPositiveSimpleRootBivector` and
  `TauCeti.SpinPolarizationData.lie_diagonalBivector_typeDNegativeSimpleRootBivector`: their
  Bourbaki simple-root weights.
* The positive/negative bracket theorem gives the Chevalley normalization.
* `TauCeti.SpinPolarizationData.typeDPositiveSimpleRootBivector_mem_integralSpinActionSubring`
  and its negative analogue: preservation of the integral spinor lattice.
* `TauCeti.SpinPolarizationData.spinAction_typeDPositiveSimpleRootBivector_sq` and its negative
  analogue: square-zero action.

## Roadmap

This is the simple-root Clifford prerequisite for the type-`D` Chevalley carrier in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, which instantiates it at an even polarization. The
remaining carrier step is to identify these
elements with the standard type-`D` matrix root generators and package the resulting integral
pinned representation. That carrier is consumed by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {Q : QuadraticForm ℚ V} (P : SpinPolarizationData Q)
variable {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W)

/-- The positive integral Clifford representative of the `i`-th Bourbaki simple root of the `Dₙ`
carried by the polarization basis `b`, which is all of the quadratic Lie algebra of `Q` exactly
when `P` is even. For a chain node it is creation at `i` followed by annihilation at `i + 1`; at
the fork node it is creation at each of the last two coordinates. -/
noncomputable def typeDPositiveSimpleRootBivector (hn : 4 ≤ n) (i : Fin n) :
    CliffordAlgebra Q :=
  if h : (i : ℕ) + 1 < n then
    ι Q (b i : V) * ι Q (P.dualVector b ⟨(i : ℕ) + 1, h⟩ : V)
  else
    ι Q (b ⟨n - 2, by omega⟩ : V) * ι Q (b ⟨n - 1, by omega⟩ : V)

/-- The negative integral Clifford representative of the `i`-th Bourbaki simple root of the `Dₙ`
carried by the polarization basis `b`, paired with the `i`-th positive representative. The
reversed order at the fork fixes the standard Chevalley sign convention. -/
noncomputable def typeDNegativeSimpleRootBivector (hn : 4 ≤ n) (i : Fin n) :
    CliffordAlgebra Q :=
  if h : (i : ℕ) + 1 < n then
    ι Q (b ⟨(i : ℕ) + 1, h⟩ : V) * ι Q (P.dualVector b i : V)
  else
    ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) *
      ι Q (P.dualVector b ⟨n - 2, by omega⟩ : V)

/-- The positive simple-root representative, exposed as the corresponding Clifford bivector. -/
theorem typeDPositiveSimpleRootBivector_eq (hn : 4 ≤ n) (i : Fin n) :
    P.typeDPositiveSimpleRootBivector b hn i =
      if h : (i : ℕ) + 1 < n then
        bivector Q (b i : V) (P.dualVector b ⟨(i : ℕ) + 1, h⟩ : V)
      else
        bivector Q (b ⟨n - 2, by omega⟩ : V) (b ⟨n - 1, by omega⟩ : V) := by
  rw [typeDPositiveSimpleRootBivector]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    rw [ι_mul_ι_eq_bivector_add, P.polar_dualVector]
    simp [Fin.ext_iff]
  · simp only [dite_eq_right h]
    rw [ι_mul_ι_eq_bivector_add, P.polar_W_eq_zero]
    simp

/-- The negative simple-root representative, exposed as the corresponding Clifford bivector. -/
theorem typeDNegativeSimpleRootBivector_eq (hn : 4 ≤ n) (i : Fin n) :
    P.typeDNegativeSimpleRootBivector b hn i =
      if h : (i : ℕ) + 1 < n then
        bivector Q (b ⟨(i : ℕ) + 1, h⟩ : V) (P.dualVector b i : V)
      else
        bivector Q (P.dualVector b ⟨n - 1, by omega⟩ : V)
          (P.dualVector b ⟨n - 2, by omega⟩ : V) := by
  rw [typeDNegativeSimpleRootBivector]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    rw [ι_mul_ι_eq_bivector_add, P.polar_dualVector]
    simp [Fin.ext_iff]
  · simp only [dite_eq_right h]
    rw [ι_mul_ι_eq_bivector_add, P.polar_W'_eq_zero]
    simp

/-- Positive type-`D` simple-root representatives are quadratic Clifford elements. -/
theorem typeDPositiveSimpleRootBivector_mem_quadraticLieSubalgebra
    (hn : 4 ≤ n) (i : Fin n) :
    P.typeDPositiveSimpleRootBivector b hn i ∈ quadraticLieSubalgebra Q := by
  rw [P.typeDPositiveSimpleRootBivector_eq b hn i]
  split <;> exact bivector_mem_quadraticLieSubalgebra Q _ _

/-- Negative type-`D` simple-root representatives are quadratic Clifford elements. -/
theorem typeDNegativeSimpleRootBivector_mem_quadraticLieSubalgebra
    (hn : 4 ≤ n) (i : Fin n) :
    P.typeDNegativeSimpleRootBivector b hn i ∈ quadraticLieSubalgebra Q := by
  rw [P.typeDNegativeSimpleRootBivector_eq b hn i]
  split <;> exact bivector_mem_quadraticLieSubalgebra Q _ _

private theorem lie_diagonalBivector_bivector_basis_dualVector (k i j : Fin n) :
    ⁅P.diagonalBivector b k, bivector Q (b i : V) (P.dualVector b j : V)⁆ =
      ((if k = i then (1 : ℚ) else 0) - if k = j then 1 else 0) •
        bivector Q (b i : V) (P.dualVector b j : V) := by
  have h1 : polar Q (P.dualVector b k : V) (b i : V) = if k = i then 1 else 0 := by
    rw [polar_comm, P.polar_dualVector]
    simp [eq_comm]
  have h2 : polar Q (b k : V) (b i : V) = 0 := P.polar_W_eq_zero _ _
  have h3 : polar Q (P.dualVector b k : V) (P.dualVector b j : V) = 0 :=
    P.polar_W'_eq_zero _ _
  have h4 : polar Q (b k : V) (P.dualVector b j : V) = if k = j then 1 else 0 := by
    rw [P.polar_dualVector]
  rw [P.diagonalBivector_def b, lie_bivector_bivector, h1, h2, h3, h4]
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp [bivector_def]
      module
    · simp [hkj, bivector_def]
  · by_cases hkj : k = j
    · subst j
      simp [hki, bivector_def]
      module
    · simp [hki, hkj, bivector_def]

private theorem lie_diagonalBivector_bivector_basis_basis (k i j : Fin n) :
    ⁅P.diagonalBivector b k, bivector Q (b i : V) (b j : V)⁆ =
      ((if k = i then (1 : ℚ) else 0) + if k = j then 1 else 0) •
        bivector Q (b i : V) (b j : V) := by
  have h1 : polar Q (P.dualVector b k : V) (b i : V) = if k = i then 1 else 0 := by
    rw [polar_comm, P.polar_dualVector]
    simp [eq_comm]
  have h2 : polar Q (b k : V) (b i : V) = 0 := P.polar_W_eq_zero _ _
  have h3 : polar Q (P.dualVector b k : V) (b j : V) = if k = j then 1 else 0 := by
    rw [polar_comm, P.polar_dualVector]
    simp [eq_comm]
  have h4 : polar Q (b k : V) (b j : V) = 0 := P.polar_W_eq_zero _ _
  rw [P.diagonalBivector_def b, lie_bivector_bivector, h1, h2, h3, h4]
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp
    · simp [hkj, bivector_def]
  · by_cases hkj : k = j
    · subst j
      simp [hki, bivector_def]
    · simp [hki, hkj, bivector_def]

private theorem lie_diagonalBivector_bivector_dualVector_dualVector (k i j : Fin n) :
    ⁅P.diagonalBivector b k, bivector Q (P.dualVector b i : V) (P.dualVector b j : V)⁆ =
      -((if k = i then (1 : ℚ) else 0) + if k = j then 1 else 0) •
        bivector Q (P.dualVector b i : V) (P.dualVector b j : V) := by
  have h1 : polar Q (P.dualVector b k : V) (P.dualVector b i : V) = 0 :=
    P.polar_W'_eq_zero _ _
  have h2 : polar Q (b k : V) (P.dualVector b i : V) = if k = i then 1 else 0 := by
    rw [P.polar_dualVector]
  have h3 : polar Q (P.dualVector b k : V) (P.dualVector b j : V) = 0 :=
    P.polar_W'_eq_zero _ _
  have h4 : polar Q (b k : V) (P.dualVector b j : V) = if k = j then 1 else 0 := by
    rw [P.polar_dualVector]
  rw [P.diagonalBivector_def b, lie_bivector_bivector, h1, h2, h3, h4]
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp [bivector_def]
    · simp [hkj, bivector_def]
      module
  · by_cases hkj : k = j
    · subst j
      simp [hki, bivector_def]
      module
    · simp [hki, hkj, bivector_def]

/-- The diagonal Cartan bivectors act on a positive simple-root representative with the
corresponding coordinate of the Bourbaki simple root. -/
theorem lie_diagonalBivector_typeDPositiveSimpleRootBivector
    (hn : 4 ≤ n) (i k : Fin n) :
    ⁅P.diagonalBivector b k, P.typeDPositiveSimpleRootBivector b hn i⁆ =
      algebraMap ℤ ℚ (DynkinType.typeDSimpleRoot n hn i k) •
        P.typeDPositiveSimpleRootBivector b hn i := by
  rw [P.typeDPositiveSimpleRootBivector_eq b hn i]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    rw [lie_diagonalBivector_bivector_basis_dualVector,
      DynkinType.typeDSimpleRoot_of_add_one_lt hn h]
    simp [Pi.sub_apply, Pi.single_apply]
  · simp only [dite_eq_right h]
    rw [lie_diagonalBivector_bivector_basis_basis,
      DynkinType.typeDSimpleRoot_of_not_add_one_lt hn h]
    simp [Pi.add_apply, Pi.single_apply]

/-- The diagonal Cartan bivectors act on a negative simple-root representative with the negative
of the corresponding Bourbaki simple-root coordinate. -/
theorem lie_diagonalBivector_typeDNegativeSimpleRootBivector
    (hn : 4 ≤ n) (i k : Fin n) :
    ⁅P.diagonalBivector b k, P.typeDNegativeSimpleRootBivector b hn i⁆ =
      -algebraMap ℤ ℚ (DynkinType.typeDSimpleRoot n hn i k) •
        P.typeDNegativeSimpleRootBivector b hn i := by
  rw [P.typeDNegativeSimpleRootBivector_eq b hn i]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    rw [lie_diagonalBivector_bivector_basis_dualVector,
      DynkinType.typeDSimpleRoot_of_add_one_lt hn h]
    simp [Pi.sub_apply, Pi.single_apply]
  · simp only [dite_eq_right h]
    rw [lie_diagonalBivector_bivector_dualVector_dualVector,
      DynkinType.typeDSimpleRoot_of_not_add_one_lt hn h]
    simp [Pi.add_apply, Pi.single_apply]
    module

/-- The positive and negative representatives have the standard type-`D` Chevalley
normalization. Their bracket is the simple coroot: `Hᵢ - Hᵢ₊₁` along the chain and
`Hₙ₋₂ + Hₙ₋₁` at the fork. -/
theorem lie_typeDPositiveSimpleRootBivector_typeDNegativeSimpleRootBivector
    (hn : 4 ≤ n) (i : Fin n) :
    ⁅P.typeDPositiveSimpleRootBivector b hn i,
        P.typeDNegativeSimpleRootBivector b hn i⁆ =
      if h : (i : ℕ) + 1 < n then
        P.diagonalBivector b i - P.diagonalBivector b ⟨(i : ℕ) + 1, h⟩
      else
        P.diagonalBivector b ⟨n - 2, by omega⟩ +
          P.diagonalBivector b ⟨n - 1, by omega⟩ := by
  rw [P.typeDPositiveSimpleRootBivector_eq b hn i,
    P.typeDNegativeSimpleRootBivector_eq b hn i]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    have h1 : polar Q (P.dualVector b ⟨(i : ℕ) + 1, h⟩ : V)
        (b ⟨(i : ℕ) + 1, h⟩ : V) = 1 := by
      rw [polar_comm, P.polar_dualVector_self]
    have h2 : polar Q (b i : V) (b ⟨(i : ℕ) + 1, h⟩ : V) = 0 :=
      P.polar_W_eq_zero _ _
    have h3 : polar Q (P.dualVector b ⟨(i : ℕ) + 1, h⟩ : V)
        (P.dualVector b i : V) = 0 := P.polar_W'_eq_zero _ _
    have h4 : polar Q (b i : V) (P.dualVector b i : V) = 1 :=
      P.polar_dualVector_self b i
    rw [lie_bivector_bivector, h1, h2, h3, h4, P.diagonalBivector_def,
      P.diagonalBivector_def]
    simp [bivector_def]
    module
  · simp only [dite_eq_right h]
    have hpell : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp only at this
      omega
    have h1 : polar Q (b ⟨n - 1, by omega⟩ : V)
        (P.dualVector b ⟨n - 1, by omega⟩ : V) = 1 :=
      P.polar_dualVector_self b _
    have h2 : polar Q (b ⟨n - 2, by omega⟩ : V)
        (P.dualVector b ⟨n - 1, by omega⟩ : V) = 0 := by
      rw [P.polar_dualVector]
      simp only [ite_eq_right hpell]
    have h3 : polar Q (b ⟨n - 1, by omega⟩ : V)
        (P.dualVector b ⟨n - 2, by omega⟩ : V) = 0 := by
      rw [P.polar_dualVector]
      simp only [ite_eq_right hpell.symm]
    have h4 : polar Q (b ⟨n - 2, by omega⟩ : V)
        (P.dualVector b ⟨n - 2, by omega⟩ : V) = 1 :=
      P.polar_dualVector_self b _
    rw [lie_bivector_bivector, h1, h2, h3, h4, P.diagonalBivector_def,
      P.diagonalBivector_def]
    simp [bivector_def]
    module

/-- Positive simple-root bivectors preserve the coordinate integral spinor lattice. -/
theorem typeDPositiveSimpleRootBivector_mem_integralSpinActionSubring
    (hn : 4 ≤ n) (i : Fin n) :
    P.typeDPositiveSimpleRootBivector b hn i ∈ P.integralSpinActionSubring b := by
  rw [typeDPositiveSimpleRootBivector]
  split
  · exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b _)
      (P.ι_dualVector_mem_integralSpinActionSubring b _)
  · exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b _)
      (P.ι_basis_mem_integralSpinActionSubring b _)

/-- Negative simple-root bivectors preserve the coordinate integral spinor lattice. -/
theorem typeDNegativeSimpleRootBivector_mem_integralSpinActionSubring
    (hn : 4 ≤ n) (i : Fin n) :
    P.typeDNegativeSimpleRootBivector b hn i ∈ P.integralSpinActionSubring b := by
  rw [typeDNegativeSimpleRootBivector]
  split
  · exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b _)
      (P.ι_dualVector_mem_integralSpinActionSubring b _)
  · exact mul_mem (P.ι_dualVector_mem_integralSpinActionSubring b _)
      (P.ι_dualVector_mem_integralSpinActionSubring b _)

private theorem ι_mul_ι_mul_self_eq_zero {x y : V} (hx : Q x = 0)
    (hxy : polar Q x y = 0) :
    (ι Q x * ι Q y) * (ι Q x * ι Q y) = 0 := by
  have hyx : polar Q y x = 0 := by simpa [polar_comm] using hxy
  calc
    (ι Q x * ι Q y) * (ι Q x * ι Q y) =
        ι Q x * (ι Q y * ι Q x) * ι Q y := by simp only [mul_assoc]
    _ = ι Q x * (-(ι Q x * ι Q y)) * ι Q y := by
      rw [ι_mul_ι_comm (Q := Q) y x, hyx, map_zero, zero_sub]
    _ = -(ι Q x * ι Q x) * (ι Q y * ι Q y) := by noncomm_ring
    _ = 0 := by rw [ι_sq_scalar, hx, map_zero, neg_zero, zero_mul]

/-- Every positive type-`D` simple-root bivector squares to zero in the Clifford algebra. -/
theorem typeDPositiveSimpleRootBivector_sq (hn : 4 ≤ n) (i : Fin n) :
    P.typeDPositiveSimpleRootBivector b hn i *
        P.typeDPositiveSimpleRootBivector b hn i = 0 := by
  rw [typeDPositiveSimpleRootBivector]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    apply ι_mul_ι_mul_self_eq_zero
    · exact P.isotropic_W _
    · rw [P.polar_dualVector]
      simp [Fin.ext_iff]
  · simp only [dite_eq_right h]
    apply ι_mul_ι_mul_self_eq_zero
    · exact P.isotropic_W _
    · exact P.polar_W_eq_zero _ _

/-- Every negative type-`D` simple-root bivector squares to zero in the Clifford algebra. -/
theorem typeDNegativeSimpleRootBivector_sq (hn : 4 ≤ n) (i : Fin n) :
    P.typeDNegativeSimpleRootBivector b hn i *
        P.typeDNegativeSimpleRootBivector b hn i = 0 := by
  rw [typeDNegativeSimpleRootBivector]
  by_cases h : (i : ℕ) + 1 < n
  · simp only [dite_eq_left h]
    apply ι_mul_ι_mul_self_eq_zero
    · exact P.isotropic_W _
    · rw [P.polar_dualVector]
      simp [Fin.ext_iff]
  · simp only [dite_eq_right h]
    apply ι_mul_ι_mul_self_eq_zero
    · exact P.isotropic_W' _
    · exact P.polar_W'_eq_zero _ _

/-- A positive type-`D` simple-root bivector acts by a square-zero endomorphism on spinors. -/
theorem spinAction_typeDPositiveSimpleRootBivector_sq (hn : 4 ≤ n) (i : Fin n) :
    spinAction Q P (P.typeDPositiveSimpleRootBivector b hn i) *
        spinAction Q P (P.typeDPositiveSimpleRootBivector b hn i) = 0 := by
  rw [← map_mul, P.typeDPositiveSimpleRootBivector_sq b hn i, map_zero]

/-- A negative type-`D` simple-root bivector acts by a square-zero endomorphism on spinors. -/
theorem spinAction_typeDNegativeSimpleRootBivector_sq (hn : 4 ≤ n) (i : Fin n) :
    spinAction Q P (P.typeDNegativeSimpleRootBivector b hn i) *
        spinAction Q P (P.typeDNegativeSimpleRootBivector b hn i) = 0 := by
  rw [← map_mul, P.typeDNegativeSimpleRootBivector_sq b hn i, map_zero]

end TauCeti.SpinPolarizationData
