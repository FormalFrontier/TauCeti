/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector

/-!
# Reversal on Clifford subalgebras

This file restricts Clifford reversal to the even subalgebra and records its action on bivectors.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- Reversal restricted to the even Clifford subalgebra. -/
def reverseEven (Q : QuadraticForm R M) : ↥(even Q) →ₗ[R] ↥(even Q) :=
  (reverse (Q := Q)).restrict (p := (even Q).toSubmodule) (q := (even Q).toSubmodule)
    (fun _x hx => (reverse_mem_evenOdd_iff Q).2 hx)

/-- Coercing the restricted reversal agrees with Clifford reversal. -/
@[simp] theorem coe_reverseEven_apply (x : ↥(even Q)) :
    (reverseEven Q x : CliffordAlgebra Q) = reverse x := by
  exact LinearMap.coe_restrict_apply (f := reverse (Q := Q))
    (fun _x hx => (reverse_mem_evenOdd_iff Q).2 hx) x

/-- On the even Clifford subalgebra, Clifford reversal agrees with Clifford `star`. -/
@[simp] theorem reverse_eq_star_of_mem_even (x : ↥(even Q)) :
    reverse (x : CliffordAlgebra Q) = star (x : CliffordAlgebra Q) := by
  rw [star_def,
    involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact x.2)]

/-- Reversal restricted to the even subalgebra fixes its unit. -/
@[simp] theorem reverseEven_map_one : reverseEven Q 1 = 1 := by
  apply Subtype.ext
  simp

/-- Reversal restricted to the even subalgebra fixes scalars. -/
@[simp] theorem reverseEven_algebraMap (r : R) :
    reverseEven Q (algebraMap R (even Q) r) = algebraMap R (even Q) r := by
  apply Subtype.ext
  simp

/-- Reversal restricted to the even subalgebra reverses products. -/
@[simp] theorem reverseEven_mul (x y : ↥(even Q)) :
    reverseEven Q (x * y) = reverseEven Q y * reverseEven Q x := by
  apply Subtype.ext
  simp only [coe_reverseEven_apply, Subalgebra.coe_mul, reverse.map_mul]

/-- Reversal restricted to the even subalgebra is an involution. -/
@[simp] theorem reverseEven_reverseEven (x : ↥(even Q)) :
    reverseEven Q (reverseEven Q x) = x := by
  apply Subtype.ext
  simpa only [coe_reverseEven_apply] using (reverse_reverse (Q := Q) (x : CliffordAlgebra Q))

section Bivector

variable [Invertible (2 : R)]

/-- Clifford reversal negates every bivector. -/
@[simp] theorem reverse_bivector (q : QuadraticForm R M) (a b : M) :
    reverse (bivector q a b) = -bivector q a b := by
  rw [bivector_def, map_smul, map_sub, reverse.map_mul, reverse.map_mul, reverse_ι, reverse_ι]
  module

/-- Clifford reversal negates the image of the exterior-square bivector map. -/
@[simp] theorem reverse_bivectorExterior (q : QuadraticForm R M) (x : ⋀[R]^2 M) :
    reverse (bivectorExterior q x) = -bivectorExterior q x := by
  let P := LinearMap.eqLocus (reverse (Q := q)) (-LinearMap.id)
  have hle : LinearMap.range (bivectorExterior q) ≤ P :=
    bivectorExterior_range_le_of_bivector_mem q P fun a b =>
      LinearMap.mem_eqLocus.2 (reverse_bivector q a b)
  exact LinearMap.mem_eqLocus.mp (hle ⟨x, rfl⟩)

end Bivector

end CliffordAlgebra
