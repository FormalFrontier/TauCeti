/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Integrality in the rational circle group

A rational number reduces to zero in `ℚ/ℤ`, realized as `AddCircle (1 : ℚ)`, exactly when it
lies in `(1 : Submodule ℤ ℚ)`, the copy of `ℤ` inside `ℚ`. This bridges the two spellings of
integrality used by the discriminant-form theory: vanishing in the circle group and membership
in the unit `ℤ`-submodule.

## Main declarations

* `AddCircle.coe_eq_zero_iff_mem_one`: vanishing in `AddCircle (1 : ℚ)` is membership in
  `(1 : Submodule ℤ ℚ)`.
* `AddCircle.coe_eq_zero_of_eq_intCast`: a rational equal to an integer reduces to zero.
* `AddCircle.zsmul_coe_eq_zero_of_mul_eq_intCast`: a rational whose integer multiple is an
  integer becomes torsion in `ℚ/ℤ`.
* `AddCircle.four_zsmul_coe_div_eight_eq_zero_of_even`: the class of `n / 8` is four-torsion
  when `n` is even.
-/

public section

namespace AddCircle

/-- A rational number reduces to zero in `ℚ/ℤ` exactly when it is an integer. -/
theorem coe_eq_zero_iff_mem_one (q : ℚ) :
    (q : AddCircle (1 : ℚ)) = 0 ↔ q ∈ (1 : Submodule ℤ ℚ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (coe_eq_zero_iff (1 : ℚ)).mp h
    exact Submodule.mem_one.mpr ⟨n, by simpa using hn⟩
  · intro h
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp h
    exact (coe_eq_zero_iff (1 : ℚ)).mpr ⟨n, by simpa using hn⟩

/-- A rational number equal to an integer reduces to zero in `ℚ/ℤ`. -/
theorem coe_eq_zero_of_eq_intCast {q : ℚ} (m : ℤ) (h : q = (m : ℚ)) :
    (q : AddCircle (1 : ℚ)) = 0 := by
  rw [coe_eq_zero_iff_mem_one]
  exact Submodule.mem_one.mpr ⟨m, by simpa using h.symm⟩

/-- A rational whose integer multiple is an integer becomes torsion in `ℚ/ℤ`. -/
theorem zsmul_coe_eq_zero_of_mul_eq_intCast {q : ℚ} (n m : ℤ)
    (h : (n : ℚ) * q = (m : ℚ)) : n • (q : AddCircle (1 : ℚ)) = 0 := by
  rw [← coe_zsmul, zsmul_eq_mul]
  exact coe_eq_zero_of_eq_intCast m h

/-- The class of `n / 8` in `ℚ/ℤ` is four-torsion when `n` is even. -/
theorem four_zsmul_coe_div_eight_eq_zero_of_even (n : ℕ) (hn : Even n) :
    (4 : ℤ) • (((n : ℚ) / 8 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  obtain ⟨k, hk⟩ := hn
  refine zsmul_coe_eq_zero_of_mul_eq_intCast 4 k ?_
  rw [hk]
  push_cast
  ring

end AddCircle
