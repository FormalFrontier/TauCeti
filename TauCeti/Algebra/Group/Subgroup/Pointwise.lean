/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Conjugating a subgroup by a group element

Mathlib writes the conjugate `sHs⁻¹` of a subgroup `H` of a group `G` as the pointwise scalar
action `MulAut.conj s • H`.  This file records the membership criterion for that subgroup and the
two laws making `s ↦ MulAut.conj s • (-)` an action of `G` on the subgroups of `G`.

`Subgroup.mem_pointwise_smul_iff_inv_smul_mem` fixes the orientation: membership of `x` in
`MulAut.conj s • H` is `s⁻¹ * x * s ∈ H`, so `MulAut.conj s • H` is `sHs⁻¹` and not `s⁻¹Hs`.
`TauCeti.mem_conj_smul` pins that reading in the form the conjugate representation
(`TauCeti.RepresentationTheory.Induction.Conjugate`) and the Mackey subgroup
(`TauCeti.RepresentationTheory.Induction.Mackey.Subgroup`) consume, so neither can be silently
orientation-reversed.

## Main statements

* `TauCeti.mem_conj_smul`: membership in `sHs⁻¹` is `s⁻¹ * x * s ∈ H`.
* `TauCeti.conj_one_smul`, `TauCeti.conj_mul_smul`, `TauCeti.conj_inv_smul_smul`: conjugation of
  subgroups is an action of `G`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- Membership in `sHs⁻¹`, in the conjugation convention `MulAut.conj s • H`. -/
@[simp]
theorem mem_conj_smul (s : G) (H : Subgroup G) (x : G) :
    x ∈ (MulAut.conj s • H : Subgroup G) ↔ s⁻¹ * x * s ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

/-- Conjugating a subgroup by `1` leaves it unchanged. -/
theorem conj_one_smul (H : Subgroup G) : MulAut.conj (1 : G) • H = H := by
  simp

/-- Conjugating a subgroup by `s * t` is conjugating by `t` and then by `s`. -/
theorem conj_mul_smul (s t : G) (H : Subgroup G) :
    MulAut.conj (s * t) • H = MulAut.conj s • (MulAut.conj t • H) := by
  rw [map_mul, mul_smul]

/-- Conjugating a subgroup by `s⁻¹` undoes conjugating it by `s`. -/
theorem conj_inv_smul_smul (s : G) (H : Subgroup G) :
    MulAut.conj s⁻¹ • (MulAut.conj s • H) = H := by
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

end TauCeti
