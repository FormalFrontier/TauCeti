/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# The identity double coset

Among the double cosets `H \ G / K` the class of `1` is distinguished: it is the only class meeting
the set `H * K`, so a double coset is the identity one exactly when its representative lies there
(`TauCeti.doubleCosetMk_eq_mk_one_iff`).  For `K = H` that condition reads `s ∈ H`
(`TauCeti.doubleCosetMk_eq_mk_one_iff_mem`), which is what lets a statement quantified over the
non-identity double cosets `H \ G / H` be rewritten as a statement quantified over the elements
outside `H`.

## Main statements

* `TauCeti.doubleCosetMk_eq_mk_one_iff`: the double coset of `s` is the identity one exactly when
  `s ∈ H * K`.
* `TauCeti.doubleCosetMk_eq_mk_one_iff_mem`: for `K = H`, that condition is `s ∈ H`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- **A double coset is the identity one exactly when its representative lies in `H * K`**:
`HsK = H · 1 · K` if and only if `s = a * b` with `a ∈ H` and `b ∈ K`. -/
theorem doubleCosetMk_eq_mk_one_iff (H K : Subgroup G) (s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K 1 ↔ s ∈ (H : Set G) * K := by
  rw [DoubleCoset.eq, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
    have h' : a⁻¹ * (a * s * b) * b⁻¹ = a⁻¹ * (1 : G) * b⁻¹ := by rw [hab]
    simpa [mul_assoc] using h'.symm
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, by simp⟩

/-- **The identity double coset of `H \ G / H` is the class of the elements of `H`.**  This is
`TauCeti.doubleCosetMk_eq_mk_one_iff` for `K = H`, where the condition `s ∈ H * H` is `s ∈ H`. -/
@[simp]
theorem doubleCosetMk_eq_mk_one_iff_mem (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [doubleCosetMk_eq_mk_one_iff, coe_mul_coe, SetLike.mem_coe]

end TauCeti
