/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# The identity double coset

Two elements have the same class in `H \ G / K` exactly when one lies in the double coset of the
other (`TauCeti.doubleCosetMk_eq_mk_iff_mem`).  Among those classes the class of `1` is
distinguished: its double coset is the set `H * K` (`TauCeti.doubleCoset_one_eq_mul`), so a double
coset is the identity one exactly when its representative lies there
(`TauCeti.doubleCosetMk_eq_mk_one_iff`).  For `K = H` that set is `H`
(`TauCeti.doubleCoset_one_self`) and the condition reads `s ∈ H`
(`TauCeti.doubleCosetMk_eq_mk_one_iff_mem`), which is what lets a statement quantified over the
non-identity double cosets `H \ G / H` be rewritten as a statement quantified over the elements
outside `H`.

## Main statements

* `TauCeti.doubleCosetMk_eq_mk_iff_mem`: the double cosets of `s` and `a` agree exactly when
  `s ∈ H a K`.
* `TauCeti.doubleCoset_one_eq_mul` and `TauCeti.doubleCoset_one_self`: the identity double coset is
  `H * K`, which for `K = H` is `H`.
* `TauCeti.doubleCosetMk_eq_mk_one_iff`: the double coset of `s` is the identity one exactly when
  `s ∈ H * K`.
* `TauCeti.doubleCosetMk_eq_mk_one_iff_mem`: for `K = H`, that condition is `s ∈ H`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Two elements have the same double coset exactly when one lies in the double coset of the
other**: `HsK = HaK` if and only if `s ∈ HaK`.  This is `DoubleCoset.eq` read through
`DoubleCoset.mem_doubleCoset`. -/
theorem doubleCosetMk_eq_mk_iff_mem (H K : Subgroup G) (a s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K a ↔
      s ∈ DoubleCoset.doubleCoset a (H : Set G) (K : Set G) := by
  rw [eq_comm, DoubleCoset.eq, DoubleCoset.mem_doubleCoset]
  simp

/-- **The identity double coset is the set `H * K`**: multiplying `1` by `H` on the left and `K` on
the right leaves the product of the two subgroups. -/
theorem doubleCoset_one_eq_mul (H K : Subgroup G) :
    DoubleCoset.doubleCoset (1 : G) (H : Set G) (K : Set G) = (H : Set G) * K := by
  simp [DoubleCoset.doubleCoset]

/-- **The identity double coset of `H \ G / H` is `H` itself.**  This is
`TauCeti.doubleCoset_one_eq_mul` for `K = H`, where the set `H * H` is `H`. -/
@[simp]
theorem doubleCoset_one_self (H : Subgroup G) :
    DoubleCoset.doubleCoset (1 : G) (H : Set G) (H : Set G) = (H : Set G) := by
  rw [doubleCoset_one_eq_mul, coe_mul_coe]

/-- **A double coset is the identity one exactly when its representative lies in `H * K`**:
`HsK = H · 1 · K` if and only if `s = a * b` with `a ∈ H` and `b ∈ K`. -/
theorem doubleCosetMk_eq_mk_one_iff (H K : Subgroup G) (s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K 1 ↔ s ∈ (H : Set G) * K := by
  rw [doubleCosetMk_eq_mk_iff_mem, doubleCoset_one_eq_mul]

/-- **The identity double coset of `H \ G / H` is the class of the elements of `H`.**  This is
`TauCeti.doubleCosetMk_eq_mk_one_iff` for `K = H`, where the condition `s ∈ H * H` is `s ∈ H`. -/
@[simp]
theorem doubleCosetMk_eq_mk_one_iff_mem (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [doubleCosetMk_eq_mk_one_iff, coe_mul_coe, SetLike.mem_coe]

end TauCeti
