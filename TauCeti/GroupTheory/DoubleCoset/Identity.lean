/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# The identity double coset

Among the double cosets `H \ G / H` the class of `1` is distinguished: it is `H` itself, and it is
the only class meeting `H`.  That is `TauCeti.doubleCosetMk_eq_mk_one_iff`, which is what lets a
statement quantified over the non-identity double cosets be rewritten as a statement quantified
over the elements outside `H`.

## Main statements

* `TauCeti.doubleCosetMk_eq_mk_one_iff`: the double coset of `s` is the identity one exactly when
  `s ∈ H`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **The identity double coset is `H` itself**: `HsH = H · 1 · H` exactly when `s ∈ H`. -/
@[simp]
theorem doubleCosetMk_eq_mk_one_iff (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [DoubleCoset.eq]
  refine ⟨fun ⟨a, ha, b, hb, hab⟩ => ?_, fun hs => ⟨1, H.one_mem, s⁻¹, H.inv_mem hs, by simp⟩⟩
  have hs : s = a⁻¹ * b⁻¹ := by
    have h' : a⁻¹ * (a * s * b) * b⁻¹ = a⁻¹ * (1 : G) * b⁻¹ := by rw [hab]
    simpa [mul_assoc] using h'
  exact hs ▸ H.mul_mem (H.inv_mem ha) (H.inv_mem hb)

end TauCeti
