/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Corners cut out by two idempotents

Let `A` be an algebra over a commutative semiring `k`. This file defines the corner `eAf` as the
range of the `k`-linear map `x ↦ e * x * f`. When `e` and `f` are idempotent, membership is
equivalent to the fixed-point equation `e * x * f = x`.

## Main definitions

* `TauCeti.cornerMap`: the `k`-linear map `x ↦ e * x * f`.
* `TauCeti.cornerSubmodule`: the corner `eAf`, as a `k`-submodule of `A`.

## Main results

* `TauCeti.mem_cornerSubmodule_iff`: the fixed-point characterization of an idempotent corner.

## References

This is the corner infrastructure used by Layer 3 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See I. Assem, D. Simson, A. Skowroński,
*Elements of the Representation Theory of Associative Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v

variable (k : Type v) [CommSemiring k] {A : Type u} [Semiring A] [Algebra k A]

/-- Cutting an element of `A` down to the corner at `(e, f)`: multiplying it by `e` on the left
and by `f` on the right. -/
def cornerMap (e f : A) : A →ₗ[k] A :=
  (LinearMap.mulLeft k e).comp (LinearMap.mulRight k f)

@[simp]
theorem cornerMap_apply (e f x : A) : cornerMap k e f x = e * x * f :=
  (mul_assoc _ _ _).symm

/-- **The corner `eAf`**, as a `k`-submodule of `A`: the range of the map `x ↦ e * x * f`. -/
def cornerSubmodule (e f : A) : Submodule k A :=
  LinearMap.range (cornerMap k e f)

/-- For idempotents `e` and `f`, an element belongs to the corner `eAf` exactly when multiplying it
by `e` on the left and by `f` on the right fixes it. -/
@[simp]
theorem mem_cornerSubmodule_iff {e f x : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : x ∈ cornerSubmodule k e f ↔ e * x * f = x := by
  constructor
  · rintro ⟨y, rfl⟩
    simp only [cornerMap_apply]
    calc
      e * (e * y * f) * f = (e * e) * y * (f * f) := by simp only [mul_assoc]
      _ = e * y * f := by rw [he.eq, hf.eq]
  · intro h
    exact ⟨x, by simpa only [cornerMap_apply] using h⟩

variable {k}

/-- An element of the corner `eAf` is fixed by `e` on the left. -/
theorem mul_eq_self_of_mem_cornerSubmodule {e f x : A} (he : IsIdempotentElem e)
    (hx : x ∈ cornerSubmodule k e f) : e * x = x := by
  rcases hx with ⟨y, rfl⟩
  simp only [cornerMap_apply]
  calc
    e * (e * y * f) = (e * (e * y)) * f := (mul_assoc _ _ _).symm
    _ = (e * e) * y * f := by rw [← mul_assoc e e y]
    _ = e * y * f := by rw [he.eq]

/-- An element of the corner `eAf` is fixed by `f` on the right. -/
theorem mul_eq_self_of_mem_cornerSubmodule_right {e f x : A} (hf : IsIdempotentElem f)
    (hx : x ∈ cornerSubmodule k e f) : x * f = x := by
  rcases hx with ⟨y, rfl⟩
  simp only [cornerMap_apply]
  rw [mul_assoc, hf.eq]

end TauCeti
