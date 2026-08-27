/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# The linear factor `X - C x`, and its reverse

Two facts about linear factors that Mathlib does not carry.

The *reversed* factor `C x - X` — the shape that arises as `x - θ` in `AdjoinRoot f` — has degree
`1`, like `X - C x` itself, which is the form Mathlib states.

And Mathlib's `Polynomial.dvd_iff_isRoot` factors `X - C x` out of any polynomial vanishing at
`x`, but leaves the cofactor unidentified. When the polynomial has degree at most one the cofactor
is forced to be a constant, so the polynomial is `C γ * (X - C x)` for a single scalar `γ`. That
sharpened form is what is needed to read off the *coefficient* of a linear factor, which
`Polynomial.eq_X_add_C_of_natDegree_le_one` does not give once a root is prescribed.

## Main results

* `Polynomial.natDegree_C_sub_X`: the reversed linear factor `C x - X` has degree `1`.
* `Polynomial.exists_eq_C_mul_X_sub_C_of_natDegree_le_one`: a polynomial of `natDegree ≤ 1` with
  root `x` is `C γ * (X - C x)` for some `γ`.

## Provenance

`exists_eq_C_mul_X_sub_C_of_natDegree_le_one` is adapted, with the author's proof, from Michael
Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`), `EllipticCurves/Mathlib/Basic.lean`.
Its consumer is the `x - T` descent map of
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`, where it pins down the line
through a `2`-torsion point.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The reversed linear polynomial `C x - X` has degree `1`, like `X - C x`. -/
@[simp]
theorem natDegree_C_sub_X [Nontrivial R] (x : R) : (C x - X).natDegree = 1 := by
  rw [natDegree_sub, natDegree_X_sub_C]

/-- A polynomial of degree at most one with prescribed root `x` is a scalar multiple of
`X - C x`. -/
lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  nontriviality R
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]

end Polynomial

end
