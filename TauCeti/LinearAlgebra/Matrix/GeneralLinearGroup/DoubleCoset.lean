/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Determinants along a double coset of `GL ι R`

The determinant is constant on a double coset `H₁ g H₂` as soon as every coefficient has
determinant one. Nothing here is arithmetic: the argument is multiplicativity of `Matrix.det`,
so it holds over any commutative ring and any finite index type.

The arithmetic consumers — `SL_n(ℤ)` and the congruence subgroups inside it — specialise this
in `TauCeti.NumberTheory.HeckeRing.GLn.Basic`.

## Main results

* `DoubleCoset.det_eq_of_mem_doubleCoset_of_det_eq_one`: the determinant is constant on a
  double coset with determinant-one coefficients.
-/

public section

open Matrix

namespace DoubleCoset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The determinant is constant on a double coset whose coefficients all have determinant one
— the only property of the coefficient subgroups the argument uses. -/
lemma det_eq_of_mem_doubleCoset_of_det_eq_one {H₁ H₂ : Subgroup (GL ι R)}
    (h₁ : ∀ γ ∈ H₁, (↑γ : Matrix ι ι R).det = 1)
    (h₂ : ∀ γ ∈ H₂, (↑γ : Matrix ι ι R).det = 1) {a b : GL ι R}
    (hb : b ∈ DoubleCoset.doubleCoset a H₁ H₂) :
    (↑b : Matrix ι ι R).det = (↑a : Matrix ι ι R).det := by
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, h₁ γ₁ hγ₁, h₂ γ₂ hγ₂,
    one_mul, mul_one]

end DoubleCoset
