/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinants of the classical Cartan matrices of types `B` and `C` are even

Mathlib computes the determinant of `CartanMatrix.E n`, and hence of the three exceptional
matrices `E₆`, `E₇` and `E₈`, and evaluates `F₄` and `G₂` directly;
`TauCeti.LinearAlgebra.Matrix.Cartan.TypeA` adds `(CartanMatrix.A n).det = n + 1`, and
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots` adds
`(CartanMatrix.D n).det = 4`. The remaining classical families `B` and `C` are covered here, but
only up to the divisibility that a consumer of unimodularity needs: both determinants are even.

Only a mod-two calculation is required, and no recursion in the rank. In `CartanMatrix.B n` the
last node is joined to its neighbour by an arrow of weight `-2`, so the whole final column is even,
which forces the determinant of the reduced matrix to vanish; `CartanMatrix.C n` is its transpose.

The exact values are `2` and `2`. They are not proved here, since divisibility by two is
what a unimodularity question consumes.

## Main results

* `CartanMatrix.two_dvd_det_B` and `CartanMatrix.two_dvd_det_C`: the determinants of the rank-`n`
  classical Cartan matrices of types `B` and `C` are even.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II--III.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.

The consumer is the unimodularity criterion of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.RootLattice`, which decides whether the
root lattice of a pinned simply connected root datum is the whole character lattice.
-/

public section

namespace CartanMatrix

open Matrix

/-- An integer matrix whose reduction modulo two is singular has an even determinant. -/
private theorem two_dvd_det_of_map_det_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (h : (M.map (Int.castRingHom (ZMod 2))).det = 0) : (2 : ℤ) ∣ M.det := by
  have hdet := (Int.castRingHom (ZMod 2)).map_det M
  rw [show (Int.castRingHom (ZMod 2)).mapMatrix M = M.map (Int.castRingHom (ZMod 2)) from rfl,
    h] at hdet
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd M.det 2).mp (by simpa using hdet)

/-- **The determinant of the type `B` Cartan matrix is even.** Its final column carries only the
diagonal entry `2` and the arrow entry `-2`, so it vanishes modulo two. -/
theorem two_dvd_det_B {n : ℕ} (hn : 0 < n) : (2 : ℤ) ∣ (B n).det := by
  refine two_dvd_det_of_map_det_eq_zero
    (Matrix.det_eq_zero_of_column_eq_zero ⟨n - 1, by omega⟩ fun i => ?_)
  have hi := i.isLt
  have hdvd : (2 : ℤ) ∣ B n i ⟨n - 1, by omega⟩ := by
    simp only [B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  obtain ⟨c, hc⟩ := hdvd
  simp only [Matrix.map_apply, hc, map_mul]
  rw [show (Int.castRingHom (ZMod 2)) 2 = 0 by decide, zero_mul]

/-- **The determinant of the type `C` Cartan matrix is even.** It is the transpose of the type `B`
Cartan matrix of the same rank. -/
theorem two_dvd_det_C {n : ℕ} (hn : 0 < n) : (2 : ℤ) ∣ (C n).det := by
  rw [← B_transpose, Matrix.det_transpose]
  exact two_dvd_det_B hn

end CartanMatrix
