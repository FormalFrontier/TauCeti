/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.adjugate` and its multiplicativity `Matrix.adjugate_mul_distrib` are the content.
public import Mathlib.LinearAlgebra.Matrix.Adjugate
-- `GL` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The adjugate of an invertible matrix

The adjugate of an invertible matrix is invertible, so `Matrix.adjugate` restricts to a map
`GL n R → GL n R`. Its inverse is exhibited directly, without dividing by the determinant:
`adjugate` is anti-multiplicative and sends `1` to `1`, so `adjugate g⁻¹` inverts `adjugate g`
on the nose. That keeps the construction over an arbitrary commutative ring — no field, no
`det ≠ 0` side condition, and nothing to discharge at a call site.

Over a group of determinant-one matrices it is the inverse, and in size two it is an
involution. Those are the two ingredients a Hecke-pair anti-involution needs from the adjugate;
the anti-involution itself also requires stability of the group and the monoid under the map,
which is proved where those objects live, not here.

## Main definitions

* `TauCeti.adjugateGL`: the adjugate as a map `GL n R → GL n R`.

## Main results

* `TauCeti.adjugateGL_one`, `TauCeti.adjugateGL_mul`: `adj(1) = 1` and `adj(gh) = adj(h) adj(g)`.
* `TauCeti.adjugateGL_eq_inv`: on determinant one, `adj(g) = g⁻¹`.
* `TauCeti.adjugateGL_mapGL`: on a special-linear image, `adj(mapGL σ) = mapGL σ⁻¹`.
* `TauCeti.adjugateGL_adjugateGL`: in size two, `adj` is an involution.

## References

* Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck), Apache-2.0,
  [`HeckeRIngs/GL2/HeckeActionGeneral.lean`](https://github.com/CBirkbeck/AINTLIB) at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, declarations `GL_adjugate`, `GL_adjugate_val`,
  `GL_adjugate_mul`, `GL_adjugate_involutive` and `GL_adjugate_eq_inv_of_det_one`. The source
  is stated for `GL (Fin 2) ℚ` and builds the element with a `det ≠ 0` obligation; here the
  inverse is exhibited directly, which removes that obligation and generalises the statements
  to `GL n R` over a commutative ring.
-/

public section

namespace TauCeti

open Matrix

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- **The adjugate of an invertible matrix**, again invertible.

The inverse is `adjugate g⁻¹` rather than anything built from the determinant: `adjugate` is
anti-multiplicative, so the two adjugates multiply to `adjugate (g⁻¹ g) = adjugate 1 = 1`. -/
def adjugateGL (g : GL n R) : GL n R where
  val := adjugate (g : Matrix n n R)
  inv := adjugate ((g⁻¹ : GL n R) : Matrix n n R)
  val_inv := by rw [← adjugate_mul_distrib, Units.inv_mul, adjugate_one]
  inv_val := by rw [← adjugate_mul_distrib, Units.mul_inv, adjugate_one]

@[simp] lemma adjugateGL_val (g : GL n R) :
    (adjugateGL g : Matrix n n R) = adjugate (g : Matrix n n R) := by rfl

/-- **The adjugate fixes the identity.** -/
@[simp] lemma adjugateGL_one : adjugateGL (1 : GL n R) = 1 := by
  ext
  simp [adjugateGL_val]

/-- **The adjugate is anti-multiplicative**, inherited entrywise from `Matrix.adjugate`. -/
@[simp] lemma adjugateGL_mul (g h : GL n R) : adjugateGL (g * h) = adjugateGL h * adjugateGL g := by
  ext
  simp [Units.val_mul, adjugate_mul_distrib]

/-- **On determinant one the adjugate is the inverse.** This is what makes it restrict to a
group of determinant-one matrices, where it is then an anti-automorphism. -/
lemma adjugateGL_eq_inv {g : GL n R} (hg : (g : Matrix n n R).det = 1) : adjugateGL g = g⁻¹ := by
  ext
  rw [adjugateGL_val, Matrix.coe_units_inv, Matrix.inv_def, hg, Ring.inverse_one, one_smul]

/-- **Adjugate is inversion on a special-linear image.** An element of `SL n R` has determinant
one in every `R`-algebra `S`, so `adjugateGL` is inversion on its image, and `mapGL S` is a
monoid map. This is `adjugateGL_eq_inv` in the form its consumers meet: the determinant
hypothesis is discharged once here rather than at each call site. -/
lemma adjugateGL_mapGL {S : Type*} [CommRing S] [Algebra R S] (σ : SpecialLinearGroup n R) :
    adjugateGL (SpecialLinearGroup.mapGL S σ) = SpecialLinearGroup.mapGL S σ⁻¹ := by
  rw [adjugateGL_eq_inv (congrArg Units.val (SpecialLinearGroup.det_mapGL (S := S) σ)), map_inv]

/-- **In size two the adjugate is an involution.** `adjugate` squares to
`det ^ (card n - 2) • id`, and the size-two hypothesis makes that exponent vanish. -/
lemma adjugateGL_adjugateGL (h2 : Fintype.card n = 2) (g : GL n R) :
    adjugateGL (adjugateGL g) = g := by
  ext
  rw [adjugateGL_val, adjugateGL_val, adjugate_adjugate _ (by rw [h2]; norm_num), h2]
  simp

end TauCeti
