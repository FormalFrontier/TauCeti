/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Radical API for quadratic forms

This file records basic properties of the radical of a quadratic form (such as its invariance under
negation and orthogonal products) and general consequences of nondegeneracy, together with the two
facts about the
quadratic form `x ↦ B x x` of a *symmetric* bilinear form `B` that a Clifford construction consumes:
its polar form is `2 • B`, and nondegeneracy passes from `B` to it as soon as `2` is invertible.

## Main results

* `QuadraticMap.radical_neg`: negating a quadratic map does not change its radical.
* `QuadraticMap.radical_prod`: the radical of an orthogonal product is the product of the radicals.
* `QuadraticMap.Nondegenerate.ne_zero`: a nondegenerate quadratic form on a nontrivial module is
  nonzero.
* `LinearMap.BilinMap.polarBilin_toQuadraticMap_of_flip`: the polar form of the quadratic form of a
  symmetric bilinear form `B` is `2 • B`.
* `LinearMap.BilinForm.radical_toQuadraticMap`: the radical of the quadratic form of a symmetric
  bilinear form `B` equals the kernel of `B`.
* `LinearMap.BilinForm.Nondegenerate.toQuadraticMap`: over a ring in which `2` is invertible, the
  quadratic form of a nondegenerate symmetric bilinear form is nondegenerate.
-/

public section

namespace QuadraticMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

/-- Negating a quadratic map does not change its radical. -/
@[simp]
theorem radical_neg (Q : QuadraticMap R M P) : (-Q).radical = Q.radical := by
  ext x
  simp only [QuadraticMap.mem_radical_iff', neg_apply, neg_eq_zero, neg_inj]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- The radical of an orthogonal product is the product of the two radicals when two is
invertible. -/
@[simp]
theorem radical_prod [Invertible (2 : R)] (Q : QuadraticMap R M P) (Q' : QuadraticMap R M' P) :
    (Q.prod Q').radical = Q.radical.prod Q'.radical := by
  rw [radical_eq_ker_polarBilin, radical_eq_ker_polarBilin, radical_eq_ker_polarBilin]
  ext p
  simp only [Submodule.mem_prod, LinearMap.mem_ker, LinearMap.ext_iff,
    LinearMap.zero_apply]
  constructor
  · intro hp
    exact ⟨fun x ↦ by simpa using hp (x, 0), fun x ↦ by simpa using hp (0, x)⟩
  · rintro ⟨hp, hp'⟩ x
    simpa using congrArg₂ (· + ·) (hp x.1) (hp' x.2)

end QuadraticMap

namespace QuadraticMap.Nondegenerate

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A nondegenerate quadratic form on a nontrivial module is nonzero. -/
theorem ne_zero [Nontrivial M] {Q : QuadraticForm R M} (hQ : Q.Nondegenerate) : Q ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  apply hv
  have hm : v ∈ Q.radical := by
    rw [hzero, QuadraticMap.mem_radical_iff']
    simp
  rwa [hQ.radical_eq_bot, Submodule.mem_bot] at hm

end QuadraticMap.Nondegenerate

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- **The polar form of the quadratic form of a symmetric bilinear form `B` is `2 • B`.** The polar
form is `B + B.flip`, so symmetry collapses it. -/
theorem BilinMap.polarBilin_toQuadraticMap_of_flip {B : LinearMap.BilinMap R M N}
    (hB : LinearMap.flip B = B) :
    QuadraticMap.polarBilin B.toQuadraticMap = (2 : R) • B := by
  rw [BilinMap.polarBilin_toQuadraticMap, hB, two_smul]

/-- The radical of the quadratic form of a symmetric bilinear form equals the kernel of the
bilinear form over a commutative ring in which `2` is invertible. -/
theorem BilinForm.radical_toQuadraticMap [Invertible (2 : R)] (B : LinearMap.BilinForm R M)
    (hB : B.IsSymm) :
    B.toQuadraticMap.radical = B.ker := by
  rw [QuadraticMap.radical_eq_ker_associated,
    QuadraticMap.associated_left_inverse (S := R) hB.eq]

/-- **Nondegeneracy passes from a symmetric bilinear form to its quadratic form** over a ring in
which `2` is invertible. Some hypothesis on `2` is needed: a quadratic form is a finer invariant
than its polar form, and it is the bilinear form, not the polar form `2 • B`, that is assumed
nondegenerate here. -/
theorem BilinForm.Nondegenerate.toQuadraticMap [Invertible (2 : R)] {B : LinearMap.BilinForm R M}
    (hB : B.Nondegenerate) (hflip : LinearMap.flip B = B) :
    (BilinMap.toQuadraticMap B).Nondegenerate := by
  have h2 : IsUnit (2 : R) := isUnit_of_invertible 2
  obtain ⟨hl, hr⟩ := hB
  rw [← QuadraticMap.nondegenerate_polar_iff, BilinMap.polarBilin_toQuadraticMap_of_flip hflip]
  refine ⟨fun x hx => hl x fun y => ?_, fun y hy => hr y fun x => ?_⟩
  · simpa only [LinearMap.smul_apply, smul_eq_mul, h2.mul_right_eq_zero] using hx y
  · simpa only [LinearMap.smul_apply, smul_eq_mul, h2.mul_right_eq_zero] using hy x

end LinearMap
