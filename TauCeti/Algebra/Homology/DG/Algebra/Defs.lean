/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Differential graded algebras

A differential graded algebra over a commutative ring `R` is a `ℤ`-graded `R`-algebra `A` together
with an `R`-linear differential `d` of degree `+1` which squares to zero and satisfies the graded
Leibniz rule

`d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.

This file fixes that structure and proves elementary consequences of the degree and Leibniz
axioms: the differential annihilates the image of the ground ring, it commutes with the homogeneous
projections of the grading up to the shift of degrees by one, and the Leibniz rule extends from a
homogeneous left factor to an arbitrary one as soon as the other factor is a cycle.

The grading is stored *internally*, as a family `𝒜 : ℤ → Submodule R A` of submodules of a single
carrier `A` with Mathlib's `GradedAlgebra 𝒜`.  This is the presentation the `DGAInfinity` roadmap
prescribes when "multiplication is easier on a total module": the product is the product of `A`, so
no signed totalization is needed to state the Leibniz rule, and `Int.negOnePow` carries the only
sign.  The cochain-complex presentation, in which the same data is a monoid object in
`CochainComplex (ModuleCat R) ℤ`, is a separate spelling; the comparison between the two is not part
of this file.

Only a homogeneous *left* factor is constrained by the Leibniz axiom, because the sign depends on
its degree alone.  Decomposing into homogeneous components extends the Leibniz rule to an arbitrary
left factor against a cycle, and shows that a cycle times a boundary is a boundary.

## Main definitions

* `TauCeti.IsDGAlgebra`: the differential graded algebra axioms on an internally `ℤ`-graded
  `R`-algebra and an `R`-linear endomorphism of its carrier.

## Main results

* `TauCeti.IsDGAlgebra.map_one_eq_zero` and `TauCeti.IsDGAlgebra.map_algebraMap`: the differential
  annihilates the unit and, more generally, the image of the ground ring.
* `TauCeti.IsDGAlgebra.map_proj`: the differential commutes with the homogeneous projections of
  the grading, `d (proj p a) = proj (p + 1) (d a)`; in particular the homogeneous components of a
  cycle are cycles.
* `TauCeti.IsDGAlgebra.leibniz_of_map_right_eq_zero`: the Leibniz rule for an arbitrary left
  factor against a cycle.
* `TauCeti.IsDGAlgebra.mul_map_mem_range_of_map_left_eq_zero`: a cycle times a boundary is a
  boundary; a boundary times a cycle is one by the previous item.
* `TauCeti.isDGAlgebra_zero`: a graded algebra with zero differential is a differential graded
  algebra.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 1, item "DG algebras, categories,
modules, and bimodules", specifically its first request to "define nonunital, unital, and augmented
DG algebras on graded `k`-modules ... cycles, boundaries, and the induced graded cohomology
algebra".  Cycles, boundaries and the cohomology algebra are built on this file in
`TauCeti.Algebra.Homology.DG.Algebra.Cohomology`.  No formalization is vendored: the internal
grading, its decomposition and its projections are Mathlib's `GradedAlgebra` API.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

open DirectSum

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A **differential graded algebra**: an internally `ℤ`-graded `R`-algebra `𝒜` on a carrier `A`
together with an `R`-linear map `d` which raises degree by one, squares to zero, and satisfies the
graded Leibniz rule on a homogeneous left factor.  The sign `(-1) ^ p` is `Int.negOnePow p`, acting
through the units of `ℤ`. -/
structure IsDGAlgebra (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) : Prop where
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)
  /-- The differential squares to zero. -/
  sq_zero (a : A) : d (d a) = 0
  /-- The graded Leibniz rule for a left factor of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)

attribute [grind =>] IsDGAlgebra.map_mem

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

namespace IsDGAlgebra

/-- The differential of a differential graded algebra annihilates the unit: the Leibniz rule for
`1 * 1` reads `d 1 = d 1 + d 1`. -/
theorem map_one_eq_zero (h : IsDGAlgebra 𝒜 d) : d 1 = 0 := by
  have key := h.leibniz (SetLike.one_mem_graded 𝒜) 1
  simp only [mul_one, one_mul, Int.negOnePow_zero, one_smul] at key
  exact left_eq_add.mp key

/-- The differential of a differential graded algebra annihilates the image of the ground ring. -/
theorem map_algebraMap (h : IsDGAlgebra 𝒜 d) (r : R) : d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h.map_one_eq_zero, smul_zero]

/-- The differential commutes with the homogeneous projections of the grading, up to the shift by
one that it applies to degrees. -/
theorem map_proj (h : IsDGAlgebra 𝒜 d) (p : ℤ) (a : A) :
    d (GradedRing.proj 𝒜 p a) = GradedRing.proj 𝒜 (p + 1) (d a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q x =>
    have hx : (x : A) ∈ 𝒜 q := x.2
    have hdx : d (x : A) ∈ 𝒜 (q + 1) := h.map_mem hx
    by_cases hpq : p = q
    · subst hpq
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜 hdx]
    · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hx (fun hq => hpq hq.symm),
        map_zero, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne 𝒜 hdx (fun hq => hpq (by omega))]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every homogeneous projection of a boundary is again a boundary. -/
theorem proj_mem_range (h : IsDGAlgebra 𝒜 d) {a : A} (ha : a ∈ LinearMap.range d) (p : ℤ) :
    GradedRing.proj 𝒜 p a ∈ LinearMap.range d := by
  obtain ⟨b, rfl⟩ := ha
  exact ⟨GradedRing.proj 𝒜 (p - 1) b, by simpa using h.map_proj (p - 1) b⟩

/-- The homogeneous components of a cycle are cycles. -/
theorem map_proj_eq_zero (h : IsDGAlgebra 𝒜 d) {a : A} (ha : d a = 0) (p : ℤ) :
    d (GradedRing.proj 𝒜 p a) = 0 := by
  rw [h.map_proj, ha, map_zero]

/-- The Leibniz rule against a cycle on the right: the sign disappears with the term it multiplies,
so the left factor need not be homogeneous. -/
theorem leibniz_of_map_right_eq_zero (h : IsDGAlgebra 𝒜 d) (a : A) {b : A} (hb : d b = 0) :
    d (a * b) = d a * b := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_mul, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h.leibniz (SetLike.coe_mem _) b, hb, mul_zero, smul_zero, add_zero]

/-- The product of two cycles is a cycle. -/
theorem map_mul_eq_zero_of_map_eq_zero (h : IsDGAlgebra 𝒜 d) {a b : A}
    (ha : d a = 0) (hb : d b = 0) :
    d (a * b) = 0 := by
  rw [h.leibniz_of_map_right_eq_zero a hb, ha, zero_mul]

/-- A homogeneous cycle times a boundary is, up to the sign of the cycle's degree, the
differential of the product. -/
theorem mul_map_eq_negOnePow_smul_map_mul (h : IsDGAlgebra 𝒜 d) {p : ℤ} {a : A}
    (ha : a ∈ 𝒜 p) (hda : d a = 0) (b : A) :
    a * d b = p.negOnePow • d (a * b) := by
  simp only [h.leibniz ha b, hda, zero_mul, zero_add, smul_smul, Int.units_mul_self, one_smul]

/-- A cycle times a boundary is a boundary.  Componentwise this is the Leibniz rule read backwards:
`x * d b = (-1) ^ |x| * d (x * b)` when `x` is a homogeneous cycle. -/
theorem mul_map_mem_range_of_map_left_eq_zero (h : IsDGAlgebra 𝒜 d) {a : A}
    (ha : d a = 0) (b : A) :
    a * d b ∈ LinearMap.range d := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_mul]
  refine Submodule.sum_mem _ fun p _ => ⟨p.negOnePow • ((decompose 𝒜 a p : A) * b), ?_⟩
  rw [Units.smul_def, map_zsmul, ← Units.smul_def]
  exact
    (h.mul_map_eq_negOnePow_smul_map_mul (SetLike.coe_mem _) (h.map_proj_eq_zero ha p) b).symm

end IsDGAlgebra

/-- A `ℤ`-graded algebra with zero differential is a differential graded algebra. -/
theorem isDGAlgebra_zero (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :
    IsDGAlgebra 𝒜 (0 : A →ₗ[R] A) where
  map_mem := fun _ => zero_mem _
  sq_zero _ := rfl
  leibniz := fun _ _ => by simp

end TauCeti
