/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# The diagonal torus attached to a weighted basis

A basis `b : Basis ι R M` and a family of units `w : ι → Rˣ` determine the automorphism of `M`
scaling the `i`-th basis vector by `w i`. Letting `w` range over all such families realizes the
group `ι → Rˣ` — the `R`-points of the split torus `𝔾ₘ^ι` — inside the automorphism group of `M`.

Weights cut this down to a torus of smaller rank. A weight function `wt : ι → κ → ℤ` assigns to
each basis vector a character of `𝔾ₘ^κ`, and evaluating those characters at a point
`s : κ → Rˣ` gives the family of units the diagonal automorphism is built from. The resulting
homomorphism `TauCeti.basisWeightTorus` is the split maximal torus of a Chevalley group written
in a weight basis of an admissible lattice, and `TauCeti.basisDiagonal_apply_of_repr_eq_zero` is
the statement that it acts on a weight vector by the corresponding character — which is what makes
the conjugation formula against a root subgroup come out.

## Main definitions

* `TauCeti.torusCharacter`: the value at `s : κ → Rˣ` of the character `μ : κ → ℤ` of `𝔾ₘ^κ`.
* `TauCeti.basisDiagonal`: the automorphism scaling each basis vector by a prescribed unit.
* `TauCeti.basisDiagonalHom`: the resulting homomorphism from `ι → Rˣ`.
* `TauCeti.basisWeightTorus`: the homomorphism from `κ → Rˣ` determined by a weight function.

## Main results

* `TauCeti.basisDiagonal_apply_of_repr_eq_zero`: a diagonal automorphism acts by a single scalar
  on any vector whose coordinates are supported where that scalar is attained.
* `TauCeti.basisWeightTorus_apply_of_repr_eq_zero`: the special case for a weight vector.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4 and §7.1.
-/

public section

namespace TauCeti

open Finset Module

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w} {M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-! ## Characters of a split torus -/

section TorusCharacter

variable [Fintype κ]

/-- The value at the point `s` of the character `μ` of the split torus `𝔾ₘ^κ`, namely
`∏ j, s j ^ μ j`. Weights of a representation are exactly such characters, so this is the scalar
by which a torus point acts on a weight vector. -/
def torusCharacter (s : κ → Rˣ) (μ : κ → ℤ) : Rˣ := ∏ j, s j ^ μ j

/-- A split-torus character evaluates as the product of its coordinate powers. -/
theorem torusCharacter_def (s : κ → Rˣ) (μ : κ → ℤ) :
    torusCharacter s μ = ∏ j, s j ^ μ j :=
  (rfl)

/-- Writing a finite-support exponent vector as a function identifies its character value with
the corresponding finitely supported product. -/
theorem torusCharacter_equivFunOnFinite (s : κ → Rˣ) (m : κ →₀ ℤ) :
    torusCharacter s (Finsupp.equivFunOnFinite m) = m.prod fun i z ↦ s i ^ z := by
  rw [torusCharacter, Finsupp.prod_zpow]
  rfl

/-- The trivial character takes the value one at every point. -/
@[simp] theorem torusCharacter_zero (s : κ → Rˣ) : torusCharacter s (0 : κ → ℤ) = 1 := by
  simp [torusCharacter]

/-- Characters multiply when weights are added. -/
theorem torusCharacter_add (s : κ → Rˣ) (μ ν : κ → ℤ) :
    torusCharacter s (μ + ν) = torusCharacter s μ * torusCharacter s ν := by
  simp [torusCharacter, zpow_add, prod_mul_distrib]

/-- Scaling a weight by a natural number raises its value to that power. -/
theorem torusCharacter_nsmul (s : κ → Rˣ) (μ : κ → ℤ) (n : ℕ) :
    torusCharacter s (n • μ) = torusCharacter s μ ^ n := by
  simp only [torusCharacter, Pi.smul_apply, nsmul_eq_mul, ← prod_pow]
  refine prod_congr rfl fun j _ => ?_
  rw [mul_comm, zpow_mul, zpow_natCast]

/-- Negating a weight inverts the value of its character. -/
theorem torusCharacter_neg (s : κ → Rˣ) (μ : κ → ℤ) :
    torusCharacter s (-μ) = (torusCharacter s μ)⁻¹ := by
  simp [torusCharacter, ← prod_inv_distrib]

/-- Subtracting weights divides the values of their characters. -/
theorem torusCharacter_sub (s : κ → Rˣ) (μ ν : κ → ℤ) :
    torusCharacter s (μ - ν) = torusCharacter s μ / torusCharacter s ν := by
  rw [sub_eq_add_neg, torusCharacter_add, torusCharacter_neg, div_eq_mul_inv]

/-- Scaling a weight by an integer raises its value to that integer power. -/
theorem torusCharacter_zsmul (s : κ → Rˣ) (μ : κ → ℤ) (z : ℤ) :
    torusCharacter s (z • μ) = torusCharacter s μ ^ z := by
  simp only [torusCharacter, Pi.smul_apply, smul_eq_mul, ← prod_zpow]
  refine prod_congr rfl fun j _ => ?_
  rw [mul_comm, zpow_mul]

/-- Every character takes the value one at the identity point. -/
@[simp] theorem torusCharacter_one (μ : κ → ℤ) : torusCharacter (1 : κ → Rˣ) μ = 1 := by
  simp [torusCharacter]

/-- A character is a homomorphism on the points of the torus. -/
theorem torusCharacter_mul (s t : κ → Rˣ) (μ : κ → ℤ) :
    torusCharacter (s * t) μ = torusCharacter s μ * torusCharacter t μ := by
  simp [torusCharacter, mul_zpow, prod_mul_distrib]

/-- The family of characters attached to a weight function, as a homomorphism from the points of
the split torus `𝔾ₘ^κ` to families of units indexed by the basis. -/
def torusCharacterHom (wt : ι → κ → ℤ) : (κ → Rˣ) →* (ι → Rˣ) where
  toFun s i := torusCharacter s (wt i)
  map_one' := funext fun i => torusCharacter_one (R := R) (wt i)
  map_mul' s t := funext fun i => torusCharacter_mul s t (wt i)

/-- The value of the weight-character homomorphism at a point and a basis index. -/
@[simp] theorem torusCharacterHom_apply (wt : ι → κ → ℤ) (s : κ → Rˣ) (i : ι) :
    torusCharacterHom (R := R) wt s i = torusCharacter s (wt i) := (rfl)

/-- Torus characters are natural in the ring of values. -/
theorem map_torusCharacter {S : Type*} [CommRing S] (φ : R →+* S) (s : κ → Rˣ) (μ : κ → ℤ) :
    Units.map (φ : R →* S) (torusCharacter s μ) =
      torusCharacter (fun j => Units.map (φ : R →* S) (s j)) μ := by
  simp [torusCharacter, map_prod, map_zpow]

end TorusCharacter

/-! ## Diagonal automorphisms -/

/-- The automorphism of `M` scaling the `i`-th vector of the basis `b` by the unit `w i`. -/
noncomputable def basisDiagonal (b : Basis ι R M) (w : ι → Rˣ) : M ≃ₗ[R] M :=
  b.equiv (b.unitsSMul w) (Equiv.refl ι)

/-- The defining action of a diagonal automorphism on a basis vector. -/
@[simp] theorem basisDiagonal_basis (b : Basis ι R M) (w : ι → Rˣ) (i : ι) :
    basisDiagonal b w (b i) = (w i : R) • b i := by
  rw [basisDiagonal, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, Units.smul_def]

/-- The diagonal automorphism attached to the constant family `1` is the identity. -/
@[simp] theorem basisDiagonal_one (b : Basis ι R M) : basisDiagonal b 1 = 1 := by
  refine LinearEquiv.toLinearMap_injective (b.ext fun i => ?_)
  simp

/-- Diagonal automorphisms multiply pointwise in the family of scaling units. -/
theorem basisDiagonal_mul (b : Basis ι R M) (w v : ι → Rˣ) :
    basisDiagonal b (w * v) = basisDiagonal b w * basisDiagonal b v := by
  refine LinearEquiv.toLinearMap_injective (b.ext fun i => ?_)
  simp only [LinearEquiv.coe_coe, basisDiagonal_basis, LinearEquiv.mul_eq_trans,
    LinearEquiv.trans_apply, Pi.mul_apply, Units.val_mul, map_smul]
  rw [smul_smul, mul_comm]

/-- The diagonal automorphisms as a homomorphism from the group of families of units. -/
noncomputable def basisDiagonalHom (b : Basis ι R M) : (ι → Rˣ) →* (M ≃ₗ[R] M) where
  toFun := basisDiagonal b
  map_one' := basisDiagonal_one b
  map_mul' := basisDiagonal_mul b

/-- The homomorphism of diagonal automorphisms evaluates to `TauCeti.basisDiagonal`. -/
@[simp] theorem basisDiagonalHom_apply (b : Basis ι R M) (w : ι → Rˣ) :
    basisDiagonalHom b w = basisDiagonal b w := (rfl)

/-- A diagonal automorphism scales each coordinate by its corresponding unit. -/
theorem repr_basisDiagonal (b : Basis ι R M) (w : ι → Rˣ) (m : M) (i : ι) :
    b.repr (basisDiagonal b w m) i = (w i : R) * b.repr m i :=
  b.repr_apply_of_apply_basis (basisDiagonal_basis b w) m i

/-- Inverting a diagonal automorphism inverts each of its diagonal entries. -/
theorem basisDiagonal_inv (b : Basis ι R M) (w : ι → Rˣ) :
    (basisDiagonal b w)⁻¹ = basisDiagonal b w⁻¹ := by
  simpa only [basisDiagonalHom_apply] using (map_inv (basisDiagonalHom b) w).symm

/-- The matrix of a diagonal basis automorphism in that basis is the diagonal matrix of its
scaling units. -/
theorem toMatrix_basisDiagonal [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (w : ι → Rˣ) :
    LinearMap.toMatrix b b (basisDiagonal b w).toLinearMap =
      Matrix.diagonal fun i => (w i : R) := by
  calc
    _ = b.toMatrix (b.unitsSMul w) := by
      ext i j
      rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
      have hbasis : (basisDiagonal b w).toLinearMap (b j) = (b.unitsSMul w) j := by
        rw [LinearEquiv.coe_toLinearMap, basisDiagonal_basis, Basis.unitsSMul_apply,
          Units.smul_def]
      rw [hbasis]
    _ = _ := b.toMatrix_unitsSMul w

/-- A diagonal automorphism scales by a single unit any vector whose coordinates vanish outside
the basis vectors carrying that unit. Applied to a weight basis, this says that a torus point acts
on a weight vector by the value of the corresponding character. -/
theorem basisDiagonal_apply_of_repr_eq_zero (b : Basis ι R M) (w : ι → Rˣ) {c : Rˣ} {m : M}
    (hm : ∀ i, w i ≠ c → b.repr m i = 0) :
    basisDiagonal b w m = (c : R) • m := by
  have key : ∀ i ∈ (b.repr m).support, (w i : R) = (c : R) := by
    intro i hi
    by_contra hne
    exact Finsupp.mem_support_iff.1 hi (hm i fun hwc => hne (congrArg Units.val hwc))
  conv_lhs => rw [← b.linearCombination_repr m]
  conv_rhs => rw [← b.linearCombination_repr m]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, smul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [map_smul, basisDiagonal_basis, smul_smul, smul_smul, key i hi, mul_comm]

/-! ## The torus of a weighted basis -/

section WeightTorus

variable [Fintype κ]

/-- The split torus of rank `κ` acting on `M` through a weight function on a basis: the point
`s` acts on the `i`-th basis vector by the value at `s` of the character `wt i`.

This is how the split maximal torus of a Chevalley group acts on an admissible lattice written in
a weight basis. -/
noncomputable def basisWeightTorus (b : Basis ι R M) (wt : ι → κ → ℤ) :
    (κ → Rˣ) →* (M ≃ₗ[R] M) :=
  (basisDiagonalHom b).comp (torusCharacterHom (R := R) wt)

/-- The weight torus at a point is the diagonal automorphism scaling by the weight characters. -/
theorem basisWeightTorus_apply (b : Basis ι R M) (wt : ι → κ → ℤ) (s : κ → Rˣ) :
    basisWeightTorus b wt s = basisDiagonal b fun i => torusCharacter s (wt i) := (rfl)

/-- A torus point scales the `i`-th basis vector by the value at it of the character `wt i`. -/
@[simp] theorem basisWeightTorus_basis (b : Basis ι R M) (wt : ι → κ → ℤ) (s : κ → Rˣ) (i : ι) :
    basisWeightTorus b wt s (b i) = (torusCharacter s (wt i) : R) • b i :=
  basisDiagonal_basis b _ i

/-- A torus point acts on a weight vector by the value of the corresponding character. -/
theorem basisWeightTorus_apply_of_repr_eq_zero (b : Basis ι R M) (wt : ι → κ → ℤ) (s : κ → Rˣ)
    {μ : κ → ℤ} {m : M} (hm : ∀ i, wt i ≠ μ → b.repr m i = 0) :
    basisWeightTorus b wt s m = (torusCharacter s μ : R) • m := by
  rw [basisWeightTorus_apply]
  exact basisDiagonal_apply_of_repr_eq_zero b _ fun i hi => hm i fun hwt => hi (by rw [hwt])

end WeightTorus

end TauCeti
