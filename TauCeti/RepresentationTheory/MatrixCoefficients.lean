/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

-- `Representation.IntertwiningMap` occurs in the statements below, and this module supplies
-- `Representation` itself together with `Representation.tprod`.
public import Mathlib.RepresentationTheory.Intertwining
-- `LinearMap.toMatrix` and `Module.Basis.tensorProduct` occur in the statements below, and
-- `TensorProduct.toMatrix_map` is what computes the entries of a tensor product.
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
-- `Basis.piTensorProduct`, the basis of pure tensors the tensor-power entries are read
-- against.
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
-- `Representation.tensorPower` occurs in the statements below.
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# Matrix coefficients of a representation

The **matrix coefficients** of a representation `ρ` against a basis `b` of its carrier are the
functions `g ↦ LinearMap.toMatrix b b (ρ g) i j` on the group.  A property of a representation is
often expressed by asking that all of them lie in some fixed algebra `A` of functions on the group:
that they are polynomial in the entries of `g`, say, or bounded, or continuous.

This file collects the closure properties of such a condition that hold for *every* subalgebra `A`,
so that a proof of the condition never has to be repeated for each choice:

* a surjective intertwining map carries the condition from source to target, because a basis vector
  of the target lifts to a vector of the source, and the entries against the target basis are then
  fixed linear combinations of the entries against the source basis, with coefficients read off the
  lift and independent of `g`;
* changing the basis of a single representation is the special case of the identity map, so the
  condition is basis independent;
* against the basis of pure tensors of basis vectors, the matrix coefficients of a tensor power of a
  representation are the products of matrix coefficients of the representation;
* against a tensor product of bases, the matrix coefficients of a tensor product of representations
  are the products of matrix coefficients of the two factors.

All but the last need only a commutative semiring of scalars; the tensor-product entries are read
off `TensorProduct.toMatrix_map`, which Mathlib states over a commutative ring.

## Main results

* `TauCeti.Representation.toMatrix_mem_of_toMatrix_mem_of_surjective`: the matrix coefficients of a
  quotient representation stay inside any subalgebra containing those of the source.
* `TauCeti.Representation.toMatrix_mem_of_toMatrix_mem`: changing basis keeps the matrix
  coefficients inside any subalgebra.
* `TauCeti.Representation.toMatrix_tensorPower` and
  `TauCeti.Representation.toMatrix_tensorPower_mem`: the matrix coefficients of a tensor power are
  products of matrix coefficients, hence stay inside any subalgebra containing those of the
  representation.
* `TauCeti.Representation.toMatrix_tprod` and `TauCeti.Representation.toMatrix_tprod_mem`: the
  matrix coefficients of a tensor product are products of matrix coefficients, hence stay inside
  any subalgebra containing those of the two factors.
-/

public section

universe u v w x y z

namespace TauCeti

namespace Representation

section CommSemiring

variable {k : Type u} [CommSemiring k] {G : Type z} [Monoid G] {W : Type v} [AddCommMonoid W]
  [Module k W]
variable {V : Type y} [AddCommMonoid V] [Module k V]

/-- **The matrix coefficients of a quotient representation stay inside any subalgebra of
functions.**  If `σ` is the image of `ρ` under a surjective intertwining map, and every matrix
coefficient of `ρ` against a basis of the source lies in a subalgebra `A` of the functions on the
group, then so does every matrix coefficient of `σ` against a basis of the target. -/
theorem toMatrix_mem_of_toMatrix_mem_of_surjective (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f)
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : κ) :
    (fun g => LinearMap.toMatrix c c (σ g) i j) ∈ A := by
  obtain ⟨w, hw⟩ := hf (c j)
  have key : (fun g => LinearMap.toMatrix c c (σ g) i j)
      = ∑ p : ι, ∑ l : ι, (b.repr w l * c.repr (f (b p)) i) •
          fun g => LinearMap.toMatrix b b (ρ g) p l := by
    funext g
    have hfg : σ g (c j) = f (ρ g w) := by
      rw [← hw]
      exact (Representation.IntertwiningMap.isIntertwining ρ σ f g w).symm
    have hexp : ∀ p, b.repr (ρ g w) p = ∑ l, b.repr w l * LinearMap.toMatrix b b (ρ g) p l := by
      intro p
      simpa [Matrix.mulVec, dotProduct, mul_comm] using
        (congr_fun (LinearMap.toMatrix_mulVec_repr b b (ρ g) w) p).symm
    rw [LinearMap.toMatrix_apply, hfg]
    conv_lhs => rw [← b.sum_repr (ρ g w)]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, hexp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [key]
  exact Subalgebra.sum_mem _ fun p _ =>
    Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (h p l) _

/-- **Changing basis keeps the matrix coefficients inside any subalgebra of functions**: if every
matrix coefficient of `ρ` against one basis lies in a subalgebra `A` of the functions on the group,
so does every matrix coefficient against any other basis. -/
theorem toMatrix_mem_of_toMatrix_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k W)
    (ρ : Representation k G W)
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : κ) :
    (fun g => LinearMap.toMatrix c c (ρ g) i j) ∈ A :=
  toMatrix_mem_of_toMatrix_mem_of_surjective A b c (.id ρ) (fun v => ⟨v, rfl⟩) h i j

/-- Against the basis of pure tensors of basis vectors, a matrix coefficient of the `d`-fold tensor
power of `ρ` is the product of the `d` matrix coefficients of `ρ` listed by the two indices. -/
theorem toMatrix_tensorPower {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k W)
    (ρ : Representation k G W) (d : ℕ) (g : G) (i j : Fin d → ι) :
    LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => b)
        (Basis.piTensorProduct fun _ : Fin d => b) (ρ.tensorPower d g) i j
      = ∏ l : Fin d, LinearMap.toMatrix b b (ρ g) (i l) (j l) := by
  rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    _root_.Representation.tensorPower_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp [LinearMap.toMatrix_apply]

/-- **The matrix coefficients of a tensor power stay inside any subalgebra of functions**
containing those of the representation. -/
theorem toMatrix_tensorPower_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k W)
    {ρ : Representation k G W} {d : ℕ}
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : Fin d → ι) :
    (fun g => LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => b)
        (Basis.piTensorProduct fun _ : Fin d => b) (ρ.tensorPower d g) i j) ∈ A := by
  have hentry : (fun g => LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => b)
        (Basis.piTensorProduct fun _ : Fin d => b) (ρ.tensorPower d g) i j)
      = ∏ l : Fin d, fun g => LinearMap.toMatrix b b (ρ g) (i l) (j l) := by
    funext g
    simpa using toMatrix_tensorPower b ρ d g i j
  rw [hentry]
  exact prod_mem fun l _ => h (i l) (j l)

end CommSemiring

section CommRing

variable {k : Type u} [CommRing k] {G : Type z} [Monoid G] {W : Type v} [AddCommGroup W]
  [Module k W]
variable {V : Type y} [AddCommGroup V] [Module k V]

/-- Against a tensor product of bases, the matrix coefficients of a tensor product of
representations are the products of the matrix coefficients of the two factors: the Kronecker
product, read entrywise. -/
theorem toMatrix_tprod {ι : Type w} [Fintype ι] [DecidableEq ι]
    {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V} (g : G) (i j : ι × κ) :
    LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c) ((ρ.tprod σ) g) i j
      = LinearMap.toMatrix b b (ρ g) i.1 j.1 * LinearMap.toMatrix c c (σ g) i.2 j.2 := by
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  simp [Matrix.kroneckerMap_apply]

/-- **The matrix coefficients of a tensor product stay inside any subalgebra of functions**
containing those of the two factors. -/
theorem toMatrix_tprod_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V}
    (hb : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A)
    (hc : ∀ p l, (fun g => LinearMap.toMatrix c c (σ g) p l) ∈ A) (i j : ι × κ) :
    (fun g => LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c) ((ρ.tprod σ) g) i j)
      ∈ A := by
  have hentry : (fun g => LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c)
        ((ρ.tprod σ) g) i j)
      = (fun g => LinearMap.toMatrix b b (ρ g) i.1 j.1) *
        fun g => LinearMap.toMatrix c c (σ g) i.2 j.2 :=
    funext fun g => toMatrix_tprod b c g i j
  rw [hentry]
  exact mul_mem (hb i.1 j.1) (hc i.2 j.2)

end CommRing

end Representation

end TauCeti
