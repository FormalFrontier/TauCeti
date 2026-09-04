/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Pure tensors on two strands

Calculations on a tensor square index their pure tensors by `Fin 2`, and repeatedly need the same
three pieces of bookkeeping: a sum over the functions `Fin 2 → ι` is a double sum, a pure tensor
indexed by `Fin 2` may be rewritten in `![·, ·]` form, and pushing a matrix through both strands
re-expands a basis pure tensor in the standard basis. None of them says anything about what the
tensor square is being used for, so they live here rather than in any one consumer.

## Main results

* `TauCeti.sum_pi_fin_two`: a sum over `Fin 2 → ι` is a double sum over `ι`.
* `TauCeti.tprod_fin_two`: a pure tensor on two strands is `⨂ₜ ![v 0, v 1]`.
* `Matrix.piTensorProductMap_tprod_single`: applying a matrix in both strands re-expands a basis
  pure tensor in the standard basis. Use it whenever a two-strand pure tensor of standard basis
  vectors is pushed through `PiTensorProduct.map` and the result is wanted coefficientwise.
* `Matrix.piTensorProductMap_bivector`: the same for a whole bivector `∑ x y, K x y • ⨂ₜ`, which
  becomes the bivector of the congruate `A * K * Aᵀ`. `A` may be rectangular, so the result is
  indexed by its row type.
-/

public section

namespace TauCeti

/-- A sum over the functions `Fin 2 → ι` is a double sum. -/
theorem sum_pi_fin_two {ι M : Type*} [Fintype ι] [AddCommMonoid M] (f : ι → ι → M) :
    ∑ r : Fin 2 → ι, f (r 0) (r 1) = ∑ p : ι, ∑ q : ι, f p q :=
  Eq.trans
    (Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => ι) _
      (fun pq : ι × ι => f pq.1 pq.2) fun _ => rfl)
    (Fintype.sum_prod_type' f)

/-- A pure tensor on two strands, written in `![·, ·]` form. -/
theorem tprod_fin_two {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 2 → M) :
    PiTensorProduct.tprod R v = PiTensorProduct.tprod R ![v 0, v 1] := by
  congr 1
  funext i
  fin_cases i <;> simp

end TauCeti

namespace Matrix

/-- Applying a matrix `A` in both strands re-expands a pure tensor of standard basis vectors back
in the standard basis: the coefficient of `Pi.single p 1 ⊗ Pi.single q 1` is `A p x * A q y`. -/
theorem piTensorProductMap_tprod_single {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [CommSemiring R] (A : Matrix κ ι R) (x y : ι) :
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
        (PiTensorProduct.tprod R ![Pi.single x (1 : R), Pi.single y (1 : R)]) =
      ∑ p : κ, ∑ q : κ, (A p x * A q y) •
        PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] := by
  have hcol : ∀ z : ι, A *ᵥ Pi.single z (1 : R) = ∑ p : κ, A p z • Pi.single p (1 : R) := by
    intro z
    rw [Matrix.mulVec_single_one, ← (Pi.basisFun R κ).sum_repr (A.col z)]
    simp [Matrix.col_apply]
  have hfun : (fun i : Fin 2 =>
      Matrix.mulVecLin A (![Pi.single x (1 : R), Pi.single y (1 : R)] i)) =
      fun i : Fin 2 => ∑ p : κ, A p (![x, y] i) • Pi.single p (1 : R) := by
    funext i
    fin_cases i <;> simp [hcol]
  rw [PiTensorProduct.map_tprod, hfun,
    MultilinearMap.map_sum (PiTensorProduct.tprod R)
      (g := fun i : Fin 2 => fun p : κ => A p (![x, y] i) • Pi.single p (1 : R)),
    ← TauCeti.sum_pi_fin_two fun p q => (A p x * A q y) •
      PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)]]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : PiTensorProduct.tprod R (fun i : Fin 2 => Pi.single (r i) (1 : R))
      = PiTensorProduct.tprod R ![Pi.single (r 0) (1 : R), Pi.single (r 1) (1 : R)] :=
    TauCeti.tprod_fin_two _
  rw [MultilinearMap.map_smul_univ, hr, Fin.prod_univ_two]
  simp

/-- Applying a matrix `A` in both tensor factors turns the bivector of `K` into the bivector of the
congruate `A * K * Aᵀ`. It is the computation behind the invariance of the Brauer cup. -/
theorem piTensorProductMap_bivector {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [CommSemiring R] (A : Matrix κ ι R) (K : Matrix ι ι R) :
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
        (∑ x : ι, ∑ y : ι, K x y •
          PiTensorProduct.tprod R ![Pi.single x (1 : R), Pi.single y (1 : R)]) =
      ∑ p : κ, ∑ q : κ, (A * K * Aᵀ) p q •
        PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] := by
  have hcoef : ∀ p q : κ,
      ∑ x : ι, ∑ y : ι, K x y * (A p x * A q y) = (A * K * Aᵀ) p q := by
    intro p q
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  calc
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
        (∑ x : ι, ∑ y : ι, K x y •
          PiTensorProduct.tprod R ![Pi.single x (1 : R), Pi.single y (1 : R)])
        = ∑ x : ι, ∑ y : ι, ∑ p : κ, ∑ q : κ,
            (K x y * (A p x * A q y)) •
              PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] := by
          simp only [map_sum, map_smul, Matrix.piTensorProductMap_tprod_single,
            Finset.smul_sum, smul_smul]
    -- move the two outer sums past the two inner ones, one adjacent swap at a time
    _ = ∑ x : ι, ∑ p : κ, ∑ y : ι, ∑ q : κ,
          (K x y * (A p x * A q y)) •
            PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p : κ, ∑ x : ι, ∑ y : ι, ∑ q : κ,
          (K x y * (A p x * A q y)) •
            PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] := Finset.sum_comm
    _ = ∑ p : κ, ∑ x : ι, ∑ q : κ, ∑ y : ι,
          (K x y * (A p x * A q y)) •
            PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p : κ, ∑ q : κ, ∑ x : ι, ∑ y : ι,
          (K x y * (A p x * A q y)) •
            PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p : κ, ∑ q : κ, (A * K * Aᵀ) p q •
          PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          simp only [← Finset.sum_smul]
          rw [hcoef p q]

end Matrix
