/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The Killing-dual basis of a Cartan subalgebra

For a finite-dimensional Lie algebra with non-degenerate Killing form, the restriction of that
form to a Cartan subalgebra is non-degenerate. This file records the basis dual to a chosen basis
of the Cartan subalgebra and its coordinate expansion.

## Main definitions and results

* `TauCeti.cartanKillingDualBasis`: the basis dual under the restricted Killing form.
* `TauCeti.killingForm_cartanKillingDualBasis`: its defining biorthogonality.
* `TauCeti.cartanKillingDualBasis_repr_apply`: its coordinate accessor.
* `TauCeti.sum_killingForm_smul_cartanKillingDualBasis`: expansion in the dual basis.
-/

public section

namespace TauCeti

open Finset LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {ι : Type w} [Finite ι] [DecidableEq ι]

/-- The basis of the Cartan subalgebra dual to `bH` under the Killing form of `L`. -/
noncomputable def cartanKillingDualBasis (bH : Basis ι K H) : Basis ι K H :=
  (LieModule.traceForm K H L).dualBasis (traceForm_cartan_nondegenerate K L H) bH

/-- The defining biorthogonality of `TauCeti.cartanKillingDualBasis`. -/
@[simp]
theorem killingForm_cartanKillingDualBasis (bH : Basis ι K H) (i j : ι) :
    killingForm K L (bH i : L) (cartanKillingDualBasis bH j : L) = if i = j then 1 else 0 :=
  (DFunLike.congr_fun (LinearMap.congr_fun (LieAlgebra.restrict_killingForm K L H) (bH i))
      (cartanKillingDualBasis bH j)).trans
    (LinearMap.BilinForm.apply_dualBasis_right _
      (LinearMap.BilinForm.isSymm_def.mpr fun u v ↦ LieModule.traceForm_comm K H L u v) bH i j)

/-- Coordinates in the Cartan Killing-dual basis are Killing pairings against `bH`. -/
@[simp]
theorem cartanKillingDualBasis_repr_apply (bH : Basis ι K H) (u : H) (i : ι) :
    (cartanKillingDualBasis bH).repr u i = killingForm K L (bH i : L) (u : L) := by
  rw [cartanKillingDualBasis, LinearMap.BilinForm.dualBasis_repr_apply,
    LieModule.traceForm_comm K H L]
  exact (DFunLike.congr_fun
    (LinearMap.congr_fun (LieAlgebra.restrict_killingForm K L H) (bH i)) u).symm

/-- Expansion of an element of `H` in the Killing-dual basis: the coefficients are its Killing
pairings against `bH`. -/
theorem sum_killingForm_smul_cartanKillingDualBasis [Fintype ι] (bH : Basis ι K H) (u : H) :
    ∑ i, killingForm K L (bH i : L) (u : L) • cartanKillingDualBasis bH i = u := by
  conv_rhs => rw [← (cartanKillingDualBasis bH).sum_repr u]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [cartanKillingDualBasis_repr_apply]

end TauCeti
