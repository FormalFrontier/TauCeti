/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The basis dual to a basis of a Lie algebra under its Killing form

Let `L` be a Lie algebra over a field `K` whose Killing form `κ` is nondegenerate. Every basis `b`
of `L` then has a **Killing-dual basis** `TauCeti.killingDualBasis b`, characterised by
`κ (b i) (killingDualBasis b j) = if i = j then 1 else 0`. This is Mathlib's
`LinearMap.BilinForm.dualBasis` for the Killing form, together with the consequences of
biorthogonality that a computation reads off: the coordinates in either basis are the Killing
pairings against the other, and each vector expands accordingly.

This is pure linear algebra of the Killing form; it is used both by the Casimir element of
`TauCeti/Algebra/Lie/UniversalEnveloping/Casimir.lean` and by the basis adapted to the root space
decomposition of `TauCeti/Algebra/Lie/Weights/Root/Basis.lean`.

## Main definitions

* `TauCeti.killingDualBasis`: the basis dual to a given one under the Killing form.

## Main results

* `TauCeti.killingForm_killingDualBasis`: the defining biorthogonality.
* `TauCeti.sum_killingForm_smul_basis` and `TauCeti.sum_killingForm_smul_killingDualBasis`: the
  expansion of a vector in either basis, with the coefficients read off by the other.
-/

public section

open Finset LieAlgebra LieModule

namespace TauCeti

universe u v

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [LieAlgebra.IsKilling K L] in
/-- The Killing form is symmetric, in the bundled `LinearMap.BilinForm.IsSymm` form that the
dual-basis API asks for; Mathlib supplies it as the unbundled `LieModule.traceForm_isSymm`. -/
private theorem killingForm_isSymm : (killingForm K L).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ LieModule.traceForm_comm K L L x y

/-- The basis of `L` **dual to `b` under the Killing form**: `κ (b i) (killingDualBasis b j)` is
`1` when `i = j` and `0` otherwise (`TauCeti.killingForm_killingDualBasis`). -/
noncomputable def killingDualBasis (b : Module.Basis ι K L) : Module.Basis ι K L :=
  (killingForm K L).dualBasis (LieAlgebra.IsKilling.killingForm_nondegenerate K L) b

/-- The defining biorthogonality of the Killing-dual basis. -/
@[simp]
theorem killingForm_killingDualBasis (b : Module.Basis ι K L) (i j : ι) :
    killingForm K L (b i) (killingDualBasis b j) = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right _ killingForm_isSymm b i j

/-- Coordinates in the Killing-dual basis are Killing pairings against `b`. -/
@[simp]
theorem killingDualBasis_repr_apply (b : Module.Basis ι K L) (v : L) (i : ι) :
    (killingDualBasis b).repr v i = killingForm K L (b i) v :=
  (LinearMap.BilinForm.dualBasis_repr_apply _ b v i).trans
    (LieModule.traceForm_comm K L L v (b i))

/-- Conjugating twice returns the original basis: the Killing-dual basis of the Killing-dual
basis of `b` is `b`. -/
@[simp]
theorem killingDualBasis_killingDualBasis (b : Module.Basis ι K L) :
    killingDualBasis (killingDualBasis b) = b :=
  LinearMap.BilinForm.dualBasis_dualBasis _ killingForm_isSymm b

/-- Coordinates in `b` are Killing pairings against the Killing-dual basis. -/
theorem repr_apply_eq_killingForm (b : Module.Basis ι K L) (v : L) (i : ι) :
    b.repr v i = killingForm K L v (killingDualBasis b i) := by
  conv_lhs => rw [← killingDualBasis_killingDualBasis b]
  rw [killingDualBasis_repr_apply, LieModule.traceForm_comm]

/-- **Expansion in `b`**, with the coefficients read off by the Killing-dual basis. -/
theorem sum_killingForm_smul_basis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L v (killingDualBasis b i) • b i = v := by
  conv_rhs => rw [← b.sum_repr v]
  exact sum_congr rfl fun i _ ↦ by rw [repr_apply_eq_killingForm]

/-- **Expansion in the Killing-dual basis**, with the coefficients read off by `b`. -/
theorem sum_killingForm_smul_killingDualBasis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L (b i) v • killingDualBasis b i = v := by
  conv_rhs => rw [← (killingDualBasis b).sum_repr v]
  exact sum_congr rfl fun i _ ↦ by rw [killingDualBasis_repr_apply]

end TauCeti
