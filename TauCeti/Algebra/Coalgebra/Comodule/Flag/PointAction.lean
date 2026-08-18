/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Detecting comodule fixed vectors on geometric points

Let `H` be a reduced commutative bialgebra of finite type over a field `k`, and let `M` be an
`H`-comodule. A vector `m : M` is fixed by the coaction if and only if every point of `H` valued in
an algebraically closed extension fixes `1 ⊗ m` in the scalar extension.

The reverse implication is the substantive one. Evaluating the pointwise fixed-vector equation
against every linear functional shows that every geometric point takes the corresponding matrix
coefficient of `m` to its trivial-comodule value. Reduced finite-type point separation then
identifies those coefficients in `H`. A finite-dimensional subspace containing the single tensor
`coact m - m ⊗ 1` has enough coordinate functionals to show that this tensor vanishes.

For a Hopf algebra this is restated using the group action of its convolution group of points.
This is the bridge in the Kolchin induction for Layer 5 of the ReductiveGroups roadmap: a common
fixed vector obtained from the geometric point representation is thereby promoted to a fixed
vector of the comodule itself.

## Main declarations

* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq`: geometric-point detection of
  a fixed vector for a bialgebra comodule.
* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq`: the same criterion for the
  convolution-group action of a Hopf algebra.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open WithConv

universe u v w x

noncomputable section

section Bialgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing H] [Bialgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- A vector in a comodule over a reduced finite-type bialgebra is fixed by the coaction exactly
when every algebraically closed point fixes its scalar extension. -/
theorem coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : H →ₐ[k] K, endOfPoint M g (1 ⊗ₜ[k] m) = 1 ⊗ₜ[k] m := by
  constructor
  · intro hm g
    rw [endOfPoint_tmul, hm]
    simp
  · intro h
    have hcoeff (φ : Module.Dual k M) :
        matrixCoefficient (C := H) φ m = (φ m) • (1 : H) := by
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
      intro g
      have heval := congrArg
        (fun z ↦ TauCeti.Module.Dual.baseChangeEvaluation
          (R := k) (M := M) (A := K) (1 ⊗ₜ[k] φ) z) (h g)
      simpa [Algebra.smul_def] using heval
    let z := coact (R := k) (C := H) m - m ⊗ₜ[k] (1 : H)
    suffices z = 0 by exact sub_eq_zero.mp this
    obtain ⟨M', hM', hz⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
      ({z} : Set (M ⊗[k] H)) (Set.finite_singleton z)
    obtain ⟨z', hz'⟩ := hz (Set.mem_singleton z)
    let _ : Module.Finite k M' := hM'
    let b := Module.finBasis k M'
    have hz'zero : z' = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
      ext i
      rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
      obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
      rw [← hφ, LinearMap.rTensor_comp_apply, hz']
      simpa [z, matrixCoefficient_def, LinearMap.rTensor_def] using
        sub_eq_zero.mpr (hcoeff φ)
    rw [← hz', hz'zero, map_zero]

end Bialgebra

section HopfAlgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- For a Hopf-algebra comodule, a vector is fixed by the coaction exactly when every point in the
convolution group fixes its scalar extension. -/
theorem coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : WithConv (H →ₐ[k] K),
        pointsAction M g ((1 : K) ⊗ₜ[k] m) = (1 : K) ⊗ₜ[k] m := by
  rw [coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (K := K)]
  constructor
  · intro h g
    rw [← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap]
    exact h g.ofConv
  · intro h g
    have hg := h (toConv g)
    rw [← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap] at hg
    simpa only [ofConv_toConv] using hg

end HopfAlgebra

end

end TauCeti.Comodule
