/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Induction
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Detecting comodule fixed vectors on geometric points

Let `H` be a reduced commutative bialgebra of finite type over a field `k`, and let `M` be a
finite-dimensional `H`-comodule. A vector `m : M` is fixed by the coaction if and only if every
point of `H` valued in an algebraically closed extension fixes `1 ⊗ m` in the scalar extension.

The reverse implication is the substantive one. Evaluating the pointwise fixed-vector equation
against each member of a dual basis shows that every geometric point takes the corresponding
matrix coefficient of `m` to its trivial-comodule value. Reduced finite-type point separation
then identifies those coefficients in `H`, and the basis expansion of the coaction gives
`m ↦ m ⊗ 1`.

For a Hopf algebra this is restated using the group action of its convolution group of points,
and then as a characterization of `Comodule.HasNonzeroFixedVector`. This is the bridge in the
Kolchin induction for Layer 5 of the ReductiveGroups roadmap: a common fixed vector obtained from
the geometric point representation is thereby promoted to a fixed vector of the comodule itself.

## Main declarations

* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq`: geometric-point detection of
  a fixed vector for a bialgebra comodule.
* `TauCeti.Comodule.hasNonzeroFixedVector_iff_exists_forall_endOfPoint_tmul_eq`: the corresponding
  existence criterion for a nonzero fixed vector.
* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq`: the same criterion for the
  convolution-group action of a Hopf algebra.
* `TauCeti.Comodule.hasNonzeroFixedVector_iff_exists_forall_pointsAction_tmul_eq`: nonzero
  comodule fixed vectors are exactly nonzero vectors fixed by every geometric point.

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
variable [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- A vector in a finite-dimensional comodule over a reduced finite-type bialgebra is fixed by
the coaction exactly when every algebraically closed point fixes its scalar extension. -/
theorem coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : H →ₐ[k] K, endOfPoint M g (1 ⊗ₜ[k] m) = 1 ⊗ₜ[k] m := by
  constructor
  · intro hm g
    rw [endOfPoint_tmul, hm]
    simp
  · intro h
    let b := Module.Basis.ofVectorSpace k M
    rw [coact_eq_sum_basis_matrixCoefficient (C := H) b]
    calc
      ∑ i, b i ⊗ₜ[k] matrixCoefficient (C := H) (b.coord i) m =
          ∑ i, b i ⊗ₜ[k] ((b.coord i m) • (1 : H)) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
        intro g
        have heval := congrArg
          (fun z ↦ TauCeti.Module.Dual.baseChangeEvaluation
            (R := k) (M := M) (A := K) (1 ⊗ₜ[k] b.coord i) z) (h g)
        simpa [Module.Basis.coord_apply, Algebra.smul_def] using heval
      _ = (∑ i, (b.coord i m) • b i) ⊗ₜ[k] (1 : H) := by
        rw [TensorProduct.sum_tmul]
        apply Finset.sum_congr rfl
        intro i _
        exact (TensorProduct.smul_tmul (b.coord i m) (b i) (1 : H)).symm
      _ = m ⊗ₜ[k] (1 : H) := by
        congr 1
        simpa only [Module.Basis.coord_apply] using b.sum_repr m

/-- A finite-dimensional bialgebra comodule has a nonzero fixed vector exactly when some nonzero
vector is fixed after scalar extension by every algebraically closed point. -/
theorem hasNonzeroFixedVector_iff_exists_forall_endOfPoint_tmul_eq :
    HasNonzeroFixedVector k H M ↔
      ∃ m : M, m ≠ 0 ∧
        ∀ g : H →ₐ[k] K, endOfPoint M g ((1 : K) ⊗ₜ[k] m) = (1 : K) ⊗ₜ[k] m := by
  rw [hasNonzeroFixedVector_iff]
  apply exists_congr
  intro m
  exact and_congr_right fun _ ↦
    coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (K := K) m

end Bialgebra

section HopfAlgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- For a finite-dimensional Hopf-algebra comodule, a vector is fixed by the coaction exactly
when every point in the convolution group fixes its scalar extension. -/
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

/-- A finite-dimensional comodule over a reduced finite-type Hopf algebra has a nonzero fixed
vector exactly when some nonzero vector is fixed after scalar extension by every geometric
point. -/
theorem hasNonzeroFixedVector_iff_exists_forall_pointsAction_tmul_eq :
    HasNonzeroFixedVector k H M ↔
      ∃ m : M, m ≠ 0 ∧
        ∀ g : WithConv (H →ₐ[k] K),
          pointsAction M g ((1 : K) ⊗ₜ[k] m) = (1 : K) ⊗ₜ[k] m := by
  rw [hasNonzeroFixedVector_iff]
  apply exists_congr
  intro m
  exact and_congr_right fun _ ↦
    coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq (K := K) m

end HopfAlgebra

end

end TauCeti.Comodule
