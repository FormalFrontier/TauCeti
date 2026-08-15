/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generation.LimitSemigroup
public import TauCeti.Analysis.Semigroups.Generation.Yosida.Generator

/-!
# The Lumer--Phillips generation theorem

A densely defined m-dissipative operator `A` on a real Banach space generates a strongly
continuous contraction semigroup. The semigroup itself is built in
`TauCeti/Analysis/Semigroups/Generation/LimitSemigroup.lean` as the limit
`S(t) x = lim_{lambda -> ∞} exp (t A_lambda) x` of the Yosida exponentials.

The reusable generator-identification argument lives in
`TauCeti/Analysis/Semigroups/Generation/Yosida/Generator.lean`. This file supplies its hypotheses:
the compact-time convergence defining `yosidaLimitSemigroup`, convergence of `A_lambda x` to
`A x` on the dense domain, the contraction bound on the approximating semigroups, and the shared
resolvent point `1`. Thus the generator of the limit semigroup is `A`.

## Main results

* `TauCeti.Semigroups.IsMDissipative.yosidaLimitSemigroup_generator`: the generator of the
  Yosida limit semigroup of a densely defined m-dissipative `A` is `A`.
* `TauCeti.Semigroups.IsMDissipative.exists_contractionSemigroup_generator_eq`: the
  **Lumer--Phillips generation theorem**.
* `TauCeti.Semigroups.exists_contractionSemigroup_generator_eq_iff`: an operator generates a
  contraction semigroup exactly when it is densely defined and m-dissipative.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.15.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 4.3.
-/

public section

noncomputable section

open scoped NNReal Topology

open Filter NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace IsMDissipative

variable {A : X →ₗ.[ℝ] X}

/-- **The generator of the Yosida limit semigroup is the operator it was built from.** For a
densely defined m-dissipative `A`, the semigroup `yosidaLimitSemigroup` has generator `A`. -/
@[simp]
theorem yosidaLimitSemigroup_generator (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) :
    (hA.yosidaLimitSemigroup hdense).toStronglyContinuousSemigroup.generator = A := by
  let S := (hA.yosidaLimitSemigroup hdense).toStronglyContinuousSemigroup
  apply S.generator_eq_of_yosidaApproximation (lambda := 1)
    (hA.mem_resolventSet one_pos)
    ((ContractionSemigroup.isMDissipative_generator _).mem_resolventSet one_pos)
  · exact hA.tendsto_yosidaApproximation_apply_atTop hdense
  · intro x t ht
    have hx := hA.tendsto_yosidaLimit hdense ht (x : X)
    rwa [← hA.yosidaLimitSemigroup_realOperator_apply hdense ht (x : X)] at hx
  · intro x T hT
    exact (hA.tendstoUniformlyOn_exp_yosidaApproximation hdense (A x) hT).congr_right
      fun u hu => (hA.yosidaLimitSemigroup_realOperator_apply hdense hu.1 (A x)).symm
  · refine fun T => ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda u hu
    exact norm_exp_smul_yosidaApproximation_le_one
      (hA.mul_norm_resolvent_le_one hlambda) hlambda hu.1

/-- **The Lumer--Phillips generation theorem.** A densely defined m-dissipative operator on a
real Banach space generates a strongly continuous contraction semigroup.

Dissipativity plus the range condition packaged in `IsMDissipative` is exactly the hypothesis
set of Lumer--Phillips; the semigroup produced is the strong limit of the semigroups generated
by the Yosida approximations of `A`. -/
theorem exists_contractionSemigroup_generator_eq (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) :
    ∃ S : ContractionSemigroup X, S.toStronglyContinuousSemigroup.generator = A :=
  ⟨hA.yosidaLimitSemigroup hdense, hA.yosidaLimitSemigroup_generator hdense⟩

end IsMDissipative

/-- **Lumer--Phillips as a characterization.** An unbounded operator on a real Banach space is
the generator of a strongly continuous contraction semigroup if and only if it is densely
defined and m-dissipative.

The forward direction is the density of a generator domain together with the converse of
Lumer--Phillips; the backward direction is the generation theorem. -/
theorem exists_contractionSemigroup_generator_eq_iff (A : X →ₗ.[ℝ] X) :
    (∃ S : ContractionSemigroup X, S.toStronglyContinuousSemigroup.generator = A) ↔
      Dense (A.domain : Set X) ∧ IsMDissipative A := by
  refine ⟨fun ⟨S, hS⟩ => ⟨?_, ?_⟩, fun ⟨hdense, hA⟩ =>
    hA.exists_contractionSemigroup_generator_eq hdense⟩
  · have hdom : (A.domain : Set X) =
        (S.toStronglyContinuousSemigroup.domain : Set X) := by
      rw [← hS, S.toStronglyContinuousSemigroup.generator_domain]
    rw [hdom]
    exact S.toStronglyContinuousSemigroup.dense_domain
  · rw [← hS]
    exact ContractionSemigroup.isMDissipative_generator S

end TauCeti.Semigroups

end
