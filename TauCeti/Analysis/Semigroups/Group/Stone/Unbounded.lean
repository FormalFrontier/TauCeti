/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Unitary
public import TauCeti.Analysis.Semigroups.Group.InverseSemigroups
import TauCeti.Analysis.Semigroups.Generator.Neg
import TauCeti.Analysis.Semigroups.Dissipative.SkewSelfAdjoint
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Analysis.Semigroups.Generation.LumerPhillips

/-!
# Stone's theorem for unbounded self-adjoint operators

A self-adjoint operator `A` on a complex Hilbert space is `-i` times the complex generator of
exactly one unitary C₀-group, the group `e^{itA}`.  This completes the converse direction of
Stone's theorem, begun for bounded `A` in `TauCeti.Analysis.Semigroups.Group.Stone.Basic`.
Together with the skew-adjointness of the generator of a unitary group
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.complexGenerator_adjoint_eq_neg`) this
characterizes the self-adjoint operators as the operators `A` with `i • A` the complex
generator of a unitary group.

The construction is the classical one.  The real restrictions of `i • A` and `-i • A` are
m-dissipative (`IsSelfAdjoint.isMDissipative_smul_restrictScalars` at `c = ± i`), so by
Lumer--Phillips each generates a contraction semigroup.  Their generators are negatives of one
another, so their equal-time operators are mutually inverse and the two semigroups glue into a
C₀-group (`TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse`, the inverse hypotheses
being `StronglyContinuousSemigroup.comp_eq_id_of_generator_eq_neg` and its primed variant).  The
glued group is complex linear because its forward half is (the generator of that half is the real
restriction of a complex-linear partial map), and unitary because it contracts in both time
directions.  Its complex generator is `i • A`, and a unitary group is determined by its complex
generator.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.isUnitary_toGroupOfInverse`: a complex-linear
  contraction semigroup and an inverse contraction semigroup glue into a unitary group.
* `IsSelfAdjoint.existsUnique_isUnitary_complexGenerator_eq_I_smul`: **Stone's theorem, converse
  direction**: a self-adjoint operator `A` has exactly one unitary C₀-group with complex
  generator `i • A`.
* `LinearPMap.isSelfAdjoint_iff_exists_isUnitary_complexGenerator_eq_I_smul` is **Stone's
  theorem** as a characterization of self-adjoint operators.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.24.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem VIII.7 and Theorem VIII.8.
-/

public section

noncomputable section

open scoped InnerProductSpace NNReal

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A complex-linear contraction semigroup and an inverse contraction semigroup glue into a
unitary C₀-group (complex linearity of the inverse half follows from the group law). -/
theorem isUnitary_toGroupOfInverse (S T : ContractionSemigroup H)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (hST : ∀ t, (S.toStronglyContinuousSemigroup t).comp (T.toStronglyContinuousSemigroup t) =
      ContinuousLinearMap.id ℝ H)
    (hTS : ∀ t, (T.toStronglyContinuousSemigroup t).comp (S.toStronglyContinuousSemigroup t) =
      ContinuousLinearMap.id ℝ H) :
    (S.toStronglyContinuousSemigroup.toGroupOfInverse T.toStronglyContinuousSemigroup hST
      hTS).IsUnitary := by
  refine isUnitary_of_isComplexLinear_of_opNorm_le_one _ ?_ fun t => ?_
  · rw [StronglyContinuousSemigroup.toGroupOfInverse_toSemigroup]
    exact hS
  · rcases le_or_gt 0 t with ht | ht
    · rw [StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonneg _ _ _ _ ht]
      exact S.contracting_real t ht
    · rw [StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonpos _ _ _ _ ht.le]
      exact T.contracting_real (-t) (neg_nonneg.mpr ht.le)

variable [CompleteSpace H]

/-- **Stone's theorem, converse direction (existence).** A self-adjoint operator `A` on a complex
Hilbert space is `-i` times the complex generator of a unitary C₀-group. -/
theorem _root_.IsSelfAdjoint.exists_isUnitary_complexGenerator_eq_I_smul {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) :
    ∃ (U : StronglyContinuousGroup H) (hU : U.IsUnitary),
      U.complexGenerator hU = Complex.I • A := by
  -- Step 1: Lumer–Phillips gives contraction semigroups `S` for `i • A` and `T` for `-i • A`.
  have hnegI : (-Complex.I).re = 0 := by simp
  have hdense : ∀ c : ℂ, Dense (((c • A.restrictScalars ℝ).domain : Set H)) := fun c => by
    have hset : (((c • A.restrictScalars ℝ).domain : Set H)) = (A.domain : Set H) :=
      Set.ext fun x => by rw [LinearPMap.smul_domain]; exact A.mem_restrictScalars_domain ℝ
    rw [hset]
    exact hA.dense_domain
  obtain ⟨S, hS⟩ :=
    (hA.isMDissipative_smul_restrictScalars Complex.I_re
      Complex.I_ne_zero).exists_contractionSemigroup_generator_eq (hdense _)
  obtain ⟨T, hT⟩ :=
    (hA.isMDissipative_smul_restrictScalars hnegI
      (neg_ne_zero.mpr Complex.I_ne_zero)).exists_contractionSemigroup_generator_eq (hdense _)
  -- Step 2: their generators are negatives of one another, so `S` and `T` glue into a C₀-group,
  -- which is unitary because the forward half is complex linear and both halves contract.
  have hgen : T.toStronglyContinuousSemigroup.generator =
      -S.toStronglyContinuousSemigroup.generator := by
    rw [hT, hS, LinearPMap.neg_smul]
  have hS' : S.toStronglyContinuousSemigroup.generator = (Complex.I • A).restrictScalars ℝ := by
    rw [hS, LinearPMap.restrictScalars_smul]
  set U : StronglyContinuousGroup H :=
    S.toStronglyContinuousSemigroup.toGroupOfInverse T.toStronglyContinuousSemigroup
      (StronglyContinuousSemigroup.comp_eq_id_of_generator_eq_neg hgen)
      (StronglyContinuousSemigroup.comp_eq_id_of_generator_eq_neg' hgen) with hUdef
  have hU : U.IsUnitary := isUnitary_toGroupOfInverse S T
    (StronglyContinuousSemigroup.isComplexLinear_of_generator_eq_restrictScalars _ hS') _ _
  -- Step 3: its complex generator is `i • A`, read off the generator of the forward half `S`.
  refine ⟨U, hU, U.complexGenerator_eq_of_generator_eq_restrictScalars hU ?_⟩
  rw [U.generator_def, hUdef, StronglyContinuousSemigroup.toGroupOfInverse_toSemigroup]
  exact hS'

/-- **Stone's theorem, converse direction.** A self-adjoint operator `A` on a complex Hilbert
space is `-i` times the complex generator of exactly one unitary C₀-group. -/
theorem _root_.IsSelfAdjoint.existsUnique_isUnitary_complexGenerator_eq_I_smul {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) :
    ∃! U : StronglyContinuousGroup H,
      ∃ hU : U.IsUnitary, U.complexGenerator hU = Complex.I • A := by
  obtain ⟨U, hU, hUA⟩ := hA.exists_isUnitary_complexGenerator_eq_I_smul
  exact ⟨U, ⟨hU, hUA⟩, fun V ⟨hV, hVA⟩ => eq_of_complexGenerator_eq hV hU (hVA.trans hUA.symm)⟩

/-- **Stone's theorem.** An operator `A` on a complex Hilbert space is self-adjoint if and only if
`i • A` is the complex generator of a unitary C₀-group. -/
theorem _root_.LinearPMap.isSelfAdjoint_iff_exists_isUnitary_complexGenerator_eq_I_smul
    (A : H →ₗ.[ℂ] H) :
    IsSelfAdjoint A ↔
      ∃ (U : StronglyContinuousGroup H) (hU : U.IsUnitary),
        U.complexGenerator hU = Complex.I • A := by
  refine ⟨fun hA => hA.exists_isUnitary_complexGenerator_eq_I_smul, ?_⟩
  rintro ⟨U, hU, hUA⟩
  have h := LinearPMap.isSelfAdjoint_smul_of_adjoint_eq_neg (c := -Complex.I) (by simp)
    (neg_ne_zero.mpr Complex.I_ne_zero) hU.complexGenerator_adjoint_eq_neg
  simpa [hUA, smul_smul] using h

end StronglyContinuousGroup

end TauCeti.Semigroups

end
