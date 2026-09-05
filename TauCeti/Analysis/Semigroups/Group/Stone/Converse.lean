/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Unitary
import TauCeti.Analysis.Semigroups.Group.InverseSemigroups
import TauCeti.Analysis.Semigroups.Generator.Neg
import TauCeti.Analysis.Semigroups.Dissipative.SkewSelfAdjoint
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Analysis.Semigroups.Generation.LumerPhillips

/-!
# Stone's theorem for unbounded self-adjoint operators

A self-adjoint operator `A` on a complex Hilbert space is `-i` times the generator of exactly one
unitary C₀-group, the group `e^{itA}`.  This completes the converse direction of Stone's theorem,
begun for bounded `A` in `TauCeti.Analysis.Semigroups.Group.Stone.Basic`.  Together with the
skew-adjointness of the generator of a unitary group
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.complexGenerator_adjoint_eq_neg`) this
characterizes the self-adjoint operators as the operators `A` with `i • A` the complex
generator of a unitary group.

The construction is the classical one.  The real restrictions of `i • A` and `-i • A` are
m-dissipative (`IsSelfAdjoint.isMDissipative_smul_restrictScalars` at `c = ± i`), so by
Lumer--Phillips each generates a contraction semigroup.  Their generators
are negatives of one another, so their equal-time operators are mutually inverse and the two
semigroups glue into a C₀-group
(`TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse`, the inverse hypotheses being
`StronglyContinuousSemigroup.comp_eq_id_of_generator_eq_neg` and its primed variant).  The glued
group is
complex linear because both halves are (their generators are real restrictions of complex-linear
partial maps), and unitary because it contracts in both time directions.  Its complex generator
is `i • A`, and a unitary group is determined by its complex generator.

## Main results

* `IsSelfAdjoint.existsUnique_isUnitary_complexGenerator_eq`: **Stone's theorem, converse
  direction**: a self-adjoint operator `A` has exactly one unitary C₀-group with complex
  generator `i • A`.
* `LinearPMap.isSelfAdjoint_iff_exists_isUnitary_complexGenerator` is **Stone's theorem** as a
  characterization of self-adjoint operators.

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

variable [CompleteSpace H]

/-- **Stone's theorem, converse direction (existence).** A self-adjoint operator `A` on a complex
Hilbert space is `-i` times the complex generator of a unitary C₀-group. -/
theorem _root_.IsSelfAdjoint.exists_isUnitary_complexGenerator_eq {A : H →ₗ.[ℂ] H}
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
  -- Step 2: their generators are negatives of one another, so `S` and `T` glue into a C₀-group.
  have hgen : T.toStronglyContinuousSemigroup.generator =
      -S.toStronglyContinuousSemigroup.generator := by
    rw [hT, hS, LinearPMap.neg_smul]
  have hS' : S.toStronglyContinuousSemigroup.generator = (Complex.I • A).restrictScalars ℝ := by
    rw [hS, LinearPMap.restrictScalars_smul]
  have hT' : T.toStronglyContinuousSemigroup.generator =
      ((-Complex.I) • A).restrictScalars ℝ := by
    rw [hT, LinearPMap.restrictScalars_smul]
  have hSlin : S.toStronglyContinuousSemigroup.IsComplexLinear :=
    StronglyContinuousSemigroup.isComplexLinear_of_generator_eq_restrictScalars _ hS'
  have hTlin : T.toStronglyContinuousSemigroup.IsComplexLinear :=
    StronglyContinuousSemigroup.isComplexLinear_of_generator_eq_restrictScalars _ hT'
  set U : StronglyContinuousGroup H :=
    S.toStronglyContinuousSemigroup.toGroupOfInverse T.toStronglyContinuousSemigroup
      (StronglyContinuousSemigroup.comp_eq_id_of_generator_eq_neg hgen)
      (StronglyContinuousSemigroup.comp_eq_id_of_generator_eq_neg' hgen) with hUdef
  have hpos : ∀ {t : ℝ}, 0 ≤ t → U t = S.toStronglyContinuousSemigroup.realOperator t :=
    fun ht => StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonneg _ _ _ _ ht
  have hneg : ∀ {t : ℝ}, t ≤ 0 → U t = T.toStronglyContinuousSemigroup.realOperator (-t) :=
    fun ht => StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonpos _ _ _ _ ht
  -- Step 3: the glued group is complex linear and contractive, hence unitary.
  have hlin : ∀ (t : ℝ) (z : ℂ) (x : H), U t (z • x) = z • U t x := by
    intro t z x
    rcases le_or_gt 0 t with ht | ht
    · rw [hpos ht, StronglyContinuousSemigroup.realOperator_def]
      exact hSlin.map_smul _ z x
    · rw [hneg ht.le, StronglyContinuousSemigroup.realOperator_def]
      exact hTlin.map_smul _ z x
  have hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1 := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [hpos ht]
      exact S.contracting_real t ht
    · rw [hneg ht.le]
      exact T.contracting_real (-t) (neg_nonneg.mpr ht.le)
  have hU : U.IsUnitary := U.isUnitary_of_isComplexLinear_of_forall_norm_le_one hlin hnorm
  -- Step 4: its complex generator is `i • A`, read off the generator of the forward half `S`.
  refine ⟨U, hU, U.complexGenerator_eq_of_generator_eq_restrictScalars hU ?_⟩
  rw [U.generator_def, hUdef, StronglyContinuousSemigroup.toGroupOfInverse_toSemigroup]
  exact hS'

/-- **Stone's theorem, converse direction.** A self-adjoint operator `A` on a complex Hilbert
space is `-i` times the complex generator of exactly one unitary C₀-group. -/
theorem _root_.IsSelfAdjoint.existsUnique_isUnitary_complexGenerator_eq {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) :
    ∃! U : StronglyContinuousGroup H,
      ∃ hU : U.IsUnitary, U.complexGenerator hU = Complex.I • A := by
  obtain ⟨U, hU, hUA⟩ := hA.exists_isUnitary_complexGenerator_eq
  exact ⟨U, ⟨hU, hUA⟩, fun V ⟨hV, hVA⟩ => eq_of_complexGenerator_eq hV hU (hVA.trans hUA.symm)⟩

/-- **Stone's theorem.** An operator `A` on a complex Hilbert space is self-adjoint if and only if
`i • A` is the complex generator of a unitary C₀-group. -/
theorem _root_.LinearPMap.isSelfAdjoint_iff_exists_isUnitary_complexGenerator (A : H →ₗ.[ℂ] H) :
    IsSelfAdjoint A ↔
      ∃ (U : StronglyContinuousGroup H) (hU : U.IsUnitary),
        U.complexGenerator hU = Complex.I • A := by
  refine ⟨fun hA => hA.exists_isUnitary_complexGenerator_eq, ?_⟩
  rintro ⟨U, hU, hUA⟩
  have hdense : Dense ((U.complexGenerator hU).domain : Set H) := by
    rw [U.complexGenerator_domain]
    exact U.dense_complexDomain hU
  have h := LinearPMap.isSelfAdjoint_neg_I_smul_of_adjoint_eq_neg hdense
    hU.complexGenerator_adjoint_eq_neg
  simpa [hUA, smul_smul] using h

end StronglyContinuousGroup

end TauCeti.Semigroups

end
