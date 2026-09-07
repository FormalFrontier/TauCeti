/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Similarity
public import TauCeti.Analysis.Semigroups.Generator.Basic
import TauCeti.Analysis.Semigroups.Generator.Uniqueness

/-!
# The generator of a similar semigroup

The transported semigroup `S.similar e` of `TauCeti.Analysis.Semigroups.Similarity` has the
transported generator: the domain is the image of `D(A)` under `e`, and the action is
`e ∘ A ∘ e⁻¹`.

The first application is a commutation criterion.  A semigroup whose generator commutes with an
invertible operator `J` has `J ∘ S t ∘ J⁻¹` with the same generator, so by uniqueness it agrees
with `S`; this is how complex linearity of a semigroup is read off its generator.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.mem_similar_domain_iff`: `y` is in the
  transported generator domain iff `e⁻¹ y` is in the original one.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.similar_generator_apply`: the transported
  generator is `e ∘ A ∘ e⁻¹`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.similar_eq_self_of_generator_comm` and
  `map_comm_of_generator_comm`: the commutation criterion, `S.similar e = S`
  when `e` commutes with the generator, so `S t` commutes with `e`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.2.1.
-/

public section

noncomputable section

open scoped NNReal
open Filter

namespace TauCeti.Semigroups

namespace StronglyContinuousSemigroup

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The generator difference quotient of the transported semigroup is the transported difference
quotient of `S`. -/
private theorem similar_genQuot_eq (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ)
    (y : Y) : (1 / t) • ((S.similar e).realOperator t y - y) =
      e ((1 / t) • (S.realOperator t (e.symm y) - e.symm y)) := by
  rw [similar_realOperator_apply, e.map_smul, e.map_sub, e.apply_symm_apply]

/-- `y` lies in the generator domain of the transported semigroup iff `e⁻¹ y` lies in the
generator domain of `S`. -/
@[simp]
theorem mem_similar_domain_iff (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (y : Y) :
    y ∈ (S.similar e).domain ↔ e.symm y ∈ S.domain := by
  rw [mem_domain_iff_tendsto, mem_domain_iff_tendsto]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    refine ((e.symm.continuous.tendsto z).comp hz).congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, similar_genQuot_eq, e.symm_apply_apply]
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    refine ((e.continuous.tendsto z).comp hz).congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, similar_genQuot_eq]

/-- The generator of the transported semigroup is `e ∘ A ∘ e⁻¹`. -/
theorem similar_generator_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) {y : Y}
    (hy : y ∈ (S.similar e).domain) :
    (S.similar e).generator ⟨y, by rw [(S.similar e).generator_domain]; exact hy⟩ =
      e (S.generator ⟨e.symm y, by
        rw [S.generator_domain]
        exact (S.mem_similar_domain_iff e y).mp hy⟩) := by
  apply (S.similar e).generator_eq_of_tendsto hy
  refine ((e.continuous.tendsto _).comp
    (S.generator_tendsto ⟨e.symm y, (S.mem_similar_domain_iff e y).mp hy⟩)).congr'
    (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, similar_genQuot_eq]

/-- **Commutation criterion.** A C₀-semigroup whose generator commutes with an invertible
operator `e` (in the sense that `e` maps the generator domain onto itself and intertwines the
generator) is invariant under conjugation by `e`: `S.similar e = S`. -/
theorem similar_eq_self_of_generator_comm [CompleteSpace X] (S : StronglyContinuousSemigroup X)
    (e : X ≃L[ℝ] X) (hdom : ∀ x, e x ∈ S.domain ↔ x ∈ S.domain)
    (hcomm : ∀ (x : X) (hx : x ∈ S.generator.domain),
      S.generator ⟨e x, by rw [S.generator_domain, hdom, ← S.generator_domain]; exact hx⟩ =
        e (S.generator ⟨x, hx⟩)) :
    S.similar e = S := by
  refine eq_of_generator_eq (LinearPMap.ext ?_ fun y hy hy' => ?_)
  · ext y
    rw [(S.similar e).generator_domain, S.generator_domain, S.mem_similar_domain_iff,
      ← hdom (e.symm y), e.apply_symm_apply]
  · have hy₂ : y ∈ (S.similar e).domain := by rwa [(S.similar e).generator_domain] at hy
    have hy₃ : e.symm y ∈ S.generator.domain := by
      rw [S.generator_domain]
      exact (S.mem_similar_domain_iff e y).mp hy₂
    rw [S.similar_generator_apply e hy₂, ← hcomm (e.symm y) hy₃]
    congr 1
    exact Subtype.ext (e.apply_symm_apply y)

/-- The operators of a C₀-semigroup commute with an invertible operator that commutes with the
generator. -/
theorem map_comm_of_generator_comm [CompleteSpace X]
    (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] X) (hdom : ∀ x, e x ∈ S.domain ↔ x ∈ S.domain)
    (hcomm : ∀ (x : X) (hx : x ∈ S.generator.domain),
      S.generator ⟨e x, by rw [S.generator_domain, hdom, ← S.generator_domain]; exact hx⟩ =
        e (S.generator ⟨x, hx⟩))
    (t : ℝ≥0) (x : X) : S t (e x) = e (S t x) := by
  have h := congrArg (fun T : StronglyContinuousSemigroup X => T t (e x))
    (S.similar_eq_self_of_generator_comm e hdom hcomm)
  rw [similar_apply_apply, e.symm_apply_apply] at h
  exact h.symm

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
