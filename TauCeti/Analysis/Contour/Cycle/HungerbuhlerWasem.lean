/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
public import TauCeti.Analysis.Contour.Cycle.PrincipalValue
public import TauCeti.Analysis.Contour.HungerbuhlerWasem

/-!
# The Hungerbühler–Wasem generalized residue theorem for contour cycles

This file lifts HW Thm 3.3 from one parametrized closed curve to a finite formal integer cycle
`C` of them. For `f` holomorphic on `U ∖ S` and meromorphic at each point of the finite `S ⊆ U`,
and a cycle `C` in `U` that is **null-homologous** there, whose curves are piecewise-`C¹`
immersions rooted off `S` and satisfy the regularity conditions (A′) and (B),

`PV ∮_C f = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

each singularity weighted by the **generalized, non-integer** winding number of the cycle about
it — so the singularities may lie **on** `C`. This removes the first of the narrowings the
roadmap records for the pinned single-curve form
(`TauCeti.Contour.hungerbuhlerWasem_residueTheorem`), which the paper states for a cycle.

Just as for the classical residue theorem for cycles
(`TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous`), this is not the single-curve
theorem applied generator by generator. Null homology is asked of `C` alone: its generators may
each wind around the holes of `U`, and the point of allowing formal integer combinations is
precisely that a cycle can bound while its pieces do not. So the proof runs one rung lower down.
A polar-part decomposition `f = g + ∑_{s ∈ S} P_s` on `U` is fixed once, and the
null-homology-free splitting

`PV ∮_γ f = ∮_γ g + 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`

(`PolarPartDecomposition.hasCauchyPV_analyticRemainder_add_residue_sum_of_conditions`)
is summed over the generators with their coefficients — the principal value being additive over
a cycle by construction (`TauCeti.Contour.Cycle.cauchyPV`). Only then is the analytic remainder
`g` discharged, by the homology Cauchy theorem for cycles
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`), which does see the cancellations between
generators.

The remaining narrowings of the single-curve form are inherited unchanged: `S` is finite, `f` is
`MeromorphicAt` at each of its points, and each generator is rooted off `S`.

## Main results

* `TauCeti.Contour.Cycle.hasCauchyPV_analyticRemainder_add_residue_sum` — the residue sum splits
  off the cycle's principal value, before any null-homology hypothesis is used.
* `TauCeti.Contour.Cycle.hungerbuhlerWasem_residueTheorem` — HW Thm 3.3 for a null-homologous
  cycle.
* `TauCeti.Contour.Cycle.hungerbuhlerWasem_residueTheorem_of_simple_poles` — the unconditional
  regime, conditions (A′) and (B) being automatic at worst-simple poles.

## Provenance

No formal source is vendored: the statements are assembled here from this repository's
single-curve Hungerbühler–Wasem theory and its homology Cauchy theorem for cycles, which are
themselves migrated from the AINTLIB `LeanModularForms` development.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Thm 3.3 — there stated for a cycle.
-/

public section

open Complex Set

namespace TauCeti.Contour.Cycle

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {C : Cycle}

/-- **The residue sum splits off a cycle's principal value.** For a fixed polar-part
decomposition of `f` on `U` at `S`, and a cycle in `U` whose curves are piecewise-`C¹`
immersions rooted off `S` and satisfying conditions (A′) and (B), the Cauchy principal value of
`f` along the cycle exists and is the ordinary cycle integral of the analytic remainder plus
`2πi` times the winding-weighted residue sum.

Nothing is assumed about null-homology, of the cycle or of its generators: the identity is
summed from its single-curve form
(`PolarPartDecomposition.hasCauchyPV_analyticRemainder_add_residue_sum_of_conditions`)
over the generators of the cycle, each of which may wind arbitrarily around the holes of `U`. -/
theorem hasCauchyPV_analyticRemainder_add_residue_sum (decomp : PolarPartDecomposition f S U)
    (hU : IsOpen U) (h_ord : ∀ s : S, decomp.order s = meromorphicPolarOrderAt f ↑s)
    (hSU : (S : Set ℂ) ⊆ U) (hmero : ∀ s ∈ S, MeromorphicAt f s) (hCU : IsIn C U)
    (h_imm : ∀ γ ∈ FreeAbelianGroup.support C, IsPwC1ImmersionOn (⇑γ) γ.a γ.b)
    (hbase : ∀ γ ∈ FreeAbelianGroup.support C, γ γ.a ∉ (S : Set ℂ))
    (hA : ∀ γ ∈ FreeAbelianGroup.support C, ConditionAprime (⇑γ) γ.a γ.b f S)
    (hB : ∀ γ ∈ FreeAbelianGroup.support C, ConditionB (⇑γ) γ.a γ.b f) :
    HasCauchyPV C f (integral decomp.analyticRemainder C
      + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s) := by
  classical
  -- The single-curve splitting, applied to each generator in the canonical support.
  have hgen : ∀ γ ∈ FreeAbelianGroup.support C, TauCeti.Contour.HasCauchyPV (⇑γ) γ.a γ.b f
      ((∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
        + 2 * (Real.pi : ℂ) * Complex.I *
            ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := fun γ hγ ↦
    decomp.hasCauchyPV_analyticRemainder_add_residue_sum_of_conditions hU h_ord hSU (h_imm γ hγ)
      γ.source_eq_target (hbase γ hγ)
      (fun t ht ↦ isIn_iff.mp hCU (mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩)) hmero (hA γ hγ)
      (hB γ hγ)
  -- Regroup the double sum over generators and poles, pole index outermost.
  have hswap : ∀ γ : PiecewiseC1ClosedCurve,
      (FreeAbelianGroup.coeff γ C : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I *
            ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s)
        = ∑ s ∈ S, 2 * (Real.pi : ℂ) * Complex.I *
            ((FreeAbelianGroup.coeff γ C : ℂ) *
              TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := fun γ ↦ by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hval : (∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
        ((∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
          + 2 * (Real.pi : ℂ) * Complex.I *
              ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s))
      = integral decomp.analyticRemainder C
        + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s :=
    calc
      ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
            ((∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
              + 2 * (Real.pi : ℂ) * Complex.I *
                  ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s)
          = (∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
                (∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t)))
              + ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
                  (2 * (Real.pi : ℂ) * Complex.I *
                    ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := by
            simp only [smul_add]
            exact Finset.sum_add_distrib
      _ = integral decomp.analyticRemainder C
            + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s := by
            rw [← integral_eq_sum_support]
            refine congrArg _ ?_
            simp only [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
            rw [Finset.sum_congr rfl fun γ _ ↦ hswap γ, Finset.sum_comm, Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ ↦ ?_
            rw [windingNumber_eq_sum_support, Finset.sum_mul, Finset.mul_sum]
  rw [← hval]
  exact HasCauchyPV.of_generators hgen

/-- **The Hungerbühler–Wasem generalized residue theorem for a contour cycle** (HW Thm 3.3).
Let `U` be open, `S ⊆ U` finite, `f` holomorphic on `U ∖ S` and meromorphic at each point of
`S`, and let `C` be a contour cycle in `U`, **null-homologous** in `U`, whose curves are
piecewise-`C¹` immersions rooted off `S` and satisfy conditions (A′) and (B). Then the Cauchy
principal value of `f` along `C` exists and

`PV ∮_C f = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

each singularity weighted by the **generalized** winding number of `C` about it. The
singularities are allowed to lie **on** `C`, where those weights are in general not integers and
the contour integral only exists as a principal value.

Null-homology is asked of the cycle only, never of its generators, so the theorem covers the
combinations that make cycles worth having: a difference of two homologous loops around a hole of
`U`, neither of them null-homologous, is null-homologous. Its `S = ∅` case is the homology Cauchy
theorem for cycles
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`), and its one-generator case is the single-curve
theorem `TauCeti.Contour.hungerbuhlerWasem_residueTheorem`. Where the trace of `C` avoids `S`
the principal value is an ordinary integral and the statement is the classical residue theorem
for cycles (`TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous`), which needs neither
immersions nor the conditions. -/
theorem hungerbuhlerWasem_residueTheorem (hU : IsOpen U) (S : Finset ℂ)
    (hSU : (S : Set ℂ) ⊆ U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hCU : IsIn C U)
    (h_imm : ∀ γ ∈ FreeAbelianGroup.support C, IsPwC1ImmersionOn (⇑γ) γ.a γ.b)
    (hbase : ∀ γ ∈ FreeAbelianGroup.support C, γ γ.a ∉ (S : Set ℂ))
    (hnull : IsNullHomologous C U)
    (hA : ∀ γ ∈ FreeAbelianGroup.support C, ConditionAprime (⇑γ) γ.a γ.b f S)
    (hB : ∀ γ ∈ FreeAbelianGroup.support C, ConditionB (⇑γ) γ.a γ.b f) :
    HasCauchyPV C f
      (2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s) := by
  have h := hasCauchyPV_analyticRemainder_add_residue_sum
    (PolarPartDecomposition.ofMeromorphic hU hf hmero) hU
    (fun s ↦ PolarPartDecomposition.ofMeromorphic_order s) hSU hmero hCU h_imm hbase hA hB
  rwa [homologyCauchyTheorem hU hCU
    (PolarPartDecomposition.ofMeromorphic hU hf hmero).analyticRemainder_differentiableOn hnull,
    zero_add] at h

/-- **The generalized residue theorem for a contour cycle with simple poles** — HW Thm 3.3's
unconditional regime for cycles. When every prescribed singularity is at worst a simple pole,
conditions (A′) and (B) hold automatically along each curve of the cycle
(`TauCeti.Contour.conditionAprime_of_simple_poles`,
`TauCeti.Contour.conditionB_of_simple_poles`), leaving no regularity hypotheses beyond the
immersions. This is the form the argument principle consumes, a logarithmic derivative having
only simple poles. -/
theorem hungerbuhlerWasem_residueTheorem_of_simple_poles (hU : IsOpen U) (S : Finset ℂ)
    (hSU : (S : Set ℂ) ⊆ U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hCU : IsIn C U)
    (h_imm : ∀ γ ∈ FreeAbelianGroup.support C, IsPwC1ImmersionOn (⇑γ) γ.a γ.b)
    (hbase : ∀ γ ∈ FreeAbelianGroup.support C, γ γ.a ∉ (S : Set ℂ))
    (hnull : IsNullHomologous C U)
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV C f
      (2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s) := by
  have hγU : ∀ γ ∈ FreeAbelianGroup.support C, ∀ t ∈ uIcc γ.a γ.b, γ t ∈ U := fun γ hγ t ht ↦
    isIn_iff.mp hCU (mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩)
  refine hungerbuhlerWasem_residueTheorem hU S hSU hf hmero hCU h_imm hbase hnull
    (fun γ hγ ↦ conditionAprime_of_simple_poles hU (h_imm γ hγ) ?_ (hγU γ hγ) hf h_simple)
    (fun γ hγ ↦ conditionB_of_simple_poles hU (hγU γ hγ) hf h_simple)
  rcases le_total γ.a γ.b with h | h
  · rw [min_eq_left h]; exact hbase γ hγ
  · rw [min_eq_right h, ← γ.source_eq_target]; exact hbase γ hγ

end TauCeti.Contour.Cycle

end
