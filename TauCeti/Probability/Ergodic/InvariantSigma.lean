/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Cameron Freer's `cameronfreer/exchangeability`.
-/
module

public import TauCeti.Probability.Ergodic.FixedSpace
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Invariant measurable representatives

Within the ambient-almost-everywhere strongly measurable real-valued functions, this file
identifies almost-everywhere invariance under a nonsingular endomorphism with almost-everywhere
strong measurability for Mathlib's invariant σ-algebra.

The nontrivial direction replaces an almost invariant real-valued function by a pointwise
invariant representative.  For an ambient-measurable representative `g`, the replacement is the
real part of

`limsup (fun n => g (T^[n] ω))`.

Dropping the first term does not change this limsup, so the replacement is pointwise invariant.
Nonsingularity transports the original a.e. invariance along every iterate, making the replacement
a.e. equal to `g`.

## Main results

* `aestronglyMeasurable_invariants_of_comp_ae_eq` — an ambient-a.e. strongly measurable,
  a.e. invariant function has an invariant measurable representative;
* `aestronglyMeasurable_invariants_iff_comp_ae_eq` — the characteristic equivalence;
* `fixedSpace_eq_lpMeas_invariants` — the `Lᵖ` fixed space is exactly Mathlib's `lpMeas` subspace
  for the invariant σ-algebra.

The construction and proof are adapted from
`cameronfreer/exchangeability`, `Exchangeability/Ergodic/ShiftInvariantRepresentatives.lean` and
`Exchangeability/Ergodic/InvariantSigma.lean`, at commit
`e0532e59ceff23edab44dda9ab0655debbc9cc22`.  This version is generalized from the path-space shift
to an arbitrary nonsingular endomorphism at the function level (and a measure-preserving one on
`Lᵖ`) and uses
`MeasurableSpace.invariants` directly, as required by the Exchangeability roadmap.
-/

public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Invariant representatives -/

/-- A canonical pointwise invariant candidate obtained by taking the limsup along forward
orbits. -/
private def invariantRepresentative (T : Ω → Ω) (g : Ω → ℝ) : Ω → ℝ :=
  fun ω => (limsup (fun n : ℕ => (g ((T^[n]) ω) : EReal)) atTop).toReal

private theorem measurable_invariantRepresentative {T : Ω → Ω} (hT : Measurable T)
    {g : Ω → ℝ} (hg : Measurable g) :
    Measurable (invariantRepresentative T g) := by
  apply measurable_ereal_toReal.comp
  apply Measurable.limsup
  intro n
  exact measurable_coe_real_ereal.comp (hg.comp (hT.iterate n))

omit [MeasurableSpace Ω] in
private theorem invariantRepresentative_comp (T : Ω → Ω) (g : Ω → ℝ) :
    invariantRepresentative T g ∘ T = invariantRepresentative T g := by
  funext ω
  apply congrArg EReal.toReal
  simpa only [invariantRepresentative, comp_apply, Function.iterate_succ_apply,
    Nat.succ_eq_add_one] using
    limsup_nat_add (fun n : ℕ => (g ((T^[n]) ω) : EReal)) 1

private theorem iterate_comp_ae_eq_of_comp_ae_eq {T : Ω → Ω}
    (hT : Measure.QuasiMeasurePreserving T μ μ) {g : Ω → ℝ} (hg : g ∘ T =ᵐ[μ] g) :
    ∀ n : ℕ, g ∘ T^[n] =ᵐ[μ] g := by
  intro n
  induction n with
  | zero => simp
  | succ n hn =>
      rw [Function.iterate_succ]
      exact (hT.ae_eq_comp hn).trans hg

private theorem invariantRepresentative_ae_eq {T : Ω → Ω}
    (hT : Measure.QuasiMeasurePreserving T μ μ) {g : Ω → ℝ} (hg : g ∘ T =ᵐ[μ] g) :
    invariantRepresentative T g =ᵐ[μ] g := by
  have hiter : ∀ᵐ ω ∂μ, ∀ n : ℕ, g ((T^[n]) ω) = g ω := by
    rw [ae_all_iff]
    exact fun n => iterate_comp_ae_eq_of_comp_ae_eq hT hg n
  filter_upwards [hiter] with ω hω
  have hconst :
      (fun n : ℕ => (g ((T^[n]) ω) : EReal)) = fun _ => (g ω : EReal) := by
    funext n
    exact congrArg (fun x : ℝ => (x : EReal)) (hω n)
  simp only [invariantRepresentative, hconst, limsup_const, EReal.toReal_coe]

/-- An ambient-almost-everywhere strongly measurable, almost-everywhere invariant real-valued
function has a representative measurable for Mathlib's invariant σ-algebra.

The nonsingular endomorphism is arbitrary: path-space shift is the specialization used by the
Koopman route to de Finetti's theorem. -/
theorem aestronglyMeasurable_invariants_of_comp_ae_eq {T : Ω → Ω}
    (hT : Measure.QuasiMeasurePreserving T μ μ) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfix : f ∘ T =ᵐ[μ] f) :
    AEStronglyMeasurable[MeasurableSpace.invariants T] f μ := by
  let g := hf.mk f
  have hg_meas : Measurable g := hf.stronglyMeasurable_mk.measurable
  have hg_eq : g =ᵐ[μ] f := hf.ae_eq_mk.symm
  have hg_fix : g ∘ T =ᵐ[μ] g :=
    (hT.ae_eq_comp hg_eq).trans (hfix.trans hg_eq.symm)
  let g' := invariantRepresentative T g
  have hg'_meas : Measurable g' := measurable_invariantRepresentative hT.measurable hg_meas
  have hg'_inv : g' ∘ T = g' := invariantRepresentative_comp T g
  have hg'_meas_inv : Measurable[MeasurableSpace.invariants T] g' :=
    (MeasurableSpace.measurable_invariants_dom.mpr
      ⟨hg'_meas, fun s _ => congrArg (fun q : Ω → ℝ => q ⁻¹' s) hg'_inv⟩)
  exact hg'_meas_inv.aestronglyMeasurable.congr
    ((invariantRepresentative_ae_eq hT hg_fix).trans hg_eq)

/-- A function almost-everywhere strongly measurable for the invariant σ-algebra is almost
everywhere fixed by composition. -/
theorem AEStronglyMeasurable.comp_ae_eq_of_invariants {T : Ω → Ω}
    {E : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSingletonClass E]
    (hT : Measure.QuasiMeasurePreserving T μ μ) {f : Ω → E}
    (hf : AEStronglyMeasurable[MeasurableSpace.invariants T] f μ) :
    f ∘ T =ᵐ[μ] f := by
  let g := hf.mk f
  have hg_meas : Measurable[MeasurableSpace.invariants T] g :=
    hf.stronglyMeasurable_mk.measurable
  have hg_eq : g =ᵐ[μ] f := hf.ae_eq_mk.symm
  exact (hT.ae_eq_comp hg_eq.symm).trans
    ((EventuallyEq.of_eq (MeasurableSpace.comp_eq_of_measurable_invariants hg_meas)).trans hg_eq)

/-- Within the ambient-almost-everywhere strongly measurable real-valued functions,
almost-everywhere strong measurability for the invariant σ-algebra is equivalent to
almost-everywhere invariance under composition. -/
@[simp]
theorem aestronglyMeasurable_invariants_iff_comp_ae_eq {T : Ω → Ω}
    (hT : Measure.QuasiMeasurePreserving T μ μ) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[MeasurableSpace.invariants T] f μ ↔ f ∘ T =ᵐ[μ] f :=
  ⟨fun h => AEStronglyMeasurable.comp_ae_eq_of_invariants hT h,
    aestronglyMeasurable_invariants_of_comp_ae_eq hT hf⟩

/-! ## The invariant subspace of `Lᵖ` -/

variable {p : ℝ≥0∞}

/-- Membership in the `Lᵖ` fixed space is equivalent to almost-everywhere strong measurability for
the invariant σ-algebra. -/
theorem mem_fixedSpace_iff_aestronglyMeasurable_invariants {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ p μ) :
    f ∈ fixedSpace (𝕜 := ℝ) T hT ↔
      AEStronglyMeasurable[MeasurableSpace.invariants T] f μ := by
  rw [mem_fixedSpace_iff, compMeasurePreserving_eq_self_iff]
  exact
    (aestronglyMeasurable_invariants_iff_comp_ae_eq hT.quasiMeasurePreserving
      (Lp.aestronglyMeasurable f)).symm

/-- The `Lᵖ` fixed space of a measure-preserving endomorphism is the subspace of functions
almost-everywhere strongly measurable for its invariant σ-algebra. -/
theorem fixedSpace_eq_lpMeas_invariants (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    fixedSpace (𝕜 := ℝ) (E := ℝ) (p := p) T hT =
      lpMeas ℝ ℝ (MeasurableSpace.invariants T) p μ := by
  ext f
  rw [mem_fixedSpace_iff_aestronglyMeasurable_invariants hT,
    mem_lpMeas_iff_aestronglyMeasurable]

end Probability

end TauCeti
