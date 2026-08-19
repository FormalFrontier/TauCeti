/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
public import TauCeti.Analysis.Contour.Cycle.Basic

/-!
# The Cauchy principal value along a contour cycle

A contour cycle is a formal integer combination of closed piecewise-`C¹` curves, and every
additive invariant of curves extends to it by linearity. This file carries out that extension
for the set-level Cauchy principal value, the invariant the Hungerbühler–Wasem generalized
residue theorem evaluates when singularities of the integrand lie **on** the contour.

The direction of the definitions is opposite to the single-curve case, and deliberately so.
For one curve the predicate `TauCeti.Contour.HasCauchyPV` comes first — it is a genuine
analytic statement about symmetric excision — and the value `TauCeti.Contour.cauchyPV` is read
off it. For a cycle the **value** comes first: `Cycle.cauchyPV f` is the additive extension of
`TauCeti.Contour.cauchyPV`, hence an `AddMonoidHom` by construction, exactly like
`Cycle.integral` and `Cycle.windingNumber`. The predicate `Cycle.HasCauchyPV` is then existence
along each curve of the canonical support together with that value. Defining the predicate
first, by simultaneously truncating all the generators, would not have produced an additive
value: a cancelling pair of generators would have to be seen to cancel truncation by
truncation, which no argument supplies before the limit is taken.

Nothing here identifies a principal value with an ordinary integral. Where the ordinary contour
integrand *is* interval-integrable along each generator, the two agree
(`Cycle.hasCauchyPV_integral`), which is the only bridge between them.

## Main definitions

* `TauCeti.Contour.Cycle.cauchyPV` — the additive extension of the single-curve principal value.
* `TauCeti.Contour.Cycle.CauchyPVExists` — the principal value exists along every curve of the
  canonical support.
* `TauCeti.Contour.Cycle.HasCauchyPV` — existence, together with the value.

## Main results

* `TauCeti.Contour.Cycle.cauchyPV_eq_sum_support` — the value as a coefficient-weighted sum.
* `TauCeti.Contour.Cycle.cauchyPVExists_iff` — existence along the canonical support.
* `TauCeti.Contour.Cycle.hasCauchyPV_iff` — the predicate as its two clauses.
* `TauCeti.Contour.Cycle.HasCauchyPV.of_generators` — a per-generator family of principal values
  assembles into the cycle's.
* `TauCeti.Contour.Cycle.HasCauchyPV.unique` — the value in the predicate is determined.
* `TauCeti.Contour.Cycle.hasCauchyPV_integral` — where the contour integrand is
  interval-integrable along each generator, the principal value is the ordinary cycle integral.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), §3.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Contour

namespace Cycle

variable {f : ℂ → ℂ} {C D : Cycle}

/-- The Cauchy principal value of `f` along a cycle, obtained by additively extending the
single-curve principal value `TauCeti.Contour.cauchyPV` from generators. Like every value read
off a junk-valued function, it is meaningful exactly where `Cycle.CauchyPVExists` holds. -/
def cauchyPV (f : ℂ → ℂ) : Cycle →+ ℂ :=
  FreeAbelianGroup.lift fun γ : PiecewiseC1ClosedCurve ↦ TauCeti.Contour.cauchyPV γ γ.a γ.b f

/-- The principal value along a one-generator cycle is the principal value along that curve. -/
@[simp]
theorem cauchyPV_of (γ : PiecewiseC1ClosedCurve) (f : ℂ → ℂ) :
    cauchyPV f (FreeAbelianGroup.of γ) = TauCeti.Contour.cauchyPV γ γ.a γ.b f := by
  rw [cauchyPV, FreeAbelianGroup.lift_apply_of]

/-- The principal value along a raw closed curve bundled as a one-generator cycle is its raw
principal value. -/
theorem cauchyPV_of_raw {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (f : ℂ → ℂ) :
    cauchyPV f (FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of γ hγ hclosed)) =
      TauCeti.Contour.cauchyPV γ a b f := by
  rw [cauchyPV_of]
  simpa only [PiecewiseC1ClosedCurve.of_a, PiecewiseC1ClosedCurve.of_b] using
    TauCeti.Contour.cauchyPV_congr_curve (f := f) fun _ ht ↦
      PiecewiseC1ClosedCurve.of_apply γ hγ hclosed (uIoo_subset_uIcc_self ht)

/-- The principal value along a cycle is the coefficient-weighted sum of the principal values
along the curves of its canonical support. -/
theorem cauchyPV_eq_sum_support (f : ℂ → ℂ) (C : Cycle) :
    cauchyPV f C = ∑ γ ∈ FreeAbelianGroup.support C,
      FreeAbelianGroup.coeff γ C • TauCeti.Contour.cauchyPV γ γ.a γ.b f := by
  conv_lhs => rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of C]
  simp only [map_sum, map_zsmul, cauchyPV_of]

/-- The Cauchy principal value of `f` along a cycle **exists** when it exists along every curve
of the canonical support. Curves that cancel out of the cycle impose no condition. -/
def CauchyPVExists (C : Cycle) (f : ℂ → ℂ) : Prop :=
  ∀ γ ∈ FreeAbelianGroup.support C, TauCeti.Contour.CauchyPVExists γ γ.a γ.b f

/-- Characterization of `Cycle.CauchyPVExists` as existence along every curve of the canonical
support — the eliminator/constructor interface, so downstream users need not unfold the
definition. -/
theorem cauchyPVExists_iff :
    CauchyPVExists C f ↔
      ∀ γ ∈ FreeAbelianGroup.support C, TauCeti.Contour.CauchyPVExists γ γ.a γ.b f :=
  Iff.rfl

/-- The Cauchy principal value of `f` along the cycle `C` exists and equals `v`. -/
def HasCauchyPV (C : Cycle) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  CauchyPVExists C f ∧ cauchyPV f C = v

/-- `Cycle.HasCauchyPV` unfolded into its two clauses — existence along every curve of the
canonical support, and the value — so consumers need not unfold the definition.

Deliberately not `@[simp]`: it unfolds the predicate, so it would take the left-hand sides of
`hasCauchyPV_of_iff`, `hasCauchyPV_zero` and `hasCauchyPV_neg_iff` out of simp-normal form.
Those three are the normal forms `simp` should reach for — on a generator, on `0`, and under
negation — and they carry the `@[simp]` annotation instead. -/
theorem hasCauchyPV_iff {v : ℂ} :
    HasCauchyPV C f v ↔ CauchyPVExists C f ∧ cauchyPV f C = v := Iff.rfl

/-- Existence of the principal value along a one-generator cycle is exactly existence along its
generating curve. -/
@[simp]
theorem cauchyPVExists_of_iff (γ : PiecewiseC1ClosedCurve) :
    CauchyPVExists (FreeAbelianGroup.of γ) f ↔
      TauCeti.Contour.CauchyPVExists γ γ.a γ.b f := by
  simp [CauchyPVExists, FreeAbelianGroup.support_of]

/-- A one-generator cycle has principal value `v` exactly when its generating curve does. -/
@[simp]
theorem hasCauchyPV_of_iff (γ : PiecewiseC1ClosedCurve) {v : ℂ} :
    HasCauchyPV (FreeAbelianGroup.of γ) f v ↔ TauCeti.Contour.HasCauchyPV γ γ.a γ.b f v := by
  constructor
  · intro h
    have hex := (cauchyPVExists_of_iff (f := f) γ).mp h.1
    have hv := hex.hasCauchyPV_cauchyPV
    rwa [← cauchyPV_of γ f, h.2] at hv
  · intro h
    exact ⟨(cauchyPVExists_of_iff (f := f) γ).mpr (TauCeti.Contour.CauchyPVExists.intro h),
      (cauchyPV_of γ f).trans h.cauchyPV_eq⟩

/-- Reading the value off the predicate. -/
theorem HasCauchyPV.cauchyPV_eq {v : ℂ} (h : HasCauchyPV C f v) : cauchyPV f C = v := h.2

/-- The predicate implies existence. -/
theorem HasCauchyPV.cauchyPVExists {v : ℂ} (h : HasCauchyPV C f v) : CauchyPVExists C f := h.1

/-- The value in the predicate is determined by the cycle and the integrand. -/
theorem HasCauchyPV.unique {v₁ v₂ : ℂ} (h₁ : HasCauchyPV C f v₁) (h₂ : HasCauchyPV C f v₂) :
    v₁ = v₂ := h₁.2 ▸ h₂.2

/-- Where the principal value exists, the predicate holds at the canonical value. -/
theorem CauchyPVExists.hasCauchyPV_cauchyPV (h : CauchyPVExists C f) :
    HasCauchyPV C f (cauchyPV f C) := ⟨h, rfl⟩

/-- **Assembling a cycle's principal value from its generators.** If the principal value of `f`
along each curve `γ` of the canonical support of `C` exists and equals `w γ`, then the principal
value along `C` exists and is the coefficient-weighted sum of the `w γ`. -/
theorem HasCauchyPV.of_generators {w : PiecewiseC1ClosedCurve → ℂ}
    (h : ∀ γ ∈ FreeAbelianGroup.support C, TauCeti.Contour.HasCauchyPV γ γ.a γ.b f (w γ)) :
    HasCauchyPV C f (∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C • w γ) := by
  refine ⟨fun γ hγ ↦ TauCeti.Contour.CauchyPVExists.intro (h γ hγ), ?_⟩
  rw [cauchyPV_eq_sum_support]
  exact Finset.sum_congr rfl fun γ hγ ↦ by rw [(h γ hγ).cauchyPV_eq]

/-- The zero cycle has principal value `0`, for every integrand. -/
@[simp]
theorem hasCauchyPV_zero (f : ℂ → ℂ) : HasCauchyPV (0 : Cycle) f 0 :=
  ⟨fun _ hγ ↦ absurd hγ (by simp), map_zero _⟩

/-- Principal values add over a sum of cycles, provided each side has one: the value is additive
by construction, and the canonical support of a sum lies in the union of the supports. -/
theorem HasCauchyPV.add {v₁ v₂ : ℂ} (h₁ : HasCauchyPV C f v₁) (h₂ : HasCauchyPV D f v₂) :
    HasCauchyPV (C + D) f (v₁ + v₂) := by
  classical
  refine ⟨fun γ hγ ↦ ?_, by rw [map_add, h₁.2, h₂.2]⟩
  rcases Finset.mem_union.mp (FreeAbelianGroup.support_add C D hγ) with hγC | hγD
  · exact h₁.1 γ hγC
  · exact h₂.1 γ hγD

/-- Negating a cycle negates its principal value. -/
@[simp]
theorem hasCauchyPV_neg_iff {v : ℂ} : HasCauchyPV (-C) f (-v) ↔ HasCauchyPV C f v := by
  simp only [HasCauchyPV, CauchyPVExists, FreeAbelianGroup.support_neg, map_neg, neg_inj]

/-- An integer multiple of a cycle has the correspondingly scaled principal value. -/
theorem HasCauchyPV.zsmul {v : ℂ} (h : HasCauchyPV C f v) (n : ℤ) :
    HasCauchyPV (n • C) f (n • v) := by
  refine ⟨fun γ hγ ↦ ?_, by rw [map_zsmul, h.2]⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact absurd hγ (by simp)
  · exact h.1 γ (by rwa [FreeAbelianGroup.support_zsmul n hn] at hγ)

/-- **The principal value extends the ordinary cycle integral.** If the contour integrand of `f`
is interval-integrable along every curve of the canonical support — as it is when no on-contour
singularity obstructs it — then the principal value along the cycle exists and is the ordinary
cycle integral. -/
theorem hasCauchyPV_integral (h : ∀ γ ∈ FreeAbelianGroup.support C,
    IntervalIntegrable (fun t ↦ f (γ t) * deriv (⇑γ) t) volume γ.a γ.b) :
    HasCauchyPV C f (integral f C) := by
  have hgen := HasCauchyPV.of_generators
    (w := fun γ : PiecewiseC1ClosedCurve ↦ ∫ t in γ.a..γ.b, f (γ t) * deriv (⇑γ) t)
    fun γ hγ ↦ TauCeti.Contour.HasCauchyPV.of_integrable (h γ hγ)
  refine ⟨hgen.1, hgen.2.trans ?_⟩
  rw [integral_eq_sum_support]
  exact Finset.sum_congr rfl fun γ _ ↦ congrArg _
    (intervalIntegral.integral_congr fun t _ ↦ by rw [smul_eq_mul, mul_comm])

end Cycle

end TauCeti.Contour

end

end
