/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic

/-!
# Cycles of piecewise-`C¹` curves

A contour cycle is a finite formal `ℤ`-linear combination of closed piecewise-`C¹` curves. This
file packages that definition as the free abelian group on parametrized closed curves and extends
the contour integral and winding number additively from curves to cycles.

Individual curves remain raw functions on real intervals, as elsewhere in the contour library. The
small `PiecewiseC1ClosedCurve` bundle exists only because `FreeAbelianGroup` needs a type of
generators; it records exactly a function, its oriented parameter interval, its regularity, and its
closedness. In particular, it does not introduce a second notion of contour integral.

The geometric trace of a cycle is the union of the images of the generators with nonzero
coefficient. Thus cancellation removes a curve from the trace, just as it removes that curve's
contribution to every additive invariant.

## Main definitions

* `TauCeti.Contour.PiecewiseC1ClosedCurve` — a closed piecewise-`C¹` parametrized curve.
* `TauCeti.Contour.Cycle` — the free abelian group on such curves.
* `TauCeti.Contour.Cycle.trace` — the geometric trace of a cycle.
* `TauCeti.Contour.Cycle.integral` — the additive extension of the contour integral.
* `TauCeti.Contour.Cycle.windingNumber` — the additive extension of the winding number.
* `TauCeti.Contour.Cycle.IsIn` and `TauCeti.Contour.Cycle.IsNullHomologous` — the cycle-level
  domain and null-homology predicates.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, Definition 2.1 and Theorem 3.3.
* L. Ahlfors, *Complex Analysis*, Chapter 4.
-/

public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace TauCeti.Contour

/-- A parametrized closed piecewise-`C¹` curve on an oriented real interval. The function is kept
on `ℝ`, rather than restricted to the interval, so all existing raw-function contour results apply
directly. -/
@[ext]
structure PiecewiseC1ClosedCurve where
  /-- The parametrization of the curve. -/
  toFun : ℝ → ℂ
  /-- The initial parameter. -/
  a : ℝ
  /-- The terminal parameter. -/
  b : ℝ
  /-- Piecewise-`C¹` regularity on the parameter interval. -/
  isPiecewiseC1On : IsPiecewiseC1On toFun a b
  /-- The parametrization has equal endpoints. -/
  source_eq_target : toFun a = toFun b

namespace PiecewiseC1ClosedCurve

instance : CoeFun PiecewiseC1ClosedCurve fun _ ↦ ℝ → ℂ :=
  ⟨PiecewiseC1ClosedCurve.toFun⟩

/-- The underlying parametrization is continuous on its parameter interval. -/
theorem continuousOn (γ : PiecewiseC1ClosedCurve) : ContinuousOn γ (uIcc γ.a γ.b) :=
  γ.isPiecewiseC1On.continuousOn

/-- The derivative of a closed piecewise-`C¹` curve is interval-integrable. -/
theorem intervalIntegrable_deriv (γ : PiecewiseC1ClosedCurve) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume γ.a γ.b :=
  γ.isPiecewiseC1On.intervalIntegrable_deriv

end PiecewiseC1ClosedCurve

/-- A contour cycle is a finite formal `ℤ`-linear combination of closed piecewise-`C¹` curves. -/
abbrev Cycle := FreeAbelianGroup PiecewiseC1ClosedCurve

namespace Cycle

/-- The geometric trace of a cycle: the union of the images of the curves occurring with nonzero
coefficient. -/
def trace (C : Cycle) : Set ℂ :=
  ⋃ γ ∈ FreeAbelianGroup.support C, γ '' uIcc γ.a γ.b

/-- Membership in the trace means membership in the image of a generator with nonzero
coefficient. -/
theorem mem_trace_iff {C : Cycle} {z : ℂ} :
    z ∈ trace C ↔ ∃ γ ∈ FreeAbelianGroup.support C, z ∈ γ '' uIcc γ.a γ.b := by
  simp only [trace, mem_iUnion, exists_prop]

/-- The zero cycle has empty trace. -/
@[simp]
theorem trace_zero : trace (0 : Cycle) = ∅ := by
  simp [trace]

/-- The trace of a single generator is its image on its parameter interval. -/
@[simp]
theorem trace_of (γ : PiecewiseC1ClosedCurve) :
    trace (FreeAbelianGroup.of γ) = γ '' uIcc γ.a γ.b := by
  simp [trace]

/-- Negating every coefficient does not change the trace. -/
@[simp]
theorem trace_neg (C : Cycle) : trace (-C) = trace C := by
  simp [trace]

/-- The trace of a sum is contained in the union of the traces. Equality can fail when a generator
occurs with opposite coefficients and cancels. -/
theorem trace_add_subset (C D : Cycle) : trace (C + D) ⊆ trace C ∪ trace D := by
  classical
  intro z hz
  rw [mem_trace_iff] at hz
  obtain ⟨γ, hγ, hz⟩ := hz
  rcases Finset.mem_union.mp (FreeAbelianGroup.support_add C D hγ) with hγC | hγD
  · exact Set.mem_union_left _ (mem_trace_iff.mpr ⟨γ, hγC, hz⟩)
  · exact Set.mem_union_right _ (mem_trace_iff.mpr ⟨γ, hγD, hz⟩)

/-- A nonzero integer multiple has the same trace as the original cycle. -/
theorem trace_zsmul (C : Cycle) {n : ℤ} (hn : n ≠ 0) : trace (n • C) = trace C := by
  simp [trace, hn]

/-- A cycle lies in `Ω` when its geometric trace is contained in `Ω`. -/
def IsIn (C : Cycle) (Ω : Set ℂ) : Prop :=
  trace C ⊆ Ω

/-- Restatement of cycle containment in terms of its trace. -/
theorem isIn_iff {C : Cycle} {Ω : Set ℂ} : IsIn C Ω ↔ trace C ⊆ Ω :=
  Iff.rfl

/-- A one-generator cycle lies in `Ω` exactly when its parametrization maps its interval into
`Ω`. -/
@[simp]
theorem isIn_of_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAbelianGroup.of γ) Ω ↔ MapsTo γ (uIcc γ.a γ.b) Ω := by
  rw [isIn_iff, trace_of]
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h z ⟨x, hx, rfl⟩
    exact h hx

/-- The zero cycle lies in every set. -/
@[simp]
theorem IsIn.zero (Ω : Set ℂ) : IsIn (0 : Cycle) Ω := by
  simp [isIn_iff]

/-- A sum of two cycles in `Ω` is in `Ω`. -/
theorem IsIn.add {C D : Cycle} {Ω : Set ℂ} (hC : IsIn C Ω) (hD : IsIn D Ω) :
    IsIn (C + D) Ω :=
  (trace_add_subset C D).trans (union_subset hC hD)

/-- Negation preserves containment in a set. -/
@[simp]
theorem isIn_neg_iff {C : Cycle} {Ω : Set ℂ} : IsIn (-C) Ω ↔ IsIn C Ω := by
  simp [isIn_iff]

/-- Every integer multiple of a cycle in `Ω` is in `Ω`. -/
theorem IsIn.zsmul {C : Cycle} {Ω : Set ℂ} (hC : IsIn C Ω) (n : ℤ) : IsIn (n • C) Ω := by
  by_cases hn : n = 0
  · subst n
    simpa only [zero_zsmul] using IsIn.zero Ω
  · rw [isIn_iff, trace_zsmul C hn]
    exact hC

/-- The integral of `f` over a cycle, obtained by additively extending the raw contour integral
`∫ t in γ.a..γ.b, deriv γ t • f (γ t)` from generators. -/
def integral (C : Cycle) (f : ℂ → ℂ) : ℂ :=
  FreeAbelianGroup.lift
    (fun γ : PiecewiseC1ClosedCurve ↦ ∫ t in γ.a..γ.b, deriv γ t • f (γ t)) C

/-- Integrating over a one-generator cycle gives the raw contour integral over that curve. -/
@[simp]
theorem integral_of (γ : PiecewiseC1ClosedCurve) (f : ℂ → ℂ) :
    integral (FreeAbelianGroup.of γ) f =
      ∫ t in γ.a..γ.b, deriv γ t • f (γ t) := by
  rw [integral, FreeAbelianGroup.lift_apply_of]

/-- The integral over the zero cycle vanishes. -/
@[simp]
theorem integral_zero (f : ℂ → ℂ) : integral 0 f = 0 :=
  by rw [integral, map_zero]

/-- The integral is additive in the cycle. -/
@[simp]
theorem integral_add (C D : Cycle) (f : ℂ → ℂ) :
    integral (C + D) f = integral C f + integral D f := by
  simp only [integral, map_add]

/-- Reversing every coefficient negates the integral. -/
@[simp]
theorem integral_neg (C : Cycle) (f : ℂ → ℂ) : integral (-C) f = -integral C f := by
  simp only [integral, map_neg]

/-- The integral respects subtraction of cycles. -/
@[simp]
theorem integral_sub (C D : Cycle) (f : ℂ → ℂ) :
    integral (C - D) f = integral C f - integral D f := by
  simp only [sub_eq_add_neg, integral_add, integral_neg]

/-- The integral respects integer multiplicities. -/
@[simp]
theorem integral_zsmul (n : ℤ) (C : Cycle) (f : ℂ → ℂ) :
    integral (n • C) f = n • integral C f := by
  simp only [integral, map_zsmul]

/-- The winding number of a cycle, obtained by additively extending the generalized winding number
of its generators. -/
def windingNumber (C : Cycle) (z₀ : ℂ) : ℂ :=
  FreeAbelianGroup.lift
    (fun γ : PiecewiseC1ClosedCurve ↦ TauCeti.Contour.windingNumber γ γ.a γ.b z₀) C

/-- The winding number of a one-generator cycle is the winding number of that curve. -/
@[simp]
theorem windingNumber_of (γ : PiecewiseC1ClosedCurve) (z₀ : ℂ) :
    windingNumber (FreeAbelianGroup.of γ) z₀ =
      TauCeti.Contour.windingNumber γ γ.a γ.b z₀ := by
  rw [windingNumber, FreeAbelianGroup.lift_apply_of]

/-- The zero cycle has winding number zero. -/
@[simp]
theorem windingNumber_zero (z₀ : ℂ) : windingNumber 0 z₀ = 0 :=
  by rw [windingNumber, map_zero]

/-- The winding number is additive in the cycle. -/
@[simp]
theorem windingNumber_add (C D : Cycle) (z₀ : ℂ) :
    windingNumber (C + D) z₀ = windingNumber C z₀ + windingNumber D z₀ := by
  simp only [windingNumber, map_add]

/-- Negating every coefficient negates the winding number. -/
@[simp]
theorem windingNumber_neg (C : Cycle) (z₀ : ℂ) :
    windingNumber (-C) z₀ = -windingNumber C z₀ := by
  simp only [windingNumber, map_neg]

/-- The winding number respects subtraction of cycles. -/
@[simp]
theorem windingNumber_sub (C D : Cycle) (z₀ : ℂ) :
    windingNumber (C - D) z₀ = windingNumber C z₀ - windingNumber D z₀ := by
  simp only [sub_eq_add_neg, windingNumber_add, windingNumber_neg]

/-- The winding number respects integer multiplicities. -/
@[simp]
theorem windingNumber_zsmul (n : ℤ) (C : Cycle) (z₀ : ℂ) :
    windingNumber (n • C) z₀ = n • windingNumber C z₀ := by
  simp only [windingNumber, map_zsmul]

/-- A cycle is null-homologous in `Ω` when its winding number vanishes at every point outside
`Ω`. -/
def IsNullHomologous (C : Cycle) (Ω : Set ℂ) : Prop :=
  ∀ z ∉ Ω, windingNumber C z = 0

/-- Restatement of null-homology as vanishing of the cycle winding number outside the domain. -/
theorem isNullHomologous_iff {C : Cycle} {Ω : Set ℂ} :
    IsNullHomologous C Ω ↔ ∀ z ∉ Ω, windingNumber C z = 0 :=
  Iff.rfl

/-- Cycle null-homology specializes on a generator to the raw-curve predicate. -/
@[simp]
theorem isNullHomologous_of_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsNullHomologous (FreeAbelianGroup.of γ) Ω ↔
      TauCeti.Contour.IsNullHomologous γ γ.a γ.b Ω := by
  simp only [isNullHomologous_iff, windingNumber_of,
    TauCeti.Contour.isNullHomologous_iff]

/-- The zero cycle is null-homologous in every set. -/
@[simp]
theorem IsNullHomologous.zero (Ω : Set ℂ) : IsNullHomologous (0 : Cycle) Ω := by
  intro z hz
  simp

/-- A sum of null-homologous cycles is null-homologous. -/
theorem IsNullHomologous.add {C D : Cycle} {Ω : Set ℂ} (hC : IsNullHomologous C Ω)
    (hD : IsNullHomologous D Ω) : IsNullHomologous (C + D) Ω := by
  intro z hz
  rw [windingNumber_add, hC z hz, hD z hz, add_zero]

/-- Negation preserves null-homology. -/
@[simp]
theorem isNullHomologous_neg_iff {C : Cycle} {Ω : Set ℂ} :
    IsNullHomologous (-C) Ω ↔ IsNullHomologous C Ω := by
  constructor <;> intro h z hz
  · simpa only [windingNumber_neg, neg_eq_zero] using h z hz
  · simpa only [windingNumber_neg, neg_eq_zero] using h z hz

/-- Every integer multiple of a null-homologous cycle is null-homologous. -/
theorem IsNullHomologous.zsmul {C : Cycle} {Ω : Set ℂ} (hC : IsNullHomologous C Ω) (n : ℤ) :
    IsNullHomologous (n • C) Ω := by
  intro z hz
  rw [windingNumber_zsmul, hC z hz, smul_zero]

end Cycle

end TauCeti.Contour

end
