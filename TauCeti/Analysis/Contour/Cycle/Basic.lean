/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

Individual curves remain functions on real intervals, as elsewhere in the contour library. The
small `PiecewiseC1ClosedCurve` bundle exists only because `FreeAbelianGroup` needs a type of
generators; it records exactly an interval-restricted function, its oriented parameter interval,
its regularity, and its closedness. Its canonical extension to `ℝ` lets existing raw-function
contour results apply directly. In particular, it does not introduce a second notion of contour
integral.

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

/-- A parametrized closed piecewise-`C¹` curve on an oriented real interval. The parametrization
is stored only on its interval, so curves cannot differ merely in irrelevant values outside it. -/
@[ext]
structure PiecewiseC1ClosedCurve where
  /-- The initial parameter. -/
  a : ℝ
  /-- The terminal parameter. -/
  b : ℝ
  /-- The interval-restricted parametrization of the curve. -/
  toFun : uIcc a b → ℂ
  /-- Piecewise-`C¹` regularity on the parameter interval. -/
  isPiecewiseC1On : IsPiecewiseC1On (Function.extend Subtype.val toFun 0) a b
  /-- The parametrization has equal endpoints. -/
  source_eq_target :
    Function.extend Subtype.val toFun 0 a = Function.extend Subtype.val toFun 0 b

namespace PiecewiseC1ClosedCurve

/-- A closed curve coerces to the canonical extension of its parametrization to `ℝ`. -/
instance : CoeFun PiecewiseC1ClosedCurve fun _ ↦ ℝ → ℂ :=
  ⟨fun γ ↦ Function.extend Subtype.val γ.toFun 0⟩

/-- On its parameter interval, a closed curve's coercion agrees with its stored function. -/
theorem coe_apply (γ : PiecewiseC1ClosedCurve) (t : uIcc γ.a γ.b) : γ t = γ.toFun t :=
  Subtype.val_injective.extend_apply γ.toFun 0 t

/-- Bundle a raw closed piecewise-`C¹` curve by restricting it to its parameter interval. -/
def of {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) :
    PiecewiseC1ClosedCurve where
  a := a
  b := b
  toFun t := γ t
  isPiecewiseC1On := by
    rw [isPiecewiseC1On_iff] at hγ ⊢
    refine ⟨hγ.1.congr (fun t ht ↦ ?_), ?_⟩
    · exact Subtype.val_injective.extend_apply (fun t : uIcc a b ↦ γ t) 0 ⟨t, ht⟩
    · obtain ⟨p, hp, hpieces⟩ := hγ.2
      refine ⟨p, hp, fun c d hcd hdis ↦ (hpieces c d hcd hdis).congr fun t ht ↦ ?_⟩
      exact Subtype.val_injective.extend_apply (fun t : uIcc a b ↦ γ t) 0 ⟨t, hcd ht⟩
  source_eq_target := by
    calc
      Function.extend Subtype.val (fun t : uIcc a b ↦ γ t) 0 a =
          γ (⟨a, left_mem_uIcc⟩ : uIcc a b) :=
        Subtype.val_injective.extend_apply (fun t : uIcc a b ↦ γ t) 0
          ⟨a, left_mem_uIcc⟩
      _ = γ (⟨b, right_mem_uIcc⟩ : uIcc a b) := hclosed
      _ = Function.extend Subtype.val (fun t : uIcc a b ↦ γ t) 0 b :=
        (Subtype.val_injective.extend_apply (fun t : uIcc a b ↦ γ t) 0
          ⟨b, right_mem_uIcc⟩).symm

/-- Bundling a raw curve preserves its initial parameter. -/
@[simp]
theorem of_a {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) :
    (of γ hγ hclosed).a = a := (rfl)

/-- Bundling a raw curve preserves its terminal parameter. -/
@[simp]
theorem of_b {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) :
    (of γ hγ hclosed).b = b := (rfl)

/-- Bundling a raw curve preserves its values on the parameter interval. -/
@[simp]
theorem of_apply {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) {t : ℝ} (ht : t ∈ uIcc a b) :
    of γ hγ hclosed t = γ t := by
  exact coe_apply (of γ hγ hclosed) ⟨t, ht⟩

/-- Bundling a raw curve preserves its interval image. -/
@[simp]
theorem image_of {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) :
    of γ hγ hclosed '' uIcc a b = γ '' uIcc a b := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (of_apply γ hγ hclosed ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, of_apply γ hγ hclosed ht⟩

/-- Bundling a raw curve preserves the set into which it maps its parameter interval. -/
@[simp]
theorem mapsTo_of_iff {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (Ω : Set ℂ) :
    MapsTo (of γ hγ hclosed) (uIcc a b) Ω ↔ MapsTo γ (uIcc a b) Ω := by
  rw [Set.mapsTo_iff_image_subset, Set.mapsTo_iff_image_subset, image_of]

/-- Bundling a raw curve preserves its contour integral. -/
@[simp]
theorem integral_of {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) :
    (∫ t in a..b, deriv (of γ hγ hclosed) t • f (of γ hγ hclosed t)) =
      ∫ t in a..b, deriv γ t • f (γ t) := by
  have heq : EqOn (of γ hγ hclosed) γ (uIoo a b) :=
    fun _ ht ↦ of_apply γ hγ hclosed (uIoo_subset_uIcc_self ht)
  exact intervalIntegral.integral_congr_uIoo fun t ht ↦ by
    rw [heq ht, heq.deriv isOpen_Ioo ht]

/-- Bundling a raw curve preserves its winding number. -/
@[simp]
theorem windingNumber_of {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (z₀ : ℂ) :
    TauCeti.Contour.windingNumber (of γ hγ hclosed) a b z₀ =
      TauCeti.Contour.windingNumber γ a b z₀ := by
  apply TauCeti.Contour.windingNumber_congr_curve
  intro t ht
  exact of_apply γ hγ hclosed (uIoo_subset_uIcc_self ht)

/-- Bundling a raw curve preserves null-homology. -/
@[simp]
theorem isNullHomologous_of_iff {a b : ℝ} (γ : ℝ → ℂ)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) (Ω : Set ℂ) :
    TauCeti.Contour.IsNullHomologous (of γ hγ hclosed) a b Ω ↔
      TauCeti.Contour.IsNullHomologous γ a b Ω := by
  simp only [TauCeti.Contour.isNullHomologous_iff, windingNumber_of]

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
@[simp]
theorem mem_trace_iff {C : Cycle} {z : ℂ} :
    z ∈ trace C ↔ ∃ γ ∈ FreeAbelianGroup.support C, z ∈ γ '' uIcc γ.a γ.b := by
  simp only [trace, mem_iUnion, exists_prop]

/-- A point outside the trace of a cycle is avoided by every curve in its canonical support. -/
theorem avoids_of_mem_support {C : Cycle} {z : ℂ} (hz : z ∉ trace C)
    {γ : PiecewiseC1ClosedCurve} (hγ : γ ∈ FreeAbelianGroup.support C) :
    ∀ t ∈ uIcc γ.a γ.b, γ t ≠ z := by
  intro t ht htz
  exact hz (mem_trace_iff.mpr ⟨γ, hγ, t, ht, htz⟩)

/-- The trace of a contour cycle is compact. -/
theorem isCompact_trace (C : Cycle) : IsCompact (trace C) := by
  rw [trace]
  exact (FreeAbelianGroup.support C).isCompact_biUnion fun γ _ ↦
    isCompact_uIcc.image_of_continuousOn γ.continuousOn

/-- The zero cycle has empty trace. -/
@[simp]
theorem trace_zero : trace (0 : Cycle) = ∅ := by
  simp [trace]

/-- The trace of a single generator is its image on its parameter interval. -/
@[simp]
theorem trace_of (γ : PiecewiseC1ClosedCurve) :
    trace (FreeAbelianGroup.of γ) = γ '' uIcc γ.a γ.b := by
  simp [trace]

/-- The trace of a raw curve bundled as a one-generator cycle is its raw interval image. -/
theorem trace_of_raw {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) :
    trace (FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of γ hγ hclosed)) =
      γ '' uIcc a b := by
  rw [trace_of]
  exact PiecewiseC1ClosedCurve.image_of γ hγ hclosed

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

/-- A raw curve bundled as a one-generator cycle lies in `Ω` exactly when it maps its interval
into `Ω`. -/
theorem isIn_of_raw_iff {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (Ω : Set ℂ) :
    IsIn (FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of γ hγ hclosed)) Ω ↔
      MapsTo γ (uIcc a b) Ω := by
  rw [isIn_iff, trace_of, ← Set.mapsTo_iff_image_subset]
  exact PiecewiseC1ClosedCurve.mapsTo_of_iff γ hγ hclosed Ω

/-- A one-generator cycle lies in `Ω` exactly when its parametrization maps its interval into
`Ω`. -/
@[simp]
theorem isIn_of_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAbelianGroup.of γ) Ω ↔ MapsTo γ (uIcc γ.a γ.b) Ω := by
  simpa [isIn_iff] using
    (Set.mapsTo_iff_image_subset (f := γ) (s := uIcc γ.a γ.b) (t := Ω)).symm

/-- The zero cycle lies in every set. -/
@[simp]
theorem IsIn.zero (Ω : Set ℂ) : IsIn (0 : Cycle) Ω := by
  simp [isIn_iff]

/-- A sum of two cycles in `Ω` is in `Ω`. -/
theorem IsIn.add {C D : Cycle} {Ω : Set ℂ} (hC : IsIn C Ω) (hD : IsIn D Ω) :
    IsIn (C + D) Ω := by
  rw [isIn_iff] at hC hD ⊢
  exact (trace_add_subset C D).trans (union_subset hC hD)

/-- Negation preserves containment in a set. -/
@[simp]
theorem isIn_neg_iff {C : Cycle} {Ω : Set ℂ} : IsIn (-C) Ω ↔ IsIn C Ω := by
  simp [isIn_iff]

/-- Every integer multiple of a cycle in `Ω` is in `Ω`. -/
theorem IsIn.zsmul {C : Cycle} {Ω : Set ℂ} (hC : IsIn C Ω) (n : ℤ) : IsIn (n • C) Ω := by
  rw [isIn_iff] at hC
  by_cases hn : n = 0
  · subst n
    simpa only [zero_zsmul] using IsIn.zero Ω
  · rw [isIn_iff, trace_zsmul C hn]
    exact hC

/-- The integral of `f` over a cycle, obtained by additively extending the raw contour integral
`∫ t in γ.a..γ.b, deriv γ t • f (γ t)` from generators. -/
def integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) : Cycle →+ E :=
  FreeAbelianGroup.lift
    fun γ : PiecewiseC1ClosedCurve ↦ ∫ t in γ.a..γ.b, deriv γ t • f (γ t)

/-- Integrating over a raw curve bundled as a one-generator cycle gives its raw contour integral. -/
theorem integral_of_raw {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) :
    integral f (FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of γ hγ hclosed)) =
      ∫ t in a..b, deriv γ t • f (γ t) := by
  rw [integral, FreeAbelianGroup.lift_apply_of]
  exact PiecewiseC1ClosedCurve.integral_of γ hγ hclosed f

/-- Integrating over a one-generator cycle gives the raw contour integral over that curve. -/
@[simp]
theorem integral_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : PiecewiseC1ClosedCurve) (f : ℂ → E) :
    integral f (FreeAbelianGroup.of γ) =
      ∫ t in γ.a..γ.b, deriv γ t • f (γ t) := by
  rw [integral, FreeAbelianGroup.lift_apply_of]

/-- The integral over a cycle is the coefficient-weighted sum of the integrals over the curves in
its canonical support. -/
theorem integral_eq_sum_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (C : Cycle) :
    integral f C = ∑ γ ∈ FreeAbelianGroup.support C,
      FreeAbelianGroup.coeff γ C • (∫ t in γ.a..γ.b, deriv γ t • f (γ t)) := by
  conv_lhs => rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of C]
  simp only [map_sum, map_zsmul, integral_of]

/-- The winding number of a cycle, obtained by additively extending the generalized winding number
of its generators. -/
def windingNumber (z₀ : ℂ) : Cycle →+ ℂ :=
  FreeAbelianGroup.lift
    fun γ : PiecewiseC1ClosedCurve ↦ TauCeti.Contour.windingNumber γ γ.a γ.b z₀

/-- The winding number of a raw curve bundled as a one-generator cycle is its raw winding number. -/
theorem windingNumber_of_raw {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (z₀ : ℂ) :
    windingNumber z₀ (FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of γ hγ hclosed)) =
      TauCeti.Contour.windingNumber γ a b z₀ := by
  rw [windingNumber, FreeAbelianGroup.lift_apply_of]
  exact PiecewiseC1ClosedCurve.windingNumber_of γ hγ hclosed z₀

/-- The winding number of a one-generator cycle is the winding number of that curve. -/
@[simp]
theorem windingNumber_of (γ : PiecewiseC1ClosedCurve) (z₀ : ℂ) :
    windingNumber z₀ (FreeAbelianGroup.of γ) =
      TauCeti.Contour.windingNumber γ γ.a γ.b z₀ := by
  rw [windingNumber, FreeAbelianGroup.lift_apply_of]

/-- A cycle is null-homologous in `Ω` when its winding number vanishes at every point outside
`Ω`. -/
def IsNullHomologous (C : Cycle) (Ω : Set ℂ) : Prop :=
  ∀ z ∉ Ω, windingNumber z C = 0

/-- Restatement of null-homology as vanishing of the cycle winding number outside the domain. -/
theorem isNullHomologous_iff {C : Cycle} {Ω : Set ℂ} :
    IsNullHomologous C Ω ↔ ∀ z ∉ Ω, windingNumber z C = 0 :=
  Iff.rfl

/-- Null-homology of a raw curve bundled as a one-generator cycle is the raw-curve predicate. -/
theorem isNullHomologous_of_raw_iff {a b : ℝ} (γ : ℝ → ℂ)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) (Ω : Set ℂ) :
    IsNullHomologous (FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of γ hγ hclosed)) Ω ↔
      TauCeti.Contour.IsNullHomologous γ a b Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_raw,
    TauCeti.Contour.isNullHomologous_iff]

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
  rw [isNullHomologous_iff]
  intro z hz
  simp

/-- A sum of null-homologous cycles is null-homologous. -/
theorem IsNullHomologous.add {C D : Cycle} {Ω : Set ℂ} (hC : IsNullHomologous C Ω)
    (hD : IsNullHomologous D Ω) : IsNullHomologous (C + D) Ω := by
  rw [isNullHomologous_iff] at hC hD ⊢
  intro z hz
  rw [map_add, hC z hz, hD z hz, add_zero]

/-- Negation preserves null-homology. -/
@[simp]
theorem isNullHomologous_neg_iff {C : Cycle} {Ω : Set ℂ} :
    IsNullHomologous (-C) Ω ↔ IsNullHomologous C Ω := by
  rw [isNullHomologous_iff, isNullHomologous_iff]
  constructor <;> intro h z hz
  · simpa only [map_neg, neg_eq_zero] using h z hz
  · simpa only [map_neg, neg_eq_zero] using h z hz

/-- Every integer multiple of a null-homologous cycle is null-homologous. -/
theorem IsNullHomologous.zsmul {C : Cycle} {Ω : Set ℂ} (hC : IsNullHomologous C Ω) (n : ℤ) :
    IsNullHomologous (n • C) Ω := by
  rw [isNullHomologous_iff] at hC ⊢
  intro z hz
  rw [map_zsmul, hC z hz, smul_zero]

end Cycle

end TauCeti.Contour

end
