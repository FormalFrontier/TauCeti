/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Data.EReal.Operations
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic

/-!
# Attainment and lower semicontinuity of the infimal `c`-transform

The upper-semicontinuity half of the topological theory of the infimal `c`-transform lives in
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic`: an infimum of upper-semicontinuous
sections is upper semicontinuous, with no compactness anywhere. This file proves the other
half, the compact regime.

The engine is a value-function fact: if `g : X × Y → EReal` is jointly lower semicontinuous,
then `y ↦ ⨅ x, g x y` is lower semicontinuous whenever `X` is compact
(`TauCeti.lowerSemicontinuous_ciInf_of_isCompact`). The proof needs neither metrizability nor
separation: a margin above the target level persists on a product neighborhood around each
point of the compact factor, and finitely many of these neighborhoods cover the factor. If
moreover every section is lower semicontinuous, the infimum is attained
(`TauCeti.exists_ciInf_eq_of_isCompact`).

Applied to the transform integrand `(x, y) ↦ (c (x, y) : EReal) - φ x`, this gives the compact
regime for Kantorovich potentials: against a jointly lower-semicontinuous cost and an
upper-semicontinuous potential, the infimal `c`-transform is lower semicontinuous
(`TauCeti.lowerSemicontinuous_cTransform_of_lowerSemicontinuous`) and its defining infimum is
attained over a compact nonempty source (`TauCeti.exists_cTransform_eq_of_lowerSemicontinuous`);
with both halves the transform is continuous
(`TauCeti.continuous_cTransform_of_continuous_of_lowerSemicontinuous`), and either
semicontinuity regime yields Borel measurability (`TauCeti.measurable_cTransform_*`). Every
statement has a symmetric counterpart for `TauCeti.cTransformSymm`.

## Main statements

* `TauCeti.lowerSemicontinuous_ciInf_of_isCompact`,
  `TauCeti.exists_ciInf_eq_of_isCompact` — the two value-function facts;
* `TauCeti.lowerSemicontinuous_cTransform_of_lowerSemicontinuous`,
  `TauCeti.exists_cTransform_eq_of_lowerSemicontinuous`,
  `TauCeti.continuous_cTransform_of_continuous_of_lowerSemicontinuous`;
* `TauCeti.measurable_cTransform_of_lowerSemicontinuous`,
  `TauCeti.measurable_cTransform_of_continuous`.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 2: the regularity and
  stability facts on `c`-transforms in this compact/lower-semicontinuous regime.

This is Layer 2, item 2 of the optimal-transport roadmap.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c : X × Y → ℝ} {φ : X → EReal} {ψ : Y → EReal}

/-- A function into `EReal` that is both lower and upper semicontinuous is continuous: at each
point its value is squeezed between the liminf and the limsup along the neighborhood filter,
and those two extremes coincide. -/
private theorem continuous_of_lowerSemicontinuous_upperSemicontinuous {α : Type*}
    [TopologicalSpace α] {f : α → EReal} (hl : LowerSemicontinuous f)
    (hu : UpperSemicontinuous f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_of_le_liminf_of_limsup_le (lowerSemicontinuous_iff_le_liminf.1 hl x)
      (upperSemicontinuous_iff_limsup_le.1 hu x)

/-! ### The value-function facts -/

variable [TopologicalSpace X] [TopologicalSpace Y] {g : X × Y → EReal}

/-- The infimum of a jointly lower-semicontinuous function over a compact factor is lower
semicontinuous in the remaining variable. No separation or countability hypothesis is needed:
a margin above the target level persists on a product neighborhood around each point of the
compact factor, and finitely many of these neighborhoods cover the factor. -/
theorem lowerSemicontinuous_ciInf_of_isCompact [CompactSpace X] (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun y => ⨅ x, g (x, y) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro b
  have key : ∀ y₀ : Y, ((fun y => ⨅ x, g (x, y)) y₀ ∈ Ioi b) →
      ∃ w ∈ 𝓝 y₀, w ⊆ ((fun y => ⨅ x, g (x, y)) ⁻¹' Ioi b) := by
    rintro y₀ (hy₀ : b < ⨅ x, g (x, y₀))
    obtain ⟨m, hbm, hm⟩ := exists_between hy₀
    -- every section at the base point stays above the margin
    have hsec : ∀ x : X, m < g (x, y₀) := fun x ↦ lt_of_lt_of_le hm (iInf_le _ x)
    -- around each source point the margin persists on a product of open neighborhoods
    have hpoint : ∀ x : X, ∃ u : Set X, ∃ v : Set Y, u ∈ 𝓝 x ∧ v ∈ 𝓝 y₀ ∧
        u ×ˢ v ⊆ g ⁻¹' Ioi m ∧ IsOpen u ∧ IsOpen v := by
      intro x
      have hmem : g ⁻¹' Ioi m ∈ 𝓝 ((x, y₀)) :=
        (hg.isOpen_preimage m).mem_nhds (Set.mem_preimage.2 (Set.mem_Ioi.2 (hsec x)))
      obtain ⟨u, v, hu_open, hxu, hv_open, hyv, huv⟩ := mem_nhds_prod_iff'.1 hmem
      exact ⟨u, v, hu_open.mem_nhds hxu, hv_open.mem_nhds hyv, huv, hu_open, hv_open⟩
    choose U V hU hV hUV hUopen hVopen using hpoint
    obtain ⟨T, -, hTcover⟩ :=
      isCompact_univ.elim_nhds_subcover U (fun x (_ : x ∈ univ) ↦ hU x)
    set W : Set Y := ⋂ x ∈ T, V x with hWdef
    have hWopen : IsOpen W := isOpen_biInter_finset fun x (_ : x ∈ T) ↦ hVopen x
    have hsub : W ⊆ ((fun y => ⨅ x, g (x, y)) ⁻¹' Ioi b) := by
      intro y hy
      have hyV : ∀ x ∈ T, y ∈ V x := fun x hx ↦ Set.mem_iInter₂.1 hy x hx
      refine Set.mem_preimage.2 (lt_of_lt_of_le hbm (le_iInf fun x ↦ le_of_lt ?_))
      obtain ⟨p, hpT, hxU⟩ := Set.mem_iUnion₂.1 (hTcover (Set.mem_univ x))
      exact Set.mem_preimage.1 (hUV p ⟨hxU, hyV p hpT⟩)
    exact ⟨W, hWopen.mem_nhds (Set.mem_iInter₂.2 fun x (_ : x ∈ T) ↦ mem_of_mem_nhds (hV x)),
      hsub⟩
  exact isOpen_iff_mem_nhds.2 fun y₀ hy₀ ↦ let ⟨w, hw, hsub⟩ := key y₀ hy₀
    mem_of_superset hw hsub

omit [TopologicalSpace Y] in
/-- The infimum over a nonempty compact index factor of a family of lower-semicontinuous
functions indexed by a second variable is attained by one of the sections. -/
theorem exists_ciInf_eq_of_isCompact [CompactSpace X] (hne : Nonempty X)
    (hgsec : ∀ y, LowerSemicontinuous fun x => g (x, y)) (y : Y) :
    ∃ x : X, ⨅ x' : X, g (x', y) = g (x, y) := by
  have hsec' : LowerSemicontinuousOn (fun x => g (x, y)) Set.univ :=
    (hgsec y).lowerSemicontinuousOn Set.univ
  obtain ⟨a, -, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn Set.univ_nonempty isCompact_univ hsec'
  refine ⟨a, le_antisymm (iInf_le_of_le a (le_refl _)) (le_iInf fun x' ↦ ?_)⟩
  exact isMinOn_iff.1 hmin x' (mem_univ x')

/-! ### Application to the transform -/

/-- Against a jointly lower-semicontinuous real cost, subtracting an upper-semicontinuous
potential on the source keeps the integrand of the `c`-transform jointly lower
semicontinuous. The potential may take the values `±∞`; subtraction by them makes the
integrand constant. -/
theorem lowerSemicontinuous_coe_sub_of_upperSemicontinuous
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal) - φ z.1 := by
  refine hc.add' ?_ ?_
  · refine continuous_neg.comp_upperSemicontinuous_antitone
      (Semicontinuous.comp (r := fun (a : X) (b : EReal) => φ a < b) hφ continuous_fst)
      EReal.neg_strictAnti.antitone
  · intro z
    exact EReal.continuousAt_add (Or.inl (by simp)) (Or.inl (by simp))

/-- If the cost is jointly lower semicontinuous and the potential is upper semicontinuous,
the infimum defining the `c`-transform is attained at some source point, provided the source
space is compact and nonempty. -/
theorem exists_cTransform_eq_of_lowerSemicontinuous [CompactSpace X] (hne : Nonempty X)
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) (y : Y) :
    ∃ x : X, cTransform c φ y = ((c (x, y) : ℝ) : EReal) - φ x := by
  have hgsec : ∀ y', LowerSemicontinuous fun x' => ((c (x', y') : ℝ) : EReal) - φ x' :=
    fun y' ↦
      Semicontinuous.comp (lowerSemicontinuous_coe_sub_of_upperSemicontinuous hc hφ)
        (Continuous.prodMk_left y')
  obtain ⟨x, hx⟩ :=
    exists_ciInf_eq_of_isCompact (g := fun z => ((c z : ℝ) : EReal) - φ z.1) hne hgsec y
  refine ⟨x, ?_⟩
  rw [cTransform_apply]
  exact hx

/-- If the cost is jointly lower semicontinuous and the potential is upper semicontinuous,
the infimal `c`-transform against a compact source space is lower semicontinuous. Together
with the upper semicontinuity of `CTransform.Basic` this yields continuity under continuous
cost sections. -/
theorem lowerSemicontinuous_cTransform_of_lowerSemicontinuous [CompactSpace X]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    LowerSemicontinuous (cTransform c φ) := by
  have hEq : cTransform c φ = fun y => ⨅ x, ((c (x, y) : ℝ) : EReal) - φ x :=
    funext (cTransform_apply c φ)
  rw [hEq]
  exact lowerSemicontinuous_ciInf_of_isCompact
    (lowerSemicontinuous_coe_sub_of_upperSemicontinuous hc hφ)

/-- The compact/lower-semicontinuous regime in which the infimal `c`-transform is continuous:
the cost sections are continuous and the cost is jointly lower semicontinuous, so the upper
semicontinuity of `CTransform.Basic` combines with
`lowerSemicontinuous_cTransform_of_lowerSemicontinuous`. -/
theorem continuous_cTransform_of_continuous_of_lowerSemicontinuous [CompactSpace X]
    (hcsec : ∀ x, Continuous fun y => c (x, y))
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    Continuous (cTransform c φ) :=
  continuous_of_lowerSemicontinuous_upperSemicontinuous
    (lowerSemicontinuous_cTransform_of_lowerSemicontinuous hc hφ)
    (upperSemicontinuous_cTransform_of_continuous hcsec φ)

/-- In the compact/lower-semicontinuous regime the `c`-transform is Borel measurable. -/
theorem measurable_cTransform_of_lowerSemicontinuous [CompactSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    Measurable (cTransform c φ) :=
  (lowerSemicontinuous_cTransform_of_lowerSemicontinuous hc hφ).measurable

omit [TopologicalSpace X] in
/-- With continuous cost sections the `c`-transform is Borel measurable, on an arbitrary
source space and with no compactness. -/
theorem measurable_cTransform_of_continuous
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hcsec : ∀ x, Continuous fun y => c (x, y)) (φ : X → EReal) :
    Measurable (cTransform c φ) :=
  (upperSemicontinuous_cTransform_of_continuous hcsec φ).measurable

/-! ### The symmetric transform -/

/-- If the cost is jointly lower semicontinuous and the potential is upper semicontinuous,
the infimum defining the symmetric `c`-transform is attained at some target point, provided
the target space is compact and nonempty. -/
theorem exists_cTransformSymm_eq_of_lowerSemicontinuous [CompactSpace Y] (hne : Nonempty Y)
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) (x : X) :
    ∃ y : Y, cTransformSymm c ψ x = ((c (x, y) : ℝ) : EReal) - ψ y := by
  have hc' : LowerSemicontinuous fun z : Y × X => ((c (z.2, z.1) : ℝ) : EReal) :=
    Semicontinuous.comp hc continuous_swap
  obtain ⟨y, hy⟩ :=
    exists_cTransform_eq_of_lowerSemicontinuous (c := fun z : Y × X => c (z.2, z.1)) hne hc' hψ x
  refine ⟨y, ?_⟩
  rw [cTransform_apply (fun z : Y × X => c (z.2, z.1)) ψ x] at hy
  rw [cTransformSymm_apply, hy]

/-- If the cost is jointly lower semicontinuous and the potential is upper semicontinuous,
the symmetric `c`-transform against a compact target space is lower semicontinuous. -/
theorem lowerSemicontinuous_cTransformSymm_of_lowerSemicontinuous [CompactSpace Y]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) :
    LowerSemicontinuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact lowerSemicontinuous_cTransform_of_lowerSemicontinuous
    (c := fun z : Y × X => c (z.2, z.1)) (Semicontinuous.comp hc continuous_swap) hψ

/-- The compact/lower-semicontinuous regime in which the symmetric `c`-transform is
continuous. -/
theorem continuous_cTransformSymm_of_continuous_of_lowerSemicontinuous [CompactSpace Y]
    (hcsec : ∀ y, Continuous fun x => c (x, y))
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) :
    Continuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact continuous_cTransform_of_continuous_of_lowerSemicontinuous
    (c := fun z : Y × X => c (z.2, z.1))
    hcsec (Semicontinuous.comp hc continuous_swap) hψ

/-- In the compact/lower-semicontinuous regime the symmetric `c`-transform is Borel
measurable. -/
theorem measurable_cTransformSymm_of_lowerSemicontinuous [CompactSpace Y]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) :
    Measurable (cTransformSymm c ψ) :=
  (lowerSemicontinuous_cTransformSymm_of_lowerSemicontinuous hc hψ).measurable

omit [TopologicalSpace Y] in
/-- With continuous cost sections the symmetric `c`-transform is Borel measurable. -/
theorem measurable_cTransformSymm_of_continuous
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (hcsec : ∀ y, Continuous fun x => c (x, y)) (ψ : Y → EReal) :
    Measurable (cTransformSymm c ψ) :=
  (upperSemicontinuous_cTransformSymm_of_continuous hcsec ψ).measurable

end TauCeti
