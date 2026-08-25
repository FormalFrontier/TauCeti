/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Compactness and semicontinuity for a pointwise infimum

Two value-function facts about the pointwise infimum of a jointly lower-semicontinuous function
over a compact factor. The proof needs neither metrizability nor separation: a margin above the
target level persists on a product neighborhood around each point of the compact factor, and
finitely many of these neighborhoods cover the factor.

* `TauCeti.lowerSemicontinuous_ciInf_of_isCompact`: if `g : X × Y → EReal` is jointly lower
  semicontinuous and `X` is compact, then `y ↦ ⨅ x, g (x, y)` is lower semicontinuous;
* `TauCeti.exists_ciInf_eq_of_isCompact`: if moreover every section is lower semicontinuous,
  the infimum over a nonempty compact factor is attained by one of the sections.

These are the engine behind the compact regularity theory of the infimal `c`-transform in
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Topology`, but they are stated for arbitrary
topological spaces and an arbitrary jointly lower-semicontinuous integrand.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {g : X × Y → EReal}

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

end TauCeti
