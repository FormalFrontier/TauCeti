/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Subcontinuum

/-!
# Monotone maps from a Jordan curve

A continuous map from a Jordan curve is called *monotone* when each of its point fibres is
connected. This file records the rigidity consequence needed by the Carathéodory boundary
correspondence: a monotone map whose fibres have empty interior is injective.

The argument is intrinsic to the curve. A point fibre is compact by continuity and compactness of
the Jordan curve, and it is preconnected by monotonicity. If it had two points, the classification
of subcontinua of a Jordan curve in `TauCeti/Topology/JordanCurve/Subcontinuum.lean` would force it
to contain a relative open arc. Equivalently, the nowhere-dense criterion
`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` makes every fibre a subsingleton.

The theorem is phrased for a map whose domain is the subtype `C`. Thus its fibres and their
interiors are taken in the topology of the curve itself, which is the natural form for boundary
maps and avoids an ambient-space side condition.

## Main result

* `TauCeti.IsJordanCurve.injective_of_isPreconnected_fiber_of_interior_fiber_eq_empty` — a
  continuous map from a Jordan curve with preconnected, interiorless point fibres is injective.
* `TauCeti.IsJordanCurve.injective_iff_isPreconnected_fiber_of_interior_fiber_eq_empty` — under
  the same interior condition, monotonicity is equivalent to injectivity.

## References

* G. T. Whyburn, *Analytic Topology*, Ch. VII.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T1Space Y] {C : Set X} {g : C → Y}

/-- **A monotone map from a Jordan curve with interiorless fibres is injective.** Let `C` be a
Jordan curve and `g : C → Y` a continuous map to a `T₁` space. If every point fibre of `g` is
preconnected and has empty interior in `C`, then `g` is injective.

Continuity makes each fibre closed, hence compact because `C` is compact. Empty interior says its
complement is dense. The fibre is therefore a nowhere-dense subcontinuum of the Jordan curve, so
`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` makes it a subsingleton. -/
theorem IsJordanCurve.injective_of_isPreconnected_fiber_of_interior_fiber_eq_empty
    (hC : IsJordanCurve C) (hg : Continuous g)
    (hpre : ∀ y, IsPreconnected {x | g x = y})
    (hinterior : ∀ y, interior {x | g x = y} = ∅) : Function.Injective g := by
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have hJ : IsJordanCurve (univ : Set C) := by
    obtain ⟨e⟩ := isJordanCurve_iff.mp hC
    exact isJordanCurve_iff.mpr ⟨(Homeomorph.Set.univ C).trans e⟩
  intro x y hxy
  let S : Set C := {z | g z = g x}
  have hScompact : IsCompact S := by
    exact (isClosed_singleton.preimage hg).isCompact
  have hSdense : S ⊆ closure ((univ : Set C) \ S) := by
    have hdense : Dense Sᶜ := interior_eq_empty_iff_dense_compl.mp (hinterior (g x))
    rw [← compl_eq_univ_sdiff, hdense.closure_eq]
    exact subset_univ S
  have hSsub : S.Subsingleton :=
    hJ.subsingleton_of_subset_closure_sdiff (subset_univ S) hScompact (hpre (g x)) hSdense
  exact hSsub (by simp [S]) (by simp [S, hxy])

/-- **For an interiorless-fibre map from a Jordan curve, monotonicity is equivalent to
injectivity.** The forward implication is
`TauCeti.IsJordanCurve.injective_of_isPreconnected_fiber_of_interior_fiber_eq_empty`. Conversely,
an injective map has empty or singleton point fibres, hence preconnected fibres; this direction
needs neither continuity nor the Jordan-curve hypothesis. -/
theorem IsJordanCurve.injective_iff_isPreconnected_fiber_of_interior_fiber_eq_empty
    (hC : IsJordanCurve C) (hg : Continuous g)
    (hinterior : ∀ y, interior {x | g x = y} = ∅) :
    Function.Injective g ↔ ∀ y, IsPreconnected {x | g x = y} := by
  constructor
  · intro hinj y
    have hsub : ({x | g x = y} : Set C).Subsingleton := by
      intro x hx z hz
      exact hinj (hx.trans hz.symm)
    exact hsub.isPreconnected
  · exact fun hpre ↦
      hC.injective_of_isPreconnected_fiber_of_interior_fiber_eq_empty hg hpre hinterior

end TauCeti
