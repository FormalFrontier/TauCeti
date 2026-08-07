/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Jordan curves traced by paths

A path whose two endpoints agree is a parametrised closed curve, but its range need not be a
Jordan curve: the path may pause, retrace an arc, or cross itself. This file supplies the exact
criterion needed to exclude those degeneracies. If a closed path has no repeated values except
for its two endpoint parameters, its range is a Jordan curve
(`TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints`).

The proof uses the quotient model of the circle already in Mathlib. The extension of a path
`γ : Path x x` to `ℝ` has equal values at `0` and `1`, so
`AddCircle.liftIco 1 0 γ.extend` factors it through the additive circle `ℝ / ℤ`. The hypothesis on
repetitions says precisely that this factor is injective. Its range is the range of `γ`; compactness
of the additive circle then upgrades the resulting continuous bijection onto the range to a
homeomorphism, and `AddCircle.homeomorphCircle` identifies its source with `Circle`.

The condition is stated directly rather than bundled as a new notion of simple closed path. This
is the only operation needed here, and keeping it as a theorem hypothesis avoids introducing a
second simplicity vocabulary alongside Mathlib's path API.

## Main result

* `TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints` — the range of a closed path whose only
  possible repetition is its pair of endpoints is a Jordan curve.

## Roadmap role

This is the topological gluing step used by layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence. A
finite-length image crosscut is already packaged as a path with exactly this simplicity property in
`TauCeti/Analysis/Complex/Conformal/Crosscut/Path.lean`; when its two boundary ends coincide, the
result below identifies the closure of that crosscut as a Jordan curve. The conformal specialization
is in `TauCeti/Analysis/Complex/Conformal/Crosscut/Jordan.lean`.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] {x : X}

/-- **The range of a simple closed path is a Jordan curve.** Let `γ : Path x x` be a closed path.
If equality `γ s = γ t` forces either `s = t` or the unordered pair of parameters to be `{0, 1}`,
then `range γ` is homeomorphic to the circle.

The disjunction records both orientations of the exceptional endpoint pair explicitly. No local
injectivity, embedding, or ambient separation hypothesis is needed. -/
theorem isJordanCurve_range_of_eq_or_eq_endpoints (γ : Path x x)
    (hγ : ∀ ⦃s t : unitInterval⦄, γ s = γ t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    IsJordanCurve (range γ) := by
  -- Factor the extended path through `[0, 1]` with its endpoints identified.
  let g : AddCircle (1 : ℝ) → X := AddCircle.liftIco 1 0 γ.extend
  have hg0 : γ.extend 0 = γ.extend 1 := by rw [γ.extend_zero, γ.extend_one]
  have hgc : Continuous g :=
    AddCircle.liftIco_zero_continuous hg0 γ.continuous_extend.continuousOn
  have hgcoe {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
      g (t : AddCircle (1 : ℝ)) = γ ⟨t, ht.1, ht.2.le⟩ := by
    rw [show g (t : AddCircle (1 : ℝ)) = γ.extend t from
      AddCircle.liftIco_zero_coe_apply ht]
    exact γ.extend_extends' ⟨t, ht.1, ht.2.le⟩
  -- Representatives in `[0, 1)` cannot form the exceptional endpoint pair, so the factor is
  -- injective on the quotient.
  have hgi : Function.Injective g := by
    intro q q' hqq'
    obtain ⟨s, hs, rfl⟩ := AddCircle.eq_coe_Ico q
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico q'
    rw [hgcoe hs, hgcoe ht] at hqq'
    rcases hγ hqq' with hst | hends | hends
    · exact congrArg (fun u : unitInterval => ((u : ℝ) : AddCircle (1 : ℝ))) hst
    · exact absurd (congrArg ((↑) : unitInterval → ℝ) hends.2) ht.2.ne
    · exact absurd (congrArg ((↑) : unitInterval → ℝ) hends.1) hs.2.ne
  -- The quotient factor traces exactly the original path range; the endpoint `1` is represented
  -- by `0` in the additive circle.
  have hgrange : range g = range γ := by
    apply Subset.antisymm
    · rintro y ⟨q, rfl⟩
      obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico q
      exact ⟨⟨t, ht.1, ht.2.le⟩, (hgcoe ht).symm⟩
    · rintro y ⟨t, rfl⟩
      by_cases ht : (t : ℝ) < 1
      · exact ⟨((t : ℝ) : AddCircle (1 : ℝ)), hgcoe ⟨t.2.1, ht⟩⟩
      · have ht1 : t = 1 := Subtype.ext (le_antisymm t.2.2 (not_lt.mp ht))
        refine ⟨(0 : AddCircle (1 : ℝ)), ?_⟩
        subst t
        exact (hgcoe (t := 0) (by simp)).trans (γ.source.trans γ.target.symm)
  -- Restrict the codomain to the range and use compact-to-Hausdorff to upgrade the continuous
  -- bijection to a homeomorphism.
  let g' : AddCircle (1 : ℝ) → range γ := fun q =>
    ⟨g q, hgrange.le (mem_range_self q)⟩
  have hgi' : Function.Injective g' := fun _ _ h => hgi (congrArg Subtype.val h)
  have hgs' : Function.Surjective g' := by
    rintro ⟨y, t, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, g q = γ t := hgrange.ge (mem_range_self t)
    exact ⟨q, Subtype.ext hq⟩
  let e : AddCircle (1 : ℝ) ≃ range γ := Equiv.ofBijective g' ⟨hgi', hgs'⟩
  have he : (e : AddCircle (1 : ℝ) → range γ) = g' := by
    unfold e
    exact Equiv.coe_ofBijective g' ⟨hgi', hgs'⟩
  have hec : Continuous e := by
    rw [he]
    exact hgc.subtype_mk fun q => hgrange.le (mem_range_self q)
  let h : AddCircle (1 : ℝ) ≃ₜ range γ := Continuous.homeoOfEquivCompactToT2 hec
  exact isJordanCurve_iff.mpr ⟨h.symm.trans (AddCircle.homeomorphCircle one_ne_zero)⟩

end TauCeti
