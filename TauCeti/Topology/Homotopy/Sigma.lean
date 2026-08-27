/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Sigma
public import Mathlib.Topology.Homotopy.Path

/-!
# Paths in a disjoint union

A path in a disjoint union `Σ i, X i` never leaves the summand it starts in, because the unit
interval is connected: this is Mathlib's `ContinuousMap.exists_lift_sigma`. This file draws the
two consequences that the fundamental groupoid of a disjoint union needs, namely that the
endpoint of a path out of the `i`-th summand again lies in the `i`-th summand, and that a path
between two points of the `i`-th summand is the image of a path in that summand — the latter also
for path homotopy classes.

The inclusion of a summand is spelled out as the anonymous bundled map
`⟨Sigma.mk i, continuous_sigmaMk⟩` rather than `ContinuousMap.sigmaMk i`, because only the former
has an application that reduces definitionally, which the dependently typed rewrites downstream
need.

## Main declarations

* `TauCeti.sigmaFst_eq_of_path`: a path out of the `i`-th summand of a disjoint union ends in
  the `i`-th summand.
* `TauCeti.exists_path_map_sigmaMk_eq`: **a path between two points of the `i`-th summand is the
  image of a path in that summand.**
* `TauCeti.exists_quotient_map_sigmaMk_eq`: the same for path homotopy classes.

## References

This supplies the fundamental-groupoid half of the disconnected case of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

namespace TauCeti

open Topology unitInterval

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- A path out of the `i`-th summand of a disjoint union ends in the `i`-th summand. -/
theorem sigmaFst_eq_of_path {i : ι} {x : X i} {z : Σ j, X j}
    (γ : Path (⟨i, x⟩ : Σ j, X j) z) : z.1 = i := by
  obtain ⟨j, g, hg⟩ := ContinuousMap.exists_lift_sigma γ.toContinuousMap
  have hγ : ∀ t, γ t = ⟨j, g t⟩ := fun t => DFunLike.congr_fun hg t
  rw [γ.target.symm.trans (hγ 1)]
  exact congrArg Sigma.fst ((hγ 0).symm.trans γ.source)

/-- **A path between two points of the `i`-th summand of a disjoint union is the image of a path
in that summand.** -/
theorem exists_path_map_sigmaMk_eq {i : ι} {x y : X i}
    (γ : Path (⟨i, x⟩ : Σ j, X j) ⟨i, y⟩) :
    ∃ γ' : Path x y, γ'.map continuous_sigmaMk = γ := by
  obtain ⟨j, g, hg⟩ := ContinuousMap.exists_lift_sigma γ.toContinuousMap
  have hγ : ∀ t, γ t = ⟨j, g t⟩ := fun t => DFunLike.congr_fun hg t
  obtain rfl : j = i := congrArg Sigma.fst ((hγ 0).symm.trans γ.source)
  exact ⟨⟨g, sigma_mk_injective ((hγ 0).symm.trans γ.source),
    sigma_mk_injective ((hγ 1).symm.trans γ.target)⟩, Path.ext (funext fun t => (hγ t).symm)⟩

/-- **A path homotopy class between two points of the `i`-th summand of a disjoint union is the
image of a class in that summand.** -/
theorem exists_quotient_map_sigmaMk_eq {i : ι} {x y : X i}
    (γ : Path.Homotopic.Quotient (⟨i, x⟩ : Σ j, X j) ⟨i, y⟩) :
    ∃ γ' : Path.Homotopic.Quotient x y,
      γ'.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) = γ := by
  obtain ⟨γ⟩ := γ
  obtain ⟨γ', hγ'⟩ := exists_path_map_sigmaMk_eq γ
  exact ⟨Path.Homotopic.Quotient.mk γ', by rw [← Path.Homotopic.Quotient.mk_map, hγ']; rfl⟩

/-- A path homotopy class out of the `i`-th summand of a disjoint union ends in the `i`-th
summand. -/
theorem sigmaFst_eq_of_quotient {i : ι} {x : X i} {z : Σ j, X j}
    (γ : Path.Homotopic.Quotient (⟨i, x⟩ : Σ j, X j) z) : z.1 = i := by
  obtain ⟨γ⟩ := γ
  exact sigmaFst_eq_of_path γ

end TauCeti
