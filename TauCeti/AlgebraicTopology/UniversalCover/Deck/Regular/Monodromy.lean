/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Monodromy
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Basic

/-!
# Regularity from one fibre

Deck transformations commute with transport between fibres by covering-space monodromy. Thus,
over a path-connected base, transitivity of the deck action on one nonempty fibre implies
transitivity on every fibre (and also supplies surjectivity of the covering map). This reduces
regularity to a condition at a single chosen fibre.

## Main declarations

* `TauCeti.Deck.isRegular_iff_fiber_isPretransitive`: over a path-connected base, a covering is
  regular exactly when its deck group acts transitively on one chosen fibre.

## References

The proof uses Junyan Xu's path-lifting and monodromy API in
`Mathlib.Topology.Homotopy.Lifting`. It supplies the fibre-transport step needed for the regular
cover criterion in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8.
-/

public section

namespace TauCeti

namespace Deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  {x y : X}

/-- Over a path-connected base, a covering map with a chosen point in one fibre is regular
exactly when the deck action on that one fibre is transitive.

Monodromy transports transitivity to every other fibre. The chosen point also transports to
every fibre, proving the surjectivity required by `Deck.IsRegular`. -/
theorem isRegular_iff_fiber_isPretransitive [PathConnectedSpace X]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    IsRegular p ↔ MulAction.IsPretransitive (Deck p) (p ⁻¹' {x}) := by
  constructor
  · intro hreg
    exact hreg.fiber_isPretransitive x
  · intro htrans
    letI := htrans
    refine ⟨?_, fun y ↦ MulAction.IsPretransitive.mk ?_⟩
    · intro y
      let γ : Path.Homotopic.Quotient x y :=
        Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)
      exact ⟨hp.monodromy γ e, Set.mem_singleton_iff.mp (hp.monodromy γ e).2⟩
    · intro u v
      let γ : Path.Homotopic.Quotient x y :=
        Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)
      obtain ⟨u₀, hu₀⟩ := (hp.monodromy_bijective γ).2 u
      obtain ⟨v₀, hv₀⟩ := (hp.monodromy_bijective γ).2 v
      obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) u₀ v₀
      refine ⟨φ, ?_⟩
      rw [← hu₀, ← hv₀, ← monodromy_smul hp γ φ u₀, hφ]

end Deck

end TauCeti
