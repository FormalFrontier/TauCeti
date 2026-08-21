/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Deck actions and monodromy transport

Deck transformations commute with transport between fibres by covering-space monodromy.

## Main declaration

* `TauCeti.Deck.monodromy_smul`: deck transformations commute with monodromy along a path.

## References

The proof specializes `TauCeti.IsCoveringMap.fiberMap_monodromy` to the continuous map underlying
a deck transformation. It supplies the fibre-transport step needed for the regular-cover criterion
in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8.
-/

public section

namespace TauCeti

namespace Deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  {x y : X}

/-- Transport by covering-space monodromy commutes with the action of a deck transformation.

Both sides transport a point of the fibre over `x` to the fibre over `y`: one first applies the
deck transformation and then lifts the path, while the other first lifts the path and then
applies the deck transformation. -/
@[simp]
theorem monodromy_smul (hp : IsCoveringMap p)
    (γ : Path.Homotopic.Quotient x y) (φ : Deck p) (e : p ⁻¹' {x}) :
    hp.monodromy γ (φ • e) = φ • hp.monodromy γ e := by
  let g : C(E, E) := ⟨φ.1, φ.1.continuous⟩
  have hgp : p ∘ g = p := funext (map_proj φ)
  have hfiber (z : X) (u : p ⁻¹' {z}) : IsCoveringMap.fiberMap g hgp z u = φ • u := by
    apply Subtype.ext
    simp only [IsCoveringMap.fiberMap_apply_coe, fiber_smul_coe]
    rfl
  simpa only [hfiber] using (IsCoveringMap.fiberMap_monodromy hp hp g hgp γ e).symm

end Deck

end TauCeti
