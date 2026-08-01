/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Basic

/-!
# Deck actions and monodromy transport

Deck transformations commute with transport between fibres by covering-space monodromy.

## Main declaration

* `TauCeti.Deck.monodromy_smul`: deck transformations commute with monodromy along a path.

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

/-- Transport by covering-space monodromy commutes with the action of a deck transformation.

Both sides transport a point of the fibre over `x` to the fibre over `y`: one first applies the
deck transformation and then lifts the path, while the other first lifts the path and then
applies the deck transformation. -/
@[simp]
theorem monodromy_smul (hp : IsCoveringMap p)
    (γ : Path.Homotopic.Quotient x y) (φ : Deck p) (e : p ⁻¹' {x}) :
    hp.monodromy γ (φ • e) = φ • hp.monodromy γ e := by
  let Γ := hp.liftPathQuotient γ e
  let g : C(E, E) := ⟨φ.1, φ.1.continuous⟩
  let p' : C(E, X) := ⟨p, hp.continuous⟩
  have hgp : p'.comp g = p' := by
    ext z
    exact map_proj φ z
  apply hp.monodromy_eq_of_map_eq (Γ.map g)
  change (Γ.map g).map p' = _
  rw [← Path.Homotopic.Quotient.map_comp]
  convert hp.map_liftPathQuotient γ e using 2
  grind

end Deck

end TauCeti
