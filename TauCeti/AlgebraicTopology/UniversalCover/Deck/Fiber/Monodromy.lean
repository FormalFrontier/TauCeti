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
  have hmapComp : Γ.map (p'.comp g) ≍ Γ.map p' :=
    congr_arg_heq (fun q : C(E, X) ↦ Γ.map q) hgp
  have hmapMap : (Γ.map g).map p' = Γ.map (p'.comp g) :=
    Path.Homotopic.Quotient.map_comp.symm
  have hmap : (Γ.map g).map p' ≍ Γ.map p' :=
    (heq_of_eq hmapMap).trans hmapComp
  let Γ' : Path.Homotopic.Quotient ((φ • e : p ⁻¹' {x}) : E)
      ((φ • hp.monodromy γ e : p ⁻¹' {y}) : E) :=
    (Γ.map g).cast (fiber_smul_coe φ e) (fiber_smul_coe φ (hp.monodromy γ e))
  apply hp.monodromy_eq_of_map_eq Γ'
  dsimp only [Γ']
  rw [Path.Homotopic.Quotient.map_cast]
  apply eq_of_heq
  have hcastSource :
      ((Γ.map g).map p').cast
          (congrArg p' (fiber_smul_coe φ e))
          (congrArg p' (fiber_smul_coe φ (hp.monodromy γ e))) ≍
        (Γ.map g).map p' :=
    Path.Homotopic.Quotient.cast_heq _ _
  have hlift : Γ.map p' ≍ γ.cast e.2 (hp.monodromy γ e).2 :=
    heq_of_eq (hp.map_liftPathQuotient γ e)
  have hcastLift : γ.cast e.2 (hp.monodromy γ e).2 ≍ γ :=
    Path.Homotopic.Quotient.cast_heq _ _
  have hcastTarget : γ ≍ γ.cast (φ • e).2 (φ • hp.monodromy γ e).2 :=
    (Path.Homotopic.Quotient.cast_heq _ _).symm
  exact hcastSource.trans (hmap.trans (hlift.trans (hcastLift.trans hcastTarget)))

end Deck

end TauCeti
