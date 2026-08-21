/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Degree
public import TauCeti.FieldTheory.SquareClassGroup

/-!
# Square-class independence as `ZMod 2`-linear independence

The multiquadratic degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range` takes the
**square-class independence** hypothesis in the elaboration-friendly *Finset form*: no nonempty
subset product `∏_{i ∈ S} d i` of the radicands is a square in `K`. The Galois-theoretic
arguments instead want the structural form: the classes of the `d i` in the square-class group
`Kˣ ⧸ (Kˣ)²` are `ZMod 2`-linearly independent.

The square-class group, the class of a unit, and the equivalence between linear independence of
the classes and the Finset form live in `TauCeti.FieldTheory.SquareClassGroup`
(`TauCeti.linearIndependent_squareClass_iff`), field-generically and depending only on Mathlib.
This file consumes that equivalence to restate the degree theorem against the structural form.

## Main results

* `TauCeti.Multiquadratic.finrank_adjoin_range_of_linearIndependent`: the degree theorem
  `[K(rootᵢ : i) : K] = 2^|ι|` restated against linear independence of the unit classes.
-/

public section

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

/-- A unit is a square iff its underlying field element is. -/
private theorem isSquare_units_val_iff {u : Kˣ} : IsSquare (u : K) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := fun h => u.ne_zero (by rw [hx, h, mul_zero])
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(v : K), by simp⟩

/-- **The multiquadratic degree theorem, restated via linear independence.** If the square classes
of the radicands `d : ι → Kˣ` are `ZMod 2`-linearly independent, then the field generated over `K`
by their square roots `root i` has degree `2^|ι|`. This is `finrank_adjoin_range` consuming the
structural form of square-class independence. -/
theorem finrank_adjoin_range_of_linearIndependent {ι : Type*} [Finite ι] {d : ι → Kˣ}
    {root : ι → L} (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) [NeZero (2 : K)]
    (hli : LinearIndependent (ZMod 2) (fun i => squareClass (d i))) :
    Module.finrank K (IntermediateField.adjoin K (Set.range root)) = 2 ^ Nat.card ι := by
  let := Fintype.ofFinite ι
  refine finrank_adjoin_range (d := fun i => (d i : K)) hroot (fun S hS => ?_)
  have hne := (linearIndependent_squareClass_iff d).mp hli S hS
  rw [← Units.coe_prod, isSquare_units_val_iff]
  exact hne

end TauCeti.Multiquadratic
