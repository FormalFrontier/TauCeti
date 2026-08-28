/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology

/-!
# Stabilizers for the Krull topology are open

`Mathlib/FieldTheory/KrullTopology.lean` supplies the Krull topology on `Gal(L/K)` together with
`IntermediateField.fixingSubgroup_isOpen`, the fact that the fixing subgroup of a finite
intermediate field is open. This file draws the pointwise consequence: an element `x` of `L` that
is integral over `K` has an **open** stabilizer, since its stabilizer contains the fixing subgroup
of the finite intermediate field `K⟮x⟯`; and the same holds for a unit of `L`, an automorphism
fixing a unit being exactly one that fixes the underlying element.

Through Mathlib's `continuousSMul_iff_stabilizer_isOpen` this is what makes an algebraic extension
and its units *discrete modules* over the Galois group, in the sense continuous cohomology asks
for; `TauCeti.unitsCoeff_continuousSMul` is that consequence for a separable closure.

## Main results

* `TauCeti.isOpen_stabilizer_of_isIntegral`, `TauCeti.isOpen_stabilizer`: the stabilizer of an
  element of `L` is an open subgroup of `Gal(L/K)`.
* `TauCeti.isOpen_stabilizer_units`: the same for a unit of `L`.
-/

public section

namespace TauCeti

open IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The stabilizer in `Gal(L/K)` of an element integral over `K` is open: it contains the fixing
subgroup of `K⟮x⟯`, which is finite over `K` and so is a basic open subgroup of the Krull
topology. -/
theorem isOpen_stabilizer_of_isIntegral {x : L} (hx : IsIntegral K x) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
  refine Subgroup.isOpen_mono (H₁ := K⟮x⟯.fixingSubgroup) (fun σ hσ ↦ ?_)
    K⟮x⟯.fixingSubgroup_isOpen
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x (mem_adjoin_simple_self K x)

/-- Over an algebraic extension every point stabilizer is open. -/
theorem isOpen_stabilizer [Algebra.IsAlgebraic K L] (x : L) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) :=
  isOpen_stabilizer_of_isIntegral (Algebra.IsIntegral.isIntegral x)

/-- The stabilizer of a unit of an algebraic extension is open: an automorphism fixes a unit
exactly when it fixes the underlying element. -/
theorem isOpen_stabilizer_units [Algebra.IsAlgebraic K L] (u : Lˣ) :
    IsOpen (MulAction.stabilizer Gal(L/K) u : Set Gal(L/K)) := by
  convert isOpen_stabilizer (K := K) (u : L) using 2
  ext σ
  simp [MulAction.mem_stabilizer_iff, Units.ext_iff]

end TauCeti
