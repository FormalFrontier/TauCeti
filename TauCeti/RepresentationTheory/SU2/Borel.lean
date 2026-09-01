/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.RepresentationTheory.SU2.Basic

/-!
# The Borel structure of `SU(2)`

`SU(2)` carries the subspace topology of the `2 × 2` complex matrices, which makes it a compact
Hausdorff topological group (`TauCeti/RepresentationTheory/SU2/Basic.lean`), but no measurable
structure comes with it. This file equips it with its Borel σ-algebra, which is what lets the Haar
measure of a compact group -- and with it the `L²` theory of
`TauCeti/RepresentationTheory/Compact/` -- be applied to `SU(2)`.

The σ-algebra is taken to be `borel SU(2)` by definition, so the `MeasurableSpace` and
`BorelSpace` instances agree by construction and no compatibility lemma is needed.
-/

public section

namespace TauCeti

namespace SU2

/-- `SU(2)` carries its Borel σ-algebra, the measurable structure Haar measure needs. -/
noncomputable instance : MeasurableSpace SU2 := borel SU2

instance : BorelSpace SU2 := ⟨rfl⟩

end SU2

end TauCeti
