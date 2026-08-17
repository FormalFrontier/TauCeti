/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Radical
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# The radical of a module is the radical of its submodule lattice

`Module.jacobson R M` is defined as the infimum of the maximal submodules of `M`, and
`Order.radical` of a lattice is defined as the infimum of its coatoms. For the lattice
`Submodule R M` these are the same infimum, but Mathlib defines the two independently and states no
lemma connecting them. This file supplies that bridge, which makes the general `Order.radical` API
— notably `Order.radical_nongenerating` — available for `Module.jacobson`.

## Main results

* `TauCeti.Module.jacobson_eq_radical`: `Module.jacobson R M = Order.radical (Submodule R M)`.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/-- The Jacobson radical of a module is the order radical of its submodule lattice: both are the
infimum of the coatoms. Mathlib defines the two independently and states no lemma connecting
them. -/
theorem Module.jacobson_eq_radical :
    Module.jacobson R M = Order.radical (Submodule R M) := by
  simp only [Module.jacobson, Order.radical]
  exact sInf_eq_iInf

end TauCeti
