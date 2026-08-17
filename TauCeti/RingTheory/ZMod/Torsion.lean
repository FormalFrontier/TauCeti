/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ZMod.Torsion

/-!
# Roots of unity of order dividing `p - 1` in a prime field

The unit group of `ZMod p` is cyclic of order `p - 1`, which `Mathlib.RingTheory.ZMod.Torsion`
records as the instance `HasEnoughRootsOfUnity (ZMod p) (p - 1)`. Transporting it along a divisor
`d ∣ p - 1` puts a primitive `d`-th root of unity into `ZMod p`, and with it the splitting of
`X ^ d - 1`.

## Main results

* `TauCeti.ZMod.hasEnoughRootsOfUnity_of_dvd_sub_one`: `ZMod p` has enough roots of unity of every
  order dividing `p - 1`.
* `TauCeti.ZMod.exists_isPrimitiveRoot_of_dvd_sub_one`: hence a primitive `d`-th root of unity for
  every such `d`.
-/

public section

namespace TauCeti

namespace ZMod

/-- **`ZMod p` has enough roots of unity of every order dividing `p - 1`.** This is the divisor
transport of Mathlib's instance `HasEnoughRootsOfUnity (ZMod p) (p - 1)`, which says that the unit
group of a prime field is cyclic. -/
theorem hasEnoughRootsOfUnity_of_dvd_sub_one {p d : ℕ} (hp : p.Prime) (hd : d ∣ p - 1) :
    HasEnoughRootsOfUnity (ZMod p) d := by
  have := Fact.mk hp
  have : NeZero (p - 1) := ⟨by have := hp.two_le; omega⟩
  exact HasEnoughRootsOfUnity.of_dvd (ZMod p) hd

/-- **`ZMod p` contains a primitive `d`-th root of unity for every `d` dividing `p - 1`.** -/
theorem exists_isPrimitiveRoot_of_dvd_sub_one {p d : ℕ} (hp : p.Prime) (hd : d ∣ p - 1) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ d :=
  have := hasEnoughRootsOfUnity_of_dvd_sub_one hp hd
  HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod p) d

end ZMod

end TauCeti
