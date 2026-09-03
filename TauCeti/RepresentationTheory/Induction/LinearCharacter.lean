/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.FiniteDimensional
public import TauCeti.RepresentationTheory.LinearCharacter

/-!
# The dimension of a representation induced from a linear character

Induction from a subgroup of finite index multiplies the dimension by the index
(`TauCeti.finrank_indFDRep`), and the representation carrying a linear character is a line
(`FDRep.finrank_ofLinearCharacter`). Putting the two together, what a linear character of `N`
induces to has dimension exactly `N.index`, whatever the group and whatever the character: this
is the dimension count every worked example of induction from a linear character opens with.

Nothing here is about irreducibility, so nothing here depends on the Mackey theory that those
examples go on to use.

## Main statements

* `TauCeti.finrank_indFDRep_ofLinearCharacter`: what a linear character induces to has the
  dimension of the index of the subgroup.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.FiniteIndex]

/-- **What a linear character induces to has the dimension of the index of the subgroup.**
Induction multiplies the dimension by the index, and the representation carrying a linear
character is a line. -/
theorem finrank_indFDRep_ofLinearCharacter (χ : N →* kˣ) :
    Module.finrank k (indFDRep (FDRep.ofLinearCharacter χ)) = N.index := by
  rw [finrank_indFDRep, FDRep.finrank_ofLinearCharacter, mul_one]

end TauCeti
