/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Rings fixed by a power map

This file records an elementary consequence of every element of a domain extension of a finite
field being fixed by the cardinality power map: the extension is the base field itself.

This is a general finite-ring prerequisite for the good-prime structure theorem in the roadmap
`RepresentationTheory/CharacterTheory`, Layer 6.

## Main results

* `TauCeti.algebraMap_bijective_of_pow_card_eq_self`: an extension fixed by the base-field
  cardinality power map is the base field itself.
-/

public section

namespace TauCeti

/-- **A field extension in which `x ^ |K| = x` is `K` itself.** Every element of the extension is
then in the range of the algebra map by the finite-field Frobenius fixed-point criterion. -/
theorem algebraMap_bijective_of_pow_card_eq_self {K L : Type*} [Field K] [Fintype K] [CommRing L]
    [IsDomain L] [Algebra K L] (h : ∀ x : L, x ^ Fintype.card K = x) :
    Function.Bijective (algebraMap K L) :=
  ⟨(algebraMap K L).injective,
    fun x => (FiniteField.pow_card_eq_self_iff_mem_range_algebraMap x).mp (h x)⟩

end TauCeti
