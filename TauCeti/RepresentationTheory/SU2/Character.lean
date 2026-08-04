/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Continuous.Character
public import TauCeti.RepresentationTheory.SU2.Weyl

/-!
# Characters of `SU(2)` are even on the maximal torus

The Weyl group of `SU(2)` computed in `TauCeti/RepresentationTheory/SU2/Weyl.lean` inverts the
maximal torus: the quarter turn `w = !![0, -1; 1, 0]` conjugates `diag (z, z⁻¹)` to
`diag (z⁻¹, z)`. Characters are conjugation invariant, so the character of a continuous
finite-dimensional representation of `SU(2)` takes the same value at a torus element and at its
inverse. In the angle parametrisation `θ ↦ diag (e^{iθ}, e^{-iθ})` this reads
`χ (torusExp (-θ)) = χ (torusExp θ)`: the character is an even function of `θ`.

This is the `W`-invariance, on the maximal torus, of the characters of `SU(2)`, and it is what
makes those characters functions of `cos θ`. It is stated here for characters only; the roadmap's
identification of the `W`-invariant functions on `T` with *all* class functions of `SU(2)` needs
the conjugation of an arbitrary element of `SU(2)` into `T`, which is not proved here.

## Main results

* `TauCeti.SU2.character_torusHom_inv`: the character of a continuous finite-dimensional
  representation of `SU(2)` agrees at `diag (z, z⁻¹)` and `diag (z⁻¹, z)`.
* `TauCeti.SU2.character_torusExp_neg`: read in the angle parametrisation of the maximal torus,
  that character is an even function of the angle.

## References

This serves the engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`, "Engine case: `SU(2)` and the maximal
torus", which needs the characters of `SU(2)` to be even functions on the maximal torus.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 18.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV.
-/

public section

namespace TauCeti

namespace SU2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (π : ContRepresentation ℂ SU2 V) (hπ : Continuous π)

/-- **The character of a continuous representation of `SU(2)` is even on the maximal torus:** its
values at `diag (z, z⁻¹)` and at `diag (z⁻¹, z)` agree, the two being conjugate by the quarter
turn. -/
theorem character_torusHom_inv (z : Circle) :
    ContRepresentation.character π hπ (torusHom z⁻¹)
      = ContRepresentation.character π hπ (torusHom z) := by
  rw [← weylElement_conj_torusHom z]
  exact ContRepresentation.character_conj π hπ _ _

/-- The character of a continuous representation of `SU(2)`, read in the angle parametrisation
`θ ↦ diag (e^{iθ}, e^{-iθ})` of the maximal torus, is an even function of `θ`. This is the sense in
which the characters of `SU(2)` are `W`-invariant functions on the torus. -/
theorem character_torusExp_neg (θ : ℝ) :
    ContRepresentation.character π hπ (torusExp (-θ))
      = ContRepresentation.character π hπ (torusExp θ) := by
  obtain ⟨z, hz⟩ := mem_torus_iff_exists_torusHom.mp (torusExp_mem_torus θ)
  rw [torusExp_neg, ← hz, ← map_inv]
  exact character_torusHom_inv π hπ z

end SU2

end TauCeti
