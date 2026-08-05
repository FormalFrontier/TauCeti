/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular

/-!
# Orbits of the modular group on the upper half-plane

Every `SL(2, ℤ)`-orbit of `ℍ` has a representative in the standard fundamental domain,
and translation by one preserves orbits. These are the orbit-space inputs of the
valence formula.

## Main declarations

* `TauCeti.ModularGroup.exists_rep_mem_fd`: every orbit meets `𝒟`.
* `TauCeti.ModularGroup.orbit_mk_int_vadd`: integer translation preserves the orbit.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups Modular

namespace TauCeti

namespace ModularGroup

/-- Every `SL(2, ℤ)`-orbit of `ℍ` has a representative in the standard fundamental
domain. -/
lemma exists_rep_mem_fd (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :
    ∃ p : ℍ, Quotient.mk'' p = q ∧ p ∈ 𝒟 := by
  induction q using Quotient.inductionOn' with
  | h z =>
    obtain ⟨g, hg⟩ := _root_.ModularGroup.exists_smul_mem_fd z
    exact ⟨g • z, Quotient.sound' ⟨g, rfl⟩, hg⟩

/-- Translation by any integer preserves the `SL(2, ℤ)`-orbit. -/
@[simp]
lemma orbit_mk_int_vadd (n : ℤ) (z : ℍ) :
    (Quotient.mk'' ((n : ℝ) +ᵥ z) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) =
      Quotient.mk'' z :=
  Quotient.sound' ⟨_root_.ModularGroup.T ^ n, UpperHalfPlane.modular_T_zpow_smul z n⟩


end ModularGroup

end TauCeti

end
