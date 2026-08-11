/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular

/-!
# Orbits of the modular group on the upper half-plane

Every `SL(2, ℤ)`-orbit of `ℍ` has a representative in the standard fundamental domain, and
translation by one preserves orbits. On the *open* domain the representative is moreover unique,
so the orbit map is injective there. These are the orbit-space inputs of the valence formula: the
first says a sum over orbits can be read off representatives, the last says doing so counts each
orbit once.

## Main declarations

* `TauCeti.ModularGroup.exists_rep_mem_fd`: every orbit meets `𝒟`.
* `TauCeti.ModularGroup.orbit_mk_int_vadd`: integer translation preserves the orbit.
* `TauCeti.ModularGroup.orbit_mk_injOn_fdo`: the orbit map is injective on `𝒟ᵒ`.
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


/-- Distinct points of the **open** fundamental domain lie in distinct `SL(2, ℤ)`-orbits: the
orbit map is injective there. This is the Second Fundamental Domain Lemma
(`ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`) restated as injectivity, which is the form the
orbit-indexed valence formula needs. It fails on the closed domain `𝒟`, whose boundary is
identified with itself by `T` and `S`. -/
lemma orbit_mk_injOn_fdo :
    Set.InjOn (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) 𝒟ᵒ := by
  intro p hp q hq hpq
  obtain ⟨g, hg⟩ := Quotient.exact' hpq
  have hg' : g • q = p := hg
  have hgq : g • q ∈ 𝒟ᵒ := by rw [hg']; exact hp
  exact hg'.symm.trans (_root_.ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hq hgq).symm

end ModularGroup

end TauCeti

end
