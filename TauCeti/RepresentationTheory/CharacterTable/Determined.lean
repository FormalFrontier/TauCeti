/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
import Mathlib.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# Finite-group representations are determined by their characters

For a finite group over an algebraically closed field of characteristic zero, two
finite-dimensional representations with the same character are equivalent. Maschke's theorem
makes their group-algebra modules semisimple, while the character pairing identifies the
dimension of every intertwiner space. The reconstruction theorem in
`TauCeti/RingTheory/Semisimple/Multiplicity.lean` then shows that the modules are equivalent.

## Main results

* `Representation.nonempty_equiv_of_character_eq`: equal characters determine
  equivalent finite-dimensional representations.
* `FDRep.nonempty_iso_of_character_eq`: the bundled `FDRep` form.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part I, §§2.3 and 2.5.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §§25 and 30.

This is the object-level input to the injectivity target in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u v w

private def linearMapCongrLeft {k A S T N : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
    [AddCommMonoid S] [Module A S] [AddCommMonoid T] [Module A T]
    [AddCommMonoid N] [Module k N] [Module A N] [IsScalarTower k A N]
    (e : S ≃ₗ[A] T) : (S →ₗ[A] N) ≃ₗ[k] (T →ₗ[A] N) where
  toFun f :=
    { toFun := fun x ↦ f (e.symm x)
      map_add' := by simp
      map_smul' := by simp }
  invFun f :=
    { toFun := fun x ↦ f (e x)
      map_add' := by simp
      map_smul' := by simp }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv f := by ext; simp
  right_inv f := by ext; simp

namespace Representation

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
variable {V W : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **For a finite group over an algebraically closed field of characteristic zero,
finite-dimensional representations are determined by their characters.** -/
theorem _root_.Representation.nonempty_equiv_of_character_eq (ρ : Representation k G V)
    (σ : Representation k G W) (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ : Module.Finite k[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  let _ : Module.Finite k[G] σ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  have hhom (S : Submodule k[G] k[G]) [IsSimpleModule k[G] S] :
      Module.finrank k (S →ₗ[k[G]] ρ.asModule) =
        Module.finrank k (S →ₗ[k[G]] σ.asModule) := by
    let Z := _root_.Representation.ofModule' (k := k) (G := G) S
    have hofCharacter : ClassFunction.ofCharacter ρ = ClassFunction.ofCharacter σ :=
      Subtype.ext <| funext fun g ↦ by simp only [ClassFunction.ofCharacter_apply, hchar]
    have heq : ClassFunction.characterPairing (ClassFunction.ofCharacter ρ)
          (ClassFunction.ofCharacter Z) =
        ClassFunction.characterPairing (ClassFunction.ofCharacter σ)
          (ClassFunction.ofCharacter Z) := by
      rw [hofCharacter]
    have hinter : Module.finrank k (_root_.Representation.IntertwiningMap Z ρ) =
        Module.finrank k (_root_.Representation.IntertwiningMap Z σ) := by
      apply Nat.cast_injective (R := k)
      simpa only [ClassFunction.characterPairing_ofCharacter_eq_finrank] using heq
    calc
      Module.finrank k (S →ₗ[k[G]] ρ.asModule) =
          Module.finrank k (Z.asModule →ₗ[k[G]] ρ.asModule) :=
        (linearMapCongrLeft (k := k) (Representation.ofModule'AsModuleEquiv S)).finrank_eq.symm
      _ = Module.finrank k (_root_.Representation.IntertwiningMap Z ρ) :=
        (_root_.Representation.IntertwiningMap.equivLinearMapAsModule Z ρ).finrank_eq.symm
      _ = Module.finrank k (_root_.Representation.IntertwiningMap Z σ) := hinter
      _ = Module.finrank k (Z.asModule →ₗ[k[G]] σ.asModule) :=
        (_root_.Representation.IntertwiningMap.equivLinearMapAsModule Z σ).finrank_eq
      _ = Module.finrank k (S →ₗ[k[G]] σ.asModule) :=
        (linearMapCongrLeft (k := k) (Representation.ofModule'AsModuleEquiv S)).finrank_eq
  exact nonempty_equiv_iff.mpr
    (nonempty_linearEquiv_of_finrank_linearMap_eq (k := k) (A := k[G]) hhom)

end Representation

/-- **For a finite group over an algebraically closed field of characteristic zero, objects of
`FDRep` are determined by their characters.** -/
theorem _root_.FDRep.nonempty_iso_of_character_eq {k : Type u} {G : Type v}
    [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k] (X Y : FDRep k G)
    (hchar : X.character = Y.character) : Nonempty (X ≅ Y) :=
  nonempty_fdRepIso_iff.mpr
    (Representation.nonempty_equiv_of_character_eq X.ρ Y.ρ hchar)

end TauCeti
