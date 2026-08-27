/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.RepresentationRing.Basic
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RingTheory.Semisimple.Multiplicity
import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# Injectivity of the character map on the representation ring

Let `G` be a finite group and `k` an algebraically closed field of characteristic zero. This file
proves that the character homomorphism from the representation ring of `G` is injective. Thus a
virtual representation is determined by its character.

The main input is Maschke's theorem. The `k[G]`-module underlying every object of `FDRep k G`
decomposes as a finite direct sum of simple submodules. If two representations `X` and `Y` have
the same character, pairing that equality against the character of a simple module `S` shows that

`finrank k (S →ₗ[k[G]] X) = finrank k (S →ₗ[k[G]] Y)`.

By `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`, these dimensions count the simple
summands isomorphic to `S`. The counts therefore agree in every simple-module isomorphism class.
`Equiv.ofFiberEquiv` matches the two finite families class by class, and the resulting family of
linear equivalences assembles into an isomorphism `X ≅ Y`.

For the representation ring itself, every element of split `K₀` is a difference `[V] - [W]`.
A difference in the kernel has `V.character = W.character`, so the object-level theorem makes
`V` and `W` isomorphic and their difference vanishes.

Characteristic zero is used both to invert the nonzero group order and when equality of the
character-pairing values in `k` is read back as equality of natural-number multiplicities.
Algebraic closure is the splitting-field hypothesis used by the character pairing.

## Main results

* `TauCeti.FDRep.nonempty_iso_of_character_eq_of_charZero`: two finite-dimensional
  representations with equal characters are isomorphic in the semisimple characteristic-zero
  regime.
* `TauCeti.repRingCharacter_injective`: the character homomorphism on the representation ring is
  injective.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part I, §§2.3 and 2.5, and Part II,
  §9.1.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §§25 and 30.

This is the injectivity target in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra

namespace TauCeti

universe u v

namespace FDRep

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]

/-- **Finite-dimensional representations are determined by their characters in characteristic
zero.** Over an algebraically closed field in which the finite group order is invertible, Maschke
decomposes the underlying group-algebra modules into finite sums of simple modules. Pairing equal
characters against a simple character equates the corresponding natural-number multiplicities;
characteristic zero makes the cast of those multiplicities injective. Matching the summands in
each simple-module isomorphism class then gives an isomorphism of representations. -/
theorem nonempty_iso_of_character_eq_of_charZero (X Y : FDRep k G)
    (hchar : X.character = Y.character) : Nonempty (X ≅ Y) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hfinX : Module.Finite k[G] (_root_.Representation.asModule X.ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  have hfinY : Module.Finite k[G] (_root_.Representation.asModule Y.ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  obtain ⟨n, SX, eX, hSX⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp k[G]
      (_root_.Representation.asModule X.ρ)
  obtain ⟨m, SY, eY, hSY⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp k[G]
      (_root_.Representation.asModule Y.ρ)
  let _ (i : Fin n) : Module.Finite k (SX i) :=
    Module.Finite.of_injective ((SX i).subtype.restrictScalars k) Subtype.val_injective
  let _ (i : Fin m) : Module.Finite k (SY i) :=
    Module.Finite.of_injective ((SY i).subtype.restrictScalars k) Subtype.val_injective
  let _ (i : Fin n) : IsSimpleModule k[G] (SX i) := hSX i
  let _ (i : Fin m) : IsSimpleModule k[G] (SY i) := hSY i
  let epX : _root_.Representation.asModule X.ρ ≃ₗ[k[G]] ∀ i, SX i :=
    eX.trans DFinsupp.linearEquivFunOnFintype
  let epY : _root_.Representation.asModule Y.ρ ≃ₗ[k[G]] ∀ i, SY i :=
    eY.trans DFinsupp.linearEquivFunOnFintype
  let cX : Fin n → SimpleSubmoduleClasses k[G] k[G] := fun i ↦
    simpleModuleClass k[G] (SX i)
  let cY : Fin m → SimpleSubmoduleClasses k[G] k[G] := fun i ↦
    simpleModuleClass k[G] (SY i)
  have hfiber : ∀ c, Nat.card {i // cX i = c} = Nat.card {j // cY j = c} := by
    intro c
    induction c using SimpleSubmoduleClasses.ind with
    | mk S hS =>
      let Z := _root_.Representation.ofModule' (k := k) (G := G) S
      let _ : IsSimpleModule k[G] (_root_.Representation.asModule Z) :=
        (Representation.ofModule'AsModuleEquiv S).isSimpleModule_iff.mpr hS
      have hpair : Module.finrank k (Representation.IntertwiningMap Z X.ρ) =
          Module.finrank k (Representation.IntertwiningMap Z Y.ρ) := by
        have hcf : ClassFunction.ofFDRep X = ClassFunction.ofFDRep Y :=
          Subtype.ext <| funext fun g ↦ by
            simp only [ClassFunction.ofFDRep_apply, hchar]
        have heq : ClassFunction.characterPairing (ClassFunction.ofFDRep X)
              (ClassFunction.ofCharacter Z) =
            ClassFunction.characterPairing (ClassFunction.ofFDRep Y)
              (ClassFunction.ofCharacter Z) := by
          rw [hcf]
        rw [ClassFunction.ofFDRep_eq_ofCharacter,
          ClassFunction.characterPairing_ofCharacter_eq_finrank,
          ClassFunction.ofFDRep_eq_ofCharacter,
          ClassFunction.characterPairing_ofCharacter_eq_finrank] at heq
        exact Nat.cast_injective heq
      have hmultX : Module.finrank k (Representation.IntertwiningMap Z X.ρ) =
          Nat.card {i // Nonempty
            (_root_.Representation.asModule Z ≃ₗ[k[G]] SX i)} := by
        calc
          _ = Module.finrank k (_root_.Representation.asModule Z →ₗ[k[G]]
                _root_.Representation.asModule X.ρ) :=
            (Representation.IntertwiningMap.equivLinearMapAsModule Z X.ρ).finrank_eq
          _ = _ := finrank_linearMap_eq_natCard_of_linearEquiv_pi
            (k := k) (S := _root_.Representation.asModule Z) epX
      have hmultY : Module.finrank k (Representation.IntertwiningMap Z Y.ρ) =
          Nat.card {i // Nonempty
            (_root_.Representation.asModule Z ≃ₗ[k[G]] SY i)} := by
        calc
          _ = Module.finrank k (_root_.Representation.asModule Z →ₗ[k[G]]
                _root_.Representation.asModule Y.ρ) :=
            (Representation.IntertwiningMap.equivLinearMapAsModule Z Y.ρ).finrank_eq
          _ = _ := finrank_linearMap_eq_natCard_of_linearEquiv_pi
            (k := k) (S := _root_.Representation.asModule Z) epY
      have hpredX (i : Fin n) : cX i = SimpleSubmoduleClasses.mk S ↔
          Nonempty (_root_.Representation.asModule Z ≃ₗ[k[G]] SX i) := by
        rw [show cX i = simpleModuleClass k[G] (SX i) by rfl,
          simpleModuleClass_eq_mk_iff]
        constructor
        · rintro ⟨e⟩
          exact ⟨(Representation.ofModule'AsModuleEquiv S).trans e.symm⟩
        · rintro ⟨e⟩
          exact ⟨e.symm.trans (Representation.ofModule'AsModuleEquiv S)⟩
      have hpredY (i : Fin m) : cY i = SimpleSubmoduleClasses.mk S ↔
          Nonempty (_root_.Representation.asModule Z ≃ₗ[k[G]] SY i) := by
        rw [show cY i = simpleModuleClass k[G] (SY i) by rfl,
          simpleModuleClass_eq_mk_iff]
        constructor
        · rintro ⟨e⟩
          exact ⟨(Representation.ofModule'AsModuleEquiv S).trans e.symm⟩
        · rintro ⟨e⟩
          exact ⟨e.symm.trans (Representation.ofModule'AsModuleEquiv S)⟩
      calc
        Nat.card {i // cX i = SimpleSubmoduleClasses.mk S} =
            Nat.card {i // Nonempty
              (_root_.Representation.asModule Z ≃ₗ[k[G]] SX i)} :=
          Nat.card_congr (Equiv.subtypeEquivRight hpredX)
        _ = Nat.card {i // Nonempty
              (_root_.Representation.asModule Z ≃ₗ[k[G]] SY i)} := hmultX ▸ hpair ▸ hmultY
        _ = Nat.card {i // cY i = SimpleSubmoduleClasses.mk S} :=
          Nat.card_congr (Equiv.subtypeEquivRight hpredY).symm
  have efiber : ∀ c, {i // cX i = c} ≃ {j // cY j = c} := fun c ↦ by
    letI := Fintype.ofFinite {i // cX i = c}
    letI := Fintype.ofFinite {j // cY j = c}
    exact Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using hfiber c)
  let σ : Fin n ≃ Fin m := Equiv.ofFiberEquiv efiber
  have hclass (i : Fin n) : cX i = cY (σ i) := (Equiv.ofFiberEquiv_map efiber i).symm
  have hiso (i : Fin n) : Nonempty (SX i ≃ₗ[k[G]] SY (σ i)) :=
    simpleModuleClass_eq_iff.mp (hclass i)
  let eXY : _root_.Representation.asModule X.ρ ≃ₗ[k[G]]
      _root_.Representation.asModule Y.ρ :=
    eX |>.trans (DirectSum.lequivCongrLeft k[G] σ) |>.trans
      (DFinsupp.mapRange.linearEquiv fun j ↦
        (hiso (σ.symm j)).some.trans
          (LinearEquiv.ofEq _ _ (congrArg SY (σ.apply_symm_apply j)))) |>.trans eY.symm
  let i := fdRepIsoOfAsModuleLinearEquiv eXY
  rw [FDRep.of_ρ_eq_self, FDRep.of_ρ_eq_self] at i
  exact ⟨i⟩

end FDRep

section CharacterMap

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- Every virtual representation is the difference of the classes of two genuine
representations. This presentation lemma is internal: the public interface for split `K₀` remains
its induction principle and universal property. -/
private theorem exists_repRing_eq_sub_of (x : repRing k G) :
    ∃ V W : FDRep k G, x = SplitK0.of V - SplitK0.of W := by
  induction x using SplitK0.induction_on with
  | zero =>
      exact ⟨0, 0, by simp⟩
  | of V =>
      exact ⟨V, 0, by simp⟩
  | add x y hx hy =>
      obtain ⟨V, W, rfl⟩ := hx
      obtain ⟨V', W', rfl⟩ := hy
      refine ⟨V ⊞ V', W ⊞ W', ?_⟩
      simp only [SplitK0.of_biprod]
      abel
  | neg x hx =>
      obtain ⟨V, W, rfl⟩ := hx
      exact ⟨W, V, by abel⟩

/-- **The character homomorphism is injective in characteristic zero.** If a virtual difference
`[V] - [W]` has zero character, then `V` and `W` have equal characters. Semisimplicity and
`FDRep.nonempty_iso_of_character_eq_of_charZero` make them isomorphic, so their classes agree in
the representation ring. -/
theorem repRingCharacter_injective [Finite G] [IsAlgClosed k] [CharZero k] :
    Function.Injective (repRingCharacter k G) := by
  intro x y hxy
  apply sub_eq_zero.mp
  obtain ⟨V, W, hVW⟩ := exists_repRing_eq_sub_of (x - y)
  have hzero : repRingCharacter k G (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hchar : V.character = W.character := by
    rw [hVW, map_sub, repRingCharacter_of, repRingCharacter_of, sub_eq_zero] at hzero
    exact hzero
  obtain ⟨i⟩ := FDRep.nonempty_iso_of_character_eq_of_charZero V W hchar
  rw [hVW, SplitK0.of_congr i, sub_self]

end CharacterMap

end TauCeti
