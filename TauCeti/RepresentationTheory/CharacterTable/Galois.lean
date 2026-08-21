/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.FiniteOrder
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# The Galois action on character values

A character value `χ(g)` at an element with `g ^ n = 1` is a sum of `n`-th roots of unity, the
eigenvalues of `ρ g`, weighted by the dimensions of the eigenspaces. A ring endomorphism `σ` of the
coefficient field fixes those dimensions, which enter as natural numbers, so it acts on `χ(g)` only
through its action on the roots of unity. The roots of unity form a cyclic group, so `σ` acts on
them as a power map `μ ↦ μ ^ j`, and then `σ (χ(g)) = ∑ dim(V_μ) · μ ^ j = χ(g ^ j)`: **the Galois
action on character values is by power maps of the group element**.

This file proves that identity, first for an arbitrary ring endomorphism of an algebraically closed
field and then, over `ℂ`, in the form the character-theory roadmap asks for, with the exponent `j`
supplied by Mathlib's cyclotomic character `IsPrimitiveRoot.autToPow`, which reads it off a chosen
primitive root of unity and an algebra automorphism. A field automorphism of `ℂ` is automatically
`ℚ`-linear, so `ℂ ≃ₐ[ℚ] ℂ` is the group of field automorphisms of `ℂ`; the endomorphism statement
above is the more general one, since a `ℚ`-linear ring homomorphism `ℂ →+* ℂ` is an embedding but
need not be surjective.

Complex conjugation is the instance `j = n - 1` of all this, and gives back
`TauCeti.Representation.conj_char_eq_char_inv`, `conj (χ g) = χ g⁻¹`.

Two consequences are recorded: `χ(g)` and `χ(g ^ j)` are conjugate algebraic numbers over `ℚ`
(they are `IsConjRoot ℚ`), and a character value that is rational is unchanged by the power maps
that automorphisms of `ℂ` realize.

Only the direction "an automorphism determines the power map" is proved here. The converse
direction, that every `j` coprime to the exponent is realized by some `σ : ℂ →+* ℂ`, needs a
cyclotomic Galois automorphism to be extended along a transcendence basis of `ℂ`, and is not proved
here; the identity above is the load-bearing half, and it is the half the Dixon-Schneider lift
consumes once such a `σ` is in hand.

## Main statements

* `TauCeti.Representation.map_character_eq_character_pow`: if `σ` raises every `n`-th root of unity
  to the `j`-th power and `g ^ n = 1`, then `σ (χ(g)) = χ(g ^ j)`. The variant
  `TauCeti.Representation.map_character_eq_character_pow_of_isPrimitiveRoot` witnesses the power on
  a single primitive root of unity.
* `TauCeti.Representation.map_ofCharacter_eq_powMap`: on a group of exponent dividing `n` the
  Galois twist `σ ∘ χ` is the power-map twist `TauCeti.ClassFunction.powMap j` of the class
  function of `χ`, so the twist is an operation on `ClassFunction k G`.
* `TauCeti.FDRep.map_character_eq_character_pow_of_isPrimitiveRoot`: over `ℂ`, a field
  automorphism `f` of `ℂ` sends `χ(g)` to `χ(g ^ j)`, with `j` the cyclotomic exponent
  `IsPrimitiveRoot.autToPow` attaches to `f`.
* `TauCeti.FDRep.isConjRoot_character_pow`: `χ(g)` and `χ(g ^ j)` are conjugate over `ℚ`.
* `TauCeti.FDRep.character_pow_eq_character_of_mem_range`: a rational character value is unchanged
  by the power maps that automorphisms of `ℂ` realize.

## References

* [Character Theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 4, "The Galois action".
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Lemma 9.16.
* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.4.
-/

public section

namespace TauCeti

open Module Polynomial

universe u v w

namespace Representation

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **The Galois action on character values is by power maps.** If `g ^ n = 1` and the ring
endomorphism `σ` of the coefficient field raises every `n`-th root of unity to the `j`-th power,
then `σ (χ(g)) = χ(g ^ j)`: the eigenvalues of `ρ g` are `n`-th roots of unity, and `σ` fixes the
dimensions of the eigenspaces they are weighted by. -/
theorem map_character_eq_character_pow (ρ : Representation k G V) {g : G} {n j : ℕ}
    (hn : (n : k) ≠ 0) (hg : g ^ n = 1) (σ : k →+* k) (hσ : ∀ μ : k, μ ^ n = 1 → σ μ = μ ^ j) :
    σ (ρ.character g) = ρ.character (g ^ j) := by
  simp only [Representation.character, map_pow]
  exact End.map_trace_eq_trace_pow hn (by rw [← map_pow, hg, map_one]) σ hσ

/-- **The Galois action on character values is by power maps**, in the form where the power `j` is
witnessed on a single primitive `n`-th root of unity: if `σ ζ = ζ ^ j` for a primitive `n`-th root
of unity `ζ` and `g ^ n = 1`, then `σ (χ(g)) = χ(g ^ j)`. -/
theorem map_character_eq_character_pow_of_isPrimitiveRoot (ρ : Representation k G V) {g : G}
    {n j : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hn : (n : k) ≠ 0) (hg : g ^ n = 1)
    (σ : k →+* k) (hσ : σ ζ = ζ ^ j) :
    σ (ρ.character g) = ρ.character (g ^ j) :=
  have : NeZero n := ⟨fun h => hn (by rw [h, Nat.cast_zero])⟩
  Representation.map_character_eq_character_pow ρ hn hg σ
    fun _ hμ => IsPrimitiveRoot.map_eq_pow hζ σ hσ hμ

end Representation

section ClassFunction

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [IsAlgClosed k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **The Galois twist of a character is the power-map twist of its class function.** On a group
of exponent dividing `n`, the composite `σ ∘ χ` is `TauCeti.ClassFunction.powMap j` applied to the
class function of `χ`. This is the form in which a Galois group acts on `ClassFunction k G`. -/
theorem Representation.map_ofCharacter_eq_powMap (ρ : Representation k G V) {n j : ℕ}
    (hn : (n : k) ≠ 0) (hG : ∀ g : G, g ^ n = 1) (σ : k →+* k)
    (hσ : ∀ μ : k, μ ^ n = 1 → σ μ = μ ^ j) :
    σ ∘ (ClassFunction.ofCharacter ρ).1 =
      (ClassFunction.powMap j (ClassFunction.ofCharacter ρ)).1 := by
  funext g
  simpa only [Function.comp_apply, ClassFunction.powMap_apply, ClassFunction.ofCharacter_apply]
    using Representation.map_character_eq_character_pow ρ hn (hG g) σ hσ

end ClassFunction

namespace FDRep

variable {G : Type v} [Monoid G]

/-- **The Galois action on complex character values is by power maps.** If `g ^ n = 1` and the ring
endomorphism `σ` of `ℂ` raises every `n`-th root of unity to the `j`-th power, then
`σ (χ(g)) = χ(g ^ j)`. -/
theorem map_character_eq_character_pow (X : FDRep ℂ G) {g : G} {n j : ℕ} (hn : n ≠ 0)
    (hg : g ^ n = 1) (σ : ℂ →+* ℂ) (hσ : ∀ μ : ℂ, μ ^ n = 1 → σ μ = μ ^ j) :
    σ (X.character g) = X.character (g ^ j) :=
  Representation.map_character_eq_character_pow X.ρ (Nat.cast_ne_zero.2 hn) hg σ hσ

/-- **The Galois action on complex character values is by power maps**, with the power supplied by
the cyclotomic character `IsPrimitiveRoot.autToPow`: a field automorphism `f` of `ℂ`, which is the
same thing as a `ℚ`-algebra automorphism, acts on the roots of unity of order dividing `n` as
`ζ ↦ ζ ^ j` for a unique `j : (ZMod n)ˣ`, and then `f (χ(g)) = χ(g ^ j)` whenever `g ^ n = 1`. -/
theorem map_character_eq_character_pow_of_isPrimitiveRoot (X : FDRep ℂ G) {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {g : G} (hg : g ^ n = 1) (f : ℂ ≃ₐ[ℚ] ℂ) :
    f (X.character g) = X.character (g ^ ((hζ.autToPow ℚ f : ZMod n).val)) :=
  FDRep.map_character_eq_character_pow X (NeZero.ne n) hg f.toAlgHom.toRingHom
    fun _ hμ => IsPrimitiveRoot.map_eq_pow hζ _ (hζ.autToPow_spec ℚ f).symm hμ

/-- **A character value and its power-map twist are conjugate algebraic numbers**: `χ(g)` and
`χ(g ^ j)` have the same minimal polynomial over `ℚ`, being images of one another under a field
automorphism of `ℂ`. -/
theorem isConjRoot_character_pow (X : FDRep ℂ G) {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {g : G} (hg : g ^ n = 1) (f : ℂ ≃ₐ[ℚ] ℂ) :
    IsConjRoot ℚ (X.character g) (X.character (g ^ ((hζ.autToPow ℚ f : ZMod n).val))) := by
  rw [← FDRep.map_character_eq_character_pow_of_isPrimitiveRoot X hζ hg f]
  exact isConjRoot_of_algEquiv _ f

/-- **A rational character value is fixed by the power maps that automorphisms of `ℂ` realize**: if
`χ(g)` is rational then `χ(g ^ j) = χ(g)` for every `j` coming from a field automorphism of `ℂ`. -/
theorem character_pow_eq_character_of_mem_range (X : FDRep ℂ G) {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {g : G} (hg : g ^ n = 1) (f : ℂ ≃ₐ[ℚ] ℂ)
    (hχ : X.character g ∈ (algebraMap ℚ ℂ).range) :
    X.character (g ^ ((hζ.autToPow ℚ f : ZMod n).val)) = X.character g := by
  obtain ⟨q, hq⟩ := hχ
  rw [← FDRep.map_character_eq_character_pow_of_isPrimitiveRoot X hζ hg f, ← hq, AlgEquiv.commutes]

end FDRep

end TauCeti
