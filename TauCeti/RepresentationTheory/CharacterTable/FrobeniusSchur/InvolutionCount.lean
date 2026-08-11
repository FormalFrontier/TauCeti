/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Trichotomy
public import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# The Frobenius-Schur involution count

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible.
Counting the square roots of a group element,

`θ(x) = #{g ∈ G : g² = x}`,

produces a class function: conjugation carries the square roots of `x` bijectively onto those of
`h x h⁻¹`.  Expanding `θ` in the basis of irreducible characters therefore makes sense, and this
file computes the expansion.  The coefficient of an irreducible character `χ` is the pairing
`⟨χ, θ⟩`, and that pairing telescopes: summing `χ(x) θ(x⁻¹)` over `x` groups the group elements by
the value of `g ↦ (g²)⁻¹`, so the sum collapses to `∑_g χ(g⁻²) = ∑_g χ(g²)`, which is `|G|` times
the **Frobenius-Schur indicator** `ν₂(χ)`.  Hence

`#{g ∈ G : g² = x} = ∑_χ ν₂(χ) χ(x)`,

the degree-weighted signed sum over the irreducibles.  At `x = 1` the left side counts the
solutions of `g² = 1` — the involutions of `G` together with the identity — and the right side is
`∑_χ ν₂(χ) χ(1)`, weighted by the **degrees**; it is not the raw count `∑_χ ν₂(χ)` of orthogonal
minus symplectic irreducibles.

Only one input is genuinely about the indicator, namely that `ν₂` *is* the pairing coefficient
(`TauCeti.ClassFunction.characterPairing_ofCharacter_squareRootCount`); everything else is the
expansion of a class function in the basis of irreducible characters, which
`TauCeti/RepresentationTheory/CharacterTable/Completeness.lean` supplies.  The identity holds over
every algebraically closed field in which `|G|` is invertible, characteristic zero included but not
required: nothing here uses the trichotomy, so the values `ν₂` takes are irrelevant to the count.

## Main statements

* `TauCeti.squareRootConjEquiv`: conjugation is a bijection between the square roots of `x` and
  those of `h * x * h⁻¹`, with `TauCeti.sum_card_squareRoot` the complementary count that the
  square-root counts of a finite group add up to its order.
* `TauCeti.ClassFunction.squareRootCount`: the class function `x ↦ #{g ∈ G : g² = x}`.
* `TauCeti.ClassFunction.characterPairing_ofCharacter_squareRootCount`: **the Frobenius-Schur
  indicator is the coefficient of the character** in the expansion of the square-root count.
* `TauCeti.ClassFunction.card_squareRoot_eq_sum_frobeniusSchurIndicator`: **the involution-counting
  formula** `#{g : g² = x} = ∑_χ ν₂(χ) χ(x)`, over a complete family of irreducibles.
* `TauCeti.frobeniusSchurIndicatorRow`: the indicator of the `i`-th row of `TauCeti.characterTable`.
* `TauCeti.card_squareRoot_eq_sum_frobeniusSchurIndicatorRow_mul_characterTable`: the same formula
  read off the rows of `TauCeti.characterTable`, and
  `TauCeti.card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree` its value at
  `x = 1`, weighted by the degrees.

## Implementation notes

`Nat.card` is used for the count, so no `DecidableEq G` is needed to state the results; the
`Finset.filter`s that the proofs run through are introduced classically and inside the proofs.

The field is taken in `Type` rather than an arbitrary universe, matching
`TauCeti.Representation.frobeniusSchurIndicator` in the sibling module
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Basic.lean`.

## References

This implements the involution-counting item of Layer 7 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
whose `Suggested.lean` pins it as `card_sq_eq_sum_frobeniusSchur` over `ℂ` and the `ℂ`-valued
character table, together with the per-row indicator `frobeniusSchurIndicatorRow`.

See I. M. Isaacs, *Character Theory of Finite Groups* (1976), Corollary 4.6, or J.-P. Serre,
*Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, Proposition 39.
-/

public section

namespace TauCeti

universe v w

/-! ### Square roots in a group -/

section SquareRoot

variable {G : Type v} [Group G]

/-- **Conjugation permutes square roots**: `g ↦ h * g * h⁻¹` is a bijection from the square roots
of `x` onto the square roots of `h * x * h⁻¹`. -/
def squareRootConjEquiv (x h : G) :
    {g : G // g * g = x} ≃ {g : G // g * g = h * x * h⁻¹} where
  toFun g := ⟨h * g.1 * h⁻¹, by
    have hexp : h * g.1 * h⁻¹ * (h * g.1 * h⁻¹) = h * (g.1 * g.1) * h⁻¹ := by group
    rw [hexp, g.2]⟩
  invFun g := ⟨h⁻¹ * g.1 * h, by
    have hexp : h⁻¹ * g.1 * h * (h⁻¹ * g.1 * h) = h⁻¹ * (g.1 * g.1) * h := by group
    rw [hexp, g.2]
    group⟩
  left_inv _ := Subtype.ext (by group)
  right_inv _ := Subtype.ext (by group)

/-- **The number of square roots is a class function of the group element**: `x` and its
conjugate `h * x * h⁻¹` have equally many square roots. -/
theorem card_squareRoot_conj (x h : G) :
    Nat.card {g : G // g * g = h * x * h⁻¹} = Nat.card {g : G // g * g = x} :=
  Nat.card_congr (squareRootConjEquiv x h).symm

variable (G) in
/-- **The square-root counts add up to the order of the group**: each `g` is a square root of
exactly one element, namely `g * g`, so the fibres of squaring partition a finite group. -/
theorem sum_card_squareRoot [Fintype G] :
    ∑ x : G, Nat.card {g : G // g * g = x} = Nat.card G := by
  classical
  have hfib : ∀ x : G,
      Nat.card {g : G // g * g = x} = ({g ∈ Finset.univ | g * g = x} : Finset G).card :=
    fun x => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [hfib]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise fun g _ => Finset.mem_univ (g * g)).symm

end SquareRoot

namespace ClassFunction

/-! ### The square-root counting class function -/

section Count

variable (k : Type) (G : Type v) [Semiring k] [Group G]

/-- **The square-root counting class function** `x ↦ #{g ∈ G : g² = x}`, with values in `k`.  It is
a class function by `TauCeti.card_squareRoot_conj`. -/
noncomputable def squareRootCount : ClassFunction k G :=
  ⟨fun x => (Nat.card {g : G // g * g = x} : k),
    mem_iff.mpr fun x h => by rw [card_squareRoot_conj]⟩

variable {k G}

/-- The square-root counting class function evaluates to the number of square roots. -/
@[simp]
theorem squareRootCount_apply (x : G) :
    (squareRootCount k G).1 x = (Nat.card {g : G // g * g = x} : k) :=
  (rfl)

end Count

/-! ### The indicator as a pairing coefficient -/

section Pairing

variable {k : Type} {G : Type v} [Field k] [Group G] [Fintype G]

/-- **The Frobenius-Schur indicator is the coefficient of the character.** Pairing the character of
`ρ` against the square-root count returns `ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)`.

Both sides are averages of a sum over `G` of character values, and the two sums agree termwise
after the group elements are grouped by the value of `g ↦ (g²)⁻¹` and the resulting sum
`∑_g χ(g⁻²)` is reindexed by inversion. -/
theorem characterPairing_ofCharacter_squareRootCount {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    characterPairing (ofCharacter ρ) (squareRootCount k G) =
      Representation.frobeniusSchurIndicator ρ := by
  classical
  have hcard : ∀ x : G, Nat.card {g : G // g * g = x⁻¹} =
      ({g ∈ Finset.univ | (g * g)⁻¹ = x} : Finset G).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card
      (Finset.filter_congr fun g _ => (inv_eq_iff_eq_inv (a := g * g) (b := x)).symm)
  rw [characterPairing_apply, Representation.frobeniusSchurIndicator_def]
  refine congrArg _ ?_
  calc ∑ x : G, (ofCharacter ρ).1 x * (squareRootCount k G).1 x⁻¹
      = ∑ x : G, ∑ _g ∈ {g ∈ Finset.univ | (g * g)⁻¹ = x}, ρ.character x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [ofCharacter_apply, squareRootCount_apply, hcard x, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
    _ = ∑ g : G, ρ.character ((g * g)⁻¹) :=
        Finset.sum_fiberwise' Finset.univ (fun g : G => (g * g)⁻¹) fun x => ρ.character x
    _ = ∑ g : G, ρ.character (g ^ 2) := by
        refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
        rw [Equiv.inv_apply, sq, ← mul_inv_rev]

end Pairing

/-! ### The involution-counting formula -/

section Formula

variable {k : Type} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} [Fintype ι] {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
  (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

include hind hcard

/-- **The involution-counting formula** `#{g : g² = x} = ∑_χ ν₂(χ) χ(x)`, summed over a complete
family of pairwise inequivalent irreducible representations: the square-root count is the class
function whose coordinates in the basis of irreducible characters are the Frobenius-Schur
indicators. -/
theorem card_squareRoot_eq_sum_frobeniusSchurIndicator (x : G) :
    (Nat.card {g : G // g * g = x} : k) =
      ∑ i, Representation.frobeniusSchurIndicator (ρ i) * (ρ i).character x := by
  have hexp := apply_eq_sum_characterPairing_mul_character ρ hind hcard (squareRootCount k G) x
  rw [squareRootCount_apply] at hexp
  refine hexp.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [characterPairing_ofCharacter_squareRootCount]

end Formula

end ClassFunction

/-! ### The formula on the character table -/

section Table

variable (k : Type) (G : Type v) [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

variable {G} in
/-- **The Frobenius-Schur indicator of the `i`-th row of the character table**: the indicator of a
representation affording the `i`-th irreducible character. -/
noncomputable def frobeniusSchurIndicatorRow (i : Fin (Nat.card (ConjClasses G))) : k :=
  Representation.frobeniusSchurIndicator (irreducibleRepresentation k i)

variable {G} in
/-- The defining equation of the row indicator.  The definition is not `@[expose]`d, so this is how
it unfolds outside this file. -/
theorem frobeniusSchurIndicatorRow_def (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i =
      Representation.frobeniusSchurIndicator (irreducibleRepresentation k i) :=
  (rfl)

variable {G} in
/-- **The row indicator takes only the values `1`, `0` and `-1`** in characteristic zero, by the
Frobenius-Schur trichotomy applied to a representation affording the row. -/
theorem frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one [CharZero k]
    (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i = 1 ∨ frobeniusSchurIndicatorRow k i = 0 ∨
      frobeniusSchurIndicatorRow k i = -1 :=
  Representation.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one
    (irreducibleRepresentation k i)

/-- **The involution-counting formula on the character table**: the number of square roots of `x`
is the sum over the rows of the character table of the row's Frobenius-Schur indicator times the
entry in the column of the class of `x`. -/
theorem card_squareRoot_eq_sum_frobeniusSchurIndicatorRow_mul_characterTable (x : G) :
    (Nat.card {g : G // g * g = x} : k) =
      ∑ i, frobeniusSchurIndicatorRow k i * characterTable k G i (ConjClasses.mk x) := by
  have hsum := ClassFunction.card_squareRoot_eq_sum_frobeniusSchurIndicator
    (irreducibleRepresentation k) (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) x
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [frobeniusSchurIndicatorRow_def, characterTable_apply,
    ← character_irreducibleRepresentation k i]

/-- **The count of the solutions of `g² = 1`**, the involutions of `G` together with the identity:
it is the sum of the Frobenius-Schur indicators of the rows of the character table, each weighted
by the **degree** of its character.  The unweighted sum `∑ᵢ ν₂(χᵢ)` counts the orthogonal
irreducibles minus the symplectic ones and is a different quantity. -/
theorem card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree :
    (Nat.card {g : G // g * g = 1} : k) =
      ∑ i : Fin (Nat.card (ConjClasses G)),
        frobeniusSchurIndicatorRow k i * (characterDegree k i : k) := by
  have hsum := card_squareRoot_eq_sum_frobeniusSchurIndicatorRow_mul_characterTable k G (1 : G)
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [characterTable_one]

end Table

end TauCeti
