/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Square

/-!
# The Frobenius-Schur indicator

For a finite group `G` and a finite-dimensional representation `ρ` of `G` over a field `k`, the
**Frobenius-Schur indicator** is the average of the character over squares,
`ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)`.

The point of the indicator is what it counts. Mathlib's `Representation.character` averages to the
dimension of the invariants (`Representation.card_inv_mul_sum_char_eq_finrank`), and
`Representation.char_symmetricSquare_sub_char_exteriorSquare` says that the summand `χ(g²)` is the
difference of the symmetric-square and exterior-square characters at `g`. Averaging that identity
gives the main result of this file: the indicator is the signed count

`ν₂(ρ) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`

of the invariants in the symmetric and exterior squares. Reading the companion identity
`Representation.char_tensorSquare` the same way shows that those same two invariant dimensions sum
to the dimension of the invariants of `V ⊗ V`.

Both identities are proved wherever `|G|` is invertible in `k`, with **no hypothesis on
characteristic two**, because the two character identities they average hold over every field: the
tensor square need not split for the two invariant counts to add up. The price is that a count of
invariants only ever appears here through its image in `k`, so in characteristic `p` the additivity
of the invariant dimensions is an identity of residues. Over a field of characteristic zero it
upgrades to an equality of natural numbers, and there the indicator is an integer.

This is the module-level half of the roadmap's Layer 7 pair; the `FDRep`-level indicator and its
agreement with this one are at the end of the file.

## Main definitions

* `TauCeti.Representation.frobeniusSchurIndicator`: `ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)`.
* `TauCeti.FDRep.frobeniusSchurIndicator`: the same indicator, for a `V : FDRep k G`.

## Main results

* `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants`: **the indicator is
  the signed count of invariants in the two squares**, `ν₂(ρ) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.
* `TauCeti.Representation.finrank_invariants_tprod_self`: **the two invariant dimensions add to
  that of the tensor square**, `dim (V ⊗ V)ᴳ = dim (Sym²V)ᴳ + dim (Λ²V)ᴳ`, as an identity in `k`
  in general (`TauCeti.Representation.finrank_invariants_tprod_self_cast`) and as natural numbers
  in characteristic zero.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_intCast`: in characteristic zero the indicator
  is the integer `dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.
* `TauCeti.FDRep.frobeniusSchurIndicator_def`: the `FDRep`-level indicator is the indicator of the
  underlying representation.

## Implementation notes

The definition asks only for a `Fintype G`: invertibility of `|G|` is a hypothesis of the theorems,
not of the object. The two statements that do not mention the indicator ask only for `Finite G`,
and build the `Fintype` they average over inside their proofs.

The `FDRep`-level indicator is the module-level one applied to `V.ρ` rather than a second copy of
the average, so `TauCeti.FDRep.frobeniusSchurIndicator_def` unfolds that one definition and nothing
else, and every theorem about the average transfers through it. Neither definition is `@[expose]`d,
so the two `_def` lemmas are the only route to the two averages from another module; that is what
they are for. It is also why both are proved by a parenthesised `(rfl)`: a proof written
syntactically as `:= rfl` is implicitly tagged `@[defeq]`, and validating that tag on an exported
theorem asks that every definition it unfolds be exposed, which these two deliberately are not. The
parentheses suppress the tag, which is what `@[defeq]`'s own documentation prescribes them for; a
bare `rfl` does not compile here.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7, “The indicator on the module spine” and “The symmetric and exterior squares”. The
  invariant bilinear forms of that layer, and the trichotomy `ν₂ ∈ {+1, 0, -1}` for an irreducible
  representation over `ℂ`, are proved in the sibling module
  `TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Trichotomy.lean`, which identifies
  the invariant forms with the invariants of the duals of the symmetric and exterior squares.
  What this file supplies is the counting identity those statements are read off from.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Lemma 4.4 and Theorem 4.5.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

universe v w w'

variable {k : Type} {G : Type v} {V : Type w}

namespace TauCeti

open Module (finrank)

namespace Representation

section Fintype

variable [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]

/-- **The Frobenius-Schur indicator** of a representation of a finite group,
`ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)`. It is the theorems below, not the average itself, that ask for `V` to be
finite-dimensional and for `|G|` to be invertible in `k`. -/
noncomputable def frobeniusSchurIndicator (ρ : Representation k G V) : k :=
  (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character (g ^ 2)

/-- The defining equation of the indicator, `ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)`. The definition is not
`@[expose]`d, so this is how it unfolds outside this file. -/
theorem frobeniusSchurIndicator_def (ρ : Representation k G V) :
    frobeniusSchurIndicator ρ = (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character (g ^ 2) :=
  (rfl)

/-- Equivalent representations have the same Frobenius-Schur indicator, since they have the same
character. -/
theorem frobeniusSchurIndicator_eq_of_equiv {W : Type w'} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (φ : Representation.Equiv ρ σ) :
    frobeniusSchurIndicator ρ = frobeniusSchurIndicator σ := by
  simp only [frobeniusSchurIndicator, Representation.char_iso φ]

variable [FiniteDimensional k V]

/-- The Frobenius-Schur indicator of a trivial representation is its dimension: every `χ(g²)` is
`dim V`, and the average of a constant is that constant. -/
@[simp]
theorem frobeniusSchurIndicator_trivial [Invertible (Nat.card G : k)] :
    frobeniusSchurIndicator (Representation.trivial k G V) = (finrank k V : k) := by
  have hchar : ∀ g : G, (Representation.trivial k G V).character (g ^ 2) = (finrank k V : k) := by
    intro g
    have h1 : (Representation.trivial k G V) (g ^ 2) = LinearMap.id (R := k) (M := V) := by
      ext v; simp
    rw [Representation.character, h1, LinearMap.trace_id]
  simp only [frobeniusSchurIndicator, hchar, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Invertible.ne_zero _), one_mul]

/-- **The Frobenius-Schur indicator counts invariants in the two squares.** Averaging
`Representation.char_symmetricSquare_sub_char_exteriorSquare` over the group,
`ν₂(ρ) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.

This holds over every field in which `|G|` is invertible, characteristic two included, because the
character identity it averages does; what fails in characteristic two is the splitting of the
tensor square itself, not this count. -/
theorem frobeniusSchurIndicator_eq_sub_finrank_invariants [Invertible (Nat.card G : k)]
    (ρ : Representation k G V) :
    frobeniusSchurIndicator ρ =
      (finrank k (ρ.symmetricPower 2).invariants : k) -
        (finrank k (ρ.exteriorPower 2).invariants : k) := by
  rw [← Representation.card_inv_mul_sum_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank, ← mul_sub, ← Finset.sum_sub_distrib,
    frobeniusSchurIndicator]
  simp_rw [Representation.char_symmetricSquare_sub_char_exteriorSquare, sq]

end Fintype

section Finite

variable [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Invertible (Nat.card G : k)]

/-- **The two invariant dimensions add to that of the tensor square**, as an identity in `k`:
averaging `Representation.char_tensorSquare` gives `dim (V ⊗ V)ᴳ = dim (Sym²V)ᴳ + dim (Λ²V)ᴳ`
in `k`.

As with `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants`, no hypothesis
on characteristic two is needed: this is an equality of invariant dimensions, not a decomposition
of the tensor square. In characteristic `p` it is an identity of residues only; see
`TauCeti.Representation.finrank_invariants_tprod_self` for the characteristic-zero form. -/
theorem finrank_invariants_tprod_self_cast (ρ : Representation k G V) :
    (finrank k (Representation.tprod ρ ρ).invariants : k) =
      (finrank k (ρ.symmetricPower 2).invariants : k) +
        (finrank k (ρ.exteriorPower 2).invariants : k) := by
  have : Fintype G := Fintype.ofFinite G
  rw [← Representation.card_inv_mul_sum_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank, ← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  rw [← Representation.char_tensorSquare ρ g, Representation.char_tensor, Pi.mul_apply, sq]

/-- **The two invariant dimensions add to that of the tensor square**, as natural numbers: over a
field of characteristic zero, `dim (V ⊗ V)ᴳ = dim (Sym²V)ᴳ + dim (Λ²V)ᴳ`. -/
theorem finrank_invariants_tprod_self [CharZero k] (ρ : Representation k G V) :
    finrank k (Representation.tprod ρ ρ).invariants =
      finrank k (ρ.symmetricPower 2).invariants + finrank k (ρ.exteriorPower 2).invariants := by
  exact_mod_cast finrank_invariants_tprod_self_cast (k := k) ρ

end Finite

section CharZero

variable [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **In characteristic zero the Frobenius-Schur indicator is an integer**, namely the difference
`dim (Sym²V)ᴳ - dim (Λ²V)ᴳ` of the two invariant counts. In characteristic zero `|G|` is
automatically invertible, so no such hypothesis is needed. -/
theorem frobeniusSchurIndicator_eq_intCast (ρ : Representation k G V) :
    frobeniusSchurIndicator ρ =
      (((finrank k (ρ.symmetricPower 2).invariants : ℤ) -
        (finrank k (ρ.exteriorPower 2).invariants : ℤ) : ℤ) : k) := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants]
  push_cast
  rfl

end CharZero

end Representation

namespace FDRep

variable [Field k] [Group G] [Fintype G]

/-- **The Frobenius-Schur indicator** of a finite-dimensional representation presented as an
object of `FDRep k G`: the indicator `|G|⁻¹ ∑_g χ(g²)` of the underlying representation `V.ρ`. -/
noncomputable def frobeniusSchurIndicator (V : FDRep k G) : k :=
  Representation.frobeniusSchurIndicator V.ρ

/-- The two forms of the indicator agree: the `FDRep`-level indicator of `V` is the indicator of
the underlying representation `V.ρ`. It is a `simp` lemma, so results proved on the module spine
apply to the `FDRep`-level indicator automatically. -/
@[simp]
theorem frobeniusSchurIndicator_def (V : FDRep k G) :
    frobeniusSchurIndicator V = Representation.frobeniusSchurIndicator V.ρ :=
  (rfl)

end FDRep

end TauCeti
