/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.EigenvectorSearch
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Structure

/-!
# The modular central-character search finds one row per conjugacy class

`TauCeti.ClassData.centralCharacterSearch` is the executable simultaneous eigenvalue search of the
Burnside--Dixon--Schneider algorithm: it returns the `Finset` of normalized common left eigenrows of
the reduced class-multiplication matrices. `TauCeti.ClassData.mem_centralCharacterSearch` says what
its elements are; it does not say **how many** there are, and without that the algorithm cannot know
that it has found every central character rather than a proper subset of them.

This file supplies the count. Over a coefficient field that splits the centre of the group algebra
into coordinates, the search returns exactly `r` rows, `r` the number of conjugacy classes. The
splitting hypothesis is essential and not automatic: over a field too small to contain the relevant
roots of unity some characters of `Z(F[G])` take values in a proper extension of `F` and are simply
invisible to a search carried out over `F`, so the search would come back short. At a good Dixon
prime the good-prime structure theorem
`TauCeti.IsGoodDixonPrime.nonempty_center_algEquiv_conjClasses` supplies exactly that hypothesis
over `ZMod p`, which is what makes the modular phase of the algorithm lossless.

The argument is a chain of transports and one genuinely new input. Splitting the centre turns its
characters into the coordinate evaluations of a finite power of `F`, and those are in bijection with
the coordinates (`Pi.evalAlgHomEquiv`); the class-algebra dictionary
`TauCeti.algHomEquivEigenrow` turns characters into normalized class-indexed eigenrows; and
`TauCeti.ClassData.modularEigenrowEquiv` renumbers those into the numbered rows the executable
search returns.

## Main results

* `TauCeti.IsGoodDixonPrime.card_normalized_isClassEigenrow`: at a good Dixon prime the
  class-multiplication matrices have exactly one normalized common left eigenrow over `ZMod p` per
  conjugacy class of `G`.
* `TauCeti.ClassData.card_centralCharacterSearch`: the executable search returns
  `d.numClasses` rows over any coefficient field splitting the centre -- in particular it is
  nonempty (`TauCeti.ClassData.centralCharacterSearch_nonempty`) -- and
  `TauCeti.ClassData.card_centralCharacterSearch_of_isGoodDixonPrime` reads that off a good Dixon
  prime.
## Implementation notes

The general results are stated over an arbitrary finite coefficient field `F` with the splitting of
the centre as an explicit hypothesis, rather than over `ZMod p` with a good Dixon prime: the
splitting is the only thing the count uses, and stating it that way keeps the argument free of the
arithmetic conditions in `TauCeti.IsGoodDixonPrime`, which enter only through
`TauCeti.ClassData.card_centralCharacterSearch_of_isGoodDixonPrime`.

## References

This is the cardinality result Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
asks of "The good-prime structure theorem": that the reduced class-multiplication matrices have
exactly `r` distinct algebra homomorphisms, so that the eigenvector search terminates in
one-dimensional common eigenspaces.

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### The count at a good Dixon prime -/

namespace IsGoodDixonPrime

variable {p : ℕ}

/-- **At a good Dixon prime there is one normalized common left eigenrow per conjugacy class.**
This is the good-prime structure theorem
`TauCeti.IsGoodDixonPrime.nonempty_center_algEquiv_conjClasses` read through the identification of
the normalized common left eigenrows with the characters of the centre.

It is the modular counterpart of `TauCeti.card_normalized_isClassEigenrow`, which counts the
eigenrows over an algebraically closed field; the point of the Burnside--Dixon--Schneider algorithm
is that the count survives the passage to the small field `ZMod p`, where the eigenrows can actually
be searched for. -/
theorem card_normalized_isClassEigenrow (hp : IsGoodDixonPrime G p) :
    Nat.card {v : ConjClasses G → ZMod p //
        v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v} = Nat.card (ConjClasses G) := by
  have := hp.fact_prime
  exact card_normalized_isClassEigenrow_of_nonempty_center_algEquiv
    hp.nonempty_center_algEquiv_conjClasses

end IsGoodDixonPrime

/-! ### The count for the executable search -/

namespace ClassData

variable (d : ClassData G) {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The executable search returns one row per conjugacy class**, as an explicit enumeration of its
output by the conjugacy classes, whenever the coefficient field splits the centre of `F[G]`. -/
theorem nonempty_conjClasses_equiv_centralCharacterSearch
    (h : Nonempty (Subalgebra.center F (MonoidAlgebra F G) ≃ₐ[F] (ConjClasses G → F))) :
    Nonempty (ConjClasses G ≃
      {a : Fin d.numClasses → F // a ∈ d.centralCharacterSearch}) :=
  (nonempty_conjClasses_equiv_normalized_isClassEigenrow h).map fun e =>
    e.trans (d.modularEigenrowEquiv.symm.trans
      (Equiv.subtypeEquivRight fun _ => d.mem_centralCharacterSearch.symm))

/-- **The executable central-character search returns exactly `r` rows**, `r` the number of
conjugacy classes, over any coefficient field splitting the centre of `F[G]`.

Together with `TauCeti.ClassData.mem_centralCharacterSearch`, which says that every returned row is
a normalized common left eigenrow, this is what tells the Burnside--Dixon--Schneider algorithm that
the search has found *all* the central characters: the rows it returns are central characters, and
there are as many of them as there are irreducible representations to account for. -/
theorem card_centralCharacterSearch
    (h : Nonempty (Subalgebra.center F (MonoidAlgebra F G) ≃ₐ[F] (ConjClasses G → F))) :
    (d.centralCharacterSearch (F := F)).card = d.numClasses := by
  rw [← Nat.card_eq_finsetCard,
    ← Nat.card_congr (d.nonempty_conjClasses_equiv_centralCharacterSearch h).some,
    ← d.numClasses_eq_card_conjClasses]

/-- **The executable central-character search never comes back empty** over a coefficient field
splitting the centre: a group has at least one conjugacy class, hence at least one central
character, and the search finds it. -/
theorem centralCharacterSearch_nonempty
    (h : Nonempty (Subalgebra.center F (MonoidAlgebra F G) ≃ₐ[F] (ConjClasses G → F))) :
    (d.centralCharacterSearch (F := F)).Nonempty := by
  rw [← Finset.card_pos, d.card_centralCharacterSearch h, d.numClasses_eq_card_conjClasses]
  exact Nat.card_pos

/-- **The executable central-character search over `ZMod p` returns exactly `r` rows at a good
Dixon prime**, the form in which the modular phase of the Burnside--Dixon--Schneider algorithm
consumes the count. -/
theorem card_centralCharacterSearch_of_isGoodDixonPrime {p : ℕ} [Fact p.Prime]
    (hp : IsGoodDixonPrime G p) :
    (d.centralCharacterSearch (F := ZMod p)).card = d.numClasses :=
  d.card_centralCharacterSearch hp.nonempty_center_algEquiv_conjClasses

end ClassData

end TauCeti
