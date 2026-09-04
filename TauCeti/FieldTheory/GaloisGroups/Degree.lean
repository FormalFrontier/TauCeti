/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Coset.Card

/-!
# Degree of the root permutation representation

This file records the degree bookkeeping for the faithful permutation representation of the
Galois group of a polynomial. A separable polynomial has `natDegree` distinct roots in its
splitting field, so its intrinsic root set admits a numbering by `Fin p.natDegree`. No numbering
is chosen globally: the result is stated as a `Nonempty` equivalence, leaving later comparisons
with reference permutation groups to carry their chosen numbering explicitly.

The Galois action itself is faithful over every splitting extension. Consequently its image has
the same cardinality as the polynomial Galois group, and the Galois-group order divides the
factorial of the polynomial degree.

## Main results

* `TauCeti.nonempty_rootSet_splittingField_equiv_fin`: a separable polynomial's roots in its
  splitting field can be numbered by `Fin p.natDegree`.
* `TauCeti.natCard_galActionHom_range`: the faithful Galois image has the order of the polynomial
  Galois group.
* `TauCeti.natCard_gal_dvd_factorial_card_rootSet`: the Galois-group order divides the factorial
  of the number of distinct roots.
* `TauCeti.natCard_gal_dvd_factorial_natDegree`: the order of a polynomial's Galois group divides
  the factorial of its degree.

The proofs reuse Mathlib's `Polynomial.card_rootSet_eq_natDegree`,
`Polynomial.Gal.galActionHom_injective`, `MonoidHom.ofInjective`, and Lagrange's theorem. This is
the degree bookkeeping used by the orbit-to-factor dictionary and by low-degree label predicates.
-/

public section

namespace TauCeti

open Polynomial

universe u v

variable {F : Type u} [Field F]

/-! ## Numbering the roots -/

/-- A separable polynomial's roots in its splitting field admit a numbering by
`Fin p.natDegree`.

Only existence is recorded: later statements choose a numbering locally, so the intrinsic root
set is not equipped with a global order. -/
theorem nonempty_rootSet_splittingField_equiv_fin (p : F[X]) (hsep : p.Separable) :
    Nonempty (p.rootSet p.SplittingField ≃ Fin p.natDegree) := by
  let e := Fintype.equivFin (p.rootSet p.SplittingField)
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p)
  exact ⟨e.trans (finCongr hcard)⟩

/-! ## The faithful image -/

/-- The image of the Galois action on the roots in any splitting extension has the same order as
the polynomial Galois group. -/
theorem natCard_galActionHom_range (p : F[X]) (E : Type v) [Field E] [Algebra F E]
    [Fact ((p.map (algebraMap F E)).Splits)] :
    Nat.card (Polynomial.Gal.galActionHom p E).range = Nat.card p.Gal := by
  exact Nat.card_congr
    (MonoidHom.ofInjective (Polynomial.Gal.galActionHom_injective p E)).toEquiv.symm

/-- The order of the Galois group of a polynomial divides the factorial of the number of its
distinct roots in the splitting field, through the faithful root action. -/
theorem natCard_gal_dvd_factorial_card_rootSet (p : F[X]) :
    Nat.card p.Gal ∣ (Fintype.card (p.rootSet p.SplittingField)).factorial := by
  have : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  calc
    Nat.card p.Gal = Nat.card (Polynomial.Gal.galActionHom p p.SplittingField).range :=
      (natCard_galActionHom_range p p.SplittingField).symm
    _ ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
      Subgroup.card_subgroup_dvd_card _
    _ = (Fintype.card (p.rootSet p.SplittingField)).factorial := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card]

/-- The order of the Galois group of a polynomial divides the factorial of its degree, through
its faithful action on the distinct roots. -/
theorem natCard_gal_dvd_factorial_natDegree (p : F[X]) :
    Nat.card p.Gal ∣ p.natDegree.factorial := by
  exact (natCard_gal_dvd_factorial_card_rootSet p).trans
    (Nat.factorial_dvd_factorial <| by
      rw [Set.fintypeCard_eq_ncard]
      exact Polynomial.ncard_rootSet_le p p.SplittingField)

end TauCeti
