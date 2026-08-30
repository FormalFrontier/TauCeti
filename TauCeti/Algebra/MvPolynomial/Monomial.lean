/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Multiset

/-!
# A monomial as a product of variables

Multiplying together a multiset of variables, one factor per element, gives the monomial whose
exponent vector is the multiplicity function of the multiset: `TauCeti.prod_map_X_eq_monomial`.
Mathlib's `MvPolynomial.prod_X_pow_eq_monomial` says the same thing for a product indexed by the
support of an exponent vector; this is the multiset-indexed form, which is how the monomials of
`MvPolynomial.hsymm` and `MvPolynomial.msymm` are written.

## Main results

* `TauCeti.prod_map_X_eq_monomial`: the product of a multiset of variables is the monomial with
  coefficient `1` at the multiplicity function of the multiset.
-/

public section

namespace TauCeti

open MvPolynomial

/-- **A monomial is the product of the variables it uses, with multiplicity.**  This is the form
in which the monomials of `MvPolynomial.hsymm` and `MvPolynomial.msymm` are written. -/
theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

end TauCeti
