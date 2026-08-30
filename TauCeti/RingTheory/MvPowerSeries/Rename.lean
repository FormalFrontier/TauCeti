/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Renaming the variables of a multivariate power series

Two gaps in Mathlib's `rename` API, both about comparing a renaming with another operation on the
same series.

Substituting after renaming is the substitution along the renamed index: Mathlib has both
operations and the law that lets them be compared — `rename_eq_subst`, which says a renaming *is*
the substitution sending each variable to a variable — but not the comparison itself, which is
what a caller reindexing a series needs.

Reading the coefficient of a single-variable monomial through a renaming along an embedding is
likewise available only through `coeff_embDomain_rename`, which speaks about `Finsupp.embDomain`;
at one variable raised to an arbitrary power the `single (e i) n` spelling is the more usable one.

## Main results

* `MvPowerSeries.subst_rename`: substituting into `rename e p` reindexes the family, i.e. it is
  substituting `g ∘ e` into `p`.
* `MvPowerSeries.coeff_single_rename`: the coefficient of `rename e p` at the single-variable
  monomial `single (e i) n` is the coefficient of `p` at `single i n`, for any exponent `n`.

## Provenance

No external source: both statements are gaps in Mathlib's `MvPowerSeries` API and each proof is a
few steps of that same API. They are recorded here rather than inside their callers because they
carry no elliptic content.
-/

public section

namespace MvPowerSeries

open Filter Finsupp

variable {σ τ υ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- **A single-variable monomial's coefficient survives a renaming along an embedding**, for any
exponent `n`. Mathlib's `coeff_embDomain_rename` states this through `Finsupp.embDomain`; at one
variable the `single (e i) n` spelling is the one a caller meets. -/
@[simp]
theorem coeff_single_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (i : σ) (n : ℕ) :
    coeff (single (e i) n) (rename e p) = coeff (single i n) p := by
  rw [← embDomain_single, coeff_embDomain_rename]

end CommSemiring

section CommRing

variable [CommRing R]

/-- **Substituting into a renamed series reindexes the family**: `rename e p` followed by
substituting `g` is `p` with `g ∘ e` substituted.

Both hypotheses are the ones the two operations already carry: `rename` needs `e` to have finite
fibres (`TendstoCofinite`) for the renamed coefficients to be well defined, and `subst` needs
`HasSubst g`. Nothing is assumed about `e` beyond that — in particular it need not be injective,
since a collision merely substitutes the same series for two variables. -/
theorem subst_rename (e : σ → τ) [TendstoCofinite e] (p : MvPowerSeries σ R)
    {g : τ → MvPowerSeries υ R} (hg : HasSubst g) :
    (rename e p).subst g = p.subst (g ∘ e) := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hg]
  simp [subst_X hg, Function.comp_def]

end CommRing

end MvPowerSeries
