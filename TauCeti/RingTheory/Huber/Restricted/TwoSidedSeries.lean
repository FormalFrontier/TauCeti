/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter

/-!
# Two-sided restricted series `A⟨X, X⁻¹⟩`

Wedhorn's Example 6.39 introduces, for a Tate ring `A`, the ring of formal series
`∑_{n ∈ ℤ} aₙ Xⁿ` whose coefficients satisfy a convergence condition: for every neighbourhood `U`
of zero, all but finitely many `aₙ` lie in `U`. This module builds the underlying coefficient
object — the `A`-module of such two-sided families — together with its coefficients and
extensionality.

The condition is exactly the one `TauCeti.Huber.IsRestricted` already expresses for the
one-sided series `A⟨X₁, …, Xₖ⟩`: a coefficient family tending to `0` along the cofinite filter,
i.e. Mathlib's `Filter.ZeroAtFilter` at `Filter.cofinite`. Nothing in that predicate refers to the
shape of the index set, so the two-sided object is the same notion indexed by `ℤ` rather than by
`Fin k →₀ ℕ`, and is built from the same Mathlib primitive
(`Filter.zeroAtFilterSubmodule`) that `TauCeti.Huber.restrictedMvPowerSeriesSubmodule` is built
from.

## Why this file is not called `Laurent`

Two neighbouring modules already use that word for different objects, and a third meaning would be
a placement hazard:

* `TauCeti.RingTheory.Huber.Restricted.Laurent` is Wedhorn's **Example 6.38** — the *Laurent
  rational subsets* `{|f| ≤ 1}` and `{|f| ≥ 1}`, whose coordinate rings `A⟨X⟩/(f - X)` and
  `A⟨X⟩/(1 - f X)` are quotients of the **one-sided** `A⟨X⟩`. Those are the two *pieces* of the
  cover whose *overlap* is the ring this file serves.
* `TauCeti.RingTheory.Huber.LaurentSeries` is the formal Laurent series **field** `K⸨X⸩` over a
  *field* `K` with the `X`-adic topology. That is a different object in three ways: its base is a
  field rather than an arbitrary Tate ring, its series have only finitely many negative terms, and
  its topology is `X`-adic rather than coefficientwise. It is **not** reusable here; the
  distinguishing feature is precisely the convergence condition on the coefficients.

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule`: the `A`-module of two-sided restricted families,
  the coefficient object underlying `A⟨X, X⁻¹⟩`.

## Main results

* `TauCeti.Huber.mem_twoSidedRestrictedSubmodule_iff_finite_notMem`: Example 6.39's defining
  condition verbatim — membership is the finiteness condition on open additive subgroups. It is
  the `ℤ` case of `NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem`, which is
  stated for an arbitrary index type in
  `TauCeti/Topology/Algebra/Nonarchimedean/ZeroAtFilter.lean` because neither direction of it
  looks at the index set or at series.
* `TauCeti.Huber.twoSidedRestrictedSubmodule_ext`: coefficientwise extensionality.

## Implementation notes

Only the additive and `A`-module structure is built here. The **ring** structure is deliberately
absent: the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ` is a *finite* sum for one-sided
series — which is what `TauCeti.Huber.IsRestricted.mul` exploits, through
`MvPowerSeries.coeff_mul` over a finite antidiagonal — but over `ℤ` that antidiagonal is infinite,
so multiplication needs a summability argument in a complete ring rather than a rearrangement of a
finite sum. That is separate work and does not belong to this rung.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open Filter Topology

namespace TauCeti.Huber

section Submodule

variable (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]
  [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **The two-sided restricted `M`-valued families**: the `A`-module of families `ℤ → M` tending
to `0` along the cofinite filter, i.e. those whose coefficients leave every neighbourhood of zero
finitely often.

At `M = A` this is the coefficient object of Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). It is only the
*coefficients*: no ring structure is defined here, so this is not yet that algebra — see the
implementation notes.

This is `TauCeti.Huber.restrictedMvPowerSeriesSubmodule`'s condition at the index set `ℤ`, and is
built from the same Mathlib primitive. -/
def twoSidedRestrictedSubmodule : Submodule A (ℤ → M) :=
  Filter.zeroAtFilterSubmodule A (Filter.cofinite : Filter ℤ)

variable {A M}

/-- Membership is the convergence condition on the coefficient family. -/
@[simp]
theorem mem_twoSidedRestrictedSubmodule {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔ ZeroAtFilter cofinite f := (Iff.rfl)

/-- **Coefficientwise extensionality**: two members of the submodule that agree at every index are
equal. This is subtype-and-function extensionality, nothing more — in particular it does *not* say
that a coefficient family is recovered from any sum it represents, which would need an evaluation
map that does not exist until there is a ring structure. -/
@[ext]
theorem twoSidedRestrictedSubmodule_ext {f g : twoSidedRestrictedSubmodule A M}
    (h : ∀ n, (f : ℤ → M) n = (g : ℤ → M) n) : f = g :=
  Subtype.ext (funext h)

end Submodule

section WedhornCriterion

variable {A M : Type*} [Semiring A] [AddCommGroup M] [TopologicalSpace M] [Module A M]
  [ContinuousConstSMul A M] [NonarchimedeanAddGroup M]

/-- **The membership criterion in Wedhorn's form**: a family lies in the submodule exactly when,
for every open additive subgroup, only finitely many of its members lie outside. At `M = A` this
is Example 6.39's defining condition on the coefficients, verbatim.

Deliberately **not** `@[simp]`: `mem_twoSidedRestrictedSubmodule` is already `@[simp]` and rewrites
this left-hand side to `ZeroAtFilter cofinite f`, so tagging this one too fails the `simpNF` linter
— simp reaches the membership unfolding first and this lemma can never fire. The `@[simp]` stays on
the membership lemma, matching the one-sided `mem_restrictedMvPowerSeriesSubmodule`. -/
theorem mem_twoSidedRestrictedSubmodule_iff_finite_notMem {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔
      ∀ W : OpenAddSubgroup M, {n | f n ∉ (W : Set M)}.Finite := by
  rw [mem_twoSidedRestrictedSubmodule]
  exact NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem

end WedhornCriterion

end TauCeti.Huber
