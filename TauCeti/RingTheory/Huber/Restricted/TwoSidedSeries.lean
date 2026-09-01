/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Pi
public import TauCeti.Order.Filter.ZeroAndBoundedAtFilter
public import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter

/-!
# Two-sided restricted series `A⟨X, X⁻¹⟩`

Wedhorn's Example 6.39 introduces, for a Tate ring `A`, the ring of formal series
`∑_{n ∈ ℤ} aₙ Xⁿ` whose coefficients satisfy a convergence condition: for every neighbourhood `U`
of zero, all but finitely many `aₙ` lie in `U`. This module builds the underlying coefficient
object — the `A`-module of such two-sided families — together with its coefficients,
extensionality, and the decomposition of that module by degree.

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
* `TauCeti.Huber.twoSidedRestrictedSubmodule_eq_sup` and
  `TauCeti.Huber.disjoint_twoSidedRestricted_nonneg_neg`: **the degree decomposition and its
  directness** — `A⟨X, X⁻¹⟩` is the sum of its non-negative and negative parts, and that sum is
  direct. This is fact (i) of Wedhorn's Lemma 8.33 at the level of coefficients, and it is what
  the diagram chase there needs; the Example 6.39 universal property does not supply it.
* `TauCeti.Huber.twoSidedRestrictedSubmodule_eq_sup_compl` and
  `TauCeti.Huber.disjoint_twoSidedRestricted_compl`: the same decomposition and directness along
  an arbitrary set of degrees and its complement, of which the sign partition above is a special
  case. Nothing in either argument uses the order on `ℤ`, only that the two sets are
  complementary.
* `Filter.ZeroAtFilter.of_eventually_eq_or_eq_zero`: zeroing coefficients keeps a family
  restricted. Stated pointwise rather than for an indicator, so it carries no decidability
  hypothesis; it is what makes the decomposition land inside the submodule rather than merely
  inside `ℤ → M`.

## Implementation notes

Only the additive and `A`-module structure is built here. The **ring** structure is deliberately
absent: the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ` is a *finite* sum for one-sided
series — which is what `TauCeti.Huber.IsRestricted.mul` exploits, through
`MvPowerSeries.coeff_mul` over a finite antidiagonal — but over `ℤ` that antidiagonal is infinite,
so multiplication needs a summability argument in a complete ring rather than a rearrangement of a
finite sum. That is separate work and does not belong to this rung.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39 and §8.2.1,
  Lemma 8.33.
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

section DegreeSplit

variable (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]

variable {A M}

variable (A M) [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **The degree decomposition along any set of degrees and its complement.** A two-sided
restricted family is the sum of its part supported in `s` and its part supported in `sᶜ`. The
argument uses nothing about `s` beyond the two sets being complementary: the witnesses are the
two indicators of `f`, each restricted by `Filter.ZeroAtFilter.of_eventually_eq_or_eq_zero`, and
they add back to `f` by `Set.indicator_self_add_compl`. The sign partition of
`twoSidedRestrictedSubmodule_eq_sup` is the case `s = {n | 0 ≤ n}`. -/
theorem twoSidedRestrictedSubmodule_eq_sup_compl (s : Set ℤ) :
    twoSidedRestrictedSubmodule A M =
      (twoSidedRestrictedSubmodule A M ⊓
          Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M)) ⊔
        (twoSidedRestrictedSubmodule A M ⊓
          Submodule.pi s fun _ ↦ (⊥ : Submodule A M)) := by
  refine le_antisymm (fun f hf ↦ ?_) (sup_le inf_le_left inf_le_left)
  refine Submodule.mem_sup.mpr
    ⟨s.indicator f, ⟨?_, ?_⟩, sᶜ.indicator f, ⟨?_, ?_⟩, ?_⟩
  · exact hf.of_eventually_eq_or_eq_zero (.of_forall fun n ↦ by
      by_cases h : n ∈ s <;> simp [h])
  · intro n hn; simpa [Set.indicator_apply] using fun h ↦ absurd h (by simpa using hn)
  · exact hf.of_eventually_eq_or_eq_zero (.of_forall fun n ↦ by
      by_cases h : n ∈ sᶜ <;> simp [h])
  · intro n hn; simpa [Set.indicator_apply] using fun h ↦ absurd h (by simpa using hn)
  · exact Set.indicator_self_add_compl _ f

/-- **Wedhorn's degree decomposition, Lemma 8.33(i).** A two-sided restricted family is the sum of
its non-negative part and its negative part: `A⟨z, z⁻¹⟩ = A⟨z⟩ + z⁻¹A⟨z⁻¹⟩` at the level of
coefficients. This is `twoSidedRestrictedSubmodule_eq_sup_compl` at the sign partition, which is
where the restrictedness of each summand is established. -/
theorem twoSidedRestrictedSubmodule_eq_sup :
    twoSidedRestrictedSubmodule A M =
      (twoSidedRestrictedSubmodule A M ⊓
          Submodule.pi {n : ℤ | 0 ≤ n}ᶜ fun _ ↦ (⊥ : Submodule A M)) ⊔
        (twoSidedRestrictedSubmodule A M ⊓
          Submodule.pi {n : ℤ | n < 0}ᶜ fun _ ↦ (⊥ : Submodule A M)) := by
  have hcompl : {n : ℤ | n < 0}ᶜ = {n : ℤ | 0 ≤ n} := by ext n; simp
  rw [hcompl]
  exact twoSidedRestrictedSubmodule_eq_sup_compl A M {n : ℤ | 0 ≤ n}

/-- **The degree decomposition along any set of degrees is direct.** A family supported in `sᶜ`
and in `s` at once is zero, so the two summands of `twoSidedRestrictedSubmodule_eq_sup_compl`
meet in `⊥`. As with the decomposition itself, the argument uses nothing about `s` beyond the
two sets being complementary: the witness is `Submodule.disjoint_pi_compl_bot_of_disjoint` at
`Disjoint s sᶜ`. The sign partition of `disjoint_twoSidedRestricted_nonneg_neg` is the case
`s = {n | 0 ≤ n}`. -/
theorem disjoint_twoSidedRestricted_compl (s : Set ℤ) :
    Disjoint
      (twoSidedRestrictedSubmodule A M ⊓
        Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M))
      (twoSidedRestrictedSubmodule A M ⊓
        Submodule.pi s fun _ ↦ (⊥ : Submodule A M)) := by
  have h : Disjoint (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M))
      (Submodule.pi s fun _ ↦ (⊥ : Submodule A M)) := by
    have hs := Submodule.disjoint_pi_compl_bot_of_disjoint (A := A) (M := M)
      (disjoint_compl_right (a := s))
    rwa [compl_compl] at hs
  exact h.mono inf_le_right inf_le_right

/-- **The decomposition is direct.** A family supported in non-negative degrees and in negative
degrees at once is zero, so the two summands of `twoSidedRestrictedSubmodule_eq_sup` meet in `⊥`.
Together they exhibit `A⟨z, z⁻¹⟩` as the internal direct sum of the two half-line pieces. This is
`disjoint_twoSidedRestricted_compl` at the sign partition. -/
theorem disjoint_twoSidedRestricted_nonneg_neg :
    Disjoint
      (twoSidedRestrictedSubmodule A M ⊓
        Submodule.pi {n : ℤ | 0 ≤ n}ᶜ fun _ ↦ (⊥ : Submodule A M))
      (twoSidedRestrictedSubmodule A M ⊓
        Submodule.pi {n : ℤ | n < 0}ᶜ fun _ ↦ (⊥ : Submodule A M)) := by
  have hcompl : {n : ℤ | n < 0}ᶜ = {n : ℤ | 0 ≤ n} := by ext n; simp
  rw [hcompl]
  exact disjoint_twoSidedRestricted_compl A M {n : ℤ | 0 ≤ n}

end DegreeSplit

end TauCeti.Huber
