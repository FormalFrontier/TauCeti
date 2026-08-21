/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.BoundedAtCusp
public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Basic
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# Finite sums of rational slashes at the cusps

A slash is zero at `c` exactly when the original function is zero at `g • c`
(`OnePoint.IsZeroAt.smul_iff`), and for a **rational** `g` the point `g • c` is again a cusp of an
arithmetic subgroup (`IsCusp.smul_map_ratCast`). So a function vanishing, or bounded, at every
cusp keeps that property after any finite sum of rational slashes.

Nothing here is specific to Hecke operators: the index type is arbitrary and the matrices are
unconstrained apart from rationality. The Hecke sums are corollaries, obtained by supplying their
own index and representatives.

## Main results

* `OnePoint.isZeroAt_rat_slash`, `OnePoint.isBoundedAt_rat_slash`: a single rational slash
  inherits vanishing, resp. boundedness, at the cusps.
* `OnePoint.isZeroAt_sum_rat_slash`, `OnePoint.isBoundedAt_sum_rat_slash`: the same for a finite
  sum, obtained by closing the summand-wise statements under `OnePoint.IsZeroAt.sum` and
  `OnePoint.IsBoundedAt.sum` respectively.

## Provenance

No code is transcribed. The argument is the one the AINTLIB `LeanModularForms` project (Chris
Birkbeck, Apache-2.0) uses for its specific representative sum in
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` (`heckeT_p_ut_zero_at_cusps`, lines 62-70), where it is
open-coded per call site. Here it is stated once, for an arbitrary finite family of rational
matrices, so that each Hecke sum specialises it instead of repeating it.
-/

public section

namespace OnePoint

open UpperHalfPlane

open scoped MatrixGroups ModularForm

variable (k : ℤ) {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {ι : Type*} {f : ℍ → ℂ}
  {c : OnePoint ℝ}

/-- **A rational slash vanishes at every cusp** when the function does. The matrix is
unconstrained: only its rationality is used, via `IsCusp.smul_map_ratCast`. -/
lemma isZeroAt_rat_slash (g : GL (Fin 2) ℚ)
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsZeroAt f k) (hc : IsCusp c Γ) :
    c.IsZeroAt (f ∣[k] g) k := by
  rw [ModularForm.rat_slash]
  exact OnePoint.IsZeroAt.smul_iff.mp (hf _ (hc.smul_map_ratCast _))

/-- **A finite sum of rational slashes vanishes at every cusp** — the summand-wise statement
`isZeroAt_rat_slash` closed under `OnePoint.IsZeroAt.sum`. -/
lemma isZeroAt_sum_rat_slash (s : Finset ι) (g : ι → GL (Fin 2) ℚ)
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsZeroAt f k) (hc : IsCusp c Γ) :
    c.IsZeroAt (∑ i ∈ s, f ∣[k] g i) k :=
  OnePoint.IsZeroAt.sum fun i _ ↦ isZeroAt_rat_slash k (g i) hf hc

/-- **A rational slash is bounded at every cusp** when the function is. -/
lemma isBoundedAt_rat_slash (g : GL (Fin 2) ℚ)
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsBoundedAt f k) (hc : IsCusp c Γ) :
    c.IsBoundedAt (f ∣[k] g) k := by
  rw [ModularForm.rat_slash]
  exact OnePoint.IsBoundedAt.smul_iff.mp (hf _ (hc.smul_map_ratCast _))

/-- **A finite sum of rational slashes is bounded at every cusp** — the summand-wise statement
`isBoundedAt_rat_slash` closed under `OnePoint.IsBoundedAt.sum`. -/
lemma isBoundedAt_sum_rat_slash (s : Finset ι) (g : ι → GL (Fin 2) ℚ)
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsBoundedAt f k) (hc : IsCusp c Γ) :
    c.IsBoundedAt (∑ i ∈ s, f ∣[k] g i) k :=
  OnePoint.IsBoundedAt.sum fun i _ ↦ isBoundedAt_rat_slash k (g i) hf hc

end OnePoint

end
