/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PolarPart.Decomposition

/-!
# Decomposition at finitely many simple poles

A meromorphic function whose poles in a finite set `S` have order at most one splits, away from
`S`, as a function holomorphic on the ambient open set plus the sum of its elementary principal
parts

`∑ s ∈ S, residue f s / (z - s)`.

This is the simple-pole decomposition from Layer 2 of the contour-integration roadmap. The general
canonical Laurent decomposition is already provided by `PolarPartDecomposition.ofMeromorphic`.
Here the order bound collapses every finite Laurent tail to its order-`(-1)` coefficient, which is
the residue.

## Main results

* `meromorphicPolarOrderAt_le_one_iff` identifies “polar order at most one” with the
  `meromorphicOrderAt` condition `-1 ≤ meromorphicOrderAt f s`.
* `PolarPartDecomposition.polarPart_eq_residue_div_of_order_le_one` collapses an abstract polar
  part of order at most one to its residue term.
* `PolarPartDecomposition.f_eq_analyticRemainder_add_residue_div` specializes a bundled
  decomposition pointwise.
* `exists_simplePoleDecomposition` gives the textbook existence statement: a differentiable
  remainder on `U` and an explicit sum of simple principal parts off `S`.

## Provenance

The target corresponds to `simple_poles_decomposition` in the AINTLIB `LeanModularForms`
development. The proof here is a direct specialization of Tau Ceti's canonical
`PolarPartDecomposition`; no external code is copied.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- A polar part of order at most one is its residue divided by the simple factor. For order zero,
both sides vanish; for order one, the unique Laurent coefficient is the residue. -/
theorem polarPart_eq_residue_div_of_order_le_one
    (decomp : PolarPartDecomposition f S U) (s : S) (horder : decomp.order s ≤ 1) (z : ℂ) :
    decomp.polarPart s z = residue f s / (z - (s : ℂ)) := by
  rw [decomp.polarPart_eq, decomp.residue_eq]
  by_cases hpos : 0 < decomp.order s
  · rw [dif_pos hpos]
    have huniv : (Finset.univ : Finset (Fin (decomp.order s))) = {⟨0, hpos⟩} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      apply Fin.ext
      omega
    rw [huniv, Finset.sum_singleton]
    simp
  · rw [dif_neg hpos, zero_div]
    apply Finset.sum_eq_zero
    intro k _
    exact (hpos (Nat.zero_lt_of_lt k.isLt)).elim

/-- Pointwise simple-pole form of a polar-part decomposition. If every bundled polar order is at
most one, then off `S` the function is its analytic remainder plus the sum of the residue terms. -/
theorem f_eq_analyticRemainder_add_residue_div
    (decomp : PolarPartDecomposition f S U) (horder : ∀ s, decomp.order s ≤ 1)
    {z : ℂ} (hz : z ∈ U \ (↑S : Set ℂ)) :
    f z = decomp.analyticRemainder z + ∑ s ∈ S, residue f s / (z - s) := by
  calc
    f z = decomp.analyticRemainder z + ∑ s ∈ S.attach, decomp.polarPart s z :=
      decomp.f_eq z hz
    _ = decomp.analyticRemainder z + ∑ s ∈ S, residue f s / (z - s) := by
      congr 1
      calc
        ∑ s ∈ S.attach, decomp.polarPart s z =
            ∑ s ∈ S.attach, residue f (s : ℂ) / (z - (s : ℂ)) :=
          Finset.sum_congr rfl fun s _ =>
            decomp.polarPart_eq_residue_div_of_order_le_one s (horder s) z
        _ = ∑ s ∈ S, residue f s / (z - s) :=
          Finset.sum_attach S (fun s => residue f s / (z - s))

end PolarPartDecomposition

/-- **Simple-pole decomposition.** Let `U` be open and `S` finite. If `f` is differentiable on
`U \ S`, meromorphic at every point of `S`, and has at most a simple pole there, then there is a
function `g` differentiable throughout `U` such that, away from `S`,

`f z = g z + ∑ s ∈ S, residue f s / (z - s)`.

Points of `S` where `f` is analytic are allowed: their residue terms are zero. -/
theorem exists_simplePoleDecomposition {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (horder : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z ∈ U \ (↑S : Set ℂ),
        f z = g z + ∑ s ∈ S, residue f s / (z - s) := by
  let decomp := PolarPartDecomposition.ofMeromorphic hU hf hmero
  refine ⟨decomp.analyticRemainder, decomp.analyticRemainder_differentiableOn, fun z hz => ?_⟩
  refine decomp.f_eq_analyticRemainder_add_residue_div (z := z) ?_ hz
  intro s
  rw [PolarPartDecomposition.ofMeromorphic_order]
  exact meromorphicPolarOrderAt_le_one_iff.mpr (horder s s.2)

end TauCeti.Contour

end
