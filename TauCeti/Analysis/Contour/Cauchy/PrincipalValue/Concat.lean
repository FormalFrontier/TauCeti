/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On

/-!
# Concatenating set-level Cauchy principal values

`HasCauchyPV` binds its finite excision set **existentially**, which is the right interface for
consumers but is too weak to concatenate: two principal values along adjacent subcurves may be
witnessed by *different* excision sets, and passing to their union changes the excised integrand.
Recovering the union form needs extra control that `HasCauchyPV` does not supply — the added
points being met on a null set of parameters is one sufficient condition, though not a necessary
one, since enlargement is also harmless wherever the integrand's contribution already vanishes.

This file therefore works with the prescribed-witness form `HasCauchyPVWith` of
`PrincipalValue/On.lean`, in which the excision set is an explicit parameter, and concatenates
there. Adjacent subcurves sharing one excision set
add (`HasCauchyPVWith.concat`), and the complementary piece can be subtracted off
(`HasCauchyPVWith.sub_right`) — the direction that splits a principal value along a closed contour
into its constituent arcs. Both are the set-level analogues of `HasCauchyPVAt.concat`, whose single
excised point is automatically shared.

## Main results

* `TauCeti.Contour.HasCauchyPVWith.concat` — principal values along `[a, b]` and `[b, c]` sharing
  an excision set add to the one along `[a, c]`.
* `TauCeti.Contour.HasCauchyPVWith.sub_right` — the converse split: removing the `[b, c]` piece
  from the `[a, c]` principal value leaves the `[a, b]` one.
-/

public section

open Filter Topology MeasureTheory

namespace TauCeti.Contour

/-- **Concatenation.** Principal values along the adjacent subcurves `[a, b]` and `[b, c]` that
excise the *same* finite set add to the principal value along `[a, c]`. As for
`HasCauchyPVAt.concat`, the integrability of the excised integrand across `[a, c]` and the
additivity of the integral both follow from the two given principal values, so no ordering or
separate integrability hypothesis is needed. -/
theorem HasCauchyPVWith.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPVWith γ a b f S L₁) (h_bc : HasCauchyPVWith γ b c f S L₂) :
    HasCauchyPVWith γ a c f S (L₁ + L₂) := by
  rw [hasCauchyPVWith_iff] at h_ab h_bc ⊢
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ab.1, h_bc.1] with ε hab hbc
    exact hab.trans hbc
  · refine Filter.Tendsto.congr' ?_ (h_ab.2.add h_bc.2)
    filter_upwards [h_ab.1, h_bc.1] with ε hab hbc
    exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- **Splitting off the far piece.** If the principal value along `[a, c]` and the one along
`[b, c]` excise the same finite set, then their difference is the principal value along `[a, b]`.
This is the direction that decomposes a contour: knowing the whole and one arc gives the rest. -/
theorem HasCauchyPVWith.sub_right {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {L L₂ : ℂ}
    (h_ac : HasCauchyPVWith γ a c f S L) (h_bc : HasCauchyPVWith γ b c f S L₂) :
    HasCauchyPVWith γ a b f S (L - L₂) := by
  rw [hasCauchyPVWith_iff] at h_ac h_bc ⊢
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ac.1, h_bc.1] with ε hac hbc
    exact hac.trans hbc.symm
  · refine Filter.Tendsto.congr' ?_ (h_ac.2.sub h_bc.2)
    filter_upwards [h_ac.1, h_bc.1] with ε hac hbc
    simpa using
      intervalIntegral.integral_interval_sub_interval_comm hac hbc (hac.trans hbc.symm)

end TauCeti.Contour

end
