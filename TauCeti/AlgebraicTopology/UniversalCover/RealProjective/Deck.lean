/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic

/-!
# The deck group of the antipodal cover of real projective space

The unit sphere `Sⁿ` covers real projective `n`-space as the quotient by the antipodal
action of `ℤˣ`; `TauCeti.RealProjectiveSpace.isQuotientCoveringMap_mk` records this. This
file identifies the deck transformation group of that cover.

The antipodal map is always a deck transformation, and it is never the identity because no
unit vector is its own negative. For `1 ≤ n` the sphere is connected, so a deck
transformation is determined by its value at a single point; the deck group is then exactly
the two-element acting group:

  `Deck (mk n) ≃* ℤˣ`.

Both facts come from `TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`, which identifies the
acting group of a quotient covering map with connected total space as its deck group. The
regularity of the antipodal cover needs no connectedness hypothesis.

For `n = 0` the sphere is the two-point space `S⁰`, which is disconnected, so the argument
does not apply; the statements that need it carry the hypothesis `1 ≤ n` explicitly.

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, the computation
of `π₁(RPⁿ)`: for a regular cover the deck group is a quotient of the fundamental group of
the base, so knowing that the antipodal cover is regular with deck group of order two is the
covering-space input to that computation.

## Main declarations

* `TauCeti.RealProjectiveSpace.antipode`: the antipodal map as a deck transformation of the
  cover `Sⁿ → RPⁿ`.
* `TauCeti.RealProjectiveSpace.antipode_ne_one`: it is not the identity.
* `TauCeti.RealProjectiveSpace.deckMulEquiv`: for `1 ≤ n`, the deck group of the antipodal
  cover is `ℤˣ`.
* `TauCeti.RealProjectiveSpace.eq_one_or_eq_antipode`: for `1 ≤ n`, a deck transformation of
  the antipodal cover is the identity or the antipodal map.
* `TauCeti.RealProjectiveSpace.card_deck`: for `1 ≤ n`, the deck group has two elements.
* `TauCeti.RealProjectiveSpace.isRegular_mk`: the antipodal cover is regular.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

open Metric Deck

noncomputable section

variable (n : ℕ)

/-- The unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` is nonempty. -/
instance instNonemptySphere :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- The unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` is connected once `1 ≤ n`, that is,
from the circle `S¹` on. This is the standing hypothesis behind the identification of the
deck group of the antipodal cover. -/
theorem connectedSpace_sphere (hn : 1 ≤ n) :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  refine Subtype.connectedSpace (isConnected_sphere ?_ 0 zero_le_one)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
  omega

/-- The antipodal map, as a deck transformation of the cover `Sⁿ → RPⁿ`. It is translation by
the nontrivial integer unit. -/
def antipode : Deck (mk n) :=
  IsQuotientCoveringMap.toDeckHom (isQuotientCoveringMap_mk n) (-1)

/-- On points, the antipodal deck transformation negates. -/
@[simp]
theorem antipode_apply (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (antipode n).1 x = -x := by
  simp [antipode]

/-- On points, the inverse of the antipodal deck transformation also negates. -/
@[simp]
theorem antipode_symm_apply (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (antipode n).1.symm x = -x := by
  simp [antipode]

/-- The antipodal deck transformation is an involution. -/
@[simp]
theorem antipode_mul_self : antipode n * antipode n = 1 := by
  rw [antipode, ← map_mul]
  simp

/-- The antipodal deck transformation is its own inverse. -/
@[simp]
theorem inv_antipode : (antipode n)⁻¹ = antipode n :=
  inv_eq_of_mul_eq_one_right (antipode_mul_self n)

/-- The antipodal deck transformation is not the identity: the nontrivial integer unit is not
trivial, and translation is injective because the antipodal action is free. -/
@[simp]
theorem antipode_ne_one : antipode n ≠ 1 := by
  intro hone
  rw [antipode, ← map_one (IsQuotientCoveringMap.toDeckHom (isQuotientCoveringMap_mk n))]
    at hone
  exact absurd (IsQuotientCoveringMap.toDeckHom_injective _ hone) (by decide)

/-- **The deck group of the antipodal cover `Sⁿ → RPⁿ` is the two-element group `ℤˣ`**, for
`1 ≤ n`. The isomorphism sends an integer unit to the corresponding antipodal translation. -/
def deckMulEquiv (hn : 1 ≤ n) : ℤˣ ≃* Deck (mk n) :=
  letI := connectedSpace_sphere n hn
  IsQuotientCoveringMap.deckMulEquiv (isQuotientCoveringMap_mk n)

/-- On points, the deck-group isomorphism is the antipodal action. -/
@[simp]
theorem deckMulEquiv_apply (hn : 1 ≤ n) (u : ℤˣ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (deckMulEquiv n hn u).1 x = u • x := by
  letI := connectedSpace_sphere n hn
  rw [deckMulEquiv, IsQuotientCoveringMap.deckMulEquiv_apply]

/-- On points, the inverse of the deck-group isomorphism recovers the given deck
transformation. -/
@[simp]
theorem deckMulEquiv_symm_apply (hn : 1 ≤ n) (φ : Deck (mk n))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (deckMulEquiv n hn).symm φ • x = φ.1 x := by
  letI := connectedSpace_sphere n hn
  rw [deckMulEquiv, IsQuotientCoveringMap.deckMulEquiv_symm_apply]

/-- The deck-group isomorphism sends the nontrivial integer unit to the antipodal map. -/
@[simp]
theorem deckMulEquiv_neg_one (hn : 1 ≤ n) : deckMulEquiv n hn (-1) = antipode n :=
  Subtype.ext (Homeomorph.ext fun x => by simp)

/-- For `1 ≤ n`, a deck transformation of the antipodal cover is either the identity or the
antipodal map. -/
theorem eq_one_or_eq_antipode (hn : 1 ≤ n) (φ : Deck (mk n)) :
    φ = 1 ∨ φ = antipode n := by
  obtain ⟨u, rfl⟩ := (deckMulEquiv n hn).surjective φ
  obtain rfl | rfl := Int.units_eq_one_or u
  · exact Or.inl (map_one _)
  · exact Or.inr (deckMulEquiv_neg_one n hn)

/-- For `1 ≤ n`, the deck group of the antipodal cover has exactly two elements. -/
theorem card_deck (hn : 1 ≤ n) : Nat.card (Deck (mk n)) = 2 := by
  rw [← Nat.card_congr (deckMulEquiv n hn).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

/-- The antipodal cover `Sⁿ → RPⁿ` is regular: its deck group acts transitively on every
fibre. Unlike the identification of the deck group, this needs no connectedness. -/
theorem isRegular_mk : IsRegular (mk n) :=
  IsQuotientCoveringMap.isRegular (isQuotientCoveringMap_mk n)

end

end RealProjectiveSpace

end TauCeti
