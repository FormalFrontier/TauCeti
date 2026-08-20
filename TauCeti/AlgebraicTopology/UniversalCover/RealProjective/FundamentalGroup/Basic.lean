/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Deck

/-!
# The fundamental group of real projective space

For `2 ≤ n`, real projective `n`-space `RPⁿ` has fundamental group isomorphic to `ℤˣ` via the
two-sheeted antipodal quotient `mk n`.

The antipodal cover is a regular covering map with deck group `ℤˣ`, and the covering sphere `Sⁿ`
is simply connected for `2 ≤ n` by `TauCeti.simplyConnectedSpace_euclideanSphere`. The
regular-cover comparison `TauCeti.Deck.IsRegular.fundamentalGroupEquiv` therefore identifies the
fundamental group of `RPⁿ` at any basepoint with the opposite of the deck group. Since `ℤˣ` is
commutative, the opposite drops out, yielding

  `FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ`.

As consequences, `RPⁿ` (for `2 ≤ n`) has a fundamental group of order 2, a nontrivial fundamental
group, is not simply connected, not contractible, and not homeomorphic to `ℝ`.

## Main declarations

* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv`: for `2 ≤ n`,
  `FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ` for any basepoint `x`
  with a chosen lift `e`.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv_apply_eq_iff`: characterization of the
  isomorphism on monodromy.
* `TauCeti.RealProjectiveSpace.monodromy_fundamentalGroupMulEquiv_symm`: inverse equivalence on
  monodromy.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv_eq_one_iff`: loop class maps to `1`
  iff monodromy fixes lift.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquivAt`: basepoint-unconscious version
  for any `x`.
* `TauCeti.RealProjectiveSpace.card_fundamentalGroup`:
  `Nat.card (FundamentalGroup (RealProjectiveSpace n) x) = 2`.
* `TauCeti.RealProjectiveSpace.nontrivial_fundamentalGroup`: the fundamental group is nontrivial.
* `TauCeti.RealProjectiveSpace.not_simplyConnectedSpace`: `RPⁿ` is not simply connected.
* `TauCeti.RealProjectiveSpace.not_contractibleSpace`: `RPⁿ` is not contractible.
* `TauCeti.RealProjectiveSpace.isEmpty_homeomorph_real`: `RPⁿ` is not homeomorphic to `ℝ`.

## References

This is the deck-to-fundamental-group part of the `π₁(RPⁿ)` milestone in
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13. It consumes
`TauCeti.RealProjectiveSpace.isQuotientCoveringMap_mk` and
`TauCeti.RealProjectiveSpace.deckMulEquiv` from
`TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Deck`, the simple connectivity of the
covering sphere from `TauCeti.AlgebraicTopology.Sphere.SimplyConnected`, and the regular-cover
comparison of Stage 1. The equivalence construction and monodromy proof pattern are adapted from
`TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup` for the antipodal cover.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

open Metric Deck

noncomputable section

variable (n : ℕ)

/-- **The fundamental group of real projective space `RPⁿ` (for `2 ≤ n`) is isomorphic to `ℤˣ`**,
for any basepoint `x` with a chosen lift `e` in the sphere:
`FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ`. -/
def fundamentalGroupMulEquiv (hn : 2 ≤ n)
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x}) :
    FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ :=
  haveI := simplyConnectedSpace_euclideanSphere hn
  (Deck.IsRegular.fundamentalGroupEquiv (isRegular_mk n) (isCoveringMap_mk n) e).trans
    ((MulEquiv.op (deckMulEquiv n (by omega)).symm).trans
      (MulOpposite.opMulEquiv (M := ℤˣ)).symm)

/-- Characterization of the element of `ℤˣ` assigned by `fundamentalGroupMulEquiv`: a loop
class `γ` maps to `u : ℤˣ` exactly when its monodromy translate of the chosen lift `e` is
`u • (e : sphere _ 1)`. -/
@[simp]
lemma fundamentalGroupMulEquiv_apply_eq_iff (hn : 2 ≤ n)
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x})
    (γ : FundamentalGroup (RealProjectiveSpace n) x) (u : ℤˣ) :
    fundamentalGroupMulEquiv n hn e γ = u ↔
      ((isCoveringMap_mk n).monodromy γ e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
        u • (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have := simplyConnectedSpace_euclideanSphere hn
  let F := Deck.IsRegular.fundamentalGroupEquiv (isRegular_mk n) (isCoveringMap_mk n) e
  let T := (MulEquiv.op (deckMulEquiv n (by omega)).symm).trans
    (MulOpposite.opMulEquiv (M := ℤˣ)).symm
  have hT (g : (Deck (mk n))ᵐᵒᵖ) : T g = u ↔ g = MulOpposite.op (deckMulEquiv n (by omega) u) := by
    rw [T.eq_symm_apply.symm]
    simp [T]
  calc
    fundamentalGroupMulEquiv n hn e γ = u ↔ T (F γ) = u := by
      simp only [fundamentalGroupMulEquiv, F, T, MulEquiv.trans_apply]
    _ ↔ F γ = MulOpposite.op (deckMulEquiv n (by omega) u) := hT (F γ)
    _ ↔ ((MulOpposite.op (deckMulEquiv n (by omega) u)).unop •
          (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
            (isCoveringMap_mk n).monodromy γ e :=
      Deck.IsRegular.fundamentalGroupEquiv_apply_eq_iff (isRegular_mk n) (isCoveringMap_mk n) e γ _
    _ ↔ ((isCoveringMap_mk n).monodromy γ e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
          u • (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
      simp [Deck.smul_eq_apply, eq_comm]

/-- The inverse equivalence sends an integer unit `u` to the loop class whose monodromy
translates the chosen lift by `u`. -/
@[simp]
lemma monodromy_fundamentalGroupMulEquiv_symm (hn : 2 ≤ n)
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x}) (u : ℤˣ) :
    ((isCoveringMap_mk n).monodromy ((fundamentalGroupMulEquiv n hn e).symm u) e :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
        u • (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  exact (fundamentalGroupMulEquiv_apply_eq_iff n hn e
    ((fundamentalGroupMulEquiv n hn e).symm u) u).1
      (MulEquiv.apply_symm_apply _ _)

/-- A loop class maps to `1` under the fundamental group equivalence exactly when its monodromy
fixes the chosen lift. -/
lemma fundamentalGroupMulEquiv_eq_one_iff (hn : 2 ≤ n)
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x})
    (γ : FundamentalGroup (RealProjectiveSpace n) x) :
    fundamentalGroupMulEquiv n hn e γ = 1 ↔
      (isCoveringMap_mk n).monodromy γ e = e := by
  rw [fundamentalGroupMulEquiv_apply_eq_iff]
  simpa using (Iff.symm Subtype.ext_iff :
    (((isCoveringMap_mk n).monodromy γ e :
          sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
        (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ↔
      (isCoveringMap_mk n).monodromy γ e = e))

/-- **The fundamental group of real projective space `RPⁿ` (for `2 ≤ n`) is isomorphic to `ℤˣ`
for any basepoint `x`**: `FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ`. -/
def fundamentalGroupMulEquivAt (hn : 2 ≤ n)
    (x : RealProjectiveSpace n) :
    FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ :=
  let h := mk_surjective n x
  fundamentalGroupMulEquiv n hn ⟨h.choose, Set.mem_singleton_iff.mpr h.choose_spec⟩

/-- For `2 ≤ n`, the fundamental group of `RPⁿ` has
exactly two elements. -/
theorem card_fundamentalGroup (hn : 2 ≤ n)
    (x : RealProjectiveSpace n) :
    Nat.card (FundamentalGroup (RealProjectiveSpace n) x) = 2 := by
  rw [Nat.card_congr (fundamentalGroupMulEquivAt n hn x).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

/-- For `2 ≤ n`, the fundamental group of `RPⁿ` is
nontrivial. -/
theorem nontrivial_fundamentalGroup (hn : 2 ≤ n)
    (x : RealProjectiveSpace n) :
    Nontrivial (FundamentalGroup (RealProjectiveSpace n) x) := by
  have hunit : Nontrivial ℤˣ := ⟨(1 : ℤˣ), (-1 : ℤˣ), by decide⟩
  exact @Equiv.nontrivial _ _ (fundamentalGroupMulEquivAt n hn x).toEquiv hunit

/-- For `2 ≤ n`, real projective space `RPⁿ` is not simply connected. -/
theorem not_simplyConnectedSpace (hn : 2 ≤ n)
 :
    ¬ SimplyConnectedSpace (RealProjectiveSpace n) := by
  let x : RealProjectiveSpace n := mk n (instNonemptySphere n).some
  have := nontrivial_fundamentalGroup n hn x
  exact not_simplyConnectedSpace_of_nontrivial_fundamentalGroup x

/-- For `2 ≤ n`, real projective space `RPⁿ` is not contractible. -/
theorem not_contractibleSpace (hn : 2 ≤ n)
 :
    ¬ ContractibleSpace (RealProjectiveSpace n) :=
  not_contractibleSpace_of_not_simplyConnectedSpace (not_simplyConnectedSpace n hn)

/-- For `2 ≤ n`, real projective space `RPⁿ` is not homeomorphic to `ℝ`. -/
theorem isEmpty_homeomorph_real (hn : 2 ≤ n)
 :
    IsEmpty (RealProjectiveSpace n ≃ₜ ℝ) :=
  isEmpty_homeomorph_real_of_not_simplyConnectedSpace (not_simplyConnectedSpace n hn)

end

end RealProjectiveSpace

end TauCeti
