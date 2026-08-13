/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Algebra.Group.Equiv.Opposite
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Opposite
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Deck

/-!
# The fundamental group of real projective space `RPⁿ` is `ℤˣ`

For `1 ≤ n`, real projective `n`-space `RPⁿ` is covered by the unit sphere `Sⁿ` via the two-sheeted
antipodal quotient `mk n`. The antipodal cover is a regular covering map with deck group `ℤˣ`.
For `2 ≤ n`, the covering sphere `Sⁿ` is simply connected. Using the regular-cover comparison
`TauCeti.Deck.IsRegular.fundamentalGroupEquiv`, the fundamental group of `RPⁿ` at any basepoint is
isomorphic to the opposite of the deck group. Since `ℤˣ` is commutative, the opposite drops out,
yielding

  `FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ`

and in particular `π₁(RPⁿ) ≅ ℤ/2`.

As consequences, `RPⁿ` (for `1 ≤ n` and simply connected `Sⁿ`) has a fundamental group of order 2,
a nontrivial fundamental group, is not simply connected, not contractible, and not homeomorphic to
`ℝ`.

## Main declarations

* `TauCeti.RealProjectiveSpace.pathConnectedSpace_sphere`: `Sⁿ` is path-connected for `1 ≤ n`.
* `TauCeti.RealProjectiveSpace.pathConnectedSpace`: `RPⁿ` is path-connected for `1 ≤ n`.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv`: for `1 ≤ n` and a simply connected
  covering sphere, `FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ` for any basepoint `x`
  with a chosen lift `e`.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv'`: basepoint-unconscious version
  for any `x`.
* `TauCeti.RealProjectiveSpace.card_fundamentalGroup`:
  `Nat.card (FundamentalGroup (RealProjectiveSpace n) x) = 2`.
* `TauCeti.RealProjectiveSpace.nontrivial_fundamentalGroup`: the fundamental group is nontrivial.
* `TauCeti.RealProjectiveSpace.not_simplyConnectedSpace`: `RPⁿ` is not simply connected.
* `TauCeti.RealProjectiveSpace.not_contractibleSpace`: `RPⁿ` is not contractible.
* `TauCeti.RealProjectiveSpace.isEmpty_homeomorph_real`: `RPⁿ` is not homeomorphic to `ℝ`.

## References

This completes the `π₁(RPⁿ)` milestone in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4,
item 13. It consumes `TauCeti.RealProjectiveSpace.isQuotientCoveringMap_mk` and
`TauCeti.RealProjectiveSpace.deckMulEquiv` from
`TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Deck`, and the regular-cover comparison
of Stage 1.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

open Metric Deck

noncomputable section

variable (n : ℕ)

/-- The unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` is path-connected once `1 ≤ n`. -/
theorem pathConnectedSpace_sphere (hn : 1 ≤ n) :
    PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  have hpc := isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 1))) zero_le_one
  exact isPathConnected_iff_pathConnectedSpace.mp hpc

/-- Real projective space is path-connected once `1 ≤ n`, as the continuous image of the
path-connected unit sphere `Sⁿ`. -/
theorem pathConnectedSpace (hn : 1 ≤ n) :
    PathConnectedSpace (RealProjectiveSpace n) := by
  have hpc := pathConnectedSpace_sphere n hn
  exact (mk_surjective n).pathConnectedSpace (continuous_mk n)

/-- **The fundamental group of real projective space `RPⁿ` (for `1 ≤ n`) with a simply connected
covering sphere is isomorphic to `ℤˣ`**, for any basepoint `x` with a chosen lift `e` in the sphere:
`FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ`. -/
def fundamentalGroupMulEquiv (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x}) :
    FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ :=
  (Deck.IsRegular.fundamentalGroupEquiv (isRegular_mk n) (isCoveringMap_mk n) e).trans
    ((MulEquiv.op (deckMulEquiv n hn).symm).trans
      (MulOpposite.opMulEquiv (M := ℤˣ)).symm)

/-- Characterization of the element of `ℤˣ` assigned by `fundamentalGroupMulEquiv`: a loop
class `γ` maps to `u : ℤˣ` exactly when its monodromy translate of the chosen lift `e` is
`u • (e : sphere _ 1)`. -/
lemma fundamentalGroupMulEquiv_apply_eq_iff (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x})
    (γ : FundamentalGroup (RealProjectiveSpace n) x) (u : ℤˣ) :
    fundamentalGroupMulEquiv n hn e γ = u ↔
      ((isCoveringMap_mk n).monodromy γ e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
        u • (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have h1 : fundamentalGroupMulEquiv n hn e γ = u ↔
      (deckMulEquiv n hn).symm (Deck.IsRegular.fundamentalGroupEquiv (isRegular_mk n)
        (isCoveringMap_mk n) e γ).unop = u := Iff.rfl
  have h2 : (deckMulEquiv n hn).symm (Deck.IsRegular.fundamentalGroupEquiv (isRegular_mk n)
        (isCoveringMap_mk n) e γ).unop = u ↔
      Deck.IsRegular.fundamentalGroupEquiv (isRegular_mk n)
        (isCoveringMap_mk n) e γ = MulOpposite.op (deckMulEquiv n hn u) := by
    rw [MulEquiv.symm_apply_eq]
    constructor
    · intro h
      rw [← MulOpposite.op_unop (Deck.IsRegular.fundamentalGroupEquiv _ _ e γ), h]
    · intro h
      rw [h, MulOpposite.unop_op]
  rw [h1, h2, Deck.IsRegular.fundamentalGroupEquiv_apply_eq_iff, MulOpposite.unop_op]
  change (deckMulEquiv n hn u).1 (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
    ((isCoveringMap_mk n).monodromy γ e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ↔ _
  rw [deckMulEquiv_apply n hn u (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
  exact eq_comm

/-- The inverse equivalence sends an integer unit `u` to the loop class whose monodromy
translates the chosen lift by `u`. -/
@[simp]
lemma fundamentalGroupMulEquiv_symm_monodromy (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x}) (u : ℤˣ) :
    ((isCoveringMap_mk n).monodromy ((fundamentalGroupMulEquiv n hn e).symm u) e :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
        u • (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  exact (fundamentalGroupMulEquiv_apply_eq_iff n hn e
    ((fundamentalGroupMulEquiv n hn e).symm u) u).1
      (MulEquiv.apply_symm_apply _ _)

/-- A loop class maps to `1` under `fundamentalGroupMulEquiv` exactly when its monodromy fixes
the chosen lift. -/
lemma fundamentalGroupMulEquiv_eq_one_iff (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    {x : RealProjectiveSpace n} (e : (mk n) ⁻¹' {x})
    (γ : FundamentalGroup (RealProjectiveSpace n) x) :
    fundamentalGroupMulEquiv n hn e γ = 1 ↔ (isCoveringMap_mk n).monodromy γ e = e := by
  rw [fundamentalGroupMulEquiv_apply_eq_iff]
  simpa using (Iff.symm Subtype.ext_iff :
    (((isCoveringMap_mk n).monodromy γ e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
      (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ↔
        (isCoveringMap_mk n).monodromy γ e = e))

/-- **The fundamental group of real projective space `RPⁿ` (for `1 ≤ n`) with a simply connected
covering sphere is isomorphic to `ℤˣ` for any basepoint `x`**:
`FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ`. -/
def fundamentalGroupMulEquiv' (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    (x : RealProjectiveSpace n) :
    FundamentalGroup (RealProjectiveSpace n) x ≃* ℤˣ :=
  let h := mk_surjective n x
  fundamentalGroupMulEquiv n hn ⟨h.choose, Set.mem_singleton_iff.mpr h.choose_spec⟩

/-- For `1 ≤ n` and a simply connected covering sphere, the fundamental group of `RPⁿ` has
exactly two elements. -/
theorem card_fundamentalGroup (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    (x : RealProjectiveSpace n) :
    Nat.card (FundamentalGroup (RealProjectiveSpace n) x) = 2 := by
  rw [Nat.card_congr (fundamentalGroupMulEquiv' n hn x).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

/-- For `1 ≤ n` and a simply connected covering sphere, the fundamental group of `RPⁿ` is
nontrivial. -/
theorem nontrivial_fundamentalGroup (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)]
    (x : RealProjectiveSpace n) :
    Nontrivial (FundamentalGroup (RealProjectiveSpace n) x) := by
  have hunit : Nontrivial ℤˣ := ⟨(1 : ℤˣ), (-1 : ℤˣ), by decide⟩
  exact @Equiv.nontrivial _ _ (fundamentalGroupMulEquiv' n hn x).toEquiv hunit

/-- For `1 ≤ n` and a simply connected covering sphere, real projective space `RPⁿ` is not
simply connected. -/
theorem not_simplyConnectedSpace (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)] :
    ¬ SimplyConnectedSpace (RealProjectiveSpace n) := by
  let x : RealProjectiveSpace n := mk n (instNonemptySphere n).some
  have := nontrivial_fundamentalGroup n hn x
  exact not_simplyConnectedSpace_of_nontrivial_fundamentalGroup x

/-- For `1 ≤ n` and a simply connected covering sphere, real projective space `RPⁿ` is not
contractible. -/
theorem not_contractibleSpace (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)] :
    ¬ ContractibleSpace (RealProjectiveSpace n) :=
  not_contractibleSpace_of_not_simplyConnectedSpace (not_simplyConnectedSpace n hn)

/-- For `1 ≤ n` and a simply connected covering sphere, real projective space `RPⁿ` is not
homeomorphic to `ℝ`. -/
theorem isEmpty_homeomorph_real (hn : 1 ≤ n)
    [SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)] :
    IsEmpty (RealProjectiveSpace n ≃ₜ ℝ) :=
  isEmpty_homeomorph_real_of_not_simplyConnectedSpace (not_simplyConnectedSpace n hn)

end

end RealProjectiveSpace

end TauCeti
