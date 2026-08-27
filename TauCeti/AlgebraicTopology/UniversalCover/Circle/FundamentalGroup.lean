/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.AddCircle
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Basic

/-!
# The fundamental group of the circle is `ℤ`

The covering `(↑) : ℝ → AddCircle p` is the universal cover of the circle: its total space
`ℝ` is contractible, hence simply connected, and the cover is regular with deck group
`Multiplicative ℤ` (the translations by the period subgroup, computed in
`TauCeti.Deck.addCircleMulEquivInt`). The regular-cover comparison
`TauCeti.Deck.IsRegular.fundamentalGroupDeckEquiv` then identifies the fundamental group of
the base with the deck group itself (the opposite drops out because the deck group is
commutative), giving

  `FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`

for any nonzero real period `p`. Specialising to the unit circle `UnitAddCircle = ℝ ⧸ ℤ`
yields the classical `π₁(S¹) ≅ ℤ`.

The regularity input is elementary and holds for an arbitrary topological additive group:
two points of `𝕜` with the same image under `(↑) : 𝕜 → AddCircle p` differ by an element of
the period subgroup `zmultiples p`, and translation by that element is a deck
transformation, so `Deck ((↑) : 𝕜 → AddCircle p)` acts transitively on every fibre.

## Main declarations

* `AddCircle.fundamentalGroupMulEquivZMultiples`: for a covering projection from a simply
  connected additive group, the fundamental group of `AddCircle p` is the period subgroup.
* `AddCircle.fundamentalGroupMulEquivInt`: for a covering projection from a simply connected
  additive group with non-torsion period, the fundamental group of `AddCircle p` is
  `Multiplicative ℤ`.
* `AddCircle.fundamentalGroupMulEquiv`: for a nonzero real period, the fundamental group of
  `AddCircle p` (based at any point with a chosen lift) is `Multiplicative ℤ`.
* `AddCircle.fundamentalGroupMulEquivZero`: the basepoint-`0` specialisation, using the lift
  `0 : ℝ`.
* `UnitAddCircle.fundamentalGroupMulEquiv`: `π₁(S¹) ≅ ℤ` for the unit circle.

## References

This advances the Tau Ceti universal-covers roadmap, Stage 4 target 12 (`π₁(S¹) ≅ ℤ`,
"built from `AddCircle.isCoveringMap_coe` (`ℝ → S¹`) and deck transformations";
`TauCetiRoadmap/UniversalCovers/README.md`). It consumes Mathlib's `AddCircle` covering map
(`AddCircle.isCoveringMap_coe`, Junyan Xu) and the contractibility of a real topological
vector space, together with the Tau Ceti deck-transformation theory of Stages 0.4 and 1.
-/

public section

open TauCeti AddSubgroup

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  {p : 𝕜} [SimplyConnectedSpace 𝕜]
  [TotallyDisconnectedSpace (zmultiples p)]

/-- For a covering projection `(↑) : 𝕜 → AddCircle p` from a simply connected preconnected
topological additive commutative group with totally disconnected period subgroup, the
fundamental group of `AddCircle p` is the multiplicative period subgroup. -/
noncomputable def fundamentalGroupMulEquivZMultiples (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative (zmultiples p) :=
  (Deck.isRegular_addCircleCoe.fundamentalGroupDeckEquiv hcov e
    (fun a b => Deck.addCircleMulEquiv.symm.injective (by simp [mul_comm]))).trans
    Deck.addCircleMulEquiv.symm

/-- Characterization of the period-subgroup element assigned by
`fundamentalGroupMulEquivZMultiples`: a loop class maps to `n` exactly when its monodromy
translate of the chosen lift differs by the element `n`. -/
lemma fundamentalGroupMulEquivZMultiples_apply_eq_iff (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (AddCircle p) x) (n : Multiplicative (zmultiples p)) :
    fundamentalGroupMulEquivZMultiples hcov e γ = n ↔
      (hcov.monodromy γ e : 𝕜) = (e : 𝕜) + (n.toAdd : 𝕜) := by
  rw [fundamentalGroupMulEquivZMultiples, MulEquiv.trans_apply, MulEquiv.symm_apply_eq,
    Deck.IsRegular.fundamentalGroupDeckEquiv_apply_eq_iff]
  simp only [Deck.smul_eq_apply, Deck.addCircleMulEquiv_apply,
    Deck.addRightZMultiples_apply, eq_comm]

/-- The inverse of the period-subgroup equivalence sends `n` to the loop class whose monodromy
translates the chosen lift by `n`. -/
@[simp]
lemma fundamentalGroupMulEquivZMultiples_symm_monodromy
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (n : Multiplicative (zmultiples p)) :
    (hcov.monodromy ((fundamentalGroupMulEquivZMultiples hcov e).symm n) e : 𝕜) =
      (e : 𝕜) + (n.toAdd : 𝕜) := by
  exact (fundamentalGroupMulEquivZMultiples_apply_eq_iff hcov e
    ((fundamentalGroupMulEquivZMultiples hcov e).symm n) n).1
      (MulEquiv.apply_symm_apply _ _)

/-- A loop class maps to `1` under the period-subgroup equivalence exactly when its monodromy
fixes the chosen lift. -/
lemma fundamentalGroupMulEquivZMultiples_eq_one_iff (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p))
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) :
    fundamentalGroupMulEquivZMultiples hcov e γ = 1 ↔ hcov.monodromy γ e = e := by
  rw [fundamentalGroupMulEquivZMultiples_apply_eq_iff]
  simpa using (Iff.symm Subtype.ext_iff :
    ((hcov.monodromy γ e : 𝕜) = (e : 𝕜) ↔ hcov.monodromy γ e = e))

/-- For a covering projection `(↑) : 𝕜 → AddCircle p` from a simply connected preconnected
topological additive commutative group with totally disconnected non-torsion period subgroup,
the fundamental group of `AddCircle p` is infinite cyclic:
`FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`. -/
noncomputable def fundamentalGroupMulEquivInt
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivZMultiples hcov e).trans (intEquivZMultiples hp).toMultiplicative.symm

/-- Characterization of the integer assigned by `fundamentalGroupMulEquivInt`: a loop
class maps to `n` exactly when its monodromy translate of the chosen lift differs by `n • p`. -/
lemma fundamentalGroupMulEquivInt_apply_eq_iff
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x})
    (γ : FundamentalGroup (AddCircle p) x) (n : Multiplicative ℤ) :
    fundamentalGroupMulEquivInt hcov hp e γ = n ↔
      (hcov.monodromy γ e : 𝕜) = (e : 𝕜) + n.toAdd • p := by
  dsimp [fundamentalGroupMulEquivInt]
  rw [MulEquiv.symm_apply_eq]
  simpa using fundamentalGroupMulEquivZMultiples_apply_eq_iff hcov e γ
    ((intEquivZMultiples hp).toMultiplicative n)

/-- The inverse generic integer equivalence sends `n` to the loop class whose monodromy
translates the chosen lift by `n • p`. -/
@[simp]
lemma fundamentalGroupMulEquivInt_symm_monodromy
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (n : Multiplicative ℤ) :
    (hcov.monodromy ((fundamentalGroupMulEquivInt hcov hp e).symm n) e : 𝕜) =
      (e : 𝕜) + n.toAdd • p := by
  exact (fundamentalGroupMulEquivInt_apply_eq_iff hcov hp e
    ((fundamentalGroupMulEquivInt hcov hp e).symm n) n).1
      (MulEquiv.apply_symm_apply _ _)

/-- A loop class maps to `1` under the generic integer equivalence exactly when its monodromy
fixes the chosen lift. -/
lemma fundamentalGroupMulEquivInt_eq_one_iff
    (hcov : IsCoveringMap ((↑) : 𝕜 → AddCircle p)) (hp : ¬ IsOfFinAddOrder p)
    {x : AddCircle p} (e : ((↑) : 𝕜 → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) :
    fundamentalGroupMulEquivInt hcov hp e γ = 1 ↔ hcov.monodromy γ e = e := by
  rw [fundamentalGroupMulEquivInt_apply_eq_iff]
  simpa using (Iff.symm Subtype.ext_iff :
    ((hcov.monodromy γ e : 𝕜) = (e : 𝕜) ↔ hcov.monodromy γ e = e))

variable (p : ℝ)

/-- For a nonzero real period `p`, the fundamental group of the circle `AddCircle p`, based at
any point `x` with a chosen lift `e : (↑) ⁻¹' {x}`, is infinite cyclic:
`FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`. -/
noncomputable def fundamentalGroupMulEquiv (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  fundamentalGroupMulEquivInt (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e

/-- Characterization of the integer assigned by `fundamentalGroupMulEquiv`: a loop class maps
to `n` exactly when its monodromy translate of the chosen lift differs by `n • p`. -/
lemma fundamentalGroupMulEquiv_apply_eq_iff (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x)
    (n : Multiplicative ℤ) :
    fundamentalGroupMulEquiv p hp e γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy γ e : ℝ) = (e : ℝ) + n.toAdd • p :=
  fundamentalGroupMulEquivInt_apply_eq_iff (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e γ n

/-- The inverse equivalence sends `n` to the loop class whose monodromy translates the chosen
lift by `n • p`. -/
@[simp]
lemma fundamentalGroupMulEquiv_symm_monodromy (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy ((fundamentalGroupMulEquiv p hp e).symm n) e :
      ℝ) = (e : ℝ) + n.toAdd • p :=
  fundamentalGroupMulEquivInt_symm_monodromy (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e n

/-- A loop class maps to `1` under `fundamentalGroupMulEquiv` exactly when its monodromy fixes
the chosen lift. -/
lemma fundamentalGroupMulEquiv_eq_one_iff (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) :
    fundamentalGroupMulEquiv p hp e γ = 1 ↔ (AddCircle.isCoveringMap_coe p).monodromy γ e = e :=
  fundamentalGroupMulEquivInt_eq_one_iff (AddCircle.isCoveringMap_coe p)
    (not_isOfFinAddOrder_of_isAddTorsionFree hp) e γ

/-- The fundamental group of the circle `AddCircle p` based at `0`, with the lift `0 : ℝ`, is
`Multiplicative ℤ`. -/
noncomputable def fundamentalGroupMulEquivZero (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p) 0 ≃* Multiplicative ℤ :=
  fundamentalGroupMulEquiv p hp ⟨0, by simp⟩

/-- Characterization of the integer assigned by the basepoint-`0` specialization. -/
lemma fundamentalGroupMulEquivZero_apply_eq_iff (hp : p ≠ 0)
    (γ : FundamentalGroup (AddCircle p) 0) (n : Multiplicative ℤ) :
    fundamentalGroupMulEquivZero p hp γ = n ↔
      ((AddCircle.isCoveringMap_coe p).monodromy γ ⟨0, by simp⟩ : ℝ) = n.toAdd • p := by
  rw [fundamentalGroupMulEquivZero]
  simpa using fundamentalGroupMulEquiv_apply_eq_iff p hp ⟨0, by simp⟩ γ n

@[simp]
lemma fundamentalGroupMulEquivZero_apply (hp : p ≠ 0) (γ : FundamentalGroup (AddCircle p) 0) :
    fundamentalGroupMulEquivZero p hp γ = fundamentalGroupMulEquiv p hp ⟨0, by simp⟩ γ := by
  apply (fundamentalGroupMulEquivZero_apply_eq_iff p hp γ _).2
  simpa using (fundamentalGroupMulEquiv_apply_eq_iff p hp ⟨0, by simp⟩ γ _).1 rfl

@[simp]
lemma fundamentalGroupMulEquivZero_symm_apply (hp : p ≠ 0) (n : Multiplicative ℤ) :
    (fundamentalGroupMulEquivZero p hp).symm n =
      (fundamentalGroupMulEquiv p hp ⟨0, by simp⟩).symm n := by
  apply (fundamentalGroupMulEquivZero p hp).injective
  rw [MulEquiv.apply_symm_apply, fundamentalGroupMulEquivZero_apply, MulEquiv.apply_symm_apply]

/-- The inverse of the basepoint-`0` specialization has monodromy translation `n • p`. -/
lemma fundamentalGroupMulEquivZero_symm_monodromy (hp : p ≠ 0) (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy ((fundamentalGroupMulEquivZero p hp).symm n)
      ⟨0, by simp⟩ : ℝ) = n.toAdd • p := by
  rw [fundamentalGroupMulEquivZero]
  simp

/-- A loop class maps to `1` under the basepoint-`0` specialization exactly when its monodromy
fixes the zero lift. -/
lemma fundamentalGroupMulEquivZero_eq_one_iff (hp : p ≠ 0) (γ : FundamentalGroup (AddCircle p) 0) :
    fundamentalGroupMulEquivZero p hp γ = 1 ↔
      (AddCircle.isCoveringMap_coe p).monodromy γ ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
  rw [fundamentalGroupMulEquivZero]
  exact fundamentalGroupMulEquiv_eq_one_iff p hp ⟨0, by simp⟩ γ

end AddCircle

namespace UnitAddCircle

/-- The fundamental group of the unit circle `S¹ = ℝ ⧸ ℤ` is `ℤ`:
`FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ`. This is the classical `π₁(S¹) ≅ ℤ`. -/
noncomputable def fundamentalGroupMulEquiv :
    FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ :=
  AddCircle.fundamentalGroupMulEquivZero 1 one_ne_zero

/-- Characterization of the integer assigned by the unit-circle equivalence. -/
lemma fundamentalGroupMulEquiv_apply_eq_iff (γ : FundamentalGroup UnitAddCircle 0)
    (n : Multiplicative ℤ) :
    fundamentalGroupMulEquiv γ = n ↔
      ((AddCircle.isCoveringMap_coe 1).monodromy γ ⟨0, by simp⟩ : ℝ) = n.toAdd := by
  simpa [fundamentalGroupMulEquiv] using
    AddCircle.fundamentalGroupMulEquivZero_apply_eq_iff 1 one_ne_zero γ n

/-- The inverse of the unit-circle equivalence has monodromy translation by `n`. -/
@[simp]
lemma fundamentalGroupMulEquiv_symm_monodromy (n : Multiplicative ℤ) :
    ((AddCircle.isCoveringMap_coe 1).monodromy (fundamentalGroupMulEquiv.symm n)
      ⟨0, by simp⟩ : ℝ) = n.toAdd := by
  simp [fundamentalGroupMulEquiv]

/-- A unit-circle loop class maps to `1` exactly when its monodromy fixes the zero lift. -/
lemma fundamentalGroupMulEquiv_eq_one_iff (γ : FundamentalGroup UnitAddCircle 0) :
    fundamentalGroupMulEquiv γ = 1 ↔
      (AddCircle.isCoveringMap_coe 1).monodromy γ ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
  simpa [fundamentalGroupMulEquiv] using
    AddCircle.fundamentalGroupMulEquivZero_eq_one_iff 1 one_ne_zero γ

end UnitAddCircle
