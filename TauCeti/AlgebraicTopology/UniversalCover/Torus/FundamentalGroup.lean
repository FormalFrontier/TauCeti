/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup

/-!
# The fundamental group of a torus

Combining the product formula for fundamental groups
(`TauCeti.FundamentalGroup.prodMulEquiv`, `…piMulEquiv`) with the circle computation
`π₁(AddCircle p) ≃* Multiplicative ℤ` (`TauCeti.AddCircle.fundamentalGroupMulEquiv_zero`)
gives the fundamental group of a torus. For a finite product of circles this is the free
abelian group `(Multiplicative ℤ)ᵏ`; in particular the standard two-torus
`AddCircle p × AddCircle q` has fundamental group `Multiplicative ℤ × Multiplicative ℤ`.

This realises the universal-covers roadmap Stage 4 "applications" target `π_n(Tᵏ)` at
`n = 1`: `π₁(Tᵏ) ≅ ℤᵏ`.

## Main declarations

* `TauCeti.AddCircle.prodFundamentalGroupMulEquiv`:
  `π₁(AddCircle p × AddCircle q, (x, y)) ≃* Multiplicative ℤ × Multiplicative ℤ`.
* `TauCeti.AddCircle.piFundamentalGroupMulEquiv`:
  `π₁(Π i, AddCircle (p i), x) ≃* Π i, Multiplicative ℤ`, the fundamental group of a torus.
* `TauCeti.AddCircle.prodFundamentalGroupMulEquiv_zero`,
  `TauCeti.AddCircle.piFundamentalGroupMulEquiv_zero`: the basepoint-`0` specialisations.
-/

public section

namespace TauCeti

open Path.Homotopic

noncomputable section

namespace AddCircle

/-- The fundamental group of the two-torus `AddCircle p × AddCircle q`, based at any point
`(x, y)` with chosen lifts `ex`, `ey`, is `Multiplicative ℤ × Multiplicative ℤ`, for nonzero
real periods `p` and `q`. The forward map records, in each coordinate, the integer the
corresponding projected loop winds around that circle. -/
def prodFundamentalGroupMulEquiv {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    {x : AddCircle p} {y : AddCircle q}
    (ex : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (ey : ((↑) : ℝ → AddCircle q) ⁻¹' {y}) :
    FundamentalGroup (AddCircle p × AddCircle q) (x, y) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquiv x y).trans
    ((fundamentalGroupMulEquiv p hp ex).prodCongr (fundamentalGroupMulEquiv q hq ey))

@[simp]
theorem prodFundamentalGroupMulEquiv_apply {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    {x : AddCircle p} {y : AddCircle q}
    (ex : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (ey : ((↑) : ℝ → AddCircle q) ⁻¹' {y})
    (γ : FundamentalGroup (AddCircle p × AddCircle q) (x, y)) :
    prodFundamentalGroupMulEquiv hp hq ex ey γ =
      (fundamentalGroupMulEquiv p hp ex
          (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × AddCircle q, _)) (x, y) γ),
        fundamentalGroupMulEquiv q hq ey
          (FundamentalGroup.map (ContinuousMap.snd : C(AddCircle p × AddCircle q, _)) (x, y) γ)) :=
  congrArg ((fundamentalGroupMulEquiv p hp ex).prodCongr (fundamentalGroupMulEquiv q hq ey))
    (FundamentalGroup.prodMulEquiv_apply x y γ)

@[simp]
theorem prodFundamentalGroupMulEquiv_symm_apply {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    {x : AddCircle p} {y : AddCircle q}
    (ex : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (ey : ((↑) : ℝ → AddCircle q) ⁻¹' {y})
    (mn : Multiplicative ℤ × Multiplicative ℤ) :
    (prodFundamentalGroupMulEquiv hp hq ex ey).symm mn =
      prod ((fundamentalGroupMulEquiv p hp ex).symm mn.1)
        ((fundamentalGroupMulEquiv q hq ey).symm mn.2) :=
  FundamentalGroup.prodMulEquiv_symm_apply x y
    (((fundamentalGroupMulEquiv p hp ex).prodCongr (fundamentalGroupMulEquiv q hq ey)).symm mn)

/-- The fundamental group of a torus `Π i, AddCircle (p i)`, based at any point `x` with chosen
lifts `e`, is the product `Π i, Multiplicative ℤ`, for a family of nonzero real periods. For a
finite index this is the free abelian group `(Multiplicative ℤ)ᵏ`, i.e. `π₁(Tᵏ) ≅ ℤᵏ`. The
forward map records, in each coordinate, the winding integer of the corresponding projected
loop. -/
def piFundamentalGroupMulEquiv {ι : Type*} {p : ι → ℝ} (hp : ∀ i, p i ≠ 0)
    {x : ∀ i, AddCircle (p i)} (e : ∀ i, ((↑) : ℝ → AddCircle (p i)) ⁻¹' {x i}) :
    FundamentalGroup (∀ i, AddCircle (p i)) x ≃* ∀ _ : ι, Multiplicative ℤ :=
  (FundamentalGroup.piMulEquiv x).trans
    (MulEquiv.piCongrRight fun i => fundamentalGroupMulEquiv (p i) (hp i) (e i))

@[simp]
theorem piFundamentalGroupMulEquiv_apply {ι : Type*} {p : ι → ℝ} (hp : ∀ i, p i ≠ 0)
    {x : ∀ i, AddCircle (p i)} (e : ∀ i, ((↑) : ℝ → AddCircle (p i)) ⁻¹' {x i})
    (γ : FundamentalGroup (∀ i, AddCircle (p i)) x) (i : ι) :
    piFundamentalGroupMulEquiv hp e γ i =
      fundamentalGroupMulEquiv (p i) (hp i) (e i)
        (FundamentalGroup.map (ContinuousMap.eval i) x γ) :=
  congrArg (fundamentalGroupMulEquiv (p i) (hp i) (e i))
    (FundamentalGroup.piMulEquiv_apply x γ i)

@[simp]
theorem piFundamentalGroupMulEquiv_symm_apply {ι : Type*} {p : ι → ℝ} (hp : ∀ i, p i ≠ 0)
    {x : ∀ i, AddCircle (p i)} (e : ∀ i, ((↑) : ℝ → AddCircle (p i)) ⁻¹' {x i})
    (n : ∀ _ : ι, Multiplicative ℤ) :
    (piFundamentalGroupMulEquiv hp e).symm n =
      pi fun i => (fundamentalGroupMulEquiv (p i) (hp i) (e i)).symm (n i) :=
  FundamentalGroup.piMulEquiv_symm_apply x
    ((MulEquiv.piCongrRight fun i => fundamentalGroupMulEquiv (p i) (hp i) (e i)).symm n)

/-- The fundamental group of the two-torus `AddCircle p × AddCircle q`, based at `(0, 0)`, is
`Multiplicative ℤ × Multiplicative ℤ`, for nonzero real periods `p` and `q`. -/
def prodFundamentalGroupMulEquiv_zero {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    FundamentalGroup (AddCircle p × AddCircle q) (0, 0) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  prodFundamentalGroupMulEquiv hp hq ⟨0, by simp⟩ ⟨0, by simp⟩

@[simp]
theorem prodFundamentalGroupMulEquiv_zero_apply {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (γ : FundamentalGroup (AddCircle p × AddCircle q) (0, 0)) :
    prodFundamentalGroupMulEquiv_zero hp hq γ =
      (fundamentalGroupMulEquiv_zero p hp
          (FundamentalGroup.map (ContinuousMap.fst : C(AddCircle p × AddCircle q, _)) (0, 0) γ),
        fundamentalGroupMulEquiv_zero q hq
          (FundamentalGroup.map
            (ContinuousMap.snd : C(AddCircle p × AddCircle q, _)) (0, 0) γ)) := by
  simp [prodFundamentalGroupMulEquiv_zero]

@[simp]
theorem prodFundamentalGroupMulEquiv_zero_symm_apply {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (mn : Multiplicative ℤ × Multiplicative ℤ) :
    (prodFundamentalGroupMulEquiv_zero hp hq).symm mn =
      prod ((fundamentalGroupMulEquiv_zero p hp).symm mn.1)
        ((fundamentalGroupMulEquiv_zero q hq).symm mn.2) := by
  simp [prodFundamentalGroupMulEquiv_zero]

/-- The fundamental group of a torus `Π i, AddCircle (p i)`, based at `0`, is the product
`Π i, Multiplicative ℤ`, for a family of nonzero real periods. For a finite index this is the
free abelian group `(Multiplicative ℤ)ᵏ`, i.e. `π₁(Tᵏ) ≅ ℤᵏ`. -/
def piFundamentalGroupMulEquiv_zero {ι : Type*} {p : ι → ℝ} (hp : ∀ i, p i ≠ 0) :
    FundamentalGroup (∀ i, AddCircle (p i)) (fun _ => 0) ≃* ∀ _ : ι, Multiplicative ℤ :=
  piFundamentalGroupMulEquiv hp fun i => ⟨0, by simp⟩

@[simp]
theorem piFundamentalGroupMulEquiv_zero_apply {ι : Type*} {p : ι → ℝ}
    (hp : ∀ i, p i ≠ 0)
    (γ : FundamentalGroup (∀ i, AddCircle (p i)) (fun _ => 0)) (i : ι) :
    piFundamentalGroupMulEquiv_zero hp γ i =
      fundamentalGroupMulEquiv_zero (p i) (hp i)
        (FundamentalGroup.map (ContinuousMap.eval i) (fun _ => 0) γ) := by
  simp [piFundamentalGroupMulEquiv_zero]

@[simp]
theorem piFundamentalGroupMulEquiv_zero_symm_apply {ι : Type*} {p : ι → ℝ}
    (hp : ∀ i, p i ≠ 0) (n : ∀ _ : ι, Multiplicative ℤ) :
    (piFundamentalGroupMulEquiv_zero hp).symm n =
      pi fun i => (fundamentalGroupMulEquiv_zero (p i) (hp i)).symm (n i) := by
  simp [piFundamentalGroupMulEquiv_zero]

end AddCircle

end

end TauCeti
