/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Weil

/-!
# Local components of a Weil differential

A `k`-linear form `ω` on the repartition space `A_F` of an algebraic function field `F / k` can be
evaluated on the repartitions supported at a single place: writing `ι_P x` for the repartition
with the entry `x` at `P` and `0` everywhere else, the **local component** of `ω` at `P` is the
`k`-linear form

`ω_P : F → k`, `ω_P x = ω (ι_P x)`

on `F` itself.  When `ω` is a Weil differential the local components determine it, and they do so
by a *sum*: for every repartition `a`, all but finitely many of the values `ω_P (a P)` vanish and

`ω a = ∑_P ω_P (a P)`.

Applying this to the constant repartition of a function `x ∈ F` — which a Weil differential kills,
being a linear form on `A_F / (A_F(D) + F)` — gives `∑_P ω_P (x) = 0`, the **abstract residue
theorem**: it is Stichtenoth's `(1.45)` for `x = 1`, and it holds over an arbitrary constant field,
with no analysis and before any residue map has been constructed.

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Definitions 1.7.1,
Proposition 1.7.2 and the divisor-free half of Proposition 1.7.3(a).  The remaining statements of
Section I.7 — that no local component of a nonzero Weil differential vanishes, that `v_P (ω)` is
the largest bound its local component respects, and the explicit generator of `Ω_{k(x)}` — need
the divisor of a Weil differential, and are not proved here.

The repartitions `ι_P x` themselves are built in
`TauCeti.FieldTheory.FunctionField.Repartition.Basic`, next to the repartition space and its
filtration, which are all they depend on.

## Main definitions

* `TauCeti.repartitionDualComponent`: the local component `ω_P` of a `k`-linear form on `A_F`
  (Stichtenoth, Definition 1.7.1).

## Main results

* `TauCeti.repartitionDualComponent_apply_eq_zero_of_le`: the local component at `P` of a Weil
  differential bounded by `D` vanishes on the functions whose pole at `P` is bounded by `D`.
* `TauCeti.finite_support_repartitionDualComponent_apply` and
  `TauCeti.apply_eq_finsum_repartitionDualComponent`: **`ω a = ∑_P ω_P (a P)`, with cofinite
  vanishing** (Stichtenoth, Proposition 1.7.2).
* `TauCeti.mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero`: a Weil
  differential is bounded by `D` exactly when each of its local components vanishes on the
  functions `D` allows at that place (Stichtenoth, half of Proposition 1.7.3(a)).
* `TauCeti.finsum_repartitionDualComponent_eq_zero`: **the abstract residue theorem**
  `∑_P ω_P (x) = 0` for every function `x` (Stichtenoth, (1.45)).
* `TauCeti.eq_zero_iff_repartitionDualComponent_eq_zero`: a Weil differential all of whose local
  components vanish is zero.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.7.
-/

public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The local components -/

/-- The **local component** `ω_P` at a place `P` of a `k`-linear form `ω` on the repartition space
(Stichtenoth, Definition 1.7.1): the `k`-linear form `x ↦ ω (ι_P x)` on `F`. -/
noncomputable def repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F))
    (P : Place k F) : Module.Dual k F :=
  ω ∘ₗ singleRepartition P

/-- The defining formula `ω_P x = ω (ι_P x)` of a local component. -/
@[simp]
theorem repartitionDualComponent_apply (ω : Module.Dual k ↥(repartitionSpace k F))
    (P : Place k F) (x : F) :
    repartitionDualComponent ω P x = ω (singleRepartition P x) :=
  (rfl)

/-- The local components of a multiple of a linear form: `(f · ω)_P x = ω_P (f x)`.

This is not `@[simp]`: `simp` already proves it from `repartitionDualComponent_apply`,
`repartitionDualMul_apply_apply` and `repartitionMul_singleRepartition`, so tagging it is a
simp-normal-form violation that `scripts/lint-env.sh` rejects. -/
theorem repartitionDualComponent_repartitionDualMul (hF : IsFunctionField k F) (f : F)
    (ω : Module.Dual k ↥(repartitionSpace k F)) (P : Place k F) (x : F) :
    repartitionDualComponent (repartitionDualMul hF f ω) P x =
      repartitionDualComponent ω P (f * x) := by
  simp

/-- **The local component at `P` of a Weil differential bounded by `D` kills the functions whose
pole at `P` is bounded by `D`**: such an `x` has `ι_P x ∈ A_F(D)`, which `ω` kills. -/
theorem repartitionDualComponent_apply_eq_zero_of_le {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialFiltration D)
    (P : Place k F) {x : F} (hx : P.valuation x ≤ WithZero.exp (D.coeff P)) :
    repartitionDualComponent ω P x = 0 :=
  weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hω _
    (singleRepartition_mem_adeleFiltration_iff.mpr hx)

/-- **A finite set of places carrying `ω`**: outside it the values `ω_P (a P)` vanish, and over it
they sum to `ω a` (Stichtenoth, Proposition 1.7.2).  This is the common witness behind the two
public halves, `TauCeti.finite_support_repartitionDualComponent_apply` and
`TauCeti.apply_eq_finsum_repartitionDualComponent`. -/
-- The witness is the support of `E - D` for a divisor `E` bounding `a`: off it the entry `a P` is
-- already bounded by `D`, so `ι_P (a P)` lies in `A_F(D)` and `ω_P (a P) = 0`; and subtracting
-- from `a` the finitely many repartitions `ι_P (a P)` with `P` in that support leaves a
-- repartition bounded by `D`, which `ω` kills.
private theorem exists_finset_repartitionDualComponent {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialFiltration D)
    (a : ↥(repartitionSpace k F)) :
    ∃ s : Finset (Place k F),
      (Function.support fun P ↦ repartitionDualComponent ω P ((a : Place k F → F) P)) ⊆ s ∧
        ω a = ∑ P ∈ s, repartitionDualComponent ω P ((a : Place k F → F) P) := by
  classical
  obtain ⟨E, hE⟩ := exists_mem_adeleFiltration a.2
  have hbound : ∀ P ∉ (E - D).support,
      P.valuation ((a : Place k F → F) P) ≤ WithZero.exp (D.coeff P) := by
    intro P hP
    have hPD : E.coeff P = D.coeff P := by
      have h0 : (E - D).coeff P = 0 := by
        by_contra hne
        exact hP (WeilDivisor.mem_support_iff.mpr hne)
      rw [WeilDivisor.coeff_sub] at h0
      omega
    exact hPD ▸ mem_adeleFiltration_iff.mp hE P
  refine ⟨(E - D).support, Function.support_subset_iff'.mpr fun P hP ↦
    repartitionDualComponent_apply_eq_zero_of_le hω P (hbound P hP), ?_⟩
  have hsub : ((a - ∑ P ∈ (E - D).support, singleRepartition P ((a : Place k F → F) P) :
      ↥(repartitionSpace k F)) : Place k F → F) ∈ adeleFiltration D := by
    refine mem_adeleFiltration_iff.mpr fun Q ↦ ?_
    have hcoe : ((a - ∑ P ∈ (E - D).support, singleRepartition P ((a : Place k F → F) P) :
        ↥(repartitionSpace k F)) : Place k F → F) Q =
        if Q ∈ (E - D).support then 0 else (a : Place k F → F) Q := by
      rw [Submodule.coe_sub, Pi.sub_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      split_ifs with h
      · rw [Finset.sum_eq_single_of_mem Q h fun P _ hP ↦ singleRepartition_of_ne (Ne.symm hP) _,
          singleRepartition_self, sub_self]
      · rw [Finset.sum_eq_zero fun P hP ↦ singleRepartition_of_ne (by rintro rfl; exact h hP) _,
          sub_zero]
    rw [hcoe]
    split_ifs with h
    · simp
    · exact hbound Q h
  have hzero := weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hω _ hsub
  rw [map_sub, map_sum, sub_eq_zero] at hzero
  simpa using hzero

/-- **The sum `∑_P ω_P (a P)` has finitely many nonzero terms**: for every repartition `a`, the
values `ω_P (a P)` of the local components of a Weil differential vanish at all but finitely many
places `P` (Stichtenoth, Proposition 1.7.2).  It says nothing about a single local component
`ω_P`, which is a linear form on all of `F` and need not vanish anywhere. -/
theorem finite_support_repartitionDualComponent_apply
    {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (a : ↥(repartitionSpace k F)) :
    (Function.support fun P ↦ repartitionDualComponent ω P ((a : Place k F → F) P)).Finite := by
  obtain ⟨D, hD⟩ := mem_weilDifferentialSpace_iff.mp hω
  obtain ⟨s, hs, -⟩ := exists_finset_repartitionDualComponent hD a
  exact s.finite_toSet.subset hs

/-- **A Weil differential is the sum of its local components**: `ω a = ∑_P ω_P (a P)`, a sum with
finitely many nonzero terms (Stichtenoth, Proposition 1.7.2). -/
theorem apply_eq_finsum_repartitionDualComponent {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (a : ↥(repartitionSpace k F)) :
    ω a = ∑ᶠ P : Place k F, repartitionDualComponent ω P ((a : Place k F → F) P) := by
  obtain ⟨D, hD⟩ := mem_weilDifferentialSpace_iff.mp hω
  obtain ⟨s, hs, hsum⟩ := exists_finset_repartitionDualComponent hD a
  rw [hsum, finsum_eq_sum_of_support_subset _ hs]

/-- **A Weil differential is bounded by `D` exactly when its local components are**: the pole
order of `ω` at each place is a local condition, read off from `ω_P` alone.

This is the half of Stichtenoth, Proposition 1.7.3(a) that does not mention the divisor `(ω)`:
the bound at `P` restricts `ω_P` to vanish on the functions whose pole at `P` is bounded by `D`,
and conversely those vanishings force `ω` to kill `A_F(D)`, since `ω` is the sum of its local
components. -/
theorem mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero
    {D : Divisor k F} {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) :
    ω ∈ weilDifferentialFiltration D ↔
      ∀ (P : Place k F) (x : F), P.valuation x ≤ WithZero.exp (D.coeff P) →
        repartitionDualComponent ω P x = 0 := by
  refine ⟨fun h P x hx ↦ repartitionDualComponent_apply_eq_zero_of_le h P hx, fun h ↦ ?_⟩
  obtain ⟨E, hE⟩ := mem_weilDifferentialSpace_iff.mp hω
  refine mem_weilDifferentialFiltration_of_apply_eq_zero (fun a ha ↦ ?_) (fun a ha ↦
    weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions hE a ha)
  rw [apply_eq_finsum_repartitionDualComponent hω a,
    finsum_congr fun P ↦ h P _ (mem_adeleFiltration_iff.mp ha P), finsum_zero]

/-- **The abstract residue theorem** (Stichtenoth, (1.45)): the local components of a Weil
differential sum to zero on every function of `F`.

The constant repartition of `x` lies in the diagonal copy of `F` inside `A_F`, on which every Weil
differential vanishes, and its entry at every place is `x`.  Stichtenoth states the case `x = 1`;
no hypothesis on the constant field `k` is needed, and no residue map has been constructed. -/
theorem finsum_repartitionDualComponent_eq_zero (hF : IsFunctionField k F)
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialSpace k F) (x : F) :
    ∑ᶠ P : Place k F, repartitionDualComponent ω P x = 0 := by
  obtain ⟨D, hD⟩ := mem_weilDifferentialSpace_iff.mp hω
  have hx : Function.const (Place k F) x ∈ repartitionSpace k F := const_mem_repartitionSpace hF x
  have hsum := apply_eq_finsum_repartitionDualComponent hω ⟨_, hx⟩
  rw [weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions hD _
    (const_mem_diagonalRepartitions x)] at hsum
  exact hsum.symm

/-- **A Weil differential is determined by its local components**: it vanishes exactly when all of
them do. -/
theorem eq_zero_iff_repartitionDualComponent_eq_zero
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialSpace k F) :
    ω = 0 ↔ ∀ P : Place k F, repartitionDualComponent ω P = 0 := by
  refine ⟨fun h P ↦ by subst h; ext x; simp, fun h ↦ LinearMap.ext fun a ↦ ?_⟩
  rw [LinearMap.zero_apply, apply_eq_finsum_repartitionDualComponent hω a]
  simp only [h, LinearMap.zero_apply, finsum_zero]

end TauCeti
