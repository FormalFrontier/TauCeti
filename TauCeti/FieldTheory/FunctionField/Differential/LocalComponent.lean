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

## Main definitions

* `TauCeti.singleRepartition`: the repartition `ι_P x` supported at one place, as a `k`-linear map
  `F →ₗ[k] A_F` (Stichtenoth, Definition 1.7.1).
* `TauCeti.repartitionDualComponent`: the local component `ω_P` of a `k`-linear form on `A_F`
  (Stichtenoth, Definition 1.7.1).

## Main results

* `TauCeti.repartitionDualComponent_apply_eq_zero_of_le`: the local component at `P` of a Weil
  differential bounded by `D` vanishes on the functions whose pole at `P` is bounded by `D`.
* `TauCeti.finite_support_repartitionDualComponent` and
  `TauCeti.apply_eq_finsum_repartitionDualComponent`: **`ω a = ∑_P ω_P (a P)`, with cofinite
  vanishing** (Stichtenoth, Proposition 1.7.2).
* `TauCeti.mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero`: a Weil
  differential is bounded by `D` exactly when each of its local components vanishes on the
  functions `D` allows at that place (Stichtenoth, half of Proposition 1.7.3(a)).
* `TauCeti.finsum_repartitionDualComponent_eq_zero`: **the abstract residue theorem**
  `∑_P ω_P (x) = 0` for every function `x` (Stichtenoth, (1.45)).
* `TauCeti.eq_zero_iff_repartitionDualComponent_eq_zero`: a Weil differential all of whose local
  components vanish is zero.

## Implementation notes

`ι_P x` is built with `Set.indicator` on the singleton `{P}` rather than with `Pi.single` or
`LinearMap.single`: the latter two carry a `DecidableEq` argument, and no instance supplies a
decidable equality of places, whereas `Set.indicator` is deliberately noncomputable and needs
none.  `TauCeti.coe_singleRepartition` together with `Set.indicator_singleton` recovers the
`Pi.single` form wherever a decidable equality is at hand.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.7.
-/

public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### Repartitions supported at a single place -/

/-- A family with a single nonzero entry is a repartition: its exceptional set is contained in
the singleton carrying that entry. -/
private theorem indicator_singleton_mem_repartitionSpace (P : Place k F) (x : F) :
    Set.indicator {P} (fun _ ↦ x) ∈ repartitionSpace k F := by
  rw [mem_repartitionSpace_iff_finite]
  refine (Set.finite_singleton P).subset fun Q hQ ↦ ?_
  by_contra hne
  exact hQ (by simp [Set.indicator_of_notMem hne])

/-- The repartition `ι_P x` with the entry `x` at the place `P` and `0` at every other place
(Stichtenoth, Definition 1.7.1), as a `k`-linear map `F →ₗ[k] A_F`. -/
noncomputable def singleRepartition (P : Place k F) : F →ₗ[k] ↥(repartitionSpace k F) where
  toFun x := ⟨Set.indicator {P} (fun _ ↦ x), indicator_singleton_mem_repartitionSpace P x⟩
  map_add' x y := Subtype.ext <| funext fun Q ↦ by
    rcases eq_or_ne Q P with rfl | hQ
    · simp
    · simp [Set.indicator_of_notMem (fun h ↦ hQ (Set.mem_singleton_iff.mp h))]
  map_smul' c x := Subtype.ext <| funext fun Q ↦ by
    rcases eq_or_ne Q P with rfl | hQ
    · simp
    · simp [Set.indicator_of_notMem (fun h ↦ hQ (Set.mem_singleton_iff.mp h))]

/-- The entries of `ι_P x`: the definition of `TauCeti.singleRepartition`, unfolded. -/
theorem coe_singleRepartition (P : Place k F) (x : F) :
    ((singleRepartition P x : ↥(repartitionSpace k F)) : Place k F → F) =
      Set.indicator {P} (fun _ ↦ x) :=
  (rfl)

/-- The entry of `ι_P x` at `P` is `x`. -/
@[simp]
theorem singleRepartition_self (P : Place k F) (x : F) :
    ((singleRepartition P x : ↥(repartitionSpace k F)) : Place k F → F) P = x := by
  rw [coe_singleRepartition, Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl)]

/-- The entries of `ι_P x` away from `P` vanish. -/
@[simp]
theorem singleRepartition_of_ne {P Q : Place k F} (h : Q ≠ P) (x : F) :
    ((singleRepartition P x : ↥(repartitionSpace k F)) : Place k F → F) Q = 0 := by
  rw [coe_singleRepartition,
    Set.indicator_of_notMem (fun hQ ↦ h (Set.mem_singleton_iff.mp hQ))]

/-- `ι_P x` is bounded by `D` exactly when the pole of `x` at `P` is: at every other place its
entry is `0`, which every divisor bounds. -/
theorem singleRepartition_mem_adeleFiltration_iff {D : Divisor k F} {P : Place k F} {x : F} :
    ((singleRepartition P x : ↥(repartitionSpace k F)) : Place k F → F) ∈ adeleFiltration D ↔
      P.valuation x ≤ WithZero.exp (D.coeff P) := by
  rw [mem_adeleFiltration_iff]
  refine ⟨fun h ↦ by simpa using h P, fun h Q ↦ ?_⟩
  rcases eq_or_ne Q P with rfl | hQ
  · simpa using h
  · simp [singleRepartition_of_ne hQ]

/-- Multiplying `ι_P x` by a function multiplies its entry: `f · ι_P x = ι_P (f x)`. -/
@[simp]
theorem repartitionMul_singleRepartition (hF : IsFunctionField k F) (f : F) (P : Place k F)
    (x : F) : repartitionMul hF f (singleRepartition P x) = singleRepartition P (f * x) :=
  Subtype.ext <| funext fun Q ↦ by
    rcases eq_or_ne Q P with rfl | hQ
    · simp [coe_repartitionMul_apply]
    · simp [coe_repartitionMul_apply, singleRepartition_of_ne hQ]

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

/-- The local components of a multiple of a linear form: `(f · ω)_P x = ω_P (f x)`. -/
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

/-- **The local components of a Weil differential sum to it**, in the form carrying the finite set
outside which the terms vanish (Stichtenoth, Proposition 1.7.2).

Take a divisor `E` bounding the repartition `a`.  Off the support of `E - D` the entry `a P` is
already bounded by `D`, so `ι_P (a P)` lies in `A_F(D)` and `ω_P (a P) = 0`; and subtracting from
`a` the finitely many repartitions `ι_P (a P)` with `P` in that support leaves a repartition
bounded by `D`, which `ω` kills. -/
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
      simp only [coe_singleRepartition, Set.indicator_singleton, Finset.sum_pi_single]
      split_ifs <;> simp
    rw [hcoe]
    split_ifs with h
    · simp
    · exact hbound Q h
  have hzero := weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hω _ hsub
  rw [map_sub, map_sum, sub_eq_zero] at hzero
  simpa using hzero

/-- **The local components of a Weil differential vanish at all but finitely many places**
(Stichtenoth, Proposition 1.7.2). -/
theorem finite_support_repartitionDualComponent {ω : Module.Dual k ↥(repartitionSpace k F)}
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
