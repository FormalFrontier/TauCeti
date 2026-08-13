/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Basic

/-!
# Analytic points, the analytic locus, and emptiness of `Spa(A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.39 and Proposition 7.49.**

This file formalizes the analytic locus of the adic spectrum `Spa(A, A⁺)` and the emptiness
criterion for `Spa(A, A⁺)`.

## Main definitions

* `TauCeti.ValuationSpectrum.IsAnalyticPoint` : a point `v : Spv A` is *analytic* if its support
  `v.supp` is not an open ideal of `A`.
* `TauCeti.ValuationSpectrum.spaAnalytic` : **Wedhorn's `Spa(A, A⁺)ᵃ`**, the analytic locus of
  `Spa(A, A⁺)` as a `Set (Spv A)`.

## Main results

* `TauCeti.ValuationSpectrum.isClosed_setOfPred_forall_vle_zero` : demanding `v(a) ≤ 0` at every
  `a ∈ S` cuts out a closed subset of `Spv A`.
* `TauCeti.ValuationSpectrum.cont_eq_empty_of_one_mem_closure_zero` : if `1 ∈ closure {0}` in a
  topological ring `A`, then `Cont A = ∅`.
* `TauCeti.ValuationSpectrum.spa_eq_empty_of_one_mem_closure_zero` : if `1 ∈ closure {0}` in a
  topological ring `A`, then `Spa(A, A⁺) = ∅` for any plus ring `A⁺`
  (Wedhorn Proposition 7.49(1)).
* `TauCeti.ValuationSpectrum.spa_eq_empty_of_subsingleton` : over a zero ring `A`, `Spa(A, A⁺) = ∅`.
* `TauCeti.ValuationSpectrum.not_isOpen_of_isPrime` : in a Tate ring, no prime ideal is open.
* `TauCeti.ValuationSpectrum.isAnalyticPoint_of_isTateRing` : **Wedhorn Proposition 7.49(2)**,
  over a Tate ring every point of `Spv A` (and hence `Spa(A, A⁺)`) is analytic.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_spa_of_isTateRing` : for a Tate ring `A`, the
  analytic locus is the entire adic spectrum `spaAnalytic Aplus = spa Aplus`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.39 and Proposition 7.49.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber TauCeti.Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Analytic points of `Spv A` (Wedhorn Definition 7.39).** A point `v : Spv A` is *analytic*
if its support `v.supp` is not an open ideal of `A`. -/
def IsAnalyticPoint (v : Spv A) : Prop :=
  ¬ IsOpen (v.supp : Set A)

/-- **Wedhorn's Analytic Locus `Spa(A, A⁺)ᵃ`**: the subset of `spa Aplus` consisting of analytic
points (Definition 7.39). -/
def spaAnalytic (Aplus : Subring A) : Set (Spv A) :=
  spa Aplus ∩ {v : Spv A | IsAnalyticPoint v}

/-- The set-level characterization of the analytic locus. -/
theorem spaAnalytic_def (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus ∩ {v : Spv A | IsAnalyticPoint v} := (rfl)

/-- Membership in the analytic locus: `v ∈ Spa(A, A⁺)ᵃ` iff `v ∈ Spa(A, A⁺)` and `v` is an
analytic point. -/
@[simp]
theorem mem_spaAnalytic_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spaAnalytic Aplus ↔ v ∈ spa Aplus ∧ IsAnalyticPoint v := by
  rw [spaAnalytic_def, Set.mem_inter_iff, Set.mem_ofPred_eq]

/-- The analytic locus is contained in the adic spectrum. -/
theorem spaAnalytic_subset_spa (Aplus : Subring A) :
    spaAnalytic Aplus ⊆ spa Aplus :=
  spaAnalytic_def Aplus ▸ Set.inter_subset_left

omit [TopologicalSpace A] in
/-- **The locus of points where `v(a) ≤ 0` for all `a ∈ S` is closed in `Spv A`.** The complement
is the union over `a ∈ S` of the basic opens `Spv(A)(a/a)` = `{v | ¬ v(a) ≤ 0}`. -/
theorem isClosed_setOfPred_forall_vle_zero (S : Set A) :
    IsClosed {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vle a 0} := by
  rw [← isOpen_compl_iff]
  have h : {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vle a 0}ᶜ = ⋃ a ∈ S, basicOpen a a := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, Set.mem_iUnion,
      mem_basicOpen_iff, exists_prop]
    refine ⟨fun ⟨a, haS, h0⟩ ↦ ⟨a, haS, v.toValuativeRel.vle_refl a, h0⟩,
      fun ⟨a, haS, _, h0⟩ ↦ ⟨a, haS, h0⟩⟩
  rw [h]
  exact isOpen_biUnion fun a _ ↦ isOpen_basicOpen a a

section TopologicalRing

variable [IsTopologicalRing A]

/-- **Wedhorn Proposition 7.49(1) (forward direction).** If `1 ∈ closure {0}` in a topological
ring `A`, then `Cont A = ∅`. -/
theorem cont_eq_empty_of_one_mem_closure_zero (h : (1 : A) ∈ closure ({0} : Set A)) :
    cont A = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false, mem_cont_iff]
  intro hv
  have h_open : IsOpen {a : A | v.valuation a < 1} := by
    have h1 : v.valuation 1 = 1 := v.valuation.map_one
    have hcont : v.valuation.IsContinuous := (isContinuous_def v).mp hv
    rw [← h1]
    exact Valuation.isContinuous_def.mp hcont 1
  have h_sub_open : IsOpen {a : A | v.valuation (a - 1) < 1} :=
    h_open.preimage (continuous_sub_right 1)
  have h1_mem : (1 : A) ∈ {a : A | v.valuation (a - 1) < 1} := by
    simp only [Set.mem_ofPred_eq, sub_self, Valuation.map_zero]
    exact zero_lt_one
  have h0_mem : (0 : A) ∈ {a : A | v.valuation (a - 1) < 1} := by
    obtain ⟨x, hx_sub, hx_zero⟩ := mem_closure_iff.mp h _ h_sub_open h1_mem
    rw [Set.mem_singleton_iff] at hx_zero
    subst hx_zero
    exact hx_sub
  rw [Set.mem_ofPred_eq, zero_sub, Valuation.map_neg] at h0_mem
  have h1_val : v.valuation 1 = 1 := v.valuation.map_one
  rw [h1_val] at h0_mem
  exact lt_irrefl 1 h0_mem

/-- **Wedhorn Proposition 7.49(1) (forward direction for `Spa`).** If `1 ∈ closure {0}` in a
topological ring `A`, then `Spa (A, A⁺) = ∅` for any plus ring `A⁺`. -/
theorem spa_eq_empty_of_one_mem_closure_zero (Aplus : Subring A)
    (h : (1 : A) ∈ closure ({0} : Set A)) : spa Aplus = ∅ := by
  rw [spa_def, cont_eq_empty_of_one_mem_closure_zero h, Set.empty_inter]

/-- Over a zero ring, `Cont A = ∅`. -/
theorem cont_eq_empty_of_subsingleton [Subsingleton A] : cont A = ∅ :=
  cont_eq_empty_of_one_mem_closure_zero (by simp [Subsingleton.elim (1 : A) 0])

/-- Over a zero ring, `Spa (A, A⁺) = ∅`. -/
@[simp]
theorem spa_eq_empty_of_subsingleton [Subsingleton A] (Aplus : Subring A) :
    spa Aplus = ∅ :=
  spa_eq_empty_of_one_mem_closure_zero Aplus (by simp [Subsingleton.elim (1 : A) 0])

/-- Over a zero ring, the analytic locus `Spa (A, A⁺)ᵃ` is empty. -/
@[simp]
theorem spaAnalytic_eq_empty_of_subsingleton [Subsingleton A] (Aplus : Subring A) :
    spaAnalytic Aplus = ∅ := by
  rw [spaAnalytic_def, spa_eq_empty_of_subsingleton, Set.empty_inter]

end TopologicalRing

section TateRing

variable [IsTopologicalRing A] [IsTateRing A]

/-- **In a Tate ring, no prime ideal is open.** A Tate ring contains a topologically nilpotent
unit `ϖ`. If a prime ideal `I` were open, it would contain some power `ϖⁿ`, hence `ϖ` itself
(by primality), hence `1` (since `ϖ` is a unit), making `I = ⊤`, contradicting `I` being prime. -/
theorem not_isOpen_of_isPrime (I : Ideal A) [hI : I.IsPrime] :
    ¬ IsOpen (I : Set A) := by
  intro hopen
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  have hnhds : (I : Set A) ∈ nhds (0 : A) := hopen.mem_nhds I.zero_mem
  obtain ⟨n, hn⟩ := hϖ.isTopologicallyNilpotent.exists_pow_mem_of_mem_nhds hnhds
  have hϖ_mem : ϖ ∈ I := hI.mem_of_pow_mem n hn
  have hone_mem : (1 : A) ∈ I := by
    obtain ⟨u, hu⟩ := hϖ.isUnit
    have h1 : (1 : A) = ↑u⁻¹ * ϖ := by
      rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [h1]
    exact Ideal.mul_mem_left I (↑u⁻¹) hϖ_mem
  exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr hone_mem)

/-- **Wedhorn Proposition 7.49(2).** Over a Tate ring, every point of `Spv A` is analytic. -/
theorem isAnalyticPoint_of_isTateRing (v : Spv A) : IsAnalyticPoint v :=
  not_isOpen_of_isPrime v.supp

/-- **Wedhorn Proposition 7.49(2).** Over a Tate ring, the analytic locus is the entire adic
spectrum: `Spa (A, A⁺)ᵃ = Spa (A, A⁺)`. -/
@[simp]
theorem spaAnalytic_eq_spa_of_isTateRing (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus := by
  ext v
  simp [mem_spaAnalytic_iff, isAnalyticPoint_of_isTateRing v]

end TateRing

end TauCeti.ValuationSpectrum
