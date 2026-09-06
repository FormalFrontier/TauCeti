/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic

/-!
# Herbrand quotients of finite cyclic group representations

For a representation `M` of a finite cyclic group, its Herbrand quotient is the quotient of the
orders of `H-hat^0(G, M)` and `H-hat^(-1)(G, M)`. This file defines it directly on Mathlib's
Tate-cohomology carrier, on top of the low-degree descriptions

`H-hat^0(G, M) = M^G / N M` and `H-hat^(-1)(G, M) = ker(N) / I_G M`,

and proves its two base calculations: the quotient is `1` for a finite module, and it is `|G|`
for the trivial integral representation.

The proofs are adapted to Mathlib's current Tate complex from the corresponding calculations in
`ClassFieldTheory/Cohomology/FiniteCyclic/HerbrandQuotient/{Defs,Finite,Trivial}.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`. The trivial
integral calculation reads off the low-degree evaluations
`natCard_tateCohomology_zero_trivial_int_eq_card` and
`subsingleton_tateCohomology_negOne_trivial_int`.

## Main definitions

* `TauCeti.TateCohomology.herbrandQuotient` is the Herbrand quotient.
* `TauCeti.TateCohomology.herbrandQuotient_eq_one_of_finite` computes it for a finite module.
* `TauCeti.TateCohomology.herbrandQuotient_trivial_int_eq_card` computes it for trivial integral
  coefficients.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, section 4.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IX, section 4.
-/

public noncomputable section

universe u

open CategoryTheory groupCohomology groupHomology LinearMap Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The Herbrand quotient, the order of degree-zero Tate cohomology divided by the order of
degree `-1` Tate cohomology. Classically the invariant is only defined when both Tate groups are
finite; this definition is totalized by `Nat.card`, which is `0` on an infinite type, so together
with division by zero it returns `0` as soon as either group is infinite. The definition makes
sense for any finite group; periodicity makes it useful for cyclic groups. -/
def herbrandQuotient (M : Rep R G) : ℚ :=
  Nat.card (tateCohomology M 0) / Nat.card (tateCohomology M (-1))

/-- The Herbrand quotient vanishes exactly when one of its two defining Tate groups is infinite. -/
@[simp]
theorem herbrandQuotient_eq_zero_iff {M : Rep R G} :
    herbrandQuotient M = 0 ↔
      Infinite (tateCohomology M 0) ∨ Infinite (tateCohomology M (-1)) := by
  simp [herbrandQuotient, Nat.card_eq_zero]

/-- The Herbrand quotient is nonzero exactly when its two defining Tate groups are finite. This is
not `@[simp]`: `herbrandQuotient_eq_zero_iff` already normalizes the negated form. -/
theorem herbrandQuotient_ne_zero_iff {M : Rep R G} :
    herbrandQuotient M ≠ 0 ↔
      Finite (tateCohomology M 0) ∧ Finite (tateCohomology M (-1)) := by
  simp [herbrandQuotient, Nat.card_eq_zero]

/-- The Herbrand quotient of a finite representation of a finite cyclic group is one. -/
@[simp]
theorem herbrandQuotient_eq_one_of_finite [IsCyclic G] (M : Rep R G) [Finite M] :
    herbrandQuotient M = 1 := by
  let hgen := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let g := hgen.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x ↦
    hgen.choose_spec.ge (Subgroup.mem_top x)
  let D : Module.End R M := M.ρ g - LinearMap.id
  have hinv : M.ρ.invariants = ker D := by
    ext x
    simpa only [D, mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using
      (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x)
  have hcoinv : Representation.Coinvariants.ker M.ρ = range D := by
    simpa only [D] using Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg
  have hnorm_le : range M.ρ.norm ≤ M.ρ.invariants := by
    rintro _ ⟨x, rfl⟩
    exact fun a ↦ M.ρ.self_norm_apply a x
  have hzero :
      Nat.card M.ρ.invariants =
        Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
    calc
      Nat.card M.ρ.invariants =
          Nat.card ((range M.ρ.norm).submoduleOf M.ρ.invariants) *
            Nat.card (M.ρ.invariants ⧸
              (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe hnorm_le).toEquiv,
          ← Nat.card_congr (H0IsoNormQuotient M).toLinearEquiv.toEquiv]
  have hnegone :
      Nat.card (ker M.ρ.norm) =
        Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
    calc
      Nat.card (ker M.ρ.norm) =
          Nat.card ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) *
            Nat.card (ker M.ρ.norm ⧸
              (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe (by
          rw [← range_d₁₀_eq_coinvariantsKer]
          exact LinearMap.range_le_ker_iff.mpr
            (ModuleCat.hom_ext_iff.mp (Rep.comp_eq_zero M)))).toEquiv,
          ← Nat.card_congr (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv]
  have hnorm :
      Nat.card M = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := by
    calc
      Nat.card M = Nat.card (ker M.ρ.norm) * Nat.card (M ⧸ ker M.ρ.norm) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := by
        rw [Nat.card_congr M.ρ.norm.quotKerEquivRange.toEquiv]
  have hdiff : Nat.card M = Nat.card (ker D) * Nat.card (range D) := by
    calc
      Nat.card M = Nat.card (ker D) * Nat.card (M ⧸ ker D) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (ker D) * Nat.card (range D) := by
        rw [Nat.card_congr D.quotKerEquivRange.toEquiv]
  have hrangeNorm : 0 < Nat.card (range M.ρ.norm) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hrangeDiff : 0 < Nat.card (range D) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hcard : Nat.card (tateCohomology M 0) = Nat.card (tateCohomology M (-1)) := by
    apply Nat.mul_right_cancel (Nat.mul_pos hrangeNorm hrangeDiff)
    calc
      Nat.card (tateCohomology M 0) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) =
          (Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0)) *
            Nat.card (range D) := by ac_rfl
      _ = Nat.card (ker D) * Nat.card (range D) := by rw [← hzero, hinv]
      _ = Nat.card M := hdiff.symm
      _ = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := hnorm
      _ = (Nat.card (range D) * Nat.card (tateCohomology M (-1))) *
          Nat.card (range M.ρ.norm) := by rw [hnegone, hcoinv]
      _ = Nat.card (tateCohomology M (-1)) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) := by ac_rfl
  have hfiniteQuotient : Finite (ker M.ρ.norm ⧸
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
    Finite.of_surjective (Submodule.mkQ _ ) (Submodule.mkQ_surjective _)
  have hfiniteNegOne : Finite (tateCohomology M (-1)) :=
    (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv.finite_iff.mpr hfiniteQuotient
  rw [herbrandQuotient, hcard]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨0⟩, hfiniteNegOne⟩))

section TrivialInt

variable (H : Type) [Group H] [Fintype H]

/-- The Herbrand quotient of the trivial integral representation is the order of the finite
group. -/
@[simp]
theorem herbrandQuotient_trivial_int_eq_card :
    herbrandQuotient (Rep.trivial ℤ H ℤ) = Nat.card H := by
  let hsub := subsingleton_tateCohomology_negOne_trivial_int H
  rw [herbrandQuotient, natCard_tateCohomology_zero_trivial_int_eq_card]
  rw [@Nat.card_of_subsingleton _ 0 hsub]
  simp

end TrivialInt

end TauCeti.TateCohomology
