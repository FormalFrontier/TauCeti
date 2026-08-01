/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.FixedDegree
public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Basic

/-!
# Abel-Jacobi fibers and complete linear systems

This file records the formal fixed-degree fiber statement for the divisor-class shadow of the
Abel-Jacobi map.  The existing map

`D ↦ [D - deg(D) • [x₀]] ∈ Pic⁰`

is defined on all Weil divisors as `OrderSystem.weightedAbelJacobiDivisorClass`.  On effective
divisors of a fixed degree, two divisors have the same normalized Abel-Jacobi class exactly when
they are linearly equivalent; equivalently, one lies in the complete linear system of the other.
The same statement is restated for Mathlib's symmetric powers through the existing equivalence
between `Sym X d` and effective divisors of degree `d`.

This is the formal-divisor version of the classical fact that the fibers of the Abel map
`Symᵈ X → Pic⁰ X`, `D ↦ 𝒪_X(D - d·x₀)`, are complete linear systems.  It advances
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer C/D, the symmetric-power Abel-map lane
`D ↦ 𝒪_X(D - d·x₀)`, using the abstract divisor class group available before line bundles,
the Picard scheme, or the Jacobian variety exist.  No external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

noncomputable section

/-! ### Fixed-degree effective divisors -/

variable {d : ℕ}

/-- For effective divisors of the same fixed degree, equality of normalized Abel-Jacobi
classes is exactly linear equivalence of the underlying divisors. -/
lemma weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_linearlyEquivalent
    (h : S.IsUnweightedDegreeZero) (x₀ : X) (D E : EffectiveDivisorOfDegree X d) :
    S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
        (D : WeilDivisor X) =
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (E : WeilDivisor X) ↔
      S.LinearlyEquivalent (D : WeilDivisor X) E := by
  refine S.weightedAbelJacobiDivisorClass_one_eq_iff_linearlyEquivalent_of_degree_eq
    h x₀ ?_
  rw [D.degree_eq, E.degree_eq]

/-- The fixed-degree Abel-Jacobi fiber through `D` is the complete linear system `|D|`, restricted
to effective divisors of the same degree. -/
lemma weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem
    (h : S.IsUnweightedDegreeZero) (x₀ : X) (D E : EffectiveDivisorOfDegree X d) :
    S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
        (E : WeilDivisor X) =
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (D : WeilDivisor X) ↔
      (E : WeilDivisor X) ∈ S.completeLinearSystem (D : WeilDivisor X) := by
  rw [S.weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_linearlyEquivalent
    h x₀ E D, S.mem_completeLinearSystem]
  constructor
  · intro hlin
    exact ⟨E.isEffective, hlin.symm⟩
  · exact fun hE => hE.2.symm

/-- As a set of fixed-degree effective divisors, the Abel-Jacobi fiber through `D` is the
restriction of the complete linear system `|D|`. -/
lemma setOf_weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq
    (h : S.IsUnweightedDegreeZero) (x₀ : X) (D : EffectiveDivisorOfDegree X d) :
    {E : EffectiveDivisorOfDegree X d |
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (E : WeilDivisor X) =
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (D : WeilDivisor X)} =
      {E : EffectiveDivisorOfDegree X d |
        (E : WeilDivisor X) ∈ S.completeLinearSystem (D : WeilDivisor X)} := by
  ext E
  exact
    S.weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem
      h x₀ D E

/-! ### Symmetric powers -/

/-- On symmetric powers, equality of normalized Abel-Jacobi classes is exactly membership of the
corresponding divisor in the complete linear system. -/
lemma weightedAbelJacobiDivisorClass_one_ofSym_eq_iff_mem_completeLinearSystem
    (h : S.IsUnweightedDegreeZero) (x₀ : X) (s t : Sym X d) :
    S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
        (EffectiveDivisorOfDegree.ofSym t : WeilDivisor X) =
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (EffectiveDivisorOfDegree.ofSym s : WeilDivisor X) ↔
      (EffectiveDivisorOfDegree.ofSym t : WeilDivisor X) ∈
        S.completeLinearSystem (EffectiveDivisorOfDegree.ofSym s : WeilDivisor X) :=
  S.weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem
    h x₀ (EffectiveDivisorOfDegree.ofSym s) (EffectiveDivisorOfDegree.ofSym t)

/-- As a set of symmetric-power points, the Abel-Jacobi fiber through `s` is the preimage of the
complete linear system `|ofSym s|`. -/
lemma setOf_weightedAbelJacobiDivisorClass_one_ofSym_eq
    (h : S.IsUnweightedDegreeZero) (x₀ : X) (s : Sym X d) : {t : Sym X d |
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (EffectiveDivisorOfDegree.ofSym t : WeilDivisor X) =
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl
          (EffectiveDivisorOfDegree.ofSym s : WeilDivisor X)} =
      {t : Sym X d |
        (EffectiveDivisorOfDegree.ofSym t : WeilDivisor X) ∈
          S.completeLinearSystem (EffectiveDivisorOfDegree.ofSym s : WeilDivisor X)} := by
  ext t
  exact S.weightedAbelJacobiDivisorClass_one_ofSym_eq_iff_mem_completeLinearSystem h x₀ s t

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
