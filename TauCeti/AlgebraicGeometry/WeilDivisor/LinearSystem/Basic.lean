/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic

/-!
# Complete linear systems of Weil divisors

This file adds the **complete linear system** `|D|` of a Weil divisor to the Jacobian roadmap's
Layer A, on top of the formal Weil divisor group
(`TauCeti.AlgebraicGeometry.WeilDivisor.Basic`) and the principal divisors and divisor class group
of an order system (`TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic`).

For an `OrderSystem S` on a type of points `X`, the complete linear system of a divisor `D` is
the set of *effective* divisors linearly equivalent to `D`:

`|D| = { E | E effective and E ∼ D }`.

Classically `|D|` is the set of effective divisors of the form `D + div f` for a rational
function `f` with `D + div f ≥ 0`; its members are the effective divisors in the linear
equivalence class of `D`, and the associated projective space is `ℙ(L(D))` for the
Riemann–Roch space `L(D)`. The vector-space structure of `L(D)` is Layer B and needs coherent
cohomology, so it is deliberately not built here; this file supplies the set `|D|`, its
description in terms of principal divisors, and the facts that make it well behaved: it depends
only on the divisor class of `D`, every member shares the class and hence (when principal
divisors have degree zero) the degree of `D`, a divisor of negative degree has empty linear
system, and a degree-zero divisor has only the zero effective representative.

This advances the Tau Ceti Jacobian roadmap, Layer A, "Divisors on a curve" and "Degree":
`TauCetiRoadmap/JacobianChallenge/README.md`. It reuses Tau Ceti's existing `WeilDivisor` and
`OrderSystem` API and Mathlib's `Set` and quotient-group machinery; no external mathematics is
vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-- The **complete linear system** `|D|` of a Weil divisor `D` with respect to an order system
`S`: the set of effective divisors linearly equivalent to `D`.

Classically these are the divisors `D + div f` for a rational function `f` with `D + div f`
effective; see `mem_completeLinearSystem_iff_exists_principalDivisor`. -/
def completeLinearSystem (D : WeilDivisor X) : Set (WeilDivisor X) :=
  {E | IsEffective E ∧ S.LinearlyEquivalent D E}

@[simp]
lemma mem_completeLinearSystem {D E : WeilDivisor X} :
    E ∈ S.completeLinearSystem D ↔ IsEffective E ∧ S.LinearlyEquivalent D E :=
  Iff.rfl

lemma isEffective_of_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) : IsEffective E :=
  hE.1

lemma linearlyEquivalent_of_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) : S.LinearlyEquivalent D E :=
  hE.2

/-- An effective divisor lies in its own complete linear system. -/
lemma self_mem_completeLinearSystem {D : WeilDivisor X} (hD : IsEffective D) :
    D ∈ S.completeLinearSystem D :=
  ⟨hD, LinearlyEquivalent.refl S D⟩

/-- Membership in the complete linear system in terms of the divisor class: `|D|` consists of
the effective divisors whose class equals that of `D`. -/
lemma mem_completeLinearSystem_iff_divisorClass {D E : WeilDivisor X} :
    E ∈ S.completeLinearSystem D ↔ IsEffective E ∧ S.divisorClass D = S.divisorClass E := by
  rw [mem_completeLinearSystem]
  exact and_congr_right fun _ => S.divisorClass_eq_iff.symm

/-- Every member of `|D|` has the same divisor class as `D`. -/
lemma divisorClass_eq_of_mem_completeLinearSystem {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) : S.divisorClass E = S.divisorClass D :=
  ((S.mem_completeLinearSystem_iff_divisorClass.mp hE).2).symm

/-- The classical description of the complete linear system: its members are exactly the
effective divisors `D + div g` obtained from `D` by adding a principal divisor. -/
lemma mem_completeLinearSystem_iff_exists_principalDivisor {D E : WeilDivisor X} :
    E ∈ S.completeLinearSystem D ↔ IsEffective E ∧ ∃ g, E = D + S.principalDivisor g := by
  rw [mem_completeLinearSystem]
  refine and_congr_right fun _ => ?_
  rw [S.linearlyEquivalent_iff_exists_principalDivisor]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨-g, ?_⟩
    rw [S.principalDivisor_neg, hg, ← sub_eq_add_neg, sub_sub_cancel]
  · rintro ⟨g, hg⟩
    refine ⟨-g, ?_⟩
    rw [S.principalDivisor_neg, hg, sub_add_cancel_left]

/-- The complete linear system depends only on the divisor class: linearly equivalent divisors
have the same complete linear system. -/
lemma completeLinearSystem_eq_of_divisorClass_eq {D D' : WeilDivisor X}
    (h : S.divisorClass D = S.divisorClass D') :
    S.completeLinearSystem D = S.completeLinearSystem D' := by
  ext E
  rw [mem_completeLinearSystem_iff_divisorClass, mem_completeLinearSystem_iff_divisorClass, h]

/-- The complete linear systems of linearly equivalent divisors coincide. -/
lemma completeLinearSystem_eq_of_linearlyEquivalent {D D' : WeilDivisor X}
    (h : S.LinearlyEquivalent D D') :
    S.completeLinearSystem D = S.completeLinearSystem D' :=
  S.completeLinearSystem_eq_of_divisorClass_eq (S.divisorClass_eq_iff.mpr h)

/-- The complete linear system of the zero divisor consists of the effective principal
divisors. -/
lemma mem_completeLinearSystem_zero {E : WeilDivisor X} :
    E ∈ S.completeLinearSystem 0 ↔ IsEffective E ∧ ∃ g, E = S.principalDivisor g := by
  rw [mem_completeLinearSystem_iff_exists_principalDivisor]
  simp

/-! ### Degree along a complete linear system

When principal divisors have weighted degree zero (the geometric fact that a rational function
has as many zeros as poles, counted with residue-field degrees), the weighted degree is
constant on a complete linear system, so a negative-degree divisor has none. -/

/-- When principal divisors have weighted degree zero, every member of `|D|` has the same
weighted degree as `D`. -/
lemma weightedDegree_eq_of_mem_completeLinearSystem {w : X → ℤ} (h : S.IsWeightedDegreeZero w)
    {D E : WeilDivisor X} (hE : E ∈ S.completeLinearSystem D) :
    weightedDegree w E = weightedDegree w D := by
  have hcl : S.divisorClass D = S.divisorClass E :=
    (S.mem_completeLinearSystem_iff_divisorClass.mp hE).2
  rw [← weightedDegreeClass_divisorClass w h E, ← hcl, weightedDegreeClass_divisorClass w h D]

/-- With nonnegative weights and weighted-degree-zero principal divisors, a divisor of negative
weighted degree has empty complete linear system. -/
lemma completeLinearSystem_eq_empty_of_weightedDegree_neg {w : X → ℤ} (hw : ∀ x, 0 ≤ w x)
    (h : S.IsWeightedDegreeZero w) {D : WeilDivisor X} (hD : weightedDegree w D < 0) :
    S.completeLinearSystem D = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro E hE
  have hEeff : IsEffective E := (S.mem_completeLinearSystem.mp hE).1
  have hdeg : weightedDegree w E = weightedDegree w D :=
    S.weightedDegree_eq_of_mem_completeLinearSystem h hE
  have hpos : 0 ≤ weightedDegree w E := hEeff.weightedDegree_nonneg hw
  rw [hdeg] at hpos
  exact absurd hD (not_lt.mpr hpos)

/-- With positive weights and weighted-degree-zero principal divisors, every member of the
complete linear system of a weighted-degree-zero divisor is zero. -/
lemma eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero {w : X → ℤ}
    (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w) {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (hD : weightedDegree w D = 0) : E = 0 := by
  have hEeff : IsEffective E := S.isEffective_of_mem_completeLinearSystem hE
  have hdeg : weightedDegree w E = 0 := by
    rw [S.weightedDegree_eq_of_mem_completeLinearSystem h hE, hD]
  exact hEeff.eq_zero_of_weightedDegree_eq_zero_of_pos hw hdeg

/-- With positive weights and weighted-degree-zero principal divisors, membership in the
complete linear system of a weighted-degree-zero divisor is equivalent to being the zero divisor
and the divisor class being zero. -/
lemma mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D E : WeilDivisor X} (hD : weightedDegree w D = 0) :
    E ∈ S.completeLinearSystem D ↔ E = 0 ∧ S.divisorClass D = 0 := by
  constructor
  · intro hE
    have hE0 : E = 0 :=
      S.eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero hw h hE hD
    refine ⟨hE0, ?_⟩
    have hclass := (S.mem_completeLinearSystem_iff_divisorClass.mp hE).2
    simpa [hE0] using hclass
  · rintro ⟨rfl, hclass⟩
    exact S.mem_completeLinearSystem_iff_divisorClass.mpr ⟨isEffective_zero, by simpa using hclass⟩

/-- With positive weights and weighted-degree-zero principal divisors, membership in the
complete linear system of a weighted-degree-zero divisor is equivalent to being zero and
linearly equivalent to zero. -/
lemma mem_completeLinearSystem_iff_eq_zero_and_linearlyEquivalent_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D E : WeilDivisor X} (hD : weightedDegree w D = 0) :
    E ∈ S.completeLinearSystem D ↔ E = 0 ∧ S.LinearlyEquivalent D 0 := by
  rw [S.mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_weightedDegree_zero
    hw h hD, ← S.divisorClass_eq_iff]
  simp

/-- With positive weights and weighted-degree-zero principal divisors, nonemptiness of the
complete linear system of a weighted-degree-zero divisor is equivalent to the divisor class
being zero. -/
lemma nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.divisorClass D = 0 := by
  constructor
  · rintro ⟨E, hE⟩
    exact (S.mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_weightedDegree_zero
      hw h hD).mp hE |>.2
  · intro hclass
    refine ⟨0, ?_⟩
    exact (S.mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_weightedDegree_zero
      hw h hD).mpr ⟨rfl, hclass⟩

/-- With positive weights and weighted-degree-zero principal divisors, the complete linear system
of `D` is `{0}` exactly when its divisor class is zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_isWeightedDegreeZero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w) {D : WeilDivisor X} :
    S.completeLinearSystem D = {0} ↔ S.divisorClass D = 0 := by
  constructor
  · intro hset
    have h0 : (0 : WeilDivisor X) ∈ S.completeLinearSystem D := by
      rw [hset]
      simp
    simpa using (S.mem_completeLinearSystem_iff_divisorClass.mp h0).2
  · intro hclass
    have hD : weightedDegree w D = 0 := by
      rw [← weightedDegreeClass_divisorClass w h D, hclass, map_zero]
    apply Set.Subset.antisymm
    · intro E hE
      rw [Set.mem_singleton_iff]
      exact S.eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero hw h hE hD
    · rw [Set.singleton_subset_iff]
      exact (S.mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_weightedDegree_zero
        hw h hD).mpr ⟨rfl, hclass⟩

/-- With positive weights and weighted-degree-zero principal divisors, the complete linear system
of `D` is `{0}` exactly when `D` is linearly equivalent to zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_linearlyEquivalent_zero_of_isWeightedDegreeZero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w) {D : WeilDivisor X} :
    S.completeLinearSystem D = {0} ↔ S.LinearlyEquivalent D 0 := by
  rw [S.completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_isWeightedDegreeZero
    hw h, ← S.divisorClass_eq_iff]
  simp

/-- With positive weights and weighted-degree-zero principal divisors, a weighted-degree-zero
divisor has a nonempty complete linear system exactly when it is linearly equivalent to zero. -/
lemma nonempty_completeLinearSystem_iff_linearlyEquivalent_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.LinearlyEquivalent D 0 := by
  rw [S.nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero hw h hD,
    ← S.divisorClass_eq_iff]
  simp

/-- When principal divisors have unweighted degree zero, every member of `|D|` has the same
unweighted degree as `D`. -/
lemma degree_eq_of_mem_completeLinearSystem (h : S.IsUnweightedDegreeZero)
    {D E : WeilDivisor X} (hE : E ∈ S.completeLinearSystem D) : degree E = degree D := by
  have hcl : S.divisorClass D = S.divisorClass E :=
    (S.mem_completeLinearSystem_iff_divisorClass.mp hE).2
  rw [← unweightedDegreeClass_divisorClass h E, ← hcl, unweightedDegreeClass_divisorClass h D]

/-- With unweighted-degree-zero principal divisors, a divisor of negative degree has empty
complete linear system. -/
lemma completeLinearSystem_eq_empty_of_degree_neg (h : S.IsUnweightedDegreeZero)
    {D : WeilDivisor X} (hD : degree D < 0) : S.completeLinearSystem D = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro E hE
  have hEeff : IsEffective E := (S.mem_completeLinearSystem.mp hE).1
  have hdeg : degree E = degree D := S.degree_eq_of_mem_completeLinearSystem h hE
  have hpos : 0 ≤ degree E := hEeff.degree_nonneg
  rw [hdeg] at hpos
  exact absurd hD (not_lt.mpr hpos)

/-- In the unweighted theory, every member of the complete linear system of a degree-zero
divisor is zero. -/
lemma eq_zero_of_mem_completeLinearSystem_of_degree_zero (h : S.IsUnweightedDegreeZero)
    {D E : WeilDivisor X} (hE : E ∈ S.completeLinearSystem D) (hD : degree D = 0) : E = 0 := by
  exact S.eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h hE (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- Assuming unweighted-degree-zero principal divisors, membership in the complete linear system
of a degree-zero divisor is equivalent to being the zero divisor and the divisor class being
zero. -/
lemma mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D E : WeilDivisor X} (hD : degree D = 0) :
    E ∈ S.completeLinearSystem D ↔ E = 0 ∧ S.divisorClass D = 0 := by
  exact S.mem_completeLinearSystem_iff_eq_zero_and_divisorClass_eq_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- Assuming unweighted-degree-zero principal divisors, membership in the complete linear system
of a degree-zero divisor is equivalent to being zero and linearly equivalent to zero. -/
lemma mem_completeLinearSystem_iff_eq_zero_and_linearlyEquivalent_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D E : WeilDivisor X} (hD : degree D = 0) :
    E ∈ S.completeLinearSystem D ↔ E = 0 ∧ S.LinearlyEquivalent D 0 := by
  exact S.mem_completeLinearSystem_iff_eq_zero_and_linearlyEquivalent_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- Assuming unweighted-degree-zero principal divisors, a degree-zero divisor has a nonempty
complete linear system exactly when its divisor class is zero. -/
lemma nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} (hD : degree D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.divisorClass D = 0 := by
  exact S.nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- Assuming unweighted-degree-zero principal divisors, the complete linear system of `D` is
`{0}` exactly when its divisor class is zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_principal_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} :
    S.completeLinearSystem D = {0} ↔ S.divisorClass D = 0 :=
  S.completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_isWeightedDegreeZero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h

/-- Assuming unweighted-degree-zero principal divisors, the complete linear system of `D` is
`{0}` exactly when it is linearly equivalent to zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_linearlyEquivalent_zero_of_principal_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} :
    S.completeLinearSystem D = {0} ↔ S.LinearlyEquivalent D 0 :=
  S.completeLinearSystem_eq_singleton_zero_iff_linearlyEquivalent_zero_of_isWeightedDegreeZero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h

/-- Assuming unweighted-degree-zero principal divisors, a degree-zero divisor has a nonempty
complete linear system exactly when it is linearly equivalent to zero. -/
lemma nonempty_completeLinearSystem_iff_linearlyEquivalent_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} (hD : degree D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.LinearlyEquivalent D 0 := by
  exact S.nonempty_completeLinearSystem_iff_linearlyEquivalent_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- A complete linear system is nonempty exactly when the divisor class of `D` contains an
effective divisor. -/
lemma nonempty_completeLinearSystem_iff {D : WeilDivisor X} : (S.completeLinearSystem D).Nonempty ↔
      ∃ E, IsEffective E ∧ S.divisorClass E = S.divisorClass D := by
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨E, hE.1, S.divisorClass_eq_of_mem_completeLinearSystem hE⟩
  · rintro ⟨E, hEeff, hcl⟩
    exact ⟨E, S.mem_completeLinearSystem_iff_divisorClass.mpr ⟨hEeff, hcl.symm⟩⟩

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
