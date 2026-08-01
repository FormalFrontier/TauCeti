/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Indicator
public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic

/-!
# Finite sums of point divisors

This file adds an API for the effective Weil divisors represented by finitely supported
natural-number multiplicities and by named finite-set constructors. These are the formal
Layer A divisor objects that later receive geometric restrictions from symmetric powers and
relative effective divisors: before any scheme-level construction exists, a finite collection
of points gives the divisor `Σ nₓ[x]`.

The API records the coefficient, support, degree, weighted degree, pushforward, and degree-zero
normal forms needed by the existing Abel-Jacobi and linear-system files.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve:
Weil divisors `⊕_x ℤ`" and "Degree", and supplies a clean formal prerequisite for the Layer C/D
Abel-map lane `D ↦ 𝒪_X(D - d·x₀)` from symmetric powers. No external mathematics is vendored;
the proofs use Tau Ceti's `WeilDivisor.ofPoint`, `degree`, `weightedDegree`, and `pushforward`
API together with Mathlib's finite-sum lemmas.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

/-! ### Finitely supported multiplicities -/

/-- Every Weil divisor is the finite sum of its coefficients times point divisors over its
support. -/
lemma eq_sum_coeff_smul_ofPoint (D : WeilDivisor X) :
    D = ∑ x ∈ D.support, coeff D x • ofPoint x := by
  simp only [← single_eq_zsmul_ofPoint]
  exact (Finsupp.sum_single D).symm

/-- The Weil divisor associated to finitely supported natural-number multiplicities. -/
noncomputable def ofFinsupp (m : X →₀ ℕ) : WeilDivisor X :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m

/-- Coefficients of the divisor from finitely supported natural multiplicities are the
multiplicities. -/
@[simp]
lemma coeff_ofFinsupp (m : X →₀ ℕ) (x : X) :
    coeff (ofFinsupp m : WeilDivisor X) x = m x := by
  simp [ofFinsupp, coeff]

/-- Finitely supported natural multiplicities give effective divisors. -/
@[simp]
lemma isEffective_ofFinsupp (m : X →₀ ℕ) : IsEffective (ofFinsupp m : WeilDivisor X) := by
  rw [isEffective_iff]
  intro x
  simp

/-- The support of a divisor from finitely supported natural multiplicities is the support of
those multiplicities. -/
@[simp]
lemma support_ofFinsupp (m : X →₀ ℕ) : (ofFinsupp m : WeilDivisor X).support = m.support :=
  Finsupp.support_mapRange_of_injective (by simp) m Nat.cast_injective

/-- A divisor from finitely supported multiplicities is the corresponding sum of point divisors
over the support. -/
lemma ofFinsupp_eq_sum (m : X →₀ ℕ) :
    ofFinsupp m = ∑ x ∈ m.support, (m x : ℤ) • ofPoint x := by
  conv_lhs => rw [eq_sum_coeff_smul_ofPoint (ofFinsupp m)]
  simp

/-- The degree of a divisor from finitely supported multiplicities is the sum over the support. -/
@[simp]
lemma degree_ofFinsupp (m : X →₀ ℕ) :
    degree (ofFinsupp m : WeilDivisor X) = ∑ x ∈ m.support, (m x : ℤ) := by
  classical
  simp [ofFinsupp_eq_sum]

/-- The weighted degree of a divisor from finitely supported multiplicities is the weighted sum over
the support. -/
@[simp]
lemma weightedDegree_ofFinsupp (w : X → ℤ) (m : X →₀ ℕ) :
    weightedDegree w (ofFinsupp m : WeilDivisor X) =
      ∑ x ∈ m.support, (m x : ℤ) * w x := by
  classical
  simp [ofFinsupp_eq_sum, mul_comm]

/-- Pushing forward a divisor from finitely supported multiplicities applies the map to each point
in the support sum. -/
@[simp]
lemma pushforward_ofFinsupp (f : X → Y) (m : X →₀ ℕ) :
    pushforward f (ofFinsupp m : WeilDivisor X) =
      ∑ x ∈ m.support, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [ofFinsupp_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights on the support, a divisor from finitely supported multiplicities has
weighted degree zero exactly when all multiplicities vanish. -/
lemma weightedDegree_ofFinsupp_eq_zero_iff_of_pos
    (m : X →₀ ℕ) {w : X → ℤ} (hw : ∀ x ∈ m.support, 0 < w x) :
    weightedDegree w (ofFinsupp m : WeilDivisor X) = 0 ↔ m = 0 := by
  constructor
  · intro hdeg
    have hzero : (ofFinsupp m : WeilDivisor X) = 0 :=
      IsEffective.eq_zero_of_weightedDegree_eq_zero_of_pos_on_support
        (isEffective_ofFinsupp m) (by simpa using hw) hdeg
    ext x
    have hcoeff := congrArg (fun D : WeilDivisor X => coeff D x) hzero
    simpa using hcoeff
  · intro hm
    simp [hm]

/-- With positive weights on the support, a divisor from finitely supported multiplicities lies in
the weighted degree-zero subgroup exactly when all multiplicities vanish. -/
lemma ofFinsupp_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (m : X →₀ ℕ) {w : X → ℤ} (hw : ∀ x ∈ m.support, 0 < w x) :
    (ofFinsupp m : WeilDivisor X) ∈ weightedDegreeZeroSubgroup w ↔ m = 0 := by
  rw [mem_weightedDegreeZeroSubgroup, weightedDegree_ofFinsupp_eq_zero_iff_of_pos m hw]

/-- A divisor from finitely supported multiplicities has unweighted degree zero exactly when all
multiplicities vanish. -/
lemma ofFinsupp_mem_degreeZeroSubgroup_iff (m : X →₀ ℕ) :
    (ofFinsupp m : WeilDivisor X) ∈ degreeZeroSubgroup X ↔ m = 0 := by
  rw [mem_degreeZeroSubgroup, ← weightedDegree_one_eq_degree]
  exact weightedDegree_ofFinsupp_eq_zero_iff_of_pos
    (w := fun _ : X => (1 : ℤ)) m (fun _ _ => zero_lt_one)

/-! ### Named finite-set constructors -/

/-- The Weil divisor supported on a finite set with prescribed natural multiplicities. -/
noncomputable def ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) : WeilDivisor X :=
  Finsupp.indicator s (fun x _ => (m x : ℤ))

/-- Coefficients of the named finite-set divisor with prescribed multiplicities. -/
@[simp]
lemma coeff_ofFinsetWithMultiplicity [DecidableEq X] (s : Finset X) (m : X → ℕ) (x : X) :
    coeff (ofFinsetWithMultiplicity s m : WeilDivisor X) x = if x ∈ s then m x else 0 := by
  simp [ofFinsetWithMultiplicity, coeff, Finsupp.indicator_apply]

/-- The named finite-set divisor with multiplicities is the corresponding finite sum of point
divisors. -/
lemma ofFinsetWithMultiplicity_eq_sum (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m = ∑ x ∈ s, (m x : ℤ) • ofPoint x := by
  refine (Finsupp.indicator_eq_sum_single s fun x => (m x : ℤ)).trans ?_
  simp only [single_eq_zsmul_ofPoint]

/-- The named finite-set divisor with multiplicities over the empty set is zero. -/
@[simp]
lemma ofFinsetWithMultiplicity_empty (m : X → ℕ) :
    ofFinsetWithMultiplicity (∅ : Finset X) m = (0 : WeilDivisor X) := by
  simp [ofFinsetWithMultiplicity_eq_sum]

/-- Inserting a new point in a named finite-set divisor splits off its weighted point divisor. -/
@[simp]
lemma ofFinsetWithMultiplicity_insert [DecidableEq X] {s : Finset X} {x : X}
    (hx : x ∉ s) (m : X → ℕ) :
    ofFinsetWithMultiplicity (insert x s) m =
      (m x : ℤ) • ofPoint x + ofFinsetWithMultiplicity s m := by
  simp [ofFinsetWithMultiplicity_eq_sum, Finset.sum_insert hx]

/-- A named finite-set divisor with natural multiplicities is effective. -/
@[simp]
lemma isEffective_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    IsEffective (ofFinsetWithMultiplicity s m : WeilDivisor X) := by
  classical
  rw [isEffective_iff]
  intro x
  rw [coeff_ofFinsetWithMultiplicity]
  split_ifs <;> simp

/-- A named finite-set divisor with natural multiplicities belongs to the effective divisor
submonoid. -/
lemma ofFinsetWithMultiplicity_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinsetWithMultiplicity s m)

/-- The support of a named finite-set divisor with multiplicities is contained in the chosen
finite set. Points in the set whose multiplicity is zero may drop out of the support. -/
lemma support_ofFinsetWithMultiplicity_subset (s : Finset X) (m : X → ℕ) :
    (ofFinsetWithMultiplicity s m : WeilDivisor X).support ⊆ s :=
  Finsupp.support_indicator_subset s (fun x _ => (m x : ℤ))

/-- A point is in the support of a named finite-set divisor with multiplicities exactly when it
is selected and has nonzero multiplicity. -/
lemma mem_support_ofFinsetWithMultiplicity_iff {s : Finset X} {m : X → ℕ} {x : X} :
    x ∈ (ofFinsetWithMultiplicity s m : WeilDivisor X).support ↔ x ∈ s ∧ m x ≠ 0 := by
  classical
  rw [mem_support_iff, coeff_ofFinsetWithMultiplicity]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The degree of a named finite-set divisor with multiplicities is the sum of the
multiplicities. -/
@[simp]
lemma degree_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    degree (ofFinsetWithMultiplicity s m : WeilDivisor X) = ∑ x ∈ s, (m x : ℤ) := by
  classical
  simp [ofFinsetWithMultiplicity_eq_sum]

/-- The weighted degree of a named finite-set divisor with multiplicities is the corresponding
weighted finite sum. -/
@[simp]
lemma weightedDegree_ofFinsetWithMultiplicity (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  classical
  simp [ofFinsetWithMultiplicity_eq_sum, mul_comm]

/-- Pushing forward a named finite-set divisor with multiplicities applies the map to each
point in the finite sum. -/
@[simp]
lemma pushforward_ofFinsetWithMultiplicity (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (ofFinsetWithMultiplicity s m : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [ofFinsetWithMultiplicity_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights at selected points with nonzero multiplicity, a named finite-set
divisor has weighted degree zero exactly when every selected multiplicity vanishes. -/
lemma weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos
    (s : Finset X) {w : X → ℤ} (m : X → ℕ) (hw : ∀ x ∈ s, m x ≠ 0 → 0 < w x) :
    weightedDegree w (ofFinsetWithMultiplicity s m : WeilDivisor X) = 0 ↔
      ∀ x ∈ s, m x = 0 := by
  classical
  constructor
  · intro hdeg x hx
    have hzero : (ofFinsetWithMultiplicity s m : WeilDivisor X) = 0 :=
      IsEffective.eq_zero_of_weightedDegree_eq_zero_of_pos_on_support
        (isEffective_ofFinsetWithMultiplicity s m)
        (fun y hy => by
          obtain ⟨hys, hmy⟩ := mem_support_ofFinsetWithMultiplicity_iff.mp hy
          exact hw y hys hmy)
        hdeg
    have hcoeff := congrArg (fun D : WeilDivisor X => coeff D x) hzero
    simpa [hx] using hcoeff
  · intro hm
    rw [weightedDegree_ofFinsetWithMultiplicity]
    exact Finset.sum_eq_zero fun x hx => by simp [hm x hx]

/-- With positive weights at selected points with nonzero multiplicity, a named finite-set
divisor lies in the weighted degree-zero subgroup exactly when all selected multiplicities
vanish. -/
lemma ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (m : X → ℕ) (hw : ∀ x ∈ s, m x ≠ 0 → 0 < w x) :
    (ofFinsetWithMultiplicity s m : WeilDivisor X) ∈ weightedDegreeZeroSubgroup w ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_weightedDegreeZeroSubgroup,
    weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos s m hw]

/-- A named finite-set divisor with multiplicities has unweighted degree zero exactly when every
selected multiplicity vanishes. -/
lemma ofFinsetWithMultiplicity_mem_degreeZeroSubgroup_iff (s : Finset X) (m : X → ℕ) :
    (ofFinsetWithMultiplicity s m : WeilDivisor X) ∈ degreeZeroSubgroup X ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_degreeZeroSubgroup, ← weightedDegree_one_eq_degree]
  exact weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos
    (w := fun _ : X => (1 : ℤ)) s m (fun _ _ _ => zero_lt_one)

/-! ### Named coefficient-one finite-set constructors -/

/-- The Weil divisor with coefficient `1` on each point of a finite set. -/
noncomputable def ofFinset (s : Finset X) : WeilDivisor X :=
  ofFinsetWithMultiplicity s fun _ => 1

/-- The named coefficient-one finite-set divisor is the corresponding finite sum of point
divisors. -/
lemma ofFinset_eq_sum (s : Finset X) :
    ofFinset s = ∑ x ∈ s, ofPoint x := by
  simpa [ofFinset] using ofFinsetWithMultiplicity_eq_sum s fun _ => 1

/-- The named coefficient-one finite-set divisor over the empty set is zero. -/
@[simp]
lemma ofFinset_empty : ofFinset (∅ : Finset X) = (0 : WeilDivisor X) :=
  ofFinsetWithMultiplicity_empty fun _ => 1

/-- Inserting a new point in a named coefficient-one finite-set divisor splits off its point
divisor. -/
@[simp]
lemma ofFinset_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s) :
    ofFinset (insert x s) = ofPoint x + ofFinset s := by
  simpa [ofFinset] using ofFinsetWithMultiplicity_insert hx fun _ => 1

/-- Coefficients of the named coefficient-one finite-set divisor are `1` on the set and `0` off
it. -/
@[simp]
lemma coeff_ofFinset [DecidableEq X] (s : Finset X) (x : X) :
    coeff (ofFinset s : WeilDivisor X) x = if x ∈ s then 1 else 0 := by
  simp [ofFinset]

/-- The named coefficient-one finite-set divisor is effective. -/
@[simp]
lemma isEffective_ofFinset (s : Finset X) : IsEffective (ofFinset s : WeilDivisor X) :=
  isEffective_ofFinsetWithMultiplicity s fun _ => 1

/-- The named coefficient-one finite-set divisor belongs to the effective divisor submonoid. -/
lemma ofFinset_mem_effectiveSubmonoid (s : Finset X) :
    ofFinset s ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinset s)

/-- The support of the named coefficient-one finite-set divisor is exactly the chosen finite
set. -/
@[simp]
lemma support_ofFinset (s : Finset X) : (ofFinset s : WeilDivisor X).support = s := by
  ext x
  simp only [ofFinset, mem_support_ofFinsetWithMultiplicity_iff]
  simp

/-- The degree of the named coefficient-one finite-set divisor is the finite set's cardinality. -/
@[simp]
lemma degree_ofFinset (s : Finset X) : degree (ofFinset s : WeilDivisor X) = s.card := by
  simp [ofFinset]

/-- The weighted degree of the named coefficient-one finite-set divisor is the sum of weights on
it. -/
@[simp]
lemma weightedDegree_ofFinset (w : X → ℤ) (s : Finset X) :
    weightedDegree w (ofFinset s : WeilDivisor X) = ∑ x ∈ s, w x := by
  simp [ofFinset]

/-- Pushing forward the named coefficient-one finite-set divisor applies the map to each point. -/
@[simp]
lemma pushforward_ofFinset (f : X → Y) (s : Finset X) :
    pushforward f (ofFinset s : WeilDivisor X) = ∑ x ∈ s, ofPoint (f x) := by
  simp [ofFinset]

/-- For positive weights, a named coefficient-one finite-set divisor lies in the weighted
degree-zero subgroup exactly when the finite set is empty. -/
lemma ofFinset_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) :
    (ofFinset s : WeilDivisor X) ∈ weightedDegreeZeroSubgroup w ↔ s = ∅ :=
  (ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos s (fun _ => 1)
    fun x hx _ => hw x hx).trans (by simp [Finset.eq_empty_iff_forall_notMem])

/-- A named coefficient-one finite-set divisor has unweighted degree zero exactly when the set is
empty. -/
lemma ofFinset_mem_degreeZeroSubgroup_iff (s : Finset X) :
    (ofFinset s : WeilDivisor X) ∈ degreeZeroSubgroup X ↔ s = ∅ :=
  (ofFinsetWithMultiplicity_mem_degreeZeroSubgroup_iff s fun _ => 1).trans
    (by simp [Finset.eq_empty_iff_forall_notMem])

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti
