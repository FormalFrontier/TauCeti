/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Hyperbolic decomposition of quadratic forms

A finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is a sum of hyperbolic planes and at most one square.

## Main result

* `TauCeti.QuadraticForm.hyperbolicDecomposition`: the isometric equivalence with the uniform
  hyperbolic model in every dimension.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
* `Mathlib.LinearAlgebra.QuadraticForm.AlgClosed`, whose square-root normalization argument is
  adapted below from algebraically closed to separably closed fields.
-/

public section

open QuadraticMap

namespace TauCeti.QuadraticForm

noncomputable section

variable {K V : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The half-dimensional coordinate space in the hyperbolic model of an `n`-dimensional form. -/
abbrev hyperbolicHalf (K : Type*) (n : ℕ) := Fin (n / 2) → K

/-- The at-most-one-dimensional remainder in the hyperbolic model of an `n`-dimensional form. -/
abbrev hyperbolicRemainder (K : Type*) (n : ℕ) := Fin (n % 2) → K

/-- The underlying module of the uniform hyperbolic model in dimension `n`. -/
abbrev hyperbolicModel (K : Type*) [CommSemiring K] (n : ℕ) :=
  (Module.Dual K (hyperbolicHalf K n) × hyperbolicHalf K n) × hyperbolicRemainder K n

/-- The product of `n / 2` hyperbolic planes and the standard `n % 2`-dimensional form. -/
def hyperbolicModelForm (K : Type*) [CommSemiring K] (n : ℕ) :
    QuadraticForm K (hyperbolicModel K n) :=
  (QuadraticForm.dualProd K (hyperbolicHalf K n)).prod
    (QuadraticMap.weightedSumSquares K (1 : Fin (n % 2) → K))

/-- The hyperbolic model is the evaluation pairing plus the standard remainder square. -/
@[simp]
theorem hyperbolicModelForm_apply {R : Type*} [CommSemiring R]
    (n : ℕ) (x : hyperbolicModel R n) :
    hyperbolicModelForm R n x = x.1.1 x.1.2 + ∑ i, x.2 i * x.2 i := by
  simp [hyperbolicModelForm, QuadraticMap.weightedSumSquares_apply]

private def isometryEquivSumSquaresUnits [IsSepClosed K] {I : Type*} [Fintype I]
    (w : I → Kˣ) :
    (QuadraticMap.weightedSumSquares K fun i ↦ (w i : K)).IsometryEquiv
      (QuadraticMap.weightedSumSquares K (1 : I → K)) := by
  classical
  refine QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ Units.mk0 (IsSepClosed.exists_eq_mul_self (w i : K)).choose ?_) ?_
  · rw [← mul_self_eq_zero.ne, ← (IsSepClosed.exists_eq_mul_self (w i : K)).choose_spec]
    exact (w i).ne_zero
  · intro i
    simp [pow_two, ← (IsSepClosed.exists_eq_mul_self (w i : K)).choose_spec]

private theorem equivalentSumSquares [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Q.Equivalent
      (QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K V) → K)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).2 hQ).1
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

private theorem hyperbolicModelForm_associated_separatingLeft (n : ℕ) :
    (QuadraticMap.associated (hyperbolicModelForm K n)).SeparatingLeft := by
  classical
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  intro x hx
  rcases x with ⟨⟨f, u⟩, z⟩
  apply Prod.ext
  · apply Prod.ext
    · apply LinearMap.ext
      intro v
      have h := hx (((0 : Module.Dual K (hyperbolicHalf K n)), v), 0)
      simpa [hyperbolicModelForm, QuadraticMap.associated_apply, QuadraticMap.polar, htwo] using h
    · have hu : u = 0 := by
        apply (Module.forall_dual_apply_eq_zero_iff K u).1
        intro g
        have h := hx (((g : Module.Dual K (hyperbolicHalf K n)), 0), 0)
        simpa [hyperbolicModelForm, QuadraticMap.associated_apply, QuadraticMap.polar, htwo] using h
      exact hu
  · funext i
    have h := hx (((0 : Module.Dual K (hyperbolicHalf K n)), 0), Pi.single i 1)
    have hsum (w : Fin (n % 2) → K) : ∑ j, w j = w i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exfalso
        apply hji
        apply Fin.ext
        have hi_lt := i.isLt
        have hj_lt := j.isLt
        have hm := Nat.mod_lt n (by decide : 0 < 2)
        omega
      · simp
    simp only [hyperbolicModelForm, QuadraticMap.associated_apply, QuadraticMap.prod_apply,
      QuadraticForm.dualProd_apply, add_zero, QuadraticMap.weightedSumSquares_apply,
      Prod.fst_add, Prod.snd_add, map_zero, hsum] at h
    simp only [Pi.one_apply, Pi.add_apply, Pi.single_apply, if_pos, zero_add,
      smul_eq_mul] at h
    ring_nf at h
    simpa [smul_eq_mul, mul_comm (z i) (2 : K), ← mul_assoc] using h

omit [Invertible (2 : K)] in
private theorem finrank_hyperbolicModel (n : ℕ) :
    Module.finrank K (hyperbolicModel K n) = n := by
  simp [hyperbolicModel, hyperbolicHalf, hyperbolicRemainder, Subspace.dual_finrank_eq]
  omega

/-- Every finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is a sum of hyperbolic planes and at most one square. -/
noncomputable def hyperbolicDecomposition [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Q.IsometryEquiv (hyperbolicModelForm K (Module.finrank K V)) := by
  let n := Module.finrank K V
  let hQ' := equivalentSumSquares Q hQ
  have hAssociated :
      (QuadraticMap.associated (hyperbolicModelForm K n)).Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (QuadraticForm.associated_isSymm K (hyperbolicModelForm K n)).isRefl).2
        (hyperbolicModelForm_associated_separatingLeft n)
  have hModel : (hyperbolicModelForm K n).Nondegenerate :=
    (QuadraticMap.nondegenerate_associated_iff (Q := hyperbolicModelForm K n)).1 hAssociated
  have hModel' : (hyperbolicModelForm K n).Equivalent
      (QuadraticMap.weightedSumSquares K (1 : Fin n → K)) := by
    have h := equivalentSumSquares (hyperbolicModelForm K n) hModel
    rw [finrank_hyperbolicModel] at h
    exact h
  exact hQ'.some.trans hModel'.some.symm

end

end TauCeti.QuadraticForm
