/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Split models for quadratic forms

A finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is isometric to a split model: hyperbolic dual-pairing
coordinates together with an at-most-one-dimensional standard remainder.

## Main definitions

* `TauCeti.QuadraticForm.SplitModel`: the coordinate module in a fixed dimension.
* `TauCeti.QuadraticForm.splitModelForm`: its dual-pairing quadratic form and standard remainder.

## Main results

* `TauCeti.QuadraticForm.splitModelForm_polar_apply`: the polar form of the split model.
* `TauCeti.QuadraticForm.finrank_splitModel` and
  `TauCeti.QuadraticForm.splitModelForm_nondegenerate`: its structural facts.
* `TauCeti.QuadraticForm.isometryEquivSplitModelForm`: the isometry from any finite-dimensional
  nondegenerate form over a separably closed field to its split model.

This supplies the quadratic-space coordinates needed by the spin-representation roadmap. The
subsequent construction of maximal isotropic subspaces and the spinor action remains in the
representation-theory consumer.

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

/-- The paired-coordinate space in the split model of an `n`-dimensional form. -/
abbrev SplitHalf (K : Type*) (n : ℕ) := Fin (n / 2) → K

/-- The at-most-one-dimensional remainder in the split model of an `n`-dimensional form. -/
abbrev SplitRemainder (K : Type*) (n : ℕ) := Fin (n % 2) → K

/-- The underlying module of the uniform split model in dimension `n`. -/
abbrev SplitModel (K : Type*) [CommSemiring K] (n : ℕ) :=
  (Module.Dual K (SplitHalf K n) × SplitHalf K n) × SplitRemainder K n

/-- The `QuadraticForm.dualProd` pairing on the paired coordinates, together with the standard
sum-of-squares form on the remainder. -/
def splitModelForm (K : Type*) [CommSemiring K] (n : ℕ) :
    QuadraticForm K (SplitModel K n) :=
  (QuadraticForm.dualProd K (SplitHalf K n)).prod
    (QuadraticMap.weightedSumSquares K (1 : Fin (n % 2) → K))

/-- The split model form is the evaluation pairing plus the standard remainder square. -/
@[simp]
theorem splitModelForm_apply {R : Type*} [CommSemiring R]
    (n : ℕ) (x : SplitModel R n) :
    splitModelForm R n x = x.1.1 x.1.2 + ∑ i, x.2 i * x.2 i := by
  simp [splitModelForm, QuadraticMap.weightedSumSquares_apply]

/-- The polar form of the split model is the symmetric evaluation pairing plus twice the standard
remainder pairing. -/
@[simp]
theorem splitModelForm_polar_apply {R : Type*} [CommRing R]
    (n : ℕ) (x y : SplitModel R n) :
    QuadraticMap.polar (splitModelForm R n) x y =
      x.1.1 y.1.2 + y.1.1 x.1.2 + 2 * ∑ i, x.2 i * y.2 i := by
  simp only [QuadraticMap.polar, splitModelForm_apply, Prod.fst_add, Prod.snd_add,
    LinearMap.add_apply, Pi.add_apply, map_add]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  have hxy : (∑ i, y.2 i * x.2 i) = ∑ i, x.2 i * y.2 i := by
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  rw [hxy]
  ring

variable {K V : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

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

/-- A nondegenerate quadratic form over a separably closed field of characteristic different from
two is equivalent to the standard sum-of-squares form. -/
theorem equivalent_weightedSumSquares_of_isSepClosed [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Q.Equivalent
      (QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K V) → K)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).2 hQ).1
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

/-- Two nondegenerate quadratic forms on the same finite-dimensional vector space over a
separably closed field of characteristic different from two are equivalent. -/
theorem equivalent_of_isSepClosed [IsSepClosed K]
    (Q₁ Q₂ : QuadraticForm K V) (hQ₁ : Q₁.Nondegenerate) (hQ₂ : Q₂.Nondegenerate) :
    Q₁.Equivalent Q₂ :=
  (equivalent_weightedSumSquares_of_isSepClosed Q₁ hQ₁).trans
    (equivalent_weightedSumSquares_of_isSepClosed Q₂ hQ₂).symm

private theorem splitModelForm_associated_apply {R : Type*} [CommRing R] [Invertible (2 : R)]
    (n : ℕ) (x y : SplitModel R n) :
    QuadraticMap.associated (splitModelForm R n) x y =
      ⅟(2 : R) • (x.1.1 y.1.2 + y.1.1 x.1.2) + ∑ i, x.2 i * y.2 i := by
  rw [QuadraticMap.associated_apply]
  -- `associated_apply` expands definitionally to this polar expression.
  change ⅟(2 : R) • QuadraticMap.polar (splitModelForm R n) x y = _
  rw [splitModelForm_polar_apply]
  simp only [smul_eq_mul]
  rw [mul_add, mul_add, invOf_mul_cancel_left]

private theorem splitModelForm_associated_separatingLeft {R : Type*} [CommRing R]
    [Invertible (2 : R)] (n : ℕ) :
    (QuadraticMap.associated (splitModelForm R n)).SeparatingLeft := by
  classical
  intro x hx
  rcases x with ⟨⟨f, u⟩, z⟩
  apply Prod.ext
  · apply Prod.ext
    · apply LinearMap.ext
      intro v
      have h := hx (((0 : Module.Dual R (SplitHalf R n)), v), 0)
      rw [splitModelForm_associated_apply] at h
      have h' : ⅟(2 : R) • f v = 0 := by
        simpa using h
      simpa using (invOf_smul_eq_iff.mp h')
    · apply (Module.forall_dual_apply_eq_zero_iff R u).1
      intro g
      have h := hx (((g : Module.Dual R (SplitHalf R n)), 0), 0)
      rw [splitModelForm_associated_apply] at h
      have h' : ⅟(2 : R) • g u = 0 := by
        simpa using h
      simpa using (invOf_smul_eq_iff.mp h')
  · funext i
    have h := hx (((0 : Module.Dual R (SplitHalf R n)), 0), Pi.single i 1)
    rw [splitModelForm_associated_apply] at h
    simpa [Pi.single_apply] using h

omit [Invertible (2 : K)] in
/-- The split model has its advertised dimension. -/
theorem finrank_splitModel (n : ℕ) :
    Module.finrank K (SplitModel K n) = n := by
  simp only [SplitModel, SplitHalf, SplitRemainder, Module.finrank_prod,
    Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

/-- The split model form is nondegenerate. -/
theorem splitModelForm_nondegenerate {R : Type*} [CommRing R] [Invertible (2 : R)] (n : ℕ) :
    (splitModelForm R n).Nondegenerate :=
  (QuadraticMap.nondegenerate_associated_iff (Q := splitModelForm R n)).1 <|
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (QuadraticForm.associated_isSymm R (splitModelForm R n)).isRefl).2
        (splitModelForm_associated_separatingLeft n)

/-- Every finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is isometric to its split model form. -/
noncomputable def isometryEquivSplitModelForm [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Q.IsometryEquiv (splitModelForm K (Module.finrank K V)) := by
  let n := Module.finrank K V
  let hQ' := equivalent_weightedSumSquares_of_isSepClosed Q hQ
  have hModel' : (splitModelForm K n).Equivalent
      (QuadraticMap.weightedSumSquares K (1 : Fin n → K)) := by
    have h := equivalent_weightedSumSquares_of_isSepClosed (splitModelForm K n)
      (splitModelForm_nondegenerate n)
    rw [finrank_splitModel] at h
    exact h
  exact hQ'.some.trans hModel'.some.symm

end

end TauCeti.QuadraticForm
