/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.SepClosed

/-!
# Split models for quadratic forms

A finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is isometric to a split model: hyperbolic dual-pairing
coordinates together with an at-most-one-dimensional standard remainder.

## Main definitions

* `TauCeti.QuadraticForm.SplitModel`: the coordinate module in a fixed dimension.
* `TauCeti.QuadraticForm.splitModelForm`: its dual-pairing quadratic form and standard remainder.

## Main results

* `TauCeti.QuadraticForm.splitModelForm_apply`: evaluation of the model form.
* `TauCeti.QuadraticForm.polar_splitModelForm`: the polar form of the split model.
* `TauCeti.QuadraticForm.finrank_splitModel` and
  `TauCeti.QuadraticForm.splitModelForm_nondegenerate`: its dimension and nondegeneracy.
* `TauCeti.QuadraticForm.isometryEquivSplitModelForm`: the isometry from any finite-dimensional
  nondegenerate form over a separably closed field to its split model.

This supplies the quadratic-space coordinates needed by the spin-representation roadmap. The
subsequent construction of maximal isotropic subspaces and the spinor action remains in the
representation-theory consumer.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
* `TauCeti.LinearAlgebra.QuadraticForm.SepClosed`, which supplies the classification used below.
-/

public section

open QuadraticMap

namespace TauCeti.QuadraticForm

noncomputable section

/-- The `n / 2`-dimensional coordinate space whose dual pairing forms the hyperbolic part of the
split model. -/
abbrev SplitHalf (R : Type*) (n : ℕ) := Fin (n / 2) → R

/-- The at-most-one-dimensional remainder in the split model of an `n`-dimensional form. -/
abbrev SplitRemainder (R : Type*) (n : ℕ) := Fin (n % 2) → R

/-- The underlying module of the uniform split model in dimension `n`. -/
abbrev SplitModel (R : Type*) [CommSemiring R] (n : ℕ) :=
  (Module.Dual R (SplitHalf R n) × SplitHalf R n) × SplitRemainder R n

/-- The `QuadraticForm.dualProd` pairing on the paired coordinates, together with the standard
sum-of-squares form on the remainder. -/
def splitModelForm (R : Type*) [CommSemiring R] (n : ℕ) :
    QuadraticForm R (SplitModel R n) :=
  (QuadraticForm.dualProd R (SplitHalf R n)).prod
    (QuadraticMap.weightedSumSquares R (1 : Fin (n % 2) → R))

/-- The split model form is the evaluation pairing plus the standard remainder square. -/
@[simp]
theorem splitModelForm_apply {R : Type*} [CommSemiring R]
    (n : ℕ) (x : SplitModel R n) :
    splitModelForm R n x = x.1.1 x.1.2 + ∑ i, x.2 i * x.2 i := by
  simp [splitModelForm, QuadraticMap.weightedSumSquares_apply]

/-- The polar form of the split model is the symmetric evaluation pairing plus twice the standard
remainder pairing. -/
@[simp]
theorem polar_splitModelForm {R : Type*} [CommRing R]
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

private theorem associated_splitModelForm {R : Type*} [CommRing R] [Invertible (2 : R)]
    (n : ℕ) (x y : SplitModel R n) :
    QuadraticMap.associated (splitModelForm R n) x y =
      ⅟(2 : R) • (x.1.1 y.1.2 + y.1.1 x.1.2) + ∑ i, x.2 i * y.2 i := by
  rw [QuadraticMap.associated_apply, Module.End.smul_def, half_moduleEnd_apply_eq_half_smul,
    ← QuadraticMap.polar, polar_splitModelForm]
  simp only [smul_eq_mul]
  rw [mul_add, mul_add, invOf_mul_cancel_left]

private theorem associated_splitModelForm_separatingLeft {R : Type*} [CommRing R]
    [Invertible (2 : R)] (n : ℕ) :
    (QuadraticMap.associated (splitModelForm R n)).SeparatingLeft := by
  classical
  have invOf_smul_eq_zero (a : R) (ha : ⅟(2 : R) • a = 0) : a = 0 :=
    by simpa using invOf_smul_eq_iff.mp ha
  intro x hx
  rcases x with ⟨⟨f, u⟩, z⟩
  apply Prod.ext
  · apply Prod.ext
    · apply LinearMap.ext
      intro v
      have h := hx (((0 : Module.Dual R (SplitHalf R n)), v), 0)
      rw [associated_splitModelForm] at h
      exact invOf_smul_eq_zero _ (by simpa using h)
    · apply (Module.forall_dual_apply_eq_zero_iff R u).1
      intro g
      have h := hx (((g : Module.Dual R (SplitHalf R n)), 0), 0)
      rw [associated_splitModelForm] at h
      exact invOf_smul_eq_zero _ (by simpa using h)
  · funext i
    have h := hx (((0 : Module.Dual R (SplitHalf R n)), 0), Pi.single i 1)
    rw [associated_splitModelForm] at h
    simpa [Pi.single_apply] using h

/-- The split model has its advertised dimension. -/
@[simp high]
theorem finrank_splitModel {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    Module.finrank R (SplitModel R n) = n := by
  simp only [Module.finrank, rank_prod, Module.rank_linearMap_self, rank_pi, Module.rank_self,
    Cardinal.sum_const, Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast,
    Cardinal.lift_uzero, mul_one, Cardinal.lift_id]
  rw [Cardinal.toNat_add
      (Cardinal.add_lt_aleph0 Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0)
      Cardinal.natCast_lt_aleph0,
    Cardinal.toNat_add Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0]
  simp only [Cardinal.toNat_natCast]
  omega

/-- The split model form is nondegenerate. -/
theorem splitModelForm_nondegenerate {R : Type*} [CommRing R] [Invertible (2 : R)] (n : ℕ) :
    (splitModelForm R n).Nondegenerate :=
  (QuadraticMap.nondegenerate_associated_iff (Q := splitModelForm R n)).1 <|
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (QuadraticForm.associated_isSymm R (splitModelForm R n)).isRefl).2
        (associated_splitModelForm_separatingLeft n)

/-- Every finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is isometric to its split model form. -/
noncomputable def isometryEquivSplitModelForm [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Q.IsometryEquiv (splitModelForm K (Module.finrank K V)) := by
  have hQ' := equivalent_weightedSumSquares_of_isSepClosed Q
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).2 hQ).1
  have hModel' :
      (splitModelForm K (Module.finrank K V)).Equivalent
        (QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K V) → K)) := by
    have h := equivalent_weightedSumSquares_of_isSepClosed
      (splitModelForm K (Module.finrank K V))
      (associated_splitModelForm_separatingLeft (R := K) (Module.finrank K V))
    rw [finrank_splitModel] at h
    exact h
  exact hQ'.some.trans hModel'.some.symm

end

end TauCeti.QuadraticForm
