/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Existence of polarization data

This file constructs `TauCeti.SpinPolarizationData` for finite-dimensional nondegenerate
quadratic spaces over separably closed fields of characteristic different from two.

## Main definition

* `TauCeti.SpinPolarizationData.ofNondegenerate` constructs the data for a finite-dimensional
  nondegenerate quadratic space over a separably closed field of characteristic different from
  two.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
* Mathlib's `QuadraticForm.isometryEquivSumSquaresUnits` and
  `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` supply the normalization argument
  adapted below from algebraically closed to separably closed fields.
-/

public section

open QuadraticMap

namespace TauCeti

universe u v

namespace SpinPolarizationData

noncomputable section

private abbrev SplitHalf (R : Type*) (n : ℕ) := Fin (n / 2) → R

private abbrev SplitRemainder (R : Type*) (n : ℕ) := Fin (n % 2) → R

private abbrev SplitModel (R : Type*) [CommSemiring R] (n : ℕ) :=
  (Module.Dual R (SplitHalf R n) × SplitHalf R n) × SplitRemainder R n

private def splitModelForm (R : Type*) [CommSemiring R] (n : ℕ) :
    QuadraticForm R (SplitModel R n) :=
  (QuadraticForm.dualProd R (SplitHalf R n)).prod
    (QuadraticMap.weightedSumSquares R (1 : Fin (n % 2) → R))

@[simp]
private theorem splitModelForm_apply {R : Type*} [CommSemiring R]
    (n : ℕ) (x : SplitModel R n) :
    splitModelForm R n x = x.1.1 x.1.2 + ∑ i, x.2 i * x.2 i := by
  simp [splitModelForm, QuadraticMap.weightedSumSquares_apply]

@[simp]
private theorem polar_splitModelForm {R : Type*} [CommRing R]
    (n : ℕ) (x y : SplitModel R n) :
    QuadraticMap.polar (splitModelForm R n) x y =
      x.1.1 y.1.2 + y.1.1 x.1.2 + 2 * ∑ i, x.2 i * y.2 i := by
  rw [splitModelForm, QuadraticMap.polar_prod]
  simp only [QuadraticMap.polar, QuadraticForm.dualProd_apply,
    QuadraticMap.weightedSumSquares_apply, Prod.fst_add, Prod.snd_add, LinearMap.add_apply,
    Pi.add_apply, map_add, Pi.one_apply, one_smul]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  have hxy : (∑ i, y.2 i * x.2 i) = ∑ i, x.2 i * y.2 i := by
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  rw [hxy]
  ring

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

variable {K : Type u} [CommRing K]

private def modelW (n : ℕ) : Submodule K (SplitModel K n) :=
  ((⊥ : Submodule K (Module.Dual K (SplitHalf K n))).prod ⊤).prod ⊥

private def modelW' (n : ℕ) : Submodule K (SplitModel K n) :=
  ((⊤ : Submodule K (Module.Dual K (SplitHalf K n))).prod ⊥).prod ⊥

private def modelLine (n : ℕ) : Submodule K (SplitModel K n) :=
  (⊥ : Submodule K (Module.Dual K (SplitHalf K n) × SplitHalf K n)).prod ⊤

private theorem mem_modelW_iff (n : ℕ) (x : SplitModel K n) :
    x ∈ modelW (K := K) n ↔ x.1.1 = 0 ∧ x.2 = 0 := by
  simp [modelW]

private theorem mem_modelW'_iff (n : ℕ) (x : SplitModel K n) :
    x ∈ modelW' (K := K) n ↔ x.1.2 = 0 ∧ x.2 = 0 := by
  simp [modelW']

private theorem mem_modelLine_iff (n : ℕ) (x : SplitModel K n) :
    x ∈ modelLine (K := K) n ↔ x.1 = 0 := by
  simp [modelLine]

private def modelWEquivHalf (n : ℕ) :
    modelW (K := K) n ≃ₗ[K] SplitHalf K n where
  toFun x := x.1.1.2
  invFun u := ⟨((0, u), 0), by simp [modelW]⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨⟨f, u⟩, z⟩, hx⟩
    rw [mem_modelW_iff] at hx
    rcases hx with ⟨rfl, rfl⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def modelW'EquivDual (n : ℕ) :
    modelW' (K := K) n ≃ₗ[K] Module.Dual K (SplitHalf K n) where
  toFun x := x.1.1.1
  invFun f := ⟨((f, 0), 0), by simp [modelW']⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨⟨f, u⟩, z⟩, hx⟩
    rw [mem_modelW'_iff] at hx
    rcases hx with ⟨rfl, rfl⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def modelLineEquivRemainder (n : ℕ) :
    modelLine (K := K) n ≃ₗ[K] SplitRemainder K n where
  toFun x := x.1.2
  invFun z := ⟨((0, 0), z), by simp [modelLine]⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨p, z⟩, hx⟩
    rw [mem_modelLine_iff] at hx
    simp only at hx
    subst p
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def modelDecompositionEquiv (n : ℕ) :
    ((modelW (K := K) n × modelW' (K := K) n) × modelLine (K := K) n) ≃ₗ[K]
      SplitModel K n :=
  (((modelWEquivHalf (K := K) n).prodCongr (modelW'EquivDual (K := K) n)).prodCongr
      (modelLineEquivRemainder (K := K) n)).trans
    ((LinearEquiv.prodComm K _ _).prodCongr (LinearEquiv.refl K _))

@[simp]
private theorem modelDecompositionEquiv_apply (n : ℕ)
    (x : ((modelW (K := K) n × modelW' (K := K) n) × modelLine (K := K) n)) :
    modelDecompositionEquiv (K := K) n x = x.1.1 + x.1.2 + x.2 := by
  rcases x with ⟨⟨x, y⟩, z⟩
  rcases x with ⟨⟨⟨f, u⟩, w⟩, hx⟩
  rcases y with ⟨⟨⟨f', u'⟩, w'⟩, hy⟩
  rcases z with ⟨⟨p, z⟩, hz⟩
  rw [mem_modelW_iff] at hx
  rw [mem_modelW'_iff] at hy
  rw [mem_modelLine_iff] at hz
  simp only at hx hy hz
  rcases hx with ⟨rfl, rfl⟩
  rcases hy with ⟨rfl, rfl⟩
  subst p
  simp [modelDecompositionEquiv, modelWEquivHalf, modelW'EquivDual,
    modelLineEquivRemainder]

private noncomputable def modelPairingEquiv (n : ℕ) :
    modelW' (K := K) n ≃ₗ[K] Module.Dual K (modelW (K := K) n) :=
  (modelW'EquivDual (K := K) n).trans (modelWEquivHalf (K := K) n).dualMap

@[simp]
private theorem modelPairingEquiv_apply (n : ℕ) (y : modelW' (K := K) n)
    (x : modelW (K := K) n) :
    modelPairingEquiv (K := K) n y x =
      QuadraticMap.polar (splitModelForm K n) x y := by
  rcases x with ⟨⟨⟨f, u⟩, z⟩, hx⟩
  rcases y with ⟨⟨⟨f', u'⟩, z'⟩, hy⟩
  rw [mem_modelW_iff] at hx
  rw [mem_modelW'_iff] at hy
  simp only at hx hy
  rcases hx with ⟨rfl, rfl⟩
  rcases hy with ⟨rfl, rfl⟩
  simp [modelPairingEquiv, modelW'EquivDual, modelWEquivHalf, polar_splitModelForm]

private def remainderCoordinate (n : ℕ) : SplitRemainder K n →ₗ[K] K where
  toFun z := ∑ i, z i
  map_add' x y := by simpa using Finset.sum_add_distrib
  map_smul' a x := by simp [Finset.mul_sum]

private theorem remainderCoordinate_sq (n : ℕ) (z : SplitRemainder K n) :
    remainderCoordinate n z * remainderCoordinate n z = ∑ i, z i * z i := by
  classical
  let : Subsingleton (Fin (n % 2)) := ⟨fun i j ↦ Fin.ext (by omega)⟩
  cases isEmpty_or_nonempty (Fin (n % 2)) with
  | inl => simp [remainderCoordinate]
  | inr =>
      let i : Fin (n % 2) := Classical.choice inferInstance
      simp [remainderCoordinate, Fintype.sum_subsingleton z i,
        Fintype.sum_subsingleton (fun j ↦ z j * z j) i]

private theorem remainderCoordinate_injective (n : ℕ) :
    Function.Injective (remainderCoordinate (K := K) n) := by
  classical
  let : Subsingleton (Fin (n % 2)) := ⟨fun i j ↦ Fin.ext (by omega)⟩
  intro x y hxy
  cases isEmpty_or_nonempty (Fin (n % 2)) with
  | inl => exact Subsingleton.elim x y
  | inr =>
      funext i
      simpa [remainderCoordinate, Fintype.sum_subsingleton x i,
        Fintype.sum_subsingleton y i] using hxy

private def modelLineCoordinate (n : ℕ) : modelLine (K := K) n →ₗ[K] K :=
  (remainderCoordinate (K := K) n).comp (modelLineEquivRemainder (K := K) n).toLinearMap

private theorem modelLineCoordinate_sq (n : ℕ) (z : modelLine (K := K) n) :
    modelLineCoordinate (K := K) n z * modelLineCoordinate (K := K) n z =
      splitModelForm K n z := by
  rcases z with ⟨⟨p, z⟩, hz⟩
  rw [mem_modelLine_iff] at hz
  simp only at hz
  subst p
  simpa [modelLineCoordinate, modelLineEquivRemainder] using
    remainderCoordinate_sq (K := K) n z

private theorem modelLineCoordinate_injective (n : ℕ) :
    Function.Injective (modelLineCoordinate (K := K) n) :=
  (remainderCoordinate_injective (K := K) n).comp
    (modelLineEquivRemainder (K := K) n).injective

private noncomputable def modelData (n : ℕ) :
    SpinPolarizationData (splitModelForm K n) where
  W := modelW (K := K) n
  W' := modelW' (K := K) n
  line := modelLine (K := K) n
  decompositionEquiv := modelDecompositionEquiv (K := K) n
  decompositionEquiv_apply := modelDecompositionEquiv_apply (K := K) n
  isotropic_W x := by
    rcases x with ⟨⟨⟨f, u⟩, z⟩, hx⟩
    rw [mem_modelW_iff] at hx
    simp only at hx
    rcases hx with ⟨rfl, rfl⟩
    simp
  isotropic_W' y := by
    rcases y with ⟨⟨⟨f, u⟩, z⟩, hy⟩
    rw [mem_modelW'_iff] at hy
    simp only at hy
    rcases hy with ⟨rfl, rfl⟩
    simp
  pairingEquiv := modelPairingEquiv (K := K) n
  pairingEquiv_apply := modelPairingEquiv_apply (K := K) n
  pairing_separatingLeft x hx := by
    apply (modelWEquivHalf (K := K) n).injective
    apply (Module.forall_dual_apply_eq_zero_iff K (modelWEquivHalf (K := K) n x)).1
    intro f
    let y := (modelW'EquivDual (K := K) n).symm f
    calc
      f (modelWEquivHalf (K := K) n x) =
          modelPairingEquiv (K := K) n y x := by
            simp [y, modelPairingEquiv]
      _ = QuadraticMap.polar (splitModelForm K n) x y :=
        modelPairingEquiv_apply (K := K) n y x
      _ = 0 := hx y
  lineCoordinate := modelLineCoordinate (K := K) n
  lineCoordinate_injective := modelLineCoordinate_injective (K := K) n
  lineCoordinate_sq := modelLineCoordinate_sq (K := K) n
  line_orthogonal_W z x := by
    rcases z with ⟨⟨p, z⟩, hz⟩
    rcases x with ⟨⟨⟨f, u⟩, w⟩, hx⟩
    rw [mem_modelLine_iff] at hz
    rw [mem_modelW_iff] at hx
    simp only at hz hx
    subst p
    rcases hx with ⟨rfl, rfl⟩
    simp
  line_orthogonal_W' z y := by
    rcases z with ⟨⟨p, z⟩, hz⟩
    rcases y with ⟨⟨⟨f, u⟩, w⟩, hy⟩
    rw [mem_modelLine_iff] at hz
    rw [mem_modelW'_iff] at hy
    simp only at hz hy
    subst p
    rcases hy with ⟨rfl, rfl⟩
    simp

private noncomputable def pullback {V V' : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') (P : SpinPolarizationData Q') : SpinPolarizationData Q := by
  have hpolar (x y : V) : QuadraticMap.polar Q x y = QuadraticMap.polar Q' (e x) (e y) := by
    simp only [QuadraticMap.polar]
    rw [← e.map_app (x + y), ← e.map_app x, ← e.map_app y, map_add]
  let W := P.W.comap e.toLinearEquiv.toLinearMap
  let W' := P.W'.comap e.toLinearEquiv.toLinearMap
  let line := P.line.comap e.toLinearEquiv.toLinearMap
  have hRange (S : Submodule K V') : S ≤ LinearMap.range e.toLinearEquiv.toLinearMap := by
    intro x _
    exact ⟨e.toLinearEquiv.symm x, e.toLinearEquiv.apply_symm_apply x⟩
  let eW : W ≃ₗ[K] P.W :=
    Submodule.comap_equiv_self_of_inj_of_le e.toLinearEquiv.injective (hRange P.W)
  let eW' : W' ≃ₗ[K] P.W' :=
    Submodule.comap_equiv_self_of_inj_of_le e.toLinearEquiv.injective (hRange P.W')
  let eLine : line ≃ₗ[K] P.line :=
    Submodule.comap_equiv_self_of_inj_of_le e.toLinearEquiv.injective (hRange P.line)
  have eW_apply (x : W) : (eW x : V') = e x := by
    exact congrArg Subtype.val
      (Submodule.comap_equiv_self_of_inj_of_le_apply e.toLinearEquiv.injective (hRange P.W) x)
  have eW'_apply (x : W') : (eW' x : V') = e x := by
    exact congrArg Subtype.val
      (Submodule.comap_equiv_self_of_inj_of_le_apply e.toLinearEquiv.injective (hRange P.W') x)
  have eLine_apply (x : line) : (eLine x : V') = e x := by
    exact congrArg Subtype.val
      (Submodule.comap_equiv_self_of_inj_of_le_apply e.toLinearEquiv.injective (hRange P.line) x)
  let decomp : ((W × W') × line) ≃ₗ[K] V :=
    ((eW.prodCongr eW').prodCongr eLine).trans <| P.decompositionEquiv.trans e.toLinearEquiv.symm
  refine
    { W := W
      W' := W'
      line := line
      decompositionEquiv := decomp
      decompositionEquiv_apply := ?_
      isotropic_W := ?_
      isotropic_W' := ?_
      pairingEquiv := eW'.trans <| P.pairingEquiv.trans eW.dualMap
      pairingEquiv_apply := ?_
      pairing_separatingLeft := ?_
      lineCoordinate := P.lineCoordinate.comp eLine.toLinearMap
      lineCoordinate_injective := P.lineCoordinate_injective.comp eLine.injective
      lineCoordinate_sq := ?_
      line_orthogonal_W := ?_
      line_orthogonal_W' := ?_ }
  · intro x
    apply e.toLinearEquiv.injective
    simp [decomp, P.decompositionEquiv_apply, eW_apply, eW'_apply, eLine_apply, map_add]
  · intro x
    rw [← e.map_app]
    exact P.isotropic_W (eW x)
  · intro y
    rw [← e.map_app]
    exact P.isotropic_W' (eW' y)
  · intro y x
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
      P.pairingEquiv_apply]
    exact (hpolar x y).symm
  · intro x hx
    apply eW.injective
    rw [map_zero]
    apply P.pairing_separatingLeft (eW x)
    intro y
    have hy : (y : V') = e (eW'.symm y : V) := by
      rw [← eW'_apply]
      exact congrArg Subtype.val (eW'.apply_symm_apply y).symm
    calc
      QuadraticMap.polar Q' (eW x) y =
          QuadraticMap.polar Q' (e x) (e (eW'.symm y)) := by
            rw [eW_apply, hy]
      _ = QuadraticMap.polar Q x (eW'.symm y) := (hpolar _ _).symm
      _ = 0 := hx _
  · intro z
    rw [LinearMap.comp_apply, P.lineCoordinate_sq, ← e.map_app]
    exact congrArg Q' (eLine_apply z)
  · intro z x
    rw [hpolar]
    exact P.line_orthogonal_W (eLine z) (eW x)
  · intro z y
    rw [hpolar]
    exact P.line_orthogonal_W' (eLine z) (eW' y)

private def isometryEquivSumSquaresUnits {F : Type*} [Field F] [NeZero (2 : F)]
    [IsSepClosed F]
    {I : Type*} [Fintype I] (w : I → Fˣ) :
    (QuadraticMap.weightedSumSquares F fun i ↦ (w i : F)).IsometryEquiv
      (QuadraticMap.weightedSumSquares F (1 : I → F)) := by
  classical
  refine QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ Units.mk0 (IsSepClosed.exists_eq_mul_self (w i : F)).choose ?_) ?_
  · rw [← mul_self_eq_zero.ne, ← (IsSepClosed.exists_eq_mul_self (w i : F)).choose_spec]
    exact (w i).ne_zero
  · intro i
    simp [pow_two, ← (IsSepClosed.exists_eq_mul_self (w i : F)).choose_spec]

private theorem equivalent_weightedSumSquares {F X : Type*} [Field F] [Invertible (2 : F)]
    [IsSepClosed F] [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (Q : QuadraticForm F X) (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    Q.Equivalent (QuadraticMap.weightedSumSquares F (1 : Fin (Module.finrank F X) → F)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

private theorem finrank_splitModel {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    Module.finrank R (SplitModel R n) = n := by
  let _ : Module.Free R (SplitHalf R n) := Module.Free.pi R _
  let _ : Module.Finite R (SplitHalf R n) := Module.Finite.pi
  let _ : Module.Free R (SplitRemainder R n) := Module.Free.pi R _
  let _ : Module.Finite R (SplitRemainder R n) := Module.Finite.pi
  simp only [SplitModel, SplitHalf, SplitRemainder, Module.Dual, Module.finrank_prod,
    Module.finrank_linearMap_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

private noncomputable def isometryEquivSplitModel {F X : Type*} [Field F]
    [Invertible (2 : F)] [IsSepClosed F] [AddCommGroup X] [Module F X]
    [FiniteDimensional F X] (Q : QuadraticForm F X) (hQ : Q.Nondegenerate) :
    Q.IsometryEquiv (splitModelForm F (Module.finrank F X)) := by
  have hQ' := equivalent_weightedSumSquares Q
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).2 hQ).1
  have hModel' :
      (splitModelForm F (Module.finrank F X)).Equivalent
        (QuadraticMap.weightedSumSquares F (1 : Fin (Module.finrank F X) → F)) := by
    have h := equivalent_weightedSumSquares
      (splitModelForm F (Module.finrank F X))
      (associated_splitModelForm_separatingLeft (R := F) (Module.finrank F X))
    rw [finrank_splitModel] at h
    exact h
  exact hQ'.some.trans hModel'.some.symm

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

/-- Every finite-dimensional nondegenerate quadratic space over a separably closed field of
characteristic different from two admits polarization data. -/
noncomputable def ofNondegenerate [FiniteDimensional F V] [NeZero (2 : F)]
    [IsSepClosed F] (Q : QuadraticForm F V) (hQ : Q.Nondegenerate) :
    SpinPolarizationData Q := by
  letI : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact pullback (isometryEquivSplitModel Q hQ)
    (modelData (K := F) (Module.finrank F V))

end

end SpinPolarizationData

end TauCeti
