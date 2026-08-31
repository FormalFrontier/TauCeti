/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.SpinWeight
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.SerreRelations

import TauCeti.LinearAlgebra.Eigenspace.Binomial
import TauCeti.RingTheory.DividedPowers.Associative

/-!
# The type-D spinor lattice is Kostant-stable

This file turns the type-`Dₙ` Clifford Serre system into a rational representation of the
type-`D` Serre presentation and proves that its coordinate spinor lattice is stable under the
Serre Kostant form.

The positive and negative simple-root representatives act by square-zero endomorphisms and
preserve the exterior coordinate lattice. The simple-coroot representatives act diagonally on
the exterior basis with the integral weights `TauCeti.DynkinType.typeDSpinWeight`; consequently
all of their binomial coefficients preserve the same lattice. These two facts give stability
under every generator of the Serre Kostant form.

The full exterior algebra, rather than either parity summand alone, is used because its weights
span the full simply connected type-`D` character lattice. Thus this is the admissible-lattice
input for the full-weight type-`D` Chevalley--Demazure carrier in Layer 9 of the ReductiveGroups
roadmap. That carrier is consumed by the `Dₙ(q)` and `²Dₙ(q)` branches of milestone L0 in the
CFSGStatement roadmap.

## Main declarations

* `TauCeti.SpinPolarizationData.typeDSpinSerreRepresentation`: the type-`D` Serre presentation
  acting on the spinor module.
* `TauCeti.SpinPolarizationData.typeDSpinRep`: its extension to the universal enveloping algebra.
* `TauCeti.SpinPolarizationData.typeDSpinRep_rootGenerator_sq`: the represented root operators
  are square-zero.
* `TauCeti.SpinPolarizationData.isCartanWeightVector_typeDSpinRep_integralLatticeBasis`: the
  integral exterior basis is a weight basis with weights `typeDSpinWeight`.
* `TauCeti.SpinPolarizationData.typeDSpinRep_serreKostantForm_apply_mem_integralLattice`: the
  Serre Kostant form preserves the coordinate spinor lattice.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.

The organization parallels the type-`B` spinor-lattice construction in Tau Ceti PR #5269; the
fork coroot and the need for both half-spin parities are the type-`D` features.
-/

public section

open CliffordAlgebra

namespace TauCeti.SpinPolarizationData

universe u

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W)
  (hn : 4 ≤ n)

/-! ## The rational spin representation -/

/-- The rational type-`D` Serre presentation acting on the spinor module through its canonical
Clifford Serre system. -/
noncomputable def typeDSpinSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.D n) →ₗ⁅ℚ⁆
      Module.End ℚ (ExteriorAlgebra ℚ P.W) :=
  (spinAction Q P).toLieHom.comp
    (TauCeti.serreLift (P.isSerreSystem_typeDSimpleRootBivector b hn))

/-- A Cartan generator acts through the corresponding type-`D` simple-coroot Clifford element. -/
@[simp]
theorem typeDSpinSerreRepresentation_serreH (i : Fin n) :
    P.typeDSpinSerreRepresentation b hn (TauCeti.serreH ℚ (CartanMatrix.D n) i) =
      spinAction Q P (P.typeDSimpleCorootBivector b (by omega) i) := by
  simp [typeDSpinSerreRepresentation]

/-- A positive Serre generator acts through the corresponding type-`D` root Clifford element. -/
@[simp]
theorem typeDSpinSerreRepresentation_serreE (i : Fin n) :
    P.typeDSpinSerreRepresentation b hn (TauCeti.serreE ℚ (CartanMatrix.D n) i) =
      spinAction Q P (P.typeDSimpleRootBivector b (by omega) i) := by
  simp [typeDSpinSerreRepresentation]

/-- A negative Serre generator acts through the corresponding negative-root Clifford element. -/
@[simp]
theorem typeDSpinSerreRepresentation_serreF (i : Fin n) :
    P.typeDSpinSerreRepresentation b hn (TauCeti.serreF ℚ (CartanMatrix.D n) i) =
      spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) i) := by
  simp [typeDSpinSerreRepresentation]

/-- The type-`D` spin representation extended to the universal enveloping algebra. -/
noncomputable def typeDSpinRep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)) →ₐ[ℚ]
      Module.End ℚ (ExteriorAlgebra ℚ P.W) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ (P.typeDSpinSerreRepresentation b hn)

/-- An included Lie element acts through the rational Serre representation. -/
theorem typeDSpinRep_ι (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)) :
    P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      P.typeDSpinSerreRepresentation b hn x := by
  rw [typeDSpinRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]

/-! ## Root operators -/

/-- Every represented positive or negative simple-root generator is square-zero. -/
theorem typeDSpinRep_rootGenerator_sq (k : Fin n ⊕ Fin n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n) k)) ^ 2 = 0 := by
  cases k with
  | inl i =>
      simp only [TauCeti.serreRootGenerator_inl, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreE b hn, pow_two]
      exact P.spinAction_typeDSimpleRootBivector_sq b (by omega) i
  | inr i =>
      simp only [TauCeti.serreRootGenerator_inr, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreF b hn, pow_two]
      exact P.spinAction_typeDSimpleNegativeRootBivector_sq b (by omega) i

/-- Every represented positive or negative simple-root generator acts nilpotently. -/
theorem isNilpotent_typeDSpinRep_rootGenerator (k : Fin n ⊕ Fin n) :
    IsNilpotent (P.typeDSpinRep b hn
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) k))) :=
  ⟨2, P.typeDSpinRep_rootGenerator_sq b hn k⟩

/-- Every represented positive or negative simple-root generator preserves the coordinate spinor
lattice. -/
theorem typeDSpinRep_rootGenerator_apply_mem_integralLattice
    (k : Fin n ⊕ Fin n) {v : ExteriorAlgebra ℚ P.W}
    (hv : v ∈ TauCeti.ExteriorAlgebra.integralLattice b) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n) k)) v ∈
      TauCeti.ExteriorAlgebra.integralLattice b := by
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreE b hn]
      exact (P.mem_integralSpinActionSubring b).mp
        (P.typeDSimpleRootBivector_mem_integralSpinActionSubring b (by omega) i) hv
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreF b hn]
      exact (P.mem_integralSpinActionSubring b).mp
        (P.typeDSimpleNegativeRootBivector_mem_integralSpinActionSubring b (by omega) i) hv

/-! ## Cartan weights and binomial operators -/

/-- A type-`D` simple-coroot Clifford element acts diagonally on an exterior-basis vector, with
the corresponding integral spin weight as eigenvalue. -/
theorem spinAction_typeDSimpleCorootBivector_exteriorBasis
    (i : Fin n) (s : Finset (Fin n)) :
    spinAction Q P (P.typeDSimpleCorootBivector b (by omega) i)
        (b.ExteriorAlgebra s) =
      (TauCeti.DynkinType.typeDSpinWeight s i : ℚ) • b.ExteriorAlgebra s := by
  rw [P.typeDSimpleCorootBivector_eq_diagonalBivector b (by omega) i]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [dite_eq_left hnext, map_sub, LinearMap.sub_apply,
      P.spinAction_diagonalBivector_basis b, P.spinAction_diagonalBivector_basis b, ← sub_smul]
    simpa only [dite_eq_left hnext, algebraMap_int_eq, Int.coe_castRingHom] using
      (congrArg (fun z : ℚ ↦ z • b.ExteriorAlgebra s)
        (TauCeti.DynkinType.algebraMap_typeDSpinWeight_apply (K := ℚ) s i)).symm
  · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    rw [dite_eq_right hnext, map_add, LinearMap.add_apply,
      P.spinAction_diagonalBivector_basis b, P.spinAction_diagonalBivector_basis b, ← add_smul]
    have hprev :
        (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) =
          (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    have hspin : spinWeight ℚ s i = spinWeight ℚ s (⟨n - 1, by omega⟩ : Fin n) :=
      congrArg (spinWeight ℚ s) hi
    have hwt := TauCeti.DynkinType.algebraMap_typeDSpinWeight_apply (K := ℚ) s i
    rw [dite_eq_right hnext, hprev] at hwt
    rw [hspin] at hwt
    simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
      (congrArg (fun z : ℚ ↦ z • b.ExteriorAlgebra s) hwt).symm

/-- Every exterior-basis vector is a Cartan weight vector for the type-`D` spin representation,
with its integral simply connected spin weight. -/
theorem isCartanWeightVector_typeDSpinRep_exteriorBasis (s : Finset (Fin n)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)
      (TauCeti.DynkinType.typeDSpinWeight s) (b.ExteriorAlgebra s) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)).mpr fun i ↦ ?_
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinSerreRepresentation_serreH b hn]
  exact P.spinAction_typeDSimpleCorootBivector_exteriorBasis b hn i s

/-- The integral exterior basis is a Cartan weight basis for the type-`D` spin representation. -/
theorem isCartanWeightVector_typeDSpinRep_integralLatticeBasis (s : Finset (Fin n)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)
      (TauCeti.DynkinType.typeDSpinWeight s)
      (((TauCeti.ExteriorAlgebra.integralLatticeBasis b) s :
        TauCeti.ExteriorAlgebra.integralLattice b) : ExteriorAlgebra ℚ P.W) := by
  rw [TauCeti.ExteriorAlgebra.coe_integralLatticeBasis]
  exact P.isCartanWeightVector_typeDSpinRep_exteriorBasis b hn s

/-- Every binomial coefficient in a represented simple-coroot generator preserves the coordinate
spinor lattice. -/
theorem typeDSpinRep_ringChoose_serreH_apply_mem_integralLattice
    (i : Fin n) (m : ℕ) {v : ExteriorAlgebra ℚ P.W}
    (hv : v ∈ TauCeti.ExteriorAlgebra.integralLattice b) :
    P.typeDSpinRep b hn
        (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreH ℚ (CartanMatrix.D n) i)) m) v ∈
      TauCeti.ExteriorAlgebra.integralLattice b := by
  rw [Ring.map_choose]
  refine TauCeti.ExteriorAlgebra.map_mem_integralLattice b
    ((Ring.choose (P.typeDSpinRep b hn
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreH ℚ (CartanMatrix.D n) i))) m).restrictScalars ℤ)
    (fun s ↦ ?_) hv
  rw [LinearMap.restrictScalars_apply, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreH b hn]
  rw [TauCeti.ringChoose_end_apply_of_apply_eq_smul
      (P.spinAction_typeDSimpleCorootBivector_exteriorBasis b hn i s),
    Ring.choose_intCast, Int.cast_smul_eq_zsmul ℚ]
  exact Submodule.smul_mem _ _ (TauCeti.ExteriorAlgebra.basis_mem_integralLattice b s)

/-! ## Stability under the Serre Kostant form -/

/-- **The coordinate spinor lattice is admissible for the type-`D` Serre Kostant form.** -/
theorem typeDSpinRep_serreKostantForm_apply_mem_integralLattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n))}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.D n))
    {v : ExteriorAlgebra ℚ P.W}
    (hv : v ∈ TauCeti.ExteriorAlgebra.integralLattice b) :
    P.typeDSpinRep b hn u v ∈ TauCeti.ExteriorAlgebra.integralLattice b := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)
    (TauCeti.ExteriorAlgebra.integralLattice b)
    (fun k m _ hw ↦ by
      rw [Associative.map_dividedPower]
      exact Associative.dividedPower_apply_mem_of_pow_two_eq_zero _ _
        (P.typeDSpinRep_rootGenerator_sq b hn k)
        (fun hw' ↦ P.typeDSpinRep_rootGenerator_apply_mem_integralLattice b hn k hw') m hw)
    (fun i m _ hw ↦
      P.typeDSpinRep_ringChoose_serreH_apply_mem_integralLattice b hn i m hw) u hu hv

end TauCeti.SpinPolarizationData
