/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure

import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector
import TauCeti.LinearAlgebra.Matrix.AdjugateFinTwo


/-!
# The even Clifford algebra in dimension three

In dimension three the even Clifford algebra consists of scalars and Clifford bivectors.  Reversal
fixes the scalar summand and negates the bivector summand.  Consequently every algebra
equivalence from the even Clifford algebra to two-by-two matrices carries reversal to matrix
adjugation.

This is the matrix-model input for the low-dimensional isomorphism `Spin₃ ≃ SL₂`: under any
equivalence below, Clifford reversal becomes matrix adjugation, and the Spin norm equation becomes
the determinant-one equation.  Identifying the exact image with `SL₂` remains downstream.

## Main results

* `CliffordAlgebra.evenEquivMatrixFinTwoOfFinrankEqThree`: a chosen algebra equivalence from the
  even Clifford algebra of a nondegenerate three-dimensional form over a separably closed field.
* `CliffordAlgebra.reverse_eq_adjugate_of_finrank_eq_three`: every such algebra equivalence carries
  reversal to matrix adjugation.
* `CliffordAlgebra.reverse_mul_eq_det_smul_one`: the norm product maps to determinant times one.

## References

This is the matrix-model step of Layer 6 in the
[SpinRepresentations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md).
The chosen equivalence reuses
`CliffordAlgebra.nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one` from
`RepresentationTheory/Spin/OddStructure.lean` and the scalar-plus-bivector API in
`LinearAlgebra/CliffordAlgebra/Bivector.lean`. See Fulton and Harris, *Representation Theory: A
First Course*, Lecture 20, for the low-dimensional Spin isomorphisms.
-/

public section

universe u v

namespace CliffordAlgebra

variable {K : Type u} [Field K] [NeZero (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

@[instance_reducible]
private noncomputable def invertibleTwoOfNeZero : Invertible (2 : K) :=
  invertibleOfNonzero (NeZero.ne (2 : K))

attribute [local instance] invertibleTwoOfNeZero

private noncomputable def bivectorExteriorEven : ⋀[K]^2 V →ₗ[K] ↥(even Q) :=
  (bivectorExterior Q).codRestrict (even Q).toSubmodule fun x => by
    apply bivectorExterior_range_le_of_bivector_mem Q
      (even Q).toSubmodule (fun a b => ?_) ⟨x, rfl⟩
    rw [even_toSubmodule]
    exact bivector_mem_evenOdd_zero Q a b

omit [FiniteDimensional K V] in
private theorem coe_bivectorExteriorEven (x : ⋀[K]^2 V) :
    (bivectorExteriorEven Q x : CliffordAlgebra Q) = bivectorExterior Q x :=
  rfl

omit [FiniteDimensional K V] in
private theorem bivectorExteriorEven_injective :
    Function.Injective (bivectorExteriorEven Q) := fun x y h =>
  bivectorExterior_injective Q <| by
    rw [← coe_bivectorExteriorEven Q x, ← coe_bivectorExteriorEven Q y]
    exact congrArg Subtype.val h

private noncomputable def scalarAddBivectorEven : (K × ⋀[K]^2 V) →ₗ[K] ↥(even Q) :=
  LinearMap.coprod (Algebra.linearMap K ↥(even Q)) (bivectorExteriorEven Q)

omit [FiniteDimensional K V] in
private theorem scalarAddBivectorEven_apply (x : K × ⋀[K]^2 V) :
    ((scalarAddBivectorEven Q x : ↥(even Q)) : CliffordAlgebra Q) =
      algebraMap K (CliffordAlgebra Q) x.1 + bivectorExterior Q x.2 := by
  rw [scalarAddBivectorEven, LinearMap.coprod_apply, Algebra.linearMap_apply]
  simp [Subalgebra.coe_add, coe_bivectorExteriorEven]

omit [FiniteDimensional K V] in
private theorem disjoint_range_algebraMap_range_bivectorExteriorEven :
    Disjoint (LinearMap.range (Algebra.linearMap K ↥(even Q)))
      (LinearMap.range (bivectorExteriorEven Q)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨q, hq⟩ := hy
  apply Subtype.ext
  have hq' : bivectorExterior Q q = algebraMap K (CliffordAlgebra Q) r := by
    simpa only [Algebra.linearMap_apply, coe_bivectorExteriorEven, Subalgebra.coe_algebraMap]
      using congrArg Subtype.val hq
  have hrev :
      algebraMap K (CliffordAlgebra Q) r = -algebraMap K (CliffordAlgebra Q) r := by
    calc
      algebraMap K (CliffordAlgebra Q) r = reverse (algebraMap K (CliffordAlgebra Q) r) :=
        (reverse.commutes r).symm
      _ = reverse (bivectorExterior Q q) := congrArg reverse hq'.symm
      _ = -bivectorExterior Q q := reverse_bivectorExterior Q q
      _ = -algebraMap K (CliffordAlgebra Q) r := congrArg Neg.neg hq'
  have htwo : (2 : K) • algebraMap K (CliffordAlgebra Q) r = 0 := by
    rw [two_smul, add_eq_zero_iff_eq_neg]
    exact hrev
  have hz : algebraMap K (CliffordAlgebra Q) r = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (NeZero.ne (2 : K))
  exact hz

omit [FiniteDimensional K V] in
private theorem scalarAddBivectorEven_injective :
    Function.Injective (scalarAddBivectorEven Q) := by
  rw [← LinearMap.ker_eq_bot, scalarAddBivectorEven,
    LinearMap.ker_coprod_of_disjoint_range _ _
      (disjoint_range_algebraMap_range_bivectorExteriorEven Q),
    LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K ↥(even Q)),
    LinearMap.ker_eq_bot.2 (bivectorExteriorEven_injective Q), Submodule.prod_bot]

omit [NeZero (2 : K)] in
theorem finrank_prod_exteriorPower_two_of_finrank_eq_three
    (hV : Module.finrank K V = 3) :
    Module.finrank K (K × ⋀[K]^2 V) = 4 := by
  rw [Module.finrank_prod, Module.finrank_self, exteriorPower.finrank_eq, hV]
  decide

private theorem finrank_even_of_finrank_eq_three
    (hV : Module.finrank K V = 3) :
    Module.finrank K ↥(even Q) = 4 := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  rw [finrank_even Q, hV]
  decide

private noncomputable def scalarAddBivectorEquivEven
    (hV : Module.finrank K V = 3) :
    (K × ⋀[K]^2 V) ≃ₗ[K] ↥(even Q) := by
  refine LinearEquiv.ofBijective (scalarAddBivectorEven Q)
    ⟨scalarAddBivectorEven_injective Q, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_prod_exteriorPower_two_of_finrank_eq_three hV).trans
      (finrank_even_of_finrank_eq_three Q hV).symm)).1
    (scalarAddBivectorEven_injective Q)

private theorem scalarAddBivectorEquivEven_apply
    (hV : Module.finrank K V = 3) (x : K × ⋀[K]^2 V) :
    scalarAddBivectorEquivEven Q hV x = scalarAddBivectorEven Q x :=
  LinearEquiv.ofBijective_apply _ _

def reverseEven : ↥(even Q) →ₗ[K] ↥(even Q) :=
  (reverse (Q := Q)).restrict (p := (even Q).toSubmodule) (q := (even Q).toSubmodule)
    (fun _x hx => (reverse_mem_evenOdd_iff Q).2 hx)

omit [NeZero (2 : K)] [FiniteDimensional K V] in
@[simp] theorem reverseEven_coe (x : ↥(even Q)) :
    (reverseEven Q x : CliffordAlgebra Q) = reverse x := by
  rfl

theorem exists_add_reverseEven_eq_smul_one
    (hV : Module.finrank K V = 3) (x : ↥(even Q)) :
    ∃ r : K, x + reverseEven Q x = r • 1 := by
  generalize hy : (scalarAddBivectorEquivEven Q hV).symm x = y
  obtain ⟨r, q⟩ := y
  refine ⟨r + r, ?_⟩
  have hx := (scalarAddBivectorEquivEven Q hV).apply_symm_apply x
  rw [scalarAddBivectorEquivEven_apply] at hx
  rw [hy] at hx
  rw [← hx]
  apply Subtype.ext
  simp only [Subalgebra.coe_add, scalarAddBivectorEven_apply, map_add, reverse.commutes,
    reverseEven_coe, reverse_bivectorExterior, Subalgebra.coe_smul, Subalgebra.coe_one]
  calc
    algebraMap K (CliffordAlgebra Q) r + bivectorExterior Q q +
          (algebraMap K (CliffordAlgebra Q) r + -bivectorExterior Q q) =
        algebraMap K (CliffordAlgebra Q) r + algebraMap K (CliffordAlgebra Q) r := by abel
    _ = algebraMap K (CliffordAlgebra Q) (r + r) := (map_add _ _ _).symm
    _ = (r + r) • (1 : CliffordAlgebra Q) := by rw [Algebra.smul_def, mul_one]

noncomputable def reverseMatrix
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  e.toLinearMap.comp ((reverseEven Q).comp e.symm.toLinearMap)

omit [NeZero (2 : K)] [FiniteDimensional K V] in
theorem reverseMatrix_apply
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K) :
    reverseMatrix Q e A = e (reverseEven Q (e.symm A)) := by
  simp [reverseMatrix]

omit [NeZero (2 : K)] [FiniteDimensional K V] in
theorem reverseMatrix_mul
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A B : Matrix (Fin 2) (Fin 2) K) :
    reverseMatrix Q e (A * B) = reverseMatrix Q e B * reverseMatrix Q e A := by
  rw [reverseMatrix_apply, reverseMatrix_apply, reverseMatrix_apply]
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change reverse (e.symm (A * B) : CliffordAlgebra Q) =
    reverse (e.symm B : CliffordAlgebra Q) * reverse (e.symm A : CliffordAlgebra Q)
  rw [map_mul]
  exact reverse.map_mul (Q := Q) (e.symm A) (e.symm B)

theorem exists_add_reverseMatrix_eq_smul_one
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ r : K, A + reverseMatrix Q e A = r • 1 := by
  obtain ⟨r, hr⟩ := exists_add_reverseEven_eq_smul_one Q hV (e.symm A)
  refine ⟨r, ?_⟩
  rw [reverseMatrix_apply]
  calc
    A + e (reverseEven Q (e.symm A)) =
        e (e.symm A) + e (reverseEven Q (e.symm A)) := by rw [e.apply_symm_apply]
    _ = e (e.symm A + reverseEven Q (e.symm A)) := (map_add e _ _).symm
    _ = e (r • 1) := congrArg e hr
    _ = r • 1 := by rw [map_smul, map_one]

theorem reverse_eq_adjugate_of_finrank_eq_three
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    e (reverseEven Q x) = Matrix.adjugate (e x) := by
  have hf := congrArg (fun g : Matrix (Fin 2) (Fin 2) K →ₗ[K] _ => g (e x))
    (Matrix.linearMap_antimultiplicative_eq_adjugateMap (reverseMatrix Q e) (reverseMatrix_mul Q e)
      (exists_add_reverseMatrix_eq_smul_one Q hV e))
  simpa only [reverseMatrix_apply, e.symm_apply_apply, reverseEven_coe,
    Matrix.adjugateLinearMap_apply] using hf

variable [IsSepClosed K]

/-- A chosen matrix model of the even Clifford algebra of a nondegenerate three-dimensional
quadratic space over a separably closed field. -/
noncomputable def evenEquivMatrixFinTwoOfFinrankEqThree
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  (nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one hQ (l := 1) (by omega)).some

/-- In the chosen two-by-two matrix model, Clifford reversal is matrix adjugation. -/
@[simp]
theorem evenEquivMatrixFinTwoOfFinrankEqThree_reverse
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (x : ↥(even Q)) :
    evenEquivMatrixFinTwoOfFinrankEqThree Q hQ hV (reverseEven Q x) =
      Matrix.adjugate (evenEquivMatrixFinTwoOfFinrankEqThree Q hQ hV x) :=
  reverse_eq_adjugate_of_finrank_eq_three Q hV (evenEquivMatrixFinTwoOfFinrankEqThree Q hQ hV) x

omit [IsSepClosed K] in
theorem reverse_mul_eq_det_smul_one
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    e (reverseEven Q x * x) = (e x).det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [map_mul, reverse_eq_adjugate_of_finrank_eq_three Q hV e x]
  exact Matrix.adjugate_mul _

omit [IsSepClosed K] in
@[simp]
theorem reverse_mul_eq_one_iff_det_eq_one
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    reverseEven Q x * x = 1 ↔ (e x).det = 1 := by
  constructor
  · intro h
    have hm := congrArg e h
    rw [reverse_mul_eq_det_smul_one Q hV e x, map_one] at hm
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hm
    simpa using h00
  · intro hdet
    apply e.injective
    rw [map_one, reverse_mul_eq_det_smul_one Q hV e x, hdet, one_smul]

end CliffordAlgebra
