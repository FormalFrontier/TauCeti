/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure

import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector


/-!
# The even Clifford algebra in dimension three

In dimension three the even Clifford algebra consists of scalars and Clifford bivectors.  Reversal
fixes the scalar summand and negates the bivector summand.  Consequently every algebra
equivalence from the even Clifford algebra to two-by-two matrices carries reversal to matrix
adjugation.

This is the matrix-model input for the low-dimensional isomorphism `Spin₃ ≃ SL₂`: the Spin norm
equation becomes the determinant-one equation under the equivalence chosen below.  Identifying the
exact image with `SL₂` remains downstream.

## Main results

* `CliffordAlgebra.evenEquivMatrixTwoOfFinrankThree`: a chosen algebra equivalence from the even
  Clifford algebra of a nondegenerate three-dimensional form over a separably closed field.
* `CliffordAlgebra.evenEquivMatrixTwoOfFinrankThree_reverse`: reversal is carried to matrix
  adjugation.

## References

This is the matrix-model step of Layer 6 in the SpinRepresentations roadmap. See Fulton and Harris,
*Representation Theory: A First Course*, Lecture 20, for the low-dimensional Spin isomorphisms.
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

omit [FiniteDimensional K V] in
private theorem reverse_bivector (a b : V) :
    reverse (bivector Q a b) = -bivector Q a b := by
  rw [bivector_def, map_smul, map_sub, reverse.map_mul, reverse.map_mul, reverse_ι, reverse_ι]
  module

omit [FiniteDimensional K V] in
private theorem reverse_bivectorExterior (x : ⋀[K]^2 V) :
    reverse (bivectorExterior Q x) = -bivectorExterior Q x := by
  let P : Submodule K (CliffordAlgebra Q) :=
    { carrier := {x | reverse x = -x}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        have hx' : reverse x = -x := hx
        have hy' : reverse y = -y := hy
        rw [Set.mem_ofPred_eq, map_add, hx', hy', neg_add]
      smul_mem' := by
        intro r x hx
        have hx' : reverse x = -x := hx
        rw [Set.mem_ofPred_eq, map_smul, hx', smul_neg] }
  have hle : LinearMap.range (bivectorExterior Q) ≤ P :=
    bivectorExterior_range_le_of_bivector_mem Q P fun a b => reverse_bivector Q a b
  exact hle ⟨x, rfl⟩

private noncomputable def scalarAddBivectorEven : (K × ⋀[K]^2 V) →ₗ[K] ↥(even Q) :=
  LinearMap.coprod (Algebra.linearMap K ↥(even Q)) (bivectorExteriorEven Q)

omit [FiniteDimensional K V] in
private theorem scalarAddBivectorEven_apply (x : K × ⋀[K]^2 V) :
    ((scalarAddBivectorEven Q x : ↥(even Q)) : CliffordAlgebra Q) =
      algebraMap K (CliffordAlgebra Q) x.1 + bivectorExterior Q x.2 := by
  rw [scalarAddBivectorEven, LinearMap.coprod_apply, Algebra.linearMap_apply]
  rfl

omit [FiniteDimensional K V] in
private theorem scalar_range_disjoint_bivector_range :
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
    LinearMap.ker_coprod_of_disjoint_range _ _ (scalar_range_disjoint_bivector_range Q),
    LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K ↥(even Q)),
    LinearMap.ker_eq_bot.2 (bivectorExteriorEven_injective Q), Submodule.prod_bot]

omit [NeZero (2 : K)] in
private theorem finrank_domain_of_finrank_eq_three
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
    ((finrank_domain_of_finrank_eq_three hV).trans
      (finrank_even_of_finrank_eq_three Q hV).symm)).1
    (scalarAddBivectorEven_injective Q)

private theorem scalarAddBivectorEquivEven_apply
    (hV : Module.finrank K V = 3) (x : K × ⋀[K]^2 V) :
    scalarAddBivectorEquivEven Q hV x = scalarAddBivectorEven Q x :=
  LinearEquiv.ofBijective_apply _ _

omit [NeZero (2 : K)] in
private theorem adjugate_eq_trace_smul_one_sub (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.adjugate A = Matrix.trace A • 1 - A := by
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [NeZero (2 : K)] in
private noncomputable def adjugateLinear :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun := Matrix.adjugate
  map_add' A B := by
    simp only [adjugate_eq_trace_smul_one_sub, Matrix.trace_add, add_smul]
    module
  map_smul' r A := by
    simp only [adjugate_eq_trace_smul_one_sub, Matrix.trace_smul, smul_sub, smul_smul,
      RingHom.id_apply, smul_eq_mul]

omit [NeZero (2 : K)] in
private theorem antiMap_offDiag
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (Matrix.single i j 1) = -(Matrix.single i j 1) := by
  let E : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1
  obtain ⟨r, hr⟩ := hscalar E
  have hf : f E = r • 1 - E := eq_sub_of_add_eq (by simpa [add_comm] using hr)
  have hE2 : E * E = 0 := by
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [E, Matrix.mul_apply, Matrix.single] at hij ⊢
  have hsquare : f E * f E = 0 := by
    rw [← hmul, hE2, map_zero]
  rw [hf] at hsquare
  have hrii := congr_fun (congr_fun hsquare j) j
  have hrr : r * r = 0 := by
    simpa [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply,
      hij, Ne.symm hij] using hrii
  have hr0 : r = 0 := mul_self_eq_zero.mp hrr
  have hneg : f E = -E := by
    rw [hf, hr0]
    simp
  simpa only [E] using hneg

omit [NeZero (2 : K)] in
private theorem antiMap_diag
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (Matrix.single i i 1) = Matrix.single j j 1 := by
  let D : Matrix (Fin 2) (Fin 2) K := Matrix.single i i 1
  let E : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1
  obtain ⟨r, hr⟩ := hscalar D
  have hfD : f D = r • 1 - D := eq_sub_of_add_eq (by simpa [add_comm] using hr)
  have hfE := antiMap_offDiag f hmul hscalar i j hij
  have hDE : D * E = E := by
    simp [D, E]
  have hp := hmul D E
  rw [hDE, hfE, hfD] at hp
  have hpij := congr_fun (congr_fun hp i) j
  have hr1 : r = 1 := by
    have hr1' : (1 : K) = r := by
      simpa [D, E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply,
        hij, Ne.symm hij] using hpij
    exact hr1'.symm
  rw [hfD, hr1]
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [D, Matrix.single] at hij ⊢

omit [NeZero (2 : K)] in
private theorem antiMap_single_eq_adjugate
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1) (i j : Fin 2) :
    f (Matrix.single i j 1) = Matrix.adjugate (Matrix.single i j 1) := by
  by_cases hij : i = j
  · subst j
    fin_cases i
    · calc
        f (Matrix.single _ _ 1) = Matrix.single (1 : Fin 2) (1 : Fin 2) 1 := by
          simpa using antiMap_diag f hmul hscalar (0 : Fin 2) (1 : Fin 2) (by decide)
        _ = Matrix.adjugate (Matrix.single _ _ 1) := by
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_two, Matrix.single]
    · calc
        f (Matrix.single _ _ 1) = Matrix.single (0 : Fin 2) (0 : Fin 2) 1 := by
          simpa using antiMap_diag f hmul hscalar (1 : Fin 2) (0 : Fin 2) (by decide)
        _ = Matrix.adjugate (Matrix.single _ _ 1) := by
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_two, Matrix.single]
  · rw [antiMap_offDiag f hmul hscalar i j hij]
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp_all [Matrix.adjugate_fin_two, Matrix.single]

omit [NeZero (2 : K)] in
private theorem antiMap_eq_adjugate
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1) :
    f = adjugateLinear := by
  refine (Matrix.stdBasis K (Fin 2) (Fin 2)).ext ?_
  rintro ⟨i, j⟩
  rw [Matrix.stdBasis_eq_single]
  simpa only [adjugateLinear, LinearMap.coe_mk, AddHom.coe_mk] using
    antiMap_single_eq_adjugate f hmul hscalar i j

private def reverseEven : ↥(even Q) →ₗ[K] ↥(even Q) where
  toFun x := ⟨reverse x, (reverse_mem_evenOdd_iff Q).2 x.property⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

private theorem scalarAdd_reverse
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
  simp only [Subalgebra.coe_add, LinearMap.coe_mk, AddHom.coe_mk, reverseEven,
    scalarAddBivectorEven_apply, map_add, reverse.commutes, reverse_bivectorExterior,
    Subalgebra.coe_smul, Subalgebra.coe_one]
  calc
    algebraMap K (CliffordAlgebra Q) r + bivectorExterior Q q +
          (algebraMap K (CliffordAlgebra Q) r + -bivectorExterior Q q) =
        algebraMap K (CliffordAlgebra Q) r + algebraMap K (CliffordAlgebra Q) r := by abel
    _ = algebraMap K (CliffordAlgebra Q) (r + r) := (map_add _ _ _).symm
    _ = (r + r) • (1 : CliffordAlgebra Q) := by rw [Algebra.smul_def, mul_one]

private noncomputable def reverseMatrix
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  e.toLinearMap.comp ((reverseEven Q).comp e.symm.toLinearMap)

omit [NeZero (2 : K)] [FiniteDimensional K V] in
private theorem reverseMatrix_apply
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K) :
    reverseMatrix Q e A = e (reverseEven Q (e.symm A)) :=
  rfl

omit [NeZero (2 : K)] [FiniteDimensional K V] in
private theorem reverseMatrix_mul
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A B : Matrix (Fin 2) (Fin 2) K) :
    reverseMatrix Q e (A * B) = reverseMatrix Q e B * reverseMatrix Q e A := by
  rw [reverseMatrix_apply, reverseMatrix_apply, reverseMatrix_apply]
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp [reverseEven, reverse.map_mul]

private theorem reverseMatrix_add_self_smul
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ r : K, A + reverseMatrix Q e A = r • 1 := by
  obtain ⟨r, hr⟩ := scalarAdd_reverse Q hV (e.symm A)
  refine ⟨r, ?_⟩
  rw [reverseMatrix_apply]
  calc
    A + e (reverseEven Q (e.symm A)) =
        e (e.symm A) + e (reverseEven Q (e.symm A)) := by rw [e.apply_symm_apply]
    _ = e (e.symm A + reverseEven Q (e.symm A)) := (map_add e _ _).symm
    _ = e (r • 1) := congrArg e hr
    _ = r • 1 := by rw [map_smul, map_one]

private theorem reverse_eq_adjugate
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    e ⟨reverse x, (reverse_mem_evenOdd_iff Q).2 x.property⟩ = Matrix.adjugate (e x) := by
  have hf := congrArg (fun g : Matrix (Fin 2) (Fin 2) K →ₗ[K] _ => g (e x))
    (antiMap_eq_adjugate (reverseMatrix Q e) (reverseMatrix_mul Q e)
      (reverseMatrix_add_self_smul Q hV e))
  simpa [reverseMatrix, reverseEven, adjugateLinear] using hf

variable [IsSepClosed K]

/-- A chosen matrix model of the even Clifford algebra of a nondegenerate three-dimensional
quadratic space over a separably closed field. -/
noncomputable def evenEquivMatrixTwoOfFinrankThree
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  (nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one hQ (l := 1) (by omega)).some

/-- In the chosen two-by-two matrix model, Clifford reversal is matrix adjugation. -/
@[simp]
theorem evenEquivMatrixTwoOfFinrankThree_reverse
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (x : ↥(even Q)) :
    evenEquivMatrixTwoOfFinrankThree Q hQ hV
        ⟨reverse x, (reverse_mem_evenOdd_iff Q).2 x.property⟩ =
      Matrix.adjugate (evenEquivMatrixTwoOfFinrankThree Q hQ hV x) :=
  reverse_eq_adjugate Q hV (evenEquivMatrixTwoOfFinrankThree Q hQ hV) x

end CliffordAlgebra
