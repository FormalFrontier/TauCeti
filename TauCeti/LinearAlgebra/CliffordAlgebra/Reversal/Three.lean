/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.ExteriorPower
import TauCeti.LinearAlgebra.Matrix.AdjugateFinTwo
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

/-!
# Reversal in three-dimensional Clifford algebras

In dimension three, an even Clifford element plus its reversal is scalar. Thus every two-by-two
matrix model identifies reversal with adjugation and the norm-one equation with determinant one.
-/

public section

universe u v

namespace CliffordAlgebra

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

private theorem filtration_eq_top_of_finrank_eq_three
    (hV : Module.finrank K V = 3) :
    filtration Q 3 = ⊤ := by
  let _ : FiniteDimensional K V := .of_finrank_eq_succ (by omega)
  rw [eq_top_iff, ← iSup_filtration_eq_top Q]
  refine iSup_le fun n => ?_
  induction n with
  | zero => exact filtration_mono Q (by omega)
  | succ n ih =>
      by_cases hn : n + 1 ≤ 3
      · exact filtration_mono Q hn
      · have hvanish (x : ⋀[K]^(n + 1) V) : x = 0 :=
          exteriorPower.eq_zero_of_finrank_lt (n + 1) (by omega) x
        let _ : Subsingleton (⋀[K]^(n + 1) V) :=
          ⟨fun x y => (hvanish x).trans (hvanish y).symm⟩
        let _ : Subsingleton (TauCeti.Algebra.wordFiltration.GradedPiece (ι Q) (n + 1)) :=
          (filtrationLeadingTerm_surjective Q n).subsingleton
        have hstep : filtration Q (n + 1) ≤ filtration Q n := by
          -- Once the leading exterior power vanishes, its graded quotient is subsingleton;
          -- the stable filtration API then identifies every degree-`n + 1` class with zero.
          intro x hx
          have hxzero :
              (TauCeti.Algebra.wordFiltration.previousRestricted (ι Q) (n + 1)).mkQ
                  ⟨x, hx⟩ = 0 :=
            Subsingleton.elim _ _
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
            TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff,
            TauCeti.Algebra.wordFiltrationPrevious_succ] at hxzero
          exact hxzero
        exact hstep.trans ih

private def scalarAddReverseSubmodule : Submodule K (CliffordAlgebra Q) :=
  (LinearMap.range (Algebra.linearMap K (CliffordAlgebra Q))).comap
    (LinearMap.id + reverse)

private theorem mem_scalarAddReverseSubmodule_iff (x : CliffordAlgebra Q) :
    x ∈ scalarAddReverseSubmodule Q ↔
      x + reverse x ∈ LinearMap.range (Algebra.linearMap K (CliffordAlgebra Q)) := by
  simp [scalarAddReverseSubmodule, LinearMap.add_apply]

/-- In dimension three, every even element plus its reversal is scalar. -/
theorem exists_add_reverseEven_eq_smul_one_of_finrank_eq_three
    (hV : Module.finrank K V = 3) (x : ↥(even Q)) :
    ∃ r : K, x + reverseEven Q x = r • 1 := by
  let A : Submodule K (CliffordAlgebra Q) := LinearMap.range (ι Q)
  let E : Submodule K (CliffordAlgebra Q) := A ^ 0 ⊔ A ^ 2
  let O : Submodule K (CliffordAlgebra Q) := A ^ 1 ⊔ A ^ 3
  -- The dimension bound truncates the filtration at degree three; split those powers by parity.
  have hsplit : filtration Q 3 ≤ E ⊔ O := by
    rw [filtration_le_iff]
    intro l hl
    have hp := prod_map_ι_mem_pow Q l
    interval_cases hlen : l.length
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hp)
    · exact Submodule.mem_sup_right (Submodule.mem_sup_left hp)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right hp)
    · exact Submodule.mem_sup_right (Submodule.mem_sup_right hp)
  have hA0even : A ^ 0 ≤ evenOdd Q 0 := by
    simpa [A] using one_le_evenOdd_zero Q
  have hA2even : A ^ 2 ≤ evenOdd Q 0 := by
    rw [evenOdd]
    exact le_iSup (fun j : {n : ℕ // (n : ZMod 2) = 0} => A ^ (j : ℕ))
      ⟨2, by decide⟩
  have hEeven : E ≤ evenOdd Q 0 := sup_le hA0even hA2even
  have hA1odd : A ^ 1 ≤ evenOdd Q 1 := by
    simpa [A] using range_ι_le_evenOdd_one Q
  have hA3odd : A ^ 3 ≤ evenOdd Q 1 := by
    rw [evenOdd]
    exact le_iSup (fun j : {n : ℕ // (n : ZMod 2) = 1} => A ^ (j : ℕ))
      ⟨3, by decide⟩
  have hOodd : O ≤ evenOdd Q 1 := sup_le hA1odd hA3odd
  -- Reversal fixes degree zero and turns a degree-two generator pair into its polarization.
  have hA0P : A ^ 0 ≤ scalarAddReverseSubmodule Q := by
    intro y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp (by simpa [A] using hy)
    rw [mem_scalarAddReverseSubmodule_iff]
    exact ⟨r + r, by simp⟩
  have hA2P : A ^ 2 ≤ scalarAddReverseSubmodule Q := by
    rw [pow_two]
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [mem_scalarAddReverseSubmodule_iff]
    exact ⟨QuadraticMap.polar Q a b, by simpa using (ι_mul_ι_add_swap (Q := Q) a b).symm⟩
  have hEP : E ≤ scalarAddReverseSubmodule Q := sup_le hA0P hA2P
  have hxfiltration : (x : CliffordAlgebra Q) ∈ filtration Q 3 := by
    rw [filtration_eq_top_of_finrank_eq_three Q hV]
    trivial
  obtain ⟨e, he, o, ho, heo⟩ := Submodule.mem_sup.mp (hsplit hxfiltration)
  have hxeven : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]
    exact x.2
  -- Since `x` and its `E` component are even, parity disjointness kills the odd component.
  have hoEven : o ∈ evenOdd Q 0 := by
    have hsub := Submodule.sub_mem (evenOdd Q 0) hxeven (hEeven he)
    have hoeq : (x : CliffordAlgebra Q) - e = o := by rw [← heo]; abel
    rwa [hoeq] at hsub
  have hozero : o = 0 :=
    (Submodule.disjoint_def.mp (evenOdd_isCompl (Q := Q)).disjoint) o hoEven (hOodd ho)
  have hxP : (x : CliffordAlgebra Q) ∈ scalarAddReverseSubmodule Q := by
    rw [← heo, hozero, add_zero]
    exact hEP he
  rw [mem_scalarAddReverseSubmodule_iff] at hxP
  obtain ⟨r, hr⟩ := hxP
  refine ⟨r, Subtype.ext ?_⟩
  simpa [LinearMap.add_apply, Algebra.linearMap_apply, coe_reverseEven_apply,
    Algebra.smul_def] using hr.symm

/-- Reversal transported through an algebra equivalence to two-by-two matrices. -/
private noncomputable def reverseMatrix
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (q : QuadraticForm R M)
    (e : ↥(even q) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R :=
  e.toLinearMap.comp ((reverseEven q).comp e.symm.toLinearMap)

/-- Reversal transported to matrices computes from the even-subalgebra reversal. -/
@[simp] private theorem reverseMatrix_apply
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (q : QuadraticForm R M)
    (e : ↥(even q) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (A : Matrix (Fin 2) (Fin 2) R) :
    reverseMatrix q e A = e (reverseEven q (e.symm A)) := by
  simp [reverseMatrix]

/-- The transported reversal reverses products. -/
private theorem reverseMatrix_mul
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (q : QuadraticForm R M)
    (e : ↥(even q) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
    (A B : Matrix (Fin 2) (Fin 2) R) :
    reverseMatrix q e (A * B) = reverseMatrix q e B * reverseMatrix q e A := by
  rw [reverseMatrix_apply, reverseMatrix_apply, reverseMatrix_apply]
  rw [← map_mul]
  have hAB : e.symm (A * B) = e.symm A * e.symm B := map_mul e.symm A B
  rw [hAB]
  exact congrArg e (reverseEven_mul (Q := q) (e.symm A) (e.symm B))

/-- Every matrix plus its transported reversal is scalar. -/
private theorem exists_add_reverseMatrix_eq_smul_one
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ r : K, A + reverseMatrix Q e A = r • 1 := by
  obtain ⟨r, hr⟩ := exists_add_reverseEven_eq_smul_one_of_finrank_eq_three Q hV (e.symm A)
  refine ⟨r, ?_⟩
  rw [reverseMatrix_apply]
  calc
    A + e (reverseEven Q (e.symm A)) =
        e (e.symm A) + e (reverseEven Q (e.symm A)) := by rw [e.apply_symm_apply]
    _ = e (e.symm A + reverseEven Q (e.symm A)) := (map_add e _ _).symm
    _ = e (r • 1) := congrArg e hr
    _ = r • 1 := by rw [map_smul, map_one]

/-- Reversal transported through any two-by-two model is matrix adjugation. -/
theorem map_reverseEven_eq_adjugate_of_finrank_eq_three
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    e (reverseEven Q x) = Matrix.adjugate (e x) := by
  have hf := congrArg (fun g : Matrix (Fin 2) (Fin 2) K →ₗ[K] _ => g (e x))
    (Matrix.eq_adjugateFinTwoLinearMap_of_antimultiplicative_of_exists_add_eq_smul_one
      (reverseMatrix Q e) (reverseMatrix_mul Q e)
      (exists_add_reverseMatrix_eq_smul_one Q hV e))
  simpa only [reverseMatrix_apply, e.symm_apply_apply, coe_reverseEven_apply,
    Matrix.adjugateFinTwoLinearMap_apply] using hf

/-- The Clifford norm product maps to the matrix determinant times the identity. -/
 theorem map_reverseEven_mul_eq_det_smul_one_of_finrank_eq_three
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    e (reverseEven Q x * x) = (e x).det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [map_mul, map_reverseEven_eq_adjugate_of_finrank_eq_three Q hV e x]
  exact Matrix.adjugate_mul _

/-- The Clifford norm-one equation is equivalent to determinant one. -/
theorem reverseEven_mul_eq_one_iff_det_eq_one_of_finrank_eq_three
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    reverseEven Q x * x = 1 ↔ (e x).det = 1 := by
  constructor
  · intro h
    have hm := congrArg e h
    rw [map_reverseEven_mul_eq_det_smul_one_of_finrank_eq_three Q hV e x, map_one] at hm
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hm
    simpa using h00
  · intro hdet
    apply e.injective
    rw [map_one, map_reverseEven_mul_eq_det_smul_one_of_finrank_eq_three Q hV e x, hdet, one_smul]

/-- On the even Clifford subalgebra in dimension three, the Clifford `star`-norm equation is
equivalent to determinant one in any two-by-two matrix model. -/
theorem star_mul_self_eq_one_iff_det_eq_one_of_finrank_eq_three
    (hV : Module.finrank K V = 3)
    (e : ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : ↥(even Q)) :
    star (x : CliffordAlgebra Q) * x = 1 ↔ (e x).det = 1 := by
  constructor
  · intro hstar
    apply (reverseEven_mul_eq_one_iff_det_eq_one_of_finrank_eq_three Q hV e x).mp
    apply Subtype.ext
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply,
      reverse_eq_star_of_mem_even] using hstar
  · intro hdet
    have hreverse :=
      (reverseEven_mul_eq_one_iff_det_eq_one_of_finrank_eq_three Q hV e x).mpr hdet
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, coe_reverseEven_apply,
      reverse_eq_star_of_mem_even] using congrArg Subtype.val hreverse

end CliffordAlgebra
