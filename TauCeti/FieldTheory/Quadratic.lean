/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Algebra.trace` occurs in the statements below, and `Algebra.trace_eq_matrix_trace` computes it.
public import Mathlib.RingTheory.Trace.Defs
-- `Algebra.norm` occurs in the statements below, and `Algebra.norm_eq_matrix_det` computes it.
public import Mathlib.RingTheory.Norm.Defs
-- Non-public: the matrix of multiplication by `x` in the basis `(1, x)` is the companion matrix
-- `TauCeti.companionFinTwo`, whose trace and determinant are already known; used in proofs only.
import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo
-- Non-public: `basisOfLinearIndependentOfCardEqFinrank` builds that basis, inside a proof only.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- Non-public: `linearIndependent_one_of_notMem_range_algebraMap` is the independence of `1` and
-- `x` that basis rests on; used in a proof only.
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
-- Non-public: the extension theory of finite fields supplies the root of an irreducible quadratic,
-- inside a proof only.
import Mathlib.FieldTheory.Finite.Extension
-- Non-public: a quadratic without a root is irreducible, used only to build `AdjoinRoot`.
import Mathlib.Algebra.Polynomial.SpecificDegree
-- Non-public: `AdjoinRoot` and its power basis are the source of that root.
import Mathlib.RingTheory.AdjoinRoot

/-!
# The trace and the norm of a quadratic irrationality

An element `x` of a degree-`2` extension `E/F` that does not lie in `F` satisfies a monic quadratic
`x² = t x - d` over `F`, and the pair `(1, x)` is then an `F`-basis of `E`. In that basis
multiplication by `x` **is** the companion matrix `TauCeti.companionFinTwo t d` of `X² - t X + d`,
which is the reading of the companion matrix its own docstring advertises. Since the trace and the
norm of `x` are the trace and the determinant of that matrix, and both are basis independent,
`Tr_{E/F} x = t` and `N_{E/F} x = d`.

Over a *finite* base field such an `x` always exists as soon as the quadratic has no root in `F`:
the quadratic is then irreducible, so `AdjoinRoot` of it is a degree-`2` extension of `F`, and any
two extensions of a finite field of the same degree are isomorphic
(`FiniteField.algEquivExtension`), so every degree-`2` extension already contains a root.

## Main results

* `TauCeti.Algebra.trace_eq_of_mul_self_eq` and `TauCeti.Algebra.norm_eq_of_mul_self_eq`: the trace
  and the norm of an element `x` of a degree-`2` extension satisfying `x² = t x - d`, and lying
  outside the base field, are `t` and `d`.
* `TauCeti.exists_mul_self_eq_of_finite`: over a finite field, a quadratic with no root in `F` has
  a root in every degree-`2` extension.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)": these are the facts that pin the elliptic
  normal form of `GL₂` in
  `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NormalForm.lean`.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F]

/-! ### The basis `(1, x)` -/

section Basis

variable {E : Type*} [Field E] [Algebra F E]

/-- The `F`-basis `(1, x)` of a degree-`2` extension `E/F` attached to an element `x` outside `F`.
It is used only to compute the trace and the norm of `x`, both of which are basis independent. -/
private noncomputable def oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : Module.Basis (Fin 2) F E :=
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  basisOfLinearIndependentOfCardEqFinrank (b := ![1, x])
    (linearIndependent_one_of_notMem_range_algebraMap F E hx) (by simp [hE])

private theorem coe_oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : ⇑(oneRootBasis hE hx) = ![1, x] := by
  simp only [oneRootBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- In the basis `(1, x)`, multiplication by `x` **is** the companion matrix of the monic quadratic
that `x` satisfies. -/
private theorem leftMulMatrix_oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : x * x = algebraMap F E t * x - algebraMap F E d) :
    Algebra.leftMulMatrix (oneRootBasis hE hx) x = companionFinTwo t d := by
  have hb := coe_oneRootBasis hE hx
  have e0 : x * oneRootBasis hE hx 0 = oneRootBasis hE hx 1 := by
    simp [hb]
  have e1 : x * oneRootBasis hE hx 1
      = (-d) • oneRootBasis hE hx 0 + t • oneRootBasis hE hx 1 := by
    simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one, map_neg]
    linear_combination hx2
  rw [companionFinTwo_def]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j <;> fin_cases i <;> simp [e0, e1]

end Basis

/-! ### The trace and the norm -/

namespace Algebra

variable {E : Type*} [Field E] [Algebra F E]

/-- **The trace of a quadratic irrationality.** If `E/F` has degree `2` and `x : E` lies outside
`F` and satisfies `x² = t x - d`, then `Tr_{E/F} x = t`. -/
theorem trace_eq_of_mul_self_eq (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : x * x = algebraMap F E t * x - algebraMap F E d) :
    Algebra.trace F E x = t := by
  rw [Algebra.trace_eq_matrix_trace (oneRootBasis hE hx), leftMulMatrix_oneRootBasis hE hx hx2,
    trace_companionFinTwo]

/-- **The norm of a quadratic irrationality.** If `E/F` has degree `2` and `x : E` lies outside `F`
and satisfies `x² = t x - d`, then `N_{E/F} x = d`. -/
theorem norm_eq_of_mul_self_eq (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : x * x = algebraMap F E t * x - algebraMap F E d) :
    Algebra.norm F x = d := by
  rw [Algebra.norm_eq_matrix_det (oneRootBasis hE hx), leftMulMatrix_oneRootBasis hE hx hx2,
    det_companionFinTwo]

end Algebra

/-! ### A root of the quadratic in the extension -/

/-- **Over a finite field a quadratic without a root has a root in every degree-`2` extension.**
A quadratic with no root in `F` is irreducible, so `AdjoinRoot` of it is a degree-`2` extension of
`F`; over a finite field any two extensions of the same degree are isomorphic, so the supplied `E`
already contains a root. -/
theorem exists_mul_self_eq_of_finite [Finite F] (E : Type*) [Field E] [Algebra F E]
    (hE : Module.finrank F E = 2) {t d : F} (hroot : ∀ a : F, a * a ≠ t * a - d) :
    ∃ x : E, x * x = algebraMap F E t * x - algebraMap F E d := by
  classical
  have key : ∃ y : E, (Polynomial.aeval y) (X ^ 2 - C t * X + C d : F[X]) = 0 := by
    set p : F[X] := X ^ 2 - C t * X + C d with hpdef
    have hdeg : p.natDegree = 2 := by rw [hpdef]; compute_degree!
    have hmonic : p.Monic := by rw [hpdef]; monicity!
    have hirr : Irreducible p := by
      refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) fun a ha => ?_
      refine hroot a ?_
      rw [Polynomial.IsRoot, hpdef] at ha
      simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X] at ha
      linear_combination ha
    have : Fact (Irreducible p) := ⟨hirr⟩
    have hfr : Module.finrank F (AdjoinRoot p) = 2 := by
      rw [PowerBasis.finrank (AdjoinRoot.powerBasis hmonic.ne_zero), AdjoinRoot.powerBasis_dim,
        hdeg]
    obtain ⟨q, hq⟩ := CharP.exists F
    have : Fact q.Prime := ⟨CharP.char_is_prime F q⟩
    let e : AdjoinRoot p ≃ₐ[F] E :=
      (FiniteField.algEquivExtension F q 2 (AdjoinRoot p) hfr).trans
        (FiniteField.algEquivExtension F q 2 E hE).symm
    refine ⟨e (AdjoinRoot.root p), ?_⟩
    rw [Polynomial.aeval_algHom_apply e, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  obtain ⟨y, hy⟩ := key
  simp only [map_add, map_sub, map_pow, map_mul, aeval_C, aeval_X] at hy
  exact ⟨y, by linear_combination hy⟩

end TauCeti
