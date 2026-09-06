/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The classification of the conjugacy classes of `GL₂` by trace and determinant is what every
-- normal form below is checked against.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- `TauCeti.diagGL`, `TauCeti.jordanGL` and `TauCeti.GL2NonSplitTorusHom` are the three non-central
-- normal forms, and this module supplies the two facts that the first and the last of them are not
-- scalar.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer
-- Non-public: the extension theory of finite fields supplies the root of an irreducible quadratic,
-- inside a proof only.
import Mathlib.FieldTheory.Finite.Extension
-- Non-public: a quadratic without a root is irreducible, used only to build `AdjoinRoot`.
import Mathlib.Algebra.Polynomial.SpecificDegree
-- Non-public: `AdjoinRoot` and its power basis are the source of that root.
import Mathlib.RingTheory.AdjoinRoot

/-!
# The four conjugacy normal forms of `GL₂` over a finite field

`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean` classifies the conjugacy
classes of `GL₂(F)` by trace and determinant, with the companion matrix of the characteristic
polynomial as the representative of each non-scalar class. That representative is uniform but
anonymous. This file replaces it, over a finite field, by the four **named** normal forms the
character theory of `GL₂(𝔽_q)` is written against:

* a **central** scalar matrix `a • 1`;
* a **split semisimple** `TauCeti.diagGL ![a, b]` with `a ≠ b`;
* a **non-semisimple** Jordan block `TauCeti.jordanGL a 1`;
* an **elliptic** `TauCeti.GL2NonSplitTorusHom F E hE x`, multiplication by an element of a
  degree-`2` extension `E/F` that does not lie in `F`.

`TauCeti.exists_isConj_normalForm` is the resulting statement that every element of `GL₂(F)` is
conjugate to one of the four. It is what turns the four character values computed at these normal
forms in `TauCeti/RepresentationTheory/CharacterTable/GL2/CharacterValues.lean` into a full row of
the character table of `GL₂(𝔽_q)`: a character is a class function, so a row is determined once the
normal forms exhaust the classes.

The two non-central split forms need no finiteness and no extension. Each is the same two-line
check against `TauCeti.isConj_iff_of_notMem_range_scalar`: the normal form is not scalar, and its
trace and determinant are the prescribed ones. What the roots of `X² - t X + d` are is the only
thing that distinguishes them — two distinct roots give `diagGL`, a repeated root gives
`jordanGL`.

The elliptic case is the one that needs a quadratic extension, and it is where the finiteness of
`F` enters. Multiplication by `x : E` has trace `Tr_{E/F} x` and determinant `N_{E/F} x`
(`TauCeti.GL2NonSplitTorus.trace_gl2NonSplitTorusHom` and
`TauCeti.GL2NonSplitTorus.val_det_gl2NonSplitTorusHom`), so the normal form is pinned by
`TauCeti.trace_eq_of_mul_self_eq` and `TauCeti.norm_eq_of_mul_self_eq`: for `x` outside `F`
satisfying `x² = t x - d`, the pair `(1, x)` is an `F`-basis of `E` in which multiplication by `x`
*is* the companion matrix `TauCeti.companionFinTwo t d`, so its trace is `t` and its norm is `d`.
Producing such an `x` is `TauCeti.exists_mul_self_eq_of_finite`: over a finite field a quadratic
without a root in `F` is irreducible, `AdjoinRoot` of it is a degree-`2` extension, and any two
extensions of a finite field of the same degree are isomorphic
(`FiniteField.algEquivExtension`), so the supplied `E` already contains a root.

Uniqueness — that the four families are pairwise disjoint and that the parameters are determined up
to the evident symmetries `(a, b) ↦ (b, a)` and `x ↦ x^q` — is a separate statement and is not
proved here; `TauCeti.conjClassesGLFinTwoEquiv` already indexes the classes without it.

## Main results

* `TauCeti.isConj_diagGL_of_trace_of_det`, `TauCeti.isConj_jordanGL_one_of_trace_of_det` and
  `TauCeti.isConj_gl2NonSplitTorusHom_of_trace_of_det`: **the three non-central normal forms**, each
  characterized by its trace and determinant among the non-scalar elements.
* `TauCeti.trace_eq_of_mul_self_eq` and `TauCeti.norm_eq_of_mul_self_eq`: the trace and the norm of
  an element `x` of a degree-`2` extension satisfying `x² = t x - d`, and lying outside the base
  field, are `t` and `d`.
* `TauCeti.exists_mul_self_eq_of_finite`: over a finite field, a quadratic with no root in `F` has a
  root in every degree-`2` extension.
* `TauCeti.exists_isConj_normalForm`: **every element of `GL₂(F)`, for `F` finite with a degree-`2`
  extension `E`, is conjugate to one of the four normal forms.**

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)": the class representatives of the four
  families, the deliverable this file supplies alongside the count
  `TauCeti.card_conjClasses_GL2`.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.2.
-/

public section

open Matrix Polynomial

namespace TauCeti

variable {F : Type*} [Field F]

/-! ### The two split normal forms -/

/-- **The split semisimple normal form.** A non-scalar element of `GL₂(F)` whose characteristic
polynomial has the two *distinct* roots `a` and `b` is conjugate to `diagGL ![a, b]`. -/
theorem isConj_diagGL_of_trace_of_det {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)))
    {a b : Fˣ} (hab : a ≠ b)
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = (a : F) + b)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = (a : F) * b) :
    IsConj g (diagGL ![a, b]) := by
  refine (isConj_iff_of_notMem_range_scalar hg
    (notMem_range_scalar_diagGL (t := ![a, b]) (by simpa using hab))).2 ⟨?_, ?_⟩
  · rw [htrace, diagGL_coe, Matrix.trace_diagonal, Fin.sum_univ_two]
    simp
  · rw [hdet, diagGL_coe, Matrix.det_diagonal, Fin.prod_univ_two]
    simp

/-- **The non-semisimple normal form.** A non-scalar element of `GL₂(F)` whose characteristic
polynomial is `(X - a)²` is conjugate to the Jordan block `jordanGL a 1`. -/
theorem isConj_jordanGL_one_of_trace_of_det {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) {a : Fˣ}
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = 2 * (a : F))
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = (a : F) * a) :
    IsConj g (jordanGL a (1 : F)) := by
  refine (isConj_iff_of_notMem_range_scalar hg
    (notMem_range_scalar_jordanGL (one_ne_zero (α := F)))).2 ⟨?_, ?_⟩
  · rw [htrace, trace_jordanGL]
  · rw [hdet, coe_jordanGL, Matrix.det_fin_two_of]
    ring

/-! ### The trace and the norm of a quadratic irrationality -/

section Quadratic

variable {E : Type*} [Field E] [Algebra F E]

/-- An element of `E` outside `F` is linearly independent from `1` over `F`. -/
private theorem linearIndependent_one_root {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    LinearIndependent F ![(1 : E), x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hst' : algebraMap F E s + algebraMap F E t * x = 0 := by
    simpa [Algebra.smul_def] using hst
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨(algebraMap F E).injective (by simpa using hst'), rfl⟩
  · have ht' : algebraMap F E t ≠ 0 := fun h =>
      ht ((algebraMap F E).injective (by simpa using h))
    refine absurd ⟨-(s / t), ?_⟩ hx
    rw [map_neg, map_div₀]
    field_simp
    linear_combination -hst'

/-- The `F`-basis `(1, x)` of a degree-`2` extension `E/F` attached to an element `x` outside `F`.
It is used only to compute the trace and the norm of `x`, both of which are basis independent. -/
private noncomputable def oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : Module.Basis (Fin 2) F E :=
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  basisOfLinearIndependentOfCardEqFinrank (b := ![1, x]) (linearIndependent_one_root hx)
    (by simp [hE])

private theorem coe_oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : ⇑(oneRootBasis hE hx) = ![1, x] := by
  simp [oneRootBasis]

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
  rw [companionFinTwo_eq]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j <;> fin_cases i <;> simp [e0, e1]

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

end Quadratic

/-! ### The elliptic normal form -/

section Elliptic

variable {E : Type*} [Field E] [Algebra F E]

/-- **The elliptic normal form.** A non-scalar element of `GL₂(F)` whose characteristic polynomial
`X² - t X + d` is satisfied by an element `x` of a degree-`2` extension `E/F` lying outside `F` is
conjugate to the element `x` of the non-split torus. -/
theorem isConj_gl2NonSplitTorusHom_of_trace_of_det (hE : Module.finrank F E = 2)
    {g : GL (Fin 2) F} (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)))
    {x : Eˣ} (hx : (x : E) ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : (x : E) * x = algebraMap F E t * x - algebraMap F E d)
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = t)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = d) :
    IsConj g (GL2NonSplitTorusHom F E hE x) := by
  refine (isConj_iff_of_notMem_range_scalar hg
    (GL2NonSplitTorus.notMem_range_scalar_gl2NonSplitTorusHom hE hx)).2 ⟨?_, ?_⟩
  · rw [htrace, GL2NonSplitTorus.trace_gl2NonSplitTorusHom, trace_eq_of_mul_self_eq hE hx hx2]
  · rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply,
      GL2NonSplitTorus.val_det_gl2NonSplitTorusHom, norm_eq_of_mul_self_eq hE hx hx2]

end Elliptic

/-! ### A root of the characteristic polynomial in the quadratic extension -/

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

/-! ### The classification -/

/-- **Every element of `GL₂(F)` is conjugate to one of the four normal forms**, for `F` a finite
field with a supplied degree-`2` extension `E`: a central scalar, a split semisimple
`diagGL ![a, b]` with `a ≠ b`, a non-semisimple Jordan block `jordanGL a 1`, or an elliptic
element `GL2NonSplitTorusHom F E hE x` with `x` outside `F`.

This is what turns a computation of a character at these four normal forms into a full row of the
character table of `GL₂(𝔽_q)`. -/
theorem exists_isConj_normalForm [Finite F] (E : Type*) [Field E] [Algebra F E]
    (hE : Module.finrank F E = 2) (g : GL (Fin 2) F) :
    (∃ a : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) a = g) ∨
      (∃ a b : Fˣ, a ≠ b ∧ IsConj g (diagGL ![a, b])) ∨
      (∃ a : Fˣ, IsConj g (jordanGL a (1 : F))) ∨
      (∃ x : Eˣ, (x : E) ∉ Set.range (algebraMap F E) ∧
        IsConj g (GL2NonSplitTorusHom F E hE x)) := by
  classical
  by_cases hg : (g : Matrix (Fin 2) (Fin 2) F) ∈ Set.range (Matrix.scalar (Fin 2))
  · exact Or.inl (exists_scalar_eq_of_mem_range_scalar hg)
  set t := (g : Matrix (Fin 2) (Fin 2) F).trace with ht
  set d := (g : Matrix (Fin 2) (Fin 2) F).det with hd
  have hd0 : d ≠ 0 := by
    rw [hd, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  by_cases hsplit : ∃ a : F, a * a = t * a - d
  · obtain ⟨a, ha⟩ := hsplit
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hd0 (by linear_combination ha)
    have hb : a * (t - a) = d := by linear_combination -ha
    have hb0 : t - a ≠ 0 := fun h => hd0 (by rw [← hb, h, mul_zero])
    by_cases hab : a = t - a
    · refine Or.inr (Or.inr (Or.inl ⟨Units.mk0 a ha0, ?_⟩))
      refine isConj_jordanGL_one_of_trace_of_det hg ?_ ?_
      · simp only [Units.val_mk0]
        linear_combination -hab
      · simp only [Units.val_mk0]
        linear_combination -hb - a * hab
    · refine Or.inr (Or.inl ⟨Units.mk0 a ha0, Units.mk0 (t - a) hb0, ?_, ?_⟩)
      · simpa [Units.ext_iff] using hab
      · refine isConj_diagGL_of_trace_of_det hg (by simpa [Units.ext_iff] using hab) ?_ ?_
        · simp only [Units.val_mk0]
          ring
        · simp only [Units.val_mk0]
          linear_combination -hb
  · push Not at hsplit
    obtain ⟨x, hx2⟩ := exists_mul_self_eq_of_finite E hE hsplit
    have hxF : x ∉ Set.range (algebraMap F E) := by
      rintro ⟨a, rfl⟩
      refine hsplit a ?_
      have : algebraMap F E (a * a) = algebraMap F E (t * a - d) := by
        simpa using hx2
      exact (algebraMap F E).injective this
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxF ⟨0, by simp⟩
    refine Or.inr (Or.inr (Or.inr ⟨Units.mk0 x hx0, hxF, ?_⟩))
    exact isConj_gl2NonSplitTorusHom_of_trace_of_det hE hg hxF (by simpa using hx2) ht.symm hd.symm

end TauCeti
