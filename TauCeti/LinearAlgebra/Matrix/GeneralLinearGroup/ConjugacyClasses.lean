/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.companionFinTwo` occurs in the statements below, `Matrix.scalar` and the `2 × 2` matrix
-- notation come with it, and rational canonical form is what the classification runs on.
public import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo
-- `GL`, `Matrix.GeneralLinearGroup.scalar` and `Matrix.GeneralLinearGroup.det` occur in the
-- statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `Matrix.trace` occurs in the statements below, and `Matrix.trace_units_conj` in the proofs.
public import Mathlib.LinearAlgebra.Matrix.Trace
-- `ConjClasses` occurs in the statements below.
public import Mathlib.Algebra.Group.Conj
-- Non-public: `Nat.card_units`, `Nat.card_sum` and `Nat.card_prod` are used only in the final
-- count.
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: the arithmetic of the final count is closed by `ring`, in the proof only.
import Mathlib.Tactic.Ring

/-!
# The conjugacy classes of `GL₂` over a field

Rational canonical form in size two, proved in
`TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo`, says that a non-scalar `2 × 2` matrix
`M` over a field is similar to the companion matrix `!![0, -det M; 1, trace M]` of its
characteristic polynomial `X² - (trace M) X + det M`. Read inside the group, it classifies the
conjugacy classes of `GL₂(F)` completely: a scalar element is alone in its class, and two
non-scalar elements are conjugate exactly when their traces and their determinants agree.

Counting the classes over a finite field is then a matter of counting the invariants. The scalar
classes are indexed by the units `a`, giving `q - 1` of them; the non-scalar classes are indexed by
the pairs `(trace, det)` with the determinant a unit and the trace unconstrained, giving `q (q - 1)`
of them. Altogether `q² - 1`, which is the number of irreducible complex representations of
`GL₂(𝔽_q)`.

Being scalar is spelled `M ∈ Set.range (Matrix.scalar (Fin 2))`, as in
`TauCeti.LinearAlgebra.Matrix.Commute`, whose commutant computation is the companion result,
describing the centralizer of a non-scalar matrix rather than its conjugacy class.

## Main definitions

* `TauCeti.companionGL`: the companion matrix of `X² - t X + d` as an element of `GL₂`, for an
  invertible constant term.
* `TauCeti.conjRepGLFinTwo`: the chosen representative of each conjugacy class of `GL₂(F)`, indexed
  by `Fˣ ⊕ F × Fˣ`.
* `TauCeti.conjClassesGLFinTwoEquiv`: the resulting indexing of `ConjClasses (GL (Fin 2) F)`.

## Main results

* `TauCeti.isConj_companionGL`: **rational canonical form inside `GL₂(F)`**, a non-scalar element
  is conjugate to the companion element of its characteristic polynomial.
* `TauCeti.eq_of_mem_range_scalar_of_isConj`: a scalar element of `GL n R` is alone in its class.
* `TauCeti.isConj_iff_of_notMem_range_scalar`: **the classification**, two non-scalar elements of
  `GL₂(F)` are conjugate exactly when they have the same trace and the same determinant.
* `TauCeti.card_conjClasses_GL2`: `GL₂(𝔽_q)` has `q² - 1` conjugacy classes.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)": class representatives and the count
  `q² - 1 = Nat.card (ConjClasses (GL (Fin 2) F))`, matching the number of irreducibles. The final
  theorem carries the name `card_conjClasses_GL2` the roadmap gives it there.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.2.
-/

public section

open Matrix

namespace TauCeti

/-! ### Conjugacy invariants -/

section Invariants

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommSemiring R]

/-- Conjugate elements of `GL n R` have the same trace. -/
theorem trace_val_eq_of_isConj {g h : GL n R} (hgh : IsConj g h) :
    (g : Matrix n n R).trace = (h : Matrix n n R).trace := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hgh
  rw [← hc, Units.val_mul, Units.val_mul]
  exact (Matrix.trace_units_conj c _).symm

/-- **A scalar element of `GL n R` is alone in its conjugacy class**: scalar matrices are
central. -/
theorem eq_of_mem_range_scalar_of_isConj {g h : GL n R}
    (hg : (g : Matrix n n R) ∈ Set.range (Matrix.scalar n)) (hgh : IsConj g h) : g = h := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hgh
  obtain ⟨a, ha⟩ := hg
  have hcomm : c * g = g * c := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, ← ha]
    exact (Matrix.scalar_commute a (Commute.all a) (c : Matrix n n R)).symm.eq
  rw [← hc, hcomm, mul_assoc, mul_inv_cancel, mul_one]

end Invariants

/-! ### The classification in `GL₂` -/

section GeneralLinear

variable {F : Type*} [Field F]

/-- **The companion matrix of `X² - t X + d` as an element of `GL₂`**, for an invertible constant
term `d`. Every non-scalar element of `GL₂(F)` is conjugate to exactly one of these, by
`TauCeti.isConj_companionGL` and `TauCeti.isConj_iff_of_notMem_range_scalar`. -/
def companionGL (t : F) (d : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (companionFinTwo t (d : F))
    (by rw [det_companionFinTwo]; exact d.ne_zero)

@[simp]
theorem coe_companionGL (t : F) (d : Fˣ) :
    (companionGL t d : Matrix (Fin 2) (Fin 2) F) = companionFinTwo t (d : F) := (rfl)

/-- **The determinant of a companion element of `GL₂` is its constant term**, as a unit. The
matrix-level statement is `TauCeti.det_companionFinTwo`, reached from here by
`Matrix.GeneralLinearGroup.val_det_apply`. -/
@[simp]
theorem det_companionGL (t : F) (d : Fˣ) :
    Matrix.GeneralLinearGroup.det (companionGL t d) = d :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, coe_companionGL,
    det_companionFinTwo])

/-- A companion element of `GL₂` is not scalar. -/
theorem companionGL_notMem_range_scalar (t : F) (d : Fˣ) :
    (companionGL t d : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [coe_companionGL]
  exact companionFinTwo_notMem_range_scalar _ _

/-- A scalar element of `GL₂` is never a companion element. -/
theorem scalar_ne_companionGL (t : F) (d a : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a ≠ companionGL t d := by
  intro h
  refine companionGL_notMem_range_scalar t d ⟨(a : F), ?_⟩
  rw [← h]
  rfl

/-- **Rational canonical form inside `GL₂(F)`**: a non-scalar element is conjugate to the companion
element of its characteristic polynomial. -/
theorem isConj_companionGL {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) :
    IsConj g (companionGL (g : Matrix (Fin 2) (Fin 2) F).trace
      (Matrix.GeneralLinearGroup.det g)) := by
  obtain ⟨P, hP, hPM⟩ := exists_det_ne_zero_mul_eq_mul_companionFinTwo hg
  have hgp : g * Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
      = Matrix.GeneralLinearGroup.mkOfDetNeZero P hP *
        companionGL (g : Matrix (Fin 2) (Fin 2) F).trace (Matrix.GeneralLinearGroup.det g) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_companionGL,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact hPM
  refine isConj_iff.2 ⟨(Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hgp, ← mul_assoc, inv_mul_cancel, one_mul]

/-- **The conjugacy classification of the non-scalar elements of `GL₂(F)`**: two of them are
conjugate exactly when they have the same trace and the same determinant, that is, exactly when
they have the same characteristic polynomial.

The hypotheses are necessary: a scalar matrix has the same characteristic polynomial as the
corresponding Jordan block, and the two are not conjugate. -/
theorem isConj_iff_of_notMem_range_scalar {g h : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)))
    (hh : (h : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) :
    IsConj g h ↔ (g : Matrix (Fin 2) (Fin 2) F).trace = (h : Matrix (Fin 2) (Fin 2) F).trace ∧
      (g : Matrix (Fin 2) (Fin 2) F).det = (h : Matrix (Fin 2) (Fin 2) F).det := by
  refine ⟨fun hgh => ⟨trace_val_eq_of_isConj hgh, ?_⟩, fun ⟨ht, hd⟩ => ?_⟩
  · have hdet : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h :=
      isConj_iff_eq.1 (Matrix.GeneralLinearGroup.det.map_isConj hgh)
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hdet
  have hcomp : companionGL (g : Matrix (Fin 2) (Fin 2) F).trace
      (Matrix.GeneralLinearGroup.det g)
      = companionGL (h : Matrix (Fin 2) (Fin 2) F).trace (Matrix.GeneralLinearGroup.det h) := by
    rw [ht]
    congr 1
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hd])
  have hg' := isConj_companionGL hg
  rw [hcomp] at hg'
  exact hg'.trans (isConj_companionGL hh).symm

/-! ### Counting the classes -/

/-- **The chosen representatives of the conjugacy classes of `GL₂(F)`**: the scalar matrix `a • 1`
for a unit `a`, and the companion matrix of `X² - t X + d` for a scalar `t` and a unit `d`. The
first family is the centre and the second exhausts the non-scalar classes. -/
def conjRepGLFinTwo : Fˣ ⊕ F × Fˣ → GL (Fin 2) F
  | Sum.inl a => Matrix.GeneralLinearGroup.scalar (Fin 2) a
  | Sum.inr td => companionGL td.1 td.2

@[simp]
theorem conjRepGLFinTwo_inl (a : Fˣ) :
    (conjRepGLFinTwo (Sum.inl a) : GL (Fin 2) F)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) a := (rfl)

@[simp]
theorem conjRepGLFinTwo_inr (t : F) (d : Fˣ) :
    (conjRepGLFinTwo (Sum.inr (t, d)) : GL (Fin 2) F) = companionGL t d := (rfl)

/-- **The representatives meet every conjugacy class of `GL₂(F)` exactly once.** Surjectivity is
rational canonical form, injectivity the classification: a scalar is alone in its class, a
companion element is never scalar, and two companion elements with the same trace and determinant
are equal. -/
theorem bijective_mk_conjRepGLFinTwo :
    Function.Bijective fun x : Fˣ ⊕ F × Fˣ => ConjClasses.mk (conjRepGLFinTwo x) := by
  constructor
  · rintro (a | ⟨t, d⟩) (b | ⟨t', d'⟩) hab <;>
      simp only [ConjClasses.mk_eq_mk_iff_isConj, conjRepGLFinTwo_inl,
        conjRepGLFinTwo_inr] at hab
    · have hval := eq_of_mem_range_scalar_of_isConj (n := Fin 2) ⟨(a : F), rfl⟩ hab
      have hcoe := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hval
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at hcoe
      have : a = b := Units.ext (Matrix.scalar_inj.1 hcoe)
      rw [this]
    · exact absurd (eq_of_mem_range_scalar_of_isConj (n := Fin 2) ⟨(a : F), rfl⟩ hab)
        (scalar_ne_companionGL t' d' a)
    · exact absurd (eq_of_mem_range_scalar_of_isConj (n := Fin 2) ⟨(b : F), rfl⟩ hab.symm)
        (scalar_ne_companionGL t d b)
    · obtain ⟨ht, hd⟩ := (isConj_iff_of_notMem_range_scalar
        (companionGL_notMem_range_scalar t d) (companionGL_notMem_range_scalar t' d')).1 hab
      rw [coe_companionGL, coe_companionGL, trace_companionFinTwo, trace_companionFinTwo] at ht
      rw [coe_companionGL, coe_companionGL, det_companionFinTwo, det_companionFinTwo] at hd
      obtain rfl : t = t' := ht
      obtain rfl : d = d' := Units.ext hd
      rfl
  · intro C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    by_cases hg : (g : Matrix (Fin 2) (Fin 2) F) ∈ Set.range (Matrix.scalar (Fin 2))
    · obtain ⟨a, ha⟩ := hg
      have ha0 : a ≠ 0 := by
        rintro rfl
        have h1 : (g : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [← ha, map_zero, zero_mul] at h1
        exact zero_ne_one h1
      exact ⟨Sum.inl (Units.mk0 a ha0), congrArg ConjClasses.mk (Units.ext ha)⟩
    · exact ⟨Sum.inr ((g : Matrix (Fin 2) (Fin 2) F).trace, Matrix.GeneralLinearGroup.det g),
        ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_companionGL hg).symm⟩

/-- **The conjugacy classes of `GL₂(F)` are indexed by `Fˣ ⊕ F × Fˣ`**: a unit `a` indexes the
class of the scalar `a • 1`, and a pair `(t, d)` the class of the elements with trace `t` and
determinant `d` that are not scalar. -/
noncomputable def conjClassesGLFinTwoEquiv : Fˣ ⊕ F × Fˣ ≃ ConjClasses (GL (Fin 2) F) :=
  Equiv.ofBijective _ bijective_mk_conjRepGLFinTwo

@[simp]
theorem conjClassesGLFinTwoEquiv_apply (x : Fˣ ⊕ F × Fˣ) :
    conjClassesGLFinTwoEquiv x = ConjClasses.mk (conjRepGLFinTwo x) := (rfl)

end GeneralLinear

/-- **`GL₂(𝔽_q)` has `q² - 1` conjugacy classes**: `q - 1` central ones and `q (q - 1)` non-scalar
ones, indexed by their trace and their determinant. This is the number of irreducible complex
representations of `GL₂(𝔽_q)`, whose four families have dimensions `1`, `q`, `q + 1` and
`q - 1`.

The name is the roadmap's; the statement is the roadmap's with `[Fintype F]` weakened to
`[Finite F]`, nothing in the argument deciding equality. -/
theorem card_conjClasses_GL2 (F : Type*) [Field F] [Finite F] :
    Nat.card (ConjClasses (GL (Fin 2) F)) = Nat.card F ^ 2 - 1 := by
  rw [← Nat.card_congr (conjClassesGLFinTwoEquiv (F := F)), Nat.card_sum, Nat.card_prod,
    Nat.card_units F]
  obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by
    have := Nat.card_pos (α := F)
    omega⟩
  have e1 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
  rw [hm, Nat.add_sub_cancel, e1, Nat.add_sub_cancel]
  ring

end TauCeti
