/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.LinearCombination

public section

/-!
# The centre of the Hamilton quaternions

The Hamilton quaternions `ℍ[R]` over a commutative ring `R` are the free `R`-module on `1, i, j, k`
with `i² = j² = k² = -1`. This file computes their centre, and deduces that `ℍ[R]` is a *central*
`R`-algebra whenever `2` is a regular element of `R`. Over `ℝ` this makes `ℍ[ℝ]` a central simple
`ℝ`-algebra, since a division ring is a simple ring; the file closes by showing that this central
simple algebra is not split, that is, not isomorphic to a matrix algebra over `R`.

The computation runs through `TauCeti.Quaternion.commute_iff`, which says that two quaternions
commute exactly when `2` annihilates the three coordinates of the cross product of their imaginary
parts. That criterion holds over an arbitrary commutative ring, with no regularity assumption: in
characteristic two `ℍ[R]` really is commutative, and the criterion records that degeneration rather
than excluding it.

## Main results

* `TauCeti.Quaternion.commute_iff`: two quaternions commute iff `2` annihilates the cross product
  of their imaginary parts, and `TauCeti.Quaternion.commute_iff'`, its classical form for `2`
  regular: two quaternions commute iff the cross product of their imaginary parts vanishes, that
  is, iff the three `2 × 2` minors of the pair of imaginary parts all vanish. Over a field that is
  the statement that the imaginary parts are parallel; over a general commutative ring vanishing
  minors are weaker than one imaginary part being a scalar multiple of the other.
* `TauCeti.Quaternion.mem_center_iff`: a quaternion is central iff `2` annihilates each of its
  three imaginary coordinates.
* `TauCeti.Quaternion.center_eq_bot`: if `2` is left regular in `R`, the centre of `ℍ[R]` is the
  image of `R`.
* `TauCeti.Quaternion.instIsCentral`: `ℍ[R]` is a central `R`-algebra when `R` has no zero divisors
  and `2 ≠ 0` in `R`. This is the roadmap's `quaternion_isCentral` at `R = ℝ`.
* `TauCeti.Quaternion.isEmpty_algEquiv_matrix`: over a linearly ordered commutative ring, `ℍ[R]` is
  not isomorphic to a matrix algebra of size at least two, so over a field its Brauer class is
  nontrivial.

## Implementation notes

Everything is stated for `Quaternion R = ℍ[R]` rather than for Mathlib's general
`QuaternionAlgebra R c₁ c₂ c₃`. That is not a missed generalization: the centre genuinely depends on
the structure constants, and the general algebra need not be central even over `ℝ`. For instance in
`ℍ[ℝ, 0, 0, 0]` the products of `k` with each imaginary unit all vanish (`i * k = k * i = 0`,
`j * k = k * j = 0` and `k * k = 0`), so `k` is a central element outside the image of `ℝ`; the
other products of imaginary units are not all zero there, since `i * j = k` and `j * i = -k`.

The regularity hypothesis of `center_eq_bot` is carried as `IsLeftRegular (2 : R)`, which is exactly
what the proof consumes. `instIsCentral` restates it with the typeclass assumptions
`[NoZeroDivisors R] [NeZero (2 : R)]` so that instance search can discharge it; the roadmap's target
`R = ℝ` is an instance of that form.

## References

This file implements the Hamilton-quaternion worked example of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md`, whose `Suggested.lean` pins it
as `quaternion_isCentral`. The centrality of `ℍ` and the nonsplitting statement are the two halves
of the classical computation of the Brauer group of `ℝ`; see for instance P. Gille and
T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §1.1 and §2.1.
-/

open scoped Quaternion

namespace TauCeti

namespace Quaternion

section CommRing

variable {R : Type*} [CommRing R] {x y : ℍ[R]}

/-- **Two quaternions commute exactly when `2` annihilates the cross product of their imaginary
parts.** The real part of a commutator always vanishes, and its three imaginary coordinates are
twice the coordinates of the cross product `Im x × Im y`.

No regularity assumption on `2` is made, so the statement also covers characteristic two, where
`ℍ[R]` is commutative and all three conditions hold vacuously. -/
theorem commute_iff :
    Commute x y ↔
      2 * (x.imJ * y.imK - x.imK * y.imJ) = 0 ∧
        2 * (x.imK * y.imI - x.imI * y.imK) = 0 ∧
        2 * (x.imI * y.imJ - x.imJ * y.imI) = 0 := by
  rw [_root_.commute_iff_eq]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have h' := congrArg _root_.QuaternionAlgebra.imI h
      simp only [_root_.Quaternion.imI_mul] at h'
      linear_combination h'
    · have h' := congrArg _root_.QuaternionAlgebra.imJ h
      simp only [_root_.Quaternion.imJ_mul] at h'
      linear_combination h'
    · have h' := congrArg _root_.QuaternionAlgebra.imK h
      simp only [_root_.Quaternion.imK_mul] at h'
      linear_combination h'
  · rintro ⟨hI, hJ, hK⟩
    refine _root_.Quaternion.ext _ _ ?_ ?_ ?_ ?_
    · simp only [_root_.Quaternion.re_mul]; ring
    · simp only [_root_.Quaternion.imI_mul]; linear_combination hI
    · simp only [_root_.Quaternion.imJ_mul]; linear_combination hJ
    · simp only [_root_.Quaternion.imK_mul]; linear_combination hK

/-- **Two quaternions commute exactly when the cross product of their imaginary parts vanishes**,
once `2` is a left regular element of `R`. This is the classical form of
`TauCeti.Quaternion.commute_iff`: two quaternions commute precisely when the three `2 × 2` minors
of their imaginary parts vanish. Over a field that says the imaginary parts are parallel, but over
a general commutative ring vanishing minors do not force one imaginary part to be a scalar multiple
of the other. -/
theorem commute_iff' (h2 : IsLeftRegular (2 : R)) :
    Commute x y ↔
      x.imJ * y.imK = x.imK * y.imJ ∧
        x.imK * y.imI = x.imI * y.imK ∧
        x.imI * y.imJ = x.imJ * y.imI := by
  have key : ∀ a c : R, 2 * (a - c) = 0 ↔ a = c := fun a c ↦
    ⟨fun h ↦ sub_eq_zero.mp (h2 (by simpa using h)), fun h ↦ by simp [h]⟩
  rw [commute_iff, key, key, key]

/-- **A quaternion is central exactly when `2` annihilates each of its imaginary coordinates.**
Commuting with `i` and with `j` already forces all three conditions, and conversely those conditions
make the cross product criterion of `TauCeti.Quaternion.commute_iff` hold against every
quaternion. -/
theorem mem_center_iff :
    x ∈ Subalgebra.center R ℍ[R] ↔ 2 * x.imI = 0 ∧ 2 * x.imJ = 0 ∧ 2 * x.imK = 0 := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h
    -- Test `x` against `i` and against `j`.
    have hi : Commute x (⟨0, 1, 0, 0⟩ : ℍ[R]) := (h ⟨0, 1, 0, 0⟩).symm
    have hj : Commute x (⟨0, 0, 1, 0⟩ : ℍ[R]) := (h ⟨0, 0, 1, 0⟩).symm
    obtain ⟨-, hi₂, hi₃⟩ := commute_iff.mp hi
    obtain ⟨-, -, hj₃⟩ := commute_iff.mp hj
    -- Reduce the coordinates of the two literal quaternions `i` and `j`.
    dsimp only at hi₂ hi₃ hj₃
    refine ⟨by linear_combination hj₃, by linear_combination -hi₃, by linear_combination hi₂⟩
  · rintro ⟨hI, hJ, hK⟩ z
    refine (commute_iff.mpr ⟨?_, ?_, ?_⟩).symm.eq
    · linear_combination z.imK * hJ - z.imJ * hK
    · linear_combination z.imI * hK - z.imK * hI
    · linear_combination z.imJ * hI - z.imI * hJ

/-- **The centre of `ℍ[R]` is the image of `R`** as soon as `2` is a left regular element of `R`. -/
theorem center_eq_bot (h2 : IsLeftRegular (2 : R)) :
    Subalgebra.center R ℍ[R] = ⊥ := by
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  obtain ⟨hI, hJ, hK⟩ := mem_center_iff.mp hx
  have hI' : x.imI = 0 := h2 (by simpa using hI)
  have hJ' : x.imJ = 0 := h2 (by simpa using hJ)
  have hK' : x.imK = 0 := h2 (by simpa using hK)
  refine Algebra.mem_bot.mpr ⟨x.re, ?_⟩
  refine _root_.Quaternion.ext _ _ rfl ?_ ?_ ?_ <;> simp [hI', hJ', hK']

/-- **The Hamilton quaternions are a central algebra.** Over a commutative ring with no zero
divisors in which `2 ≠ 0`, the centre of `ℍ[R]` is exactly the image of `R`. Specialized to
`R = ℝ` this is the centrality half of the statement that `ℍ[ℝ]` is a central simple `ℝ`-algebra. -/
instance instIsCentral [NoZeroDivisors R] [NeZero (2 : R)] : Algebra.IsCentral R ℍ[R] :=
  ⟨(center_eq_bot fun _ _ h ↦ mul_left_cancel₀ (NeZero.ne (2 : R)) h).le⟩

end CommRing

section LinearOrderedCommRing

variable (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The Hamilton quaternions over a linearly ordered commutative ring are not split**: they are
not isomorphic, as an `R`-algebra, to a matrix algebra of size at least two. Such a matrix algebra
has nonzero zero divisors while `ℍ[R]` has none, so no isomorphism can exist.

Together with `TauCeti.Quaternion.instIsCentral` and the simplicity of a division ring this says,
for `R` a linearly ordered field, that the Brauer class of `ℍ[R]` is nontrivial; over `ℝ` it is the
nonidentity element of the Brauer group. -/
theorem isEmpty_algEquiv_matrix (n : Type*) [Fintype n] [DecidableEq n] [Nontrivial n] :
    IsEmpty (ℍ[R] ≃ₐ[R] Matrix n n R) := by
  refine ⟨fun f ↦ ?_⟩
  -- Two complementary nonzero diagonal idempotents of `Matrix n n R`, with vanishing product.
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  obtain ⟨d, e, hd, he, hde⟩ : ∃ d e : Matrix n n R, d ≠ 0 ∧ e ≠ 0 ∧ d * e = 0 := by
    refine ⟨Matrix.diagonal fun k ↦ if k = i then 1 else 0,
      Matrix.diagonal fun k ↦ if k = i then 0 else 1, fun h ↦ ?_, fun h ↦ ?_, ?_⟩
    · simpa using congrFun (Matrix.diagonal_eq_zero.mp h) i
    · simpa [hij.symm] using congrFun (Matrix.diagonal_eq_zero.mp h) j
    · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_zero]
      funext k
      by_cases hk : k = i <;> simp [hk]
  -- Pulling them back along `f.symm` contradicts the absence of zero divisors in `ℍ[R]`.
  have hsymm : f.symm d * f.symm e = 0 := by rw [← map_mul, hde, map_zero]
  rcases mul_eq_zero.mp hsymm with h | h
  · exact hd (by simpa using congrArg f h)
  · exact he (by simpa using congrArg f h)

end LinearOrderedCommRing

end Quaternion

end TauCeti
