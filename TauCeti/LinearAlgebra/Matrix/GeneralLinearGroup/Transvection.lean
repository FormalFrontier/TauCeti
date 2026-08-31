/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.transvection` and its product law are the subject of this file.
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
-- `TauCeti.diagGL` occurs in the conjugation statement below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `MonoidHom.noncommCoprod` packages products of commuting one-parameter subgroups.
public import Mathlib.GroupTheory.NoncommCoprod
-- Non-public: the diagonal-matrix-unit product law is used only in a proof below.
import TauCeti.GroupTheory.Commutator
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The commutator relations between transvections

Mathlib's `Matrix.transvection i j c = 1 + c Eᵢⱼ` is the elementary matrix adding `c` times the
`j`-th coordinate to the `i`-th one. For `i ≠ j` it is invertible, and Mathlib packages it as
`Matrix.SpecialLinearGroup.transvection`, together with its zero, addition and inverse laws; this
file views it in `GL n A` along `Matrix.SpecialLinearGroup.toGL` as `TauCeti.transvectionUnit` and
packages the resulting one-parameter subgroup as `TauCeti.transvectionHom`.

Writing `xᵢⱼ(c)` for the transvection, the relations are

* `xᵢⱼ(c) xₖₗ(d) = xₖₗ(d) xᵢⱼ(c)` whenever `j ≠ k` and `l ≠ i`;
* `⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd)` whenever `i`, `j` and `l` are distinct.

They are the **Chevalley commutator relations** of the general linear group. Reading the pair
`(i, j)` as the root `εᵢ - εⱼ` of the diagonal torus, the first covers every pair of roots whose
sum is neither a root nor zero, and the second every pair whose sum is a root:
`(εᵢ - εⱼ) + (εⱼ - εₗ)` is `εᵢ - εₗ`. In type `A` the structure constants are `±1`; the chosen
orientation in the second relation gives `1`, which is why its right-hand side is `xᵢₗ(cd)`.

The one remaining case, `xᵢⱼ(c)` against `xⱼᵢ(d)`, is deliberately absent: there the sum of the two
roots is zero, and no commutator formula in terms of a single root subgroup holds.

Conjugating a transvection by an invertible diagonal matrix rescales its parameter by the value of
the corresponding root: `TauCeti.diagGL_mul_transvectionUnit_mul_inv` says that `t xᵢⱼ(c) t⁻¹` is
`xᵢⱼ(tᵢ c tⱼ⁻¹)`. Together with the two relations above these are the equations that pin the
elementary matrices against the diagonal torus.

## Main definitions

* `TauCeti.transvectionUnit`: a transvection at a pair of distinct indices, as an element of
  `GL n A`, namely `Matrix.SpecialLinearGroup.transvection` along
  `Matrix.SpecialLinearGroup.toGL`.
* `TauCeti.transvectionHom`: the resulting homomorphism from the additive group of `A`.
* `TauCeti.commutingTransvectionPairHom`: the product of two commuting transvection
  homomorphisms, with a shared parameter.

## Main results

* `TauCeti.toGL_transvection_eq_transvectionUnit`: the defining equality relating the
  special-linear and general-linear transvection APIs.
* `TauCeti.transvectionUnit_mem_of_adjacent`: a subgroup containing the adjacent transvections
  in both orientations contains every transvection.
* `TauCeti.commute_transvectionUnit`: transvections at index pairs that do not chain commute.
* `TauCeti.commutatorElement_transvectionUnit` and
  `TauCeti.commutatorElement_transvectionUnit_reverse`: the commutators of two chaining
  transvections in either orientation.
* `TauCeti.det_transvectionUnit` and `TauCeti.transvectionUnit_injective`: a transvection has
  determinant `1`, and distinct parameters give distinct transvections.
* `TauCeti.diagGL_mul_transvectionUnit_mul_inv`: conjugation by an invertible diagonal matrix.
* `TauCeti.map_transvectionUnit`: transvections are natural in the base ring.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3, where these relations are the type `A`
  case of the Chevalley commutator formula.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open Matrix

open scoped commutatorElement

namespace TauCeti

universe u v

variable {n : Type*} [DecidableEq n] {A : Type u} {i j k l : n}

section Products

variable [Fintype n]

variable [CommRing A]

/-- Conjugating a transvection by a diagonal matrix rescales its parameter by the two
corresponding diagonal entries. The hypothesis says that the two diagonals are inverse to one
another. -/
theorem diagonal_mul_transvection_mul_diagonal {v w : n → A} (hvw : ∀ a, v a * w a = 1) (c : A) :
    diagonal v * transvection i j c * diagonal w = transvection i j (v i * c * w j) := by
  have hd : diagonal v * diagonal w = (1 : Matrix n n A) := by
    rw [Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_one.2 (by ext a; exact hvw a)
  simp only [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hd,
    diagonal_mul_single_mul_diagonal]

end Products

variable [CommRing A]

/-! ## Transvections as invertible matrices -/

section Unit

variable [Fintype n]

/-- A transvection at a pair of distinct indices, as an element of `GL n A`: Mathlib's
`Matrix.SpecialLinearGroup.transvection` viewed along `Matrix.SpecialLinearGroup.toGL`. It is the
value at `c` of the root subgroup homomorphism attached to the root `εᵢ - εⱼ` of the diagonal
torus. -/
def transvectionUnit (hij : i ≠ j) (c : A) : GL n A :=
  SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c)

/-- The matrix underlying `TauCeti.transvectionUnit` is the transvection itself. -/
@[simp]
theorem coe_transvectionUnit (hij : i ≠ j) (c : A) :
    (transvectionUnit hij c : Matrix n n A) = transvection i j c :=
  (rfl)

/-- Viewing a special-linear transvection in the general linear group gives
`TauCeti.transvectionUnit`. -/
theorem toGL_transvection_eq_transvectionUnit (hij : i ≠ j) (c : A) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c) =
      transvectionUnit hij c := by
  apply GeneralLinearGroup.ext
  intro p q
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_transvectionUnit]
  rfl

/-- The transvection of parameter zero is the identity. -/
@[simp]
theorem transvectionUnit_zero (hij : i ≠ j) : transvectionUnit hij (0 : A) = 1 := by
  rw [transvectionUnit, SpecialLinearGroup.transvection_coeff_zero, map_one]

/-- The parameter of a transvection is additive: the root subgroup is one-parameter. -/
@[simp]
theorem transvectionUnit_add (hij : i ≠ j) (c d : A) :
    transvectionUnit hij (c + d) = transvectionUnit hij c * transvectionUnit hij d := by
  simp only [transvectionUnit, SpecialLinearGroup.transvection_add, map_mul]

/-- The inverse of a transvection negates its parameter. -/
@[simp]
theorem transvectionUnit_inv (hij : i ≠ j) (c : A) :
    (transvectionUnit hij c)⁻¹ = transvectionUnit hij (-c) := by
  simp only [transvectionUnit, ← map_inv, SpecialLinearGroup.transvection_inv]

/-- A transvection has determinant one, so the root subgroup lands in `SLₙ`. -/
@[simp]
theorem det_transvectionUnit (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.det (transvectionUnit hij c) = 1 :=
  SpecialLinearGroup.coeToGL_det _

/-- The transvections at a fixed pair of distinct indices form a one-parameter subgroup of
`GL n A`, isomorphic to the additive group of `A`. This is the root subgroup of `εᵢ - εⱼ`. -/
def transvectionHom (hij : i ≠ j) : Multiplicative A →* GL n A :=
  (SpecialLinearGroup.toGL (n := n) (R := A)).comp (SpecialLinearGroup.transvectionHom hij)

/-- The value of the root subgroup homomorphism is the transvection of the parameter. -/
@[simp]
theorem transvectionHom_apply (hij : i ≠ j) (c : Multiplicative A) :
    transvectionHom hij c = transvectionUnit hij (Multiplicative.toAdd c) :=
  by simp [transvectionHom, transvectionUnit]

/-- Distinct parameters give distinct transvections: the parameter is the `(i, j)` entry. So the
root subgroup is a copy of the additive group of `A` inside `GL n A`, not a quotient of it. -/
theorem transvectionUnit_injective (hij : i ≠ j) :
    Function.Injective fun c : A => transvectionUnit hij c :=
  SpecialLinearGroup.toGL_injective.comp (SpecialLinearGroup.transvection_injective hij)

/-- The bundled root subgroup homomorphism is injective. -/
theorem transvectionHom_injective (hij : i ≠ j) :
    Function.Injective (transvectionHom (A := A) hij) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  apply transvectionUnit_injective hij
  simpa only [transvectionHom_apply] using h

/-- Transvections at index pairs that do not chain commute in `GL n A`. -/
theorem commute_transvectionUnit (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (c d : A) : Commute (transvectionUnit hij c) (transvectionUnit hkl d) :=
  (Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli c d).map
    Matrix.SpecialLinearGroup.toGL

/-- Two pointwise commuting transvection homomorphisms, evaluated at a shared parameter after a
chosen endomorphism in the second component. This packages the standard construction of a
one-parameter subgroup as a product of two commuting elementary one-parameter subgroups. -/
def commutingTransvectionPairHom (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (second : Multiplicative A →* Multiplicative A) : Multiplicative A →* GL n A :=
  ((transvectionHom hij).noncommCoprod (transvectionHom hkl)
      (fun c d ↦ by simpa only [transvectionHom_apply] using
        commute_transvectionUnit hij hkl hjk hli c.toAdd d.toAdd)).comp
    ((MonoidHom.id _).prod second)

/-- The commuting-pair homomorphism evaluates to the product of its two transvections. -/
@[simp]
theorem commutingTransvectionPairHom_apply (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (second : Multiplicative A →* Multiplicative A) (c : Multiplicative A) :
    commutingTransvectionPairHom hij hkl hjk hli second c =
      transvectionUnit hij c.toAdd * transvectionUnit hkl (second c).toAdd := by
  simp [commutingTransvectionPairHom]

/-- The product of two chaining transvections in `GL n A`, in the two orders. -/
theorem transvectionUnit_mul_transvectionUnit_eq_mul_mul
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (c d : A) :
    transvectionUnit hij c * transvectionUnit hjl d =
      transvectionUnit hjl d * transvectionUnit hij c * transvectionUnit hil (c * d) := by
  simp only [transvectionUnit, ← map_mul]
  exact congrArg SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul hij hjl hil c d)

/-- **The Chevalley commutator relation of type `A`.** The commutator of the root subgroup elements
`xᵢⱼ(c)` and `xⱼₗ(d)`, for distinct `i`, `j` and `l`, is `xᵢₗ(cd)`: the root `εᵢ - εₗ` is the sum
of `εᵢ - εⱼ` and `εⱼ - εₗ`, and the structure constant is `1`. -/
theorem commutatorElement_transvectionUnit (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (c d : A) :
    ⁅transvectionUnit hij c, transvectionUnit hjl d⁆ = transvectionUnit hil (c * d) := by
  simp only [transvectionUnit, ← map_commutatorElement]
  exact congrArg SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil c d)

/-- The reverse-orientation form of the type-`A` Chevalley commutator relation:
`[xᵢⱼ(c), xₖᵢ(d)] = xₖⱼ(-(dc))`. -/
theorem commutatorElement_transvectionUnit_reverse
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (c d : A) :
    ⁅transvectionUnit hij c, transvectionUnit hki d⁆ = transvectionUnit hkj (-(d * c)) := by
  calc
    ⁅transvectionUnit hij c, transvectionUnit hki d⁆ =
        ⁅transvectionUnit hki d, transvectionUnit hij c⁆⁻¹ :=
      (commutatorElement_inv _ _).symm
    _ = (transvectionUnit hkj (d * c))⁻¹ := by
      rw [commutatorElement_transvectionUnit hki hij hkj]
    _ = transvectionUnit hkj (-(d * c)) := transvectionUnit_inv hkj (d * c)

/-- If a subgroup of `GL (Fin (m + 1), A)` contains every adjacent transvection in both
orientations, then it contains every elementary transvection. -/
theorem transvectionUnit_mem_of_adjacent {m : ℕ}
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (m + 1)) A))
    (hadjacent : ∀ {i j : Fin (m + 1)} (hij : i ≠ j) (c : A),
      i.val + 1 = j.val ∨ j.val + 1 = i.val → transvectionUnit hij c ∈ H)
    {i j : Fin (m + 1)} (hij : i ≠ j) (c : A) : transvectionUnit hij c ∈ H := by
  exact Subgroup.mem_of_adjacent_of_commutator H
    (fun hij c => transvectionUnit hij c)
    (fun hij hjk hik a => by
      simpa using commutatorElement_transvectionUnit hij hjk hik a 1)
    hadjacent hij c

end Unit

/-! ## Naturality in the base ring -/

section Map

variable [Fintype n] {B : Type v} [CommRing B]

/-- A transvection is natural in the base ring: applying a ring homomorphism entrywise to
`xᵢⱼ(c)` gives `xᵢⱼ(f c)`. -/
@[simp]
theorem map_transvectionUnit (f : A →+* B) (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.map f (transvectionUnit hij c) = transvectionUnit hij (f c) := by
  ext a b
  exact congrArg (fun s : Matrix.SpecialLinearGroup n B => (s : Matrix n n B) a b)
    (SpecialLinearGroup.map_transvection f hij c)

end Map

/-! ## Conjugation by the diagonal torus -/

section Torus

variable {N : ℕ} {i j : Fin N}

/-- Conjugating the root subgroup element `xᵢⱼ(c)` by the diagonal matrix with entries `t`
rescales the parameter by `tᵢ tⱼ⁻¹`, the value at `t` of the root `εᵢ - εⱼ`. This is the equation
pinning the root subgroup against the diagonal torus. -/
theorem diagGL_mul_transvectionUnit_mul_inv (hij : i ≠ j) (t : Fin N → Aˣ) (c : A) :
    diagGL t * transvectionUnit hij c * (diagGL t)⁻¹ =
      transvectionUnit hij ((t i : A) * c * ((t j)⁻¹ : Aˣ)) := by
  have hval : ((((diagGL t)⁻¹ : GL (Fin N) A)) : Matrix (Fin N) (Fin N) A) =
      diagonal fun a => (((t a)⁻¹ : Aˣ) : A) := by
    rw [← map_inv diagGL t, diagGL_coe]
    simp
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transvectionUnit, coe_transvectionUnit, diagGL_coe, hval,
    diagonal_mul_transvection_mul_diagonal (fun a => (t a).mul_inv)]

end Torus

end TauCeti
