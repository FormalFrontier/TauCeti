/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.KnotTheory.Burau.Basic

/-!
# The reduced Burau representation

The unreduced Burau representation on `Rⁿ` fixes the row covector
`(1, t, ..., t ^ (n - 1))`. Its kernel is consequently an invariant submodule of rank `n - 1`;
the action on that kernel is the **reduced Burau representation**. This file constructs the
invariant kernel and the reduced representation over an arbitrary commutative ring at an arbitrary
unit.

For a braid on `n + 1` strands, the coefficient of the zeroth coordinate in the invariant
covector is `1`. The kernel is therefore canonically free on the remaining `n` coordinates:
`TauCeti.KnotTheory.reducedBurauSpaceEquiv` sends `x : Fin n → R` to the vector whose tail is
`x` and whose zeroth coordinate is the unique value making the weighted coordinate sum vanish.
Transporting the kernel action across this equivalence gives
`TauCeti.KnotTheory.reducedBurau`, a representation on `Fin n → R` ready for matrix and
determinant computations.

This is the reduced-representation prerequisite for the braid route to the Alexander polynomial
in Layer 4 of the geometric-topology roadmap. The later Alexander construction will take
determinants of endomorphisms built from `reducedBurau n T β` and prove that the resulting
normalized expression is invariant under Markov moves.

## Main definitions

* `TauCeti.KnotTheory.geometricCovector`: the invariant covector with coordinates `t ^ i`.
* `TauCeti.KnotTheory.ReducedBurauSpace`: its kernel.
* `TauCeti.KnotTheory.reducedBurauSpaceEquiv`: the explicit equivalence
  `(Fin n → R) ≃ₗ ReducedBurauSpace (n + 1) t`.
* `TauCeti.KnotTheory.burauRepresentation`: the unreduced matrix representation read as a module
  representation.
* `TauCeti.KnotTheory.reducedBurauSubrepresentation`: its restriction to the invariant kernel.
* `TauCeti.KnotTheory.reducedBurau`: the reduced representation in free coordinates.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Princeton University Press (1974), Chapter 3.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1
  and 6.
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The Burau-invariant covector on `Rⁿ`, with coordinates `(1, t, ..., t ^ (n - 1))`. -/
def geometricCovector (n : ℕ) (t : R) : (Fin n → R) →ₗ[R] R :=
  dotProductBilin R R fun i ↦ t ^ (i : ℕ)

/-- The invariant covector is the weighted sum of the coordinates. -/
@[simp]
theorem geometricCovector_apply (n : ℕ) (t : R) (x : Fin n → R) :
    geometricCovector n t x = ∑ i : Fin n, t ^ (i : ℕ) * x i := by
  rfl

/-- The invariant submodule carrying the reduced Burau representation: the kernel of the
geometric covector. -/
def reducedBurauSpace (n : ℕ) (t : R) : Submodule R (Fin n → R) :=
  LinearMap.ker (geometricCovector n t)

/-- The type underlying the invariant submodule `reducedBurauSpace n t`. -/
abbrev ReducedBurauSpace (n : ℕ) (t : R) : Type _ := reducedBurauSpace n t

/-- Membership in the reduced Burau space means that the weighted coordinate sum vanishes. -/
@[simp]
theorem mem_reducedBurauSpace_iff (n : ℕ) (t : R) (x : Fin n → R) :
    x ∈ reducedBurauSpace n t ↔ ∑ i : Fin n, t ^ (i : ℕ) * x i = 0 := by
  simp [reducedBurauSpace]

end CommSemiring

section CommRing

variable [CommRing R]

/-- Coordinates on the reduced Burau space of an `(n + 1)`-strand braid. The tail coordinates
are free, and the zeroth coordinate is determined by the equation
`x₀ + ∑ i, t ^ (i + 1) x_(i+1) = 0`. -/
def reducedBurauSpaceEquiv (n : ℕ) (t : R) :
    (Fin n → R) ≃ₗ[R] ReducedBurauSpace (n + 1) t where
  toFun x := ⟨Fin.cons (-∑ i : Fin n, t ^ ((i : ℕ) + 1) * x i) x, by
    simp only [reducedBurauSpace, LinearMap.mem_ker, geometricCovector_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_mul,
      Fin.val_succ]
    abel⟩
  invFun x := Fin.tail x.1
  left_inv x := by
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ by simp only [Fin.tail, Fin.cons_succ]) i
    have hx := x.2
    simp only [reducedBurauSpace, LinearMap.mem_ker, geometricCovector_apply,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ] at hx
    simpa only [Fin.tail, Fin.cons_zero] using (eq_neg_of_add_eq_zero_left hx).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ by simp only [Submodule.coe_add, Pi.add_apply,
      Fin.cons_succ]) i
    simp only [Fin.cons_zero, Submodule.coe_add, Pi.add_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ by simp only [Submodule.coe_smul, Pi.smul_apply,
      Fin.cons_succ, RingHom.id_apply]) i
    simp only [Fin.cons_zero, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    have hsum : (∑ i : Fin n, t ^ ((i : ℕ) + 1) * (c * x i)) =
        c * ∑ i : Fin n, t ^ ((i : ℕ) + 1) * x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring

/-- The vector underlying `reducedBurauSpaceEquiv`: the free coordinates form its tail. -/
@[simp]
theorem reducedBurauSpaceEquiv_apply_coe (n : ℕ) (t : R) (x : Fin n → R) :
    (reducedBurauSpaceEquiv n t x : Fin (n + 1) → R) =
      Fin.cons (-∑ i : Fin n, t ^ ((i : ℕ) + 1) * x i) x := by
  simp [reducedBurauSpaceEquiv]

/-- The inverse coordinate map takes the tail of a vector in the reduced Burau space. -/
@[simp]
theorem reducedBurauSpaceEquiv_symm_apply (n : ℕ) (t : R)
    (x : ReducedBurauSpace (n + 1) t) :
    (reducedBurauSpaceEquiv n t).symm x = Fin.tail x.1 := by
  simp [reducedBurauSpaceEquiv]

/-- The unreduced Burau matrix representation, regarded as a representation on the free module of
column vectors. -/
def burauRepresentation (n : ℕ) (t : Rˣ) : Representation R (BraidGroup n) (Fin n → R) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (burau n t)))

/-- The module action of the unreduced Burau representation is multiplication by its Burau
matrix. -/
@[simp]
theorem burauRepresentation_apply (n : ℕ) (t : Rˣ) (b : BraidGroup n) (x : Fin n → R) :
    burauRepresentation n t b x = (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x :=
  by simp [burauRepresentation]

/-- The geometric covector is invariant under the unreduced Burau representation. -/
theorem geometricCovector_burauRepresentation (n : ℕ) (t : Rˣ) (b : BraidGroup n)
    (x : Fin n → R) :
    geometricCovector n (t : R) (burauRepresentation n t b x) =
      geometricCovector n (t : R) x := by
  rw [burauRepresentation_apply]
  calc
    geometricCovector n (t : R)
        ((burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x) =
        (fun k : Fin n ↦ (t : R) ^ (k : ℕ)) ⬝ᵥ
          ((burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x) := rfl
    _ = ((fun k : Fin n ↦ (t : R) ^ (k : ℕ)) ᵥ*
          (burau n t b : Matrix (Fin n) (Fin n) R)) ⬝ᵥ x := dotProduct_mulVec _ _ _
    _ = (fun k : Fin n ↦ (t : R) ^ (k : ℕ)) ⬝ᵥ x := by rw [vecMul_burau_geom]
    _ = geometricCovector n (t : R) x := rfl

/-- The kernel of the geometric covector is invariant under the unreduced Burau action. -/
theorem reducedBurauSpace_invariant (n : ℕ) (t : Rˣ) (b : BraidGroup n) :
    reducedBurauSpace n (t : R) ≤
      (reducedBurauSpace n (t : R)).comap (burauRepresentation n t b) := by
  intro x hx
  rw [reducedBurauSpace] at hx ⊢
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  rw [geometricCovector_burauRepresentation, hx]

/-- The reduced Burau representation on the invariant kernel of the geometric covector. -/
def reducedBurauSubrepresentation (n : ℕ) (t : Rˣ) :
    Representation R (BraidGroup n) (ReducedBurauSpace n (t : R)) :=
  (burauRepresentation n t).subrepresentation (reducedBurauSpace n (t : R))
    (reducedBurauSpace_invariant n t)

/-- The kernel representation acts by the unreduced Burau matrix on underlying vectors. -/
@[simp]
theorem coe_reducedBurauSubrepresentation_apply (n : ℕ) (t : Rˣ) (b : BraidGroup n)
    (x : ReducedBurauSpace n (t : R)) :
    (reducedBurauSubrepresentation n t b x : Fin n → R) =
      (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x.1 :=
  by
    rw [reducedBurauSubrepresentation, Representation.subrepresentation_apply]
    exact burauRepresentation_apply n t b x

/-- The reduced Burau representation of the braid group on `n + 1` strands, transported from the
invariant kernel to its `n` free tail coordinates. -/
def reducedBurau (n : ℕ) (t : Rˣ) : Representation R (BraidGroup (n + 1)) (Fin n → R) :=
  ((reducedBurauSpaceEquiv n (t : R)).symm.conjRingEquiv).toMonoidHom.comp
    (reducedBurauSubrepresentation (n + 1) t)

/-- The reduced action is obtained by inserting free coordinates into the invariant kernel,
applying the unreduced Burau matrix, and taking the tail. -/
@[simp]
theorem reducedBurau_apply (n : ℕ) (t : Rˣ) (b : BraidGroup (n + 1)) (x : Fin n → R) :
    reducedBurau n t b x = Fin.tail
      ((burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ
        (reducedBurauSpaceEquiv n (t : R) x : Fin (n + 1) → R)) :=
  by simp [reducedBurau]

/-- On an elementary braid, the reduced action is the tail of the elementary Burau matrix acting
on the canonical kernel coordinates. -/
theorem reducedBurau_sigma (n : ℕ) (t : Rˣ) (i : Fin n) (x : Fin n → R) :
    reducedBurau n t (BraidGroup.sigma i) x = Fin.tail
      (burauMatrix (t : R) i *ᵥ
        (reducedBurauSpaceEquiv n (t : R) x : Fin (n + 1) → R)) := by
  rw [reducedBurau_apply, burau_sigma, coe_burauGL]

/-- The individual free coordinates of the reduced action of an elementary braid: the `j`-th
coordinate of the reduced action is the `j.succ`-th coordinate of the unreduced action. This is
`TauCeti.KnotTheory.reducedBurau_sigma` evaluated at a coordinate, using that `Fin.tail v j` is by
definition `v j.succ`; it is the form in which entrywise computations with the reduced matrices are
carried out. -/
theorem reducedBurau_sigma_apply (n : ℕ) (t : Rˣ) (i : Fin n) (x : Fin n → R) (j : Fin n) :
    reducedBurau n t (BraidGroup.sigma i) x j =
      (burauMatrix (n := n + 1) (t : R) i *ᵥ
        (reducedBurauSpaceEquiv n (t : R) x : Fin (n + 1) → R)) j.succ := by
  rw [reducedBurau_sigma]
  rfl

/-- On two strands the reduced Burau representation sends the elementary braid to multiplication
by `-t`. This is the first nonzero-dimensional case and fixes the normalization of the reduced
representation. -/
@[simp]
theorem reducedBurau_sigma_zero_apply (t : Rˣ) (x : Fin 1 → R) :
    reducedBurau 1 t (BraidGroup.sigma 0) x 0 = -(t : R) * x 0 := by
  rw [reducedBurau_sigma_apply, burauMatrix_mulVec, burauRow_dotProduct]
  have hstrand : BraidGroup.strand (n := 2) 0 = 0 := by simp [Fin.ext_iff]
  have hstrandSucc : BraidGroup.strandSucc (n := 2) 0 = 1 := by simp [Fin.ext_iff]
  simp [hstrand, hstrandSucc, burauCol_apply]

end CommRing

end TauCeti.KnotTheory
