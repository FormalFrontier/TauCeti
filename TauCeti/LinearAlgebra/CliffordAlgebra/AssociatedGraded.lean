/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.Algebra.DirectSum.Algebra
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# Associated-graded algebra of a Clifford filtration

This file packages the homogeneous pieces of the Clifford degree filtration into a direct-sum
associated-graded algebra. It is generic in the quadratic form and does not yet identify that
algebra with the exterior algebra.

It advances the Layer 0 associated-graded-algebra target in the
[Spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-0-the-clifford-algebra-its-universal-property-and-the-two-gradings).

Its graded-algebra packaging adapts the pattern in Mathlib's
[`TensorPower` construction](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/TensorPower/Basic.lean).

## Main definitions

* `CliffordAlgebra.filtrationAssociatedGraded Q`: the direct sum
  `⨁ k, FiltrationGradedPiece Q k` of the homogeneous pieces.
* `CliffordAlgebra.filtrationGradedMul`: the product of two homogeneous pieces, induced by
  Clifford multiplication through `filtration_mul`.
* `CliffordAlgebra.filtrationGradedOne` and
  `CliffordAlgebra.filtrationGradedAlgebraMap₀`: the degree-zero unit and the degree-zero
  image of a scalar.

## Main results

* The graded structure instances assembling those pieces:
  `CliffordAlgebra.filtrationGradedGOne`, `filtrationGradedGMul`,
  `filtrationGradedGMonoid`, `filtrationGradedGRing`, `filtrationGradedGSemiring` and
  `filtrationGradedGAlgebra`, culminating in
  `CliffordAlgebra.filtrationAssociatedGradedRing`, the ring structure on the direct sum.

## Implementation notes

`filtrationGradedGSemiring` and `filtrationAssociatedGradedRing` are stated explicitly rather than
left to instance search. `DirectSum.GRing` is declared over `[∀ i, AddCommGroup (A i)]`, so
`DirectSum.GRing.toGSemiring` supplies the pointwise `AddCommMonoid` through
`AddCommGroup.toAddCommMonoid`, which does not match the one instance search finds directly for
`FiltrationGradedPiece`; without these two declarations neither
`DirectSum.GSemiring (FiltrationGradedPiece Q)` nor `Ring (filtrationAssociatedGraded Q)` is
synthesizable.
-/

public section

open CliffordAlgebra
open scoped DirectSum

universe u v

namespace CliffordAlgebra

open TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The direct sum of the homogeneous pieces of the Clifford degree filtration. -/
abbrev filtrationAssociatedGraded (Q : QuadraticForm R M) : Type max u v :=
  ⨁ k : ℕ, FiltrationGradedPiece Q k

private noncomputable def filtrationMul (Q : QuadraticForm R M) (i j : ℕ) :
    filtration Q i →ₗ[R] filtration Q j →ₗ[R] filtration Q (i + j) :=
  TensorProduct.curry
    ((LinearEquiv.ofEq _ _ (filtration_mul Q i j)).toLinearMap ∘ₗ
      Submodule.mulMap' (filtration Q i) (filtration Q j))

private noncomputable def filtrationGradedPreMul (Q : QuadraticForm R M) (i j : ℕ) :
    filtration Q i →ₗ[R] filtration Q j →ₗ[R] FiltrationGradedPiece Q (i + j) :=
  (filtrationMul Q i j).compr₂ (Submodule.mkQ _)

private theorem filtrationGradedPreMul_apply (Q : QuadraticForm R M) (i j : ℕ)
    (x : filtration Q i) (y : filtration Q j) :
    filtrationGradedPreMul Q i j x y =
      Submodule.Quotient.mk
        (⟨(x : CliffordAlgebra Q) * y, mul_mem_filtration Q x.property y.property⟩ :
          filtration Q (i + j)) :=
  rfl

private theorem filtrationGradedPreMul_mem_ker_left (Q : QuadraticForm R M) (i j : ℕ) :
    filtrationPreviousRestricted Q i ≤
      (filtrationGradedPreMul Q i j).ker := by
  rintro ⟨x, hx⟩ hprevious
  rw [mem_filtrationPreviousRestricted_iff] at hprevious
  rw [LinearMap.mem_ker]
  ext y
  simp only [filtrationGradedPreMul_apply, LinearMap.zero_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  rw [mem_filtrationPreviousRestricted_iff]
  -- The filtration product lemma is stated for ambient Clifford-algebra elements.
  change (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q) ∈ filtrationPrevious Q (i + j)
  exact mul_mem_filtrationPrevious_left Q hprevious y.property

private theorem filtrationGradedPreMul_mem_ker_right (Q : QuadraticForm R M) (i j : ℕ) :
    filtrationPreviousRestricted Q j ≤
      (filtrationGradedPreMul Q i j).flip.ker := by
  rintro ⟨y, hy⟩ hprevious
  rw [mem_filtrationPreviousRestricted_iff] at hprevious
  rw [LinearMap.mem_ker]
  ext x
  simp only [LinearMap.flip_apply, LinearMap.zero_apply]
  rw [filtrationGradedPreMul_apply, Submodule.Quotient.mk_eq_zero]
  rw [mem_filtrationPreviousRestricted_iff]
  -- The filtration product lemma is stated for ambient Clifford-algebra elements.
  change (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q) ∈ filtrationPrevious Q (i + j)
  exact mul_mem_filtrationPrevious_right Q x.property hprevious

/-- Multiplication of two homogeneous pieces of the Clifford associated graded algebra. -/
noncomputable def filtrationGradedMul (Q : QuadraticForm R M) (i j : ℕ) :
    FiltrationGradedPiece Q i →ₗ[R] FiltrationGradedPiece Q j →ₗ[R]
      FiltrationGradedPiece Q (i + j) :=
  (filtrationGradedPreMul Q i j).liftQ₂ _ _
    (filtrationGradedPreMul_mem_ker_left Q i j)
    (filtrationGradedPreMul_mem_ker_right Q i j)

/-- On quotient representatives, the homogeneous product is induced by Clifford multiplication. -/
@[simp]
theorem filtrationGradedMul_apply_mk (Q : QuadraticForm R M) (i j : ℕ) (x : filtration Q i)
    (y : filtration Q j) :
    filtrationGradedMul Q i j (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (⟨(x : CliffordAlgebra Q) * y, mul_mem_filtration Q x.property y.property⟩ :
          filtration Q (i + j)) :=
  by
  rw [filtrationGradedMul, LinearMap.liftQ₂_mk]
  exact filtrationGradedPreMul_apply Q i j x y

private theorem filtrationGradedPiece_cast_mk' (Q : QuadraticForm R M) {i j : ℕ}
    (h : i = j) (x : filtration Q i) :
    cast (congrArg (FiltrationGradedPiece Q) h) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cast (congrArg (fun k => ↥(filtration Q k)) h) x) := by
  subst j
  rfl

private theorem filtration_coe_cast (Q : QuadraticForm R M) {i j : ℕ}
    (h : i = j) (x : filtration Q i) :
    ((cast (congrArg (fun k => ↥(filtration Q k)) h) x : filtration Q j) :
      CliffordAlgebra Q) = x := by
  subst j
  rfl

/-- Homogeneous Clifford filtration multiplication is associative after reindexing degrees. -/
theorem filtrationGradedMul_assoc (Q : QuadraticForm R M) (i j k : ℕ)
    (x : FiltrationGradedPiece Q i) (y : FiltrationGradedPiece Q j)
    (z : FiltrationGradedPiece Q k) :
    cast (congrArg (FiltrationGradedPiece Q) (Nat.add_assoc i j k))
      (filtrationGradedMul Q (i + j) k (filtrationGradedMul Q i j x y) z) =
      filtrationGradedMul Q i (j + k) x (filtrationGradedMul Q j k y z) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          induction z using Submodule.Quotient.induction_on with
          | _ z =>
              simp only [filtrationGradedMul_apply_mk]
              rw [filtrationGradedPiece_cast_mk' Q (Nat.add_assoc i j k)]
              apply (Submodule.Quotient.eq _).mpr
              rw [mem_filtrationPreviousRestricted_iff, Submodule.coe_sub,
                filtration_coe_cast Q (Nat.add_assoc i j k)]
              -- Compare the two representatives in the ambient Clifford algebra.
              change ((x : CliffordAlgebra Q) * y) * z - x * (y * z) ∈
                filtrationPrevious Q (i + (j + k))
              rw [mul_assoc, sub_self]
              exact Submodule.zero_mem (filtrationPrevious Q (i + (j + k)))

/-- The degree-zero unit of the homogeneous Clifford filtration pieces. -/
noncomputable def filtrationGradedOne (Q : QuadraticForm R M) :
    FiltrationGradedPiece Q 0 :=
  Submodule.Quotient.mk ⟨1, one_mem_filtration Q 0⟩

/-- The degree-zero unit is the quotient class of the Clifford unit. -/
theorem filtrationGradedOne_def (Q : QuadraticForm R M) :
    filtrationGradedOne Q =
      Submodule.Quotient.mk (⟨1, one_mem_filtration Q 0⟩ : filtration Q 0) := by
  rfl

/-- The quotient class of the Clifford unit is the degree-zero homogeneous unit. -/
@[simp] theorem filtrationGradedOne_mk (Q : QuadraticForm R M) :
    Submodule.Quotient.mk (⟨1, one_mem_filtration Q 0⟩ : filtration Q 0) =
      filtrationGradedOne Q :=
  (filtrationGradedOne_def Q).symm

/-- The degree-zero class of a scalar in the associated graded Clifford filtration. -/
noncomputable def filtrationGradedAlgebraMap₀ (Q : QuadraticForm R M) :
    R →+ FiltrationGradedPiece Q 0 where
  toFun r := Submodule.Quotient.mk
    ⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩
  map_zero' := by simp
  map_add' r s := by
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (map_add (algebraMap R (CliffordAlgebra Q)) r s)

/-- The degree-zero scalar map is the quotient class of its ambient scalar. -/
theorem filtrationGradedAlgebraMap₀_apply (Q : QuadraticForm R M) (r : R) :
    filtrationGradedAlgebraMap₀ Q r =
      Submodule.Quotient.mk
        (⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ :
          filtration Q 0) := by
  rfl

/-- The quotient class of an ambient scalar is its degree-zero homogeneous class. -/
@[simp] theorem filtrationGradedAlgebraMap₀_mk (Q : QuadraticForm R M) (r : R) :
    Submodule.Quotient.mk
      (⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ :
        filtration Q 0) = filtrationGradedAlgebraMap₀ Q r :=
  (filtrationGradedAlgebraMap₀_apply Q r).symm

/-- The degree-zero scalar map sends `1` to the homogeneous unit. -/
@[simp] theorem filtrationGradedAlgebraMap₀_one (Q : QuadraticForm R M) :
    filtrationGradedAlgebraMap₀ Q 1 = filtrationGradedOne Q := by
  -- Expand the two degree-zero representatives to compare their quotient classes;
  -- `map_one` is stated only in the ambient Clifford algebra.
  change Submodule.Quotient.mk
      (⟨algebraMap R (CliffordAlgebra Q) 1, algebraMap_mem_filtration Q 1 0⟩ : filtration Q 0) =
    Submodule.Quotient.mk (⟨1, one_mem_filtration Q 0⟩ : filtration Q 0)
  apply (Submodule.Quotient.eq _).mpr
  rw [mem_filtrationPreviousRestricted_iff]
  -- Quotient equality is ambient membership, the form in which `map_one` applies.
  change algebraMap R (CliffordAlgebra Q) 1 - 1 ∈ filtrationPrevious Q 0
  rw [map_one, sub_self]
  exact Submodule.zero_mem _

/-- The degree-zero homogeneous unit acts on the left. -/
@[simp] theorem filtrationGradedOne_mul (Q : QuadraticForm R M) (k : ℕ)
    (x : FiltrationGradedPiece Q k) :
    filtrationGradedMul Q 0 k (filtrationGradedOne Q) x =
      cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k).symm) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      -- Quotient induction supplies representatives, the only stable form to which the
      -- public representative multiplication lemma applies.
      change filtrationGradedMul Q 0 k (Submodule.Quotient.mk _)
        (Submodule.Quotient.mk x) = _
      rw [filtrationGradedMul_apply_mk]
      rw [filtrationGradedPiece_cast_mk' Q (Nat.zero_add k).symm]
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_filtrationPreviousRestricted_iff, Submodule.coe_sub,
        filtration_coe_cast Q (Nat.zero_add k).symm]
      -- Quotient equality is now ambient membership, the form of the filtration product API.
      change (1 : CliffordAlgebra Q) * (x : CliffordAlgebra Q) - x ∈
        filtrationPrevious Q (0 + k)
      rw [one_mul, sub_self]
      exact Submodule.zero_mem (filtrationPrevious Q (0 + k))

/-- The degree-zero homogeneous unit acts on the right. -/
@[simp] theorem filtrationGradedMul_one (Q : QuadraticForm R M) (k : ℕ)
    (x : FiltrationGradedPiece Q k) :
    filtrationGradedMul Q k 0 x (filtrationGradedOne Q) =
      cast (congrArg (FiltrationGradedPiece Q) (Nat.add_zero k).symm) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      -- Quotient induction supplies representatives, the only stable form to which the
      -- public representative multiplication lemma applies.
      change filtrationGradedMul Q k 0 (Submodule.Quotient.mk x)
        (Submodule.Quotient.mk _) = _
      rw [filtrationGradedMul_apply_mk]
      rw [filtrationGradedPiece_cast_mk' Q (Nat.add_zero k).symm]
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_filtrationPreviousRestricted_iff, Submodule.coe_sub,
        filtration_coe_cast Q (Nat.add_zero k).symm]
      -- Quotient equality is now ambient membership, the form of the filtration product API.
      change (x : CliffordAlgebra Q) * 1 - x ∈ filtrationPrevious Q (k + 0)
      rw [mul_one, sub_self]
      exact Submodule.zero_mem (filtrationPrevious Q (k + 0))

/-- The homogeneous degree-zero class supplies the `GOne` structure on filtration pieces. -/
noncomputable instance filtrationGradedGOne {Q : QuadraticForm R M} :
    GradedMonoid.GOne (FiltrationGradedPiece Q) where
  one := filtrationGradedOne Q

/-- Homogeneous filtration multiplication supplies the `GMul` structure on filtration pieces. -/
noncomputable instance filtrationGradedGMul {Q : QuadraticForm R M} :
    GradedMonoid.GMul (FiltrationGradedPiece Q) where
  mul {i j} := fun x y => filtrationGradedMul Q i j x y

/-- The homogeneous unit and multiplication form a graded monoid of filtration pieces. -/
noncomputable instance filtrationGradedGMonoid {Q : QuadraticForm R M} :
    GradedMonoid.GMonoid (FiltrationGradedPiece Q) :=
  { filtrationGradedGMul (Q := Q), filtrationGradedGOne (Q := Q) with
    one_mul := fun x => by
      rcases x with ⟨k, x⟩
      apply Sigma.ext (Nat.zero_add k)
      apply heq_of_cast_eq (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k))
      -- The sigma equality is now a homogeneous equality after exposing the GOne and GMul fields.
      change cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k))
        (filtrationGradedMul Q 0 k (filtrationGradedOne Q) x) = x
      rw [filtrationGradedOne_mul]
      simp
    mul_one := fun x => by
      rcases x with ⟨k, x⟩
      apply Sigma.ext (Nat.add_zero k)
      apply heq_of_cast_eq (congrArg (FiltrationGradedPiece Q) (Nat.add_zero k))
      -- The sigma equality is now a homogeneous equality after exposing the GOne and GMul fields.
      change cast (congrArg (FiltrationGradedPiece Q) (Nat.add_zero k))
        (filtrationGradedMul Q k 0 x (filtrationGradedOne Q)) = x
      rw [filtrationGradedMul_one]
      simp
    mul_assoc := fun x y z => by
      rcases x with ⟨i, x⟩
      rcases y with ⟨j, y⟩
      rcases z with ⟨k, z⟩
      apply Sigma.ext (Nat.add_assoc i j k)
      apply heq_of_cast_eq (congrArg (FiltrationGradedPiece Q) (Nat.add_assoc i j k))
      exact filtrationGradedMul_assoc Q i j k x y z }

/-- Bilinearity and scalar casts make the homogeneous pieces a direct-sum graded ring. -/
noncomputable instance filtrationGradedGRing {Q : QuadraticForm R M} :
    DirectSum.GRing (FiltrationGradedPiece Q) where
  mul_zero := fun x => (filtrationGradedMul Q _ _ x).map_zero
  zero_mul := fun x => by
    -- `DirectSum.GRing` states this through `GMul`; expose its declared homogeneous product.
    change filtrationGradedMul Q _ _ 0 x = 0
    rw [LinearMap.map_zero]
    rfl
  mul_add := fun x y z => (filtrationGradedMul Q _ _ x).map_add y z
  add_mul := fun x y z => by
    -- `DirectSum.GRing` states this through `GMul`; expose its declared homogeneous product.
    change filtrationGradedMul Q _ _ (x + y) z =
      filtrationGradedMul Q _ _ x z + filtrationGradedMul Q _ _ y z
    rw [LinearMap.map_add]
    rfl
  natCast := fun n => filtrationGradedAlgebraMap₀ Q n
  natCast_zero := by
    rw [Nat.cast_zero]
    exact map_zero (filtrationGradedAlgebraMap₀ Q)
  natCast_succ := fun n => by
    -- The cast field is represented by the degree-zero scalar class chosen above.
    change filtrationGradedAlgebraMap₀ Q ((n + 1 : ℕ) : R) =
      filtrationGradedAlgebraMap₀ Q (n : R) + filtrationGradedOne Q
    rw [Nat.cast_succ, map_add]
    rfl
  intCast := fun z => filtrationGradedAlgebraMap₀ Q z
  intCast_ofNat := fun n => by
    -- Integer casts use the same chosen degree-zero scalar representative.
    change filtrationGradedAlgebraMap₀ Q ((n : ℤ) : R) = filtrationGradedAlgebraMap₀ Q (n : R)
    norm_cast
  intCast_negSucc_ofNat := fun n => by
    -- Integer casts use the same chosen degree-zero scalar representative.
    change filtrationGradedAlgebraMap₀ Q ((Int.negSucc n : ℤ) : R) =
      -filtrationGradedAlgebraMap₀ Q ((n + 1 : ℕ) : R)
    rw [Int.cast_negSucc, map_neg]

/-- Left multiplication by a degree-zero scalar class is scalar multiplication. -/
@[simp] theorem filtrationGradedAlgebraMap₀_mul (Q : QuadraticForm R M) (r : R) (k : ℕ)
    (x : FiltrationGradedPiece Q k) :
    cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k))
      (filtrationGradedMul Q 0 k (filtrationGradedAlgebraMap₀ Q r) x) = r • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      -- Quotient induction supplies representatives, the only stable form to which the
      -- public representative multiplication lemma applies.
      change cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k))
        (filtrationGradedMul Q 0 k (Submodule.Quotient.mk _)
          (Submodule.Quotient.mk x)) = r • Submodule.Quotient.mk x
      rw [filtrationGradedMul_apply_mk, ← Submodule.Quotient.mk_smul]
      -- The cast needs an ambient membership witness; `filtration_mul` supplies that witness.
      rw [filtrationGradedPiece_cast_mk' Q (Nat.zero_add k)]
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_filtrationPreviousRestricted_iff, Submodule.coe_sub,
        filtration_coe_cast Q (Nat.zero_add k), Submodule.coe_smul]
      change algebraMap R (CliffordAlgebra Q) r * (x : CliffordAlgebra Q) - r • x ∈
        filtrationPrevious Q k
      rw [Algebra.smul_def, sub_self]
      exact Submodule.zero_mem (filtrationPrevious Q k)

/-- Degree-zero scalar classes multiply by multiplying their scalars. -/
@[simp 1100] theorem filtrationGradedAlgebraMap₀_mul_algebraMap₀ (Q : QuadraticForm R M) (r s : R) :
    filtrationGradedMul Q 0 0 (filtrationGradedAlgebraMap₀ Q r)
      (filtrationGradedAlgebraMap₀ Q s) = filtrationGradedAlgebraMap₀ Q (r * s) := by
  -- Both scalar classes are quotient representatives, so expose them for the
  -- representative product.
  change filtrationGradedMul Q 0 0 (Submodule.Quotient.mk _)
    (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
  rw [filtrationGradedMul_apply_mk]
  apply (Submodule.Quotient.eq _).mpr
  rw [mem_filtrationPreviousRestricted_iff]
  -- Quotient equality is ambient membership, the form in which `map_mul` applies.
  change algebraMap R (CliffordAlgebra Q) r * algebraMap R (CliffordAlgebra Q) s -
      algebraMap R (CliffordAlgebra Q) (r * s) ∈ filtrationPrevious Q 0
  rw [← map_mul, sub_self]
  exact Submodule.zero_mem (filtrationPrevious Q 0)

/-- Degree-zero scalar classes commute with homogeneous products after reindexing degrees. -/
theorem filtrationGradedAlgebraMap₀_commutes (Q : QuadraticForm R M) (r : R) (k : ℕ)
    (x : FiltrationGradedPiece Q k) :
    cast (congrArg (FiltrationGradedPiece Q)
      ((Nat.zero_add k).trans (Nat.add_zero k).symm))
      (filtrationGradedMul Q 0 k (filtrationGradedAlgebraMap₀ Q r) x) =
      filtrationGradedMul Q k 0 x (filtrationGradedAlgebraMap₀ Q r) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      -- Quotient induction provides a representative. Expose the quotient classes so the
      -- representative-product API applies on both sides of the commutation equation.
      change cast (congrArg (FiltrationGradedPiece Q)
        ((Nat.zero_add k).trans (Nat.add_zero k).symm))
        (filtrationGradedMul Q 0 k (Submodule.Quotient.mk _)
          (Submodule.Quotient.mk x)) =
        filtrationGradedMul Q k 0 (Submodule.Quotient.mk x) (Submodule.Quotient.mk _)
      rw [filtrationGradedMul_apply_mk, filtrationGradedMul_apply_mk]
      rw [filtrationGradedPiece_cast_mk' Q ((Nat.zero_add k).trans (Nat.add_zero k).symm)]
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_filtrationPreviousRestricted_iff, Submodule.coe_sub,
        filtration_coe_cast Q ((Nat.zero_add k).trans (Nat.add_zero k).symm)]
      -- Quotient equality is ambient filtration membership; this exposes the coercions needed
      -- for the Clifford algebra's scalar-commutation theorem.
      change algebraMap R (CliffordAlgebra Q) r * (x : CliffordAlgebra Q) -
          x * algebraMap R (CliffordAlgebra Q) r ∈ filtrationPrevious Q (k + 0)
      rw [Algebra.commutes, sub_self]
      exact Submodule.zero_mem (filtrationPrevious Q (k + 0))

/-- Right multiplication by a degree-zero scalar class is scalar multiplication. -/
@[simp] theorem filtrationGradedMul_algebraMap₀ (Q : QuadraticForm R M) (r : R) (k : ℕ)
    (x : FiltrationGradedPiece Q k) :
    filtrationGradedMul Q k 0 x (filtrationGradedAlgebraMap₀ Q r) = r • x := by
  rw [← filtrationGradedAlgebraMap₀_commutes Q r k x]
  simpa only [cast_cast, cast_eq] using filtrationGradedAlgebraMap₀_mul Q r k x

/-- The graded-ring structure supplies the semiring structure needed by the direct sum. -/
noncomputable instance filtrationGradedGSemiring {Q : QuadraticForm R M} :
    DirectSum.GSemiring (FiltrationGradedPiece Q) := by
  exact @DirectSum.GRing.toGSemiring ℕ (FiltrationGradedPiece Q) _ _
    (filtrationGradedGRing (Q := Q))

/-- Degree-zero scalar classes make the homogeneous pieces into a graded `R`-algebra. -/
noncomputable instance filtrationGradedGAlgebra {Q : QuadraticForm R M} :
    DirectSum.GAlgebra R (FiltrationGradedPiece Q) where
  toFun := filtrationGradedAlgebraMap₀ Q
  map_one := by
    -- `DirectSum.GAlgebra.map_one` is phrased through the degree-zero `GOne` field.
    change filtrationGradedAlgebraMap₀ Q 1 = filtrationGradedOne Q
    exact filtrationGradedAlgebraMap₀_one Q
  map_mul r s := by
    apply Sigma.ext (Nat.zero_add 0).symm
    apply heq_of_cast_eq (congrArg (FiltrationGradedPiece Q) (Nat.zero_add 0).symm)
    -- The scalar product is a degree-zero homogeneous product after this reindexing.
    change cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add 0).symm)
      (filtrationGradedAlgebraMap₀ Q (r * s)) =
      filtrationGradedMul Q 0 0 (filtrationGradedAlgebraMap₀ Q r)
        (filtrationGradedAlgebraMap₀ Q s)
    rw [filtrationGradedAlgebraMap₀_mul_algebraMap₀]
    simp
  commutes r x := by
    rcases x with ⟨k, x⟩
    apply Sigma.ext ((Nat.zero_add k).trans (Nat.add_zero k).symm)
    apply heq_of_cast_eq
      (congrArg (FiltrationGradedPiece Q) ((Nat.zero_add k).trans (Nat.add_zero k).symm))
    exact filtrationGradedAlgebraMap₀_commutes Q r k x
  smul_def r x := by
    rcases x with ⟨k, x⟩
    apply Sigma.ext (Nat.zero_add k).symm
    apply heq_of_cast_eq (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k).symm)
    -- The sigma-level scalar law reduces to the degree-`k` homogeneous scalar equation.
    change cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k).symm) (r • x) =
      filtrationGradedMul Q 0 k (filtrationGradedAlgebraMap₀ Q r) x
    symm
    simpa only [cast_cast, cast_eq] using
      congrArg (cast (congrArg (FiltrationGradedPiece Q) (Nat.zero_add k).symm))
        (filtrationGradedAlgebraMap₀_mul Q r k x)

/-- The direct sum of homogeneous filtration pieces inherits its associated-graded
ring structure. -/
noncomputable instance filtrationAssociatedGradedRing {Q : QuadraticForm R M} :
    Ring (filtrationAssociatedGraded Q) := by
  letI : ∀ k, AddCommGroup (FiltrationGradedPiece Q k) := fun _ => inferInstance
  infer_instance

end CliffordAlgebra
