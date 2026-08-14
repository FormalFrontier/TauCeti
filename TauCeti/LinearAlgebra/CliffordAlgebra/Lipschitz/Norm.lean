/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The norm of the Lipschitz group

The Clifford norm `star x * x` of a Lipschitz element is a unit scalar. This defines a
homomorphism from the Lipschitz group to the units of the base ring. Generating vectors have norm
the negative of their quadratic norm.

Together with the orthogonal action, this homomorphism is the input for the general-field spinor
norm: the Clifford norm descends modulo squares through the kernel of that action.

## Main results

* `TauCeti.CliffordAlgebra.lipschitzNorm`: the unit-valued Clifford norm.
* `TauCeti.CliffordAlgebra.lipschitzNorm_unitι`: its value on a generating vector.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.CliffordAlgebra

universe u v

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
  [Invertible (2 : R)]

private theorem exists_lipschitzNormUnit (Q : QuadraticForm R V)
    (x : (CliffordAlgebra Q)ˣ) (hx : x ∈ lipschitzGroup Q) :
    ∃ r : Rˣ,
      star (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) =
        algebraMap R (CliffordAlgebra Q) (r : R) ∧
      (x : CliffordAlgebra Q) * star (x : CliffordAlgebra Q) =
        algebraMap R (CliffordAlgebra Q) (r : R) := by
  induction hx using Subgroup.closure_induction with
  | mem x hgen =>
      obtain ⟨v, hv⟩ := hgen
      let _ := x.invertible
      let _ : Invertible (ι Q v) := by rw [hv]; infer_instance
      let _ : Invertible (Q v) := invertibleOfInvertibleι Q v
      refine ⟨-(unitOfInvertible (Q v)), ?_, ?_⟩
      · rw [← hv, star_ι, neg_mul, ι_sq_scalar]
        -- Expose the scalar value of the canonical negative unit.
        change -(algebraMap R (CliffordAlgebra Q)) (Q v) =
          (algebraMap R (CliffordAlgebra Q)) (-Q v)
        exact (map_neg _ _).symm
      · rw [← hv, star_ι, mul_neg, ι_sq_scalar]
        -- Expose the scalar value of the canonical negative unit.
        change -(algebraMap R (CliffordAlgebra Q)) (Q v) =
          (algebraMap R (CliffordAlgebra Q)) (-Q v)
        exact (map_neg _ _).symm
  | inv x hx ih =>
      obtain ⟨r, hr, hr'⟩ := ih
      refine ⟨r⁻¹, ?_, ?_⟩
      · have hunit : x * star x = Units.map (algebraMap R (CliffordAlgebra Q)) r := by
          apply Units.ext
          simpa using hr'
        have hinv := congrArg Inv.inv hunit
        have hval := congrArg Units.val hinv
        simpa [star_inv, map_inv] using hval
      · have hunit : star x * x = Units.map (algebraMap R (CliffordAlgebra Q)) r := by
          apply Units.ext
          simpa using hr
        have hinv := congrArg Inv.inv hunit
        have hval := congrArg Units.val hinv
        simpa [star_inv, map_inv] using hval
  | one =>
      exact ⟨1, by simp, by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨r, hr, hr'⟩ := ihx
      obtain ⟨s, hs, hs'⟩ := ihy
      refine ⟨r * s, ?_, ?_⟩
      · simp only [Units.val_mul, star_mul]
        rw [mul_assoc (star (y : CliffordAlgebra Q))]
        rw [← mul_assoc (star (x : CliffordAlgebra Q))]
        rw [hr, Algebra.commutes]
        rw [← mul_assoc, hs, ← map_mul, mul_comm]
      · simp only [Units.val_mul, star_mul]
        rw [mul_assoc (x : CliffordAlgebra Q)]
        rw [← mul_assoc (y : CliffordAlgebra Q)]
        rw [hs', Algebra.commutes]
        rw [← mul_assoc, hr', ← map_mul]

private noncomputable def lipschitzNormUnit (Q : QuadraticForm R V)
    (x : lipschitzGroup Q) : Rˣ :=
  Classical.choose (exists_lipschitzNormUnit Q x x.2)

private theorem star_mul_self_eq_lipschitzNormUnit (Q : QuadraticForm R V)
    (x : lipschitzGroup Q) :
    star ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (lipschitzNormUnit Q x : R) :=
  (Classical.choose_spec (exists_lipschitzNormUnit Q x x.2)).1

/-- The unit-valued Clifford norm on the Lipschitz group. -/
noncomputable def lipschitzNorm (Q : QuadraticForm R V) : lipschitzGroup Q →* Rˣ where
  toFun := lipschitzNormUnit Q
  map_one' := by
    apply Units.ext
    apply algebraMap_injective Q
    -- Compare the chosen unit through the faithful Clifford scalar map.
    change algebraMap R (CliffordAlgebra Q) (lipschitzNormUnit Q 1 : R) =
      algebraMap R (CliffordAlgebra Q) 1
    simpa using (star_mul_self_eq_lipschitzNormUnit Q 1).symm
  map_mul' x y := by
    apply Units.ext
    apply algebraMap_injective Q
    have hxy := star_mul_self_eq_lipschitzNormUnit Q (x * y)
    have hx := star_mul_self_eq_lipschitzNormUnit Q x
    have hy := star_mul_self_eq_lipschitzNormUnit Q y
    simp only [Units.val_mul]
    rw [map_mul]
    -- Compare the chosen units through the faithful Clifford scalar map.
    change algebraMap R (CliffordAlgebra Q) (lipschitzNormUnit Q (x * y) : R) =
      algebraMap R (CliffordAlgebra Q) (lipschitzNormUnit Q x : R) *
        algebraMap R (CliffordAlgebra Q) (lipschitzNormUnit Q y : R)
    rw [← hx, ← hy, ← hxy]
    simp only [Subgroup.coe_mul, Units.val_mul, star_mul]
    rw [mul_assoc (star ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)),
      ← mul_assoc (star ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)),
      hx, Algebra.commutes, ← mul_assoc, Algebra.commutes]

/-- The product of the Clifford conjugate of a Lipschitz element with itself is its scalar norm. -/
@[simp]
theorem star_mul_self_eq_algebraMap_lipschitzNorm
    (Q : QuadraticForm R V) (x : lipschitzGroup Q) :
    star ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (lipschitzNorm Q x : R) :=
  star_mul_self_eq_lipschitzNormUnit Q x

/-- A generating vector has Clifford norm equal to the negative of its quadratic norm. -/
@[simp]
theorem lipschitzNorm_unitι (Q : QuadraticForm R V) (v : V) [Invertible (Q v)] :
    lipschitzNorm Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ =
      -(unitOfInvertible (Q v)) := by
  apply Units.ext
  apply algebraMap_injective Q
  have h := star_mul_self_eq_algebraMap_lipschitzNorm Q
    ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩
  simp only [coe_unitι] at h
  rw [star_ι, neg_mul, ι_sq_scalar] at h
  -- Read the unit equality through its scalar value.
  change algebraMap R (CliffordAlgebra Q) (lipschitzNorm Q
      ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ : R) =
    algebraMap R (CliffordAlgebra Q) (-Q v)
  exact h.symm.trans (map_neg _ _).symm

/-- The Clifford norm of a Pin element is one. -/
@[simp]
theorem lipschitzNorm_pinToLipschitz (Q : QuadraticForm R V) (p : pinGroup Q) :
    lipschitzNorm Q (pinToLipschitz Q p) = 1 := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm]
  simpa only [coe_pinToLipschitz_apply, Units.val_one, map_one] using
    pinGroup.coe_star_mul_self p

end TauCeti.CliffordAlgebra
