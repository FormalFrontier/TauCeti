/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The kernel of the Spin action

For a positive-dimensional finite nondegenerate quadratic space over a field where `2` is
invertible, the kernel of the Spin action consists of the two scalar elements. The proof first
shows that an even Clifford element commuting with every generating vector is scalar, using
contraction and the exterior-algebra basis. Unitarity then restricts the scalar to `1` or `-1`.

## Main results

* `CliffordAlgebra.mem_ker_spinToSpecialOrthogonal_iff`: a Spin element is in the kernel
exactly when it is `1` or the canonical scalar `-1`.
* `CliffordAlgebra.card_ker_spinToSpecialOrthogonal`: the kernel of the Spin action on
the special orthogonal group has cardinality two.
* `CliffordAlgebra.zmodTwoMulEquivKerSpinToSpecialOrthogonal`: the kernel is canonically
  equivalent to `Multiplicative (ZMod 2)`.
* `CliffordAlgebra.zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one`: the chosen
  generator maps to the scalar `-1`.
* `CliffordAlgebra.zmodTwoMulEquivKerSpinToSpecialOrthogonal_symm_apply_negOne`: the inverse
  sends the scalar `-1` to the chosen generator.

## References

This completes Layer 2's kernel target, `card_ker_spinToSpecialOrthogonal`, in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace CliffordAlgebra

open TauCeti

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

section Scalar

variable {K : Type u} [Field K] [Module K M]

/-! ### The scalar `-1` in the Spin group -/

/-- The scalar `-1` belongs to the Spin group when the quadratic form is a unit
on some vector. -/
theorem neg_one_mem_spinGroup_of_isUnit (Q : QuadraticForm R M) (v : M)
    (hvQ : IsUnit (Q v)) :
    (-1 : CliffordAlgebra Q) ∈ spinGroup Q := by
  let _ : Invertible (Q v) := hvQ.invertible
  let a : R := -⅟(Q v)
  have ha : IsUnit a := (isUnit_of_invertible (⅟(Q v))).neg
  let _ : Invertible a := ha.invertible
  have havQ : IsUnit (Q (a • v)) := by
    rw [QuadraticMap.map_smul]
    simpa [smul_eq_mul, mul_assoc] using ha.mul (ha.mul hvQ)
  let _ : Invertible (Q (a • v)) := havQ.invertible
  let x := unitι Q (a • v) * unitι Q v
  have hx : (x : CliffordAlgebra Q) = -1 := by
    simp only [x, Units.val_mul, coe_unitι, map_smul, Algebra.smul_def]
    rw [mul_assoc, ι_sq_scalar, ← map_mul]
    simp [a]
  rw [spinGroup.mem_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨⟨x, mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _), hx⟩,
      ?_⟩
    simp [Unitary.mem_iff]
  · exact (CliffordAlgebra.even Q).neg_mem (CliffordAlgebra.even Q).one_mem

/-- The scalar `-1` belongs to the Spin group of a nonzero quadratic form over a field. -/
theorem neg_one_mem_spinGroup (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    (-1 : CliffordAlgebra Q) ∈ spinGroup Q := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact neg_one_mem_spinGroup_of_isUnit Q v
    (isUnit_iff_ne_zero.mpr (by simpa using hv))

namespace spinGroup

/-- The canonical scalar `-1` in the Spin group of a nonzero quadratic form over a field. -/
def negOne (Q : QuadraticForm K M) (hQ : Q ≠ 0) : spinGroup Q :=
  ⟨-1, neg_one_mem_spinGroup Q hQ⟩

/-- The underlying Clifford element of `spinGroup.negOne` is the scalar `-1`. -/
@[simp]
theorem coe_negOne (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    (negOne Q hQ : CliffordAlgebra Q) = -1 :=
  (rfl)

/-- The canonical scalar `-1` squares to the identity. -/
@[simp]
theorem negOne_mul_self (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    negOne Q hQ * negOne Q hQ = 1 := by
  apply Subtype.ext
  simp

/-- The canonical scalar `-1` in the Spin group is not the identity when `2` is invertible. -/
theorem negOne_ne_one (Q : QuadraticForm K M) [Invertible (2 : K)] (hQ : Q ≠ 0) :
    negOne Q hQ ≠ 1 := by
  intro h
  have hK : (-1 : K) = 1 := by
    apply algebraMap_injective Q
    simpa using congrArg (fun x : spinGroup Q ↦ (x : CliffordAlgebra Q)) h
  apply Invertible.ne_zero (2 : K)
  calc
    (2 : K) = 1 - (-1) := by ring
    _ = 1 - 1 := by rw [hK]
    _ = 0 := sub_self 1

end spinGroup

variable [FiniteDimensional K M] (Q : QuadraticForm K M) [Invertible (2 : K)]

omit [FiniteDimensional K M] in
private theorem commute_ι_of_mem_ker_spinToOrthogonal
    (x : spinGroup Q) (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) (v : M) :
    Commute (x : CliffordAlgebra Q) (ι Q v) := by
  rw [MonoidHom.mem_ker] at hx
  have hfix : spinVectorAction Q x v = v := by
    have h := congrArg
      (fun g : QuadraticMap.orthogonalGroup Q => ((g : M ≃ₗ[K] M) v)) hx
    rw [coe_spinToOrthogonal_apply] at h
    simpa using h
  have hconj :
      (x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q) = ι Q v := by
    rw [← ι_spinVectorAction_apply Q x v, hfix]
  rw [commute_iff_eq]
  calc
    (x : CliffordAlgebra Q) * ι Q v =
        ((x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q)) * x := by
          rw [mul_assoc, spinGroup.star_mul_self_of_mem x.2, mul_one]
    _ = ι Q v * x := by rw [hconj]

private theorem exists_coe_eq_algebraMap_of_mem_ker_spinToOrthogonal
    (hQ : Q.Nondegenerate) (x : spinGroup Q)
    (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) :
    ∃ r : K, (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r := by
  exact exists_eq_algebraMap_of_mem_even_of_commute Q hQ x (spinGroup.mem_even x.2)
    (commute_ι_of_mem_ker_spinToOrthogonal Q x hx)

private theorem coe_eq_one_or_eq_neg_one_of_mem_ker_spinToOrthogonal
    (hQ : Q.Nondegenerate) (x : spinGroup Q)
    (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) :
    (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  obtain ⟨r, hr⟩ := exists_coe_eq_algebraMap_of_mem_ker_spinToOrthogonal Q hQ x hx
  have hr_sq : r * r = 1 := by
    apply algebraMap_injective Q
    simpa only [hr, star_algebraMap, map_mul, map_one] using
      spinGroup.star_mul_self_of_mem x.2
  rcases (mul_self_eq_one_iff.mp hr_sq) with rfl | rfl
  · left
    simpa using hr
  · right
    simpa using hr

end Scalar

section NegOne

variable [Invertible (2 : R)]

/-- A Spin element whose Clifford value is `-1` lies in the kernel of the Spin action. -/
theorem mem_ker_spinToSpecialOrthogonal_of_coe_eq_neg_one
    (x : spinGroup Q) (h : (x : CliffordAlgebra Q) = -1) :
    x ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [coe_spinToSpecialOrthogonal_apply]
  apply ι_injective Q
  rw [ι_spinVectorAction_apply]
  simp [h]

namespace spinGroup

variable {K : Type u} [Field K] [Module K M]
  [Invertible (2 : K)]

/-- The scalar `-1` lies in the kernel of the Spin action. -/
theorem negOne_mem_ker_spinToSpecialOrthogonal
    (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    negOne Q hQ ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) :=
  mem_ker_spinToSpecialOrthogonal_of_coe_eq_neg_one Q _ (coe_negOne Q hQ)

/-- The scalar `-1` acts trivially on the quadratic space. -/
@[simp]
theorem spinToSpecialOrthogonal_negOne
    (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    spinToSpecialOrthogonal Q (negOne Q hQ) = 1 :=
  MonoidHom.mem_ker.mp (negOne_mem_ker_spinToSpecialOrthogonal Q hQ)

/-- The scalar `-1` acts trivially under the primary orthogonal Spin action. -/
@[simp]
theorem spinToOrthogonal_negOne
    (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    spinToOrthogonal Q (negOne Q hQ) = 1 := by
  rw [← MonoidHom.mem_ker, ← ker_spinToSpecialOrthogonal]
  exact negOne_mem_ker_spinToSpecialOrthogonal Q hQ

end spinGroup

end NegOne

end CliffordAlgebra

namespace CliffordAlgebra

section Kernel

variable {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- A Spin element lies in the kernel of the special-orthogonal action exactly when it is
the scalar `1` or the canonical scalar `-1`. -/
theorem mem_ker_spinToSpecialOrthogonal_iff
    (Q : QuadraticForm K M) [Invertible (2 : K)] [Nontrivial M]
    (hQ : Q.Nondegenerate)
    (x : spinGroup Q) :
    x ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) ↔
      x = 1 ∨ x = spinGroup.negOne Q hQ.ne_zero := by
  constructor
  · intro hx
    rcases coe_eq_one_or_eq_neg_one_of_mem_ker_spinToOrthogonal Q hQ x
      (ker_spinToSpecialOrthogonal Q ▸ hx) with h | h
    · left
      apply Subtype.ext
      exact h
    · right
      apply Subtype.ext
      simpa using h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ.ne_zero

/-- A Spin element lies in the kernel of the orthogonal action exactly when it is
the scalar `1` or the canonical scalar `-1`. -/
theorem mem_ker_spinToOrthogonal_iff
    (Q : QuadraticForm K M) [Invertible (2 : K)] [Nontrivial M]
    (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    x ∈ MonoidHom.ker (spinToOrthogonal Q) ↔
      x = 1 ∨ x = spinGroup.negOne Q hQ.ne_zero := by
  rw [← ker_spinToSpecialOrthogonal]
  exact mem_ker_spinToSpecialOrthogonal_iff Q hQ x

/-- The kernel of the Spin action on a positive-dimensional finite nondegenerate quadratic space
over a field where `2` is invertible has cardinality two. -/
theorem card_ker_spinToSpecialOrthogonal (hM : 0 < Module.finrank K M)
    (Q : QuadraticForm K M) [Invertible (2 : K)] (hQ : Q.Nondegenerate) :
    Nat.card (MonoidHom.ker (spinToSpecialOrthogonal Q)) = 2 := by
  let _ : Nontrivial M := Module.nontrivial_of_finrank_pos hM
  rw [Nat.card_eq_two_iff' (1 : MonoidHom.ker (spinToSpecialOrthogonal Q))]
  have hQ0 := hQ.ne_zero
  let z : MonoidHom.ker (spinToSpecialOrthogonal Q) :=
    ⟨spinGroup.negOne Q hQ0, spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ0⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    exact spinGroup.negOne_ne_one Q hQ0 (congrArg Subtype.val hz)
  · intro y hy
    apply Subtype.ext
    rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ y).mp y.2 with h | h
    · exfalso
      apply hy
      apply Subtype.ext
      exact h
    · simpa [z] using h

/-- The kernel of the Spin action on a positive-dimensional nondegenerate quadratic space over a
field in which `2` is invertible is canonically the cyclic group of order two, with its generator
sent to the scalar `-1`. -/
noncomputable def zmodTwoMulEquivKerSpinToSpecialOrthogonal [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    Multiplicative (ZMod 2) ≃* MonoidHom.ker (spinToSpecialOrthogonal Q) :=
  let z : MonoidHom.ker (spinToSpecialOrthogonal Q) :=
    ⟨spinGroup.negOne Q hQ.ne_zero,
      spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ.ne_zero⟩
  zmodMulEquivOfGenerator (g := z)
    (fun _ ↦ mem_zpowers_of_prime_card (p := 2)
      (card_ker_spinToSpecialOrthogonal Module.finrank_pos Q hQ)
      (fun h ↦ spinGroup.negOne_ne_one Q hQ.ne_zero (congrArg Subtype.val h)))
    (card_ker_spinToSpecialOrthogonal Module.finrank_pos Q hQ)

/-- The chosen generator of `Multiplicative (ZMod 2)` maps to the scalar `-1` in the Spin
kernel. -/
@[simp]
theorem zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ (Multiplicative.ofAdd 1) =
      ⟨spinGroup.negOne Q hQ.ne_zero,
        spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ.ne_zero⟩ := by
  simp only [zmodTwoMulEquivKerSpinToSpecialOrthogonal,
    zmodMulEquivOfGenerator_apply_ofAdd_one]

/-- The inverse kernel equivalence sends the scalar `-1` to the chosen generator of
`Multiplicative (ZMod 2)`. -/
@[simp]
theorem zmodTwoMulEquivKerSpinToSpecialOrthogonal_symm_apply_negOne [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    (zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ).symm
        ⟨spinGroup.negOne Q hQ.ne_zero,
          spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ.ne_zero⟩ =
      Multiplicative.ofAdd 1 := by
  simp only [zmodTwoMulEquivKerSpinToSpecialOrthogonal,
    zmodMulEquivOfGenerator_symm_apply_generator]

end Kernel

end CliffordAlgebra
