/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite
public import TauCeti.LowDimTopology.Plumbing.Weight.Basic

/-!
# The one-vertex plumbing

This file carries out the first concrete calculation for the plumbing-lattice lane. The plumbing
with one vertex of framing `w` has intersection form `wxy`; it is negative definite exactly when
`w < 0`. Its characteristic covectors are the integers `w + 2t`, and its characteristic weight at
the lattice point `m` is

`-(w * (m * (m + 1) / 2) + t * m)`.

These formulas reduce the lattice data for a negative one-vertex plumbing to integer arithmetic.
They are the algebraic input for the first lens-space and Seifert-fibered computations in lattice
homology; identifying the plumbed boundary with a lens space is a separate topological step.

## Main definitions

* `TauCeti.singleVertexPlumbing`: the edgeless one-vertex plumbing of framing `w`.
* `TauCeti.singleVertexCharacteristic`: the characteristic covector with coordinate `w + 2t`.
* `TauCeti.singleVertexCharacteristicEquiv`: all characteristic covectors, parametrized by `ℤ`.

## Main results

* `TauCeti.singleVertexPlumbing_isNegativeDefinite_iff`: negative-definiteness is equivalent to
  negativity of the framing.
* `TauCeti.singleVertex_characteristicWeight`: the closed formula for the characteristic weight.
* `TauCeti.singleVertex_canonicalCharacteristicWeight`: the corresponding formula for the
  canonical characteristic covector.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, specifically the
target asking for computations of lattice homology for Seifert-fibered examples. The plumbing
and characteristic-weight conventions follow A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Sections 2--3.
-/

public section

namespace TauCeti

/-- The plumbing graph with one vertex, no edges, and framing `w`. -/
def singleVertexPlumbing (w : ℤ) : PlumbingGraph Unit where
  toSimpleGraph := ⊥
  decidableAdj := inferInstance
  weight := fun _ => w

private theorem singleVertexPlumbing_weight_aux (w : ℤ) (v : Unit) :
    (singleVertexPlumbing w).weight v = w :=
  rfl

/-- The unique vertex of `singleVertexPlumbing w` has framing `w`. -/
@[simp]
theorem singleVertexPlumbing_weight (w : ℤ) (v : Unit) :
    (singleVertexPlumbing w).weight v = w :=
  singleVertexPlumbing_weight_aux w v

/-- The intersection form of the one-vertex plumbing is multiplication by the framing. -/
@[simp]
theorem singleVertexPlumbing_intersectionForm (w : ℤ) (x y : Unit → ℤ) :
    (singleVertexPlumbing w).intersectionForm x y = w * x () * y () := by
  rw [PlumbingGraph.intersectionForm_apply]
  simp only [Fintype.sum_unique, PlumbingGraph.intersectionMatrix_diag,
    singleVertexPlumbing_weight]
  ring

/-- A one-vertex plumbing is negative definite exactly when its framing is negative. -/
@[simp]
theorem singleVertexPlumbing_isNegativeDefinite_iff (w : ℤ) :
    (singleVertexPlumbing w).IsNegativeDefinite ↔ w < 0 := by
  constructor
  · intro h
    simpa using PlumbingGraph.IsNegativeDefinite.weight_neg (singleVertexPlumbing w) h ()
  · intro hw
    rw [PlumbingGraph.isNegativeDefinite_iff_forall_intersectionForm_self_neg]
    intro x hx
    have hx0 : x () ≠ 0 := by
      intro h
      apply hx
      funext v
      simpa using h
    rw [singleVertexPlumbing_intersectionForm]
    nlinarith [sq_pos_of_ne_zero hx0]

/-- A covector on the one-vertex plumbing is characteristic exactly when its sole coordinate is
congruent to the framing modulo two. -/
theorem singleVertexPlumbing_isCharacteristicVector_iff (w : ℤ) (k : Unit → ℤ) :
    (singleVertexPlumbing w).IsCharacteristicVector k ↔ k () ≡ w [ZMOD 2] := by
  rw [PlumbingGraph.isCharacteristicVector_iff]
  constructor
  · exact fun h => h ()
  · intro h v
    simpa using h

/-- The characteristic covector on the one-vertex plumbing with coordinate `w + 2t`.

Every characteristic covector has this form, uniquely; see
`singleVertexCharacteristicEquiv`. -/
def singleVertexCharacteristic (w t : ℤ) :
    (singleVertexPlumbing w).characteristicVectors :=
  ⟨fun _ => w + 2 * t, (singleVertexPlumbing_isCharacteristicVector_iff w _).mpr <|
    Int.modEq_iff_dvd.mpr ⟨-t, by ring⟩⟩

private theorem singleVertexCharacteristic_apply_aux (w t : ℤ) (v : Unit) :
    (singleVertexCharacteristic w t : Unit → ℤ) v = w + 2 * t :=
  rfl

/-- The coordinate of `singleVertexCharacteristic w t` is `w + 2t`. -/
@[simp]
theorem singleVertexCharacteristic_apply (w t : ℤ) (v : Unit) :
    (singleVertexCharacteristic w t : Unit → ℤ) v = w + 2 * t :=
  singleVertexCharacteristic_apply_aux w t v

/-- The integer parameter of a one-vertex characteristic covector is unique. -/
theorem singleVertexCharacteristic_injective (w : ℤ) :
    Function.Injective (singleVertexCharacteristic w) := by
  intro s t h
  have h0 := congrArg (fun k : (singleVertexPlumbing w).characteristicVectors => k.val ()) h
  simp only [singleVertexCharacteristic_apply] at h0
  omega

/-- Every characteristic covector of a one-vertex plumbing is `w + 2t` for some integer `t`. -/
theorem singleVertexCharacteristic_surjective (w : ℤ) :
    Function.Surjective (singleVertexCharacteristic w) := by
  intro k
  have hk : k.val () ≡ w [ZMOD 2] :=
    (singleVertexPlumbing_isCharacteristicVector_iff w k.val).mp k.property
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hk
  refine ⟨-t, Subtype.ext ?_⟩
  funext v
  rw [Subsingleton.elim v ()]
  simp only [singleVertexCharacteristic_apply]
  omega

/-- Characteristic covectors of the one-vertex plumbing are parametrized by `ℤ`: the parameter
`t` corresponds to the covector with coordinate `w + 2t`. -/
noncomputable def singleVertexCharacteristicEquiv (w : ℤ) :
    ℤ ≃ (singleVertexPlumbing w).characteristicVectors :=
  Equiv.ofBijective (singleVertexCharacteristic w)
    ⟨singleVertexCharacteristic_injective w, singleVertexCharacteristic_surjective w⟩

private theorem singleVertexCharacteristicEquiv_apply_aux (w t : ℤ) :
    singleVertexCharacteristicEquiv w t = singleVertexCharacteristic w t :=
  rfl

/-- The characteristic-covector equivalence sends `t` to the coordinate `w + 2t`. -/
@[simp]
theorem singleVertexCharacteristicEquiv_apply (w t : ℤ) :
    singleVertexCharacteristicEquiv w t = singleVertexCharacteristic w t :=
  singleVertexCharacteristicEquiv_apply_aux w t

/-- The canonical characteristic covector is the parameter `-w - 1` in the one-vertex
parametrization. -/
theorem singleVertex_canonicalCharacteristic_eq (w : ℤ) :
    ⟨(singleVertexPlumbing w).canonicalCharacteristic,
        (singleVertexPlumbing w).isCharacteristicVector_canonicalCharacteristic⟩ =
      singleVertexCharacteristic w (-w - 1) := by
  apply Subtype.ext
  funext v
  cases v
  simp
  ring

/-- The characteristic-weight numerator on a one-vertex plumbing is the expected one-variable
quadratic polynomial. -/
theorem singleVertex_characteristicWeightNumerator (w : ℤ) (k x : Unit → ℤ) :
    (singleVertexPlumbing w).characteristicWeightNumerator k x =
      k () * x () + w * x () ^ 2 := by
  rw [PlumbingGraph.characteristicWeightNumerator_def,
    singleVertexPlumbing_intersectionForm]
  simp
  ring

/-- For the characteristic covector `w + 2t`, the weight numerator at the lattice point `m` is
`(w + 2t)m + wm²`. -/
theorem singleVertex_characteristicWeightNumerator_param (w t m : ℤ) :
    (singleVertexPlumbing w).characteristicWeightNumerator
        (singleVertexCharacteristic w t) (fun _ => m) =
      (w + 2 * t) * m + w * m ^ 2 := by
  rw [singleVertex_characteristicWeightNumerator]
  simp

/-- The characteristic weight of the covector `w + 2t` at the lattice point `m`.

The product `m(m+1)` is even, so the displayed quotient is integral. This closed formula is the
one-variable specialization of Némethi's characteristic weight. -/
theorem singleVertex_characteristicWeight (w t m : ℤ) :
    (singleVertexPlumbing w).characteristicWeight
        (singleVertexCharacteristic w t) (fun _ => m) =
      -(w * (m * (m + 1) / 2) + t * m) := by
  have hweight := (singleVertexPlumbing w).two_mul_characteristicWeight
    (singleVertexCharacteristic w t) (fun _ => m)
  rw [singleVertex_characteristicWeightNumerator_param] at hweight
  have heven : Even (m * (m + 1)) := Int.even_mul_succ_self m
  apply (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0))
  rw [hweight]
  calc
    -((w + 2 * t) * m + w * m ^ 2) =
        -(w * (m * (m + 1)) + 2 * (t * m)) := by ring
    _ = -(w * ((m * (m + 1) / 2) * 2) + 2 * (t * m)) := by
      rw [Int.ediv_two_mul_two_of_even heven]
    _ = 2 * -(w * (m * (m + 1) / 2) + t * m) := by ring

/-- The characteristic weight for the canonical covector of a one-vertex plumbing. -/
theorem singleVertex_canonicalCharacteristicWeight (w m : ℤ) :
    (singleVertexPlumbing w).characteristicWeight
        ⟨(singleVertexPlumbing w).canonicalCharacteristic,
          (singleVertexPlumbing w).isCharacteristicVector_canonicalCharacteristic⟩
        (fun _ => m) =
      (w + 1) * m - w * (m * (m + 1) / 2) := by
  rw [singleVertex_canonicalCharacteristic_eq, singleVertex_characteristicWeight]
  ring

/-- The one-vertex plumbing of framing `-p` is negative definite when `p` is positive. -/
theorem singleVertexPlumbing_neg_isNegativeDefinite {p : ℤ} (hp : 0 < p) :
    (singleVertexPlumbing (-p)).IsNegativeDefinite := by
  rw [singleVertexPlumbing_isNegativeDefinite_iff]
  exact neg_neg_of_pos hp

/-- For framing `-p`, the canonical characteristic weight is a quadratic expression with positive
leading term when `p > 0`. -/
theorem singleVertex_neg_canonicalCharacteristicWeight (p m : ℤ) :
    (singleVertexPlumbing (-p)).characteristicWeight
        ⟨(singleVertexPlumbing (-p)).canonicalCharacteristic,
          (singleVertexPlumbing (-p)).isCharacteristicVector_canonicalCharacteristic⟩
        (fun _ => m) =
      (1 - p) * m + p * (m * (m + 1) / 2) := by
  rw [singleVertex_canonicalCharacteristicWeight]
  ring

end TauCeti
