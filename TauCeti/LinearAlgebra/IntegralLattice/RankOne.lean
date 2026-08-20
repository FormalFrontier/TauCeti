/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# Even rank-one integral lattices

For a nonzero integer `m`, this file computes the discriminant form of the rank-one lattice
`⟨2m⟩`.  Its carrier is `ℤ ⊆ ℚ`, its form is `B(x,y) = 2mxy`, and its dual carrier is
`(1/(2m))ℤ`.  Evaluation against the carrier generator identifies the dual carrier with `ℤ` and
the original carrier with `2mℤ`; hence the discriminant group is `ZMod |2m|`.

The class of `1/(2m)` is the chosen generator.  Its self-pairing is `1/(2m)` modulo `ℤ`, and its
half-norm is `1/(4m)` modulo `ℤ`.  These formulas use the half-norm convention fixed by the
integral-lattices roadmap and work without a positivity hypothesis: negative `m` gives a
negative-definite lattice and the signed discriminant-form values change sign accordingly.

## Main declarations

* `TauCeti.IntegralLattice.rankOne`: the lattice `⟨2m⟩`.
* `TauCeti.IntegralLattice.mem_rankOne_dualCarrier_iff`: its dual is `(1/(2m))ℤ`.
* `TauCeti.IntegralLattice.rankOneDiscriminantEquiv`: its discriminant group is `ZMod |2m|`.
* `TauCeti.IntegralLattice.rankOneDiscriminantGenerator`: the class of `1/(2m)`.
* `TauCeti.IntegralLattice.rankOne_pairing_generator`: its bilinear value is `1/(2m)`.
* `TauCeti.IntegralLattice.rankOne_quadratic_generator`: its quadratic value is `1/(4m)`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5, rank-one acceptance calculation.
-/

public section

open Module

namespace TauCeti.IntegralLattice

private def rankOneMatrix (m : ℤ) : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => 2 * m

/-- The rank-one integral lattice `⟨2m⟩`, with carrier `ℤ ⊆ ℚ` and Gram matrix `[2m]`. -/
noncomputable def rankOne (m : ℤ) : IntegralLattice ℚ :=
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) (rankOneMatrix m) (by
    apply Matrix.IsSymm.ext
    intro i j
    rfl)

/-- Membership in the carrier of `⟨2m⟩` is integrality as a rational number. -/
@[simp]
theorem mem_rankOne_carrier_iff (m : ℤ) (x : ℚ) :
    x ∈ (rankOne m).carrier ↔ ∃ z : ℤ, (z : ℚ) = x := by
  classical
  rw [rankOne, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Basis.singleton_repr]

/-- The form of `⟨2m⟩` is `(x,y) ↦ 2mxy`. -/
@[simp]
theorem rankOne_form_apply (m : ℤ) (x y : ℚ) :
    (rankOne m).form x y = 2 * (m : ℚ) * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [rankOne, ofGramMatrix_form, Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply, rankOneMatrix]
  push_cast
  norm_num
  left
  ring

/-- The norm of `x` in `⟨2m⟩` is `2m x²`. -/
@[simp]
theorem rankOne_norm_apply (m : ℤ) (x : ℚ) :
    (rankOne m).norm x = 2 * (m : ℚ) * x ^ 2 := by
  rw [norm_apply, rankOne_form_apply]
  ring

/-- Every lattice `⟨2m⟩` is even, including the degenerate case `m = 0`. -/
theorem isEven_rankOne (m : ℤ) : (rankOne m).IsEven := by
  rw [rankOne, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨m, by simp [rankOneMatrix, two_mul]⟩

/-- The signed determinant of `⟨2m⟩` is `2m`. -/
@[simp]
theorem rankOne_determinant (m : ℤ) : (rankOne m).determinant = 2 * m := by
  rw [rankOne, determinant_ofGramMatrix]
  simp [rankOneMatrix]

/-- The discriminant of `⟨2m⟩` is `|2m|`. -/
@[simp]
theorem rankOne_discriminant (m : ℤ) : (rankOne m).discriminant = (2 * m).natAbs := by
  rw [rankOne, discriminant_ofGramMatrix]
  simp [rankOneMatrix]

/-- The form of `⟨2m⟩` is nondegenerate when `m` is nonzero. -/
noncomputable instance instIsNondegenerateRankOne (m : ℤ) [NeZero m] :
    (rankOne m).IsNondegenerate := by
  apply isNondegenerate_ofGramMatrix
  simpa [rankOneMatrix] using mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) (NeZero.ne m)

/-- The dual of `⟨2m⟩` is `(1/(2m))ℤ`. -/
@[simp]
theorem mem_rankOne_dualCarrier_iff (m : ℤ) [NeZero m] (x : ℚ) :
    x ∈ (rankOne m).dualCarrier ↔ ∃ z : ℤ, (z : ℚ) / (2 * m : ℤ) = x := by
  rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx
    have hone : (1 : ℚ) ∈ (rankOne m).carrier :=
      (mem_rankOne_carrier_iff m 1).2 ⟨1, by norm_num⟩
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (hx 1 hone)
    refine ⟨z, ?_⟩
    rw [rankOne_form_apply, eq_intCast] at hz
    simp only [mul_one] at hz
    rw [hz]
    push_cast
    field_simp [NeZero.ne m]
  · rintro ⟨z, rfl⟩ y hy
    obtain ⟨w, rfl⟩ := (mem_rankOne_carrier_iff m y).1 hy
    refine Submodule.mem_one.mpr ⟨z * w, ?_⟩
    rw [rankOne_form_apply, eq_intCast]
    push_cast
    field_simp [NeZero.ne m]

/-- The canonical carrier generator `1` of `⟨2m⟩`. -/
private def rankOneCarrierOne (m : ℤ) : rankOne m :=
  ⟨1, (mem_rankOne_carrier_iff m 1).2 ⟨1, by norm_num⟩⟩

/-- The integral numerator of a dual vector, characterized over `ℚ` by
`rankOneDualNumerator m x = 2m x`. -/
noncomputable def rankOneDualNumerator (m : ℤ) :
    (rankOne m).dualCarrier →ₗ[ℤ] ℤ :=
  (LinearMap.applyₗ (rankOneCarrierOne m)).comp (rankOne m).dualPairing

private theorem rankOneDualNumerator_cast (m : ℤ) (x : (rankOne m).dualCarrier) :
    ((rankOneDualNumerator m x : ℤ) : ℚ) = 2 * (m : ℚ) * (x : ℚ) := by
  rw [rankOneDualNumerator, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
    (rankOne m).dualPairing_cast, rankOne_form_apply]
  simp [rankOneCarrierOne]

/-- Evaluation against the carrier generator identifies the dual carrier of `⟨2m⟩` with `ℤ`. -/
private noncomputable def rankOneDualCarrierEquivInt (m : ℤ) [NeZero m] :
    (rankOne m).dualCarrier ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective (rankOneDualNumerator m) ⟨by
    intro x y hxy
    apply Subtype.ext
    have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hxy
    rw [rankOneDualNumerator_cast, rankOneDualNumerator_cast] at hcast
    have h2m : (2 * (m : ℚ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne m)
    exact mul_left_cancel₀ h2m hcast, by
    intro z
    let x : (rankOne m).dualCarrier :=
      ⟨(z : ℚ) / (2 * m : ℤ), (mem_rankOne_dualCarrier_iff m _).2 ⟨z, rfl⟩⟩
    refine ⟨x, Int.cast_injective (α := ℚ) ?_⟩
    rw [rankOneDualNumerator_cast]
    dsimp [x]
    push_cast
    field_simp [NeZero.ne m]⟩

private theorem map_carrierInDual_rankOneDualCarrierEquivInt (m : ℤ) [NeZero m] :
    (rankOne m).carrierInDual.map (rankOneDualCarrierEquivInt m).toLinearMap =
      (ℤ ∙ (2 * m) : Submodule ℤ ℤ) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw⟩ := (mem_rankOne_carrier_iff m x).1
      ((rankOne m).mem_carrierInDual_iff x |>.1 hx)
    rw [Submodule.mem_span_singleton]
    refine ⟨w, ?_⟩
    -- `ofBijective` leaves the equivalence coercion opaque; return to its underlying map.
    change w * (2 * m) = rankOneDualNumerator m x
    apply Int.cast_injective (α := ℚ)
    rw [rankOneDualNumerator_cast, ← hw]
    push_cast
    ring
  · rw [Submodule.mem_span_singleton]
    rintro ⟨w, rfl⟩
    let x : (rankOne m).dualCarrier :=
      ⟨(w : ℚ), (mem_rankOne_dualCarrier_iff m _).2 ⟨w * (2 * m), by
        push_cast
        field_simp [NeZero.ne m]
        ⟩⟩
    refine ⟨x, (rankOne m).mem_carrierInDual_iff x |>.2
      ((mem_rankOne_carrier_iff m _).2 ⟨w, rfl⟩), ?_⟩
    -- `ofBijective` leaves the equivalence coercion opaque; return to its underlying map.
    change rankOneDualNumerator m x = w * (2 * m)
    apply Int.cast_injective (α := ℚ)
    rw [rankOneDualNumerator_cast]
    dsimp [x]
    push_cast
    ring

private theorem rankOne_span_toAddSubgroup (m : ℤ) :
    (ℤ ∙ (2 * m) : Submodule ℤ ℤ).toAddSubgroup = AddSubgroup.zmultiples (2 * m) := by
  ext z
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, Int.mem_zmultiples_iff]
  constructor <;> rintro ⟨a, rfl⟩
  · exact ⟨a, by ring⟩
  · exact ⟨a, by ring⟩

/-- The discriminant group of `⟨2m⟩` is the cyclic group `ZMod |2m|`.

The equivalence sends a dual vector to its numerator modulo `2m`; in particular the class of
`1/(2m)` maps to `1`. -/
noncomputable def rankOneDiscriminantEquiv (m : ℤ) [NeZero m] :
    (rankOne m).DiscriminantGroup ≃+ ZMod (2 * m).natAbs :=
  (Submodule.Quotient.equiv (rankOne m).carrierInDual (ℤ ∙ (2 * m))
      (rankOneDualCarrierEquivInt m)
      (map_carrierInDual_rankOneDualCarrierEquivInt m)).toAddEquiv.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (rankOne_span_toAddSubgroup m)).trans
      (Int.quotientZMultiplesEquivZMod (2 * m)))

/-- On representatives, the cyclic discriminant-group equivalence reads the integral numerator
modulo `2m`. -/
@[simp]
theorem rankOneDiscriminantEquiv_mk (m : ℤ) [NeZero m]
    (x : (rankOne m).dualCarrier) :
    rankOneDiscriminantEquiv m (Submodule.Quotient.mk x) =
      (rankOneDualNumerator m x : ZMod (2 * m).natAbs) :=
  (rfl)

/-- The distinguished generator of the discriminant group of `⟨2m⟩`, represented by `1/(2m)`. -/
noncomputable def rankOneDiscriminantGenerator (m : ℤ) [NeZero m] :
    (rankOne m).DiscriminantGroup :=
  Submodule.Quotient.mk
    ⟨1 / (2 * m : ℤ), (mem_rankOne_dualCarrier_iff m _).2 ⟨1, by norm_num⟩⟩

/-- The distinguished discriminant class maps to `1 ∈ ZMod |2m|`. -/
@[simp]
theorem rankOneDiscriminantEquiv_generator (m : ℤ) [NeZero m] :
    rankOneDiscriminantEquiv m (rankOneDiscriminantGenerator m) = 1 := by
  rw [rankOneDiscriminantGenerator, rankOneDiscriminantEquiv_mk]
  have hnum : rankOneDualNumerator m
      ⟨1 / (2 * m : ℤ), (mem_rankOne_dualCarrier_iff m _).2 ⟨1, by norm_num⟩⟩ = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [rankOneDualNumerator_cast]
    push_cast
    field_simp [NeZero.ne m]
  rw [hnum]
  norm_num

/-- The self-pairing of the distinguished generator is `1/(2m)` modulo `ℤ`. -/
@[simp]
theorem rankOne_pairing_generator (m : ℤ) [NeZero m] :
    (rankOne m).discriminantPairing (rankOneDiscriminantGenerator m)
        (rankOneDiscriminantGenerator m) =
      ((1 / (2 * m : ℤ) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [rankOneDiscriminantGenerator, discriminantPairing_mk, rankOne_form_apply]
  congr 1
  push_cast
  field_simp [NeZero.ne m]

/-- The half-norm of the distinguished generator is `1/(4m)` modulo `ℤ`. -/
@[simp]
theorem rankOne_quadratic_generator (m : ℤ) [NeZero m] :
    (rankOne m).discriminantQuadraticMap (isEven_rankOne m)
        (rankOneDiscriminantGenerator m) =
      ((1 / (4 * m : ℤ) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [rankOneDiscriminantGenerator, discriminantQuadraticMap_mk, rankOne_form_apply]
  congr 1
  push_cast
  field_simp [NeZero.ne m]
  norm_num

/-- The discriminant group of `⟨2m⟩` has order `|2m|`. -/
theorem natCard_rankOne_discriminantGroup (m : ℤ) [NeZero m] :
    Nat.card (rankOne m).DiscriminantGroup = (2 * m).natAbs := by
  rw [(rankOne m).natCard_discriminantGroup, rankOne_discriminant]

/-- For `m > 0`, the lattice `⟨2m⟩` is positive-definite. -/
theorem isPosDef_rankOne (m : ℤ) (hm : 0 < m) : (rankOne m).IsPosDef := by
  rw [(rankOne m).isPosDef_iff]
  intro x hx
  rw [rankOne_form_apply]
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hx' : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  nlinarith

/-- The lattice `⟨2m⟩` is positive-definite exactly when `m` is positive. -/
theorem isPosDef_rankOne_iff (m : ℤ) : (rankOne m).IsPosDef ↔ 0 < m := by
  refine ⟨fun h ↦ ?_, isPosDef_rankOne m⟩
  have h1 := (rankOne m).isPosDef_iff.mp h 1 one_ne_zero
  rw [rankOne_form_apply] at h1
  norm_num at h1
  exact_mod_cast h1

/-- For `m < 0`, the lattice `⟨2m⟩` is negative-definite. -/
theorem isNegDef_rankOne (m : ℤ) (hm : m < 0) : (rankOne m).IsNegDef := by
  rw [(rankOne m).isNegDef_iff]
  intro x hx
  rw [rankOne_form_apply]
  have hm' : (m : ℚ) < 0 := by exact_mod_cast hm
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  nlinarith [sq_nonneg x]

/-- The lattice `⟨2m⟩` is negative-definite exactly when `m` is negative. -/
theorem isNegDef_rankOne_iff (m : ℤ) : (rankOne m).IsNegDef ↔ m < 0 := by
  refine ⟨fun h ↦ ?_, isNegDef_rankOne m⟩
  have h1 := (rankOne m).isNegDef_iff.mp h 1 one_ne_zero
  rw [rankOne_form_apply] at h1
  norm_num at h1
  have h2m : 2 * m < 0 := by exact_mod_cast h1
  omega

/-- The signature of `⟨2m⟩` is `(1,0,0)` when `m > 0`. -/
@[simp]
theorem rankOne_signature_of_pos (m : ℤ) (hm : 0 < m) :
    (rankOne m).signature = (1, 0, 0) := by
  have hzero := (rankOne m).isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero.mp
    (isPosDef_rankOne m hm)
  have hsum := (rankOne m).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  have hpos : (rankOne m).sigPos = 1 := by omega
  simp [signature, hpos, hzero.1, hzero.2]

/-- The signature of `⟨2m⟩` is `(0,0,1)` when `m < 0`. -/
@[simp]
theorem rankOne_signature_of_neg (m : ℤ) (hm : m < 0) :
    (rankOne m).signature = (0, 0, 1) := by
  have hzero := (rankOne m).isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero.mp
    (isNegDef_rankOne m hm)
  have hsum := (rankOne m).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  have hneg : (rankOne m).sigNeg = 1 := by omega
  simp [signature, hzero.1, hzero.2, hneg]

/-- The degenerate lattice `⟨0⟩` has signature `(0,1,0)`. -/
@[simp]
theorem rankOne_signature_zero : (rankOne 0).signature = (0, 1, 0) := by
  have hpos : (rankOne 0).sigPos = 0 :=
    (rankOne 0).isNegSemidef_iff_sigPos_eq_zero.mp <|
      (rankOne 0).isNegSemidef_iff.mpr fun x ↦ by simp
  have hneg : (rankOne 0).sigNeg = 0 :=
    (rankOne 0).isPosSemidef_iff_sigNeg_eq_zero.mp <|
      (rankOne 0).isPosSemidef_iff.mpr fun x ↦ by simp
  have hsum := (rankOne 0).signature_sum_eq_finrank
  simp only [Module.finrank_self, hpos, hneg, zero_add, add_zero] at hsum
  simp [signature, hpos, hsum, hneg]

end TauCeti.IntegralLattice
