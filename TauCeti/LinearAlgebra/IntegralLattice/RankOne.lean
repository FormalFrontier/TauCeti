/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Examples

public section

/-!
# The rank-one lattice `⟨2m⟩` and its discriminant form

For a nonzero integer `m`, let `⟨2m⟩` be the lattice `ℤe` inside `ℚ` carrying the form
`B(e, e) = 2m`.  This file constructs it as `TauCeti.IntegralLattice.rankOne` and computes every
invariant the integral-lattices roadmap asks a rank-one example to produce: the dual lattice, the
discriminant group with its generator, the two discriminant forms on that generator, and the
signature.

The whole family is treated at once, for every `m`, rather than one sign at a time: the
positive-definite and negative-definite cases differ only in the sign of `m`, and the degenerate
`m = 0` form is the same construction, but the subsequent finite discriminant-group
calculations exclude it.  The two rank-one lattices already present as Layer 1 acceptance examples
are the two smallest members,
`rankOne 1 = a1` and `rankOne (-1) = negativeA1`, and those identifications are recorded below
rather than a third and fourth copy of the construction being made.

## The calculation

Writing `e` for the chosen basis vector of `ℚ` and `g` for the class of `e / (2m)`, the results
are

```text
Lᵛ = (1 / (2m)) ℤe,   A_L ≅ ℤ / 2mℤ,   b_L(g, g) = 1 / (2m),   q_L(g) = 1 / (4m),
```

with `g` generating `A_L` and `#A_L = |2m|`.  The quadratic value is in the half-norm convention
fixed by `TauCeti.IntegralLattice.discriminantQuadraticMap`, so it is half of Nikulin's
`ℚ/2ℤ`-valued `1 / (2m)`.  Both forms are computed on an arbitrary multiple `k • g`, which is what
identifies the finite quadratic module rather than merely its order.  The two displayed forms are
compatible: the polar of `q_L` on those elements is the displayed pairing,
`q_L((k + l) • g) - q_L(k • g) - q_L(l • g) = b_L(k • g, l • g) = kl / (2m)`.

Nonvanishing of `m` is carried as a `NeZero` instance, so that the nondegeneracy of `⟨2m⟩` — which
the discriminant group needs in order to be finite — is available to instance synthesis.

## Main definitions

* `TauCeti.IntegralLattice.rankOne`: the lattice `⟨2m⟩`.
* `TauCeti.IntegralLattice.rankOneDualGen`: the dual vector `e / (2m)`.
* `TauCeti.IntegralLattice.rankOneClass`: its class `g` in the discriminant group.
* `TauCeti.IntegralLattice.rankOneDualEquiv`: the dual lattice is free of rank one on
  `rankOneDualGen`.
* `TauCeti.IntegralLattice.rankOneDiscriminantEquiv`: the isomorphism `A_L ≅ ℤ / 2mℤ` sending `g`
  to `1`.

## Main results

* `TauCeti.IntegralLattice.mem_rankOne_dualCarrier_iff` and
  `TauCeti.IntegralLattice.rankOne_dualCarrier_eq_span`: the dual lattice is `(1 / (2m)) ℤe`.
* `TauCeti.IntegralLattice.span_rankOneClass_eq_top`: `g` generates the discriminant group.
* `TauCeti.IntegralLattice.natCard_rankOne_discriminantGroup`: the discriminant group has `|2m|`
  elements.
* `TauCeti.IntegralLattice.discriminantPairing_zsmul_rankOneClass` and
  `TauCeti.IntegralLattice.discriminantQuadraticMap_zsmul_rankOneClass`: the two displayed forms,
  on every element.
* `TauCeti.IntegralLattice.polar_discriminantQuadraticMap_zsmul_rankOneClass`: the polar of the
  displayed quadratic form is the displayed pairing.
* `TauCeti.IntegralLattice.rankOne_signature_of_pos`,
  `TauCeti.IntegralLattice.rankOne_signature_of_neg` and
  `TauCeti.IntegralLattice.rankOne_zero_signature`: the signature is `(1, 0, 0)` for `0 < m`,
  `(0, 0, 1)` for `m < 0`, and `(0, 1, 0)` for `m = 0`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5, the rank-one acceptance test.
-/

namespace TauCeti

namespace IntegralLattice

open Module

/-! ## The lattice `⟨2m⟩` -/

private def rankOneMatrix (m : ℤ) : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ ↦ 2 * m

private theorem isSymm_rankOneMatrix (m : ℤ) : (rankOneMatrix m).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rfl

/-- The rank-one integral lattice `⟨2m⟩`: the lattice `ℤe` in `ℚ` whose form has `B(e, e) = 2m`.

The parameter is unrestricted, so `rankOne 0` is the degenerate rank-one lattice.  Every statement
that needs a discriminant group assumes `NeZero m` instead. -/
noncomputable def rankOne (m : ℤ) : IntegralLattice ℚ :=
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) (rankOneMatrix m) (isSymm_rankOneMatrix m)

/-- A rational number belongs to the carrier of `⟨2m⟩` exactly when it is an integer. -/
@[simp]
theorem mem_rankOne_carrier_iff (m : ℤ) (x : ℚ) :
    x ∈ (rankOne m).carrier ↔ ∃ z : ℤ, (z : ℚ) = x := by
  classical
  rw [rankOne, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Basis.singleton_repr]

/-- The form of `⟨2m⟩` is `2m` times the product of its two arguments. -/
@[simp]
theorem rankOne_form_apply (m : ℤ) (x y : ℚ) : (rankOne m).form x y = 2 * m * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [rankOne, ofGramMatrix_form, Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply, rankOneMatrix, eq_intCast]
  push_cast
  ring

/-- The norm of `⟨2m⟩` is `2m` times a square. -/
@[simp]
theorem rankOne_norm_apply (m : ℤ) (x : ℚ) : (rankOne m).norm x = 2 * m * x ^ 2 := by
  rw [norm_apply, rankOne_form_apply]
  ring

/-- `⟨2m⟩` is an even lattice. -/
theorem isEven_rankOne (m : ℤ) : (rankOne m).IsEven := by
  rw [rankOne, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨m, by simp [rankOneMatrix, two_mul]⟩

/-- The signed determinant of `⟨2m⟩` is `2m`. -/
@[simp]
theorem rankOne_determinant (m : ℤ) : (rankOne m).determinant = 2 * m := by
  rw [rankOne, determinant_ofGramMatrix]
  simp [rankOneMatrix]

/-- `⟨2m⟩` is nondegenerate for nonzero `m`. -/
instance instIsNondegenerateRankOne (m : ℤ) [NeZero m] : (rankOne m).IsNondegenerate := by
  refine ⟨(rankOne m).determinant_ne_zero_iff.mp ?_⟩
  rw [rankOne_determinant]
  exact mul_ne_zero two_ne_zero (NeZero.ne m)

/-- The smallest positive member of the family is the Layer 1 acceptance example `a1`. -/
theorem rankOne_one : rankOne 1 = a1 := by
  refine IntegralLattice.ext (Submodule.ext fun x ↦ ?_) (LinearMap.ext₂ fun x y ↦ ?_)
  · rw [mem_rankOne_carrier_iff, mem_a1_carrier_iff]
  · rw [rankOne_form_apply, a1_form_apply]
    norm_num

/-- The smallest negative member of the family is the Layer 1 acceptance example `negativeA1`. -/
theorem rankOne_neg_one : rankOne (-1) = negativeA1 := by
  refine IntegralLattice.ext (Submodule.ext fun x ↦ ?_) (LinearMap.ext₂ fun x y ↦ ?_)
  · rw [mem_rankOne_carrier_iff, mem_negativeA1_carrier_iff]
  · rw [rankOne_form_apply, negativeA1_form_apply]
    norm_num

/-! ## The dual lattice -/

section NeZero

variable (m : ℤ) [NeZero m]

private theorem rankOne_cast_ne_zero : (m : ℚ) ≠ 0 :=
  Int.cast_ne_zero.mpr (NeZero.ne m)

private theorem rankOne_two_mul_ne_zero : (2 * m : ℚ) ≠ 0 :=
  mul_ne_zero two_ne_zero (rankOne_cast_ne_zero m)

/-- The dual lattice of `⟨2m⟩` consists of the integer multiples of `1 / (2m)`. -/
theorem mem_rankOne_dualCarrier_iff (x : ℚ) :
    x ∈ (rankOne m).dualCarrier ↔ ∃ k : ℤ, x = k / (2 * m) := by
  have hmq := rankOne_cast_ne_zero m
  have h2m := rankOne_two_mul_ne_zero m
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp
      (hx 1 ((mem_rankOne_carrier_iff m 1).mpr ⟨1, by norm_num⟩))
    rw [eq_intCast, rankOne_form_apply, mul_one] at hk
    exact ⟨k, by rw [eq_div_iff h2m]; linear_combination -hk⟩
  · rintro ⟨k, rfl⟩ y hy
    obtain ⟨z, rfl⟩ := (mem_rankOne_carrier_iff m y).mp hy
    refine Submodule.mem_one.mpr ⟨k * z, ?_⟩
    rw [eq_intCast, rankOne_form_apply]
    push_cast
    field_simp

/-- The dual lattice of `⟨2m⟩` is the rank-one lattice generated by `1 / (2m)`. -/
theorem rankOne_dualCarrier_eq_span :
    (rankOne m).dualCarrier = Submodule.span ℤ {(1 / (2 * m) : ℚ)} := by
  ext x
  rw [mem_rankOne_dualCarrier_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [zsmul_eq_mul]; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [zsmul_eq_mul]; ring⟩

/-- The dual vector `e / (2m)`, the generator of the dual lattice of `⟨2m⟩`. -/
noncomputable def rankOneDualGen : (rankOne m).dualCarrier :=
  ⟨1 / (2 * m), (mem_rankOne_dualCarrier_iff m _).mpr ⟨1, by norm_num⟩⟩

/-- The underlying rational number of the distinguished dual vector is `1 / (2m)`. -/
@[simp]
theorem coe_rankOneDualGen :
    ((rankOneDualGen m : (rankOne m).dualCarrier) : ℚ) = 1 / (2 * m) := (rfl)

/-- The underlying rational number of the `k`-th multiple of the distinguished dual vector is
`k / (2m)`. -/
theorem coe_zsmul_rankOneDualGen (k : ℤ) :
    ((k • rankOneDualGen m : (rankOne m).dualCarrier) : ℚ) = k / (2 * m) := by
  rw [SetLike.val_smul, coe_rankOneDualGen, zsmul_eq_mul]
  ring

/-- Every dual vector of `⟨2m⟩` is an integer multiple of `e / (2m)`. -/
theorem exists_zsmul_rankOneDualGen (x : (rankOne m).dualCarrier) :
    ∃ k : ℤ, x = k • rankOneDualGen m := by
  obtain ⟨k, hk⟩ := (mem_rankOne_dualCarrier_iff m (x : ℚ)).mp x.2
  exact ⟨k, Subtype.ext (by rw [hk, coe_zsmul_rankOneDualGen])⟩

private theorem bijective_toSpanSingleton_rankOneDualGen :
    Function.Bijective
      ⇑(LinearMap.toSpanSingleton ℤ (rankOne m).dualCarrier (rankOneDualGen m)) := by
  refine ⟨fun k l hkl ↦ ?_, fun x ↦ ?_⟩
  · have h2m := rankOne_two_mul_ne_zero m
    have hcast : (k : ℚ) / (2 * m) = (l : ℚ) / (2 * m) := by
      simpa only [LinearMap.toSpanSingleton_apply, coe_zsmul_rankOneDualGen] using
        congrArg (fun x : (rankOne m).dualCarrier ↦ (x : ℚ)) hkl
    exact_mod_cast (div_left_inj' h2m).mp hcast
  · obtain ⟨k, hk⟩ := exists_zsmul_rankOneDualGen m x
    exact ⟨k, hk.symm⟩

/-- The dual lattice of `⟨2m⟩` is free of rank one on `e / (2m)`. -/
noncomputable def rankOneDualEquiv : ℤ ≃ₗ[ℤ] (rankOne m).dualCarrier :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _ (rankOneDualGen m))
    (bijective_toSpanSingleton_rankOneDualGen m)

/-- The identification of the dual lattice with `ℤ` sends `k` to `k / (2m)`. -/
@[simp]
theorem coe_rankOneDualEquiv (k : ℤ) :
    ((rankOneDualEquiv m k : (rankOne m).dualCarrier) : ℚ) = k / (2 * m) := by
  rw [rankOneDualEquiv, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
    coe_zsmul_rankOneDualGen]

/-- The identification of the dual lattice with `ℤ` sends `1` to the distinguished dual vector. -/
@[simp]
theorem rankOneDualEquiv_one : rankOneDualEquiv m 1 = rankOneDualGen m := by
  apply Subtype.ext
  rw [coe_rankOneDualEquiv, coe_rankOneDualGen]
  norm_num

/-! ## The discriminant group -/

/-- Under the identification of the dual lattice with `ℤ`, the original lattice is the ideal
generated by `2m`. -/
theorem comap_rankOneDualEquiv_carrierInDual :
    Submodule.comap (rankOneDualEquiv m).toLinearMap (rankOne m).carrierInDual =
      Ideal.span {2 * m} := by
  have hmq := rankOne_cast_ne_zero m
  have h2m := rankOne_two_mul_ne_zero m
  ext k
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, mem_carrierInDual_iff, coe_rankOneDualEquiv,
    mem_rankOne_carrier_iff, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hq : ((2 * m * z : ℤ) : ℚ) = (k : ℚ) := by
      rw [eq_div_iff h2m] at hz
      push_cast
      linear_combination hz
    exact_mod_cast hq.symm
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [eq_div_iff h2m]
    push_cast
    ring

/-- The distinguished generator `g = e / (2m) + L` of the discriminant group of `⟨2m⟩`. -/
noncomputable def rankOneClass : (rankOne m).DiscriminantGroup :=
  Submodule.Quotient.mk (rankOneDualGen m)

/-- A multiple of the distinguished discriminant class is the class of the corresponding multiple
of the distinguished dual vector. -/
theorem zsmul_rankOneClass (k : ℤ) :
    k • rankOneClass m = Submodule.Quotient.mk (k • rankOneDualGen m) := by
  rw [rankOneClass, Submodule.Quotient.mk_smul]

/-- The class `g` generates the discriminant group of `⟨2m⟩`. -/
theorem span_rankOneClass_eq_top :
    Submodule.span ℤ {rankOneClass m} = (⊤ : Submodule ℤ (rankOne m).DiscriminantGroup) := by
  rw [eq_top_iff]
  rintro a -
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨k, rfl⟩ := exists_zsmul_rankOneDualGen m x
    rw [← zsmul_rankOneClass]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The discriminant group of `⟨2m⟩` is cyclic of order `|2m|`**, generated by the class of
`e / (2m)`. -/
noncomputable def rankOneDiscriminantEquiv :
    (rankOne m).DiscriminantGroup ≃+ ZMod (2 * m).natAbs :=
  (Submodule.Quotient.equiv (rankOne m).carrierInDual (Ideal.span {2 * m})
        (rankOneDualEquiv m).symm (by
          rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm,
            comap_rankOneDualEquiv_carrierInDual])).toAddEquiv.trans
    (Int.quotientSpanEquivZMod (2 * m)).toAddEquiv

/-- The cyclic identification carries the distinguished class to the residue of `1`. -/
@[simp]
theorem rankOneDiscriminantEquiv_rankOneClass :
    rankOneDiscriminantEquiv m (rankOneClass m) = 1 := by
  have h : (rankOneDualEquiv m).symm (rankOneDualGen m) = 1 := by
    rw [← rankOneDualEquiv_one, LinearEquiv.symm_apply_apply]
  have hmk : ∀ k : ℤ, Int.quotientSpanEquivZMod (2 * m) (Submodule.Quotient.mk k) =
      (k : ZMod (2 * m).natAbs) := fun k ↦ by simp
  rw [rankOneDiscriminantEquiv, rankOneClass, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, hmk, h,
    Int.cast_one]

/-- The cyclic identification carries the `k`-th multiple of the distinguished class to the
residue of `k`. -/
@[simp]
theorem rankOneDiscriminantEquiv_zsmul_rankOneClass (k : ℤ) :
    rankOneDiscriminantEquiv m (k • rankOneClass m) = (k : ZMod (2 * m).natAbs) := by
  rw [map_zsmul, rankOneDiscriminantEquiv_rankOneClass, zsmul_eq_mul, mul_one]

/-- The discriminant group of `⟨2m⟩` has `|2m|` elements. -/
theorem natCard_rankOne_discriminantGroup :
    Nat.card (rankOne m).DiscriminantGroup = (2 * m).natAbs := by
  rw [natCard_discriminantGroup, discriminant_def, rankOne_determinant]

/-! ## The discriminant forms -/

/-- The discriminant pairing of `⟨2m⟩` on two multiples of the generator. -/
theorem discriminantPairing_zsmul_rankOneClass (k l : ℤ) :
    (rankOne m).discriminantPairing (k • rankOneClass m) (l • rankOneClass m) =
      ((k * l / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  have h2m := rankOne_two_mul_ne_zero m
  rw [zsmul_rankOneClass, zsmul_rankOneClass, discriminantPairing_mk, coe_zsmul_rankOneDualGen,
    coe_zsmul_rankOneDualGen, rankOne_form_apply]
  congr 1
  field_simp

/-- The displayed value `b_L(g, g) = 1 / (2m)`. -/
@[simp]
theorem discriminantPairing_rankOneClass_self :
    (rankOne m).discriminantPairing (rankOneClass m) (rankOneClass m) =
      ((1 / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using discriminantPairing_zsmul_rankOneClass m 1 1

/-- The half-norm discriminant quadratic form of `⟨2m⟩` on a multiple of the generator. -/
@[simp]
theorem discriminantQuadraticMap_zsmul_rankOneClass (k : ℤ) :
    (rankOne m).discriminantQuadraticMap (isEven_rankOne m) (k • rankOneClass m) =
      ((k ^ 2 / (4 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  have h2m := rankOne_two_mul_ne_zero m
  rw [zsmul_rankOneClass, discriminantQuadraticMap_mk, coe_zsmul_rankOneDualGen,
    rankOne_form_apply]
  congr 1
  field_simp
  ring

/-- The displayed value `q_L(g) = 1 / (4m)`, half of Nikulin's `ℚ/2ℤ`-valued `1 / (2m)`. -/
@[simp]
theorem discriminantQuadraticMap_rankOneClass :
    (rankOne m).discriminantQuadraticMap (isEven_rankOne m) (rankOneClass m) =
      ((1 / (4 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using discriminantQuadraticMap_zsmul_rankOneClass m 1

/-- **The displayed quadratic form polarizes to the displayed pairing.**  The polar of `q_L` at
`k • g` and `l • g` is the value `kl / (2m)` of `b_L` there. -/
theorem polar_discriminantQuadraticMap_zsmul_rankOneClass (k l : ℤ) :
    QuadraticMap.polar ((rankOne m).discriminantQuadraticMap (isEven_rankOne m))
        (k • rankOneClass m) (l • rankOneClass m) =
      ((k * l / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [polar_discriminantQuadraticMap, discriminantPairing_zsmul_rankOneClass]

end NeZero

/-! ## Definiteness and signature -/

/-- `⟨2m⟩` is positive-definite for positive `m`. -/
theorem isPosDef_rankOne {m : ℤ} (hm : 0 < m) : (rankOne m).IsPosDef := by
  rw [(rankOne m).isPosDef_iff]
  intro x hx
  rw [rankOne_form_apply]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  nlinarith [sq_pos_of_ne_zero hx]

/-- `⟨2m⟩` is negative-definite for negative `m`. -/
theorem isNegDef_rankOne {m : ℤ} (hm : m < 0) : (rankOne m).IsNegDef := by
  rw [(rankOne m).isNegDef_iff]
  intro x hx
  rw [rankOne_form_apply]
  have hmq : (m : ℚ) < 0 := by exact_mod_cast hm
  nlinarith [sq_pos_of_ne_zero hx]

/-- `⟨2m⟩` has signature `(1, 0, 0)` for positive `m`. -/
theorem rankOne_signature_of_pos {m : ℤ} (hm : 0 < m) : (rankOne m).signature = (1, 0, 0) := by
  have hvanish := (rankOne m).isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero.mp
    (isPosDef_rankOne hm)
  have hsum := (rankOne m).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- `⟨2m⟩` has signature `(0, 0, 1)` for negative `m`. -/
theorem rankOne_signature_of_neg {m : ℤ} (hm : m < 0) : (rankOne m).signature = (0, 0, 1) := by
  have hvanish := (rankOne m).isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero.mp
    (isNegDef_rankOne hm)
  have hsum := (rankOne m).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- `⟨2m⟩` is positive-definite exactly when `m` is positive. -/
theorem isPosDef_rankOne_iff (m : ℤ) : (rankOne m).IsPosDef ↔ 0 < m := by
  refine ⟨fun h ↦ ?_, isPosDef_rankOne⟩
  have hone := (rankOne m).isPosDef_iff.mp h 1 one_ne_zero
  rw [rankOne_form_apply] at hone
  have hmq : (0 : ℚ) < m := by nlinarith
  exact_mod_cast hmq

/-- The excluded parameter gives the degenerate rank-one lattice. -/
theorem isDegenerate_rankOne_zero : (rankOne 0).IsDegenerate := by
  rw [(rankOne 0).isDegenerate_iff_not_nondegenerate]
  intro h
  exact (rankOne 0).determinant_ne_zero_iff.mpr h (by simp)

/-- The degenerate rank-one lattice has signature `(0, 1, 0)`. -/
theorem rankOne_zero_signature : (rankOne 0).signature = (0, 1, 0) := by
  have hzero : ∀ x : ℚ, (rankOne 0).form x x = 0 := by
    intro x
    rw [rankOne_form_apply]
    ring
  have hsigNeg : (rankOne 0).sigNeg = 0 :=
    (rankOne 0).isPosSemidef_iff_sigNeg_eq_zero.mp
      ((rankOne 0).isPosSemidef_iff.mpr fun x ↦ (hzero x).ge)
  have hsigPos : (rankOne 0).sigPos = 0 :=
    (rankOne 0).isNegSemidef_iff_sigPos_eq_zero.mp
      ((rankOne 0).isNegSemidef_iff.mpr fun x ↦ (hzero x).le)
  have hsum := (rankOne 0).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

end IntegralLattice

end TauCeti
