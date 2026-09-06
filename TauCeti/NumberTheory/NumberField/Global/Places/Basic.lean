/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ProductFormula
public import TauCeti.Algebra.BigOperators.Finprod

/-!
# Places of a number field and their normalized absolute values

Mathlib indexes the two kinds of place of a number field `K` by two unrelated types: the finite
places by `IsDedekindDomain.HeightOneSpectrum (𝓞 K)` and the infinite places by
`NumberField.InfinitePlace K`.  Both carry an absolute value, but with different normalizations,
and the product formula `NumberField.prod_abs_eq_one` is stated as a product over the finite
places times a product over the infinite places.

This file introduces the single indexing type `TauCeti.GlobalNumberFields.Place K` for all places
of `K`, together with the normalized absolute value `‖·‖_v` attached to a place `v`, and states
the product formula as one `finprod` over that type.

The normalization is the one that makes the product formula hold with all exponents equal to one:

* at a finite place `v`, `‖x‖_v` is the `v`-adic absolute value `NumberField.HeightOneSpectrum.
  adicAbv`, that is `(N v) ^ (-v x)`;
* at a real place `w`, `‖x‖_w = |x|` computed through the real embedding;
* at a complex place `w`, `‖x‖_w = |x| ^ 2` computed through either complex embedding.

Because of the square at the complex places, `‖·‖_v` is not an `AbsoluteValue` — it does not
satisfy the triangle inequality there — so it is bundled as a `MonoidWithZeroHom`.  This is the
standard normalization: `‖·‖_v` is the module of the local field at `v`, which is what the idele
norm and the product formula require.

## Main definitions

* `TauCeti.GlobalNumberFields.Place`: the places of `K`, finite and infinite together.
* `TauCeti.GlobalNumberFields.normalizedAbsValue`: the normalized absolute value at a place.

## Main results

* `TauCeti.GlobalNumberFields.forall_normalizedAbsValue_inl_le_one_iff`: an element of `K` is an
  algebraic integer exactly when its normalized absolute value is at most `1` at every finite
  place.
* `TauCeti.GlobalNumberFields.hasFiniteMulSupport_normalizedAbsValue`: a nonzero element of `K`
  has normalized absolute value `1` at all but finitely many places.
* `TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_eq_one`: the product formula, as a single
  product over all places of `K`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II.
* J. Neukirch, *Algebraic Number Theory*, Chapter III.
-/

public section

open Function IsDedekindDomain NumberField
open scoped NNReal NumberField

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- A place of a number field `K`: either a finite place, indexed by a height one prime of `𝓞 K`,
or an infinite place.  This is an abbreviation for the disjoint union of Mathlib's two indexing
types; it is the uniform vocabulary in which statements ranging over *all* places of `K` (the
product formula, the restricted product defining the adeles, the idele norm) are phrased. -/
abbrev Place : Type _ := HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

variable {K}

/-- The normalized absolute value at a place of a number field: the `v`-adic absolute value at a
finite place `v`, and `w x ^ w.mult` at an infinite place `w`, so that a real place contributes
`|x|` and a complex place contributes `|x| ^ 2`.

At a complex place this is not subadditive, so it is bundled as a `MonoidWithZeroHom` rather than
as an `AbsoluteValue`. -/
noncomputable def normalizedAbsValue : Place K → K →*₀ ℝ
  | .inl v => (NumberField.HeightOneSpectrum.adicAbv K v).toMonoidWithZeroHom
  | .inr w =>
    { toFun x := w x ^ w.mult
      map_zero' := by simp [zero_pow InfinitePlace.mult_ne_zero]
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[simp]
theorem normalizedAbsValue_inl (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    normalizedAbsValue (Sum.inl v) x = NumberField.HeightOneSpectrum.adicAbv K v x := (rfl)

@[simp]
theorem normalizedAbsValue_inr (w : InfinitePlace K) (x : K) :
    normalizedAbsValue (Sum.inr w) x = w x ^ w.mult := (rfl)

/-- At a real place the normalized absolute value is the absolute value itself. -/
theorem normalizedAbsValue_inr_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    normalizedAbsValue (Sum.inr w) x = w x := by
  simp [hw.mult_eq_one]

/-- At a complex place the normalized absolute value is the *square* of the absolute value. -/
theorem normalizedAbsValue_inr_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (x : K) :
    normalizedAbsValue (Sum.inr w) x = w x ^ 2 := by
  simp [hw.mult_eq_two]

/-- The normalized absolute value at an infinite place, computed through a complex embedding
defining the place. -/
theorem normalizedAbsValue_inr_eq_norm_embedding (w : InfinitePlace K) (x : K) :
    normalizedAbsValue (Sum.inr w) x = ‖w.embedding x‖ ^ w.mult := by
  rw [normalizedAbsValue_inr, InfinitePlace.norm_embedding_eq]

theorem normalizedAbsValue_nonneg (v : Place K) (x : K) : 0 ≤ normalizedAbsValue v x := by
  cases v with
  | inl v => exact (NumberField.HeightOneSpectrum.adicAbv K v).nonneg x
  | inr w => exact pow_nonneg (apply_nonneg w x) _

theorem normalizedAbsValue_eq_zero (v : Place K) {x : K} :
    normalizedAbsValue v x = 0 ↔ x = 0 :=
  map_eq_zero _

theorem normalizedAbsValue_pos (v : Place K) {x : K} (hx : x ≠ 0) :
    0 < normalizedAbsValue v x :=
  (normalizedAbsValue_nonneg v x).lt_of_ne fun h ↦ hx ((normalizedAbsValue_eq_zero v).mp h.symm)

section Integers

variable (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)

/-- An algebraic integer has normalized absolute value at most `1` at every finite place. -/
theorem normalizedAbsValue_inl_algebraMap_le_one :
    normalizedAbsValue (Sum.inl v) (algebraMap (𝓞 K) K x) ≤ 1 := by
  rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_le_one K v x

/-- An algebraic integer has normalized absolute value exactly `1` at a finite place precisely
when it avoids the corresponding prime. -/
theorem normalizedAbsValue_inl_algebraMap_eq_one_iff :
    normalizedAbsValue (Sum.inl v) (algebraMap (𝓞 K) K x) = 1 ↔ x ∉ v.asIdeal := by
  rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_eq_one_iff_notMem K v x

/-- At a finite place, having normalized absolute value at most `1` is having `v`-adic valuation
at most `1`. -/
theorem normalizedAbsValue_inl_le_one_iff (y : K) :
    normalizedAbsValue (Sum.inl v) y ≤ 1 ↔ v.valuation K y ≤ 1 := by
  rw [normalizedAbsValue_inl, NumberField.HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

/-- An element of a number field is an algebraic integer exactly when its normalized absolute
value is at most `1` at every finite place. -/
theorem forall_normalizedAbsValue_inl_le_one_iff (y : K) :
    (∀ v : HeightOneSpectrum (𝓞 K), normalizedAbsValue (Sum.inl v) y ≤ 1) ↔
      y ∈ (algebraMap (𝓞 K) K).range := by
  refine ⟨fun h ↦ IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K y
    fun v ↦ (normalizedAbsValue_inl_le_one_iff v y).mp (h v), ?_⟩
  rintro ⟨z, rfl⟩ v
  exact normalizedAbsValue_inl_algebraMap_le_one v z

open Ideal in
/-- The normalized absolute value of a nonzero algebraic integer at a finite place, explicitly:
the ideal norm of the prime, raised to minus the multiplicity of that prime in the principal ideal
generated by the integer. -/
theorem normalizedAbsValue_inl_algebraMap_eq_absNorm_zpow (hx : x ≠ 0) :
    normalizedAbsValue (Sum.inl v) (algebraMap (𝓞 K) K x) =
      (absNorm v.asIdeal : ℝ) ^ (-(multiplicity v.asIdeal (span {x}) : ℤ)) := by
  have h := FinitePlace.apply_mul_absNorm_pow_eq_one (FinitePlace.mk v) hx
  rw [FinitePlace.maximalIdeal_mk, FinitePlace.mk_apply, FinitePlace.norm_embedding] at h
  rw [normalizedAbsValue_inl, zpow_neg, zpow_natCast]
  exact eq_inv_of_mul_eq_one_left h

end Integers

variable {x : K}

/-- A nonzero element of a number field lies outside all but finitely many height one primes,
so its `v`-adic absolute values are almost all `1`. -/
theorem hasFiniteMulSupport_adicAbv (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      NumberField.HeightOneSpectrum.adicAbv K v x := by
  refine Set.Finite.subset
    (Set.Finite.image FinitePlace.maximalIdeal (FinitePlace.hasFiniteMulSupport hx)) ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [FinitePlace.mk_apply, FinitePlace.norm_embedding] using hv

/-- A nonzero element of a number field has normalized absolute value `1` at all but finitely
many places. -/
theorem hasFiniteMulSupport_normalizedAbsValue (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : Place K ↦ normalizedAbsValue v x :=
  hasFiniteMulSupport_sum_type (hasFiniteMulSupport_adicAbv hx) (Set.toFinite _)

/-- The finite part of the product formula, indexed by the height one primes of `𝓞 K`. -/
theorem finprod_normalizedAbsValue_inl (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), normalizedAbsValue (Sum.inl v) x =
      |(Algebra.norm ℚ) x|⁻¹ := by
  have h (v : HeightOneSpectrum (𝓞 K)) : normalizedAbsValue (Sum.inl v) x =
      (FinitePlace.equivHeightOneSpectrum.symm v) x := by
    rw [normalizedAbsValue_inl, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  rw [finprod_congr h,
    finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
      (f := fun w : FinitePlace K ↦ w x),
    FinitePlace.prod_eq_inv_abs_norm hx]

/-- **The product formula** for a number field, as a single product over all of its places, finite
and infinite, of the normalized absolute values. -/
theorem finprod_normalizedAbsValue_eq_one (hx : x ≠ 0) :
    ∏ᶠ v : Place K, normalizedAbsValue v x = 1 := by
  rw [finprod_sum_type _ (hasFiniteMulSupport_adicAbv hx) (Set.toFinite _),
    finprod_normalizedAbsValue_inl hx, finprod_eq_prod_of_fintype]
  simp only [normalizedAbsValue_inr]
  rw [InfinitePlace.prod_eq_abs_norm]
  have h0 : |(Algebra.norm ℚ) x| ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using hx
  rw [← Rat.cast_mul, inv_mul_cancel₀ h0, Rat.cast_one]

end TauCeti.GlobalNumberFields
