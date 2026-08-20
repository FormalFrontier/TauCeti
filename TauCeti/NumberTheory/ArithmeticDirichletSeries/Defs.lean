/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Arithmetic functions on the nonzero ideals of a field

An *ideal arithmetic function* for a field `K` is a complex-valued function on the
nonzero integral ideals of `𝓞 K`, that is, on the submonoid `(Ideal (𝓞 K))⁰` of
non-zero-divisors of the ideal monoid. This is the primary carrier for the whole
`ArithmeticDirichletSeries` development. For the number fields used in later layers,
restricting to nonzero ideals permits finite divisor sums over factorizations `B * C = A`;
in particular, the infinitely many formal factorizations `⊥ * J = ⊥` of the zero ideal are
never in the index type.

The counterpart to that choice is a canonical way back to functions on *all* ideals, and
that is `TauCeti.IdealArithmeticFunction.zeroExtend`, which extends by the value `0` at `⊥`.

## Main declarations

* `TauCeti.IdealArithmeticFunction`: the carrier, a function `(Ideal (𝓞 K))⁰ → ℂ`;
* `TauCeti.IdealArithmeticFunction.zeroExtend`: the canonical extension by zero at `⊥`;
* `TauCeti.IdealArithmeticFunction.zeroExtend_eq_zero_iff_eq_bot`: for a nowhere-vanishing
  ideal arithmetic function the extension vanishes exactly at `⊥`;
* `TauCeti.IdealArithmeticFunction.exists_zeroExtend_eq_iff`: a function on all ideals is a
  zero extension exactly when it vanishes at `⊥`, whence
  `TauCeti.IdealArithmeticFunction.zeroExtend_ne_const_one`: the everywhere-one function on all
  ideals is not a zero extension;
* `TauCeti.IdealArithmeticFunction.map` and `TauCeti.IdealArithmeticFunction.mapEquiv`:
  functoriality under an isomorphism `K ≃+* L` of the ambient fields, with
  `TauCeti.IdealArithmeticFunction.map_id`, `TauCeti.IdealArithmeticFunction.map_map` and the
  compatibility `TauCeti.IdealArithmeticFunction.zeroExtend_map`.

## Implementation notes

`IdealArithmeticFunction` is a reducible abbreviation for the function type, so the pointwise
`ℂ`-module and pointwise multiplication structures are the ones inherited from `Pi`. Ideal
convolution (roadmap Layer 2) will be a separate named operation, never the pointwise product.
`zeroExtend` is `Function.extend` along the inclusion of the nonzero ideals, so its pointwise
algebra laws are Mathlib's `Function.extend_mul` and its additive companions.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open NumberField nonZeroDivisors

variable {K : Type*} [Field K]

/-- An **ideal arithmetic function** for a field `K`: a complex-valued function on the
nonzero integral ideals of `𝓞 K`. The index type is the submonoid `(Ideal (𝓞 K))⁰` of
non-zero-divisors of the ideal monoid, which is exactly the set of ideals different from `⊥`
because `𝓞 K` is a domain (`mem_nonZeroDivisors_iff_ne_zero`). -/
abbrev IdealArithmeticFunction (K : Type*) [Field K] : Type _ :=
  (Ideal (𝓞 K))⁰ → ℂ

namespace IdealArithmeticFunction

/-- The canonical extension of an ideal arithmetic function to *all* integral ideals of
`𝓞 K`, taking the value `0` at the zero ideal `⊥`. This is `Function.extend` along the
inclusion of the nonzero ideals. -/
noncomputable def zeroExtend (f : IdealArithmeticFunction K) : Ideal (𝓞 K) → ℂ :=
  Function.extend Subtype.val f 0

@[simp]
theorem zeroExtend_coe (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.zeroExtend I = f I :=
  Subtype.val_injective.extend_apply f 0 I

theorem zeroExtend_of_ne_bot (f : IdealArithmeticFunction K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    f.zeroExtend I = f ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ :=
  f.zeroExtend_coe ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩

@[simp]
theorem zeroExtend_bot (f : IdealArithmeticFunction K) : f.zeroExtend ⊥ = 0 :=
  Function.extend_apply' f (0 : Ideal (𝓞 K) → ℂ) ⊥ fun ⟨I, hI⟩ ↦
    mem_nonZeroDivisors_iff_ne_zero.mp I.2 hI

/-- **The zero extension detects the zero ideal.** If an ideal arithmetic function has no zero
values, then its zero extension vanishes at exactly one ideal, namely `⊥`. -/
theorem zeroExtend_eq_zero_iff_eq_bot {f : IdealArithmeticFunction K} (hf : ∀ I, f I ≠ 0)
    {I : Ideal (𝓞 K)} : f.zeroExtend I = 0 ↔ I = ⊥ := by
  refine ⟨fun h ↦ by_contra fun hI ↦ ?_, fun h ↦ h ▸ f.zeroExtend_bot⟩
  exact hf ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
    (by rwa [f.zeroExtend_of_ne_bot hI] at h)

theorem zeroExtend_injective :
    Function.Injective (zeroExtend : IdealArithmeticFunction K → Ideal (𝓞 K) → ℂ) := by
  intro f g h
  ext I
  simpa using congrFun h I

@[simp]
theorem zeroExtend_inj {f g : IdealArithmeticFunction K} :
    f.zeroExtend = g.zeroExtend ↔ f = g :=
  zeroExtend_injective.eq_iff

/-- **The zero extensions are exactly the functions vanishing at `⊥`.** -/
theorem exists_zeroExtend_eq_iff {g : Ideal (𝓞 K) → ℂ} :
    (∃ f : IdealArithmeticFunction K, f.zeroExtend = g) ↔ g ⊥ = 0 := by
  refine ⟨fun ⟨f, hf⟩ ↦ hf ▸ f.zeroExtend_bot, fun hg ↦ ⟨fun I ↦ g I, funext fun I ↦ ?_⟩⟩
  rcases eq_or_ne I ⊥ with rfl | hI
  · simpa using hg.symm
  · simp [zeroExtend_of_ne_bot _ hI]

/-- **Rejection test.** The everywhere-one function on *all* integral ideals is not the zero
extension of any ideal arithmetic function: a zero extension vanishes at `⊥`. Compare
`TauCeti.IdealArithmeticFunction.zeroExtend_one_apply`, which computes the zero extension of
the constant function `1` on the *nonzero* ideals. -/
theorem zeroExtend_ne_const_one (f : IdealArithmeticFunction K) :
    f.zeroExtend ≠ Function.const _ 1 := by
  intro h
  simpa using congrFun h ⊥

theorem zeroExtend_one_apply (I : Ideal (𝓞 K)) :
    (1 : IdealArithmeticFunction K).zeroExtend I = if I = ⊥ then 0 else 1 := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [zeroExtend_of_ne_bot _ hI, hI]

@[simp]
theorem zeroExtend_zero : (0 : IdealArithmeticFunction K).zeroExtend = 0 :=
  Function.extend_zero (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K))

@[simp]
theorem zeroExtend_add (f g : IdealArithmeticFunction K) :
    (f + g).zeroExtend = f.zeroExtend + g.zeroExtend := by
  have h := Function.extend_add (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f g 0 0
  rwa [add_zero] at h

@[simp]
theorem zeroExtend_mul (f g : IdealArithmeticFunction K) :
    (f * g).zeroExtend = f.zeroExtend * g.zeroExtend := by
  have h := Function.extend_mul (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f g 0 0
  rwa [mul_zero] at h

@[simp]
theorem zeroExtend_neg (f : IdealArithmeticFunction K) :
    (-f).zeroExtend = -f.zeroExtend := by
  have h := Function.extend_neg (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f 0
  rwa [neg_zero] at h

@[simp]
theorem zeroExtend_sub (f g : IdealArithmeticFunction K) :
    (f - g).zeroExtend = f.zeroExtend - g.zeroExtend := by
  have h := Function.extend_sub (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f g 0 0
  rwa [sub_zero] at h

@[simp]
theorem zeroExtend_smul (c : ℂ) (f : IdealArithmeticFunction K) :
    (c • f).zeroExtend = c • f.zeroExtend := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [zeroExtend_of_ne_bot _ hI]

/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [Field M]

private theorem mapRingEquiv_refl_apply (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv (RingEquiv.refl K) x = x :=
  RingOfIntegers.ext rfl

private theorem mapRingEquiv_trans_apply (e : K ≃+* L) (e' : L ≃+* M) (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv e' (RingOfIntegers.mapRingEquiv e x) =
      RingOfIntegers.mapRingEquiv (e.trans e') x :=
  RingOfIntegers.ext rfl

private theorem comap_mapRingEquiv_refl (I : Ideal (𝓞 K)) :
    Ideal.comap (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)) I = I := by
  ext x
  rw [Ideal.mem_comap, mapRingEquiv_refl_apply]

private theorem comap_mapRingEquiv_trans (e : K ≃+* L) (e' : L ≃+* M) (I : Ideal (𝓞 M)) :
    Ideal.comap (RingOfIntegers.mapRingEquiv e)
        (Ideal.comap (RingOfIntegers.mapRingEquiv e') I) =
      Ideal.comap (RingOfIntegers.mapRingEquiv (e.trans e')) I := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, mapRingEquiv_trans_apply]

/-- **Transport along an isomorphism of fields.** An isomorphism `e : K ≃+* L` carries an ideal
arithmetic function for `K` to one for `L`: the value at a nonzero ideal of `𝓞 L` is the value
of `f` at its preimage in `𝓞 K` under `NumberField.RingOfIntegers.mapRingEquiv e`. -/
noncomputable def map (e : K ≃+* L) (f : IdealArithmeticFunction K) :
    IdealArithmeticFunction L := fun J ↦
  f.zeroExtend (Ideal.comap (RingOfIntegers.mapRingEquiv e) (J : Ideal (𝓞 L)))

/-- **Transport is compatible with extension by zero**: both extensions send an ideal of `𝓞 L`
to the value of `f` at its preimage in `𝓞 K`, the zero ideal included. -/
@[simp]
theorem zeroExtend_map (e : K ≃+* L) (f : IdealArithmeticFunction K) (I : Ideal (𝓞 L)) :
    (map e f).zeroExtend I =
      f.zeroExtend (Ideal.comap (RingOfIntegers.mapRingEquiv e) I) := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [zeroExtend_bot, Ideal.comap_bot_of_injective _
      (RingOfIntegers.mapRingEquiv e).injective, zeroExtend_bot]
  · rw [zeroExtend_of_ne_bot _ hI]
    rfl

@[simp]
theorem map_id (f : IdealArithmeticFunction K) : map (RingEquiv.refl K) f = f :=
  zeroExtend_injective <| funext fun I ↦ by
    rw [zeroExtend_map, comap_mapRingEquiv_refl]

/-- **Transport is functorial**: transporting along `e` and then along `e'` is the same as
transporting along `e.trans e'`. -/
theorem map_map (e : K ≃+* L) (e' : L ≃+* M) (f : IdealArithmeticFunction K) :
    map e' (map e f) = map (e.trans e') f :=
  zeroExtend_injective <| funext fun I ↦ by
    rw [zeroExtend_map, zeroExtend_map, zeroExtend_map, comap_mapRingEquiv_trans]

/-- **Transport along an isomorphism of fields, as an equivalence** of the two carriers, with
inverse the transport along `e.symm`. -/
noncomputable def mapEquiv (e : K ≃+* L) :
    IdealArithmeticFunction K ≃ IdealArithmeticFunction L where
  toFun := map e
  invFun := map e.symm
  left_inv f := by rw [map_map, e.self_trans_symm, map_id]
  right_inv f := by rw [map_map, e.symm_trans_self, map_id]

@[simp]
theorem mapEquiv_apply (e : K ≃+* L) (f : IdealArithmeticFunction K) :
    mapEquiv e f = map e f := (rfl)

@[simp]
theorem mapEquiv_symm_apply (e : K ≃+* L) (f : IdealArithmeticFunction L) :
    (mapEquiv e).symm f = map e.symm f := (rfl)

end Transport

end IdealArithmeticFunction

end TauCeti
