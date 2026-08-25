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
# Arithmetic functions on nonzero ideals

For the intended number-field applications, an ideal-indexed Dirichlet series should not assign an
arithmetic coefficient to the zero ideal. Excluding it ensures that ideal convolution never
considers factorizations through the zero ideal. This file introduces the carrier used throughout
the arithmetic-Dirichlet-series roadmap, parameterized over an arbitrary field:

* `TauCeti.IdealArithmeticFunction K` is a complex-valued function on the nonzero ideals of
  `𝓞 K`;
* `TauCeti.IdealArithmeticFunction.zeroExtend` is its canonical extension to all integral ideals,
  with value zero at the zero ideal;
* `TauCeti.IdealArithmeticFunction.restrict` restricts a function on all ideals to the nonzero
  ideals;
* `TauCeti.IdealArithmeticFunction.map` and `TauCeti.IdealArithmeticFunction.mapEquiv`:
  functoriality under an isomorphism `K ≃+* L` of the ambient fields.

The two operations are inverse precisely on functions vanishing at the zero ideal. The resulting
existence-and-uniqueness API is recorded without exposing the implementation of `zeroExtend`:
`TauCeti.IdealArithmeticFunction.existsUnique_zeroExtend_eq` characterizes its image, while
`TauCeti.IdealArithmeticFunction.zeroExtend_injective` says that no information is lost.

The extension respects the pointwise additive, scalar, and multiplicative operations. It does not
preserve the pointwise unit: the constant-one function on all ideals takes value one at the zero
ideal, and therefore cannot be a zero extension. The theorem
`TauCeti.IdealArithmeticFunction.not_exists_zeroExtend_eq_one` is the zero-ideal rejection test
required by Layer 0 of the roadmap.

## Roadmap role

This is Layer **0.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, and is the common
carrier on which its norm regrouping, ideal convolution, Euler products, and summatory functions
are built. Later Layer 0 files add completely multiplicative and unitary subtypes; those are
special coefficient systems on this general carrier, not replacements for it.

## References

* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose Layer 0.1 nonzero-ideal
  carrier and zero-extension design are adapted here.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open NumberField nonZeroDivisors

variable (K : Type*) [Field K]

/-- An **ideal arithmetic function** over a field `K`: a complex-valued function on the nonzero
ideals of `𝓞 K`.

The domain is `(Ideal (𝓞 K))⁰`, Mathlib's non-zero-divisor submonoid. Since the ring of integers is
a domain, its elements are exactly the ideals different from `⊥`. For number fields, keeping `⊥`
out of the carrier ensures that later divisor sums use only the nonzero-ideal factorization
theory. -/
abbrev IdealArithmeticFunction := (Ideal (𝓞 K))⁰ → ℂ

namespace IdealArithmeticFunction

variable {K}

/-- Extend an ideal arithmetic function to all integral ideals by assigning zero to `⊥`.

Use `zeroExtend_bot` and `zeroExtend_coe` to simplify its two characteristic cases, rather than
unfolding this definition. -/
noncomputable def zeroExtend (f : IdealArithmeticFunction K) : Ideal (𝓞 K) → ℂ := fun I =>
  Function.extend Subtype.val f 0 I

private theorem zeroExtend_eq_extend (f : IdealArithmeticFunction K) :
    f.zeroExtend = Function.extend Subtype.val f 0 := (rfl)

/-- Restrict a function on all integral ideals to the nonzero ideals. -/
def restrict (g : Ideal (𝓞 K) → ℂ) : IdealArithmeticFunction K := fun I => g I

@[simp]
theorem restrict_apply (g : Ideal (𝓞 K) → ℂ) (I : (Ideal (𝓞 K))⁰) : restrict g I = g I := by
  simp [restrict]

/-- The zero extension is zero at the zero ideal. -/
@[simp]
theorem zeroExtend_bot (f : IdealArithmeticFunction K) : f.zeroExtend ⊥ = 0 := by
  simp [zeroExtend]

/-- Away from `⊥`, the zero extension is the original ideal arithmetic function. -/
@[simp]
theorem zeroExtend_of_ne (f : IdealArithmeticFunction K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    f.zeroExtend I = f ⟨I, by simpa using hI⟩ := by
  rw [zeroExtend]
  exact Function.extend_val_apply (by simpa using hI)

/-- The zero extension agrees with the original function on every nonzero ideal. -/
@[simp]
theorem zeroExtend_coe (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.zeroExtend I = f I := by
  exact Subtype.val_injective.extend_apply f 0 I

/-- Restricting a zero extension recovers the original ideal arithmetic function. -/
@[simp]
theorem restrict_zeroExtend (f : IdealArithmeticFunction K) : restrict f.zeroExtend = f := by
  funext I
  simp

/-- Extending a restriction recovers a function on all ideals exactly when it vanishes at `⊥`. -/
@[simp]
theorem zeroExtend_restrict {g : Ideal (𝓞 K) → ℂ} (hg : g ⊥ = 0) :
    (restrict g).zeroExtend = g := by
  funext I
  by_cases hI : I = ⊥
  · simpa [hI] using hg.symm
  · simp [hI]

/-- A function on all ideals is a zero extension if and only if it vanishes at `⊥`. -/
theorem exists_zeroExtend_eq_iff {g : Ideal (𝓞 K) → ℂ} :
    (∃ f : IdealArithmeticFunction K, f.zeroExtend = g) ↔ g ⊥ = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact zeroExtend_bot f
  · intro hg
    exact ⟨restrict g, zeroExtend_restrict hg⟩

/-- Zero extension is injective: its values on nonzero ideals retain the entire function. -/
theorem zeroExtend_injective :
    Function.Injective (zeroExtend : IdealArithmeticFunction K → Ideal (𝓞 K) → ℂ) :=
  Function.extend_injective
    (f := (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K))) Subtype.val_injective
      (0 : Ideal (𝓞 K) → ℂ)

/-- Two zero extensions agree exactly when the underlying ideal arithmetic functions agree. -/
@[simp]
theorem zeroExtend_eq_iff {f g : IdealArithmeticFunction K} :
    f.zeroExtend = g.zeroExtend ↔ f = g := zeroExtend_injective.eq_iff

/-- A function on all ideals that vanishes at `⊥` is the zero extension of a unique ideal
arithmetic function. -/
theorem existsUnique_zeroExtend_eq {g : Ideal (𝓞 K) → ℂ} (hg : g ⊥ = 0) :
    ∃! f : IdealArithmeticFunction K, f.zeroExtend = g := by
  refine ⟨restrict g, zeroExtend_restrict hg, fun f hf => ?_⟩
  exact zeroExtend_injective (hf.trans (zeroExtend_restrict hg).symm)

/-- The zero extension is zero exactly at `⊥` when the original function has no zero values. -/
theorem zeroExtend_eq_zero_iff (f : IdealArithmeticFunction K)
    (hf : ∀ I, f I ≠ 0) {I : Ideal (𝓞 K)} : f.zeroExtend I = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    by_contra hI
    exact hf ⟨I, by simpa using hI⟩ ((zeroExtend_of_ne f hI).symm.trans h)
  · rintro rfl
    exact zeroExtend_bot f

/-- If the original function does not vanish, its zero extension is nonzero at every nonzero
ideal. -/
theorem zeroExtend_ne_zero (f : IdealArithmeticFunction K) (hf : ∀ I, f I ≠ 0)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : f.zeroExtend I ≠ 0 := by
  intro hzero
  exact hI ((zeroExtend_eq_zero_iff f hf).mp hzero)

/-! ## Compatibility with pointwise operations -/

/-- Zero extension preserves the pointwise zero function. -/
@[simp]
theorem zeroExtend_zero : zeroExtend (0 : IdealArithmeticFunction K) = 0 := by
  simpa [zeroExtend_eq_extend] using
    (Function.extend_zero (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)))

/-- Zero extension preserves pointwise addition. -/
@[simp]
theorem zeroExtend_add (f g : IdealArithmeticFunction K) :
    zeroExtend (f + g) = f.zeroExtend + g.zeroExtend := by
  simpa [zeroExtend_eq_extend] using
    (Function.extend_add (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f g 0 0)

/-- Zero extension preserves pointwise negation. -/
@[simp]
theorem zeroExtend_neg (f : IdealArithmeticFunction K) : zeroExtend (-f) = -f.zeroExtend := by
  simpa [zeroExtend_eq_extend] using
    (Function.extend_neg (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f 0)

/-- Zero extension preserves pointwise subtraction. -/
@[simp]
theorem zeroExtend_sub (f g : IdealArithmeticFunction K) :
    zeroExtend (f - g) = f.zeroExtend - g.zeroExtend := by
  simpa [zeroExtend_eq_extend] using
    (Function.extend_sub (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f g 0 0)

/-- Zero extension preserves pointwise complex scalar multiplication. -/
@[simp]
theorem zeroExtend_smul (c : ℂ) (f : IdealArithmeticFunction K) :
    zeroExtend (c • f) = c • f.zeroExtend := by
  simpa [zeroExtend_eq_extend] using
    (Function.extend_smul c (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f 0)

/-- Zero extension preserves pointwise multiplication. -/
@[simp]
theorem zeroExtend_mul (f g : IdealArithmeticFunction K) :
    zeroExtend (f * g) = f.zeroExtend * g.zeroExtend := by
  simpa [zeroExtend_eq_extend] using
    (Function.extend_mul (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) f g 0 0)

/-- **Rejection test.** The everywhere-one function on *all* integral ideals is not the zero
extension of any ideal arithmetic function, since its value at `⊥` is one rather than zero. This
is the roadmap's zero-ideal rejection test. Compare
`TauCeti.IdealArithmeticFunction.zeroExtend_one_apply`, which computes the zero extension of the
constant function `1` on the *nonzero* ideals. -/
theorem not_exists_zeroExtend_eq_one :
    ¬ ∃ f : IdealArithmeticFunction K, f.zeroExtend = (1 : Ideal (𝓞 K) → ℂ) := by
  rw [exists_zeroExtend_eq_iff]
  exact one_ne_zero

/-- The constant-one function on nonzero ideals extends to the indicator of ideals unequal to
`⊥`. -/
theorem zeroExtend_one_apply (I : Ideal (𝓞 K)) :
    (1 : IdealArithmeticFunction K).zeroExtend I = if I = ⊥ then 0 else 1 := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [hI]

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
      Ideal.comap (RingOfIntegers.mapRingEquiv (e.trans e')) I :=
  (Ideal.comap_comap (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 L)
    (RingOfIntegers.mapRingEquiv e' : 𝓞 L →+* 𝓞 M)).trans
    (congrArg (Ideal.comap · I) (RingHom.ext (mapRingEquiv_trans_apply e e')))

private theorem comap_mapRingEquiv_eq_bot_iff (e : K ≃+* L) {I : Ideal (𝓞 L)} :
    Ideal.comap (RingOfIntegers.mapRingEquiv e) I = ⊥ ↔ I = ⊥ := by
  rw [← Ideal.map_symm]
  exact Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).symm.injective

/-- **Transport along an isomorphism of fields.** An isomorphism `e : K ≃+* L` carries an ideal
arithmetic function for `K` to one for `L`: the value at a nonzero ideal of `𝓞 L` is the value
of `f` at its preimage in `𝓞 K` under `NumberField.RingOfIntegers.mapRingEquiv e`. -/
noncomputable def map (e : K ≃+* L) (f : IdealArithmeticFunction K) :
    IdealArithmeticFunction L := fun J ↦
  f.zeroExtend (Ideal.comap (RingOfIntegers.mapRingEquiv e) (J : Ideal (𝓞 L)))

/-- Defining equation of `TauCeti.IdealArithmeticFunction.map`: the value at a nonzero ideal
of `𝓞 L` is the zero extension of `f` at its preimage in `𝓞 K`. -/
@[simp]
theorem map_apply (e : K ≃+* L) (f : IdealArithmeticFunction K) (J : (Ideal (𝓞 L))⁰) :
    map e f J = f.zeroExtend (Ideal.comap (RingOfIntegers.mapRingEquiv e) (J : Ideal (𝓞 L))) :=
  (rfl)

/-- **Transport is compatible with extension by zero**: both extensions send an ideal of `𝓞 L`
to the value of `f` at its preimage in `𝓞 K`, the zero ideal included. -/
@[simp]
theorem zeroExtend_map (e : K ≃+* L) (f : IdealArithmeticFunction K) (I : Ideal (𝓞 L)) :
    (map e f).zeroExtend I =
      f.zeroExtend (Ideal.comap (RingOfIntegers.mapRingEquiv e) I) := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [zeroExtend_bot, Ideal.comap_bot_of_injective _
      (RingOfIntegers.mapRingEquiv e).injective, zeroExtend_bot]
  · rw [zeroExtend_of_ne _ hI]
    rfl

/-- Transporting along the identity field isomorphism is the identity. -/
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

/-- Evaluation of `mapEquiv`. -/
@[simp]
theorem mapEquiv_apply (e : K ≃+* L) (f : IdealArithmeticFunction K) :
    mapEquiv e f = map e f := (rfl)

/-- Evaluation of the inverse of `mapEquiv`. -/
@[simp]
theorem mapEquiv_symm_apply (e : K ≃+* L) (f : IdealArithmeticFunction L) :
    (mapEquiv e).symm f = map e.symm f := (rfl)

/-! Transport preserves the pointwise structure inherited from `Pi`. -/

/-- Transport preserves the pointwise zero function. -/
@[simp]
theorem map_zero (e : K ≃+* L) : map e (0 : IdealArithmeticFunction K) = 0 := by
  ext J
  simp

/-- Transport preserves the pointwise one function. -/
@[simp]
theorem map_one (e : K ≃+* L) : map e (1 : IdealArithmeticFunction K) = 1 := by
  ext J
  have hJ : Ideal.comap (RingOfIntegers.mapRingEquiv e) (J : Ideal (𝓞 L)) ≠ ⊥ := fun h ↦
    mem_nonZeroDivisors_iff_ne_zero.mp J.2 ((comap_mapRingEquiv_eq_bot_iff e).mp h)
  simp [hJ]

/-- Transport preserves pointwise addition. -/
@[simp]
theorem map_add (e : K ≃+* L) (f g : IdealArithmeticFunction K) :
    map e (f + g) = map e f + map e g := by
  ext J
  simp

/-- Transport preserves pointwise multiplication. -/
@[simp]
theorem map_mul (e : K ≃+* L) (f g : IdealArithmeticFunction K) :
    map e (f * g) = map e f * map e g := by
  ext J
  simp

/-- Transport preserves pointwise negation. -/
@[simp]
theorem map_neg (e : K ≃+* L) (f : IdealArithmeticFunction K) : map e (-f) = -map e f := by
  ext J
  simp

/-- Transport preserves pointwise subtraction. -/
@[simp]
theorem map_sub (e : K ≃+* L) (f g : IdealArithmeticFunction K) :
    map e (f - g) = map e f - map e g := by
  ext J
  simp

/-- Transport preserves pointwise complex scalar multiplication. -/
@[simp]
theorem map_smul (e : K ≃+* L) (c : ℂ) (f : IdealArithmeticFunction K) :
    map e (c • f) = c • map e f := by
  ext J
  simp

end Transport

end IdealArithmeticFunction

end TauCeti
