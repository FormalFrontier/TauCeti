/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.NumberTheory.Multiquadratic.Degree
public import TauCeti.NumberTheory.Multiquadratic.Galois.Basic

/-!
# The Galois group of a multiquadratic field is `(ℤ/2)ⁿ`

Over a field `K` in which `2 ≠ 0`, a multiquadratic field `M = K(rootᵢ : i)` (with
`rootᵢ ^ 2 = dᵢ ∈ K`) is Galois (`TauCeti.NumberTheory.Multiquadratic.Galois.Basic`). Each
automorphism sends every generator to `± rootᵢ`, so it is determined by a *sign pattern* `ι → ℤ/2`;
this assignment is an injective group homomorphism. When the radicands are square-class independent
the degree is `2ⁿ` (`TauCeti.NumberTheory.Multiquadratic.Degree`), so counting forces the
homomorphism to be an isomorphism: `Gal(M/K) ≃ (ℤ/2)ⁿ`.

## Main results

* `TauCeti.Multiquadratic.signHom`: the injective sign-pattern homomorphism `Gal(M/K) →* (ℤ/2)ⁿ`.
* `TauCeti.Multiquadratic.galoisGroupEquiv`: for square-class independent radicands, the explicit
  isomorphism `Gal(M/K) ≃* Multiplicative (ι → ℤ/2)`.
* `TauCeti.Multiquadratic.aut_nontrivial`: under square-class independence over a nonempty index
  type, `Gal(M/K)` is nontrivial.
* `TauCeti.Multiquadratic.card_aut_adjoin_range`: the cardinality reading
  `|Gal(M/K)| = 2^|ι|` of that isomorphism.

## Provenance

Generalised from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where the
sign-change automorphisms of one concrete multiquadratic field were analysed; here the
construction is carried out for an arbitrary such tower.
-/

public section

open Polynomial IntermediateField

attribute [local instance] Classical.propDecidable

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

variable (root) in
/-- The sign pattern of an automorphism: `0` where it fixes a generator and `1` otherwise.
When `gen root i ≠ -gen root i`, the `1` case says that the automorphism negates the generator. -/
@[expose] noncomputable def signPattern
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) : ZMod 2 :=
  if σ (gen root i) = gen root i then 0 else 1

/-- An automorphism acts on each generator by the corresponding sign. -/
theorem aut_gen_eq_signPattern (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    σ (gen root i) = (-1) ^ (signPattern root σ i).val * gen root i := by
  rw [signPattern]
  split_ifs with h
  · simp [h]
  · rcases aut_gen_eq_self_or_eq_neg hroot σ i with h' | h'
    · exact absurd h' h
    · -- here the sign is `1`; `(1 : ZMod 2).val = 1`, so `(-1) ^ 1 = -1` negates the generator.
      have hval : (1 : ZMod 2).val = 1 := rfl
      simp [h', hval]

/-- **Read the sign pattern off a generator-wise sign.** If `σ (gen root i) = ε • gen root i`
with `ε = ±1` (in `ℤ`) and `d i ≠ 0`, then `signPattern root σ i` is `0` when `ε = 1` and `1`
when `ε = -1`. This bridges a generator-wise sign — for instance a Frobenius acting on `√dᵢ` by
a Legendre symbol (`TauCeti.NumberField.isArithFrobAt_apply_sqrt`) — to the `(ℤ/2)ⁿ`
identification, so it composes with `TauCeti.Multiquadratic.galoisGroupEquiv_apply`. -/
theorem signPattern_eq_ite_of_zsmul_gen [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) {i : ι} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hd : d i ≠ 0) (hσ : σ (gen root i) = ε • gen root i) :
    signPattern root σ i = if ε = 1 then 0 else 1 := by
  rw [signPattern]
  rcases hε with rfl | rfl
  · rw [one_smul] at hσ; rw [if_pos hσ, if_pos rfl]
  · rw [neg_one_zsmul] at hσ
    rw [if_neg (fun h => gen_ne_neg hroot i hd (h.symm.trans hσ)),
      if_neg (by norm_num : (-1 : ℤ) ≠ 1)]

/-- Two automorphisms with the same sign pattern are equal. -/
theorem signPattern_injective (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    Function.Injective (signPattern (K := K) root) := by
  intro σ τ h
  refine AlgEquiv.coe_toAlgHom_injective
    (IntermediateField.algHom_ext_of_eq_adjoin (F := K)
      (S := adjoin K (Set.range root)) (s := Set.range root) rfl ?_)
  rintro x ⟨i, rfl⟩
  have hgen : σ (gen root i) = τ (gen root i) := by
    rw [aut_gen_eq_signPattern hroot, aut_gen_eq_signPattern hroot, h]
  exact hgen

/-- The sign is `0` exactly where the automorphism fixes the generator. -/
theorem signPattern_eq_zero
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (h : σ (gen root i) = gen root i) : signPattern root σ i = 0 := by
  simp [signPattern, h]

/-- The sign is `0` iff the automorphism fixes the generator. -/
@[simp] theorem signPattern_eq_zero_iff
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    signPattern root σ i = 0 ↔ σ (gen root i) = gen root i := by
  rw [signPattern]
  by_cases h : σ (gen root i) = gen root i <;> simp [h]

/-- The sign is `1` where the automorphism negates a generator that differs from its negation. -/
theorem signPattern_eq_one
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (hne : gen (K := K) root i ≠ -gen root i)
    (h : σ (gen root i) = -gen root i) : signPattern root σ i = 1 := by
  have hni : σ (gen root i) ≠ gen root i := fun hh => hne (h ▸ hh.symm)
  simp [signPattern, hni]

/-- The sign is `1` iff the automorphism negates a generator that differs from its negation. -/
@[simp]
theorem signPattern_eq_one_iff (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (hne : gen (K := K) root i ≠ -gen root i) :
    signPattern root σ i = 1 ↔ σ (gen root i) = -gen root i := by
  constructor
  · intro hsign
    rw [signPattern] at hsign
    split_ifs at hsign with hfix
    · exact (zero_ne_one hsign).elim
    · rcases aut_gen_eq_self_or_eq_neg hroot σ i with h | h
      · exact (hfix h).elim
      · exact h
  · exact signPattern_eq_one σ i hne

/-- The identity automorphism has the zero sign pattern. -/
@[simp] theorem signPattern_one : signPattern (K := K) root (1 : adjoin K (Set.range root) ≃ₐ[K]
    adjoin K (Set.range root)) = 0 := by
  funext i; exact signPattern_eq_zero _ _ rfl

private theorem signed_pow_add_mul (x : adjoin K (Set.range root)) (a b : ZMod 2) :
    (-1 : adjoin K (Set.range root)) ^ b.val * ((-1) ^ a.val * x)
      = (-1) ^ (a + b).val * x := by
  -- `(-1) ^ ·` is `2`-periodic, so it factors through `ZMod.val (a + b) = (a.val + b.val) % 2`.
  rw [← mul_assoc, ← pow_add, ZMod.val_add, neg_one_pow_eq_pow_mod_two (b.val + a.val),
    add_comm b.val a.val]

private theorem zmod_two_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

private theorem aut_mul_gen_eq_signPattern_add
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ τ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    (σ * τ) (gen root i)
      = (-1) ^ (signPattern root σ i + signPattern root τ i).val * gen root i := by
  rw [AlgEquiv.mul_apply, aut_gen_eq_signPattern hroot τ i, map_mul, map_pow, map_neg,
    map_one, aut_gen_eq_signPattern hroot σ i]
  exact signed_pow_add_mul (gen root i) (signPattern root σ i) (signPattern root τ i)

/-- Pointwise composition rule for sign patterns. -/
theorem signPattern_mul_apply (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ τ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    signPattern root (σ * τ) i = signPattern root σ i + signPattern root τ i := by
  by_cases hne : gen (K := K) root i ≠ -gen root i
  · have hmul := aut_mul_gen_eq_signPattern_add hroot σ τ i
    generalize hsum : signPattern root σ i + signPattern root τ i = s
    rcases zmod_two_eq_zero_or_one s with rfl | rfl
    · refine signPattern_eq_zero _ _ ?_
      rw [hmul, hsum, ZMod.val_zero, pow_zero, one_mul]
    · refine signPattern_eq_one _ _ hne ?_
      rw [hmul, hsum, ZMod.val_one, pow_one, neg_one_mul]
  · have hself : gen (K := K) root i = -gen root i := of_not_not hne
    have hsign : ∀ υ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root),
        signPattern root υ i = 0 := by
      intro υ
      rcases aut_gen_eq_self_or_eq_neg hroot υ i with h | h
      · exact signPattern_eq_zero _ _ h
      · exact signPattern_eq_zero _ _ (h.trans hself.symm)
    rw [hsign (σ * τ), hsign σ, hsign τ]
    -- All three signs are `0`, so the goal is `(0 : ZMod 2) = 0 + 0`.
    rfl

/-- The sign pattern is additive: it is a group homomorphism to `ι → ℤ/2`. -/
@[simp]
theorem signPattern_mul (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ τ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    signPattern root (σ * τ) = signPattern root σ + signPattern root τ := by
  funext i
  exact signPattern_mul_apply hroot σ τ i

variable (root) in
/-- The Galois group of `M / K` maps to the sign patterns `(ℤ/2)ⁱ`. -/
@[expose] noncomputable def signHom (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    : (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) →*
      Multiplicative (ι → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (signPattern root σ)
  map_one' := by simp
  map_mul' σ τ := by simp [signPattern_mul hroot, ofAdd_add]

/-- Evaluation rule for `signHom`: it is the multiplicative form of `signPattern`. -/
@[simp] theorem signHom_apply (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    -- Applying the bundled `MonoidHom` unfolds to its `toFun`, which is `ofAdd ∘ signPattern`.
    signHom root hroot σ = Multiplicative.ofAdd (signPattern root σ) := rfl

/-- The sign-pattern homomorphism is injective. -/
theorem signHom_injective (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    Function.Injective (signHom (K := K) root hroot) := by
  intro σ τ h
  exact signPattern_injective hroot (Multiplicative.ofAdd.injective (by simpa using h))

private theorem signHom_bijective [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Function.Bijective (signHom (K := K) root hroot) := by
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    IsSplittingField.finiteDimensional _ (definingPolynomial d)
  haveI := isGalois hroot
  letI := Fintype.ofFinite ι
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨signHom_injective hroot, ?_⟩
  rw [← Nat.card_eq_fintype_card (α := adjoin K (Set.range root) ≃ₐ[K] _),
    IsGalois.card_aut_eq_finrank K (adjoin K (Set.range root)),
    finrank_adjoin_range hroot hindep]
  simp [ZMod.card]

/-- **For square-class independent radicands, the Galois group of a multiquadratic field is
`(ℤ/2)ⁿ`.** -/
noncomputable def galoisGroupEquiv [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) ≃*
      Multiplicative (ι → ZMod 2) :=
  MulEquiv.ofBijective (signHom root hroot) (signHom_bijective hroot hindep)

/-- **A multiquadratic field over a nonempty family of independent radicands has a nontrivial Galois
group.** -/
theorem aut_nontrivial [Finite ι] [NeZero (2 : K)] [Nonempty ι]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Nontrivial (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :=
  (galoisGroupEquiv hroot hindep).toEquiv.nontrivial

/-- The Galois-group equivalence sends an automorphism to its multiplicative sign pattern. -/
@[simp] theorem galoisGroupEquiv_apply [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    galoisGroupEquiv hroot hindep σ = Multiplicative.ofAdd (signPattern root σ) := by
  rw [galoisGroupEquiv, MulEquiv.ofBijective_apply, signHom_apply]

/-- The inverse of `galoisGroupEquiv` realizes a sign pattern `ε` as the automorphism sending each
generator `rootᵢ` to `(-1)^(εᵢ) · rootᵢ`. -/
@[simp] theorem galoisGroupEquiv_symm_apply_gen [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε : ι → ZMod 2) (i : ι) :
    ((galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd ε)) (gen root i)
      = (-1) ^ (ε i).val * gen root i := by
  have hσ : signPattern root
      ((galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd ε)) = ε := by
    have happ := (galoisGroupEquiv hroot hindep).apply_symm_apply (Multiplicative.ofAdd ε)
    rw [galoisGroupEquiv_apply] at happ
    exact Multiplicative.ofAdd.injective happ
  rw [aut_gen_eq_signPattern hroot, hσ]

/-- **Cardinality of the Galois group of a multiquadratic field.** If no nonempty subset product
of the radicands `d i` is a square in `K` (and `2 ≠ 0` in `K`), then the multiquadratic field
`M = K(rootᵢ : i)` has `|Gal(M/K)| = 2^|ι|`. This is the cardinality reading of the explicit
isomorphism `galoisGroupEquiv`. -/
theorem card_aut_adjoin_range [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Nat.card (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) = 2 ^ Nat.card ι := by
  classical
  letI := Fintype.ofFinite ι
  rw [Nat.card_congr (galoisGroupEquiv hroot hindep).toEquiv,
    Nat.card_congr (Multiplicative.ofAdd (α := ι → ZMod 2)).symm,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp [ZMod.card]

end TauCeti.Multiquadratic
