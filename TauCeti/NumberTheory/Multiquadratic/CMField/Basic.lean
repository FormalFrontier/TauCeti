/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Radicands
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Finset.Option

/-!
# Multiquadratic CM fields

A multiquadratic *CM* field is one of the form `ℚ(i, √p₁, …, √pₙ)`: a totally imaginary
multiquadratic field obtained by adjoining `√(-1)` together with the square roots of distinct
primes. The roadmap's worked example asks to recover the field
`ℚ(i, √q₀, …, √q_{g-1})` of the Erdős unit-distance formalization as a multiquadratic field of
degree `2^{g+1}`; this file supplies exactly that degree.

The single new ingredient over the prime-radicand theory is the radicand `-1`. Square-class
independence is preserved when one **negative** radicand is adjoined to a square-class
independent family of **positive** radicands: a nonempty subset product either avoids the
negative radicand (and is a positive non-square by hypothesis) or includes it exactly once
(and is then negative, hence not a square in an ordered field). This is recorded field-generically
in `not_isSquare_prod_optionNeg`, and the CM degree is the corollary for `K = ℚ` indexed by
`Option ι`.

## Main results

* `TauCeti.Multiquadratic.not_isSquare_prod_optionNeg`: adjoining a negative radicand to a
  positive square-class independent family preserves square-class independence — stated over an
  arbitrary ordered field for the `Option`-indexed family.
* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_primes`: `[ℚ(i, √p₁, …, √pₙ) : ℚ] = 2^{|ι|+1}`
  for a finite family of distinct primes — the multiquadratic CM degree.
* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_two`: `[ℚ(i, √2) : ℚ] = 4`, the smallest
  nontrivial multiquadratic CM degree.
* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_five`: `[ℚ(i, √5) : ℚ] = 4`, the
  roadmap-facing CM degree example for `ℚ(√-5)`.

## Provenance

The CM degree `finrank_adjoin_I_sqrt_primes` parallels `Kf_finrank` (for the field `Kf`) in
`ErdosUnitDistance/MultiquadraticField.lean` in
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, which computes
`[ℚ(i, √q₀, …, √q_{g-1}) : ℚ] = 2^{g+1}` for one concrete CM field. The negative-radicand argument
here is original and independent of that source: rather than adjoining `i` as a separate quadratic
step over the real subfield (the route taken there), it treats `i = √(-1)` as one more radicand and
proves the square-class combinator `not_isSquare_prod_optionNeg` over an arbitrary ordered field,
then feeds the already-migrated `finrank_adjoin_range`.
-/

public section

open scoped Function

namespace TauCeti.Multiquadratic

/-- **Adjoining a negative radicand preserves square-class independence.** Let `d : ι → K` be a
family of positive radicands in an ordered field, no nonempty subset product of which is a
square, and let `c < 0`. Index by `Option ι`, sending `none` to `c` and `some i` to `d i`. Then
no nonempty subset product of this extended family is a square: a subset that avoids `none` is a
nonempty positive non-square by hypothesis, and a subset that contains `none` has a negative
product (the negative `c` times a positive product), so it is not a square either. -/
theorem not_isSquare_prod_optionNeg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {ι : Type*} {d : ι → K} (hpos : ∀ i, 0 < d i)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    {c : K} (hc : c < 0) (S : Finset (Option ι)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ x ∈ S, x.elim c d) := by
  classical
  -- The product over the `some` part of any `T` is the corresponding product of the `d i`.
  have hbase : ∀ T : Finset (Option ι),
      ∏ x ∈ T.erase none, x.elim c d = ∏ i ∈ T.eraseNone, d i := by
    intro T
    conv_lhs => rw [← Finset.image_some_eraseNone T]
    rw [Finset.prod_image (fun a _ b _ h => Option.some_injective _ h)]
    simp
  by_cases hnone : none ∈ S
  · -- The product is `c` times a positive product, hence negative.
    have hsplit : ∏ x ∈ S, x.elim c d = c * ∏ i ∈ S.eraseNone, d i := by
      rw [← Finset.mul_prod_erase S (fun x => x.elim c d) hnone, hbase S]
      simp
    rw [hsplit]
    exact not_isSquare_of_neg
      (mul_neg_of_neg_of_pos hc (Finset.prod_pos fun i _ => hpos i))
  · -- The product avoids `none`, so it is a nonempty positive subset product of the `d i`.
    have heq : ∏ x ∈ S, x.elim c d = ∏ i ∈ S.eraseNone, d i := by
      conv_lhs => rw [← Finset.erase_eq_of_notMem hnone]
      exact hbase S
    rw [heq]
    refine hindep S.eraseNone ?_
    obtain ⟨x, hx⟩ := hS
    cases x with
    | none => exact absurd hx hnone
    | some i => exact ⟨i, Finset.mem_eraseNone.mpr hx⟩

section CMFamily

variable {ι : Type*} (p : ι → ℕ)

/-- The `Option ι`-indexed radicand family of a multiquadratic CM field: `none ↦ -1` (for `i`)
and `some i ↦ p i` (for `√(p i)`). -/
@[expose] def cmRadicand : Option ι → ℚ := fun x => x.elim (-1) (fun i => (p i : ℚ))

/-- The `Option ι`-indexed generator family of a multiquadratic CM field: `none ↦ i` and
`some i ↦ √(p i)` (as a complex number). -/
@[expose] noncomputable def cmRoot : Option ι → ℂ :=
  fun x => x.elim Complex.I (fun i => ((Real.sqrt (p i) : ℝ) : ℂ))

@[simp] theorem cmRadicand_none : cmRadicand p none = -1 := rfl

@[simp] theorem cmRadicand_some (i : ι) : cmRadicand p (some i) = (p i : ℚ) := rfl

@[simp] theorem cmRoot_none : cmRoot p none = Complex.I := rfl

@[simp] theorem cmRoot_some (i : ι) : cmRoot p (some i) = ((Real.sqrt (p i) : ℝ) : ℂ) := rfl

/-- The generator family squares to the radicand family: `i² = -1` and `√(p i)² = p i`. This is
the `hroot` hypothesis the field-generic multiquadratic results consume. -/
theorem cmRoot_sq (x : Option ι) : cmRoot p x ^ 2 = algebraMap ℚ ℂ (cmRadicand p x) := by
  cases x with
  | none => simp [cmRoot, cmRadicand, Complex.I_sq]
  | some i =>
      simp only [cmRoot, cmRadicand, Option.elim_some]
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast,
        map_natCast]

/-- The range of the CM generator family is the inserted generator set: `i` together with the
real square roots `√(p i)`. This identifies `adjoin ℚ (Set.range (cmRoot p))` with the named
field `ℚ(i, √p₁, …, √pₙ)`. -/
theorem range_cmRoot :
    Set.range (cmRoot p)
      = insert Complex.I (Set.range fun i => ((Real.sqrt (p i) : ℝ) : ℂ)) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some i, rfl⟩

/-- The CM radicand family is square-class independent: for distinct primes `p`, no nonempty
subset product of `-1, p₁, …, pₙ` is a square in `ℚ`. -/
theorem not_isSquare_prod_cmRadicand (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Option ι)) (hS : S.Nonempty) : ¬ IsSquare (∏ x ∈ S, cmRadicand p x) := by
  have h := not_isSquare_prod_optionNeg (K := ℚ) (d := fun i => (p i : ℚ))
    (fun i => by exact_mod_cast (hp i).pos)
    (not_isSquare_prod_primes_of_injective p hp hinj) (c := -1) (by norm_num) S hS
  exact h

end CMFamily

/-- **Degree of a multiquadratic CM field.** For a finite family of distinct primes `p : ι → ℕ`,
the field `ℚ(i, √p₁, …, √pₙ)` generated over `ℚ` by `i` and the real square roots of the `p i`
has degree `2^{|ι|+1}`. This recovers the Erdős CM field `ℚ(i, √q₀, …, √q_{g-1})` as a
multiquadratic field, the worked example of the roadmap. -/
theorem finrank_adjoin_I_sqrt_primes {ι : Type*} [Finite ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Module.finrank ℚ
        (IntermediateField.adjoin ℚ
          (insert Complex.I (Set.range fun i => ((Real.sqrt (p i) : ℝ) : ℂ))))
      = 2 ^ (Nat.card ι + 1) := by
  have hcard : Nat.card (Option ι) = Nat.card ι + 1 := by
    let := Fintype.ofFinite ι
    simp [Nat.card_eq_fintype_card, Fintype.card_option]
  have hkey := finrank_adjoin_range (d := cmRadicand p) (root := cmRoot p)
    (cmRoot_sq p) (not_isSquare_prod_cmRadicand p hp hinj)
  rw [range_cmRoot p, hcard] at hkey
  exact hkey

/-- **Worked example: `[ℚ(i, √2) : ℚ] = 4`.** The smallest nontrivial multiquadratic CM degree,
obtained from `finrank_adjoin_I_sqrt_primes` with the single prime `2`. -/
theorem finrank_adjoin_I_sqrt_two :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Complex.I, ((Real.sqrt 2 : ℝ) : ℂ)} : Set ℂ)) = 4 := by
  have h := finrank_adjoin_I_sqrt_primes ![2] (by decide) (by decide)
  have hset : insert Complex.I
      (Set.range fun i : Fin 1 => ((Real.sqrt ((![2] : Fin 1 → ℕ) i) : ℝ) : ℂ))
      = ({Complex.I, ((Real.sqrt 2 : ℝ) : ℂ)} : Set ℂ) := by
    rw [Set.range_unique]
    simp [Matrix.cons_val_fin_one]
  rw [hset] at h
  rw [h, Nat.card_fin]
  norm_num

/-- **Worked example: `[ℚ(i, √5) : ℚ] = 4`.** This is the Layer-0 degree statement for the
multiquadratic field generated by the prime-discriminant radicands `-1` and `5`, the
genus-field generator list for `ℚ(√-5)`. -/
theorem finrank_adjoin_I_sqrt_five :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ)) = 4 := by
  have h := finrank_adjoin_I_sqrt_primes ![5] (by decide) (by decide)
  have hset : insert Complex.I
      (Set.range fun i : Fin 1 => ((Real.sqrt ((![5] : Fin 1 → ℕ) i) : ℝ) : ℂ))
      = ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ) := by
    rw [Set.range_unique]
    simp [Matrix.cons_val_fin_one]
  rw [hset] at h
  rw [h, Nat.card_fin]
  norm_num

end TauCeti.Multiquadratic
