/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.AlgHom
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Ramification
public import TauCeti.NumberTheory.Multiquadratic.Unramified.Basic
public import TauCeti.NumberTheory.Multiquadratic.Unramified.Subfields
import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Subfactorization

/-!
# Maximality of the candidate genus field

Let `d` be a squarefree integer that is not a rational square, let `M / ℚ` be an abelian number
field extension, and let `y ∈ M` be a square root of `d` generating a quadratic subfield
`F = ℚ(√d)` of `M`. If `M / F` is unramified at every finite prime, then `M` embeds over `ℚ` into
the candidate genus field `candidateGenusField hd`. Since that field is itself such an extension —
it is abelian over `ℚ`, contains a square root of `d`, and is unramified over `ℚ(√d)` at every
finite prime — this makes it the *largest* one, which is the maximality half of the genus-field
characterisation.

The proof combines three inputs, one field-theoretic and two arithmetic.

* `exists_squarefree_root_adjoin_range_eq_top_of_isUnramifiedIn_over_quadratic` presents `M` as
  `ℚ(√a₁, …, √aₙ)` for square-class independent squarefree integers `aᵢ`.
* `dvd_fundamentalDiscriminant_base_of_dvd_subfield` and
  `not_dvd_fundamentalDiscriminant_mul_of_dvd_subfield` constrain each `aᵢ`: every prime ramifying
  in `ℚ(√aᵢ)` ramifies in `ℚ(√d)`, and none of them ramifies in `ℚ(√(aᵢ d))`.
* `subset_of_forall_prime_dvd_fundamentalDiscriminant` turns those two constraints into the
  statement that the prime-discriminant factorization of `fundamentalDiscriminant aᵢ` is a *subset*
  of the chosen factorization `genusPrimeDiscriminants hd`, whence `√aᵢ` lies in the compositum.

An `aᵢ` in the square class of `d` is not covered by the second constraint — there `ℚ(√(aᵢ d)) = ℚ`
— and is handled separately, by scaling the square root of `d` that the candidate genus field
already contains.

Once every generator has a square root inside `candidateGenusField hd`, any embedding
`M →ₐ[ℚ] ℂ` sends the generators to `±` those square roots, hence lands inside the candidate genus
field; comparing degrees gives `[M : ℚ] ≤ 2 ^ t` with `t` the number of primes ramifying in
`ℚ(√d)`.

This is the classical maximality argument for the genus field; see D. A. Cox, *Primes of the Form
x² + ny²*, §6.A, and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main results

In the namespace `TauCeti.Multiquadratic`:

* `exists_mem_candidateGenusField_sq_eq_intCast`: a quadratic subfield `ℚ(√a)` of such an `M` has
  its square root inside the candidate genus field.
* `nonempty_algHom_candidateGenusField`: `M` embeds over `ℚ` into the candidate genus field.
* `finrank_le_finrank_candidateGenusField`: hence `[M : ℚ] ≤ [K_gen : ℚ]`, and
  `finrank_le_two_pow_card_genusPrimeDiscriminants` reads that bound off as `2 ^ t`.
* `nonempty_algEquiv_candidateGenusField`: an extension attaining the bound is `ℚ`-isomorphic to
  the candidate genus field.
* `exists_isUnramifiedIn_and_finrank_eq_two_pow_card`: the candidate genus field is itself such an
  extension, so the bound is attained and the uniqueness statement is not vacuous.
-/

public section

open IntermediateField NumberField

open scoped NumberField

namespace TauCeti.Multiquadratic

/-- **A subset of the chosen prime discriminants generates a square root inside the candidate genus
field.** If the prime discriminants in `u ⊆ genusPrimeDiscriminants hd` have product
`fundamentalDiscriminant a`, then `candidateGenusField hd` contains an element squaring to `a`. -/
theorem exists_mem_candidateGenusField_sq_eq_intCast_of_subset {d a : ℤ} (hd : Squarefree d)
    {u : Finset ℤ} (huprod : ∏ P ∈ u, P = fundamentalDiscriminant a)
    (hsub : u ⊆ genusPrimeDiscriminants hd) :
    ∃ z ∈ candidateGenusField hd, z ^ 2 = ((a : ℤ) : ℂ) := by
  have hu : ∀ P ∈ u, IsPrimeDiscriminant P := fun P hP =>
    (genusPrimeDiscriminants_spec hd).1 P (hsub hP)
  obtain ⟨z, hzmem, hz⟩ := exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq hu huprod
    (L := ℂ) (fun P => genusFieldRoot hd ⟨P.val, hsub P.property⟩) fun P => by simp
  refine ⟨z, adjoin_le_iff.mpr ?_ hzmem, ?_⟩
  · rintro _ ⟨P, rfl⟩
    exact genusFieldRoot_mem_candidateGenusField hd _
  · rw [hz]; simp

variable {M : Type*} [Field M] [NumberField M]

private theorem finrank_adjoin_sq_eq_intCast {d : ℤ}
    (hnsqd : ¬ IsSquare ((d : ℤ) : ℚ)) {y : M} (hy : y ^ 2 = algebraMap ℤ M d) :
    Module.finrank ℚ (adjoin ℚ {y} : IntermediateField ℚ M) = 2 := by
  have hy_sq_mem : y ^ 2 ∈ (⊥ : IntermediateField ℚ M) := by
    rw [hy, IsScalarTower.algebraMap_apply ℤ ℚ M]
    exact IntermediateField.algebraMap_mem _ _
  have hyQ : y ^ 2 = algebraMap ℚ M ((d : ℤ) : ℚ) := by
    rw [hy, IsScalarTower.algebraMap_apply ℤ ℚ M]
    norm_num
  have hy_not_mem : y ∉ (⊥ : IntermediateField ℚ M) := by
    intro hy_mem
    rw [IntermediateField.mem_bot] at hy_mem
    obtain ⟨r, hr⟩ := hy_mem
    apply hnsqd
    refine ⟨r, ?_⟩
    apply (algebraMap ℚ M).injective
    simpa only [map_mul, hr, pow_two] using hyQ.symm
  have hdeg := TauCeti.IntermediateField.finrank_sup_adjoin_simple_eq_mul_two
    (⊥ : IntermediateField ℚ M) hy_sq_mem hy_not_mem
  rw [bot_sup_eq] at hdeg
  simpa using hdeg

section IsGalois

variable [IsGalois ℚ M]

/-- **A quadratic subfield of an unramified Galois extension lies in the candidate genus field.**
Let `M / ℚ` be Galois, let `y ∈ M` be a square root of a squarefree non-square `d` generating a
quadratic subfield, and assume `M` is unramified over that subfield at every finite prime. Then for
every squarefree non-square `a` with a square root in `M`, the candidate genus field
`candidateGenusField hd` contains an element squaring to `a`.

This is the arithmetic core of maximality: the discriminant of `ℚ(√a)` is a *subproduct* of the
prime-discriminant factorization of the discriminant of `ℚ(√d)`. -/
theorem exists_mem_candidateGenusField_sq_eq_intCast {d a : ℤ} (hd : Squarefree d)
    (hnsqd : ¬ IsSquare ((d : ℤ) : ℚ)) (hsfa : Squarefree a) (hnsqa : ¬ IsSquare ((a : ℤ) : ℚ))
    {x y : M} (hx : x ^ 2 = algebraMap ℤ M a) (hy : y ^ 2 = algebraMap ℤ M d)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q) :
    ∃ z ∈ candidateGenusField hd, z ^ 2 = ((a : ℤ) : ℂ) := by
  have hdQ : ((d : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne_zero
  by_cases hsq : IsSquare (((a * d : ℤ)) : ℚ)
  · -- `a` and `d` are in the same square class: rescale the square root of `d`.
    obtain ⟨r, hr⟩ := hsq
    obtain ⟨w, hwmem, hw⟩ := exists_mem_candidateGenusField_sq_eq hd
    have hkey : (r / ((d : ℤ) : ℚ)) ^ 2 * ((d : ℤ) : ℚ) = ((a : ℤ) : ℚ) := by
      rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hdQ)]
      push_cast at hr ⊢
      linear_combination (-(d : ℚ)) * hr
    refine ⟨algebraMap ℚ ℂ (r / ((d : ℤ) : ℚ)) * w,
      mul_mem (IntermediateField.algebraMap_mem _ _) hwmem, ?_⟩
    rw [mul_pow, hw, ← map_pow, ← map_mul, hkey]
    simp
  · -- Otherwise the two ramification constraints apply, and cut `u` down to a subset.
    obtain ⟨c, e, hsfc, he, hce⟩ :=
      Int.exists_squarefree_mul_sq (mul_ne_zero hsfa.ne_zero hd.ne_zero)
    have hnsqc : ¬ IsSquare ((c : ℤ) : ℚ) := fun h => hsq <| by
      have hcast : ((a * d : ℤ) : ℚ) = ((c : ℤ) : ℚ) * ((e : ℤ) : ℚ) ^ 2 := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℚ)) hce
      exact hcast ▸ (isSquare_mul_sq_iff (Int.cast_ne_zero.mpr he)).mpr h
    obtain ⟨u, hu, hue, huprod⟩ :=
      (isFundamentalDiscriminant_fundamentalDiscriminant hsfa).exists_finset_primeDiscriminant
    obtain ⟨hs, hse, hsprod⟩ := genusPrimeDiscriminants_spec hd
    refine exists_mem_candidateGenusField_sq_eq_intCast_of_subset hd huprod
      (subset_of_forall_prime_dvd_fundamentalDiscriminant hs hse hsprod hu hue huprod hce
        (fun p hp hpa => dvd_fundamentalDiscriminant_base_of_dvd_subfield hsfa hnsqa hd hnsqd hx hy
          hunr hp hpa) fun h2 => ?_)
    have hdeg := finrank_adjoin_sq_eq_intCast hnsqd hy
    have h := not_dvd_fundamentalDiscriminant_mul_of_dvd_subfield hsfa hnsqa hsfc hnsqc hx hy
      hdeg hunr he hce (p := 2) Nat.prime_two (by exact_mod_cast h2)
    exact_mod_cast h

end IsGalois

section IsAbelianGalois

variable [IsAbelianGalois ℚ M]

/-- **Maximality of the candidate genus field.** Let `M / ℚ` be an abelian number-field extension
containing a square root `y` of a squarefree non-square `d` that generates a quadratic subfield, and
suppose `M` is unramified over that subfield at every finite prime. Then `M` admits a `ℚ`-embedding
into `candidateGenusField hd`.

Together with the facts that `candidateGenusField hd` is itself abelian over `ℚ`, contains a square
root of `d`, and is unramified over `ℚ(√d)` at every finite prime, this says it is the largest such
extension — the maximality half of the genus-field characterisation. -/
theorem nonempty_algHom_candidateGenusField {d : ℤ} (hd : Squarefree d)
    (hnsqd : ¬ IsSquare ((d : ℤ) : ℚ)) {y : M} (hy : y ^ 2 = algebraMap ℤ M d)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q) :
    Nonempty (M →ₐ[ℚ] candidateGenusField hd) := by
  have hdeg := finrank_adjoin_sq_eq_intCast hnsqd hy
  obtain ⟨n, a, root, hsf, hroot, hindep, htop, -⟩ :=
    exists_squarefree_root_adjoin_range_eq_top_of_isUnramifiedIn_over_quadratic
      (adjoin ℚ {y} : IntermediateField ℚ M) hdeg hunr
  have key : ∀ i, ∃ z ∈ candidateGenusField hd, z ^ 2 = ((a i : ℤ) : ℂ) := fun i => by
    have hnsqa : ¬ IsSquare ((a i : ℤ) : ℚ) := by
      rw [Rat.isSquare_intCast_iff]
      simpa using hindep {i} ⟨i, Finset.mem_singleton_self i⟩
    have hxi : root i ^ 2 = algebraMap ℤ M (a i) := by
      rw [hroot i, IsScalarTower.algebraMap_apply ℤ ℚ M]
      norm_num
    exact exists_mem_candidateGenusField_sq_eq_intCast hd hnsqd (hsf i) hnsqa hxi hy hunr
  choose z hzmem hzsq using key
  set φ : M →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hle : adjoin ℚ (Set.range root) ≤ (candidateGenusField hd).comap φ := by
    rw [adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have hsqeq : φ (root i) ^ 2 = z i ^ 2 := by
      rw [← map_pow, hroot i, AlgHom.commutes, hzsq i]
      simp
    apply (Subalgebra.mem_comap (candidateGenusField hd).toSubalgebra φ (root i)).mpr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq with h | h
    · rw [h]; exact hzmem i
    · rw [h]; exact neg_mem (hzmem i)
  refine ⟨φ.codRestrict (candidateGenusField hd).toSubalgebra fun m => ?_⟩
  exact hle (by rw [htop]; exact IntermediateField.mem_top)

/-- **The degree bound from maximality.** Under the hypotheses of
`nonempty_algHom_candidateGenusField`, the degree of `M` over `ℚ` is at most the degree of the
candidate genus field. -/
theorem finrank_le_finrank_candidateGenusField {d : ℤ} (hd : Squarefree d)
    (hnsqd : ¬ IsSquare ((d : ℤ) : ℚ)) {y : M} (hy : y ^ 2 = algebraMap ℤ M d)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q) :
    Module.finrank ℚ M ≤ Module.finrank ℚ (candidateGenusField hd) := by
  obtain ⟨φ⟩ := nonempty_algHom_candidateGenusField hd hnsqd hy hunr
  exact LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap)
    fun _ _ h => φ.toRingHom.injective h

/-- **`[M : ℚ] ≤ 2 ^ t`.** An abelian extension of `ℚ` that is unramified at every finite prime
over its quadratic subfield `ℚ(√d)` has degree at most `2 ^ t`, where `t` is the number of prime
discriminants dividing `fundamentalDiscriminant d` — equivalently, by
`card_genusPrimeDiscriminants_eq_ncard_ramifiedPrimes`, the number of rational primes ramifying in
`ℚ(√d)`. The bound is attained by the candidate genus field itself. -/
theorem finrank_le_two_pow_card_genusPrimeDiscriminants {d : ℤ} (hd : Squarefree d)
    (hnsqd : ¬ IsSquare ((d : ℤ) : ℚ)) {y : M} (hy : y ^ 2 = algebraMap ℤ M d)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q) :
    Module.finrank ℚ M ≤ 2 ^ (genusPrimeDiscriminants hd).card :=
  (finrank_le_finrank_candidateGenusField hd hnsqd hy hunr).trans
    (finrank_candidateGenusField hd).le

/-- **Uniqueness at the maximal degree.** An abelian extension of `ℚ` that is unramified at every
finite prime over its quadratic subfield `ℚ(√d)` and attains the maximal degree `2 ^ t` is
`ℚ`-isomorphic to the candidate genus field: the embedding of
`nonempty_algHom_candidateGenusField` is then forced to be onto. -/
theorem nonempty_algEquiv_candidateGenusField {d : ℤ} (hd : Squarefree d)
    (hnsqd : ¬ IsSquare ((d : ℤ) : ℚ)) {y : M} (hy : y ^ 2 = algebraMap ℤ M d)
    (hunr : ∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ M)), q.IsPrime → q ≠ ⊥ →
      Algebra.IsUnramifiedIn (𝓞 M) q)
    (hfr : Module.finrank ℚ M = 2 ^ (genusPrimeDiscriminants hd).card) :
    Nonempty (M ≃ₐ[ℚ] candidateGenusField hd) := by
  obtain ⟨φ⟩ := nonempty_algHom_candidateGenusField hd hnsqd hy hunr
  have hrank : Module.finrank ℚ M = Module.finrank ℚ (candidateGenusField hd) := by
    rw [hfr, finrank_candidateGenusField hd]
  exact ⟨TauCeti.algEquivOfFinrankEq φ hrank⟩

end IsAbelianGalois

/-- **The maximality bound is attained.** The candidate genus field of `ℚ(√d)` is itself an
abelian extension of `ℚ` of the kind the bound governs: its chosen square root of `d` generates a
quadratic subfield over which it is unramified at every finite prime, and its degree over `ℚ` is
exactly `2 ^ t`. So the bound `finrank_le_two_pow_card_genusPrimeDiscriminants` is sharp, and
`nonempty_algEquiv_candidateGenusField` applies to a nonempty class of extensions. -/
theorem exists_isUnramifiedIn_and_finrank_eq_two_pow_card {d : ℤ} (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    ∃ y : candidateGenusField hd,
      y ^ 2 = algebraMap ℤ (candidateGenusField hd) d ∧
        Module.finrank ℚ (adjoin ℚ {y} : IntermediateField ℚ (candidateGenusField hd)) = 2 ∧
        (∀ q : Ideal (𝓞 (adjoin ℚ {y} : IntermediateField ℚ (candidateGenusField hd))),
            q.IsPrime → q ≠ ⊥ → Algebra.IsUnramifiedIn (𝓞 (candidateGenusField hd)) q) ∧
        Module.finrank ℚ (candidateGenusField hd) = 2 ^ (genusPrimeDiscriminants hd).card := by
  refine ⟨candidateGenusFieldBaseRoot hd, ?_, ?_, ?_, finrank_candidateGenusField hd⟩
  · rw [candidateGenusFieldBaseRoot_sq hd, IsScalarTower.algebraMap_apply ℤ ℚ]
    norm_num
  · rw [← candidateGenusFieldBase_def hd]
    exact finrank_candidateGenusFieldBase hd hnsq
  · rw [← candidateGenusFieldBase_def hd]
    exact fun q hq _ => isUnramifiedIn_candidateGenusField hd hnsq q

end TauCeti.Multiquadratic
