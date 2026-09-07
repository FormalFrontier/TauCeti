/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Irreducibility of the cyclotomic polynomial from the degree of a cyclotomic extension

Mathlib proves `[L : K] = φ n` for an `n`-th cyclotomic extension `L / K` once `Φ_n` is known to be
irreducible over `K` (`IsCyclotomicExtension.finrank`). This file records the converse: the degree
of `L / K` is always at most `φ n`, and as soon as it is at least `φ n` the polynomial `Φ_n` is
irreducible over `K`. That converse and Mathlib's forward direction give the equivalence
`IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient`.

The argument is the classical one. `L = K(ζ)` for a primitive `n`-th root of unity `ζ`, so `[L : K]`
is the degree of the minimal polynomial of `ζ` over `K`, and that minimal polynomial divides `Φ_n`;
hence `[L : K] ≤ φ n`, and if equality holds then `Φ_n` is a monic multiple of the minimal
polynomial of the same degree, so the two coincide and `Φ_n` is irreducible.

## Main results

* `IsCyclotomicExtension.finrank_le_totient`: `[L : K] ≤ φ n`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`: if `φ n ≤ [L : K]` then
  `Φ_n` is irreducible over `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient`: `Φ_n` is irreducible over
  `K` if and only if `[L : K] = φ n`.
* `IsCyclotomicExtension.card_aut_eq_sub_one`: a `q`-th cyclotomic extension with `Φ_q`
  irreducible has exactly `q - 1` automorphisms, for `q` prime.

## References

This is the degree bookkeeping of Milne, *Algebraic Number Theory*, proof of Proposition 6.2, and
of Sharifi, *Algebraic Number Theory*, proof of Lemma 3.1.13, where the base field is `ℚ`.
-/

public section

open Polynomial

namespace IsCyclotomicExtension

variable {n : ℕ} [NeZero n] (K : Type*) [Field K] (L : Type*) [CommRing L] [IsDomain L]
  [Algebra K L] [IsCyclotomicExtension {n} K L]

private theorem finrank_eq_natDegree_minpoly_zeta :
    Module.finrank K L = (minpoly K (zeta n K L)).natDegree := by
  -- `L = K(ζ)` has the power basis `1, ζ, …` of length `deg (minpoly K ζ)`.
  -- Source: Mathlib, proof of `IsCyclotomicExtension.finrank`.
  rw [((zeta_spec n K L).powerBasis K).finrank, IsPrimitiveRoot.powerBasis_dim]

private theorem minpoly_zeta_dvd_cyclotomic : minpoly K (zeta n K L) ∣ cyclotomic n K :=
  -- A primitive `n`-th root of unity is a root of `Φ_n`.
  -- Mathlib's `IsPrimitiveRoot.minpoly_dvd_cyclotomic` does not apply here: it is stated over
  -- `ℤ`, needs the root to lie in `K` itself, and assumes `[CharZero K]`.
  have : NeZero (n : L) := IsCyclotomicExtension.neZero n K L
  minpoly.dvd K _ (aeval_zeta n K L)

/-- **The degree of a cyclotomic extension is at most `φ n`.**

The bound is unconditional: nothing is assumed about `cyclotomic n K`. That is what separates it
from Mathlib's `IsCyclotomicExtension.finrank`, which gives the sharper `[L : K] = φ n` but only
under `Irreducible (cyclotomic n K)`. Reach for this one when that irreducibility is unknown, or
is itself what is being proved.

Source: Milne, *Algebraic Number Theory*, proof of Prop. 6.2 ("we know `[ℚ[ζ] : ℚ] ≤ φ(p^r)`");
Sharifi, *Algebraic Number Theory*, proof of Lemma 3.1.13 ("`[ℚ(µ_{p^r}) : ℚ] ≤ deg Φ_{p^r}`"). -/
theorem finrank_le_totient : Module.finrank K L ≤ n.totient :=
  calc
    Module.finrank K L = (minpoly K (zeta n K L)).natDegree :=
      finrank_eq_natDegree_minpoly_zeta K L
    _ ≤ (cyclotomic n K).natDegree :=
      natDegree_le_of_dvd (minpoly_zeta_dvd_cyclotomic K L) (cyclotomic_ne_zero n K)
    _ = n.totient := natDegree_cyclotomic n K

/-- **A cyclotomic extension of full degree has irreducible cyclotomic polynomial.** If
`φ n ≤ [L : K]` then the minimal polynomial of a primitive `n`-th root of unity, a monic divisor of
`Φ_n`, has degree `φ n`, so it is `Φ_n`, which is therefore irreducible.

Source: Milne, *Algebraic Number Theory*, proof of Prop. 6.2 ("(3.34) implies
`[ℚ[ζ] : ℚ] ≥ φ(p^r)`. This proves (a)"); Sharifi, proof of Lemma 3.1.13 ("which forces
`[ℚ(µ_{p^r}) : ℚ] = p^{r−1}(p − 1)`"). -/
theorem irreducible_cyclotomic_of_totient_le_finrank (h : n.totient ≤ Module.finrank K L) :
    Irreducible (cyclotomic n K) := by
  have hint : IsIntegral K (zeta n K L) := (integral {n} K L).isIntegral _
  have hdeg : (cyclotomic n K).natDegree ≤ (minpoly K (zeta n K L)).natDegree := by
    rwa [natDegree_cyclotomic, ← finrank_eq_natDegree_minpoly_zeta K L]
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic n K)
    (minpoly_zeta_dvd_cyclotomic K L) hdeg]
  exact minpoly.irreducible hint

/-- **`Φ_n` is irreducible over `K` exactly when the cyclotomic extension has degree `φ n`.** The
forward direction is Mathlib's `IsCyclotomicExtension.finrank`; the converse is
`irreducible_cyclotomic_of_totient_le_finrank`.

Source: as for the two lemmas it combines. -/
theorem irreducible_cyclotomic_iff_finrank_eq_totient :
    Irreducible (cyclotomic n K) ↔ Module.finrank K L = n.totient :=
  ⟨IsCyclotomicExtension.finrank L, fun h ↦ irreducible_cyclotomic_of_totient_le_finrank K L h.ge⟩

/-- **A `q`-th cyclotomic extension has exactly `q - 1` automorphisms**, for `q` prime with `Φ_q`
irreducible over `K`. The subtraction is truncated `ℕ` subtraction, which agrees with the totient
because `q` is prime. -/
theorem card_aut_eq_sub_one (q : ℕ) (F : Type*) [CommRing F] [IsDomain F] [Algebra K F]
    (hq : q.Prime) [IsCyclotomicExtension {q} K F] (hirr : Irreducible (cyclotomic q K)) :
    Nat.card (F ≃ₐ[K] F) = q - 1 := by
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Nat.card_congr (autEquivPow F hirr).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hq]

end IsCyclotomicExtension
