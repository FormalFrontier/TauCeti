/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import TauCeti.NumberTheory.Cyclotomic.Irreducible
public import TauCeti.NumberTheory.RamificationInertia.NumberField

/-!
# Unramifiedness makes the cyclotomic polynomial irreducible over a number field

Let `K` be a number field and `p` a prime that is unramified in `K`. Then the cyclotomic polynomial
`Φ_{p^(k+1)}` is irreducible over `K` for every `k`; in particular `Φ_p` is, so
`[K(ζ_p) : K] = p - 1`. For the Galois group itself, feed that irreducibility to Mathlib's
`IsCyclotomicExtension.autEquivPow`, which yields `Gal(K(ζ_p)/K) ≃* (ZMod p)ˣ`; this file proves
irreducibility and the ramification behind it, and does not restate that consequence.

The mechanism is ramification, not an intersection of fields. Let `F / K` be a `p^(k+1)`-th
cyclotomic extension and `𝔔` a prime of `𝓞 F` above `p`. Inside `F` the subfield `ℚ(ζ)` is the
`p^(k+1)`-th cyclotomic field over `ℚ`, in which `p` is totally ramified with index
`φ(p^(k+1))`; ramification indices multiply in towers, so `e(𝔔 / p) ≥ φ(p^(k+1))`. On the other
hand `e(𝔔 / p) = e(𝔔 / 𝔮) · e(𝔮 / p)` with `𝔮 = 𝔔 ∩ 𝓞 K`, and `e(𝔮 / p) = 1` because `p` is
unramified in `K`. Hence `e(𝔔 / 𝔮) ≥ φ(p^(k+1))`, while `e(𝔔 / 𝔮) ≤ [F : K]`. So
`[F : K] ≥ φ(p^(k+1))`, which is irreducibility of `Φ_{p^(k+1)}` over `K` by
`IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`.

The intersection `L ⊓ K(ζ_p) = ⊥` for an extension `L / K` gives none of this: it constrains `L`,
whereas `[K(ζ_p) : K]` is a proper divisor of `p - 1` exactly when `K ∩ ℚ(ζ_p) ≠ ℚ`. The witness
`K = ℚ(√5)`, `p = 5` is `Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five`.

## Main results

* `IsPrimitiveRoot.totient_le_ramificationIdx`: a primitive `p^(k+1)`-th root of unity in a
  number field `F` forces `φ(p^(k+1)) ≤ e(𝔔 ∣ ℤ)` for every prime `𝔔` of `𝓞 F` above `p`.
* `IsCyclotomicExtension.totient_le_finrank_of_unramified`: `φ(p^(k+1)) ≤ [F : K]` when `p` is
  unramified in `K`.
* `IsCyclotomicExtension.ramificationIdx_eq_totient`: every prime of `𝓞 F` above `p` has
  ramification index exactly `φ(p^(k+1))` over `𝓞 K`, so `F / K` is totally ramified there.
* `IsCyclotomicExtension.inf_eq_bot_prime_pow_of_unramified`: for intermediate fields `A` and `B`
  of `Ω / K` with `B` a `p^(k+1)`-th cyclotomic extension, `p` unramified in `A` gives
  `A ⊓ B = ⊥`.
* `IsCyclotomicExtension.inf_eq_bot_of_unramified`: the prime case.
* `IsCyclotomicExtension.irreducible_cyclotomic_prime_pow_of_unramified`: `Φ_{p^(k+1)}` is
  irreducible over `K` when `p` is unramified in `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_unramified`: the prime case.

## References

Unramifiedness, rather than an intersection of fields, is what gives the full cyclotomic degree.

Total ramification of `ℚ(ζ_{p^r})` at `p` is Milne, *Algebraic Number Theory*, Proposition 6.2,
and Sharifi, *Algebraic Number Theory*, Lemma 3.1.13; the ramification bookkeeping is Sharifi,
Remark 2.5.7 and Theorem 2.5.11. The argument mirrors
`TauCeti.Multiquadratic.ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime`.

The tower and discriminant bookkeeping was mined from the private declarations
`prime_dvd_natAbs_discr_cyclotomic_dvd` and `cyclotomicField_finrank_eq` in
`CebotarevDensity/Abelian.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states those
through coprimality to the discriminant; the results here are restated through unramifiedness.
-/

public section

open Polynomial
open scoped NumberField


namespace IsCyclotomicExtension

variable {K : Type*} [Field K] [NumberField K]

/-- **A primitive `p^(k+1)`-th root of unity forces ramification at least `φ(p^(k+1))` above
`p`.** For any number field `F` containing such a root, every prime of `𝓞 F` above `p` has
ramification index at least `φ(p^(k+1))` over `ℤ`.

No cyclotomic-extension hypothesis is needed: the root alone pins `ℚ(ζ)` inside `F`, and `p` is
totally ramified there.

Source: Milne, *Algebraic Number Theory*, Proposition 6.2(c); Sharifi, Lemma 3.1.13. -/
theorem _root_.IsPrimitiveRoot.totient_le_ramificationIdx {p k : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime]
    [𝔔.LiesOver (Ideal.span {(p : ℤ)})] : (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx ℤ := by
  -- `p` is totally ramified in `ℚ(ζ)`: Milne, Prop. 6.2(c) (`(p) = (π)^e` with `e = φ(p^r)`);
  -- Sharifi, Lemma 3.1.13 ("It is totally ramified").
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  -- Indices multiply in towers: Sharifi, Remark 2.5.7 ("`e_{P/p} = e_{P/𝔓} e_{𝔓/p}`").
  have h := (𝔔.under (𝓞 (IntermediateField.adjoin ℚ {ζ}))).ramificationIdx_below_le (R := ℤ) 𝔔
  rwa [Rat.ramificationIdx_eq_of_prime_pow p k, ← Nat.totient_prime_pow_succ Fact.out] at h

private theorem totient_le_ramificationIdx (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
    Algebra.IsUnramifiedAt ℤ 𝔮) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx (𝓞 K) := by
  -- First tower `ℤ ⊆ 𝓞 ℚ(ζ) ⊆ 𝓞 F`, through a primitive root: `e(𝔔 / p) ≥ φ(p^(k+1))`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (S := {p ^ (k + 1)}) K F
    (Set.mem_singleton _) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  -- Second tower `ℤ ⊆ 𝓞 K ⊆ 𝓞 F`: indices multiply (Sharifi, Remark 2.5.7) and `e(𝔮 / p) = 1`
  -- because `p` is unramified in `K`, so `e(𝔔 / p) = e(𝔔 / 𝔮)`.
  simpa only [Ideal.ramificationIdx_tower (R := ℤ) (𝔔.under (𝓞 K)) 𝔔,
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (R := ℤ) hur
      (𝔓 := 𝔔.under (𝓞 K)) inferInstance, one_mul] using
    hζ.totient_le_ramificationIdx 𝔔

/-- **The degree of a cyclotomic extension above an unramified prime is at least `φ(p^(k+1))`.**
Unlike `IsPrimitiveRoot.lcm_totient_le_finrank` it assumes no irreducibility, so it can feed
`irreducible_cyclotomic_of_totient_le_finrank` rather than follow from it.

Source: Sharifi, Theorem 2.5.11 (`∑ eᵢ fᵢ = [L : K]`); Milne, Theorem 3.34. -/
theorem totient_le_finrank_of_unramified (p k : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : (p ^ (k + 1)).totient ≤ Module.finrank K F := by
  have : FiniteDimensional K F := finiteDimensional {p ^ (k + 1)} K F
  have : NumberField F := .of_module_finite K F
  -- A prime of `𝓞 F` above `p`: Sharifi, Thm 2.5.11 (`pB = P₁^{e₁} ⋯ P_g^{e_g}` with `g ≥ 1`).
  obtain ⟨𝔔, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)})
    (S := 𝓞 F)
  -- `𝔔` has relative ramification index at least `φ(p^(k+1))` over `𝓞 K`, and a ramification
  -- index never exceeds the degree of the extension.
  exact (totient_le_ramificationIdx p k hur 𝔔).trans 𝔔.ramificationIdx_le_finrank_numberField

/-- **A cyclotomic extension is totally ramified above an unramified prime.** If `p` is unramified
in `K`, every prime `𝔔` of `𝓞 F` above `p` has ramification index exactly `φ(p^(k+1))` over
`𝓞 K` — which by `totient_le_finrank_of_unramified` is the full degree `[F : K]`, so there is a
single prime above `p` and it is totally ramified.

The three bounds `φ ≤ e(𝔔) ≤ [F : K] ≤ φ` collapse to equalities: the first is the tower
computation, the second the fundamental identity `∑ eᵢ fᵢ = [F : K]`, and the third holds for any
cyclotomic extension. This is the form the intersection argument consumes, where the lower bound
alone is not enough.

Source: Sharifi, *Algebraic Number Theory*, Theorem 2.5.11; Milne, Theorem 3.34. -/
theorem ramificationIdx_eq_totient (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
    Algebra.IsUnramifiedAt ℤ 𝔮) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime]
    [𝔔.LiesOver (Ideal.span {(p : ℤ)})] : 𝔔.ramificationIdx (𝓞 K) = (p ^ (k + 1)).totient := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : FiniteDimensional K F := finiteDimensional {p ^ (k + 1)} K F
  have : NumberField F := .of_module_finite K F
  exact le_antisymm (𝔔.ramificationIdx_le_finrank_numberField.trans (finrank_le_totient K F))
    (totient_le_ramificationIdx p k hur 𝔔)

/-- **A cyclotomic extension of full degree meets an unramified extension trivially.** For `A` and
`B` intermediate fields of `Ω / K` with `B` a `p^(k+1)`-th cyclotomic extension of full degree
`φ(p^(k+1))`, if `p` is unramified in `A` then `A ⊓ B = ⊥`.

`B / K` is totally ramified above `p` by `ramificationIdx_eq_totient`, while `A`, and hence
`A ⊓ B`, is unramified there; multiplicativity in the tower hands the whole of `φ(p^(k+1))` to
`B / (A ⊓ B)`, and a ramification index never exceeds a degree, so `A ⊓ B` has degree one
over `K`.

The degree `[B : K] = φ(p^(k+1))` is **derived, not assumed**: unramifiedness already pins the
ramification index at `φ(p^(k+1))` via `ramificationIdx_eq_totient`, and a ramification index never
exceeds the degree while a cyclotomic degree never exceeds `φ`, so the two bounds meet. Requiring
the degree as a hypothesis would have been redundant, and would have pushed onto every caller a
fact this theorem's own hypotheses already give.

This stays independent of `irreducible_cyclotomic_prime_pow_of_unramified` below: the degree comes
from the ramification count, not from irreducibility of `Φ_{p^(k+1)}`, so there is no circularity.
Specialised to `K = ℚ` it says a number field unramified at `p` meets `ℚ(ζ_{p^(k+1)})` trivially;
specialised to a general base it is the corresponding statement about `L ∩ K(ζ_{p^(k+1)})`. -/
theorem inf_eq_bot_prime_pow_of_unramified {Ω : Type*} [Field Ω] [Algebra K Ω]
    (p k : ℕ) [Fact p.Prime] (A B : IntermediateField K Ω) [NumberField A] [NumberField B]
    [IsCyclotomicExtension {p ^ (k + 1)} K B]
    (hur : ∀ (P : Ideal (𝓞 A)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ P) :
    A ⊓ B = ⊥ := by
  set E := (A ⊓ B : IntermediateField K Ω) with hE
  have hEA : E ≤ A := inf_le_left
  have hEB : E ≤ B := inf_le_right
  have : Module.Finite K E := Module.Finite.of_injective
    (IntermediateField.inclusion hEA).toLinearMap (IntermediateField.inclusion hEA).injective
  have : NumberField E := .of_module_finite K _
  let : Algebra E B := (IntermediateField.inclusion hEB).toAlgebra
  let : IsScalarTower K E B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨𝔔, h𝔔max, h𝔔lo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (Ideal.span {(p : ℤ)}) (S := 𝓞 B)
  have := h𝔔max
  have := h𝔔lo
  have hurK : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮 := fun 𝔮 ↦
    TauCeti.RamificationInertia.isUnramifiedAt_of_forall_isUnramifiedAt hur 𝔮
  have htot : 𝔔.ramificationIdx (𝓞 K) = (p ^ (k + 1)).totient :=
    ramificationIdx_eq_totient (K := K) p k hurK 𝔔
  -- The degree is squeezed between the same two bounds that pinned the ramification index.
  have hBK : Module.finrank K B = (p ^ (k + 1)).totient :=
    le_antisymm (finrank_le_totient K B) (htot ▸ 𝔔.ramificationIdx_le_finrank_numberField)
  have : Algebra.IsUnramifiedAt ℤ (𝔔.under (𝓞 E)) :=
    TauCeti.RamificationInertia.isUnramifiedAt_of_forall_isUnramifiedAt hur _
  have : Algebra.IsUnramifiedAt (𝓞 K) (𝔔.under (𝓞 E)) := .of_restrictScalars ℤ _
  have he1 : (𝔔.under (𝓞 E)).ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (𝔔.under (𝓞 E)) 𝔔
  have he2 : 𝔔.ramificationIdx (𝓞 E) = (p ^ (k + 1)).totient := by
    rw [htot, he1, one_mul] at htower; exact htower.symm
  exact IntermediateField.finrank_eq_one_iff.mp
    (TauCeti.NumberField.finrank_eq_one_of_ramificationIdx_eq_finrank 𝔔 he2 hBK)

/-- The prime case of `inf_eq_bot_prime_pow_of_unramified`, at `k = 0`. This is the form the
roadmap's Layer 7.2 step 2 and Layer 7.3 both use. -/
theorem inf_eq_bot_of_unramified {Ω : Type*} [Field Ω] [Algebra K Ω]
    (q : ℕ) (hq : q.Prime) (A B : IntermediateField K Ω) [NumberField A] [NumberField B]
    [IsCyclotomicExtension {q} K B]
    (hur : ∀ (P : Ideal (𝓞 A)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ P) :
    A ⊓ B = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have : IsCyclotomicExtension {q ^ (0 + 1)} K B := by simpa using ‹IsCyclotomicExtension {q} K B›
  exact inf_eq_bot_prime_pow_of_unramified q 0 A B hur


variable (K) in
/-- **Unramifiedness gives irreducibility of `Φ_{p^(k+1)}`.** If the prime `p` is unramified in the
number field `K`, then the `p^(k+1)`-th cyclotomic polynomial is irreducible over `K`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, so a proof
of that predicate can be passed directly; the bundled `Algebra.Unramified ℤ (𝓞 K)` is far stronger,
and forces `Module.finrank ℚ K = 1` by `NumberField.finrank_eq_one_of_unramified`, hence a
`ℚ`-algebra isomorphism `K ≃ₐ[ℚ] ℚ` rather than equality of types. Unramifiedness is sufficient but
not necessary: irreducibility holds exactly when `K ∩ ℚ(ζ_{p^(k+1)}) = ℚ`. For `k = 0` see
`irreducible_cyclotomic_of_unramified`.

Source: Milne, Prop. 6.2 and Sharifi, Lemma 3.1.13 for the base `ℚ`. -/
theorem irreducible_cyclotomic_prime_pow_of_unramified (p k : ℕ) [Fact p.Prime]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : Irreducible (cyclotomic (p ^ (k + 1)) K) :=
  -- `p` unramified in `K` forces the canonical `p^(k+1)`-th cyclotomic extension of `K` to have
  -- degree at least `φ(p^(k+1))`, the full degree of `Φ_{p^(k+1)}`.
  irreducible_cyclotomic_of_totient_le_finrank K (CyclotomicField (p ^ (k + 1)) K) <|
    totient_le_finrank_of_unramified p k _ hur

variable (K) in
/-- **Unramifiedness gives irreducibility of `Φ_q`.** If the prime `q` is unramified in the number
field `K`, then the `q`-th cyclotomic polynomial is irreducible over `K`, hence
`[K(ζ_q) : K] = q - 1`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})`, so a proof
of that predicate can be passed directly. `L ⊓ K(ζ_q) = ⊥` is no substitute: it constrains `L`, not
`K ∩ ℚ(ζ_q)`, which is what irreducibility is equivalent to. See
`Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five` for the witness.

Source: the case `k = 0` of `irreducible_cyclotomic_prime_pow_of_unramified`. -/
theorem irreducible_cyclotomic_of_unramified (q : ℕ) (hq : q.Prime)
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : Irreducible (cyclotomic q K) := by
  -- The case `k = 0` of the prime-power result, where `q ^ (0 + 1)` reduces to `q`.
  have : Fact q.Prime := ⟨hq⟩
  simpa using irreducible_cyclotomic_prime_pow_of_unramified K q 0 hur

end IsCyclotomicExtension

