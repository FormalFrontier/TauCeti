/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# The arithmetic Frobenius on roots of unity

Let `K` be a number field, `F` an extension field of `K`, `𝔭` a height-one prime of `𝓞 K`, and
`Q` an ideal of `𝓞 F` lying over `𝔭`. An *arithmetic Frobenius* at `Q` is a `σ` with
`σ x ≡ x ^ 𝔑𝔭 (mod Q)` for every `x : 𝓞 F` (Mathlib's `IsArithFrobAt`). This file records what
such a `σ` does to a root of unity: if `ζ` is an `m`-th root of unity in `F` and `𝔭` does not
divide `m`, then

`σ ζ = ζ ^ 𝔑𝔭`.

Over `ℚ` this reads `ζ_m ↦ ζ_m ^ p`, so the cyclotomic character sends the Frobenius at `p` to
`p mod m`. The exponent is `𝔑𝔭` itself and not `𝔑𝔭⁻¹`: the inverse describes the *geometric*
Frobenius, and using it would reverse the arithmetic progression a character reads off.

Some hypothesis relating `m` to `𝔭` is genuinely necessary rather than an artifact of the proof.
In the intended setting `F = K(μ_m)`, taking `μ_m ⊆ K` collapses `F` to `K`, making every `σ` the
identity; the formula would then force `𝔑𝔭 ≡ 1 (mod m)` for every prime. Here the hypothesis is
`(m : 𝓞 K) ∉ 𝔭.asIdeal`, that is `𝔭 ∤ m`, imposed at the base prime where a caller can check
it rather than at `Q`.

## Main results

* `AlgHom.IsArithFrobAt.apply_eq_pow_absNorm_of_pow_eq_one`: an arithmetic Frobenius at an ideal
  of `𝓞 F` over `𝔭` raises an `m`-th root of unity to the power `𝔑𝔭`, when `𝔭 ∤ m`.

## Implementation notes

The statement takes an element `σ` together with `IsArithFrobAt (𝓞 K) σ Q` rather than a chosen
Frobenius. It therefore applies to every arithmetic Frobenius at `Q`, needs no finiteness of the
residue ring `𝓞 F ⧸ Q` (which a chosen Frobenius needs in order to exist), and lets a consumer
supply whichever representative it holds.

`ζ` is asked only for `ζ ^ m = 1`, not for `IsPrimitiveRoot ζ m`. Primitivity plays no part: the
underlying `IsArithFrobAt.apply_of_pow_eq_one` is itself stated for any root of unity, and a
caller holding `hζ : IsPrimitiveRoot ζ m` passes `hζ.pow_eq_one`. Nor is `[NeZero m]` assumed —
`hm` already forces `m ≠ 0`, since every ideal contains `0`. Being a root of unity is also what
makes `ζ` an algebraic integer here (`IsIntegral.of_pow`), so no cyclotomic structure is needed to
package it into `𝓞 F`.

The statement uses the monoid-action `IsArithFrobAt`, whose head symbol unfolds to
`AlgHom.IsArithFrobAt`; the theorem lives in that namespace so a caller can write
`hσ.apply_eq_pow_absNorm_of_pow_eq_one`, matching Mathlib's own `apply_of_pow_eq_one`. Inside
that namespace the bare name `IsArithFrobAt` would resolve to the two-argument `AlgHom` form,
so the hypothesis names the monoid-action abbrev as `_root_.IsArithFrobAt`.

There is likewise no cyclotomic hypothesis on `F / K`. `IsCyclotomicExtension {m} K F` is the
ambient setting in which the result gets used, but the proof never looks at it, so assuming it
would leave an unused hypothesis on the statement. For the same reason `F` is not assumed to be a
number field: only `K` has to be one, so that `𝔭` has an absolute norm. And `Q`, which in use is a
prime above `𝔭`, is only required to lie over it: `IsArithFrobAt` reads as a congruence modulo `Q`
for any ideal, and nothing below needs `Q` to be prime.

## References

Adapted from `cyclotomic_frobenius_acts_as_norm_power` in
`CebotarevDensity/CyclotomicNormResidue.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, where the result is stated
over a source-local unramifiedness predicate and a chosen Frobenius. The mathematics is Sharifi,
*Algebraic Number Theory*, Proposition 7.2.1 step (i), p. 142.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace AlgHom.IsArithFrobAt

open NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]

/-- **An arithmetic Frobenius raises a root of unity to the norm of the prime below it.** Let `ζ`
be an `m`-th root of unity in an extension field `F` of a number field `K`, let `𝔭` be a
height-one prime of `𝓞 K` not dividing `m`, and let `σ` be an arithmetic Frobenius at an ideal
`Q` of `𝓞 F` lying over `𝔭`.
Then `σ ζ = ζ ^ 𝔑𝔭`.

The exponent is the absolute norm of `𝔭`, not its inverse: over `ℚ` this is `ζ_m ↦ ζ_m ^ p`. -/
theorem apply_eq_pow_absNorm_of_pow_eq_one {m : ℕ} {ζ : F} (hζ : ζ ^ m = 1)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (Q : Ideal (𝓞 F)) [Q.LiesOver 𝔭.asIdeal]
    {σ : F ≃ₐ[K] F} (hσ : _root_.IsArithFrobAt (𝓞 K) σ Q) :
    σ ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := by
  -- `m ≠ 0`: otherwise `(m : 𝓞 K)` is `0`, which lies in every ideal.
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ hm (by simp [h])
  -- A root of unity is an algebraic integer: `ζ ^ m` is `1`, which is integral, and `m > 0`.
  have hζmem : ζ ∈ integralClosure ℤ F :=
    IsIntegral.of_pow hm0 (by rw [hζ]; exact isIntegral_one)
  -- `𝔭` is the contraction of `Q`, so `𝔭 ∤ m` says exactly that `m` avoids `Q`.
  have hmQ : (m : 𝓞 F) ∉ Q := fun hmem ↦
    hm ((Ideal.mem_of_liesOver Q 𝔭.asIdeal (m : 𝓞 K)).mpr (by rwa [map_natCast]))
  -- The residue cardinality that `IsArithFrobAt` powers by is the absolute norm of `𝔭`.
  have hcard : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm 𝔭.asIdeal := by
    rw [← Q.over_def 𝔭.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  -- Name the algebraic integer carrying `ζ`, so the rewrites below see an opaque element.
  obtain ⟨z, hval⟩ : ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = ζ :=
    ⟨⟨ζ, hζmem⟩, RingOfIntegers.map_mk ζ hζmem⟩
  have hpow : z ^ m = 1 := RingOfIntegers.ext (by simp only [map_pow, hval, map_one]; exact hζ)
  -- Compute in `𝓞 F` on that integer, then push the identity down to `F`.
  have key := hσ.apply_of_pow_eq_one hpow hmQ
  rw [hcard] at key
  have hact : algebraMap (𝓞 F) F (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 F) σ z) = σ ζ := by
    rw [MulSemiringAction.toAlgHom_apply, algebraMap_smul_eq_apply, hval]
  -- The two sides of `key` map to the two sides of the goal.
  have hmap := congrArg (algebraMap (𝓞 F) F) key
  rwa [map_pow, hval, hact] at hmap

end AlgHom.IsArithFrobAt
