/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import TauCeti.RingTheory.DedekindDomain.RamificationLocus

/-!
# The primes of a number field ramifying in a finite extension

For an extension `L / K` of number fields, a height-one prime `𝔭` of `𝓞 K` is *ramified in `L`*
when some prime `Q` of `𝓞 L` lying over it is ramified, i.e. when

`¬ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q`.

Only finitely many `𝔭` are ramified, because each of them is the contraction of a prime dividing
the different ideal `differentIdeal (𝓞 K) (𝓞 L)`, which is nonzero and so has finitely many prime
divisors. That finiteness is what lets the ramified primes be packaged as a `Finset`, which is the
form Chebotarev's exceptional set is used in: the density statements discard `ramifiedPrimes K L`
and argue about the complement.

The ramification condition is spelled out with Mathlib's `Algebra.IsUnramifiedAt` rather than
wrapped in a named predicate, matching how the roadmap states it. A `Prop`-valued abbreviation for
"`𝔭` is unramified in `L`" would duplicate `Algebra.IsUnramifiedIn`.

## Main definitions

* `NumberField.Chebotarev.ramifiedPrimes`: the finite set of height-one primes of `𝓞 K` that
  ramify in `L`.

## Main results

* `NumberField.Chebotarev.mem_ramifiedPrimes_iff`: the defining condition for membership.

## Relation to the absolute `NumberField.ramifiedPrimes`

Every name used here already exists one namespace up, and this is deliberate rather than an
oversight. `TauCeti/NumberTheory/NumberField/RamifiedPrimes.lean` carries

* `NumberField.ramifiedPrimes (K) : Set ℕ`, the *rational* primes ramifying in `K`,
* `@[simp] NumberField.mem_ramifiedPrimes_iff`, proved by `Iff.rfl`, and
* `NumberField.finite_ramifiedPrimes`,

i.e. the same short names, in the same shape. They are kept apart rather than unified:

* They are the same *shape* — "not `Algebra.IsUnramifiedIn` the top ring at an ideal of the base"
  — but at different bases. The absolute one is `ℤ`-to-`𝓞 K`; this one is `𝓞 K`-to-`𝓞 L`. Neither
  is an instance of the other without also transporting the carrier.
* The carriers genuinely differ: `Set ℕ` against `Finset (HeightOneSpectrum (𝓞 K))`. For `K = ℚ`
  the two agree only through `𝓞 ℚ ≃ ℤ` and `HeightOneSpectrum ℤ ≃` the rational primes, and
  neither identification is definitional.
* Generalising the absolute version instead would change its carrier, and Tau Ceti keeps no
  compatibility shims, so every use would have to move in this PR — ten files on `main` reference
  that API, seven of them under `Multiquadratic/`. Its `Set ℕ` packaging is, in its own docstring,
  "the form in which `t` is counted" for genus theory.

Two consequences to be aware of when using this file. First, `NumberField.Chebotarev` is nested
inside `NumberField`, so within it a bare `ramifiedPrimes` or `mem_ramifiedPrimes_iff` resolves to
the declaration here and shadows the absolute one; a `Chebotarev` file that also wants the
absolute notion must write `_root_.NumberField.ramifiedPrimes`. (The finiteness lemma is private,
so its name collides only inside this file.) Second, both `_iff` lemmas are
`@[simp]`, but their left-hand sides head-match on different types — membership in a `Set ℕ`
against membership in a `Finset (HeightOneSpectrum (𝓞 K))` — so `simp` never has to choose
between them.

## References

Adapted from `finite_ramifiedIn` in `CebotarevDensity/Frobenius.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, where the statement is a
`Set.Finite` over `Ideal (𝓞 K)` phrased through a source-local unramifiedness predicate. The
covering argument through the different ideal is the source's; the carrier is the roadmap's.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Only finitely many primes of `K` ramify in `L`.** Each ramified `𝔭` is the contraction of a
ramified prime of `𝓞 L`, and there are finitely many of those.

Private, and stated for the underlying `Set` rather than for `ramifiedPrimes` itself, because its
only role is to *build* that `Finset`; consumers take finiteness from the `Finset` and membership
from `mem_ramifiedPrimes_iff`. The absolute analogue `_root_.NumberField.finite_ramifiedPrimes`
runs the other way round, its `ramifiedPrimes` being a `Set` that the lemma then cuts down. -/
private theorem finite_ramifiedPrimes : {𝔭 : HeightOneSpectrum (𝓞 K) |
    ¬ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q}.Finite := by
  -- `asIdeal` is injective, so it suffices to bound the image of the set in `Ideal (𝓞 K)`.
  refine Set.Finite.of_finite_image ?_ HeightOneSpectrum.asIdeal_injective.injOn
  -- Each ramified `𝔭` is the contraction of a ramified prime of `𝓞 L`, and the ramification
  -- locus of `𝓞 L` over `𝓞 K` is finite.
  refine Set.Finite.subset ((Algebra.finite_compl_unramifiedLocus (𝓞 K) (𝓞 L)).image
    (fun Q : PrimeSpectrum (𝓞 L) ↦ Q.asIdeal.under (𝓞 K))) ?_
  rintro _ ⟨𝔭, h𝔭, rfl⟩
  simp only [Set.mem_ofPred_eq, not_forall] at h𝔭
  obtain ⟨Q, hQp, hQlo, hQnu⟩ := h𝔭
  exact ⟨⟨Q, hQp⟩, hQnu, hQlo.over.symm⟩

/-- **The primes of `K` that ramify in `L`.** The height-one primes `𝔭` of `𝓞 K` for which some
prime of `𝓞 L` over `𝔭` is ramified, collected into a `Finset` by `finite_ramifiedPrimes`.

This is the relative notion; `_root_.NumberField.ramifiedPrimes` is the absolute one, over `ℤ`
and valued in `Set ℕ`. See the module docstring. -/
noncomputable def ramifiedPrimes : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_ramifiedPrimes K L).toFinset

variable {K L}

/-- The defining condition for membership in `ramifiedPrimes`. -/
@[simp]
theorem mem_ramifiedPrimes_iff (𝔭 : HeightOneSpectrum (𝓞 K)) : 𝔭 ∈ ramifiedPrimes K L ↔
    ¬ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q :=
  Set.Finite.mem_toFinset _

end NumberField.Chebotarev
