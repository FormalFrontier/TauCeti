/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# Raising the base field: the tower formula for arithmetic Frobenius elements

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `L / M` Galois, let `Q` be a prime of `𝓞 L`
unramified over `𝓞 K`, and write `𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`. An arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q` acts on the residue field by `x ↦ x ^ 𝔑𝔭`, while an arithmetic Frobenius
`τ ∈ Gal(L/M)` at `Q` acts by `x ↦ x ^ 𝔑𝔓`. Since `𝔑𝔓 = 𝔑𝔭 ^ f(𝔓/𝔭)`, the two are related by

```text
τ = σ ^ f(𝔓/𝔭).
```

The exponent is a **power**, the residue degree of the intermediate prime over the base, and never
an inverse. In particular `σ ^ f(𝔓/𝔭)` fixes `M` pointwise even though `M / K` need not be normal
and `σ` itself need not preserve `M`.

This is the second of the two tower laws for Frobenius elements. The first, restriction along a
normal subextension, takes no power at all and is
`IsArithFrobAt.restrictNormal` in `TauCeti.NumberTheory.NumberField.Frobenius.Restriction`.

## The two hypotheses that are not decoration

The statement is *relative to one prime `Q` of `L`*. Replacing `σ` by an arbitrary conjugate — an
arbitrary representative of the Artin class of `𝔭` — makes it false when `M / K` is not normal: a
conjugate need not stabilize `Q`, so its `f`-th power need not fix `M` pointwise, and it is then
the restriction of no element of `Gal(L/M)` at all.

Unramifiedness of `Q` over `𝓞 K` is likewise essential. At a ramified prime a Frobenius lift is
determined only modulo inertia, so there is no equality of automorphisms to prove; the statement
would have to be made in the quotient by the inertia subgroup, or about a coset. Here
unramifiedness enters through `Ideal.eq_of_smul_sub_smul_mem_of_isUnramifiedAt`: the decomposition
group of `Q` embeds into the automorphism group of the residue extension, so an element of
`Gal(L/K)` stabilizing `Q` is pinned down by its residue action, and both `σ ^ f(𝔓/𝔭)` and the
restriction of `τ` act by `x ↦ x ^ 𝔑𝔓`.

## Main results

* `NumberField.restrictScalars_eq_pow_inertiaDeg`: an arithmetic Frobenius of `Gal(L/M)` at `Q`
  is the `f(𝔓/𝔭)`-th power of an arithmetic Frobenius of `Gal(L/K)` at `Q`.
* `NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg`: that power characterizes the
  relative Frobenius among the elements of `Gal(L/M)`.
* `NumberField.restrictScalars_arithFrobAt_eq_pow_inertiaDeg`: the same formula for Mathlib's
  coherently chosen `arithFrobAt`, which is what the Artin symbol is built from.
* `NumberField.exists_isArithFrobAt_pow_inertiaDeg`: the existence form of the tower formula,
  stated for prime ideals `𝔓` and `𝔭` presented by their defining equations.
* `NumberField.pow_inertiaDeg_apply_algebraMap`: the `f(𝔓/𝔭)`-th power of `σ` fixes `M`
  pointwise.
* `NumberField.restrictScalars_eq_of_inertiaDeg_eq_one`: at residue degree one the relative
  Frobenius is `σ` itself, with no power.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

public section

open Ideal

open scoped NumberField Pointwise

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L] {Q : Ideal (𝓞 L)} [Q.IsPrime]

/-- **Raising the base field raises the Frobenius to the residue degree.** For number fields
`K ⊆ M ⊆ L` with `L / K` and `L / M` Galois and `Q` a prime of `𝓞 L` unramified over `𝓞 K`, an
arithmetic Frobenius `τ ∈ Gal(L/M)` at `Q` is the `f(𝔓/𝔭)`-th power of an arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q`, where `𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`.

The exponent is the residue degree of `𝔓` over `𝓞 K`, and it is a power: the residue field of `𝔓`
has `𝔑𝔭 ^ f(𝔓/𝔭)` elements, so the two Frobenius elements have residue actions `x ↦ x ^ 𝔑𝔭` and
`x ↦ x ^ 𝔑𝔭 ^ f(𝔓/𝔭)`. Both sides are read inside `Gal(L/K)`, where `τ` is placed by
`AlgEquiv.restrictScalars`. -/
theorem restrictScalars_eq_pow_inertiaDeg [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    {τ : L ≃ₐ[M] L} (hτ : IsArithFrobAt (𝓞 M) τ Q) :
    AlgEquiv.restrictScalars K τ = σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) := by
  have _ : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hσ.ne_bot inferInstance
  have _ : (Q.under (𝓞 M)).IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal Q
  have _ : (Q.under (𝓞 K)).IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal Q
  have _ : (Q.under (𝓞 M)).LiesOver (Q.under (𝓞 K)) := ⟨by rw [Ideal.under_under]⟩
  -- The residue field of `𝔓` has `𝔑𝔭 ^ f(𝔓/𝔭)` elements.
  have hcard : Nat.card (𝓞 M ⧸ Q.under (𝓞 M)) =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) := by
    have := Ideal.cardQuot_pow_inertiaDeg (R := 𝓞 K) (S := 𝓞 M)
      (Q.under (𝓞 K)) (Q.under (𝓞 M))
    simpa [Submodule.cardQuot_apply] using this.symm
  refine Ideal.eq_of_smul_sub_smul_mem_of_isUnramifiedAt Q
    (τ := σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K)) hτ.mem_stabilizer
    (pow_mem hσ.mem_stabilizer _) fun x ↦ ?_
  have hres : Ideal.Quotient.mk Q (τ • x) =
      Ideal.Quotient.mk Q x ^ Nat.card (𝓞 M ⧸ Q.under (𝓞 M)) := hτ.mk_apply x
  rw [← Ideal.Quotient.eq, hσ.mk_pow_smul _ x]
  change Ideal.Quotient.mk Q (τ • x) = _
  rw [hres, hcard]

/-- **The relative Frobenius is exactly that power.** An element of `Gal(L/M)` is an arithmetic
Frobenius at `Q` precisely when it is the `f(𝔓/𝔭)`-th power of a fixed arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q`.

The converse direction is uniqueness rather than a second computation: a Frobenius of `Gal(L/M)`
at `Q` exists, is carried to `σ ^ f(𝔓/𝔭)` by `restrictScalars_eq_pow_inertiaDeg`, and
`AlgEquiv.restrictScalars` is injective. -/
theorem isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg [IsGalois M L]
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) (τ : L ≃ₐ[M] L) :
    IsArithFrobAt (𝓞 M) τ Q ↔
      AlgEquiv.restrictScalars K τ = σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) := by
  refine ⟨restrictScalars_eq_pow_inertiaDeg hσ, fun h ↦ ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_isArithFrobAt M Q hσ.ne_bot
  have : τ = τ₀ := AlgEquiv.restrictScalars_injective K
    (h.trans (restrictScalars_eq_pow_inertiaDeg hσ hτ₀).symm)
  exact this ▸ hτ₀

/-- **The tower formula for Mathlib's chosen Frobenius.** Mathlib's `arithFrobAt` picks a
Frobenius coherently across the fibre above a prime of the base; at an unramified `Q` the choices
over `𝓞 K` and over `𝓞 M` are related by the tower formula, because at such a `Q` there is
nothing left to choose.

This is the form the Artin symbol is built from, `NumberField.artinSymbol` being the conjugacy
class of `arithFrobAt (𝓞 K) (L ≃ₐ[K] L)` at a prime above `𝔭`. -/
theorem restrictScalars_arithFrobAt_eq_pow_inertiaDeg [IsGalois M L] (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Finite (𝓞 L ⧸ Q)] [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    AlgEquiv.restrictScalars K (arithFrobAt (𝓞 M) (L ≃ₐ[M] L) Q) =
      arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) :=
  restrictScalars_eq_pow_inertiaDeg (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q)
    (IsArithFrobAt.arithFrobAt (𝓞 M) (L ≃ₐ[M] L) Q)

/-- **The tower formula, in the form the Artin symbol consumes.** For number fields `K ⊆ M ⊆ L`
with `L / K` and `L / M` Galois, a prime `Q` of `𝓞 L` with `𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`, and
`𝔭` unramified in `L`, every arithmetic Frobenius `σ ∈ Gal(L/K)` at `Q` has `σ ^ f(𝔓/𝔭)` as the
image in `Gal(L/K)` of an arithmetic Frobenius at `Q` in `Gal(L/M)`.

The unramifiedness hypothesis is phrased for all primes above `𝔭`, matching the argument that
`NumberField.artinSymbol` takes; only its value at `Q` is used. -/
theorem exists_isArithFrobAt_pow_inertiaDeg [IsGalois M L] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (𝔓 : Ideal (𝓞 M)) (𝔭 : Ideal (𝓞 K))
    (hQM : Q.under (𝓞 M) = 𝔓) (hQK : Q.under (𝓞 K) = 𝔭)
    (hur : ∀ (Q' : Ideal (𝓞 L)) [Q'.IsPrime] [Q'.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q')
    (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    ∃ τ : L ≃ₐ[M] L, IsArithFrobAt (𝓞 M) τ Q ∧
      AlgEquiv.restrictScalars K τ = σ ^ 𝔓.inertiaDeg (𝓞 K) := by
  subst hQM
  subst hQK
  have _ : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  obtain ⟨τ, hτ⟩ := exists_isArithFrobAt M Q hσ.ne_bot
  exact ⟨τ, hτ, restrictScalars_eq_pow_inertiaDeg hσ hτ⟩

/-- **The power of the Frobenius fixes the intermediate field.** Even though `M / K` need not be
normal, and `σ` therefore need not preserve `M`, its `f(𝔓/𝔭)`-th power fixes `M` pointwise: it is
the image of an element of `Gal(L/M)`. -/
theorem pow_inertiaDeg_apply_algebraMap [IsGalois M L] [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) (y : M) :
    (σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K)) (algebraMap M L y) = algebraMap M L y := by
  obtain ⟨τ, hτ⟩ := exists_isArithFrobAt M Q hσ.ne_bot
  rw [← restrictScalars_eq_pow_inertiaDeg hσ hτ]
  exact τ.commutes y

/-- **At residue degree one the Frobenius does not move.** If `𝔓 = Q ∩ 𝓞 M` has residue degree one
over `𝓞 K`, then an arithmetic Frobenius of `Gal(L/M)` at `Q` is the arithmetic Frobenius of
`Gal(L/K)` at `Q` itself, on the nose.

This is the case a fixed-field fibre count runs through: it contracts the primes of `M` whose
residue degree over `K` is one, exactly so that the relative Frobenius is the absolute one. -/
theorem restrictScalars_eq_of_inertiaDeg_eq_one [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    {τ : L ≃ₐ[M] L} (hτ : IsArithFrobAt (𝓞 M) τ Q)
    (hf : (Q.under (𝓞 M)).inertiaDeg (𝓞 K) = 1) :
    AlgEquiv.restrictScalars K τ = σ := by
  rw [restrictScalars_eq_pow_inertiaDeg hσ hτ, hf, pow_one]

end NumberField
