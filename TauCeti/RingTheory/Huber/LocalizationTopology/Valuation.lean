/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.RingTheory.Huber.LocalizationTopology.Plus
public import TauCeti.RingTheory.Valuation.Continuous.Basic
public import TauCeti.RingTheory.Valuation.ExtendToLocalization

/-!
# Extending a valuation to Wedhorn's topological localisation

Roadmap Layer 3.1 attaches to a rational subset `U = R(T/s)` of `X = Spa(A, A⁺)` a coordinate
ring together with its ring of integral elements, and asks for a natural homeomorphism

```text
Spa (A_U, A_U⁺) ≃ U.
```

The map from left to right is built in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Basic`; the map in the other direction has
to *produce* a point of an adic spectrum out of a point of `U`, and this file is its algebraic
core, before any completion.

Mathlib's `Valuation.extendToLocalization`, specialised to the away submonoid in
`TauCeti.RingTheory.Valuation.ExtendToLocalization`, already extends a valuation `v` with
`v s ≠ 0` from `A` to a localisation `Aₛ` away from `s`. What has to be proved is that the
extension satisfies the two conditions defining a point of `Spa (Aₛ, Aₛ⁺)`:

* it is **continuous** for the localisation topology of Wedhorn's Proposition and
  Definition 5.51 — `TauCeti.Huber.PairOfDefinition.locTopology`; and
* it is **bounded by `1`** on the integral closure of `A⁺[T/s]`, the plus ring that
  `TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_integralClosure_adjoin_plus` makes a
  ring of integral elements of `Aₛ`.

Both use `v t ≤ v s` for every numerator and `v s ≠ 0`. Continuity additionally requires `v` to
be continuous and `v ≤ 1` on the chosen ring of definition `A₀`; sub-unitness on the plus ring
additionally requires `v ≤ 1` on `A⁺`. For a point of `Spa(A, A⁺)`, continuity and the bound on
`A⁺` are part of membership, while a choice `A₀ ⊆ A⁺` supplies the remaining bound.

## Why continuity needs a bound on the ring of definition

The neighbourhoods of zero in `Aₛ` are the images of the powers `Jⁿ` of `J = I · D`, where
`D = A₀[t₁/s, …, tₙ/s]`. That is an ideal *of `D`*, so a bound on `v` over `Iⁿ` alone says
nothing about it: a general element is a `D`-combination of images from `Iⁿ`, and the `D`-factor
has to be harmless. So `isContinuous_extendToLocalization` asks for `v ≤ 1` on `A₀`, which
together with `v t ≤ v s` puts the whole of `D` inside the valuation ring of the extension
(`PairOfDefinition.extendToLocalization_le_one_of_mem_locSubring`).

That hypothesis is **not automatic** for a continuous valuation. Give `ℚ` the discrete topology:
it is a Huber ring with ring of definition `ℚ` and ideal of definition `0`, every valuation on it
is continuous (`Valuation.isContinuous_of_discreteTopology`), and the `p`-adic valuation has
`v (1/p) > 1` with `1/p` in the ring of definition.

It is **not restrictive** either, and that is what makes the results below usable rather than
conditional. A ring of integral elements `A⁺` is by definition open, so
`TauCeti.Huber.PairOfDefinition.exists_pairOfDefinition_ringOfDefinition_le` supplies a pair of
definition with `A₀ ⊆ A⁺`; and every point of `Spa (A, A⁺)` is `≤ 1` on `A⁺`. The choice of pair
of definition is free, and this one costs nothing.

## Main results

* `TauCeti.Huber.PairOfDefinition.extendToLocalization_le_one_of_mem_locSubring`: the extension
  is `≤ 1` on the candidate ring of definition `D = A₀[T/s]` of `Aₛ`.
* `TauCeti.Huber.PairOfDefinition.extendToLocalization_lt_of_mem_locIdealImage`: if `v` is
  smaller than `γ` on the image of `Iⁿ`, then the extension is smaller than `γ` on the whole
  `n`-th basic neighbourhood of zero in `Aₛ`.
* `TauCeti.Huber.PairOfDefinition.isContinuous_extendToLocalization`: **the extension of a
  continuous valuation is continuous** for `locTopology`.
* `TauCeti.Huber.extendToLocalization_le_one_of_mem_integralClosure_adjoin_plus`: **the extension
  is `≤ 1` on the plus ring of the localisation**, the integral closure of `A⁺[T/s]` in `Aₛ`.

The two headline results are assembled into a statement about adic spectra in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Surjective`.

## What is not proved here

Nothing about the *completed* localisation `A⟨T/s⟩`. Extending a continuous valuation from a
Huber ring to its Hausdorff completion is a separate theorem, and it is not used or assumed
below; every statement here concerns `Aₛ` with `locTopology`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and
  Definition 5.51 for the localisation topology, §7.3 for rational subsets, and §8.1 for the
  coordinate ring of a rational subset.

## Provenance

The mathematics is Huber's, in the form of Wedhorn's §8.1 identification of the adic spectrum of
a rational localisation with the rational subset; the Lean is written against this repository's
own `locTopology` and `locSubring` API together with Mathlib's `Valuation.extendToLocalization`,
and follows no existing formalisation. AINTLIB — the roadmap's designated prior formalisation of
this material — was **not** consulted: no checkout of it was available in the authoring
environment. Nothing is ported.
-/

public section

open TauCeti.Localization

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable (S : Type*) [CommRing S] [Algebra A S]

namespace PairOfDefinition

variable (P : PairOfDefinition A) (T : Finset A) (s : A) [IsLocalization.Away s S]

/-- **The extension is `≤ 1` on `D = A₀[t₁/s, …, tₙ/s]`.** `D` is generated by the image of the
ring of definition together with the distinguished fractions, and the two hypotheses bound the
extension by `1` on each family of generators; the valuation ring of the extension is a subring,
so it swallows the whole of `D`. -/
theorem extendToLocalization_le_one_of_mem_locSubring {v : Valuation A Γ₀} (hs : v s ≠ 0)
    (hA₀ : ∀ a ∈ P.ringOfDefinition, v a ≤ 1) (hT : ∀ t ∈ T, v t ≤ v s)
    {x : S} (hx : x ∈ locSubring P T s S) :
    v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S x ≤ 1 := by
  have hle : locSubring P T s S ≤
      (v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S).integer := by
    refine (locSubring_le_iff P T s S).mpr ⟨fun a ha ↦ ?_, fun t ht ↦ ?_⟩
    · rw [Valuation.mem_integer_iff _, Valuation.extendToLocalization_apply_map_apply]
      exact hA₀ a ha
    · exact (Valuation.mem_integer_iff _ _).mpr
        (Valuation.extendToLocalization_divBy_le_one S hs (hT t ht))
  exact (Valuation.mem_integer_iff _ _).mp (hle hx)

/-- **A bound on the `n`-th basic neighbourhood of zero in `Aₛ`.** If `v` is smaller than `γ` on
the image of `Iⁿ`, then the extension is smaller than `γ` on the image of `Jⁿ`.

The image of `Jⁿ` is not merely the image of `Iⁿ`: `Jⁿ` is the ideal of `D` spanned by that
image, so its elements are `D`-combinations. That is why the hypotheses bounding the extension on
`D` appear here as well. -/
theorem extendToLocalization_lt_of_mem_locIdealImage {v : Valuation A Γ₀} (hs : v s ≠ 0)
    (hA₀ : ∀ a ∈ P.ringOfDefinition, v a ≤ 1) (hT : ∀ t ∈ T, v t ≤ v s)
    {γ : Γ₀} {n : ℕ} (hn : ∀ b ∈ P.idealImage n, v b < γ)
    {x : S} (hx : x ∈ locIdealImage P T s S n) :
    v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S x < γ := by
  obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T s S n).mp hx
  clear hx
  rw [locIdeal_pow_eq_span] at hd
  induction hd using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    rw [toLocSubring_apply, Valuation.extendToLocalization_apply_map_apply]
    exact hn _ ((P.mem_idealImage n).mpr ⟨b, hb, rfl⟩)
  | zero => simpa using hn 0 (P.idealImage n).zero_mem
  | add y z _ _ hy hz => exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy hz)
  | smul r y _ hy =>
    rw [smul_eq_mul, MulMemClass.coe_mul, Valuation.map_mul]
    have hr : v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S r ≤ 1 :=
      extendToLocalization_le_one_of_mem_locSubring S P T s hs hA₀ hT r.2
    calc _ ≤ 1 * v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S y := by gcongr
      _ < γ := by rwa [one_mul]

/-- **The extension of a continuous valuation to `Aₛ` is continuous** for Wedhorn's localisation
topology, provided the valuation dominates the numerators by the denominator and is `≤ 1` on the
ring of definition. The module docstring explains why the last hypothesis is needed and why it
costs nothing. -/
theorem isContinuous_extendToLocalization [IsTopologicalRing A]
    (hden : HasDenominatorPower P T s S) {v : Valuation A Γ₀} (hv : v.IsContinuous) (hs : v s ≠ 0)
    (hA₀ : ∀ a ∈ P.ringOfDefinition, v a ≤ 1) (hT : ∀ t ∈ T, v t ≤ v s) :
    letI := locTopology P T s S hden
    (v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S).IsContinuous := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  rw [Valuation.isContinuous_iff_forall_ne_zero]
  intro b hb
  -- Every element of `Aₛ` is a fraction, so the value to be undercut is a ratio `v a / v y`,
  -- and Wedhorn's quantifier over the whole value group is exactly what reaches it.
  obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) b
  have hy : v (y : A) ≠ 0 := fun h ↦
    Ideal.mem_primeCompl_iff.mp (Valuation.powers_le_supp_primeCompl hs y.2)
      ((Valuation.mem_supp_iff _ _).mpr h)
  rw [Valuation.extendToLocalization_mk', ← div_eq_mul_inv] at hb ⊢
  have hnhds : {c : A | v c < v a / v (y : A)} ∈ nhds (0 : A) :=
    (hv.isOpen_lt_div a hy).mem_nhds (by simpa using zero_lt_iff.mpr hb)
  obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hnhds
  -- The sublevel set is an additive subgroup containing an open one, hence open.
  let G : AddSubgroup S :=
    { carrier := {x : S |
        v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S x < v a / v (y : A)}
      add_mem' := fun hx hz ↦ lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hz)
      zero_mem' := by simpa using zero_lt_iff.mpr hb
      neg_mem' := fun {x} hx ↦ by simpa using hx }
  exact AddSubgroup.isOpen_mono (H₁ := locIdealImage P T s S n) (H₂ := G)
    (fun x hx ↦ extendToLocalization_lt_of_mem_locIdealImage S P T s hs hA₀ hT
      (fun c hc ↦ hn hc) hx)
    (isOpen_locIdealImage P T s S hden n)

end PairOfDefinition

variable (T : Finset A) (s : A) [IsLocalization.Away s S]

omit [TopologicalSpace A] in
/-- **The extension is `≤ 1` on `A⁺[t₁/s, …, tₙ/s]`.** No topology enters: the subalgebra is
generated over `A⁺` by the distinguished fractions, and the two hypotheses bound the extension on
both families of generators. -/
theorem extendToLocalization_le_one_of_mem_adjoin_plus (Aplus : Subring A) {v : Valuation A Γ₀}
    (hs : v s ≠ 0) (hplus : ∀ a ∈ Aplus, v a ≤ 1) (hT : ∀ t ∈ T, v t ≤ v s) {x : S}
    (hx : x ∈ Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))) :
    v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S x ≤ 1 := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    exact Valuation.extendToLocalization_divBy_le_one S hs (hT t t.2)
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply ↥Aplus A S, Valuation.extendToLocalization_apply_map_apply]
    exact hplus _ r.2
  | add y z _ _ hy hz => exact le_trans (Valuation.map_add _ _ _) (max_le hy hz)
  | mul y z _ _ hy hz => rw [Valuation.map_mul]; exact mul_le_one' hy hz

omit [TopologicalSpace A] in
/-- **The extension is `≤ 1` on the plus ring of the localisation** — the integral closure in
`Aₛ` of `A⁺[t₁/s, …, tₙ/s]`, which
`TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_integralClosure_adjoin_plus` makes a ring
of integral elements of `Aₛ`.

The integral closure is free of charge: the valuation ring of the extension is integrally closed
in `Aₛ`, so bounding the extension on the generating subalgebra bounds it on the closure. -/
theorem extendToLocalization_le_one_of_mem_integralClosure_adjoin_plus (Aplus : Subring A)
    {v : Valuation A Γ₀} (hs : v s ≠ 0) (hplus : ∀ a ∈ Aplus, v a ≤ 1) (hT : ∀ t ∈ T, v t ≤ v s)
    {x : S} (hx : x ∈ (integralClosure
      ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring) :
    v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S x ≤ 1 := by
  set w := v.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S
  set E := Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))
  let φ : ↥E →+* w.integer :=
    (E.toSubring).subtype.codRestrict w.integer fun r ↦
      (Valuation.mem_integer_iff _ _).mpr
        (extendToLocalization_le_one_of_mem_adjoin_plus S T s Aplus hs hplus hT r.2)
  rw [Subalgebra.mem_toSubring, mem_integralClosure_iff] at hx
  have hint : IsIntegral w.integer x := hx.map_of_comp_eq φ (RingHom.id S) (by ext r; rfl)
  exact (Valuation.mem_integer_iff _ _).mp ((Valuation.integer.integers w).mem_of_integral hint)

end TauCeti.Huber

end
