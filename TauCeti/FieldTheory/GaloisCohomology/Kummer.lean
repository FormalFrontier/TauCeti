/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowerClassGroup
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact

/-!
# The Kummer map `Kˣ → H¹(G_K, μₙ)`

Let `K` be a field, `Kˢ` a separable closure, `G_K = AbsoluteGaloisGroup K`, and `n` a natural
number invertible in `K`. The Kummer sequence

```text
1 ⟶ μₙ ⟶ (Kˢ)ˣ ⟶ (Kˢ)ˣ ⟶ 1
```

of discrete `G_K`-modules is `TauCeti.kummerShortExact`; its degree-zero connecting map, read
through the identification `TauCeti.baseUnitsEquivInvariants` of `H⁰(G_K, (Kˢ)ˣ)` with `Kˣ`, is
the **Kummer map** `Kˣ → H¹(G_K, μₙ)`. This file constructs it, computes it on cocycles, and
identifies its kernel.

The computation is the classical one. Choose an `n`th root `α ∈ (Kˢ)ˣ` of `a ∈ Kˣ`; then
`g ↦ g α / α` takes values in `μₙ`, because raising it to the `n` gives `g a / a = 1`, and it is a
continuous `1`-cocycle, because its image in `(Kˢ)ˣ` is the coboundary `d⁰ α`. Its class is the
Kummer class of `a`. The class does not depend on the choice of root: two roots differ by an
element `ζ` of `μₙ`, and the two cocycles differ by the coboundary `d⁰ ζ`. That independence is
proved directly, with no hypothesis on `n`, so it is available for any `a` that happens to have a
root.

The kernel is `(Kˣ)ⁿ`. This is exactness of the long exact sequence at `H⁰(G_K, (Kˢ)ˣ)` —
`explicitLongExact_H0C` — together with the commuting square
`TauCeti.explicitCoeff0_baseUnitsEquivInvariants`, which says that the `n`th power map on the
invariants of `(Kˢ)ˣ` is the `n`th power map of `Kˣ`. So the Kummer map descends to an
**injection** of the power-class group `Kˣ ⧸ (Kˣ)ⁿ` into `H¹(G_K, μₙ)`.

What is not here is surjectivity, which is Hilbert 90 for `Kˢ/K` and needs the description of
`H¹` as a colimit over the finite quotients of `G_K`. Surjectivity is the only missing input for
the Kummer isomorphism `Kˣ ⧸ (Kˣ)ⁿ ≅ H¹(G_K, μₙ)`.

## Main definitions

* `TauCeti.kummerCocycle`: the cocycle `g ↦ g α / α` attached to a choice of `n`th root, and
  `TauCeti.kummerCocycleClass` its class in `H¹(G_K, μₙ)`.
* `TauCeti.kummerMap`: the multiplicative Kummer map
  `Kˣ →* Multiplicative (H¹(G_K, μₙ))`.
* `TauCeti.kummerClassMap`: the induced map on the power classes `Kˣ ⧸ (Kˣ)ⁿ`.

## Main results

* `TauCeti.kummerCocycle_mem_Z1`: `g ↦ g α / α` is a continuous `1`-cocycle.
* `TauCeti.kummerCocycleClass_congr`: independence of the choice of `n`th root.
* `TauCeti.kummerMap_eq_kummerCocycleClass`: the Kummer class of `a` is the class of
  `g ↦ g α / α`.
* `TauCeti.ker_kummerMap`: the kernel of the Kummer map is `(Kˣ)ⁿ`, with
  `TauCeti.kummerMap_eq_one_iff` the pointwise form.
* `TauCeti.kummerClassMap_injective`: `Kˣ ⧸ (Kˣ)ⁿ` injects into `H¹(G_K, μₙ)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The cocycle attached to an `n`th root

Nothing in this section needs `n` to be invertible in `K`: the input is a chosen `n`th root of the
given unit, and invertibility of `n` is only what produces one. -/

variable {a : Kˣ} {α β : (SeparableClosure K)ˣ}

/-- **The Kummer ratio is an `n`th root of unity**: if `αⁿ = a` with `a` in the base field, then
`(g α / α)ⁿ = g a / a = 1`. -/
theorem smul_mul_inv_mem_rootsOfUnity
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (g : AbsoluteGaloisGroup K) : g • α * α⁻¹ ∈ rootsOfUnity n (SeparableClosure K) := by
  rw [mem_rootsOfUnity, mul_pow, ← smul_pow', inv_pow, hα, smul_units_map_algebraMap,
    mul_inv_cancel]

/-- **The Kummer cocycle** `g ↦ g α / α` of a unit `a` of `K` and a choice of `n`th root `α` of
`a` in `Kˢ`. Its class is the Kummer class of `a` (`TauCeti.kummerMap_eq_kummerCocycleClass`) and
is independent of the choice of `α` (`TauCeti.kummerCocycleClass_congr`). -/
def kummerCocycle (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    AbsoluteGaloisGroup K → KummerCoeff K n :=
  fun g => Additive.ofMul ⟨g • α * α⁻¹, smul_mul_inv_mem_rootsOfUnity hα g⟩

@[simp]
theorem toMul_kummerCocycle
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (g : AbsoluteGaloisGroup K) :
    ((kummerCocycle hα g).toMul : (SeparableClosure K)ˣ) = g • α * α⁻¹ :=
  (rfl)

/-- The coefficient inclusion of the Kummer cocycle is the coboundary ratio `g • α - α` in the
units of `Kˢ`. -/
theorem kummerCoeffIncl_kummerCocycle
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (g : AbsoluteGaloisGroup K) :
    kummerCoeffIncl K n (kummerCocycle hα g) =
      g • (Additive.ofMul α : UnitsCoeff K) - Additive.ofMul α :=
  Additive.toMul.injective <| by
    rw [toMul_kummerCoeffIncl, toMul_kummerCocycle, toMul_sub, Additive.toMul_smul,
      toMul_ofMul, div_eq_mul_inv]

/-- **The Kummer ratio `g ↦ g α / α` is a continuous `1`-cocycle** with values in `μₙ`. -/
theorem kummerCocycle_mem_Z1
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerCocycle hα ∈ Z1 (AbsoluteGaloisGroup K) (KummerCoeff K n) := by
  have hd0 : ∀ g : AbsoluteGaloisGroup K, kummerCoeffIncl K n (kummerCocycle hα g) =
      d0 (AbsoluteGaloisGroup K) (UnitsCoeff K) (Additive.ofMul α) g := fun g =>
    (kummerCoeffIncl_kummerCocycle hα g).trans (d0_apply _ g).symm
  refine mem_Z1_iff.2 ⟨continuous_of_injective_comp (kummerCoeffIncl_injective K n) ?_,
    fun g h => kummerCoeffIncl_injective K n ?_⟩
  · simpa only [hd0] using
      continuous_d0_apply (G := AbsoluteGaloisGroup K) (Additive.ofMul α : UnitsCoeff K)
  · rw [map_add, kummerCoeffIncl_equivariant, kummerCoeffIncl_kummerCocycle,
      kummerCoeffIncl_kummerCocycle, kummerCoeffIncl_kummerCocycle, smul_sub, smul_smul]
    abel

/-- The class in `H¹(G_K, μₙ)` of the Kummer cocycle of a chosen `n`th root. -/
def kummerCocycleClass
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    H1 (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
  H1pi (AbsoluteGaloisGroup K) (KummerCoeff K n) ⟨kummerCocycle hα, kummerCocycle_mem_Z1 hα⟩

/-- **The Kummer class is independent of the chosen `n`th root.** Two `n`th roots of the same `a`
differ by an element `ζ` of `μₙ`, and `g (α ζ) / (α ζ) = (g α / α) · (g ζ / ζ)` differs from
`g α / α` by the coboundary of `ζ`. -/
theorem kummerCocycleClass_congr
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (hβ : β ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerCocycleClass hα = kummerCocycleClass hβ := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : KummerCoeff K n,
      kummerCoeffIncl K n ζ = (Additive.ofMul β : UnitsCoeff K) - Additive.ofMul α := by
    refine ⟨Additive.ofMul ⟨α⁻¹ * β, ?_⟩, Additive.toMul.injective ?_⟩
    · rw [mem_rootsOfUnity, mul_pow, inv_pow, hα, hβ, inv_mul_cancel]
    · rw [toMul_kummerCoeffIncl, toMul_sub, toMul_ofMul, toMul_ofMul, toMul_ofMul,
        div_eq_mul_inv, mul_comm β α⁻¹]
  have key : kummerCocycle hβ - kummerCocycle hα =
      d0 (AbsoluteGaloisGroup K) (KummerCoeff K n) ζ := by
    funext g
    refine kummerCoeffIncl_injective K n ?_
    rw [Pi.sub_apply, map_sub, kummerCoeffIncl_kummerCocycle, kummerCoeffIncl_kummerCocycle,
      map_d0_apply _ (kummerCoeffIncl_equivariant K n), hζ, d0_apply, smul_sub]
    abel
  have hB : kummerCocycle hβ - kummerCocycle hα ∈
      B1 (AbsoluteGaloisGroup K) (KummerCoeff K n) := by
    rw [key]
    exact d0_mem_B1 ζ
  rw [kummerCocycleClass, kummerCocycleClass]
  exact ((H1pi_eq_iff (f := ⟨kummerCocycle hβ, kummerCocycle_mem_Z1 hβ⟩)
    (f' := ⟨kummerCocycle hα, kummerCocycle_mem_Z1 hα⟩)).2 hB).symm

/-! ### The Kummer map and its kernel -/

variable (K n)

/-- The additive shape of the Kummer connecting homomorphism. This is an implementation detail
of `TauCeti.kummerMap`, whose public evaluation lemma `TauCeti.kummerMap_apply` states the same
equation in terms of `explicitDelta0`. -/
private def kummerMapAdd (hn : IsUnit (n : K)) :
    Additive Kˣ →+ H1 (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
  (kummerShortExact K n hn).explicitDelta0.comp (baseUnitsEquivInvariants K).toAddMonoidHom

/-- The defining equation of the implementation helper `kummerMapAdd`. -/
private theorem kummerMapAdd_apply (hn : IsUnit (n : K)) (c : Additive Kˣ) :
    kummerMapAdd K n hn c =
      (kummerShortExact K n hn).explicitDelta0 (baseUnitsEquivInvariants K c) :=
  (rfl)

/-- **The Kummer map** `Kˣ →* Multiplicative (H¹(G_K, μₙ))`: the degree-zero connecting
homomorphism of the Kummer sequence, written multiplicatively on the units of `K`. -/
def kummerMap (hn : IsUnit (n : K)) :
    Kˣ →* Multiplicative (H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :=
  (kummerMapAdd K n hn).toMultiplicativeRight

/-- **The Kummer map is the degree-zero connecting homomorphism** of the Kummer sequence, read on
the unit `a` through the identification of `Kˣ` with the invariants of `(Kˢ)ˣ`. -/
@[simp]
theorem kummerMap_apply (hn : IsUnit (n : K)) (a : Kˣ) :
    kummerMap K n hn a =
      Multiplicative.ofAdd ((kummerShortExact K n hn).explicitDelta0
        (baseUnitsEquivInvariants K (Additive.ofMul a))) :=
  AddMonoidHom.toMultiplicativeRight_apply_apply (kummerMapAdd K n hn) a

variable {K n}

/-- **Every unit of `K` has an `n`th root in `Kˢ`** when `n` is invertible in `K`; this is
`TauCeti.unitsCoeffPow_surjective` read on units. -/
theorem exists_pow_eq_units_map (hn : IsUnit (n : K)) (a : Kˣ) :
    ∃ α : (SeparableClosure K)ˣ,
      α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a := by
  obtain ⟨x, hx⟩ := unitsCoeffPow_surjective K n hn
    (Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a))
  refine ⟨x.toMul, ?_⟩
  rw [← toMul_unitsCoeffPow, hx, toMul_ofMul]

/-- **The Kummer class of `a` is represented by `g ↦ g α / α`**, for any `n`th root `α` of `a` in
`Kˢ` (NSW (6.2.1)). Together with `TauCeti.exists_pow_eq_units_map` this computes the Kummer map
on every unit. -/
theorem kummerMap_eq_kummerCocycleClass (hn : IsUnit (n : K))
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    Multiplicative.toAdd (kummerMap K n hn a) = kummerCocycleClass hα := by
  rw [kummerMap_apply, toAdd_ofAdd]
  refine (kummerShortExact K n hn).explicitDelta0_apply _
    (b := (Additive.ofMul α : UnitsCoeff K)) (Additive.toMul.injective ?_)
    (kummerCocycle_mem_Z1 hα) fun g => ?_
  · rw [kummerShortExact_proj, toMul_unitsCoeffPow, toMul_ofMul,
      toMul_coe_baseUnitsEquivInvariants, toMul_ofMul, hα]
  · rw [kummerShortExact_incl]
    exact kummerCoeffIncl_kummerCocycle hα g

/-- **The `n`th power map on invariants is the `n`th power map of `Kˣ`.** This is the commuting
square that turns exactness of the long exact sequence at `H⁰(G_K, (Kˢ)ˣ)` into the computation of
the kernel of the Kummer map. -/
theorem explicitCoeff0_baseUnitsEquivInvariants (hn : IsUnit (n : K)) (c : Additive Kˣ) :
    explicitCoeff0 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (kummerShortExact K n hn).projDistribMulActionHom (baseUnitsEquivInvariants K c) =
      baseUnitsEquivInvariants K (Additive.ofMul (c.toMul ^ n)) :=
  Subtype.ext <| Additive.toMul.injective <| by
    rw [coe_explicitCoeff0, DiscreteShortExact.projDistribMulActionHom_apply,
      kummerShortExact_proj,
      toMul_unitsCoeffPow, toMul_coe_baseUnitsEquivInvariants,
      toMul_coe_baseUnitsEquivInvariants, toMul_ofMul, map_pow]

/-- The additive form of `TauCeti.ker_kummerMap`. Exactness at `H⁰(G_K, (Kˢ)ˣ)` says the kernel
of `δ⁰` is the image of the `n`th power map on invariants, and
`TauCeti.explicitCoeff0_baseUnitsEquivInvariants` reads that image off in `Kˣ`. -/
private theorem ker_kummerMapAdd (hn : IsUnit (n : K)) :
    (kummerMapAdd K n hn).ker = (powerSubgroup Kˣ n).toAddSubgroup := by
  have hker : ∀ c : Additive Kˣ, kummerMapAdd K n hn c = 0 ↔
      baseUnitsEquivInvariants K c ∈ (explicitCoeff0 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (kummerShortExact K n hn).projDistribMulActionHom).range := fun c => by
    rw [(kummerShortExact K n hn).explicitLongExact_H0C]
    exact (AddMonoidHom.mem_ker (f := (kummerShortExact K n hn).explicitDelta0)).symm
  ext c
  rw [AddMonoidHom.mem_ker, hker, Additive.mem_toAddSubgroup, mem_powerSubgroup_iff]
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨v, hv⟩ => ⟨baseUnitsEquivInvariants K (Additive.ofMul v), ?_⟩⟩
  · obtain ⟨d, rfl⟩ := (baseUnitsEquivInvariants K).surjective u
    rw [explicitCoeff0_baseUnitsEquivInvariants] at hu
    exact ⟨d.toMul, congrArg Additive.toMul ((baseUnitsEquivInvariants K).injective hu)⟩
  · rw [explicitCoeff0_baseUnitsEquivInvariants, toMul_ofMul, hv]
    exact congrArg (baseUnitsEquivInvariants K) (Additive.ofMul.apply_symm_apply c)

/-- **The kernel of the multiplicative Kummer map is `(Kˣ)ⁿ`.** -/
theorem ker_kummerMap (hn : IsUnit (n : K)) :
    (kummerMap K n hn).ker = powerSubgroup Kˣ n := by
  ext a
  rw [MonoidHom.mem_ker, kummerMap_apply, ofAdd_eq_one, ← kummerMapAdd_apply,
    ← AddMonoidHom.mem_ker, ker_kummerMapAdd, Additive.mem_toAddSubgroup]
  simp only [toMul_ofMul]

/-- **A unit has trivial Kummer class exactly when it is an `n`th power in `K`.** -/
theorem kummerMap_eq_one_iff (hn : IsUnit (n : K)) (a : Kˣ) :
    kummerMap K n hn a = 1 ↔ ∃ b : Kˣ, b ^ n = a := by
  rw [← MonoidHom.mem_ker, ker_kummerMap, mem_powerSubgroup_iff]

/-! ### The Kummer map on power classes -/

variable (K n)

/-- **The Kummer map on power classes**, `Kˣ ⧸ (Kˣ)ⁿ → H¹(G_K, μₙ)`. It is injective
(`TauCeti.kummerClassMap_injective`); surjectivity, which needs Hilbert 90, is what would upgrade
it to the Kummer isomorphism. -/
def kummerClassMap (hn : IsUnit (n : K)) :
    powerClassQuotient Kˣ n →*
      Multiplicative (H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :=
  QuotientGroup.lift (powerSubgroup Kˣ n) (kummerMap K n hn) <| by
    rw [ker_kummerMap hn]

/-- The quotient Kummer map agrees with `kummerMap` on representatives. -/
@[simp]
theorem kummerClassMap_mk (hn : IsUnit (n : K)) (a : Kˣ) :
    kummerClassMap K n hn (QuotientGroup.mk a) = kummerMap K n hn a := by
  exact QuotientGroup.lift_mk' (powerSubgroup Kˣ n) (by rw [ker_kummerMap hn]) a

/-- The quotient Kummer map sends the named power class of `a` to its Kummer class. -/
theorem kummerClassMap_powerClassHom (hn : IsUnit (n : K)) (a : Kˣ) :
    kummerClassMap K n hn (powerClassHom Kˣ n a) = kummerMap K n hn a := by
  rw [powerClassHom_apply, kummerClassMap_mk]

/-- **`Kˣ ⧸ (Kˣ)ⁿ` injects into `H¹(G_K, μₙ)`**, the kernel of the Kummer map being exactly the
`n`th powers. -/
theorem kummerClassMap_injective (hn : IsUnit (n : K)) :
    Function.Injective (kummerClassMap K n hn) := by
  exact (QuotientGroup.injective_lift_iff _ _ _).2 (ker_kummerMap hn).symm

end TauCeti
