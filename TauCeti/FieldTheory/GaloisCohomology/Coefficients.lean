/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup
public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.RingTheory.RootsOfUnity.Action

/-!
# The multiplicative coefficient modules of Galois cohomology

Galois cohomology takes its coefficients in discrete modules over `G_K = AbsoluteGaloisGroup K`,
the automorphism group of a separable closure `Kˢ`. This file fixes the two multiplicative
coefficient modules once and for all, written additively through `Additive` as Mathlib's
`Representation.ofMulDistribMulAction` does:

```text
UnitsCoeff K = Additive (Kˢ)ˣ,      KummerCoeff K n = Additive μₙ,
```

with `μₙ = rootsOfUnity n Kˢ`. Both are **discrete** `G_K`-modules: their point stabilizers are
open because every element of `Kˢ` is separable over `K`, hence lies in a finite subextension
(`TauCeti.stabilizer_isOpen_units`). The action on `μₙ` is in general nontrivial, and the Kummer
isomorphism is false for the trivial action, so it is the module and not the abstract group that
is named here.

The two maps between them assemble the **Kummer sequence**

```text
1 ⟶ μₙ ⟶ (Kˢ)ˣ ⟶ (Kˢ)ˣ ⟶ 1
```

as a `TauCeti.ContCohomology.DiscreteShortExact`, so that the long exact sequence of continuous
cohomology applies to it verbatim. Exactness in the middle holds over any field and for any `n`;
surjectivity on the right is where `IsUnit (n : K)` enters, through the separability of `Xⁿ - a`
and the separable closedness of `Kˢ`.

Finally `TauCeti.baseUnitsEquivInvariants` identifies `H⁰(G_K, (Kˢ)ˣ)` with `Kˣ`. These are not
the same Lean type — the invariants are an additive subgroup of `Additive (Kˢ)ˣ` — so what is
supplied is the canonical isomorphism and not an equality. Using the **separable** closure is
essential: for imperfect `K` the fixed field of the automorphism group of an algebraic closure is
the purely inseparable closure of `K` and not `K` itself
(`TauCeti.mem_perfectClosure_iff_fixed`), so the invariants of the units of an algebraic closure
are strictly larger than `Kˣ`.

## Main definitions

* `TauCeti.UnitsCoeff`, `TauCeti.KummerCoeff`: the two coefficient modules, with their discrete
  topologies.
* `TauCeti.kummerCoeffIncl`, `TauCeti.unitsCoeffPow`: the inclusion `μₙ ↪ (Kˢ)ˣ` and the `n`-th
  power map, the two maps of the Kummer sequence.
* `TauCeti.kummerShortExact`: the Kummer sequence as a short exact sequence of discrete
  `G_K`-modules.
* `TauCeti.baseUnitsEquivInvariants`: the isomorphism `Kˣ ≅ H⁰(G_K, (Kˢ)ˣ)`.

## Main results

* `TauCeti.unitsCoeff_continuousSMul`, `TauCeti.kummerCoeff_continuousSMul`: the coefficients are
  discrete modules, that is, the action is continuous.
* `TauCeti.mem_H0_unitsCoeff_iff`: a unit of `Kˢ` fixed by `G_K` comes from `Kˣ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it, for the Kummer sequence and the invariants of `(Kˢ)ˣ`.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

variable (K : Type*) [Field K]

/-! ### The units of the separable closure -/

/-- The multiplicative coefficient module of Galois cohomology: the units of a separable closure
of `K`, written additively. This is the module Hilbert 90 and the cohomological Brauer group are
stated at, and `KummerCoeff K n` is its `n`-torsion submodule. -/
abbrev UnitsCoeff : Type _ := Additive (SeparableClosure K)ˣ

instance : TopologicalSpace (UnitsCoeff K) := ⊥

instance : DiscreteTopology (UnitsCoeff K) := ⟨rfl⟩

/-- **`(Kˢ)ˣ` is a discrete `G_K`-module**: every unit of `Kˢ` is separable over `K`, so it lies
in a finite subextension and its stabilizer is open. -/
instance unitsCoeff_continuousSMul : ContinuousSMul (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  continuousSMul_iff_stabilizer_isOpen.2 fun x => stabilizer_isOpen_units (K := K) x.toMul

/-! ### The roots of unity -/

/-- The Kummer coefficient module: the `n`-th roots of unity in a separable closure of `K`,
written additively. The `G_K`-action on `μₙ` is in general nontrivial and the Kummer isomorphism
depends on it, so the coefficients are fixed as this module rather than as an abstract cyclic
group. -/
abbrev KummerCoeff (n : ℕ) : Type _ := Additive (rootsOfUnity n (SeparableClosure K))

variable (n : ℕ)

instance : TopologicalSpace (KummerCoeff K n) := ⊥

instance : DiscreteTopology (KummerCoeff K n) := ⟨rfl⟩

/-- **`μₙ` is a discrete `G_K`-module**: the stabilizer of a root of unity is the stabilizer of
the underlying unit of `Kˢ`, which is open. -/
instance kummerCoeff_continuousSMul :
    ContinuousSMul (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
  continuousSMul_iff_stabilizer_isOpen.2 fun x => by
    convert stabilizer_isOpen_units (K := K) (x.toMul : (SeparableClosure K)ˣ) using 2
    ext σ
    refine ⟨fun h => ?_, fun h => Additive.toMul.injective (Subtype.ext (by simpa using h))⟩
    simpa using
      congrArg (fun v : KummerCoeff K n => (v.toMul : (SeparableClosure K)ˣ)) h

/-! ### The two maps of the Kummer sequence -/

/-- The inclusion `μₙ ↪ (Kˢ)ˣ`, the left-hand map of the Kummer sequence. -/
def kummerCoeffIncl : KummerCoeff K n →+ UnitsCoeff K :=
  MonoidHom.toAdditive (rootsOfUnity n (SeparableClosure K)).subtype

@[simp]
theorem toMul_kummerCoeffIncl (x : KummerCoeff K n) :
    (kummerCoeffIncl K n x).toMul = (x.toMul : (SeparableClosure K)ˣ) :=
  (rfl)

@[simp]
theorem kummerCoeffIncl_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K n) :
    kummerCoeffIncl K n (g • x) = g • kummerCoeffIncl K n x :=
  Additive.toMul.injective (by simp)

theorem kummerCoeffIncl_injective : Function.Injective (kummerCoeffIncl K n) := fun x y h =>
  Additive.toMul.injective <| Subtype.ext <| by
    simpa only [toMul_kummerCoeffIncl] using congrArg Additive.toMul h

/-- The `n`-th power map on `(Kˢ)ˣ`, the right-hand map of the Kummer sequence. In additive
notation it is multiplication by `n`, which is `TauCeti.unitsCoeffPow_eq_nsmul`. -/
def unitsCoeffPow : UnitsCoeff K →+ UnitsCoeff K :=
  MonoidHom.toAdditive (powMonoidHom n)

@[simp]
theorem toMul_unitsCoeffPow (x : UnitsCoeff K) :
    (unitsCoeffPow K n x).toMul = x.toMul ^ n :=
  (rfl)

theorem unitsCoeffPow_eq_nsmul (x : UnitsCoeff K) : unitsCoeffPow K n x = n • x :=
  Additive.toMul.injective <| by simp [toMul_nsmul]

@[simp]
theorem unitsCoeffPow_equivariant (g : AbsoluteGaloisGroup K) (x : UnitsCoeff K) :
    unitsCoeffPow K n (g • x) = g • unitsCoeffPow K n x :=
  Additive.toMul.injective <| by simp [smul_pow']

/-- **Exactness of the Kummer sequence in the middle**: a unit of `Kˢ` has trivial `n`-th power
exactly when it is an `n`-th root of unity. This holds over any field and for every `n`. -/
theorem kummerSequence_exact : Function.Exact (kummerCoeffIncl K n) (unitsCoeffPow K n) := by
  intro x
  refine ⟨fun hx => ⟨Additive.ofMul ⟨x.toMul, ?_⟩, Additive.toMul.injective (by simp)⟩, ?_⟩
  · simpa only [mem_rootsOfUnity, toMul_unitsCoeffPow, toMul_zero] using
      congrArg Additive.toMul hx
  · rintro ⟨y, rfl⟩
    exact Additive.toMul.injective <| by
      simpa only [toMul_unitsCoeffPow, toMul_kummerCoeffIncl, toMul_zero] using
        (mem_rootsOfUnity n _).1 y.toMul.2

/-- **The `n`-th power map on the units of a separable closure is surjective** when `n` is
invertible in `K`: `Xⁿ - a` is then separable, and `Kˢ` is separably closed. -/
theorem unitsCoeffPow_surjective (hn : IsUnit (n : K)) :
    Function.Surjective (unitsCoeffPow K n) := by
  have hn0 : (n : SeparableClosure K) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (SeparableClosure K))).2 hn.ne_zero
    rwa [map_natCast] at h
  have hn' : n ≠ 0 := by rintro rfl; simp at hn0
  have : NeZero (n : SeparableClosure K) := ⟨hn0⟩
  intro x
  obtain ⟨z, hz⟩ :=
    IsSepClosed.exists_pow_nat_eq ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) n
  have hz0 : z ≠ 0 := fun h => x.toMul.ne_zero (by rw [← hz, h, zero_pow hn'])
  refine ⟨Additive.ofMul (Units.mk0 z hz0), Additive.toMul.injective (Units.ext ?_)⟩
  simpa using hz

/-- **The Kummer sequence** `1 → μₙ → (Kˢ)ˣ → (Kˢ)ˣ → 1` of discrete `G_K`-modules, for `n`
invertible in `K` (NSW (6.2.1)). It is the datum the long exact sequence of continuous cohomology
is applied to, and its degree-zero connecting map is the Kummer map. -/
def kummerShortExact (hn : IsUnit (n : K)) :
    DiscreteShortExact (AbsoluteGaloisGroup K) (KummerCoeff K n) (UnitsCoeff K)
      (UnitsCoeff K) where
  incl := kummerCoeffIncl K n
  proj := unitsCoeffPow K n
  incl_equivariant := kummerCoeffIncl_equivariant K n
  proj_equivariant := unitsCoeffPow_equivariant K n
  incl_injective := kummerCoeffIncl_injective K n
  proj_surjective := unitsCoeffPow_surjective K n hn
  exact := kummerSequence_exact K n

@[simp]
theorem kummerShortExact_incl (hn : IsUnit (n : K)) :
    (kummerShortExact K n hn).incl = kummerCoeffIncl K n :=
  (rfl)

@[simp]
theorem kummerShortExact_proj (hn : IsUnit (n : K)) :
    (kummerShortExact K n hn).proj = unitsCoeffPow K n :=
  (rfl)

/-! ### The invariants of the units -/

variable {K}

/-- **A unit of `Kˢ` fixed by the whole Galois group comes from `Kˣ`.** This is the fixed-field
theorem for the separable closure read on units: `InfiniteGalois.mem_range_algebraMap_iff_fixed`
supplies base-field preimages of the unit and of its inverse, and those preimages are inverse to
each other in `K` because the structure map is injective. -/
theorem mem_H0_unitsCoeff_iff {u : UnitsCoeff K} :
    u ∈ H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) ↔
      ∃ a : Kˣ, Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a = u.toMul := by
  rw [FixedPoints.mem_addSubgroup]
  refine ⟨fun hu => ?_, ?_⟩
  · -- The unit and its inverse are both fixed, so both come from the base field.
    have hfixU : ∀ σ : AbsoluteGaloisGroup K,
        Units.map (σ : SeparableClosure K →* SeparableClosure K) u.toMul = u.toMul :=
      fun σ => by simpa using congrArg Additive.toMul (hu σ)
    have hfix : ∀ σ : AbsoluteGaloisGroup K,
        σ ((u.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) =
          ((u.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) :=
      fun σ => congrArg Units.val (hfixU σ)
    have hinv : ∀ σ : AbsoluteGaloisGroup K,
        σ (((u.toMul)⁻¹ : (SeparableClosure K)ˣ) : SeparableClosure K) =
          (((u.toMul)⁻¹ : (SeparableClosure K)ˣ) : SeparableClosure K) :=
      fun σ => congrArg
        (fun v : (SeparableClosure K)ˣ => ((v⁻¹ : (SeparableClosure K)ˣ) : SeparableClosure K))
        (hfixU σ)
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hinv
    have hab : a * b = 1 := (algebraMap K (SeparableClosure K)).injective <| by
      rw [map_mul, ha, hb, map_one]
      exact u.toMul.mul_inv
    exact ⟨⟨a, b, hab, by rwa [mul_comm] at hab⟩, Units.ext ha⟩
  · rintro ⟨a, ha⟩ σ
    refine Additive.toMul.injective ?_
    rw [Additive.toMul_smul, ← ha]
    exact Units.ext (AlgEquiv.commutes σ (a : K))

variable (K)

/-- **The invariants of `(Kˢ)ˣ` are the units of `K`**, that is `H⁰(G_K, (Kˢ)ˣ) ≅ Kˣ`. The two
sides are different Lean types, so this canonical isomorphism — and not an equality — is what a
cohomological construction starting from `Kˣ` goes through, the Kummer map among them. -/
def baseUnitsEquivInvariants :
    Additive Kˣ ≃+ H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  AddEquiv.ofBijective
    ((MonoidHom.toAdditive
      (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom)).codRestrict _
        fun a => mem_H0_unitsCoeff_iff.2 ⟨a.toMul, rfl⟩)
    ⟨fun x y h => Additive.toMul.injective <| Units.ext <|
        (algebraMap K (SeparableClosure K)).injective <|
          congrArg (fun v : H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) =>
            (((v : UnitsCoeff K).toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) h,
      fun u => by
        obtain ⟨a, ha⟩ := mem_H0_unitsCoeff_iff.1 u.2
        exact ⟨Additive.ofMul a, Subtype.ext (Additive.toMul.injective ha)⟩⟩

@[simp]
theorem toMul_coe_baseUnitsEquivInvariants (a : Additive Kˣ) :
    ((baseUnitsEquivInvariants K a : UnitsCoeff K).toMul : (SeparableClosure K)ˣ) =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a.toMul :=
  (rfl)

end TauCeti
