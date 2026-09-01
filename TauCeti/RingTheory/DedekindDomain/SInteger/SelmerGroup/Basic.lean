/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.NthRoot
public import TauCeti.RingTheory.DedekindDomain.SInteger.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# The fundamental exact sequence of the Selmer group, and its finiteness

Let `R` be a Dedekind domain with fraction field `K`, let `S` be a set of height-one primes of `R`
and let `n : ℕ`. Mathlib defines the Selmer group `K⟮S, n⟯` as the subgroup of `Kˣ ⧸ (Kˣ)ⁿ` of
classes whose `v`-adic valuation is divisible by `n` for every `v ∉ S`, and its module docstring
records as `TODO` both *"maps in the sequence"*, *"proofs of exactness of the sequence"* and
*"proofs of finiteness for global fields"*. This file supplies all three, in the form
```
1 → 𝒪_S(K)ˣ / (𝒪_S(K)ˣ)ⁿ → K⟮S, n⟯ → Cl_S(R)[n] → 1
```
where `𝒪_S(K) = Set.integer S K` is the ring of `S`-integers and the `S`-class group `Cl_S(R)` is
`ClassGroup (S.integer K)`.

## The dictionary that makes it work

The `S`-integers are a Dedekind domain with fraction field `K` whose height-one primes are exactly
the `v ∉ S` (`IsDedekindDomain.integerHeightOneSpectrumEquiv`), valuation-compatibly
(`IsDedekindDomain.valuation_integerHeightOneSpectrumEquiv`). Under that dictionary the Selmer
condition on a class `u(Kˣ)ⁿ` says exactly that the principal fractional ideal `(u)` of `𝒪_S` has
all of its multiplicities divisible by `n` — this is `mk_mem_selmerGroup_iff_mem_unitsNDivisible` —
so the right-hand map is the `n`-th root class map
`TauCeti.AlgebraicGeometry.WeilDivisor.nthRootClass` of the `S`-integers, descended along the
surjection `fromUnitsNDivisible`.

## Main definitions

Mathlib's `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` already gives the `S = ∅` case of
the left-hand map, as `IsDedekindDomain.selmerGroup.fromUnit` and `fromUnitLift`. The general-`S`
maps below therefore live in the same `IsDedekindDomain.selmerGroup` namespace and follow the same
`from…`/`to…` scheme.

* `IsDedekindDomain.selmerGroup.fromSUnit`: the left-hand map, from the `S`-units to `K⟮S, n⟯`.
* `IsDedekindDomain.selmerGroup.fromSUnitLift`: the same map after dividing out `n`-th powers of
  `S`-units, which is the left-hand map of the exact sequence proper.
* `IsDedekindDomain.selmerGroup.fromUnitsNDivisible`: the surjection onto `K⟮S, n⟯` from the units
  of `K` whose principal `𝒪_S`-ideal is `n`-divisible.
* `IsDedekindDomain.selmerGroup.toClassGroup`: the right-hand map, to `ClassGroup (S.integer K)`.

## Main results

* `IsDedekindDomain.mk_mem_selmerGroup_iff_mem_unitsNDivisible`: the Selmer condition on a
  representative is `n`-divisibility of its principal `𝒪_S`-ideal.
* `IsDedekindDomain.selmerGroup.fromSUnitLift_injective`: **exactness on the left** — the left-hand
  map is injective, because an `n`-th root in `K` of an `S`-unit is itself an `S`-unit.
* `IsDedekindDomain.selmerGroup.ker_toClassGroup`: **exactness in the middle** — a Selmer class has
  trivial `n`-th-root ideal class exactly when an `S`-unit represents it.
* `IsDedekindDomain.selmerGroup.range_toClassGroup`: **exactness on the right** — the image is the
  `n`-torsion of the `S`-class group. (Surjectivity onto the whole class group is false in
  general.) Of the three, only this one needs `n ≠ 0`.
* `IsDedekindDomain.selmerGroup.finite`: **the Selmer group `K⟮S, n⟯` is finite** when the
  `S`-class group is finite, the `S`-units are finitely generated and `n ≠ 0`.

Finiteness is not automatic for a general Dedekind domain — it already fails for `R = K` a field
whose unit group is not `n`-divisible of finite index — and the exact sequence isolates what is
needed: `[Group.FG (S.unit K)]` and `[Finite (ClassGroup (S.integer K))]`, which are exactly the
hypotheses `selmerGroup.finite` takes. Both are on hand over the base ring, as the `instance`s
`Set.unit_fg_of_units` and `IsDedekindDomain.finite_integer_classGroup`, so a caller holding
`[Finite (ClassGroup R)]`, `[Monoid.FG Rˣ]` and `[Finite S]` gets the finiteness by instance
resolution. For `R` the ring of integers of a number field those are the class number theorem and
Dirichlet's unit theorem.

## References

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
`EllipticCurves` roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), whose treatment this
follows. The names differ: the substrate that source keeps in its own `FractionalIdeal` file is
already here as `TauCeti.AlgebraicGeometry.WeilDivisor.nthRootClass` and its neighbours, and the
`S`-integer dictionary is already here under `IsDedekindDomain.integer*`, so only the Selmer layer
itself is adapted, and it is named after Mathlib's `selmerGroup` API rather than after the source.
Following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header.
-/

public section

open FractionalIdeal IsDedekindDomain.HeightOneSpectrum TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-! ### The Selmer condition as `n`-divisibility of an ideal -/

/-- The class of `u` lies in the Selmer group `K⟮S, n⟯` exactly when the principal fractional
ideal `(u)` of the `S`-integers has all of its multiplicities divisible by `n`. This is the
dictionary that turns the Selmer condition into a statement about ideals of `𝒪_S`, and hence
lets the `n`-th root class map act as the right-hand map of the exact sequence. -/
lemma mk_mem_selmerGroup_iff_mem_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  have lhs : (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
    forall₂_congr fun v _ ↦ valuationOfNeZeroMod_mk_eq_one_iff v n u
  have rhs : u ∈ unitsNDivisible (S.integer K) K n ↔
      ∀ w : HeightOneSpectrum (S.integer K),
        (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    rw [mem_unitsNDivisible]
    refine forall_congr' fun w ↦ ?_
    have hw : Multiplicative.toAdd (w.valuationOfNeZero u)
        = -count K w (spanSingleton (S.integer K)⁰ (u : K)) := by
      have h := adicOrd_eq_fractionalIdeal_count (R := S.integer K) (K := K) w (Additive.ofMul u)
      rw [coe_toPrincipalIdeal, toMul_ofMul, adicOrd_ofMul, ← valuationOfNeZero_eq] at h
      rw [← h, neg_neg]
      rfl
    rw [hw, Int.dvd_neg]
  rw [lhs, rhs]
  refine ⟨fun h w ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [← (integerHeightOneSpectrumEquiv K S).apply_symm_apply w,
      valuationOfNeZero_integerHeightOneSpectrumEquiv K S _ u]
    exact h _ ((integerHeightOneSpectrumEquiv K S).symm w).property
  · have hw := h (integerHeightOneSpectrumEquiv K S ⟨v, hv⟩)
    rwa [valuationOfNeZero_integerHeightOneSpectrumEquiv K S ⟨v, hv⟩ u] at hw

namespace selmerGroup

/-! ### The left-hand map: `S`-units into the Selmer group -/

/-- The class of an `S`-unit lies in the Selmer group `K⟮S, n⟯`: away from `S` an `S`-unit has
trivial valuation, so in particular a valuation divisible by `n`. -/
noncomputable def fromSUnit : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [valuationOfNeZeroMod_mk_eq_one_iff]
    simp [(valuationOfNeZero_eq_one_iff v (x : Kˣ)).mpr (x.property v hv)]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The Selmer class of an `S`-unit is, underneath the subtype, just its class in `Kˣ ⧸ (Kˣ)ⁿ`. -/
@[simp]
lemma coe_fromSUnit (x : S.unit K) :
    (fromSUnit K S n x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (x : Kˣ) :=
  (rfl)

/-- The left-hand map of the fundamental exact sequence: an `S`-unit modulo `n`-th powers of
`S`-units maps to the Selmer group `K⟮S, n⟯`. -/
noncomputable def fromSUnitLift :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (fromSUnit K S n) <| by
    rintro _ ⟨x, rfl⟩
    exact Subtype.ext <| (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

/-- The defining property of `fromSUnitLift`: on the class of an `S`-unit it agrees with the map
`fromSUnit` it descends from. -/
@[simp]
lemma fromSUnitLift_mk (x : S.unit K) :
    fromSUnitLift K S n (QuotientGroup.mk x) = fromSUnit K S n x :=
  (rfl)

/-- Dividing out the `n`-th powers of `S`-units does not change the image: the two left-hand maps
have the same range. -/
@[simp]
lemma range_fromSUnitLift : (fromSUnitLift K S n).range = (fromSUnit K S n).range := by
  ext
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, (fromSUnitLift_mk K S n y).trans hy⟩⟩
  rintro ⟨y, rfl⟩
  induction y using QuotientGroup.induction_on with
  | H y => exact ⟨y, (fromSUnitLift_mk K S n y).symm⟩

/-- **Exactness on the left of the fundamental exact sequence.** The left-hand map is injective:
an `S`-unit that becomes an `n`-th power in `K` is already the `n`-th power of an `S`-unit. What
makes this work is that an `n`-th root `y` of an `S`-unit is again an `S`-unit: away from `S` the
relation `n * ord_v(y) = ord_v(x) = 0` forces `ord_v(y) = 0`.

Like `ker_toClassGroup`, and unlike the exactness on the right, this needs no `n ≠ 0`: for `n = 0`
both sides divide out the trivial subgroup and the claim degenerates to the injectivity of
`S.unit K ≤ Kˣ`. -/
theorem fromSUnitLift_injective : Function.Injective (fromSUnitLift K S n) := by
  rw [injective_iff_map_eq_one]
  intro c
  induction c using QuotientGroup.induction_on with
  | H x =>
    intro hx
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (x : Kˣ)).mp (congrArg Subtype.val hx)
    rw [powMonoidHom_apply] at hy
    rcases eq_or_ne n 0 with rfl | hn
    · -- For `n = 0` the subgroup divided out is trivial, and `hy` already pins `x` down to `1`.
      rw [pow_zero] at hy
      have hx1 : x = 1 := Subtype.ext hy.symm
      rw [hx1, QuotientGroup.mk_one]
    · refine (QuotientGroup.eq_one_iff _).mpr ⟨⟨y, fun v hv ↦ ?_⟩, Subtype.ext ?_⟩
      · refine (valuationOfNeZero_eq_one_iff v y).mp ?_
        have h1 : v.valuationOfNeZero y ^ n = 1 := by
          rw [← map_pow, hy]
          exact (valuationOfNeZero_eq_one_iff v _).mpr (x.property v hv)
        have h2 : Multiplicative.toAdd (v.valuationOfNeZero y) * (n : ℤ) = 0 := by
          rw [← Int.toAdd_pow, h1, toAdd_one]
        exact toAdd_eq_zero.mp <| (mul_eq_zero.mp h2).resolve_right (Nat.cast_ne_zero.mpr hn)
      · rw [powMonoidHom_apply, SubmonoidClass.coe_pow]
        exact hy

/-! ### The surjection from the `n`-divisible units -/

/-- The surjection from the units of `K` whose principal `𝒪_S`-ideal is `n`-divisible onto the
Selmer group `K⟮S, n⟯`, given by taking the class modulo `n`-th powers. -/
noncomputable def fromUnitsNDivisible :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).comp
    (unitsNDivisible (S.integer K) K n).subtype).codRestrict _
      fun u ↦ (mk_mem_selmerGroup_iff_mem_unitsNDivisible K S n (u : Kˣ)).mpr u.2

/-- Underneath the codomain restriction, `fromUnitsNDivisible` is the quotient map. -/
@[simp]
lemma coe_fromUnitsNDivisible (u : unitsNDivisible (S.integer K) K n) :
    (fromUnitsNDivisible K S n u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (u : Kˣ) :=
  (rfl)

/-- **Every Selmer class is represented by an `n`-divisible unit.** This is what lets the `n`-th
root class map be transported from `unitsNDivisible` to the Selmer group. -/
lemma fromUnitsNDivisible_surjective : Function.Surjective (fromUnitsNDivisible K S n) := by
  rintro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u => exact ⟨⟨u, (mk_mem_selmerGroup_iff_mem_unitsNDivisible K S n u).mp hc⟩, rfl⟩

/-- The kernel of `fromUnitsNDivisible` is contained in that of the `n`-th root class map: a unit
that is an `n`-th power in `Kˣ` has principal `n`-th root. This is what lets the `n`-th root class
map descend to the Selmer group. -/
private lemma ker_fromUnitsNDivisible_le :
    (fromUnitsNDivisible K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hu)
  exact (nthRootClass_eq_one_iff (S.integer K) K u).mpr
    ⟨1, w, by rw [map_one, one_mul]; exact hw⟩

/-! ### The right-hand map, and exactness -/

/-- The right-hand map of the fundamental exact sequence: a Selmer class is sent to the ideal
class of the `n`-th root of the principal ideal `(u)` of any representative `u`, in the class
group of the `S`-integers. Obtained by descending the `n`-th root class map along
`fromUnitsNDivisible`. -/
noncomputable def toClassGroup :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (fromUnitsNDivisible K S n).liftOfSurjective (fromUnitsNDivisible_surjective K S n)
    ⟨nthRootClass (S.integer K) K n, ker_fromUnitsNDivisible_le K S n⟩

/-- The defining property of `toClassGroup`: on the class of an `n`-divisible unit it agrees with
the `n`-th root class map it descends from. Every computation with the right-hand map goes through
this lemma, after `fromUnitsNDivisible_surjective` supplies a representative. -/
@[simp]
lemma toClassGroup_fromUnitsNDivisible (u : unitsNDivisible (S.integer K) K n) :
    toClassGroup K S n (fromUnitsNDivisible K S n u) = nthRootClass (S.integer K) K n u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u

/-- **Exactness in the middle of the fundamental exact sequence.** A Selmer class has trivial
`n`-th-root ideal class exactly when it is represented by an `S`-unit.

No `[NeZero n]` is needed, unlike on the right-hand exactness below: `nthRootClass_eq_one_iff`
is stated here for every `n`, degenerate `n = 0` included. -/
theorem ker_toClassGroup : (toClassGroup K S n).ker = (fromSUnit K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := fromUnitsNDivisible_surjective K S n x
  rw [MonoidHom.mem_ker, toClassGroup_fromUnitsNDivisible,
    nthRootClass_eq_one_iff (S.integer K) K]
  constructor
  · rintro ⟨a, w, hw⟩
    refine ⟨(S.unitEquivUnitsInteger K).symm a, Subtype.ext ?_⟩
    rw [coe_fromSUnit, coe_fromUnitsNDivisible]
    have hcoe : ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
        Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := Units.ext rfl
    -- The two representatives differ by `w ^ n`, which is what the quotient divides out.
    refine QuotientGroup.eq.mpr ?_
    rw [hcoe, ← hw, inv_mul_cancel_left]
    exact ⟨w, rfl⟩
  · rintro ⟨s, hs⟩
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp (congrArg Subtype.val hs)
    refine ⟨S.unitEquivUnitsInteger K s, w, ?_⟩
    have hmap : Units.map (algebraMap (S.integer K) K : S.integer K →* K)
        (S.unitEquivUnitsInteger K s) = (s : Kˣ) := Units.ext rfl
    rw [powMonoidHom_apply] at hw
    rw [hmap, hw, mul_inv_cancel_left]
    rfl

/-- **Exactness on the right of the fundamental exact sequence.** The image of `toClassGroup` is
the `n`-torsion of the class group of the `S`-integers; surjectivity onto the full class group
fails in general. -/
theorem range_toClassGroup [NeZero n] : (toClassGroup K S n).range =
    (powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker := by
  ext c
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := fromUnitsNDivisible_surjective K S n x
    rw [toClassGroup_fromUnitsNDivisible]
    exact nthRootClass_pow _ _ _ _
  · intro hc
    obtain ⟨I, rfl⟩ : ∃ I, ClassGroup.mk K I = c :=
      ClassGroup.induction (K := K) (fun I ↦ ⟨I, rfl⟩) c
    rw [← map_pow, ClassGroup.mk_eq_one_iff_exists] at hc
    obtain ⟨x, hx⟩ := hc
    have hcount (v : HeightOneSpectrum (S.integer K)) :
        count K v (spanSingleton (S.integer K)⁰ (x : K)) =
          n * count K v ((I : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) := by
      rw [← coe_toPrincipalIdeal, hx, Units.val_pow_eq_pow_val, count_pow]
    have hmem : x ∈ unitsNDivisible (S.integer K) K n :=
      mem_unitsNDivisible.mpr fun v ↦ by rw [hcount v]; exact Dvd.intro _ rfl
    refine ⟨fromUnitsNDivisible K S n ⟨x, hmem⟩, ?_⟩
    rw [toClassGroup_fromUnitsNDivisible, nthRootClass_apply]
    congr 1
    refine units_eq_of_forall_count_eq _ _ fun v ↦ ?_
    rw [count_nthRootHom, coe_unitsNDivisibleToNDivisible, coe_toPrincipalIdeal, hcount v,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne n))]

/-! ### Finiteness -/

/-- **The Selmer group `K⟮S, n⟯` is finite** as soon as the `n`-torsion of the `S`-class group
is, the `S`-units are finitely generated and `n ≠ 0`.

Both halves of `MonoidHom.finite_iff_finite_ker_range` for `toClassGroup` are in hand. The kernel
is the image of `fromSUnitLift` by `ker_toClassGroup`, finite because its source is the quotient of
the finitely generated group of `S`-units by its `n`-th powers. The range is the `n`-torsion of the
class group by `range_toClassGroup`, which is exactly the hypothesis.

Only that `n`-torsion is needed, never the whole class group: `range_toClassGroup` says the image
of `toClassGroup` never exceeds it. `finite` below is this theorem for a finite class group. -/
theorem finite_of_finite_ker_powMonoidHom
    [Finite ((powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker)]
    [Group.FG (S.unit K)] [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have hker : Finite (toClassGroup K S n).ker := by
    rw [ker_toClassGroup, ← range_fromSUnitLift]
    have : Finite (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) :=
      Subgroup.finiteIndex_iff_finite_quotient.mp <|
        Subgroup.finiteIndex_range_powMonoidHom_of_fg _ (NeZero.ne n)
    exact Finite.Set.finite_range _
  have hrange : Finite (toClassGroup K S n).range := by
    rw [range_toClassGroup]; infer_instance
  exact (MonoidHom.finite_iff_finite_ker_range (toClassGroup K S n)).mpr ⟨hker, hrange⟩

/-- **The Selmer group `K⟮S, n⟯` is finite**, provided that the `S`-class group is finite, that
the `S`-units are finitely generated and that `n ≠ 0`. This discharges the `TODO`
*"proofs of finiteness for global fields"* of `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`.

This is `finite_of_finite_ker_powMonoidHom` for a finite class group, in which every subgroup —
the `n`-torsion included — is finite.

The two hypotheses are exactly what the proof consumes. They are in turn supplied by the
arithmetic over the base ring: `IsDedekindDomain.finite_integer_classGroup` and
`Set.unit_fg_of_units` are `instance`s, so a caller holding `[Finite (ClassGroup R)]`,
`[Monoid.FG Rˣ]` and `[Finite S]` — for `R` the ring of integers of a number field, the class
number theorem and Dirichlet's unit theorem — still gets this by instance resolution. -/
instance finite [Finite (ClassGroup (S.integer K))] [Group.FG (S.unit K)] [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) :=
  finite_of_finite_ker_powMonoidHom K S n

end selmerGroup

end IsDedekindDomain

end
