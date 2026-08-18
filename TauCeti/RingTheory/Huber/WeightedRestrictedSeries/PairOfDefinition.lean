/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import Mathlib.Data.Finsupp.Weight

/-!
# `A⟨X⟩_T` is a Huber ring

For a Huber ring `A` with pair of definition `(A₀, I)`, the ring `A⟨X₁,…,Xₖ⟩_T` of weighted
restricted power series is again a Huber ring, with pair of definition

```text
(A₀⟨X⟩_T, I⟨X⟩_T),    Iⁿ⟨X⟩_T = {f; coeff ν f ∈ Tν · Iⁿ for every ν}.
```

The content is the identification of the neighbourhood subgroups with the powers of one finitely
generated ideal:

```text
(I⟨X⟩_T) ^ n = Iⁿ⟨X⟩_T.
```

The inclusion `⊆` is coefficientwise multiplication. The reverse inclusion is where finite
generation of `I` is used, and it is not a formal consequence of it: a series whose coefficients
all lie in `Iⁿ⁺¹` must be written as a combination of finitely many generators with cofactors that
are themselves *restricted* series, so the cofactors have to tend to zero. They are obtained by
decomposing each coefficient not at the uniform level `n + 1` but at the level `n + 1 + m ν` that
the coefficient actually attains, cut off at the degree of `ν` so that the level is attained;
a private level-selection lemma packages that choice.

A pseudouniformiser of `A` stays one in `A⟨X⟩_T` as a constant series, so the Tate property is
inherited too. Since completion preserves both properties
(`TauCeti.Huber.IsHuberRing.completion`, `TauCeti.Huber.IsTateRing.completion`), the completed
algebra `A⟨X₁,…,Xₖ⟩` of the roadmap — the separated completion of the trivial-weight `A⟨X⟩_T` — is
a Huber ring, Tate whenever `A` is; its completeness and separatedness are those of any separated
completion and need no argument here.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.weightedRingOfDefinition`: `A₀⟨X⟩_T`, the ring of definition,
  with its structure map `TauCeti.Huber.PairOfDefinition.weightedRingOfDefinitionC` from `A₀`.
* `TauCeti.Huber.PairOfDefinition.weightedIdeal`: `Iⁿ⟨X⟩_T`, as an ideal of `A₀⟨X⟩_T`. The ideal
  of definition is the case `n = 1`.
* `TauCeti.Huber.PairOfDefinition.weighted`: the pair of definition of `A⟨X⟩_T`.

## Main results

* `TauCeti.Huber.PairOfDefinition.exists_sum_weightedRingOfDefinitionC_mul`: the decomposition of
  a series over generators of `I`, with restricted cofactors.
* `TauCeti.Huber.PairOfDefinition.weightedIdeal_one_pow`: `(I⟨X⟩_T) ^ n = Iⁿ⟨X⟩_T`, from which
  both the finite generation of the ideal of definition
  (`TauCeti.Huber.PairOfDefinition.fg_weightedIdeal_one`) and its adicity
  (`TauCeti.Huber.PairOfDefinition.isAdic_weightedIdeal_one`) follow.
* `TauCeti.Huber.isHuberRing_weightedRestrictedSubring` and
  `TauCeti.Huber.isTateRing_weightedRestrictedSubring`: the two instances. The completed algebra
  `A⟨X₁,…,Xₖ⟩` at the trivial weight, which is the roadmap's object, inherits both from them by
  synthesis, with no separate result: see the `example`s at the end of the file.

## Provenance

No formalisation of this result was available: the roadmap's status table records restricted power
series and strong noetherianness as existing AINTLIB material but lists no Huber structure on
them, and no Tau Ceti module for `A⟨X⟩_T` supplies a `PairOfDefinition`. The coefficient
decomposition reuses `TauCeti.Huber.exists_sum_eq_of_mem_span_mul`, which was written for Wedhorn
Remark 6.8 — the Huber structure on the completion `Â` — and serves the same purpose here: it
bounds, uniformly in the level, the number of generators a decomposition needs.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48 for `A⟨X⟩_T`, Example
  5.54 for the trivial weight, and Proposition and Definition 6.1 for pairs of definition.
-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The `M`-combinations of a finite family `g` in `A`: the additive subgroup of the elements
`∑ z ∈ G, g z * c z` with every `c z ∈ M`.

Phrasing the target of the coefficient decomposition as a subgroup is what lets
`TauCeti.Huber.weightMul_le` reduce decomposing an element of `Tν · Iⁿ⁺¹` to decomposing the
products `t * y` that generate it. -/
private def combSubgroup {ι : Type*} (G : Finset ι) (g : ι → A) (M : AddSubgroup A) :
    AddSubgroup A where
  carrier := {x | ∃ c : ι → A, (∀ z, c z ∈ M) ∧ ∑ z ∈ G, g z * c z = x}
  zero_mem' := ⟨0, fun _ ↦ M.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, fun z ↦ M.add_mem (hc z) (hd z), by simp [mul_add, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨-c, fun z ↦ M.neg_mem (hc z), by simp⟩

namespace PairOfDefinition

/-! ### The coefficient decomposition -/

/-- **One weighted coefficient, decomposed.** The same decomposition through the weight: an
element of `Tν · Iⁿ⁺¹` is a combination of the generators with cofactors in `Tν · Iⁿ`.

The weight is carried by the cofactors, which is what keeps the decomposition inside the
neighbourhood subgroup indexed by the same `ν`. -/
theorem exists_sum_eq_of_mem_weightMul_idealImage_succ (P : PairOfDefinition A)
    {T : Fin k → Set A} {G : Finset P.ringOfDefinition}
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition) (n : ℕ)
    (ν : Fin k →₀ ℕ) {x : A} (hx : x ∈ weightMul T ν (P.idealImage (n + 1))) :
    ∃ c : P.ringOfDefinition → A,
      (∀ z, c z ∈ weightMul T ν (P.idealImage n)) ∧ ∑ z ∈ G, (z : A) * c z = x := by
  have hle : weightMul T ν (P.idealImage (n + 1))
      ≤ combSubgroup G (fun z : P.ringOfDefinition ↦ (z : A))
          (weightMul T ν (P.idealImage n)) := by
    refine weightMul_le.mpr fun t ht y hy ↦ ?_
    obtain ⟨c, hc, hsum⟩ := P.exists_sum_eq_of_mem_idealImage_succ hG n hy
    refine ⟨fun z ↦ t * c z, fun z ↦ mul_mem_weightMul T ν _ ht (hc z), ?_⟩
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  exact hle hx

section Nonarchimedean

variable [NonarchimedeanRing A] {T : Fin k → Set A}

/-- **The level of each coefficient.** For a series all of whose coefficients meet the `Iⁿ` bound
there is a function `m` such that the coefficient at `ν` meets the sharper bound at level
`n + m ν`, and such that every sublevel set `{ν; m ν < M}` is finite.

This is the choice the reverse inclusion of
`TauCeti.Huber.PairOfDefinition.weightedIdeal_one_pow` runs on: decomposing each coefficient at
its own level rather than at the uniform level `n` is what makes the cofactors tend to zero, hence
restricted. The level is the largest admissible one bounded by the degree of `ν`, so it is
attained; the degree cut-off is what keeps the sublevel sets finite even for coefficients lying in
every power of `I`. -/
private theorem exists_level (P : PairOfDefinition A) {hT : IsWeightFamily T} (n : ℕ)
    {f : weightedRestrictedSubring T hT} (hf : f ∈ weightedNhd T hT (P.idealImage n)) :
    ∃ m : (Fin k →₀ ℕ) → ℕ,
      (∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)
        ∈ weightMul T ν (P.idealImage (n + m ν))) ∧
      ∀ M : ℕ, {ν | m ν < M}.Finite := by
  classical
  set S : (Fin k →₀ ℕ) → Finset ℕ := fun ν ↦ (Finset.range (ν.degree + 1)).filter
    fun j ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)
      ∈ weightMul T ν (P.idealImage (n + j)) with hS
  have hzero : ∀ ν, 0 ∈ S ν := fun ν ↦ by simpa [hS] using mem_weightedNhd.mp hf ν
  refine ⟨fun ν ↦ (S ν).max' ⟨0, hzero ν⟩, fun ν ↦ ?_, fun M ↦ ?_⟩
  · have hmax : (S ν).max' ⟨0, hzero ν⟩ ∈ S ν := (S ν).max'_mem _
    exact (Finset.mem_filter.mp hmax).2
  · -- a coefficient of level below `M` either sits in low degree or fails the `Iⁿ⁺ᴹ` bound
    refine ((Finsupp.finite_of_degree_lt M).union
      ((mem_weightedRestrictedSubring.mp f.2).finite_coeff_notMem
        ⟨P.idealImage (n + M), P.isOpen_idealImage (n + M)⟩)).subset ?_
    intro ν hν
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_not] at hcon
    have hmem : M ∈ S ν :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hcon.1), hcon.2⟩
    exact absurd ((S ν).le_max' M hmem) (by simpa using hν)

/-! ### The pair of definition of `A⟨X⟩_T` -/

/-- `A₀⟨X⟩_T`, the **ring of definition of `A⟨X⟩_T`**: the series all of whose coefficients meet
the `A₀` bound.

Its carrier is the neighbourhood subgroup `TauCeti.Huber.weightedNhd` of `A₀`, which is what makes
it open; that it is a subring is coefficientwise multiplicativity of `A₀`. -/
def weightedRingOfDefinition (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    Subring (weightedRestrictedSubring T hT) where
  carrier := weightedNhd T hT P.ringOfDefinition.toAddSubgroup
  zero_mem' := (weightedNhd T hT P.ringOfDefinition.toAddSubgroup).zero_mem
  one_mem' := by
    have h := weightedC_mem_weightedNhd hT (U := P.ringOfDefinition.toAddSubgroup)
      P.ringOfDefinition.one_mem
    rwa [map_one] at h
  add_mem' hf hg := (weightedNhd T hT P.ringOfDefinition.toAddSubgroup).add_mem hf hg
  neg_mem' hf := (weightedNhd T hT P.ringOfDefinition.toAddSubgroup).neg_mem hf
  mul_mem' hf hg := mul_mem_weightedNhd
    (Set.mul_subset_iff.mpr fun _ ha _ hb ↦ P.ringOfDefinition.mul_mem ha hb) hf hg

/-- Membership in `A₀⟨X⟩_T` is the `A₀` bound on every coefficient. -/
@[simp]
theorem mem_weightedRingOfDefinition (P : PairOfDefinition A) (hT : IsWeightFamily T)
    {f : weightedRestrictedSubring T hT} :
    f ∈ P.weightedRingOfDefinition hT ↔ f ∈ weightedNhd T hT P.ringOfDefinition.toAddSubgroup :=
  (Iff.rfl)

/-- The constant series `A₀ → A₀⟨X⟩_T`, the structure map of the ring of definition. -/
noncomputable def weightedRingOfDefinitionC (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    P.ringOfDefinition →+* P.weightedRingOfDefinition hT :=
  ((weightedC T hT).comp P.ringOfDefinition.subtype).codRestrict _ fun a ↦
    weightedC_mem_weightedNhd hT a.2

@[simp]
theorem coe_weightedRingOfDefinitionC (P : PairOfDefinition A) (hT : IsWeightFamily T)
    (a : P.ringOfDefinition) :
    ((P.weightedRingOfDefinitionC hT a : P.weightedRingOfDefinition hT) :
      weightedRestrictedSubring T hT) = weightedC T hT (a : A) := (rfl)

/-- `Iⁿ⟨X⟩_T`, an **ideal of `A₀⟨X⟩_T`**: the series all of whose coefficients meet the `Iⁿ`
bound. The ideal of definition of `A⟨X⟩_T` is the case `n = 1`; the general `n` is named because
the point of the file is that these are its powers
(`TauCeti.Huber.PairOfDefinition.weightedIdeal_one_pow`). -/
def weightedIdeal (P : PairOfDefinition A) (hT : IsWeightFamily T) (n : ℕ) :
    Ideal (P.weightedRingOfDefinition hT) where
  carrier := {f | (f : weightedRestrictedSubring T hT) ∈ weightedNhd T hT (P.idealImage n)}
  zero_mem' := (weightedNhd T hT (P.idealImage n)).zero_mem
  add_mem' hf hg := (weightedNhd T hT (P.idealImage n)).add_mem hf hg
  smul_mem' c f hf := mem_weightedNhd.mpr fun ν ↦ by
    refine weightMul_mono T ν ((AddSubgroup.closure_le _).mpr ?_)
      (coeff_mul_mem_weightMul (T := T) (V := P.ringOfDefinition.toAddSubgroup)
        (W := P.idealImage n) (mem_weightedNhd.mp ((P.mem_weightedRingOfDefinition hT).mp c.2))
        (mem_weightedNhd.mp hf) ν)
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact P.mul_mem_idealImage ha hx

/-- Membership in `Iⁿ⟨X⟩_T` is the `Iⁿ` bound on every coefficient. -/
@[simp]
theorem mem_weightedIdeal (P : PairOfDefinition A) (hT : IsWeightFamily T) (n : ℕ)
    {f : P.weightedRingOfDefinition hT} :
    f ∈ P.weightedIdeal hT n ↔
      (f : weightedRestrictedSubring T hT) ∈ weightedNhd T hT (P.idealImage n) := (Iff.rfl)

/-- A constant series with value in `Iⁿ` lies in `Iⁿ⟨X⟩_T`. -/
theorem weightedRingOfDefinitionC_mem_weightedIdeal (P : PairOfDefinition A)
    (hT : IsWeightFamily T) {n : ℕ} {a : P.ringOfDefinition} (ha : (a : A) ∈ P.idealImage n) :
    P.weightedRingOfDefinitionC hT a ∈ P.weightedIdeal hT n :=
  weightedC_mem_weightedNhd hT ha

/-- At `n = 0` the bound is the `A₀` bound, so `I⁰⟨X⟩_T` is all of `A₀⟨X⟩_T`. -/
@[simp]
theorem weightedIdeal_zero (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    P.weightedIdeal hT 0 = ⊤ := by
  refine eq_top_iff.mpr fun f _ ↦ mem_weightedNhd.mpr fun ν ↦ ?_
  refine weightMul_mono T ν (fun x hx ↦ ?_)
    (mem_weightedNhd.mp ((P.mem_weightedRingOfDefinition hT).mp f.2) ν)
  exact (P.mem_idealImage 0).mpr ⟨⟨x, hx⟩, by simp, rfl⟩

/-- The bounds are nested: `Iⁿ⟨X⟩_T ⊆ Iᵐ⟨X⟩_T` for `m ≤ n`. -/
theorem weightedIdeal_anti (P : PairOfDefinition A) (hT : IsWeightFamily T)
    {m n : ℕ} (h : m ≤ n) : P.weightedIdeal hT n ≤ P.weightedIdeal hT m := fun _ hf ↦
  mem_weightedNhd.mpr fun ν ↦
    weightMul_mono T ν (P.idealImage_anti h) (mem_weightedNhd.mp hf ν)

/-- The bounds multiply: `Iᵃ⟨X⟩_T · Iᵇ⟨X⟩_T ⊆ Iᵃ⁺ᵇ⟨X⟩_T`. This is one half of
`TauCeti.Huber.PairOfDefinition.weightedIdeal_one_pow`, and needs no finiteness. -/
theorem weightedIdeal_mul_le (P : PairOfDefinition A) (hT : IsWeightFamily T) (a b : ℕ) :
    P.weightedIdeal hT a * P.weightedIdeal hT b ≤ P.weightedIdeal hT (a + b) := by
  refine Ideal.mul_le.mpr fun f hf g hg ↦ mem_weightedNhd.mpr fun ν ↦ ?_
  refine weightMul_mono T ν ((AddSubgroup.closure_le _).mpr ?_)
    (coeff_mul_mem_weightMul (T := T) (V := P.idealImage a) (W := P.idealImage b)
      (mem_weightedNhd.mp hf) (mem_weightedNhd.mp hg) ν)
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact P.mul_mem_idealImage_add hx hy

/-- **The decomposition of a series.** A series all of whose coefficients meet the `Iⁿ⁺¹` bound is
a combination, with cofactors in `Iⁿ⟨X⟩_T`, of the constant series attached to a finite generating
set `G` of `I`.

This is the mathematical content of the file. The cofactors are restricted series because each
coefficient is decomposed at the level it attains; decomposing every coefficient at the uniform
level `n + 1` would leave the cofactors with no reason to tend to zero. -/
theorem exists_sum_weightedRingOfDefinitionC_mul (P : PairOfDefinition A) (hT : IsWeightFamily T)
    {G : Finset P.ringOfDefinition}
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition) (n : ℕ)
    {f : P.weightedRingOfDefinition hT} (hf : f ∈ P.weightedIdeal hT (n + 1)) :
    ∃ g : P.ringOfDefinition → P.weightedRingOfDefinition hT,
      (∀ z, g z ∈ P.weightedIdeal hT n) ∧
        f = ∑ z ∈ G, P.weightedRingOfDefinitionC hT z * g z := by
  classical
  obtain ⟨m, hm, hmfin⟩ := P.exists_level (n + 1) hf
  -- decompose the coefficient at `ν` at the level `n + m ν` it attains
  have key : ∀ ν, ∃ c : P.ringOfDefinition → A,
      (∀ z, c z ∈ weightMul T ν (P.idealImage (n + m ν))) ∧
        ∑ z ∈ G, (z : A) * c z
          = MvPowerSeries.coeff ν ((f : weightedRestrictedSubring T hT) :
              MvPowerSeries (Fin k) A) := by
    intro ν
    refine P.exists_sum_eq_of_mem_weightMul_idealImage_succ hG (n + m ν) ν ?_
    have hlevel : n + 1 + m ν = n + m ν + 1 := by omega
    exact hlevel ▸ hm ν
  choose c hc hcsum using key
  -- name the cofactor series, characterised by its coefficients
  obtain ⟨s, hs⟩ : ∃ s : P.ringOfDefinition → MvPowerSeries (Fin k) A,
      ∀ z ν, MvPowerSeries.coeff ν (s z) = c ν z := ⟨fun z ν ↦ c ν z, fun _ _ ↦ rfl⟩
  -- the cofactors are restricted series, since their coefficients tend to zero with the level
  have hres : ∀ z, IsWeightedRestricted T (s z) := by
    refine fun z ↦ isWeightedRestricted_iff.mpr fun U ↦ ?_
    obtain ⟨M, -, hM⟩ := P.hasBasis_nhds_zero.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
    rw [Filter.eventually_cofinite]
    refine (hmfin M).subset fun ν hν ↦ ?_
    simp only [Set.mem_ofPred_eq] at hν ⊢
    by_contra hle
    refine hν ?_
    rw [hs]
    refine weightMul_mono T ν ?_ (hc ν z)
    exact le_trans (P.idealImage_anti (by omega))
      fun x hx ↦ SetLike.mem_coe.mp (hM (SetLike.mem_coe.mpr hx))
  -- the cofactors, as elements of `Iⁿ⟨X⟩_T`
  obtain ⟨g, hgcoe, hgmem⟩ : ∃ g : P.ringOfDefinition → P.weightedRingOfDefinition hT,
      (∀ z, ((g z : weightedRestrictedSubring T hT) : MvPowerSeries (Fin k) A) = s z) ∧
        ∀ z, g z ∈ P.weightedIdeal hT n := by
    have hmem : ∀ z ν, MvPowerSeries.coeff ν (s z) ∈ weightMul T ν (P.idealImage n) := fun z ν ↦ by
      rw [hs]
      exact weightMul_mono T ν
        (P.idealImage_anti (Nat.le_add_right n (m ν))) (hc ν z)
    exact ⟨fun z ↦ ⟨⟨s z, mem_weightedRestrictedSubring.mpr (hres z)⟩,
      mem_weightedNhd.mpr fun ν ↦
        weightMul_mono T ν (P.idealImage_le_ringOfDefinition n) (hmem z ν)⟩,
      fun _ ↦ rfl, fun z ↦ mem_weightedNhd.mpr (hmem z)⟩
  -- `f` is the corresponding combination, checked coefficientwise
  have hcoe : (((∑ z ∈ G, P.weightedRingOfDefinitionC hT z * g z :
      P.weightedRingOfDefinition hT) : weightedRestrictedSubring T hT) :
      MvPowerSeries (Fin k) A)
      = ∑ z ∈ G, MvPowerSeries.C (z : A) * s z := by
    push_cast
    exact Finset.sum_congr rfl fun z _ ↦ by
      rw [hgcoe, coe_weightedRingOfDefinitionC, coe_weightedC]
  refine ⟨g, hgmem, Subtype.ext (Subtype.ext (MvPowerSeries.ext fun ν ↦ ?_))⟩
  rw [hcoe, map_sum]
  refine (hcsum ν).symm.trans (Finset.sum_congr rfl fun z _ ↦ ?_)
  rw [MvPowerSeries.coeff_C_mul, hs]

/-- The reverse inclusion of `TauCeti.Huber.PairOfDefinition.weightedIdeal_one_pow`, read off the
decomposition `TauCeti.Huber.PairOfDefinition.exists_sum_weightedRingOfDefinitionC_mul`. -/
theorem weightedIdeal_succ_le_mul (P : PairOfDefinition A) (hT : IsWeightFamily T) (n : ℕ) :
    P.weightedIdeal hT (n + 1) ≤ P.weightedIdeal hT 1 * P.weightedIdeal hT n := by
  obtain ⟨G, hG⟩ := P.fg_idealOfDefinition
  intro f hf
  obtain ⟨g, hg, rfl⟩ := P.exists_sum_weightedRingOfDefinitionC_mul hT hG n hf
  refine Ideal.sum_mem _ fun z hz ↦ Ideal.mul_mem_mul ?_ (hg z)
  refine P.weightedRingOfDefinitionC_mem_weightedIdeal hT ((P.mem_idealImage 1).mpr ⟨z, ?_, rfl⟩)
  rw [pow_one, ← hG]
  exact Ideal.subset_span hz

/-- **The neighbourhood subgroups are the powers of one ideal**: `(I⟨X⟩_T) ^ n = Iⁿ⟨X⟩_T`.

Both inclusions go by induction on `n`, the step being
`TauCeti.Huber.PairOfDefinition.weightedIdeal_mul_le` one way and
`TauCeti.Huber.PairOfDefinition.weightedIdeal_succ_le_mul` the other. -/
theorem weightedIdeal_one_pow (P : PairOfDefinition A) (hT : IsWeightFamily T) (n : ℕ) :
    P.weightedIdeal hT 1 ^ n = P.weightedIdeal hT n := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_antisymm ?_ ?_
    · calc P.weightedIdeal hT 1 ^ (n + 1) = P.weightedIdeal hT 1 * P.weightedIdeal hT n := by
            rw [pow_succ', ih]
        _ ≤ P.weightedIdeal hT (1 + n) := P.weightedIdeal_mul_le hT 1 n
        _ = P.weightedIdeal hT (n + 1) := by rw [Nat.add_comm]
    · calc P.weightedIdeal hT (n + 1)
          ≤ P.weightedIdeal hT 1 * P.weightedIdeal hT n := P.weightedIdeal_succ_le_mul hT n
        _ = P.weightedIdeal hT 1 ^ (n + 1) := by rw [pow_succ', ih]

/-- **The ideal of definition is finitely generated**: `I⟨X⟩_T` is generated by the constant series
attached to a finite generating set of `I`.

The generators lie in the ideal, and the reverse containment is the decomposition of a series at
`n = 0`, where the cofactors are unconstrained. -/
theorem fg_weightedIdeal_one (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    (P.weightedIdeal hT 1).FG := by
  classical
  obtain ⟨G, hG⟩ := P.fg_idealOfDefinition
  refine ⟨G.image (P.weightedRingOfDefinitionC hT), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro _ hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    refine P.weightedRingOfDefinitionC_mem_weightedIdeal hT ((P.mem_idealImage 1).mpr ⟨z, ?_, rfl⟩)
    rw [pow_one, ← hG]
    exact Ideal.subset_span hz
  · intro f hf
    obtain ⟨g, -, rfl⟩ := P.exists_sum_weightedRingOfDefinitionC_mul hT hG 0 (by simpa using hf)
    refine Ideal.sum_mem _ fun z hz ↦ Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)

/-! ### The Huber and Tate structures -/

/-- `A₀⟨X⟩_T` is open in `A⟨X⟩_T`. -/
theorem isOpen_weightedRingOfDefinition (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    IsOpen (P.weightedRingOfDefinition hT : Set (weightedRestrictedSubring T hT)) :=
  isOpen_weightedNhd hT P.isOpen_ringOfDefinition

/-- Each `Iⁿ⟨X⟩_T` is open in `A₀⟨X⟩_T`. -/
theorem isOpen_weightedIdeal (P : PairOfDefinition A) (hT : IsWeightFamily T) (n : ℕ) :
    IsOpen ((P.weightedIdeal hT n : Ideal (P.weightedRingOfDefinition hT)) :
      Set (P.weightedRingOfDefinition hT)) :=
  (isOpen_weightedNhd hT (P.isOpen_idealImage n)).preimage continuous_subtype_val

/-- **The subspace topology on `A₀⟨X⟩_T` is the `I⟨X⟩_T`-adic topology.**

The powers of `I⟨X⟩_T` are the neighbourhood subgroups by
`TauCeti.Huber.PairOfDefinition.weightedIdeal_one_pow`, and those are cofinal among the
neighbourhoods of zero because the `Iⁿ` are cofinal in `A`. -/
theorem isAdic_weightedIdeal_one (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    IsAdic (P.weightedIdeal hT 1) := by
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [P.weightedIdeal_one_pow hT n]
    exact P.isOpen_weightedIdeal hT n
  · rw [nhds_induced (Subtype.val : P.weightedRingOfDefinition hT → _),
      Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [ZeroMemClass.coe_zero] at ht
    obtain ⟨U, -, hU⟩ := (hasBasis_nhds_zero_weightedTopology hT).mem_iff.mp ht
    obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
    refine ⟨n, fun f hf ↦ hts ?_⟩
    rw [P.weightedIdeal_one_pow hT n] at hf
    refine hU (mem_weightedNhd.mpr fun ν ↦ weightMul_mono T ν (fun x hx ↦ ?_)
      (mem_weightedNhd.mp hf ν))
    exact SetLike.mem_coe.mp (hn (SetLike.mem_coe.mpr hx))

/-- **The pair of definition of `A⟨X⟩_T`**: `(A₀⟨X⟩_T, I⟨X⟩_T)`. -/
def weighted (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    PairOfDefinition (weightedRestrictedSubring T hT) where
  ringOfDefinition := P.weightedRingOfDefinition hT
  isOpen_ringOfDefinition := P.isOpen_weightedRingOfDefinition hT
  idealOfDefinition := P.weightedIdeal hT 1
  fg_idealOfDefinition := P.fg_weightedIdeal_one hT
  isAdic_idealOfDefinition := P.isAdic_weightedIdeal_one hT

@[simp]
theorem weighted_ringOfDefinition (P : PairOfDefinition A) (hT : IsWeightFamily T) :
    (P.weighted hT).ringOfDefinition = P.weightedRingOfDefinition hT := (rfl)

/-- Membership in the ideal of definition of the pair `(A₀⟨X⟩_T, I⟨X⟩_T)` is membership in
`I⟨X⟩_T`.

Stated as a membership characterisation rather than an equation because the type of
`idealOfDefinition` depends on `ringOfDefinition`, exactly as
`TauCeti.Huber.PairOfDefinition.mem_completion_idealOfDefinition` is. -/
@[simp]
theorem mem_weighted_idealOfDefinition (P : PairOfDefinition A) (hT : IsWeightFamily T)
    {f : (P.weighted hT).ringOfDefinition} :
    f ∈ (P.weighted hT).idealOfDefinition ↔
      (⟨f, by rw [← weighted_ringOfDefinition P hT]; exact f.2⟩ :
        P.weightedRingOfDefinition hT) ∈ P.weightedIdeal hT 1 := (Iff.rfl)

end Nonarchimedean

end PairOfDefinition

section Instances

variable {T : Fin k → Set A} {hT : IsWeightFamily T}

/-- **`A⟨X⟩_T` is a Huber ring** when `A` is: a pair of definition of `A` gives one of `A⟨X⟩_T`, by
`TauCeti.Huber.PairOfDefinition.weighted`. -/
instance isHuberRing_weightedRestrictedSubring [IsTopologicalRing A] [IsHuberRing A] :
    IsHuberRing (weightedRestrictedSubring T hT) :=
  ⟨IsHuberRing.nonempty_pairOfDefinition.elim fun P ↦ ⟨P.weighted hT⟩⟩

/-- **`A⟨X⟩_T` is a Tate ring** when `A` is: a pseudouniformiser of `A` is one of `A⟨X⟩_T` as a
constant series, a unit there and topologically nilpotent by continuity of `weightedC`. -/
instance isTateRing_weightedRestrictedSubring [IsTopologicalRing A] [IsTateRing A] :
    IsTateRing (weightedRestrictedSubring T hT) where
  exists_isPseudoUniformizer := by
    obtain ⟨a, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
    exact ⟨weightedC T hT a, isPseudoUniformizer_iff.mpr
      ⟨ha.isUnit.map (weightedC T hT),
        ha.isTopologicallyNilpotent.map (continuous_weightedC hT)⟩⟩

-- The completed algebra `A⟨X₁,…,Xₖ⟩` of the roadmap — the separated completion of the
-- trivial-weight `A⟨X⟩_T` — needs no result of its own: the instances above and
-- `TauCeti.Huber.IsHuberRing.completion` / `TauCeti.Huber.IsTateRing.completion` already give it
-- by synthesis, which these two `example`s record.
example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsHuberRing A] : IsHuberRing (restrictedMvPowerSeriesCompletion k A) := inferInstance

example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsTateRing A] : IsTateRing (restrictedMvPowerSeriesCompletion k A) := inferInstance

end Instances

end TauCeti.Huber
