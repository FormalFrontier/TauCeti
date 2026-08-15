/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# The localisation topology: the universal property

A ring homomorphism out of `Aₛ` is continuous as soon as its restriction along `algebraMap` is and
the fractions `t/s` go to power-bounded elements; and `Aₛ` is the universal such target. This is
the second half of Wedhorn's Proposition and Definition 5.51.

The construction of the topology is in `LocalizationTopology.Basic`, and the completion `A⟨T/s⟩`
in `LocalizationTopology.Completion`.

The power-boundedness prerequisites this needs — `isPowerBounded_of_mem_locSubring` and
`isPowerBounded_divBy`, which say every element of `D`, in particular each fraction `t/s`, is
power-bounded — are in `LocalizationTopology.Basic` and imported from there.

## Main results

* `continuous_of_continuous_algebraMap_of_isPowerBounded`: a sufficient criterion for a ring
  homomorphism out of `Aₛ` to be continuous. The converse is not proved here.
* `existsUnique_continuous_ringHom_locTopology`: the universal property — a continuous
  `φ : A →+* B` inverting `s` and sending each `t/s` to a power-bounded element extends to `Aₛ` in
  exactly one continuous way.

## Provenance

The declarations here are relocated from the AINTLIB port recorded in
`LocalizationTopology.Basic`; see that module's Provenance section for the source file and
commit. This module adds no new mathematics.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §5.6
-/

open Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-! ### A sufficient criterion for continuity -/

/-- Along `algebraMap`, some power of the ideal of definition multiplies the image of `A₀` into
any prescribed open subgroup of `B`. This is the `A₀`-level base case of
`exists_pow_mul_locSubring_mem`. -/
private theorem exists_pow_mul_algebraMap_mem {B : Type*} [Ring B] [TopologicalSpace B]
    (P : PairOfDefinition A)
    (S : Type*) [Ring S] [Algebra A S] (f : S →+* B)
    (hf : Continuous (f.comp (algebraMap A S))) (G : OpenAddSubgroup B) :
    ∃ m : ℕ, ∀ x ∈ P.ringOfDefinition.map (algebraMap A S),
      ∀ b ∈ P.idealOfDefinition ^ m,
        f (x * algebraMap A S (b : A)) ∈ (G : Set B) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ b ∈ P.idealOfDefinition ^ m,
      f (algebraMap A S (b : A)) ∈ (G : Set B) := by
    have hcont : Filter.Tendsto (f.comp (algebraMap A S)) (𝓝 0) (𝓝 0) := by
      rw [← map_zero (f.comp (algebraMap A S))]
      exact hf.continuousAt
    obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hcont (G.isOpen.mem_nhds G.zero_mem))
    exact ⟨n, fun b hb ↦ hn ((P.mem_idealImage n).mpr ⟨b, hb, rfl⟩)⟩
  refine ⟨m, ?_⟩
  rintro _ ⟨a₀, ha₀, rfl⟩ b hb
  rw [← map_mul (algebraMap A S)]
  exact hm ⟨(a₀ : A) * (b : A), P.ringOfDefinition.mul_mem ha₀ b.property⟩
    (Ideal.mul_mem_left _ ⟨a₀, ha₀⟩ hb)

/-- The same statement with `A₀` replaced by all of `D = A₀[t₁/s, …, tₙ/s]`. This is where
power-boundedness of the fractions enters: the induction adjoins one `t/s` at a time and writes an
element of the larger ring as a polynomial in it, whose powers a bounded set absorbs.

Stated over an arbitrary `U : Finset A` rather than the `T` of the theorem that uses it, because
that is what the `Finset.induction` needs. -/
private theorem exists_pow_mul_locSubring_mem {B : Type*} [Ring B] [TopologicalSpace B]
    [NonarchimedeanRing B] (P : PairOfDefinition A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (f : S →+* B)
    (hf : Continuous (f.comp (algebraMap A S))) (U : Finset A) :
    (∀ t ∈ U, IsPowerBounded (f (divBy t s))) →
      ∀ G : OpenAddSubgroup B, ∃ m : ℕ, ∀ x ∈ locSubring P U s S,
        ∀ b ∈ P.idealOfDefinition ^ m,
          f (x * algebraMap A S (b : A)) ∈ (G : Set B) := by
  classical
  induction U using Finset.induction with
  | empty =>
    intro _ G
    obtain ⟨m, hm⟩ := exists_pow_mul_algebraMap_mem P S f hf G
    exact ⟨m, fun x hx b hb ↦ hm x (locSubring_empty P s S ▸ hx) b hb⟩
  | insert t U' ht ih =>
    intro hpowU G
    obtain ⟨V, hV, hzV⟩ := isBounded_iff.mp (isPowerBounded_iff.mp
      (hpowU t (Finset.mem_insert_self t U'))) (G : Set B) (G.isOpen.mem_nhds G.zero_mem)
    obtain ⟨W, hWV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
    obtain ⟨m, hm⟩ := ih (fun t' ht' ↦ hpowU t' (Finset.mem_insert_of_mem ht')) W
    refine ⟨m, fun x hx b hb ↦ ?_⟩
    -- Write `x` as a polynomial in `t/s` with coefficients in the smaller subring: that is
    -- exactly what the insertion formula says `x` is a member of.
    have hx_adj : x ∈ Algebra.adjoin (locSubring P U' s S) ({divBy t s} : Set S) :=
      (locSubring_insert P t U' s S).le hx
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx_adj
    obtain ⟨p, hp⟩ := hx_adj
    rw [← hp, Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
    refine G.toAddSubgroup.sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def, Algebra.algebraMap_ofSubsemiring_apply, mul_right_comm,
      map_mul, map_pow]
    exact hzV (Set.mul_mem_mul (hWV (hm _ (p.coeff i).property b hb)) ⟨i, rfl⟩)

/-- If `f` sends every `x · b` with `x ∈ D` and `b ∈ Iᵐ` into `W`, then it sends `r · d` into `W`
for every `r ∈ D` and every `d` in the `D`-span of the image of `Iᵐ`. `W` is an arbitrary additive
subgroup. -/
private theorem map_mul_mem_of_mem_span_locIdeal_pow {B : Type*} [Ring B]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (f : S →+* B) (W : AddSubgroup B) {m : ℕ}
    (hm : ∀ x ∈ locSubring P T s S, ∀ b ∈ P.idealOfDefinition ^ m,
      f (x * algebraMap A S (b : A)) ∈ (W : Set B))
    {d : locSubring P T s S}
    (hd : d ∈ Ideal.span (toLocSubring P T s S ''
      ((P.idealOfDefinition ^ m : Ideal P.ringOfDefinition) : Set P.ringOfDefinition))) :
    ∀ r : locSubring P T s S, f ((locSubring P T s S).subtype (r * d)) ∈ (W : Set B) := by
  refine Submodule.span_induction (p := fun d _ ↦ ∀ r : locSubring P T s S,
    f ((locSubring P T s S).subtype (r * d)) ∈ (W : Set B)) ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨b, hb, rfl⟩ r
    rw [Subring.coe_subtype, MulMemClass.coe_mul, toLocSubring_apply]
    exact hm r.val r.property b hb
  · intro r
    simp
  · intro d₁ d₂ _ _ h₁ h₂ r
    rw [mul_add, map_add, map_add]
    exact W.add_mem (h₁ r) (h₂ r)
  · intro c d _ hd r
    rw [smul_eq_mul, ← mul_assoc]
    exact hd (r * c)

/-- A ring homomorphism out of `Aₛ` is continuous for the localisation topology as soon as its
restriction along `algebraMap` is continuous and the fractions `t/s` are sent to power-bounded
elements. This is a sufficient criterion only; no converse is proved here.

The second hypothesis does real work rather than following from the first: `D` is generated over
`A₀` by exactly those fractions, so continuity of `f ∘ algebraMap` alone says nothing about the
image of `D`. -/
theorem continuous_of_continuous_algebraMap_of_isPowerBounded {B : Type*}
    [Ring B] [TopologicalSpace B] [NonarchimedeanRing B] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (f : S →+* B)
    (hf : Continuous (f.comp (algebraMap A S)))
    (hpow : ∀ t ∈ T, IsPowerBounded (f (divBy t s))) :
    @Continuous _ _ (locTopology P T s S hden) _ f := by
  have hfull := exists_pow_mul_locSubring_mem P s S f hf T hpow
  let _ : TopologicalSpace S := locTopology P T s S hden
  have : IsTopologicalRing S := isTopologicalRing_locTopology P T s S hden
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro V hV
  obtain ⟨W, hWV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  obtain ⟨m, hm⟩ := hfull W
  refine Filter.mem_of_superset
    ((hasBasis_nhds_zero_locTopology P T s S hden).mem_iff.mpr ⟨m, trivial, le_refl _⟩) ?_
  intro x hx
  obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T s S m).mp hx
  refine hWV ?_
  rw [locIdeal_pow_eq_span] at hd
  simpa using map_mul_mem_of_mem_span_locIdeal_pow P T s S f W.toAddSubgroup hm hd 1


/-! ### The universal property -/

/-- **Wedhorn 5.51, the universal property of `Aₛ` under `locTopology`.** A ring homomorphism
`φ : A →+* B` into a nonarchimedean ring extends to `Aₛ` in exactly one continuous way, provided
`φ` is continuous, `φ s` is a unit, and each fraction `φ t / φ s` is power-bounded.

The condition on the fractions is stated as sufficient, and only that. It is *not* forced by
continuity: a continuous ring homomorphism need not carry power-bounded elements to power-bounded
elements — `IsBounded.image` in `Huber/Bounded.lean` is stated for the image under a map, and
`IsBounded.image_of_isOpenMap` needs openness on top, precisely because continuity alone does not
suffice. Whether some weaker condition is also necessary is not addressed here.

The map itself is Mathlib's `IsLocalization.Away.lift`, which is purely algebraic and needs no
topology; the topology's contribution is that this lift is *continuous*, supplied by
`continuous_of_continuous_algebraMap_of_isPowerBounded`. Uniqueness is
`IsLocalization.ringHom_ext` and is algebraic too: a homomorphism out of a localisation is already
determined by its restriction along `algebraMap`, so nothing topological enters there. -/
theorem existsUnique_continuous_ringHom_locTopology {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {φ : A →+* B} (hφ : ContinuousAt φ 0) (hs : IsUnit (φ s))
    (hpow : ∀ t ∈ T, IsPowerBounded (φ t * ↑hs.unit⁻¹)) :
    letI := locTopology P T s S hden
    ∃! f : S →+* B, Continuous f ∧ f.comp (algebraMap A S) = φ := by
  let _ := locTopology P T s S hden
  refine ⟨IsLocalization.Away.lift s hs, ⟨?_, IsLocalization.Away.lift_comp s hs⟩, ?_⟩
  · refine continuous_of_continuous_algebraMap_of_isPowerBounded P T s S hden _ ?_ ?_
    · rw [IsLocalization.Away.lift_comp s hs]; exact continuous_of_continuousAt_zero φ hφ
    · intro t ht
      have : IsLocalization.Away.lift s hs ((divBy t s : S)) = φ t * ↑hs.unit⁻¹ := by
        rw [divBy_def, IsLocalization.Away.lift, IsLocalization.lift_mk']
        congr 2
      rw [this]; exact hpow t ht
  · rintro g ⟨-, hg⟩
    exact IsLocalization.ringHom_ext (Submonoid.powers s)
      (hg.trans (IsLocalization.Away.lift_comp s hs).symm)

end PairOfDefinition

end

end TauCeti.Huber
