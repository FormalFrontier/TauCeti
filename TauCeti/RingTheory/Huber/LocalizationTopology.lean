/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Localization.Away
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import TauCeti.RingTheory.Huber.Basic

/-!
# Localization Topology for Huber Rings

We construct the non-archimedean ring topology on a localisation `S` of `A` away from an
element `s`, following Proposition and Definition 5.51, §5.6, of Wedhorn's *Adic Spaces*. The
carrier is an arbitrary `IsLocalization.Away s S` rather than the concrete `Localization.Away s`,
so a consumer holding `A[1/s]` in another presentation can use the topology directly.

## Main definitions

* `locSubring P T s S` : the candidate ring of definition `D = A₀[t₁/s, …, tₙ/s]`.
* `HasDenominatorPower P T s S` : the standing hypothesis the construction runs under — some power
  of `I` has all of its fractions `b/s` already in `D`.
* `locIdeal P T s S` : the candidate ideal of definition `J = I · D` in `D`.
* `locIdealImage P T s S n` : The `n`-th neighborhood `image(Jⁿ)` in `Aₛ`.

## Main results

* `hasDenominatorPower_of_pow_le_span`: the standing hypothesis holds whenever some power of `I`
  lies in `s · A₀`.
* `locSubring_le_iff`, with `locSubring_empty` and `locSubring_mono`: the universal property of
  `D` and the two consequences of it this file needs.
* `locIdeal_pow`, `locIdeal_pow_eq_span`, `toLocSubring_mem_locIdeal_pow` and
  `algebraMap_mem_locIdealImage`: the characteristic lemmas for the powers of `J` and their images,
  which stand in for unfolding `locIdeal` (whose body is not exported).
* `locIdealImage_antitone`: Neighborhoods are antitone.
* `locIdealImage_preimage_eq_locIdeal_pow`: the image and preimage along the subtype embedding are
  inverse on `Jⁿ`. Identifying the subspace topology on `D` with its `J`-adic topology is a
  separate result and is not proved here.
* `locIdealImage_mul_subset_add`: the basis is graded,
  `locIdealImage i * locIdealImage j ⊆ locIdealImage (i + j)`; `locIdealImage_mul_subset` and
  `locIdealImage_mul_locSubring_subset` are its diagonal and zeroth cases.
* `locIdealImage_leftMul`: the remaining multiplicative compatibility the subgroup basis needs.
* `locBasis`: The neighborhoods form a `RingSubgroupsBasis`, so they are the zero-neighbourhood
  basis of a ring topology on `Aₛ`, namely `locTopology`.
* `hasBasis_nhds_zero_locTopology`, `isTopologicalRing_locTopology` and
  `nonarchimedeanRing_locTopology`: the contract of `locTopology`, to be used in place of unfolding
  the construction.
* `continuous_algebraMap_locTopology`: the structure map `A → Aₛ` is continuous.
* `isOpen_locIdealImage`, and `isOpen_locSubring` with `isBounded_locSubring`: every basic
  neighbourhood is open, and `D` is open and bounded. These do **not** yet make `(D, J)` a
  `TauCeti.Huber.PairOfDefinition`, which also asks that `J` be finitely generated (`fg_locIdeal`,
  proved here) and that the subspace topology on `D` be `J`-adic (not proved here).
* `isPowerBounded_of_mem_locSubring` and `isPowerBounded_divBy`: every element of `D` — in
  particular each fraction `t/s` — is power-bounded, the fact a converse to the continuity
  criterion needs.
* `continuous_of_continuous_algebraMap_of_isPowerBounded`: a sufficient criterion
  for a ring homomorphism out of `Aₛ` to be continuous — its restriction along `algebraMap` is
  continuous and the fractions `t/s` go to power-bounded elements. The converse is not proved
  here.

## Provenance

This is a port of AINTLIB's `LocalizationTopology.lean`, at commit `d9f2fbbb`. The main
changes are:
- Adapted `PairOfDefinition` field names to TauCeti conventions
  (`A₀`→`ringOfDefinition`, `I`→`ideal`, etc.)
- Uses TauCeti's module system and namespace structure
- Uses characteristic lemmas instead of destructuring definitions
- Removed unused hypotheses to satisfy `#lint` checks
- Stated over an arbitrary localisation `S` away from `s`, rather than the concrete model
  `Localization.Away s` the source uses

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §5.6
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `d9f2fbbb`, `projects/AdicSpaces/Adic spaces/LocalizationTopology.lean`
-/

open Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### The candidate ring of definition `D` -/

/-! Everything below takes a `PairOfDefinition` as its first explicit argument, so it lives in
that namespace and reads `P.locSubring T s S`, matching `TauCeti/RingTheory/Huber/Basic.lean`. -/

namespace PairOfDefinition

/-- The candidate ring of definition `D = A₀[t₁/s, …, tₙ/s]` of `S`. -/
noncomputable def locSubring (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] : Subring S :=
  Subring.closure
    ((algebraMap A S) '' (P.ringOfDefinition : Set A) ∪
     Set.range (fun t : T ↦ divBy (t : A) s))

/-- The subring coercion carries the `D`-action on itself to multiplication in `Aₛ`. -/
private theorem coe_smul_locSubring (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (r d : locSubring P T s S) :
    ((r • d : locSubring P T s S) : S) =
      (r : S) * (d : S) := by
  rw [smul_eq_mul]
  exact MulMemClass.coe_mul ..

/-- `D` is the subring generated by the image of `A₀` together with the fractions `tᵢ/s`. The body
is not exported, so this is how a consumer reaches the generators. -/
theorem locSubring_def (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    locSubring P T s S = Subring.closure
      ((algebraMap A S) '' (P.ringOfDefinition : Set A) ∪
       Set.range (fun t : T ↦ divBy (t : A) s)) := (rfl)

/-- The image of `A₀` under `algebraMap` is contained in `D`. -/
theorem algebraMap_ringOfDefinition_subset_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    (algebraMap A S) '' (P.ringOfDefinition : Set A) ⊆
      (locSubring P T s S : Set S) :=
  Set.subset_union_left.trans Subring.subset_closure

/-- Each element `t/s` (for `t ∈ T`) belongs to `D`. -/
theorem divBy_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] {t : A} (ht : t ∈ T) :
    divBy t s ∈ locSubring P T s S :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

/-- An element of `A₀` maps into `D` under `algebraMap`. -/
theorem algebraMap_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] {a : A}
    (ha : a ∈ P.ringOfDefinition) :
    algebraMap A S a ∈ locSubring P T s S :=
  algebraMap_ringOfDefinition_subset_locSubring P T s S ⟨a, ha, rfl⟩

/-- **The universal property of `D`**: a subring contains `D` exactly when it contains the image
of `A₀` and every distinguished fraction. The body of `locSubring` is not exported, so this is the
elimination principle a consumer has. -/
theorem locSubring_le_iff (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    {R : Subring S} :
    locSubring P T s S ≤ R ↔
      (∀ a ∈ P.ringOfDefinition, algebraMap A S a ∈ R) ∧
        ∀ t ∈ T, (divBy t s : S) ∈ R := by
  rw [locSubring_def, Subring.closure_le]
  refine ⟨fun h ↦ ⟨fun a ha ↦ h (Set.mem_union_left _ ⟨a, ha, rfl⟩),
    fun t ht ↦ h (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)⟩, ?_⟩
  rintro ⟨h₁, h₂⟩ x (⟨a, ha, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
  · exact h₁ a ha
  · exact h₂ t ht

/-- With no fractions adjoined, `D` is just the image of `A₀`. -/
@[simp]
theorem locSubring_empty (P : PairOfDefinition A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    locSubring P ∅ s S = P.ringOfDefinition.map (algebraMap A S) := by
  rw [locSubring_def]
  simp only [Set.range_eq_empty, Set.union_empty]
  rw [← Subring.coe_map]
  exact Subring.closure_eq _

/-- `D` grows with the set of numerators. -/
theorem locSubring_mono (P : PairOfDefinition A) {T U : Finset A} (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (h : T ⊆ U) :
    locSubring P T s S ≤ locSubring P U s S :=
  (locSubring_le_iff P T s S).mpr ⟨fun _ ha ↦ algebraMap_mem_locSubring P U s S ha,
    fun _ ht ↦ divBy_mem_locSubring P U s S (h ht)⟩

/-! ### The standing hypothesis -/

/-- **The standing hypothesis** of Wedhorn's construction: some power of the ideal of definition
`I` has all of its fractions `b/s` already inside `D = A₀[t₁/s, …, tₙ/s]`. It is exactly what
makes the `locIdealImage` into a basis of neighbourhoods of zero for a ring topology, so every
declaration about `locTopology` below carries it. -/
def HasDenominatorPower (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] : Prop :=
  ∃ N : ℕ, ∀ b ∈ P.idealOfDefinition ^ N, divBy ((b : A)) s ∈ locSubring P T s S

/-- `HasDenominatorPower` unfolds to the existential it names. The body is not exported, so this
is how a consumer builds one by hand or takes one apart. -/
theorem hasDenominatorPower_iff (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    HasDenominatorPower P T s S ↔
      ∃ N : ℕ, ∀ b ∈ P.idealOfDefinition ^ N, divBy ((b : A)) s ∈ locSubring P T s S :=
  (Iff.rfl)

/-- **Introduction**: if some power of `I` lies in the ideal generated by `s` inside `A₀`, the
standing hypothesis holds. Indeed `b = c · s` makes `b/s = c`, which lies in `A₀ ⊆ D`. This is
the criterion in the standard case, where `s` itself is a topologically nilpotent element of
`A₀` generating a power of `I`. -/
theorem hasDenominatorPower_of_pow_le_span (P : PairOfDefinition A) (T : Finset A) {s : A}
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hs : s ∈ P.ringOfDefinition) {N : ℕ}
    (hN : P.idealOfDefinition ^ N ≤ Ideal.span {(⟨s, hs⟩ : P.ringOfDefinition)}) :
    HasDenominatorPower P T s S := by
  refine ⟨N, fun b hb ↦ ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hN hb)
  have hb' : (b : A) = s * (c : A) := by rw [← hc]; push_cast; ring
  rw [hb', divBy_mul_cancel_left]
  exact algebraMap_mem_locSubring P T s S c.property

/-! ### The candidate ideal of definition `J` -/

/-- The ring homomorphism `A₀ →+* D` induced by `algebraMap`. -/
noncomputable def toLocSubring (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    P.ringOfDefinition →+* (locSubring P T s S) :=
  ((algebraMap A S).comp P.ringOfDefinition.subtype).codRestrict
    (locSubring P T s S)
    (fun a ↦ algebraMap_ringOfDefinition_subset_locSubring P T s S ⟨a, a.property, rfl⟩)

/-- `toLocSubring` is `algebraMap` with its codomain cut down to `D`, so its values coerce back to
`algebraMap`. -/
@[simp]
theorem toLocSubring_apply (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (a : P.ringOfDefinition) :
    (toLocSubring P T s S a : S) = algebraMap A S (a : A) :=
  (rfl)

/-- The candidate ideal of definition `J = I · D` in `D`. -/
noncomputable def locIdeal (P : PairOfDefinition A) (T : Finset A)
    (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] : Ideal (locSubring P T s S) :=
  Ideal.map (toLocSubring P T s S) P.idealOfDefinition

/-- `J` is the ideal of `D` generated by the image of `I`. -/
theorem locIdeal_def (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    locIdeal P T s S = Ideal.map (toLocSubring P T s S) P.idealOfDefinition := (rfl)

/-- `Jⁿ` is the image of `Iⁿ`. The body of `locIdeal` is not exported, so this is how a consumer
reaches the powers that index the neighbourhood basis. -/
theorem locIdeal_pow (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (n : ℕ) :
    locIdeal P T s S ^ n = Ideal.map (toLocSubring P T s S) (P.idealOfDefinition ^ n) := by
  rw [locIdeal_def, Ideal.map_pow]

/-- `Jⁿ` is *spanned* by the image of `Iⁿ`: the form the span inductions below run on. -/
theorem locIdeal_pow_eq_span (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (n : ℕ) :
    locIdeal P T s S ^ n = Ideal.span (toLocSubring P T s S ''
      ((P.idealOfDefinition ^ n : Ideal P.ringOfDefinition) : Set P.ringOfDefinition)) := by
  conv_lhs => rw [locIdeal_pow, ← Ideal.span_eq (P.idealOfDefinition ^ n)]
  rw [Ideal.map_span]

/-- The image of `Iⁿ` under `A₀ →+* D` lands in `Jⁿ`. -/
theorem toLocSubring_mem_locIdeal_pow (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] {n : ℕ}
    {b : P.ringOfDefinition} (hb : b ∈ P.idealOfDefinition ^ n) :
    toLocSubring P T s S b ∈ locIdeal P T s S ^ n := by
  rw [locIdeal_pow]; exact Ideal.mem_map_of_mem _ hb

/-- **`J` is finitely generated**, because `I` is and `Ideal.map` preserves that. This is one of
the two conditions `(D, J)` still needs to be a `TauCeti.Huber.PairOfDefinition`; the other, that
the subspace topology on `D` is `J`-adic, is not proved here. -/
theorem fg_locIdeal (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    (locIdeal P T s S).FG := by
  rw [locIdeal_def]
  exact P.fg_idealOfDefinition.map _

/-! ### The neighborhood basis -/

/-- The `n`-th neighborhood of `0` in `S`. -/
noncomputable def locIdealImage (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (n : ℕ) : AddSubgroup S :=
  ((locIdeal P T s S) ^ n).toAddSubgroup.map
    (locSubring P T s S).subtype.toAddMonoidHom

/-- An element of `Aₛ` lies in the `n`-th neighbourhood exactly when it is the image of an element
of `Jⁿ`. -/
@[simp]
theorem mem_locIdealImage_iff (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (n : ℕ)
    {x : S} :
    x ∈ locIdealImage P T s S n ↔
      ∃ d ∈ (locIdeal P T s S ^ n : Ideal (locSubring P T s S)), (d : _) = x :=
  (Iff.rfl)

/-- The image of `Iⁿ` in `Aₛ` lands in the `n`-th basic neighbourhood: this is the introduction
rule for `locIdealImage`, and what continuity of the structure map is read off. -/
theorem algebraMap_mem_locIdealImage (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] {n : ℕ}
    {b : P.ringOfDefinition} (hb : b ∈ P.idealOfDefinition ^ n) :
    algebraMap A S (b : A) ∈ locIdealImage P T s S n :=
  (mem_locIdealImage_iff P T s S n).mpr
    ⟨toLocSubring P T s S b, toLocSubring_mem_locIdeal_pow P T s S hb, toLocSubring_apply P T s S b⟩

/-- The zeroth neighbourhood is `D` itself, because `J⁰ = ⊤`. -/
@[simp]
theorem locIdealImage_zero (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    locIdealImage P T s S 0 = (locSubring P T s S).toAddSubgroup := by
  ext x
  simp only [mem_locIdealImage_iff, pow_zero, Ideal.one_eq_top, Submodule.mem_top, true_and,
    Subring.mem_toAddSubgroup]
  exact ⟨fun ⟨d, hd⟩ ↦ hd ▸ d.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The neighborhoods are antitone. -/
theorem locIdealImage_antitone (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    Antitone (locIdealImage P T s S) :=
  fun _ _ h ↦ AddSubgroup.map_mono (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

/-- The preimage of `locIdealImage n` under the subtype embedding equals `locIdeal^n`. -/
@[simp]
theorem locIdealImage_preimage_eq_locIdeal_pow (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (n : ℕ) :
    (Subtype.val : locSubring P T s S → S) ⁻¹'
        (locIdealImage P T s S n : Set S) =
      ((locIdeal P T s S) ^ n : Ideal (locSubring P T s S)) := by
  -- The embedding is spelled `Subtype.val`, not `(locSubring P T s S).subtype`: the former is the
  -- simp-normal form (`Subring.coe_subtype` rewrites the latter to it), so the other spelling
  -- would leave this `@[simp]` lemma's left-hand side unable to fire. The proof goes through the
  -- file's own `mem_locIdealImage_iff` rather than crossing the `AddSubgroup.map`/`Subring.subtype`
  -- wrappers by definitional equality.
  ext d
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_locIdealImage_iff]
  refine ⟨fun ⟨e, he, heq⟩ ↦ Subtype.val_injective heq ▸ he, fun hd ↦ ⟨d, hd, rfl⟩⟩

/-- **The basis is graded**: the `i`-th and `j`-th neighbourhoods multiply into the `(i + j)`-th,
because `Jⁱ · Jʲ ⊆ Jⁱ⁺ʲ` in `D`. The two special cases the subgroup basis needs follow. -/
theorem locIdealImage_mul_subset_add (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (i j : ℕ) :
    (locIdealImage P T s S i : Set S) *
        (locIdealImage P T s S j : Set S) ⊆
      (locIdealImage P T s S (i + j) : Set S) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨d₁, hd₁, rfl⟩ := (mem_locIdealImage_iff P T s S i).mp hx
  obtain ⟨d₂, hd₂, rfl⟩ := (mem_locIdealImage_iff P T s S j).mp hy
  exact (mem_locIdealImage_iff P T s S (i + j)).mpr ⟨d₁ * d₂,
    pow_add (locIdeal P T s S) i j ▸ Ideal.mul_mem_mul hd₁ hd₂, MulMemClass.coe_mul ..⟩

/-- Products of the `n`-th neighbourhood land in the `n`-th neighbourhood: this is the
multiplicative half of the subgroup basis, the diagonal case of `locIdealImage_mul_subset_add`. -/
theorem locIdealImage_mul_subset (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (i : ℕ) :
    (locIdealImage P T s S i : Set S) *
        (locIdealImage P T s S i : Set S) ⊆
      (locIdealImage P T s S i : Set S) :=
  (locIdealImage_mul_subset_add P T s S i i).trans
    fun _ h ↦ locIdealImage_antitone P T s S (Nat.le_add_left i i) h

/-- `Jⁿ`'s image absorbs multiplication by `D`, because `D` is the zeroth neighbourhood and the
basis is graded. -/
theorem locIdealImage_mul_locSubring_subset (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (n : ℕ) :
    (locIdealImage P T s S n : Set S) *
        (locSubring P T s S : Set S)
      ⊆ (locIdealImage P T s S n : Set S) := by
  have h : (locSubring P T s S : Set S) =
      (locIdealImage P T s S 0 : Set S) := by
    rw [locIdealImage_zero, Subring.coe_toAddSubgroup]
  rw [h]
  exact locIdealImage_mul_subset_add P T s S n 0

/-- Multiplying `1/s` by an element of `Jᴺ` lands back in `D`, once `N` is large enough that
`b/s ∈ D` for every `b ∈ Iᴺ`. -/
private theorem locIdealImage_invSelf_mem (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (N : ℕ)
    (hN : ∀ b ∈ P.idealOfDefinition ^ N, divBy ((b : A)) s ∈ locSubring P T s S)
    {d : locSubring P T s S} (hd : d ∈ locIdeal P T s S ^ N) :
    (IsLocalization.Away.invSelf s : S) * ↑d ∈ locSubring P T s S := by
  rw [locIdeal_pow_eq_span] at hd
  refine Submodule.span_induction
    (p := fun d _ ↦
      (IsLocalization.Away.invSelf s : S) * ↑d ∈ locSubring P T s S)
    ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    rw [toLocSubring_apply, invSelf_mul_algebraMap]
    exact hN b hb
  · simp [(locSubring P T s S).zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simp only [AddMemClass.coe_add, mul_add]
    exact (locSubring P T s S).add_mem h₁ h₂
  · intro r d₁ _ h₁
    rw [coe_smul_locSubring, mul_left_comm]
    exact (locSubring P T s S).mul_mem r.property h₁

/-- Multiplying `1/s` by an element of `locIdealImage (n + N)` lands in `locIdealImage n`, once
`N` is large enough that `b/s ∈ D` for every `b ∈ Iᴺ`. -/
private theorem locIdealImage_invSelf_step (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (N : ℕ)
    (hN : ∀ b ∈ P.idealOfDefinition ^ N, divBy ((b : A)) s ∈ locSubring P T s S)
    (n : ℕ) (y : S) (hy : y ∈ locIdealImage P T s S (n + N)) :
    (IsLocalization.Away.invSelf s : S) * y ∈ locIdealImage P T s S n := by
  obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T s S _).mp hy
  rw [Nat.add_comm, pow_add] at hd
  refine Submodule.mul_induction_on hd ?_ ?_
  · intro a ha b hb
    -- expose the product `(1/s * a) * b`; the left factor lands in `D` by
    -- `locIdealImage_invSelf_mem`
    rw [MulMemClass.coe_mul, ← mul_assoc]
    exact (mem_locIdealImage_iff P T s S n).mpr
      ⟨⟨IsLocalization.Away.invSelf s * ↑a, locIdealImage_invSelf_mem P T s S N hN ha⟩ * b,
        Ideal.mul_mem_left _ _ hb, MulMemClass.coe_mul ..⟩
  · intro y₁ y₂ h₁ h₂
    simp only [AddMemClass.coe_add, mul_add]
    exact (locIdealImage P T s S n).add_mem h₁ h₂

/-- Multiplying `algebraMap a` by an element of a suitable `locIdealImage j` lands in
`locIdealImage i`. -/
private theorem locIdealImage_algMap_step [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (i : ℕ) (a : A) :
    ∃ j, ∀ y ∈ locIdealImage P T s S j,
      algebraMap A S a * y ∈ locIdealImage P T s S i := by
  obtain ⟨m₀, -, hm₀⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (continuous_const_mul a |>.continuousAt.preimage_mem_nhds
      (by rw [mul_zero]; exact P.hasBasis_nhds_zero.mem_of_mem trivial (i := i)))
  refine ⟨m₀, fun y hy ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T s S _).mp hy
  rw [locIdeal_pow_eq_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦
    algebraMap A S a * ↑d ∈ locIdealImage P T s S i) ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hval⟩ := (P.mem_idealImage i).mp (hm₀ ((P.mem_idealImage m₀).mpr ⟨b, hb, rfl⟩))
    rw [toLocSubring_apply]
    -- `hval`'s right side is the beta-redex `(fun x => a * x) ↑b`, which `rw` cannot match;
    -- `show` states the reduced form and is the only step that reaches this goal.
    rw [← map_mul, show a * (↑b : A) = ↑c from hval.symm]
    exact algebraMap_mem_locIdealImage P T s S hc
  · simp [(locIdealImage P T s S i).zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simp only [AddMemClass.coe_add, mul_add]
    exact (locIdealImage P T s S i).add_mem h₁ h₂
  · intro r d₁ _ h₁
    -- `D` absorbs `locIdealImage i` on the right, which the file already states.
    rw [coe_smul_locSubring, mul_left_comm, mul_comm]
    exact locIdealImage_mul_locSubring_subset P T s S i (Set.mul_mem_mul h₁ r.property)

/-- **Left multiplication is continuous** for the localization topology: multiplication by a
fixed `x` pulls some neighbourhood `locIdealImage j` back inside `locIdealImage i`. -/
theorem locIdealImage_leftMul [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (x : S) (i : ℕ) :
    ∃ j, (locIdealImage P T s S j : Set S) ⊆
      (x * ·) ⁻¹' (locIdealImage P T s S i : Set S) := by
  obtain ⟨N, hN⟩ := (hasDenominatorPower_iff P T s S).mp hden
  -- Every element of `S` is a fraction `a / sᵏ`; induct on `k`, peeling off one `1/s` at a time.
  -- The numerator is quantified inside the induction so that the step may choose its own.
  suffices h : ∀ (k : ℕ) (a : A), ∃ j, (locIdealImage P T s S j : Set S) ⊆
      (IsLocalization.mk' S a (⟨s ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers s) * ·) ⁻¹'
        (locIdealImage P T s S i : Set S) by
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (M := Submonoid.powers s) x
    exact h k a
  intro k
  induction k with
  | zero =>
    intro a
    -- `s ^ 0 = 1`, and `mk' a 1` is the structure map, which is what
    -- `locIdealImage_algMap_step` is stated for; `IsLocalization.mk'_one` identifies them.
    have hmk : IsLocalization.mk' S a (⟨s ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers s) =
        algebraMap A S a := by
      rw [show (⟨s ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers s) = 1 from Subtype.ext (pow_zero s)]
      exact IsLocalization.mk'_one S a
    rw [hmk]
    obtain ⟨j, hj⟩ := locIdealImage_algMap_step P T s S i a
    exact ⟨j, fun _ hy ↦ hj _ hy⟩
  | succ k ih =>
    intro a
    have hdecomp :
        IsLocalization.mk' S a (⟨s ^ (k + 1), ⟨k + 1, rfl⟩⟩ : Submonoid.powers s) =
          IsLocalization.mk' S a (⟨s ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers s) *
            (IsLocalization.Away.invSelf s : S) := by
      rw [← divBy_one, divBy_def, ← IsLocalization.mk'_mul, mul_one]
      congr 1
      exact Subtype.ext (pow_succ s k)
    obtain ⟨j₁, hj₁⟩ := ih a
    refine ⟨j₁ + N, fun y hy ↦ ?_⟩
    simp only [Set.mem_preimage]
    rw [hdecomp, mul_assoc]
    exact hj₁ (locIdealImage_invSelf_step P T s S N hN j₁ _ hy)

/-- The `RingSubgroupsBasis` underlying the localization topology on `Aₛ`: the images of the
powers `Jⁿ` are a basis of neighbourhoods of zero compatible with the ring structure. -/
private theorem locBasis [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    RingSubgroupsBasis (locIdealImage P T s S) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (locIdealImage_antitone P T s S (le_max_left i j))
        (locIdealImage_antitone P T s S (le_max_right i j))⟩)
    (fun i ↦ ⟨i, locIdealImage_mul_subset P T s S i⟩)
    (locIdealImage_leftMul P T s S hden)

/-- Wedhorn's topological localisation: the topology on `Aₛ` whose neighbourhoods of zero are the
images of the powers of `J = I · D`, the candidate ideal of definition of
`D = A₀[t₁/s, …, tₙ/s]`. -/
@[instance_reducible] noncomputable def locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    TopologicalSpace S :=
  (locBasis P T s S hden).topology

/-- The contract of `locTopology`: the `locIdealImage n` are a basis of neighbourhoods of zero.
Consumers should use this rather than unfolding the definition. -/
theorem hasBasis_nhds_zero_locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    (@nhds _ (locTopology P T s S hden) 0).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (locIdealImage P T s S n : Set S) :=
  (locBasis P T s S hden).hasBasis_nhds_zero

/-- `locTopology` is a ring topology. -/
theorem isTopologicalRing_locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    @IsTopologicalRing _ (locTopology P T s S hden) _ :=
  (locBasis P T s S hden).toRingFilterBasis.isTopologicalRing

/-- `locTopology` is nonarchimedean: `Aₛ` inherits a basis of open additive subgroups at zero. -/
theorem nonarchimedeanRing_locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    @NonarchimedeanRing _ _ (locTopology P T s S hden) :=
  (locBasis P T s S hden).nonarchimedean

/-- **Every basic neighbourhood is open**: it is a subgroup that is a neighbourhood of zero. -/
theorem isOpen_locIdealImage [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (n : ℕ) :
    letI := locTopology P T s S hden
    IsOpen (locIdealImage P T s S n : Set S) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  exact (locIdealImage P T s S n).isOpen_of_mem_nhds (g := 0)
    ((hasBasis_nhds_zero_locTopology P T s S hden).mem_of_mem (i := n) trivial)

/-- **`D` is open**: it is the zeroth basic neighbourhood of zero. With `isBounded_locSubring`
`D` is open and bounded, but that does not yet make `(D, J)` a
`TauCeti.Huber.PairOfDefinition`: both `J.FG` and `IsAdic J` remain. `fg_locIdeal` supplies the
first; the second is not proved here. -/
theorem isOpen_locSubring [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    IsOpen (locSubring P T s S : Set S) := by
  let _ := locTopology P T s S hden
  have h := isOpen_locIdealImage P T s S hden 0
  rwa [locIdealImage_zero, Subring.coe_toAddSubgroup] at h

/-- **`D` is bounded**: each `Jⁿ` already absorbs it. -/
theorem isBounded_locSubring [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    IsBounded (locSubring P T s S : Set S) := by
  let _ := locTopology P T s S hden
  rw [isBounded_iff]
  intro U hU
  obtain ⟨n, -, hn⟩ := (hasBasis_nhds_zero_locTopology P T s S hden).mem_iff.mp hU
  exact ⟨_, (hasBasis_nhds_zero_locTopology P T s S hden).mem_of_mem (i := n) trivial,
    (locIdealImage_mul_locSubring_subset P T s S n).trans hn⟩

/-- **Every element of `D` is power-bounded**: `D` is bounded, and `IsBounded.isPowerBounded_of_mem`
turns that into power-boundedness of each of its elements. -/
theorem isPowerBounded_of_mem_locSubring [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    {x : S} (hx : x ∈ locSubring P T s S) :
    letI := locTopology P T s S hden
    IsPowerBounded x := by
  let _ := locTopology P T s S hden
  exact (isBounded_locSubring P T s S hden).isPowerBounded_of_mem hx

/-- The distinguished fractions `t/s` are power-bounded: they lie in `D`, and every element of
`D` is. -/
theorem isPowerBounded_divBy [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    {t : A} (ht : t ∈ T) :
    letI := locTopology P T s S hden
    IsPowerBounded (divBy t s : S) :=
  isPowerBounded_of_mem_locSubring P T s S hden (divBy_mem_locSubring P T s S ht)

/-- The structure map `A → Aₛ` is continuous for the localisation topology: the image of `Iⁿ`
already lands in the `n`-th basic neighbourhood. -/
theorem continuous_algebraMap_locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    Continuous[_, locTopology P T s S hden] (algebraMap A S) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  refine continuous_of_continuousAt_zero (algebraMap A S) ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_locTopology P T s S hden).tendsto_right_iff]
  intro n _
  filter_upwards [P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial] with a ha
  obtain ⟨b, hb, rfl⟩ := (P.mem_idealImage n).mp ha
  exact algebraMap_mem_locIdealImage P T s S hb

/-! ### A sufficient criterion for continuity -/

/-- Along `algebraMap`, some power of the ideal of definition multiplies the image of `A₀` into
any prescribed open subgroup of `B`. This is the `A₀`-level base case of
`exists_pow_mul_locSubring_mem`. -/
private theorem exists_pow_mul_algebraMap_mem {B : Type*} [Ring B] [TopologicalSpace B]
    (P : PairOfDefinition A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] (f : S →+* B)
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
    obtain ⟨m, hm⟩ := exists_pow_mul_algebraMap_mem P s S f hf G
    exact ⟨m, fun x hx b hb ↦ hm x (locSubring_empty P s S ▸ hx) b hb⟩
  | insert t U' ht ih =>
    intro hpowU G
    have hinsert_le : locSubring P (insert t U') s S ≤
        Subring.closure ((locSubring P U' s S : Set S) ∪ {divBy t s}) :=
      (locSubring_le_iff P _ s S).mpr
        ⟨fun _ ha ↦ Subring.subset_closure (.inl (algebraMap_mem_locSubring P U' s S ha)),
         fun t' ht' ↦ by
           rcases Finset.mem_insert.mp ht' with rfl | ht'U
           · exact Subring.subset_closure (.inr rfl)
           · exact Subring.subset_closure (.inl (divBy_mem_locSubring P U' s S ht'U))⟩
    obtain ⟨V, hV, hzV⟩ := isBounded_iff.mp (isPowerBounded_iff.mp
      (hpowU t (Finset.mem_insert_self t U'))) (G : Set B) (G.isOpen.mem_nhds G.zero_mem)
    obtain ⟨W, hWV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
    obtain ⟨m, hm⟩ := ih (fun t' ht' ↦ hpowU t' (Finset.mem_insert_of_mem ht')) W
    refine ⟨m, fun x hx b hb ↦ ?_⟩
    -- Write `x` as a polynomial in `t/s` with coefficients in the smaller subring.
    have hx_adj : x ∈ Algebra.adjoin (locSubring P U' s S)
        ({divBy t s} : Set S) := by
      have h_le : Subring.closure
          ((locSubring P U' s S : Set S) ∪ {divBy t s}) ≤
            (Algebra.adjoin (locSubring P U' s S)
              ({divBy t s} : Set S)).toSubring := by
        rw [Subring.closure_le]
        rintro w (hw | rfl)
        · exact Subalgebra.algebraMap_mem _ (⟨w, hw⟩ : locSubring P U' s S)
        · exact Algebra.subset_adjoin rfl
      exact h_le (hinsert_le hx)
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx_adj
    obtain ⟨p, hp⟩ := hx_adj
    rw [← hp, Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
    refine G.toAddSubgroup.sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def, Algebra.algebraMap_ofSubsemiring_apply, mul_right_comm,
      map_mul, map_pow]
    exact hzV (Set.mul_mem_mul (hWV (hm _ (p.coeff i).property b hb)) ⟨i, rfl⟩)

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
  suffices h : ∀ r : locSubring P T s S,
      f ((locSubring P T s S).subtype (r * d)) ∈ (W : Set B) by
    simpa using h 1
  refine Submodule.span_induction (p := fun d _ ↦ ∀ r : locSubring P T s S,
    f ((locSubring P T s S).subtype (r * d)) ∈ (W : Set B)) ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨b, hb, rfl⟩ r
    rw [Subring.coe_subtype, MulMemClass.coe_mul, toLocSubring_apply]
    exact hm r.val r.property b hb
  · intro r
    simp
  · intro d₁ d₂ _ _ h₁ h₂ r
    rw [mul_add, map_add, map_add]
    exact W.toAddSubgroup.add_mem (h₁ r) (h₂ r)
  · intro c d _ hd r
    rw [smul_eq_mul, ← mul_assoc]
    exact hd (r * c)

end PairOfDefinition

end

end TauCeti.Huber
