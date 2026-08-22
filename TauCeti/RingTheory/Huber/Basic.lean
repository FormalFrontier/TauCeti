/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.Topology.Algebra.Group.FirstCountable

/-!
# Huber rings and Tate rings

A *pair of definition* for a topological ring `A` is an open subring `A₀ ⊆ A` together with a
finitely generated ideal `I ⊆ A₀` whose adic topology is the subspace topology of `A₀`. A ring
admitting one is a *Huber ring* (Wedhorn's *f-adic* ring), and a Huber ring containing a
topologically nilpotent unit is a *Tate ring*.

Everything the later layers use about the topology of a Huber ring comes from one statement: the
images in `A` of the powers `Iⁿ` are a neighbourhood basis of zero
(`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero`). They are open additive subgroups, so a
Huber ring is nonarchimedean, which is exactly the hypothesis under which
`TauCeti/RingTheory/Huber/PowerBounded.lean` makes `A°` a subring.

## Main definitions

* `TauCeti.Huber.PairOfDefinition`: a pair of definition `(A₀, I)` for `A`.
* `TauCeti.Huber.IsHuberRing`: `A` admits a pair of definition.
* `TauCeti.Huber.IsTateRing`: a Huber ring with a topologically nilpotent unit.
* `TauCeti.Huber.IsPseudoUniformizer`: a topologically nilpotent unit of `A`.

## Main results

* `TauCeti.Huber.PairOfDefinition.mem_idealImage` and
  `TauCeti.Huber.PairOfDefinition.coe_idealImage`: membership in the image of `Iⁿ`.
* `TauCeti.Huber.PairOfDefinition.span_image_eq_extendedIdealOfDefinition`: generators of `I`
  continue to generate its extension to `A`.
* `TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero`: the images of `Iⁿ` are a neighbourhood
  basis of zero.
* `TauCeti.Huber.IsAdic.comap`: an adic topology transports along a ring equivalence that is an
  inducing map. This is what lets a ring of definition carry an ideal of definition that natively
  lives in a merely equivalent ring, which is what `TauCeti.Huber.PairOfDefinition` needs.
* `TauCeti.Huber.IsHuberRing.toNonarchimedeanRing`: a Huber ring is nonarchimedean.
* `TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero`: its neighbourhoods of zero are
  countably generated. With the previous bullet these are exactly the two hypotheses Henkel's open
  mapping theorem asks of the underlying group, so both are instances.
* `TauCeti.Huber.PairOfDefinition.exists_pow_mul_mem`: a power of a topologically nilpotent `s`
  carries any `c : A` into the ring of definition.
* `TauCeti.Huber.IsHuberRing.quotient`: a quotient of a Huber ring is a Huber ring.
* `TauCeti.Huber.PairOfDefinition.isBounded_ringOfDefinition`: a ring of definition is bounded,
  hence `A₀ ≤ A°` (`TauCeti.Huber.PairOfDefinition.le_powerBoundedSubring`). This is the
  boundedness half of Wedhorn Corollary 6.4.
* `TauCeti.Huber.isOpen_powerBoundedSubring`: `A°` is open in a Huber ring.
* `TauCeti.Huber.IsPseudoUniformizer.hasBasis_nhds_zero`: for a pseudouniformiser `ϖ` and a ring
  of definition `A₀` of a Tate ring, the sets `ϖⁿ A₀` are a neighbourhood basis of zero; the
  Tate-ring form is `TauCeti.Huber.IsTateRing.exists_hasBasis_nhds_zero`.
* `TauCeti.Huber.IsHuberRing.of_discreteTopology`: a discrete ring is Huber, the first of the
  roadmap's Layer-0 examples.
* `TauCeti.Huber.exists_sum_eq_of_mem_span_mul`: pure algebra, stated here because it is what
  finite generation of an ideal of definition is used through — an element of `(G) * K`, for a
  finite family `G`, is a `K`-linear combination of `G` itself.

## Provenance

`PairOfDefinition` and `IsHuberRing` follow the shape of sfingali's mathlib4#42312, which bundles
the same five fields; the name `PairOfDefinition` is used rather than that PR's `RingOfDefinition`
because the structure carries the pair `(A₀, I)`, which is what Wedhorn calls a pair of
definition — a ring of definition is the `A₀` alone. Everything else here is new. The selection
of results follows `AdicSpaces/Suggested.lean` in the roadmap.

## Implementation notes

The pair of definition is *data*, not a `Prop`-valued field of the ring: a Huber ring has many
pairs of definition and later layers choose between them. `IsHuberRing` is the `Prop` asserting
that the type of pairs is nonempty, in the shape used by mathlib4#42312.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 6.1, Lemma 6.2 and
  Corollary 6.4.
* sfingali, *feat(Topology): huber (f-adic) rings*,
  [mathlib4#42312](https://github.com/leanprover-community/mathlib4/pull/42312).
-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

section SpanMul

variable {R : Type*} [CommSemiring R]

/-- An element of `(G) * K` is a `K`-linear combination of the finite family `G`.

This is Mathlib's `Submodule.mem_ideal_smul_span_iff_exists_sum'` in the form the Huber theory
uses it: a `Finset.sum` over `G` itself, with cofactors given by a function on all of `R`, rather
than a `Finsupp` on the subtype `↥G`. It is what bounds, uniformly in `k`, the number of terms
needed to write an element of `Iⁿ⁺ᵏ = Iⁿ * Iᵏ` over generators of `Iⁿ`, both in Wedhorn Remark 6.8
(`TauCeti.RingTheory.Huber.Completion`) and in the identification of the neighbourhood subgroups
of `A⟨X⟩_T` with the powers of one finitely generated ideal
(`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition`). -/
theorem exists_sum_eq_of_mem_span_mul (G : Finset R) (K : Ideal R) {b : R}
    (hb : b ∈ Ideal.span (G : Set R) * K) :
    ∃ c : R → R, (∀ z, c z ∈ K) ∧ ∑ z ∈ G, z * c z = b := by
  classical
  -- Present `(G) * K` as `K • span (id '' G)`, so that the coefficients are handed to us.
  rw [mul_comm, ← Ideal.smul_eq_mul, ← Set.image_id (G : Set R)] at hb
  obtain ⟨a, ha, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum' _ _ _ _).mp hb
  -- Extend the coefficients from `G` to all of `R` by zero.
  refine ⟨fun z ↦ if h : z ∈ G then a ⟨z, h⟩ else 0, fun z ↦ ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [ha _, K.zero_mem]
  · rw [Finsupp.sum_fintype _ _ (by simp),
      ← Finset.sum_finset_coe (fun z ↦ z * if h : z ∈ G then a ⟨z, h⟩ else 0) G]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [Finset.mem_coe.mp i.2, mul_comm]

end SpanMul

/-- A *pair of definition* `(A₀, I)` for a topological ring `A`: an open subring `A₀` together
with a finitely generated ideal `I` of `A₀` whose adic topology is the subspace topology.

This is data rather than a proposition, because a Huber ring generally has many pairs of
definition and the later theory chooses among them. -/
structure PairOfDefinition (A : Type*) [CommRing A] [TopologicalSpace A] where
  /-- The ring of definition `A₀`. -/
  ringOfDefinition : Subring A
  /-- The ring of definition is open in `A`. -/
  isOpen_ringOfDefinition : IsOpen (ringOfDefinition : Set A)
  /-- The ideal of definition `I ⊆ A₀`. -/
  idealOfDefinition : Ideal ringOfDefinition
  /-- The ideal of definition is finitely generated. -/
  fg_idealOfDefinition : idealOfDefinition.FG
  /-- The subspace topology on `A₀` is the `I`-adic topology. -/
  isAdic_idealOfDefinition : IsAdic idealOfDefinition

/-- A topological ring is a *Huber ring* — Wedhorn's *f-adic* ring — if it admits a pair of
definition. -/
class IsHuberRing (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] : Prop where
  /-- A Huber ring admits at least one pair of definition. -/
  nonempty_pairOfDefinition : Nonempty (PairOfDefinition A)

/-- A *pseudouniformiser* of a topological ring is a topologically nilpotent unit.

This is the topological notion, unrelated to Mathlib's `Valuation.IsUniformizer`, which asks a
*discretely valued* ring's element to have valuation the generator of the value group. A Tate
ring need carry no valuation at all. -/
def IsPseudoUniformizer {A : Type*} [MonoidWithZero A] [TopologicalSpace A] (a : A) : Prop :=
  IsUnit a ∧ IsTopologicallyNilpotent a

/-- Unfolding lemma for `TauCeti.Huber.IsPseudoUniformizer`. -/
@[simp]
theorem isPseudoUniformizer_iff {A : Type*} [MonoidWithZero A] [TopologicalSpace A] {a : A} :
    IsPseudoUniformizer a ↔ IsUnit a ∧ IsTopologicallyNilpotent a := (Iff.rfl)

/-- A pseudouniformiser is a unit. -/
theorem IsPseudoUniformizer.isUnit {A : Type*} [MonoidWithZero A] [TopologicalSpace A] {a : A}
    (ha : IsPseudoUniformizer a) : IsUnit a := ha.1

/-- A pseudouniformiser is topologically nilpotent. -/
theorem IsPseudoUniformizer.isTopologicallyNilpotent {A : Type*} [MonoidWithZero A]
    [TopologicalSpace A] {a : A} (ha : IsPseudoUniformizer a) :
    IsTopologicallyNilpotent a := ha.2

/-- A *Tate ring* is a Huber ring containing a pseudouniformiser, that is, a topologically
nilpotent unit. -/
class IsTateRing (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] : Prop
    extends IsHuberRing A where
  /-- A Tate ring contains a topologically nilpotent unit. -/
  exists_isPseudoUniformizer : ∃ a : A, IsPseudoUniformizer a

section Transport

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
/-- The powers of a comapped ideal are the comapped powers, along a ring equivalence. -/
private theorem comap_pow_of_equiv (e : B ≃+* A) (I : Ideal A) (n : ℕ) :
    (I ^ n).comap e = I.comap e ^ n := by
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

/-- An adic topology transports along a ring equivalence that is also an inducing map.

This is what lets a ring of definition carry an ideal of definition: `PairOfDefinition` asks for
an `Ideal A₀` whose adic topology is the subspace topology, while the ideal at hand usually lives
in a ring that is only equivalent to `A₀`. -/
theorem IsAdic.comap (e : B ≃+* A) (he : IsInducing e) {I : Ideal A} (h : IsAdic I) :
    IsAdic (I.comap e) := by
  rw [isAdic_iff] at h ⊢
  obtain ⟨hopen, hnhds⟩ := h
  have hset : ∀ n : ℕ,
      ((I.comap e ^ n : Ideal B) : Set B) = e ⁻¹' ((I ^ n : Ideal A) : Set A) := by
    intro n
    ext b
    rw [← comap_pow_of_equiv e I n, SetLike.mem_coe, Ideal.mem_comap, Set.mem_preimage,
      SetLike.mem_coe]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hset n, he.isOpen_iff]
    exact ⟨_, hopen n, rfl⟩
  · rw [he.nhds_eq_comap (0 : B), map_zero, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨n, hn⟩ := hnhds t ht
    exact ⟨n, by rw [hset n]; exact fun b hb ↦ hts (hn hb)⟩

end Transport

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The image in `A` of the `n`-th power of the ideal of definition. These sets are the
neighbourhood basis of zero of a Huber ring. -/
def idealImage (P : PairOfDefinition A) (n : ℕ) : AddSubgroup A :=
  (P.idealOfDefinition ^ n).toAddSubgroup.map P.ringOfDefinition.subtype.toAddMonoidHom

/-- As a set, `Iⁿ`'s image in `A` is the image of `Iⁿ ⊆ A₀` under the inclusion `A₀ → A`. -/
@[simp]
theorem coe_idealImage (P : PairOfDefinition A) (n : ℕ) : (P.idealImage n : Set A) =
    Subtype.val ''
      ((P.idealOfDefinition ^ n : Ideal P.ringOfDefinition) : Set P.ringOfDefinition) := by
  ext x
  simp [idealImage]

/-- Membership in the image of `Iⁿ`. -/
@[simp]
theorem mem_idealImage (P : PairOfDefinition A) (n : ℕ) {x : A} :
    x ∈ P.idealImage n ↔
      ∃ y ∈ (P.idealOfDefinition ^ n : Ideal P.ringOfDefinition), (y : A) = x := by
  simp [idealImage]

/-- The images of the powers of the ideal of definition are nested. -/
theorem idealImage_anti (P : PairOfDefinition A) {m n : ℕ} (h : m ≤ n) :
    P.idealImage n ≤ P.idealImage m := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage n).mp hx
  exact (P.mem_idealImage m).mpr ⟨y, Ideal.pow_le_pow_right h hy, rfl⟩

/-- `Iⁿ ⊆ A` lies in the ring of definition. -/
theorem idealImage_le_ringOfDefinition (P : PairOfDefinition A) (n : ℕ) :
    P.idealImage n ≤ P.ringOfDefinition.toAddSubgroup := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (P.mem_idealImage n).mp hx
  exact y.2

/-- `Iⁿ ⊆ A` absorbs multiplication by an element of the ring of definition. -/
theorem mul_mem_idealImage (P : PairOfDefinition A) {n : ℕ} {a x : A}
    (ha : a ∈ P.ringOfDefinition) (hx : x ∈ P.idealImage n) : a * x ∈ P.idealImage n := by
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage n).mp hx
  exact (P.mem_idealImage n).mpr ⟨⟨a, ha⟩ * y, Ideal.mul_mem_left _ _ hy, by push_cast; ring⟩

/-- The images of the powers of the ideal of definition multiply: `Iᵃ · Iᵇ ⊆ Iᵃ⁺ᵇ`. -/
theorem mul_mem_idealImage_add (P : PairOfDefinition A) {a b : ℕ} {x y : A}
    (hx : x ∈ P.idealImage a) (hy : y ∈ P.idealImage b) : x * y ∈ P.idealImage (a + b) := by
  obtain ⟨u, hu, rfl⟩ := (P.mem_idealImage a).mp hx
  obtain ⟨v, hv, rfl⟩ := (P.mem_idealImage b).mp hy
  exact (P.mem_idealImage (a + b)).mpr
    ⟨u * v, (pow_add P.idealOfDefinition a b).symm ▸ Ideal.mul_mem_mul hu hv, by push_cast; ring⟩

/-- **One coefficient, decomposed.** An element of `Iⁿ⁺¹ ⊆ A` is a combination of a finite
generating set `G` of `I` with cofactors in `Iⁿ`. -/
theorem exists_sum_eq_of_mem_idealImage_succ (P : PairOfDefinition A)
    {G : Finset P.ringOfDefinition}
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition) (n : ℕ) {x : A}
    (hx : x ∈ P.idealImage (n + 1)) :
    ∃ c : P.ringOfDefinition → A,
      (∀ z, c z ∈ P.idealImage n) ∧ ∑ z ∈ G, (z : A) * c z = x := by
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage (n + 1)).mp hx
  have hy' : y ∈ Ideal.span (G : Set P.ringOfDefinition) * P.idealOfDefinition ^ n := by
    rw [hG, ← pow_succ']
    exact hy
  obtain ⟨c, hc, hsum⟩ := exists_sum_eq_of_mem_span_mul G (P.idealOfDefinition ^ n) hy'
  refine ⟨fun z ↦ (c z : A), fun z ↦ (P.mem_idealImage n).mpr ⟨c z, hc z, rfl⟩, ?_⟩
  rw [← hsum]
  push_cast
  rfl

/-- The ideal `I · A` of `A` generated by the ideal of definition `I ⊆ A₀`. This is core data of
a pair of definition; `TauCeti/RingTheory/Huber/OpenIdeal.lean` characterises the open ideals of
`A` in terms of its powers. -/
def extendedIdealOfDefinition (P : PairOfDefinition A) : Ideal A :=
  P.idealOfDefinition.map P.ringOfDefinition.subtype

/-- Unfolding lemma for `TauCeti.Huber.PairOfDefinition.extendedIdealOfDefinition`. -/
theorem extendedIdealOfDefinition_def (P : PairOfDefinition A) :
    P.extendedIdealOfDefinition = P.idealOfDefinition.map P.ringOfDefinition.subtype := (rfl)

/-- Membership in `I · A` is membership in the ideal *spanned* by the image of `I`.

There is no simpler characterisation: the image of `I` under `A₀ → A` is an additive subgroup but
not in general an ideal of `A`, so `x ∈ I · A` is strictly weaker than `∃ y ∈ I, ↑y = x`. For
`A₀ = ℤ_[p] ⊆ A = ℚ_[p]` and `I = p • ℤ_[p]` the image is `p • ℤ_[p]` while the ideal it
generates is all of `ℚ_[p]`. -/
@[simp]
theorem mem_extendedIdealOfDefinition_iff (P : PairOfDefinition A) {x : A} :
    x ∈ P.extendedIdealOfDefinition ↔
      x ∈ Ideal.span (Subtype.val '' (P.idealOfDefinition : Set P.ringOfDefinition)) := by
  rw [P.extendedIdealOfDefinition_def, ← Ideal.span_eq P.idealOfDefinition, Ideal.map_span]
  simp

/-- The extended ideal `I · A` is finitely generated, because `I` is. -/
theorem fg_extendedIdealOfDefinition (P : PairOfDefinition A) :
    P.extendedIdealOfDefinition.FG :=
  P.fg_idealOfDefinition.map _

open scoped Classical in
/-- A finite generating set of the ideal of definition, mapped into `A`, generates the extended
ideal of definition. -/
theorem span_image_eq_extendedIdealOfDefinition (P : PairOfDefinition A)
    (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition) :
    Ideal.span ((G.image ((↑) : P.ringOfDefinition → A) : Finset A) : Set A) =
      P.extendedIdealOfDefinition := by
  rw [P.extendedIdealOfDefinition_def, ← hG, Ideal.map_span]
  congr 1
  ext a
  simp

/-- Each `Iⁿ` is open in `A`. -/
theorem isOpen_idealImage [IsTopologicalRing A] (P : PairOfDefinition A) (n : ℕ) :
    IsOpen (P.idealImage n : Set A) :=
  P.isOpen_ringOfDefinition.isOpenEmbedding_subtypeVal.isOpenMap _
    ((isAdic_iff.mp P.isAdic_idealOfDefinition).1 n)

/-- The image of `Iⁿ` as an open additive subgroup of `A`. -/
private def openAddSubgroup [IsTopologicalRing A] (P : PairOfDefinition A) (n : ℕ) :
    OpenAddSubgroup A where
  toAddSubgroup := P.idealImage n
  isOpen' := P.isOpen_idealImage n

/-- Wedhorn Proposition and Definition 6.1: the images in `A` of the powers of the ideal of
definition are a neighbourhood basis of zero. -/
theorem hasBasis_nhds_zero (P : PairOfDefinition A) :
    (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (P.idealImage n : Set A) := by
  have hmap : Filter.map ((↑) : P.ringOfDefinition → A) (𝓝 0) = 𝓝 (0 : A) :=
    P.isOpen_ringOfDefinition.isOpenEmbedding_subtypeVal.map_nhds_eq 0
  rw [← hmap]
  exact P.isAdic_idealOfDefinition.hasBasis_nhds_zero.map _

/-- **An element of the ideal of definition is topologically nilpotent.** Its powers lie in the
successive `Iⁿ`, whose images are a neighbourhood basis of zero
(`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero`), so they converge to `0` in `A`.

This is the property Wedhorn uses throughout §7.2: it is what forces a continuous valuation to
have cofinal values on `I`, and hence `v a < 1` there (Theorem 7.10). -/
theorem isTopologicallyNilpotent_of_mem_idealOfDefinition (P : PairOfDefinition A)
    {a : P.ringOfDefinition} (ha : a ∈ P.idealOfDefinition) :
    IsTopologicallyNilpotent (a : A) := by
  rw [IsTopologicallyNilpotent, P.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  refine (P.mem_idealImage n).mpr ⟨a ^ m, ?_, by push_cast; ring⟩
  exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ha m)

/-- **An element of the image of `Iⁿ` is topologically nilpotent**, for `n ≠ 0`. Unpacking the
membership gives an element of `Iⁿ ⊆ I`, so `isTopologicallyNilpotent_of_mem_idealOfDefinition`
applies. This is the form consumers meet, `idealImage` being what
`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero` is stated with.

`n ≠ 0` is needed, not incidental: `I ^ 0 = ⊤`, so `idealImage 0` is the image of the whole ring
of definition and its elements are not topologically nilpotent in general. -/
theorem isTopologicallyNilpotent_of_mem_idealImage (P : PairOfDefinition A) {n : ℕ} (hn : n ≠ 0)
    {a : A} (ha : a ∈ P.idealImage n) : IsTopologicallyNilpotent a := by
  obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage n).mp ha
  exact P.isTopologicallyNilpotent_of_mem_idealOfDefinition (Ideal.pow_le_self hn hy)

/-- A ring admitting a pair of definition is nonarchimedean. -/
theorem toNonarchimedeanRing [IsTopologicalRing A] (P : PairOfDefinition A) :
    NonarchimedeanRing A where
  is_nonarchimedean U hU := by
    obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hU
    exact ⟨P.openAddSubgroup n, hn⟩

/-- Wedhorn Corollary 6.4: a ring of definition is bounded. -/
theorem isBounded_ringOfDefinition [IsTopologicalRing A] (P : PairOfDefinition A) :
    IsBounded (P.ringOfDefinition : Set A) := by
  rw [isBounded_iff]
  intro U hU
  obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hU
  refine ⟨P.idealImage n, (P.isOpen_idealImage n).mem_nhds (P.idealImage n).zero_mem, ?_⟩
  rintro _ ⟨_, ⟨x, hx, rfl⟩, a, ha, rfl⟩
  exact hn ⟨x * ⟨a, ha⟩, Ideal.mul_mem_right _ _ hx, rfl⟩

/-- A ring of definition consists of power-bounded elements: `A₀ ≤ A°`. The nonarchimedean
hypothesis is only needed to state it, since `P` itself supplies one. -/
theorem le_powerBoundedSubring [NonarchimedeanRing A] (P : PairOfDefinition A) :
    P.ringOfDefinition ≤ powerBoundedSubring A := fun _ ha ↦
  mem_powerBoundedSubring.mpr (P.isBounded_ringOfDefinition.isPowerBounded_of_mem ha)

/-- The image of a pair of definition in a quotient ring, used to furnish the quotient Huber
ring structure. -/
private def quotient [IsTopologicalRing A] (P : PairOfDefinition A) (J : Ideal A) :
    PairOfDefinition (A ⧸ J) := by
  let q : A →+* A ⧸ J := Ideal.Quotient.mk J
  let A₀ : Subring (A ⧸ J) := P.ringOfDefinition.map q
  let q₀ : P.ringOfDefinition →+* A₀ :=
    (q.comp P.ringOfDefinition.subtype).codRestrict A₀ fun a ↦
      Subring.mem_map.mpr ⟨a, a.2, rfl⟩
  have hq₀_cont : Continuous q₀ := by
    dsimp [q₀]
    exact (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _
  have hq₀_open : IsOpenMap q₀ := by
    dsimp [q₀]
    exact
      (QuotientRing.isOpenMap_coe J).subtype_map P.isOpen_ringOfDefinition
        (fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩)
  have hq₀_surj : Function.Surjective q₀ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hx
    exact ⟨⟨a, ha⟩, rfl⟩
  refine
    { ringOfDefinition := A₀
      isOpen_ringOfDefinition := by
        rw [Subring.coe_map]
        exact QuotientRing.isOpenMap_coe J _ P.isOpen_ringOfDefinition
      idealOfDefinition := P.idealOfDefinition.map q₀
      fg_idealOfDefinition := P.fg_idealOfDefinition.map q₀
      isAdic_idealOfDefinition := isAdic_iff.mpr ⟨?_, ?_⟩ }
  · intro n
    rw [← Ideal.map_pow]
    have hset : ((P.idealOfDefinition ^ n).map q₀ : Set A₀) =
        q₀ '' ((P.idealOfDefinition ^ n : Ideal P.ringOfDefinition) :
          Set P.ringOfDefinition) := by
      ext y
      exact Ideal.mem_map_iff_of_surjective q₀ hq₀_surj
    rw [hset]
    exact hq₀_open _ ((isAdic_iff.mp P.isAdic_idealOfDefinition).1 n)
  · intro s hs
    obtain ⟨n, hn⟩ := (isAdic_iff.mp P.isAdic_idealOfDefinition).2
      (q₀ ⁻¹' s) (hq₀_cont.continuousAt.preimage_mem_nhds (by simpa using hs))
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow]
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_map_iff_of_surjective q₀ hq₀_surj |>.mp hy
    exact hn hx

/-- **Some power of a topologically nilpotent `s` carries any `c : A` into the ring of
definition.** The ring of definition is open and `sⁿ c → 0`, so `sⁿ c` is eventually inside it.

This is the arbitrary-`c` generalisation of
`TauCeti.Huber.IsPseudoUniformizer.eventually_pow_mem_ringOfDefinition`, which is the case
`c = 1`; it also asks only for topological nilpotence rather than for a pseudouniformiser. -/
theorem exists_pow_mul_mem [IsTopologicalRing A] (P : PairOfDefinition A) {s : A}
    (hs : IsTopologicallyNilpotent s) (c : A) : ∃ i : ℕ, s ^ i * c ∈ P.ringOfDefinition :=
  ((hs.mul_const c).eventually
    (P.isOpen_ringOfDefinition.mem_nhds (by simp))).exists

end PairOfDefinition

/-- Quotients of Huber rings, with the quotient topology, are Huber rings. -/
instance IsHuberRing.quotient {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (J : Ideal A) : IsHuberRing (A ⧸ J) :=
  ⟨IsHuberRing.nonempty_pairOfDefinition.elim fun P ↦ ⟨P.quotient J⟩⟩

section Discrete

variable (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- The pair of definition of a discrete ring: the whole ring, with the zero ideal. -/
def PairOfDefinition.discrete : PairOfDefinition A where
  ringOfDefinition := ⊤
  isOpen_ringOfDefinition := by simp
  idealOfDefinition := ⊥
  fg_idealOfDefinition := Submodule.fg_bot
  isAdic_idealOfDefinition := is_bot_adic_iff.mpr inferInstance

@[simp]
theorem PairOfDefinition.discrete_ringOfDefinition :
    (PairOfDefinition.discrete A).ringOfDefinition = ⊤ := (rfl)

@[simp]
theorem PairOfDefinition.discrete_idealOfDefinition :
    (PairOfDefinition.discrete A).idealOfDefinition = ⊥ := (rfl)

/-- A discrete ring is Huber, with `(A, 0)` as a pair of definition. This is the first of the
roadmap's Layer-0 examples, and the witness that `IsHuberRing` is not vacuous. -/
instance (priority := 100) IsHuberRing.of_discreteTopology [IsTopologicalRing A] :
    IsHuberRing A :=
  ⟨⟨PairOfDefinition.discrete A⟩⟩

end Discrete

section HuberRing

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- Every Huber ring is nonarchimedean. This is what makes `A°` a subring. -/
instance (priority := 100) IsHuberRing.toNonarchimedeanRing : NonarchimedeanRing A :=
  IsHuberRing.nonempty_pairOfDefinition.elim fun P ↦ P.toNonarchimedeanRing

/-- **The neighbourhoods of zero in a Huber ring are countably generated.** The images of the
powers of an ideal of definition are a basis of `𝓝 0` indexed by `ℕ`
(`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero`), and a basis indexed by a countable type
generates a countably generated filter.

This is one of the two hypotheses Henkel's open mapping theorem asks of a topological group, the
other being `TauCeti.Huber.IsHuberRing.toNonarchimedeanRing` above: nonarchimedean makes the open
subgroups a basis at zero, and countable generation extracts an antitone *sequence* from that
basis (`NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup`). Being an instance is the
point — it is what lets a Huber ring be handed to that theorem without the caller discharging
anything. -/
instance IsHuberRing.isCountablyGenerated_nhds_zero : (𝓝 (0 : A)).IsCountablyGenerated :=
  IsHuberRing.nonempty_pairOfDefinition.elim fun P ↦ P.hasBasis_nhds_zero.isCountablyGenerated

/-- Wedhorn Corollary 6.4: the power-bounded subring of a Huber ring is open. -/
theorem isOpen_powerBoundedSubring : IsOpen (powerBoundedSubring A : Set A) := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  exact AddSubgroup.isOpen_mono (H₁ := P.ringOfDefinition.toAddSubgroup)
    (H₂ := (powerBoundedSubring A).toAddSubgroup) (fun x hx ↦ P.le_powerBoundedSubring hx)
    P.isOpen_ringOfDefinition

end HuberRing

section Tate

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

namespace IsPseudoUniformizer

variable {a : A} (ha : IsPseudoUniformizer a)
include ha

omit [IsTopologicalRing A] in
/-- Wedhorn: sufficiently high powers of a pseudouniformiser lie in a given ring of definition. -/
theorem eventually_pow_mem_ringOfDefinition (P : PairOfDefinition A) :
    ∀ᶠ n in atTop, a ^ n ∈ P.ringOfDefinition :=
  ha.isTopologicallyNilpotent.eventually_mem
    (P.isOpen_ringOfDefinition.mem_nhds P.ringOfDefinition.zero_mem)

omit [IsTopologicalRing A] in
/-- The scaled copy `ϖⁿ A₀` of a ring of definition is a neighbourhood of zero.

Only continuity of multiplication by a constant is needed: multiplication by the unit `ϖⁿ` is a
homeomorphism, so it carries the neighbourhood `A₀` of zero to a neighbourhood of zero. -/
theorem smul_ringOfDefinition_mem_nhds_zero [ContinuousConstSMul A A] (P : PairOfDefinition A)
    (n : ℕ) :
    (a ^ n) • (P.ringOfDefinition : Set A) ∈ 𝓝 (0 : A) := by
  have h := (ha.isUnit.pow n).smul_mem_nhds_smul_iff
    (s := (P.ringOfDefinition : Set A)) (a := (0 : A))
  rw [smul_zero] at h
  exact h.mpr (P.isOpen_ringOfDefinition.mem_nhds P.ringOfDefinition.zero_mem)

/-- Wedhorn: in a Tate ring the sets `ϖⁿ A₀` are a neighbourhood basis of zero, for any
pseudouniformiser `ϖ` and any ring of definition `A₀`.

Cofinality is the boundedness of `A₀` (`PairOfDefinition.isBounded_ringOfDefinition`) together
with `ϖⁿ → 0`; that each `ϖⁿ A₀` is itself a neighbourhood is
`smul_ringOfDefinition_mem_nhds_zero`. -/
theorem hasBasis_nhds_zero (P : PairOfDefinition A) :
    (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (a ^ n) • (P.ringOfDefinition : Set A) := by
  refine Filter.hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, ?_⟩
  · obtain ⟨V, hV, hVU⟩ := isBounded_iff.mp P.isBounded_ringOfDefinition U hU
    obtain ⟨n, hn⟩ := (ha.isTopologicallyNilpotent.eventually_mem hV).exists
    exact ⟨n, trivial, fun _ ⟨x, hx, hxy⟩ ↦ hxy ▸ hVU (Set.mul_mem_mul hn hx)⟩
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset (ha.smul_ringOfDefinition_mem_nhds_zero P n) hn

end IsPseudoUniformizer

/-- In a Tate ring one may choose a pseudouniformiser `ϖ` and a ring of definition `A₀` whose
scaled copies `ϖⁿ A₀` are a neighbourhood basis of zero. -/
theorem IsTateRing.exists_hasBasis_nhds_zero (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsTateRing A] : ∃ (a : A) (P : PairOfDefinition A),
      IsPseudoUniformizer a ∧
        (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (a ^ n) • (P.ringOfDefinition : Set A) := by
  obtain ⟨a, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  exact ⟨a, P, ha, ha.hasBasis_nhds_zero P⟩

end Tate

end TauCeti.Huber
