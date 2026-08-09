/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.Bounded
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Power-bounded and topologically nilpotent elements

An element of a topological ring is *power-bounded* when the set of its nonnegative powers is
bounded. Following Wedhorn, *Adic Spaces*, Definitions 5.25 and 5.27, we write

```text
A°  = {a : A | the powers of a are bounded},
A°° = {a : A | aⁿ → 0}
```

for the power-bounded and the topologically nilpotent elements. Wedhorn Proposition 5.30 says that
`A°` is a subring of `A` and that `A°°` is an ideal of `A°`; both statements need `A` to be
nonarchimedean, that is, to have a neighbourhood basis of zero by additive subgroups. A basis by
open *ideals* would be too strong: a nonzero Tate ring has no proper open ideal.

Together with `TauCeti/RingTheory/Huber/Bounded.lean` this is the boundedness prerequisite of the
adic-spaces roadmap.

## Provenance

`IsPowerBounded`, `isPowerBounded_zero`, `isPowerBounded_one`, `isPowerBounded_mul_of_commute`,
`IsPowerBounded.mul`, `IsPowerBounded.neg`, `IsPowerBounded.of_isTopologicallyNilpotent`,
`IsPowerBounded.isTopologicallyNilpotent_mul_of_commute` and `powerBoundedSubring` are stated as
in William Coram's mathlib4#40013 (there `PowerBounded.subring`, and the last two under different
names), so that the two can be identified once that pull request lands. New here are
`IsPowerBounded.pow`, the nonarchimedean `IsPowerBounded.add` and `isTopologicallyNilpotent_add`,
`topologicallyNilpotentIdeal` and `coe_topologicallyNilpotentIdeal` — #40013 carries `A°°` as a
`Set.range` of an inclusion rather than as an ideal of `A°` — and the transport lemmas. The
selection and ordering of results follows AINTLIB's `Bounded.lean`, the roadmap's designated prior
formalisation of this layer; its proofs were not used.

## Main definitions

* `TauCeti.Huber.IsPowerBounded`: the powers of `a` form a bounded set.
* `TauCeti.Huber.powerBoundedSubring`: the subring `A°` of power-bounded elements.
* `TauCeti.Huber.topologicallyNilpotentIdeal`: the ideal `A°°` of `A°`.

## Main results

* `TauCeti.Huber.isPowerBounded_iff`: unfolding lemma for `IsPowerBounded`.
* `TauCeti.Huber.IsPowerBounded.of_isTopologicallyNilpotent`: `A°° ⊆ A°`.
* `TauCeti.Huber.isTopologicallyNilpotent_add_of_commute` and
  `TauCeti.Huber.isTopologicallyNilpotent_add`: commuting topologically nilpotent elements of a
  nonarchimedean ring have topologically nilpotent sum. Mathlib's `IsTopologicallyNilpotent.add`
  instead assumes a basis of open ideals, which excludes the Tate rings this is aimed at.
* `TauCeti.Huber.map_powerBoundedSubring`, `TauCeti.Huber.powerBoundedSubringEquiv`: `A°` is
  carried onto `B°` by a topological ring isomorphism, which therefore restricts to
  `A° ≃+* B°`; that restriction carries `A°°` onto `B°°`
  (`TauCeti.Huber.mem_topologicallyNilpotentIdeal_powerBoundedSubringEquiv_iff` pointwise,
  `TauCeti.Huber.map_topologicallyNilpotentIdeal` as an equality of ideals).
* `TauCeti.Huber.isPowerBounded_ringEquiv_iff`,
  `TauCeti.Huber.isTopologicallyNilpotent_ringEquiv_iff`: both constructions transport along a
  topological ring isomorphism.

## Implementation notes

`topologicallyNilpotentIdeal` is an ideal of `A°`, not of `A`, and is distinct from Mathlib's
`topologicalNilradical`, which is an ideal of the ring itself under `[IsLinearTopology R R]`. The
present ideal is available whenever `A` is nonarchimedean, and
`coe_topologicallyNilpotentIdeal` records that cutting down to `A°` loses no topologically
nilpotent element.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.25, Definition 5.27, Remark 5.28 and
  Proposition 5.30.
* William Coram, *feat: define bounded sets and power bounded elements*,
  [mathlib4#40013](https://github.com/leanprover-community/mathlib4/pull/40013).
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  `projects/AdicSpaces/Adic spaces/Bounded.lean`.

-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

section MonoidWithZero

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- An element is *power-bounded* if the set of its nonnegative powers is bounded. -/
def IsPowerBounded (a : M) : Prop := IsBounded (Set.range (a ^ · : ℕ → M))

/-- Unfolding lemma for `TauCeti.Huber.IsPowerBounded`. -/
theorem isPowerBounded_iff {a : M} :
    IsPowerBounded a ↔ IsBounded (Set.range (a ^ · : ℕ → M)) := (Iff.rfl)

/-- `0` is power-bounded. -/
@[simp]
theorem isPowerBounded_zero : IsPowerBounded (0 : M) := by
  refine isBounded_pair_zero_one.subset ?_
  rintro _ ⟨n, rfl⟩
  cases n <;> simp [zero_pow]

/-- `1` is power-bounded. -/
@[simp]
theorem isPowerBounded_one : IsPowerBounded (1 : M) := by
  refine isBounded_pair_zero_one.subset ?_
  rintro _ ⟨n, rfl⟩
  simp

end MonoidWithZero

section MonoidWithZeroLemmas

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R]

/-- A power of a power-bounded element is power-bounded. -/
theorem IsPowerBounded.pow {a : R} (ha : IsPowerBounded a) (m : ℕ) : IsPowerBounded (a ^ m) := by
  refine ha.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨m * n, pow_mul a m n⟩

/-- A product of commuting power-bounded elements is power-bounded. -/
theorem isPowerBounded_mul_of_commute {a b : R} (hab : Commute a b) (ha : IsPowerBounded a)
    (hb : IsPowerBounded b) : IsPowerBounded (a * b) := by
  refine (IsBounded.mul ha hb).subset ?_
  rintro _ ⟨n, rfl⟩
  -- `rintro … ⟨n, rfl⟩` leaves the goal as a beta-redex `(fun x ↦ _ ^ x) n`, which blocks `rw`
  change (a * b) ^ n ∈ _
  rw [hab.mul_pow]
  exact Set.mul_mem_mul ⟨n, rfl⟩ ⟨n, rfl⟩

/-- The product of a power-bounded element with a commuting topologically nilpotent element is
topologically nilpotent. -/
theorem IsPowerBounded.isTopologicallyNilpotent_mul_of_commute {a b : R} (hab : Commute a b)
    (ha : IsPowerBounded a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) := by
  rw [isPowerBounded_iff, isBounded_iff] at ha
  intro U hU
  obtain ⟨V, hV, hVU⟩ := ha U hU
  rw [Filter.mem_map]
  filter_upwards [hb.eventually_mem hV] with n hn
  -- `rintro … ⟨n, rfl⟩` leaves the goal as a beta-redex `(fun x ↦ _ ^ x) n`, which blocks `rw`
  change (a * b) ^ n ∈ U
  rw [hab.mul_pow, (hab.pow_pow n n).eq]
  exact hVU (Set.mul_mem_mul hn ⟨n, rfl⟩)

variable [ContinuousMul R]

/-- Topologically nilpotent elements are power-bounded: `A°° ⊆ A°`. -/
theorem IsPowerBounded.of_isTopologicallyNilpotent {a : R} (ha : IsTopologicallyNilpotent a) :
    IsPowerBounded a := by
  rw [isPowerBounded_iff, isBounded_iff]
  intro U hU
  have hmul : (fun p : R × R ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : R), (0 : R)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hmul
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hmul
  obtain ⟨N, hN⟩ := (ha.eventually_mem hU₂).exists_forall_of_atTop
  choose V hV hVU using fun i : Fin N ↦
    isBounded_iff.mp (isBounded_singleton (a ^ (i : ℕ))) U hU
  refine ⟨U₁ ∩ ⋂ i, V i, inter_mem hU₁ (Filter.iInter_mem.mpr hV), ?_⟩
  rintro _ ⟨v, hv, _, ⟨n, rfl⟩, rfl⟩
  by_cases hn : n < N
  · exact hVU ⟨n, hn⟩ (Set.mul_mem_mul (Set.mem_iInter.mp hv.2 ⟨n, hn⟩) rfl)
  · exact hprod (Set.mk_mem_prod hv.1 (hN n (by omega)))

end MonoidWithZeroLemmas

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [TopologicalSpace R]

/-- A product of power-bounded elements is power-bounded. -/
theorem IsPowerBounded.mul {a b : R} (ha : IsPowerBounded a) (hb : IsPowerBounded b) :
    IsPowerBounded (a * b) :=
  isPowerBounded_mul_of_commute (Commute.all ..) ha hb

/-- The product of a power-bounded element with a topologically nilpotent element is
topologically nilpotent. -/
theorem IsPowerBounded.isTopologicallyNilpotent_mul {a b : R} (ha : IsPowerBounded a)
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) :=
  ha.isTopologicallyNilpotent_mul_of_commute (Commute.all ..) hb

end CommMonoidWithZero

section CommRing

variable {A : Type*} [Ring A]

/-- If every binomial term `a ^ k * b ^ (n - k)` lies in an additive subgroup, then so does
`(a + b) ^ n`. This is the step shared by `IsPowerBounded.add_of_commute` and
`isTopologicallyNilpotent_add_of_commute`; only the two elements need to commute. -/
private theorem add_pow_mem_of_mul_pow_mem {G : AddSubgroup A} {a b : A} (hab : Commute a b)
    {n : ℕ} (h : ∀ k ≤ n, a ^ k * b ^ (n - k) ∈ G) : (a + b) ^ n ∈ G := by
  rw [hab.add_pow]
  refine sum_mem fun k hk ↦ ?_
  have hterm : a ^ k * b ^ (n - k) * (n.choose k : A)
      = (n.choose k) • (a ^ k * b ^ (n - k)) := by
    rw [nsmul_eq_mul, (Nat.cast_commute (n.choose k) _).eq]
  rw [hterm]
  exact nsmul_mem (h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) _

end CommRing

section Ring

variable {A : Type*} [Ring A] [TopologicalSpace A] [ContinuousMul A]

/-- The negative of a power-bounded element is power-bounded. -/
theorem IsPowerBounded.neg {a : A} (ha : IsPowerBounded a) : IsPowerBounded (-a) := by
  refine (((isBounded_singleton (-1 : A)).union (isBounded_singleton 1)).mul ha).subset ?_
  rintro _ ⟨n, rfl⟩
  -- `rintro … ⟨n, rfl⟩` leaves the goal as a beta-redex `(fun x ↦ _ ^ x) n`, which blocks `rw`
  change (-a) ^ n ∈ _
  rw [neg_pow]
  refine Set.mul_mem_mul ?_ ⟨n, rfl⟩
  rcases Nat.even_or_odd n with hn | hn <;> simp [hn.neg_one_pow]

/-- Power-boundedness is invariant under negation. -/
@[simp]
theorem isPowerBounded_neg {a : A} : IsPowerBounded (-a) ↔ IsPowerBounded a :=
  ⟨fun h ↦ by simpa using h.neg, IsPowerBounded.neg⟩

end Ring

section NonarchimedeanAddGroup

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanAddGroup A]

/-- A sum of commuting power-bounded elements is power-bounded in a nonarchimedean ring.

The binomial expansion writes `(a + b) ^ n` as an integer combination of products `aᵏ bᵐ`, so the
statement follows from `IsBounded.addSubgroupClosure`. Only `a` and `b` need to commute. -/
theorem IsPowerBounded.add_of_commute {a b : A} (hab : Commute a b) (ha : IsPowerBounded a)
    (hb : IsPowerBounded b) : IsPowerBounded (a + b) := by
  refine (IsBounded.mul ha hb).addSubgroupClosure.subset ?_
  rintro _ ⟨n, rfl⟩
  -- `rintro … ⟨n, rfl⟩` leaves the goal as a beta-redex `(fun x ↦ _ ^ x) n`, which blocks `rw`
  change (a + b) ^ n ∈ _
  rw [SetLike.mem_coe]
  refine add_pow_mem_of_mul_pow_mem hab fun k _ ↦ AddSubgroup.subset_closure ?_
  exact Set.mul_mem_mul ⟨k, rfl⟩ ⟨n - k, rfl⟩

/-- A sum of power-bounded elements of a nonarchimedean commutative ring is power-bounded. -/
theorem IsPowerBounded.add {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanAddGroup A] {a b : A} (ha : IsPowerBounded a) (hb : IsPowerBounded b) :
    IsPowerBounded (a + b) :=
  ha.add_of_commute (Commute.all a b) hb

section ContinuousMul

variable [ContinuousMul A]

/-- A sum of topologically nilpotent elements is topologically nilpotent in a nonarchimedean ring.

Mathlib's `IsTopologicallyNilpotent.add` assumes a neighbourhood basis of zero by open *ideals*,
which no nonzero Tate ring has; a basis by additive subgroups is enough. -/
theorem isTopologicallyNilpotent_add_of_commute {a b : A} (hab : Commute a b)
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hG : (G : Set A) ∈ 𝓝 (0 : A) := G.isOpen.mem_nhds G.zero_mem
  have ha' := IsPowerBounded.of_isTopologicallyNilpotent ha
  have hb' := IsPowerBounded.of_isTopologicallyNilpotent hb
  rw [isPowerBounded_iff, isBounded_iff] at ha' hb'
  obtain ⟨Va, hVa, hVaG⟩ := ha' _ hG
  obtain ⟨Vb, hVb, hVbG⟩ := hb' _ hG
  obtain ⟨Na, hNa⟩ := (ha.eventually_mem hVb).exists_forall_of_atTop
  obtain ⟨Nb, hNb⟩ := (hb.eventually_mem hVa).exists_forall_of_atTop
  rw [Filter.mem_map]
  filter_upwards [eventually_ge_atTop (Na + Nb)] with n hn
  refine hGU (?_ : (a + b) ^ n ∈ (G : Set A))
  rw [SetLike.mem_coe]
  refine add_pow_mem_of_mul_pow_mem hab fun k hkn ↦ ?_
  by_cases hk : Na ≤ k
  · exact hVbG (Set.mul_mem_mul (hNa k hk) ⟨n - k, rfl⟩)
  · rw [(hab.pow_pow k (n - k)).eq]
    exact hVaG (Set.mul_mem_mul (hNb (n - k) (by omega)) ⟨k, rfl⟩)

/-- Over a nonarchimedean commutative ring the topologically nilpotent elements are closed under
addition. Mathlib's `IsTopologicallyNilpotent.add` instead assumes a basis of open ideals, which
excludes the Tate rings this is aimed at. -/
theorem isTopologicallyNilpotent_add {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanAddGroup A] [ContinuousMul A] {a b : A} (ha : IsTopologicallyNilpotent a)
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a + b) :=
  isTopologicallyNilpotent_add_of_commute (Commute.all a b) ha hb

end ContinuousMul

end NonarchimedeanAddGroup

section Nonarchimedean

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

variable (A) in
/-- The subring `A°` of power-bounded elements of a nonarchimedean commutative ring
(Wedhorn Proposition 5.30). -/
def powerBoundedSubring : Subring A where
  carrier := {a : A | IsPowerBounded a}
  mul_mem' := IsPowerBounded.mul
  one_mem' := isPowerBounded_one
  add_mem' := IsPowerBounded.add
  zero_mem' := isPowerBounded_zero
  neg_mem' := IsPowerBounded.neg

/-- Membership in `A°` is power-boundedness. -/
@[simp]
theorem mem_powerBoundedSubring {a : A} : a ∈ powerBoundedSubring A ↔ IsPowerBounded a := Iff.rfl

variable (A) in
/-- The ideal `A°°` of topologically nilpotent elements inside `A°`
(Wedhorn Proposition 5.30). -/
def topologicallyNilpotentIdeal : Ideal (powerBoundedSubring A) where
  carrier := {a | IsTopologicallyNilpotent (a : A)}
  add_mem' := isTopologicallyNilpotent_add
  zero_mem' := IsTopologicallyNilpotent.zero
  smul_mem' a _ hb := a.2.isTopologicallyNilpotent_mul hb

/-- Membership in `A°°` is topological nilpotence. -/
@[simp]
theorem mem_topologicallyNilpotentIdeal {a : powerBoundedSubring A} :
    a ∈ topologicallyNilpotentIdeal A ↔ IsTopologicallyNilpotent (a : A) := Iff.rfl

/-- `A°°` is exactly the set of topologically nilpotent elements of `A`: no topologically
nilpotent element is lost by cutting down to `A°`. -/
@[simp]
theorem coe_topologicallyNilpotentIdeal :
    Subtype.val '' (topologicallyNilpotentIdeal A : Set (powerBoundedSubring A)) =
      {a : A | IsTopologicallyNilpotent a} :=
  Set.ext fun a ↦ ⟨by rintro ⟨b, hb, rfl⟩; exact hb,
    fun ha ↦ ⟨⟨a, IsPowerBounded.of_isTopologicallyNilpotent ha⟩, ha, rfl⟩⟩

/-- In a discrete ring every element is power-bounded, so `A° = A`. -/
@[simp]
theorem powerBoundedSubring_eq_top [DiscreteTopology A] : powerBoundedSubring A = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ isPowerBounded_iff.mpr (isBounded_of_discreteTopology _)

end Nonarchimedean

section Transport

variable {M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
  [TopologicalSpace M] [TopologicalSpace N]

/-- A morphism continuous at zero which carries neighbourhoods of zero to neighbourhoods of zero
preserves power-boundedness. As for `IsBounded.image`, continuity at zero alone is not enough. -/
theorem IsPowerBounded.map {F : Type*} [FunLike F M N] [MonoidWithZeroHomClass F M N] {f : F}
    (hf : ContinuousAt f 0) (hf₀ : ∀ V ∈ 𝓝 (0 : M), f '' V ∈ 𝓝 (0 : N)) {a : M}
    (ha : IsPowerBounded a) : IsPowerBounded (f a) := by
  refine (ha.image hf hf₀).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨a ^ n, ⟨n, rfl⟩, map_pow f a n⟩

/-- An open morphism continuous at zero preserves power-boundedness. -/
theorem IsPowerBounded.map_of_isOpenMap {F : Type*} [FunLike F M N] [MonoidWithZeroHomClass F M N]
    {f : F} (hf : ContinuousAt f 0) (hf₀ : IsOpenMap f) {a : M} (ha : IsPowerBounded a) :
    IsPowerBounded (f a) :=
  ha.map hf fun _ hV ↦ map_zero f ▸ hf₀.image_mem_nhds hV

variable {A B : Type*} [Semiring A] [Semiring B] [TopologicalSpace A] [TopologicalSpace B]

/-- Power-boundedness transports along a topological ring isomorphism. -/
@[simp]
theorem isPowerBounded_ringEquiv_iff (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {a : A} : IsPowerBounded (e a) ↔ IsPowerBounded a :=
  ⟨fun h ↦ by
      have := e.symm.toEquiv.continuous_symm_iff.mp (by simpa using he)
      simpa using h.map_of_isOpenMap he'.continuousAt this,
    fun h ↦ h.map_of_isOpenMap he.continuousAt (e.toEquiv.continuous_symm_iff.mp he')⟩

/-- Topological nilpotence transports along a topological ring isomorphism. -/
@[simp]
theorem isTopologicallyNilpotent_ringEquiv_iff (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {a : A} :
    IsTopologicallyNilpotent (e a) ↔ IsTopologicallyNilpotent a :=
  ⟨fun h ↦ by simpa using h.map (φ := (e.symm : B →+* A)) he', fun h ↦ h.map he⟩

section TransportSubring

variable {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
  [NonarchimedeanRing A] [NonarchimedeanRing B]

/-- `A°` is preserved by a topological ring isomorphism: `e` carries `A°` onto `B°`. This is the
bundled form of `TauCeti.Huber.isPowerBounded_ringEquiv_iff`. -/
@[simp]
theorem map_powerBoundedSubring (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    (powerBoundedSubring A).map (e : A →+* B) = powerBoundedSubring B := by
  ext b
  refine ⟨?_, fun hb ↦ ⟨e.symm b, ?_, e.apply_symm_apply b⟩⟩
  · rintro ⟨a, ha, rfl⟩
    exact (isPowerBounded_ringEquiv_iff e he he').mpr ha
  · exact (isPowerBounded_ringEquiv_iff e he he').mp (by simpa using hb)

/-- A topological ring isomorphism restricts to an isomorphism `A° ≃+* B°`. -/
def powerBoundedSubringEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    powerBoundedSubring A ≃+* powerBoundedSubring B :=
  e.restrict _ _ fun _ ↦ (isPowerBounded_ringEquiv_iff e he he').symm

@[simp]
theorem powerBoundedSubringEquiv_apply (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (a : powerBoundedSubring A) :
    ((powerBoundedSubringEquiv e he he' a : powerBoundedSubring B) : B) = e (a : A) := (rfl)

/-- `A°°` is preserved by a topological ring isomorphism: the restricted isomorphism `A° ≃+* B°`
carries `A°°` exactly onto `B°°`. See `TauCeti.Huber.map_topologicallyNilpotentIdeal` for the
bundled form. -/
theorem mem_topologicallyNilpotentIdeal_powerBoundedSubringEquiv_iff (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) (a : powerBoundedSubring A) :
    powerBoundedSubringEquiv e he he' a ∈ topologicallyNilpotentIdeal B
      ↔ a ∈ topologicallyNilpotentIdeal A := by
  rw [mem_topologicallyNilpotentIdeal, mem_topologicallyNilpotentIdeal,
    powerBoundedSubringEquiv_apply]
  exact isTopologicallyNilpotent_ringEquiv_iff e he he'

/-- The restricted isomorphism `A° ≃+* B°` carries the ideal `A°°` onto `B°°`. This is the
bundled form of
`TauCeti.Huber.mem_topologicallyNilpotentIdeal_powerBoundedSubringEquiv_iff`. -/
@[simp]
theorem map_topologicallyNilpotentIdeal (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) :
    (topologicallyNilpotentIdeal A).map
        (powerBoundedSubringEquiv e he he' : powerBoundedSubring A →+* powerBoundedSubring B) =
      topologicallyNilpotentIdeal B := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_) fun b hb ↦ ?_
  · exact (mem_topologicallyNilpotentIdeal_powerBoundedSubringEquiv_iff e he he' a).mpr ha
  · rw [← (powerBoundedSubringEquiv e he he').apply_symm_apply b]
    exact Ideal.mem_map_of_mem _
      ((mem_topologicallyNilpotentIdeal_powerBoundedSubringEquiv_iff e he he' _).mp
        (by rwa [RingEquiv.apply_symm_apply]))

end TransportSubring

end Transport

end TauCeti.Huber
