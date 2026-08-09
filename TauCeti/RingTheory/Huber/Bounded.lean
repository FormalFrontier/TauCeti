/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Bounded subsets of a topological ring

A subset `S` of a topological monoid with zero is *bounded* when every neighbourhood `U` of zero
absorbs `S`: there is a neighbourhood `V` of zero with `V * S ⊆ U`. This is the notion of
boundedness underlying Huber's theory of adic spaces (Wedhorn, *Adic Spaces*, Definition 5.27),
where it is the condition cutting out the rings of definition of a Huber ring.

## Provenance

`IsBounded` and the elementary calculus — `IsBounded.subset`, `isBounded_empty`,
`isBounded_singleton_zero`, `isBounded_pair_zero_one`, `IsBounded.union`, `IsBounded.mul`,
`isBounded_singleton` and `isBounded_finite` — are stated exactly as in William Coram's
mathlib4#40013 (several proofs follow it too), so that the two can be identified once that pull
request lands. Everything else here is new: `isBounded_iUnion`, the nonarchimedean
`IsBounded.addSubgroupClosure` and `IsBounded.add`, and the image and transport lemmas. The
selection and ordering of results follows AINTLIB's `Bounded.lean`, the roadmap's designated
prior formalisation of this layer; its proofs were not used.

## Main definitions

* `TauCeti.Huber.IsBounded`: `S` is bounded, i.e. every neighbourhood of zero absorbs `S`.

## Main results

* `TauCeti.Huber.isBounded_iff`: unfolding lemma for `IsBounded`.
* `TauCeti.Huber.isBounded_finite`: finite sets are bounded.
* `TauCeti.Huber.IsBounded.union`, `TauCeti.Huber.IsBounded.mul`: unions and pointwise products
  of bounded sets are bounded.
* `TauCeti.Huber.IsBounded.add`, `TauCeti.Huber.IsBounded.addSubgroupClosure`: over a ring with a
  nonarchimedean additive group, sums and the generated additive subgroup of bounded sets stay
  bounded.
* `TauCeti.Huber.IsBounded.image`: a morphism continuous at zero which is open at zero preserves
  boundedness, and `TauCeti.Huber.isBounded_image_ringEquiv_iff` transports boundedness along a
  topological ring isomorphism.

## Implementation notes

This is not Mathlib's `Bornology.IsVonNBounded`. That predicate asks that every neighbourhood of
zero *absorb* `S` after dilation by a norm-large scalar, so it needs a `SeminormedRing` of scalars
to have a bornology to be cofinal in; a Huber ring such as `ℤ_[p]⟦T⟧` with its `(p, T)`-adic
topology carries no such norm. The two notions agree over a nontrivially normed field acting on
itself, but neither the statement shape (`∃ V ∈ 𝓝 0, V * S ⊆ U` against
`∀ᶠ a in cobounded, S ⊆ a • U`) nor the hypotheses transfer.

Boundedness is *not* preserved by an arbitrary continuous homomorphism: giving `ℚ_[p]` the
discrete topology makes every subset bounded, while the identity to the `p`-adic topology is
continuous and `ℚ_[p]` is not bounded in itself. `IsBounded.image` therefore carries the extra
hypothesis that the morphism maps neighbourhoods of zero to neighbourhoods of zero.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27 and Remark 5.28.
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

/-- A subset `S` of a topological monoid with zero is *bounded* if for every neighbourhood `U`
of `0` there is a neighbourhood `V` of `0` with `V * S ⊆ U`. -/
def IsBounded (S : Set M) : Prop := ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : M), V * S ⊆ U

/-- Unfolding lemma for `TauCeti.Huber.IsBounded`. -/
theorem isBounded_iff {S : Set M} :
    IsBounded S ↔ ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : M), V * S ⊆ U := (Iff.rfl)

/-- Subsets of bounded sets are bounded. -/
theorem IsBounded.subset {S T : Set M} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  fun U hU ↦
    let ⟨V, hV, hVS⟩ := hS U hU
    ⟨V, hV, (Set.mul_subset_mul_left hTS).trans hVS⟩

/-- The empty set is bounded. -/
@[simp]
theorem isBounded_empty : IsBounded (∅ : Set M) :=
  fun _ _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- The singleton `{0}` is bounded. -/
@[simp]
theorem isBounded_singleton_zero : IsBounded ({0} : Set M) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun _ hx ↦ by simp_all [mem_of_mem_nhds hU]⟩

/-- The pair `{0, 1}` is bounded. -/
@[simp]
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set M) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · rw [mul_zero]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp hb, mul_one]⟩

/-- A finite union of bounded sets is bounded: intersect the absorbing neighbourhoods. -/
theorem isBounded_iUnion {ι : Sort*} [Finite ι] {S : ι → Set M} (hS : ∀ i, IsBounded (S i)) :
    IsBounded (⋃ i, S i) := by
  intro U hU
  choose V hV hVS using fun i ↦ hS i U hU
  refine ⟨⋂ i, V i, Filter.iInter_mem.mpr hV, ?_⟩
  rw [Set.mul_iUnion]
  exact Set.iUnion_subset fun i ↦
    (Set.mul_subset_mul_right (Set.iInter_subset _ i)).trans (hVS i)

/-- A finite indexed union is bounded exactly when every piece is. -/
@[simp]
theorem isBounded_iUnion_iff {ι : Sort*} [Finite ι] {S : ι → Set M} :
    IsBounded (⋃ i, S i) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun h i ↦ h.subset (Set.subset_iUnion _ i), isBounded_iUnion⟩

/-- The union of two bounded sets is bounded. -/
theorem IsBounded.union {S T : Set M} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  rw [Set.union_eq_iUnion]
  exact isBounded_iUnion (by rintro (_ | _) <;> assumption)

/-- A union is bounded exactly when both parts are. -/
@[simp]
theorem isBounded_union {S T : Set M} : IsBounded (S ∪ T) ↔ IsBounded S ∧ IsBounded T :=
  ⟨fun h ↦ ⟨h.subset Set.subset_union_left, h.subset Set.subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-- The pointwise product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set M} (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  intro U hU
  obtain ⟨W, hW, hTW⟩ := hT U hU
  obtain ⟨V, hV, hSV⟩ := hS W hW
  exact ⟨V, hV, by simpa [← mul_assoc] using (Set.mul_subset_mul_right hSV).trans hTW⟩

/-- Every subset of a discrete ring is bounded: `{0}` is already a neighbourhood of zero. -/
theorem isBounded_of_discreteTopology [DiscreteTopology M] (S : Set M) : IsBounded S := by
  rw [isBounded_iff]
  intro U hU
  refine ⟨{0}, by simp, ?_⟩
  rintro _ ⟨_, rfl, s, -, rfl⟩
  simpa using mem_of_mem_nhds hU

section ContinuousMul

variable [ContinuousMul M]

/-- Every singleton is bounded. -/
@[simp]
theorem isBounded_singleton (a : M) : IsBounded ({a} : Set M) :=
  fun U hU ↦ ⟨(· * a) ⁻¹' U, (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds
    (by simp [hU]), by simp⟩

/-- Every finite subset is bounded. -/
theorem isBounded_finite {S : Set M} (hS : S.Finite) : IsBounded S := by
  refine Set.Finite.induction_on S hS isBounded_empty fun {a s} _ _ ih ↦ ?_
  exact Set.insert_eq a s ▸ (isBounded_singleton a).union ih

end ContinuousMul

end MonoidWithZero

section Nonarchimedean

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanAddGroup A]

/-- The additive subgroup generated by a bounded set is bounded in a nonarchimedean ring.

This is the mechanism behind Wedhorn Proposition 5.30: a neighbourhood basis of zero by
subgroups lets one absorb an arbitrary `ℤ`-combination of a bounded set all at once. -/
theorem IsBounded.addSubgroupClosure {S : Set A} (hS : IsBounded S) :
    IsBounded (AddSubgroup.closure S : Set A) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hVS⟩ := hS _ (G.isOpen.mem_nhds G.zero_mem)
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, x, hx, rfl⟩
  refine hGU (?_ : v * x ∈ (G : Set A))
  induction hx using AddSubgroup.closure_induction with
  | mem s hs => exact hVS (Set.mul_mem_mul hv hs)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact G.toAddSubgroup.add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact G.toAddSubgroup.neg_mem hx

/-- The pointwise sum of two bounded sets is bounded in a nonarchimedean ring: `S + T` sits
inside the additive subgroup generated by `S ∪ T`. -/
theorem IsBounded.add {S T : Set A} (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S + T) := by
  refine (hS.union hT).addSubgroupClosure.subset ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure (.inl hs))
    (AddSubgroup.subset_closure (.inr ht))

end Nonarchimedean

section Image

variable {M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
  [TopologicalSpace M] [TopologicalSpace N]

/-- A morphism continuous at zero which carries neighbourhoods of zero to neighbourhoods of zero
sends bounded sets to bounded sets.

Boundedness is a condition at zero only, so continuity away from zero is irrelevant; but
continuity at zero alone is not enough, since refining the topology on the source only creates
bounded sets. -/
theorem IsBounded.image {F : Type*} [FunLike F M N] [MonoidWithZeroHomClass F M N] {f : F}
    (hf : ContinuousAt f 0) (hf₀ : ∀ V ∈ 𝓝 (0 : M), f '' V ∈ 𝓝 (0 : N)) {S : Set M}
    (hS : IsBounded S) : IsBounded (f '' S) := by
  intro U hU
  obtain ⟨V, hV, hVS⟩ := hS (f ⁻¹' U) (hf.preimage_mem_nhds (by rwa [map_zero]))
  exact ⟨f '' V, hf₀ V hV, by
    rw [← Set.image_mul]
    exact (Set.image_mono hVS).trans (Set.image_preimage_subset f U)⟩

/-- An open morphism continuous at zero sends bounded sets to bounded sets. -/
theorem IsBounded.image_of_isOpenMap {F : Type*} [FunLike F M N] [MonoidWithZeroHomClass F M N]
    {f : F} (hf : ContinuousAt f 0) (hf₀ : IsOpenMap f) {S : Set M} (hS : IsBounded S) :
    IsBounded (f '' S) :=
  hS.image hf fun _ hV ↦ map_zero f ▸ hf₀.image_mem_nhds hV

end Image

section Transport

variable {A B : Type*} [Semiring A] [Semiring B] [TopologicalSpace A] [TopologicalSpace B]

/-- A topological ring isomorphism sends bounded sets to bounded sets. -/
theorem IsBounded.image_ringEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {S : Set A} (hS : IsBounded S) : IsBounded (e '' S) :=
  hS.image_of_isOpenMap he.continuousAt (e.toEquiv.continuous_symm_iff.mp he')

/-- Boundedness transports along a topological ring isomorphism. -/
theorem isBounded_image_ringEquiv_iff (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {S : Set A} : IsBounded (e '' S) ↔ IsBounded S :=
  ⟨fun h ↦ by simpa [Set.image_image] using h.image_ringEquiv e.symm he' (by simpa using he),
    fun h ↦ h.image_ringEquiv e he he'⟩

end Transport

end TauCeti.Huber
