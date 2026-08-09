/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Restricted Power Series

This file defines restricted power series `A⟨T₁, …, Tₖ⟩`, following Wedhorn's *Adic Spaces*,
where the convergent/restricted power series ring is (5.6.1) in §5.6.

## Main definitions

* `IsRestricted`: A power series is **restricted** if its coefficients
  converge to `0` along the cofinite filter on multi-indices.
* `restrictedMvPowerSeriesSubring k A`: The subring of restricted power series in `k`
  variables over `A`, denoted `A⟨T₁, …, Tₖ⟩`.

## Provenance

This module is a port of AINTLIB's `projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean`,
the roadmap's designated prior formalisation of this material; the definitions, the statements and
the convolution argument are all its work. The port moves the declarations into the `TauCeti.Huber`
namespace, opts into the Lean module system with the definition bodies unexposed — hence the added
`isRestricted_iff` and `mem_restrictedMvPowerSeriesSubring` — tracks the Mathlib rename of
`Set.mem_setOf_eq` to `Set.mem_ofPred_eq`, renames the predicate from AINTLIB's `IsRestrictedAdic`
(nothing here is adic), and drops hypotheses that the individual proofs never used.

This is *not* Mathlib's `PowerSeries.IsRestricted`, which asks a one-variable series over a ring
with a linear topology to be restricted with respect to a submodule filtration. `IsRestricted`
here is Wedhorn's multivariate cofinite-tendsto condition, and needs only a topology on `A`; the
nonarchimedean hypothesis enters only for closure under multiplication and hence for the subring.

## Implementation notes

The restricted power series ring is defined as a subring of `MvPowerSeries (Fin k) A`
(the formal power series ring), cut out by the condition that coefficients tend to `0`.
This is the canonical concrete definition.

The closure of the restricted power series under multiplication (convolution) requires
that `A` is a topological ring. The proof that the convolution of two sequences tending
to `0` also tends to `0` uses the nonarchimedean property to ensure that
arbitrary finite sums of elements in an open additive subgroup remain in the subgroup.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], (5.6.1) in §5.6.
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  `projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean`.
-/

public section

open Filter

universe u

namespace TauCeti.Huber

/-! ### Restricted power series -/

/-- An element `f` of the multivariate power series ring `A⦃X₁, …, Xₖ⦄` is **restricted**
if its coefficients converge to `0` along the cofinite filter on multi-indices. That is,
for every open neighborhood `U` of `0` in `A`, all but finitely many coefficients of `f`
lie in `U`. This is the defining property of elements of `A⟨T₁, …, Tₖ⟩`.

See Wedhorn, (5.6.1) and §6.7. -/
def IsRestricted {k : ℕ} {A : Type*} [Semiring A] [TopologicalSpace A]
    (f : MvPowerSeries (Fin k) A) : Prop :=
  Tendsto (fun s : Fin k →₀ ℕ => MvPowerSeries.coeff s f) cofinite (nhds 0)

/-- Unfolding lemma for `TauCeti.Huber.IsRestricted`: the body is not exposed, so this is how
consumers recover the defining convergence condition. -/
theorem isRestricted_iff {k : ℕ} {A : Type*} [Semiring A] [TopologicalSpace A]
    {f : MvPowerSeries (Fin k) A} :
    IsRestricted f ↔
      Tendsto (fun s : Fin k →₀ ℕ => MvPowerSeries.coeff s f) cofinite (nhds 0) := (Iff.rfl)

/-- `0` is restricted: its coefficients are constantly `0`. -/
@[simp]
theorem isRestricted_zero (k : ℕ) (A : Type*) [Semiring A] [TopologicalSpace A] :
    IsRestricted (0 : MvPowerSeries (Fin k) A) := by
  rw [isRestricted_iff]
  simp only [map_zero]
  exact tendsto_const_nhds

/-- `1` is restricted: every coefficient but the `0`-th vanishes. -/
@[simp]
theorem isRestricted_one (k : ℕ) (A : Type*) [Semiring A] [TopologicalSpace A] :
    IsRestricted (1 : MvPowerSeries (Fin k) A) := by
  rw [isRestricted_iff]
  apply tendsto_nhds.mpr
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply (Set.finite_singleton (0 : Fin k →₀ ℕ)).subset
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hs (by rw [MvPowerSeries.coeff_one, if_neg h]; exact h0U)

/-- A sum of restricted series is restricted. -/
theorem IsRestricted.add {k : ℕ} {A : Type*} [Semiring A] [TopologicalSpace A]
    [ContinuousAdd A] {f g : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) (hg : IsRestricted g) : IsRestricted (f + g) := by
  rw [isRestricted_iff]
  have : Tendsto (fun s => MvPowerSeries.coeff s f + MvPowerSeries.coeff s g)
      cofinite (nhds 0) := by
    simpa using (isRestricted_iff.mp hf).add (isRestricted_iff.mp hg)
  exact this.congr (fun s => by simp [map_add])

/-- The negation of a restricted series is restricted. -/
theorem IsRestricted.neg {k : ℕ} {A : Type*} [Ring A] [TopologicalSpace A]
    [ContinuousNeg A] {f : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) : IsRestricted (-f) := by
  rw [isRestricted_iff]
  have : Tendsto (fun s => -(MvPowerSeries.coeff s f)) cofinite (nhds 0) := by
    simpa using (isRestricted_iff.mp hf).neg
  exact this.congr (fun s => by simp [map_neg])

/-- Restrictedness, restated: for every open additive subgroup `W`, all but finitely many
coefficients lie in `W`. This is the form the convolution argument actually consumes. -/
theorem IsRestricted.finite_coeff_notMem {k : ℕ} {A : Type*} [Ring A]
    [TopologicalSpace A] {f : MvPowerSeries (Fin k) A} (hf : IsRestricted f)
    (W : OpenAddSubgroup A) : {s | MvPowerSeries.coeff s f ∉ (W : Set A)}.Finite := by
  have := (tendsto_nhds.mp (isRestricted_iff.mp hf)) _ W.isOpen (SetLike.mem_coe.mpr W.zero_mem)
  rwa [Filter.mem_cofinite] at this

/-- The "bad" indices contributed by one side of a coefficient convolution form a finite set:
for each `a` in a finite `S`, only finitely many `n` have `c (n - a) ∉ T`, and `n ↦ n - a` is
injective on `{n | a ≤ n}`. Both halves of `IsRestricted.mul`'s bad set have this shape, with
the roles of the two series swapped. -/
private theorem finite_shift_bad_set {k : ℕ} {A : Type*}
    (S : Finset (Fin k →₀ ℕ)) (T : Set A) (c : (Fin k →₀ ℕ) → A)
    (hcT : {s | c s ∉ T}.Finite) : {n | ∃ a ∈ S, a ≤ n ∧ c (n - a) ∉ T}.Finite := by
  apply Set.Finite.subset (S.finite_toSet.biUnion (fun a _ => hcT.image (· + a)))
  intro n ⟨a, ha, han, hng⟩
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
  exact ⟨a, ha, n - a, hng, tsub_add_cancel_of_le han⟩

/-- Each term of the coefficient convolution lands in `V`. The trichotomy is on where the two
factors sit relative to `W`: if either is outside `W` then the *other* is in `T` by the
bad-set hypotheses, and `hT_left` / `hT_right` apply; if both are inside `W` then `hWV` does. -/
private theorem coeff_mul_mem_of_forall_mem {k : ℕ} {A : Type*} [Ring A] [TopologicalSpace A]
    {f g : MvPowerSeries (Fin k) A} (V W : OpenAddSubgroup A) (T : Set A)
    (hWV : ∀ x ∈ (W : Set A), ∀ y ∈ (W : Set A), x * y ∈ (V : Set A))
    (hT_left : ∀ a, MvPowerSeries.coeff a f ∉ (W : Set A) →
      ∀ y ∈ T, MvPowerSeries.coeff a f * y ∈ (V : Set A))
    (hT_right : ∀ b, MvPowerSeries.coeff b g ∉ (W : Set A) →
      ∀ x ∈ T, x * MvPowerSeries.coeff b g ∈ (V : Set A))
    (n : Fin k →₀ ℕ)
    (hnB1 : ∀ a, MvPowerSeries.coeff a f ∉ (W : Set A) → a ≤ n →
      MvPowerSeries.coeff (n - a) g ∈ T)
    (hnB2 : ∀ b, MvPowerSeries.coeff b g ∉ (W : Set A) → b ≤ n →
      MvPowerSeries.coeff (n - b) f ∈ T) :
    MvPowerSeries.coeff n (f * g) ∈ (V : Set A) := by
  classical
  rw [SetLike.mem_coe]
  rw [MvPowerSeries.coeff_mul]
  apply V.toAddSubgroup.sum_mem
  intro ⟨a, b⟩ hab
  rw [Finset.mem_antidiagonal] at hab
  by_cases haS : MvPowerSeries.coeff a f ∉ (W : Set A)
  · have hab_le : a ≤ n := hab ▸ le_add_right le_rfl
    have hb_eq : b = n - a := by rw [← hab]; exact (add_tsub_cancel_left a b).symm
    have hgT_b : MvPowerSeries.coeff b g ∈ T := by rw [hb_eq]; exact hnB1 a haS hab_le
    exact SetLike.mem_coe.mp (hT_left a haS _ hgT_b)
  · by_cases hbS : MvPowerSeries.coeff b g ∉ (W : Set A)
    · have hb_le : b ≤ n := hab ▸ le_add_left le_rfl
      have ha_eq : a = n - b := by rw [← hab]; exact (add_tsub_cancel_right a b).symm
      have hfT_a : MvPowerSeries.coeff a f ∈ T := by rw [ha_eq]; exact hnB2 b hbS hb_le
      exact SetLike.mem_coe.mp (hT_right b hbS _ hfT_a)
    · exact SetLike.mem_coe.mp (hWV _ (not_not.mp haS) _ (not_not.mp hbS))


/-- A product of restricted series is restricted. This is the only field of
`restrictedMvPowerSeriesSubring` that needs `A` nonarchimedean: the coefficient convolution is
a finite sum, and it is nonarchimedeanness that keeps such a sum inside an open subgroup. -/
theorem IsRestricted.mul {k : ℕ} {A : Type*} [Ring A] [TopologicalSpace A]
    [NonarchimedeanRing A] {f g : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) (hg : IsRestricted g) : IsRestricted (f * g) := by
  classical
  rw [isRestricted_iff]
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U (hU.mem_nhds h0U)
  obtain ⟨W, hWV⟩ := NonarchimedeanRing.mul_subset V
  set Sf := {s | MvPowerSeries.coeff s f ∉ (W : Set A)}
  set Sg := {s | MvPowerSeries.coeff s g ∉ (W : Set A)}
  have hSf : Sf.Finite := hf.finite_coeff_notMem W
  have hSg : Sg.Finite := hg.finite_coeff_notMem W
  -- A neighbourhood of `0` that the finitely many large coefficients multiply into `V`, on the
  -- left directly and on the right through the opposite ring.
  obtain ⟨T₁, hT₁mem, hT₁⟩ := exists_mem_nhds_zero_mul_subset
    (hSf.image fun a => MvPowerSeries.coeff a f).isCompact (V.isOpen.mem_nhds V.zero_mem)
  have hVop : MulOpposite.unop ⁻¹' (V : Set A) ∈ nhds (0 : Aᵐᵒᵖ) :=
    MulOpposite.continuous_unop.continuousAt.preimage_mem_nhds
      (by simpa using V.isOpen.mem_nhds V.zero_mem)
  obtain ⟨T₂, hT₂mem, hT₂⟩ := exists_mem_nhds_zero_mul_subset
    (hSg.image fun b => MulOpposite.op (MvPowerSeries.coeff b g)).isCompact hVop
  set T : Set A := T₁ ∩ MulOpposite.op ⁻¹' T₂ with hTdef
  have hT_nhds : T ∈ nhds (0 : A) :=
    Filter.inter_mem hT₁mem
      (MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hT₂mem))
  have hT_left : ∀ a ∈ hSf.toFinset, ∀ y ∈ T, MvPowerSeries.coeff a f * y ∈ (V : Set A) :=
    fun a ha y hy =>
      hT₁ (Set.mul_mem_mul (Set.mem_image_of_mem _ (hSf.mem_toFinset.mp ha)) hy.1)
  have hT_right : ∀ b ∈ hSg.toFinset, ∀ x ∈ T, x * MvPowerSeries.coeff b g ∈ (V : Set A) := by
    intro b hb x hx
    -- `hT₂` lives in `Aᵐᵒᵖ`, where the product is reversed; unopping it gives the `A`-statement.
    have hmem := hT₂ (Set.mul_mem_mul (Set.mem_image_of_mem _ (hSg.mem_toFinset.mp hb))
      (Set.mem_preimage.mp hx.2))
    simpa only [Set.mem_preimage, MulOpposite.unop_mul, MulOpposite.unop_op] using hmem
  have hgT : {s | MvPowerSeries.coeff s g ∉ T}.Finite :=
    (Filter.mem_cofinite.mp (isRestricted_iff.mp hg hT_nhds)).subset (fun s hs => hs)
  have hfT : {s | MvPowerSeries.coeff s f ∉ T}.Finite :=
    (Filter.mem_cofinite.mp (isRestricted_iff.mp hf hT_nhds)).subset (fun s hs => hs)
  set B := {n | ∃ a ∈ hSf.toFinset, a ≤ n ∧ MvPowerSeries.coeff (n - a) g ∉ T} ∪
           {n | ∃ b ∈ hSg.toFinset, b ≤ n ∧ MvPowerSeries.coeff (n - b) f ∉ T}
  have hB_finite : B.Finite :=
    (finite_shift_bad_set _ _ _ hgT).union (finite_shift_bad_set _ _ _ hfT)
  apply hB_finite.subset
  intro n hn
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hn
  by_contra hnB
  apply hn; clear hn
  simp only [B, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and] at hnB
  obtain ⟨hnB1, hnB2⟩ := hnB
  exact hVU (coeff_mul_mem_of_forall_mem V W T
    (fun x hx y hy => hWV ⟨x, hx, y, hy, rfl⟩)
    (fun a ha => hT_left a (hSf.mem_toFinset.mpr ha))
    (fun b hb => hT_right b (hSg.mem_toFinset.mpr hb))
    n
    (fun a ha han => not_not.mp (hnB1 a (hSf.mem_toFinset.mpr ha) han))
    (fun b hb hbn => not_not.mp (hnB2 b (hSg.mem_toFinset.mpr hb) hbn)))

/-- The set of restricted power series forms a subring of `MvPowerSeries (Fin k) A`.

The closure under multiplication (convolution of tendsto-0 coefficient sequences)
requires that `A` is a nonarchimedean topological ring (so that finite sums of elements in an
open additive subgroup remain in the subgroup). This is the canonical definition of
`A⟨T₁, …, Tₖ⟩` (Wedhorn, (5.6.1)/§5.6). -/
def restrictedMvPowerSeriesSubring (k : ℕ) (A : Type*) [Ring A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Subring (MvPowerSeries (Fin k) A) where
  carrier := {f | IsRestricted f}
  zero_mem' := isRestricted_zero k A
  one_mem' := isRestricted_one k A
  add_mem' := IsRestricted.add
  neg_mem' := IsRestricted.neg
  mul_mem' := IsRestricted.mul

/-- Membership in `A⟨T₁, …, Tₖ⟩` is restrictedness. -/
@[simp]
theorem mem_restrictedMvPowerSeriesSubring {k : ℕ} {A : Type*} [Ring A] [TopologicalSpace A]
    [NonarchimedeanRing A] {f : MvPowerSeries (Fin k) A} :
    f ∈ restrictedMvPowerSeriesSubring k A ↔ IsRestricted f := (Iff.rfl)

/-! ### Algebra instance -/

/-- Constant power series are restricted: the `algebraMap` image of any `a : A` has
coefficient `a` at multi-index `0` and `0` elsewhere, so it trivially tends to `0`. -/
@[simp]
theorem isRestricted_algebraMap {k : ℕ} {A : Type*} [CommSemiring A]
    [TopologicalSpace A] (a : A) :
    IsRestricted (algebraMap A (MvPowerSeries (Fin k) A) a) := by
  rw [isRestricted_iff]
  apply tendsto_nhds.mpr
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply (Set.finite_singleton (0 : Fin k →₀ ℕ)).subset
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hs (by rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg h]; exact h0U)

/-- The restricted power series subring inherits an `A`-algebra structure from the
`MvPowerSeries` algebra instance, since constant power series are restricted. -/
noncomputable instance restrictedMvPowerSeriesSubring.instAlgebra (k : ℕ) (A : Type*)
    [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    Algebra A (restrictedMvPowerSeriesSubring k A) :=
  RingHom.toAlgebra
    { toFun := fun a => ⟨algebraMap A (MvPowerSeries (Fin k) A) a,
        mem_restrictedMvPowerSeriesSubring.mpr (isRestricted_algebraMap a)⟩
      map_one' := by ext; simp only [map_one, OneMemClass.coe_one]
      map_mul' := by intros; ext; simp only [map_mul, Subring.coe_mul]
      map_zero' := by ext; simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := by intros; ext; simp only [map_add, Subring.coe_add] }

/-- The algebra structure on `A⟨T₁, …, Tₖ⟩` is the one inherited from `MvPowerSeries`: a constant
is sent to the constant power series. This characterises the instance, whose body is not
exposed. -/
@[simp]
theorem coe_algebraMap_restrictedMvPowerSeriesSubring {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (a : A) :
    ((algebraMap A (restrictedMvPowerSeriesSubring k A) a :
        restrictedMvPowerSeriesSubring k A) : MvPowerSeries (Fin k) A) =
      algebraMap A (MvPowerSeries (Fin k) A) a := (rfl)

end TauCeti.Huber
