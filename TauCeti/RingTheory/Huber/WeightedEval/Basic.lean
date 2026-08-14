/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Evaluating a weighted restricted power series

Wedhorn's universal property of `A⟨X₁, …, Xₖ⟩_T` (Proposition 5.50) sends a `T`-restricted series
to the sum of its terms at a chosen tuple `b`. Before there is a map to speak of, that sum has to
exist, and this file supplies exactly that: the family of terms is summable.

Summability is where the defining condition earns its keep. `T`-restrictedness says that for each
open subgroup `U` of `A`, all but finitely many coefficients lie in `Tν · U`; so all but finitely
many terms lie in `(φ(Tν) · bν) · φ(U)`. If the weighted monomials `φ(Tν) · bν` stay inside one
bounded set — `TauCeti.Huber.IsWeightBounded` below, which is Wedhorn's hypothesis that the
variables are power-bounded *relative to the weights* — then shrinking `U` shrinks every one of
those terms at once, so the terms tend to zero along the cofinite filter. That convergence is the
*necessary* condition, not yet the sufficient one: it is completeness of the target that upgrades
it to summability, through Mathlib's
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.

## Main definitions

* `TauCeti.Huber.weightedEvalTerm`: the term `φ(coeff ν f) · bν` of the evaluation.
* `TauCeti.Huber.weightedVar` and `TauCeti.Huber.IsWeightedVarPowerBounded`: Wedhorn's own
  coordinatewise hypothesis — each weighted variable `φ(Tᵢ) · bᵢ` is power-bounded as a set.
* `TauCeti.Huber.IsWeightBounded`: the weighted monomials `φ(Tν) · bν` form a bounded set. This is
  the hypothesis the summability proof uses, and
  `TauCeti.Huber.isWeightBounded_of_isWeightedVarPowerBounded` derives it from the coordinatewise
  one for an arbitrary `T`. At the one-weight family it is *equivalent* to each `bᵢ` being
  power-bounded, which is Wedhorn's condition —
  `TauCeti.Huber.isWeightBounded_one_weight_iff_forall_isPowerBounded`.

## Main results

* `TauCeti.Huber.tendsto_weightedEvalTerm_cofinite_zero`: the terms tend to zero along the
  cofinite filter. This is the analytic input, and it needs no completeness.
* `TauCeti.Huber.summable_weightedEvalTerm`: completeness upgrades that convergence to
  summability.
* `TauCeti.Huber.summable_weightedEvalTerm_of_isWeightedVarPowerBounded`: the same stated with
  Wedhorn's coordinatewise hypothesis, for an arbitrary weight family.
* `TauCeti.Huber.summable_weightedEvalTerm_of_forall_isPowerBounded`: its one-weight reading, where
  the hypothesis is that each variable is power-bounded.

This file proves only the summability that the evaluation needs. The evaluation map itself is
`TauCeti.Huber.weightedEval` in `WeightedEval/Map.lean`, its packaging as a ring homomorphism is
`TauCeti.Huber.weightedEvalHom` in `WeightedEval/Hom.lean`, and its continuity is
`TauCeti.Huber.continuous_weightedEvalHom` in `WeightedEval/Continuous.lean`. The uniqueness that
makes Proposition 5.50 a universal property is
`TauCeti.Huber.weightedRestrictedSubring_ringHom_ext_of_continuous` in
`WeightedRestrictedSeries/Basic.lean`. `WeightedEval/UniversalProperty.lean` assembles the two
into an `∃!`, and states Proposition 5.50 itself — under Wedhorn's own coordinatewise
hypothesis — as
`existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isWeightedVarPowerBounded`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50, whose analytic core this is.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Terms

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

/-- The `ν`-th term of the evaluation of `f` at `b` along `φ`, namely `φ(coeff ν f) · bν`. -/
def weightedEvalTerm (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A)
    (ν : Fin k →₀ ℕ) : B :=
  φ (MvPowerSeries.coeff ν f) * ∏ i, b i ^ ν i

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- Unfolding lemma for `TauCeti.Huber.weightedEvalTerm`. -/
@[simp]
theorem weightedEvalTerm_def (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A)
    (ν : Fin k →₀ ℕ) :
    weightedEvalTerm φ b f ν = φ (MvPowerSeries.coeff ν f) * ∏ i, b i ^ ν i := (rfl)

/-- **The hypothesis on the tuple `b`**: the weighted monomials `φ(Tν) · bν`, over all
multi-indices at once, form a bounded subset of `B`.

This is Wedhorn's requirement that the variables be power-bounded *relative to the weights*, in
the form the summability argument uses. It is a condition on the whole family rather than on each
`bᵢ` separately, because the bound has to be uniform in `ν`. For the one-weight family `T ≡ {1}`
it is equivalent to each `bᵢ` being power-bounded, which is Wedhorn's condition: every monomial
`bν` lies in the pointwise product of the power-sets, and a finite pointwise product of bounded
sets is bounded. -/
def IsWeightBounded (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) : Prop :=
  IsBounded (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν)

omit [TopologicalSpace A] in
/-- Unfolding lemma for `TauCeti.Huber.IsWeightBounded`. The body is not exported, so this is how
a consumer supplies one or takes one apart. -/
theorem isWeightBounded_iff (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) :
    IsWeightBounded φ T b ↔
      IsBounded (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν) := (Iff.rfl)

omit [TopologicalSpace A] in
/-- **At the one-weight family the hypothesis is boundedness of the monomials.** With every weight
equal to `{1}` the weighted monomials are just the `bν`, so `IsWeightBounded` says exactly that
they form a bounded set — the condition a reader expects to see, and the bridge from the roadmap's
power-bounded-variable hypothesis. -/
@[simp]
theorem isWeightBounded_one_weight_iff (φ : A →+* B) (b : Fin k → B) :
    IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b ↔
      IsBounded (Set.range fun ν : Fin k →₀ ℕ ↦ ∏ i, b i ^ ν i) := by
  have hset : (⋃ ν : Fin k →₀ ℕ,
      (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow (fun _ : Fin k ↦ ({1} : Set A)) ν)
      = Set.range fun ν : Fin k →₀ ℕ ↦ ∏ i, b i ^ ν i := by
    ext x
    simp [weightPow_one_weight]
  rw [isWeightBounded_iff, hset]

omit [TopologicalSpace A] in
/-- **At the one-weight family the hypothesis is exactly Wedhorn's**: the weighted monomials are
bounded precisely when every variable is power-bounded.

This is the case in which the weights impose nothing, so the hypothesis on the tuple is the
familiar one; for a general `T` it is `TauCeti.Huber.IsWeightedVarPowerBounded` that plays this
role. -/
theorem isWeightBounded_one_weight_iff_forall_isPowerBounded (φ : A →+* B)
    (b : Fin k → B) :
    IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b ↔ ∀ i, IsPowerBounded (b i) := by
  rw [isWeightBounded_one_weight_iff]
  refine ⟨fun hb i ↦ isPowerBounded_iff.mpr (hb.subset ?_), fun hb ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨Finsupp.single i n, by simp [Finsupp.single_apply, Finset.prod_ite_eq]⟩
  · refine (isBounded_finsetProd Finset.univ
      (fun i _ ↦ isPowerBounded_iff.mp (hb i))).subset ?_
    rintro _ ⟨ν, rfl⟩
    exact Set.finsetProd_mem_finsetProd Finset.univ _ _ fun i _ ↦ ⟨ν i, rfl⟩


/-- The **weighted variables** of Proposition 5.50: the sets `φ(Tᵢ) · bᵢ`. The hypothesis 5.50
places on the tuple is about these, not about the `bᵢ` alone. -/
def weightedVar (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) (i : Fin k) : Set B :=
  φ '' T i * {b i}

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- Unfolding lemma for `TauCeti.Huber.weightedVar`. -/
@[simp]
theorem weightedVar_def (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) (i : Fin k) :
    weightedVar φ T b i = φ '' T i * {b i} := (rfl)

/-- **Wedhorn's coordinatewise hypothesis**: each weighted variable is power-bounded *as a set*,
its powers all lying in one bounded subset of `B`.

This is the condition Proposition 5.50 actually states, one index at a time, and
`TauCeti.Huber.isWeightBounded_of_isWeightedVarPowerBounded` derives the uniform bound
`TauCeti.Huber.IsWeightBounded` from it. At the one-weight family `weightedVar` is `{bᵢ}`, so it
reduces to each `bᵢ` being power-bounded. -/
def IsWeightedVarPowerBounded (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) : Prop :=
  ∀ i, IsBounded (⋃ n : ℕ, weightedVar φ T b i ^ n)

omit [TopologicalSpace A] in
/-- Unfolding lemma for `TauCeti.Huber.IsWeightedVarPowerBounded`. The body is not exported, so
this is how a consumer supplies one or takes one apart. -/
theorem isWeightedVarPowerBounded_iff (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) :
    IsWeightedVarPowerBounded φ T b ↔
      ∀ i, IsBounded (⋃ n : ℕ, weightedVar φ T b i ^ n) := (Iff.rfl)

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The weighted monomials at `ν` are the pointwise product of the `νᵢ`-th powers of the weighted
variables. Private: it is the bookkeeping behind the bridge below and says nothing on its own. -/
private theorem image_weightPow_mul_monomial (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B)
    (ν : Fin k →₀ ℕ) :
    (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν = ∏ i, weightedVar φ T b i ^ ν i := by
  have h1 : (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν
      = (φ '' weightPow T ν) * {∏ i, b i ^ ν i} := by
    rw [Set.mul_singleton, Set.image_image]
  have h2 : φ '' weightPow T ν = ∏ i, (φ '' T i) ^ ν i := by
    rw [image_weightPow, weightPow_def]
  have h3 : ({∏ i, b i ^ ν i} : Set B) = ∏ i, ({b i} : Set B) ^ ν i := by
    rw [← Set.finsetProd_singleton]
    exact Finset.prod_congr rfl fun i _ ↦ (Set.singleton_pow ..).symm
  rw [h1, h2, h3, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [weightedVar_def, mul_pow]

omit [TopologicalSpace A] in
/-- **Wedhorn's coordinatewise hypothesis gives the uniform bound.** Each weighted monomial set is
a finite pointwise product of powers of the weighted variables, so it lies in the product of the
bounded sets containing those powers — and a finite pointwise product of bounded sets is bounded.

This is what makes `TauCeti.Huber.IsWeightBounded` the right hypothesis for the summability
theorem rather than a stronger one invented for it: the two are reached from the same place. -/
theorem isWeightBounded_of_isWeightedVarPowerBounded {φ : A →+* B} {T : Fin k → Set A}
    {b : Fin k → B} (h : IsWeightedVarPowerBounded φ T b) : IsWeightBounded φ T b := by
  rw [isWeightBounded_iff]
  refine (isBounded_finsetProd Finset.univ
    (fun i _ ↦ (isWeightedVarPowerBounded_iff φ T b).mp h i)).subset (Set.iUnion_subset fun ν ↦ ?_)
  rw [image_weightPow_mul_monomial]
  exact Set.finsetProd_subset_finsetProd _ _ _ fun i _ ↦ Set.subset_iUnion _ _

variable [NonarchimedeanAddGroup A] [NonarchimedeanAddGroup B]

omit [TopologicalSpace A] [NonarchimedeanAddGroup A] [TopologicalSpace B]
  [NonarchimedeanAddGroup B] in
/-- **A coefficient bound gives a term bound**, at a single multi-index: if the `ν`-th coefficient
of `f` lies in `Tν · U`, and `φ(U)` times the weighted monomials at `ν` lands in the subgroup `G`,
then the `ν`-th term of the evaluation lies in `G`. Both the hypothesis and the conclusion concern
that one `ν`, and nothing topological is involved.

This is the estimate both convergence results run on.
`TauCeti.Huber.tendsto_weightedEvalTerm_cofinite_zero` applies it to the cofinitely many
coefficients that satisfy the bound; the continuity proof applies it to every coefficient at
once. -/
theorem weightedEvalTerm_mem_of_mem_weightMul {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}
    {U : AddSubgroup A} {V : Set B} {G : AddSubgroup B} {ν : Fin k →₀ ℕ}
    (hUV : (φ : A → B) '' U ⊆ V)
    (hVG : V * ((fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν) ⊆ (G : Set B))
    {f : MvPowerSeries (Fin k) A} (hf : MvPowerSeries.coeff ν f ∈ weightMul T ν U) :
    weightedEvalTerm φ b f ν ∈ G := by
  -- Multiplying by `bν` is additive, so `Tν · U` lands in `G` as soon as its generators do.
  let ψ : A →+ B := (AddMonoidHom.mulRight (∏ i, b i ^ ν i)).comp (φ : A →+ B)
  have hgen : ∀ t ∈ weightPow T ν, ∀ u ∈ U, t * u ∈ G.comap ψ := by
    intro t ht u hu
    -- On a generator the term is `φ u * (φ t * bν)`: a small element times a bounded one.
    have hval : ψ (t * u) = φ u * (φ t * ∏ i, b i ^ ν i) := by
      simp only [ψ, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
        AddMonoidHom.coe_coe, map_mul]
      ring
    simp only [AddSubgroup.mem_comap, hval]
    exact hVG (Set.mul_mem_mul (hUV ⟨u, hu, rfl⟩) ⟨t, ht, rfl⟩)
  have hcomap : MvPowerSeries.coeff ν f ∈ G.comap ψ := weightMul_le.mpr hgen hf
  -- `ψ` applied to the coefficient is the term `φ (coeff ν f) * bν`; rewriting rather than
  -- relying on the wrappers and coercions agreeing definitionally.
  simpa [weightedEvalTerm_def, ψ] using hcomap

/-- **The terms of the evaluation tend to zero along the cofinite filter.** This is the whole
analytic input to summability — the convergence a summable family must have. It needs no
completeness; completeness is what makes it *sufficient*, in
`TauCeti.Huber.summable_weightedEvalTerm`.

The three hypotheses each do one thing: `T`-restrictedness puts all but finitely many coefficients
into `Tν · U`, continuity of `φ` at zero makes `U` small enough that `φ(U)` shrinks the bounded
family, and `IsWeightBounded` is what makes one `U` work for every `ν` at once. -/
theorem tendsto_weightedEvalTerm_cofinite_zero {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {T : Fin k → Set A} {b : Fin k → B} (hb : IsWeightBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    Filter.Tendsto (weightedEvalTerm φ b f) Filter.cofinite (𝓝 0) := by
  refine Filter.tendsto_def.mpr fun W hW ↦ ?_
  obtain ⟨G, hGW⟩ := NonarchimedeanAddGroup.is_nonarchimedean W hW
  -- Shrink `G` by the bounded family of weighted monomials, then pull the result back along `φ`.
  obtain ⟨V, hV, hVG⟩ := isBounded_iff.mp ((isWeightBounded_iff φ T b).mp hb) (G : Set B)
    (G.isOpen.mem_nhds G.zero_mem)
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (hφ.preimage_mem_nhds
    (by simpa only [map_zero] using hV))
  -- All but finitely many coefficients lie in `Tν · U`, and every such term lands in `G`.
  filter_upwards [isWeightedRestricted_iff.mp hf U] with ν hν
  exact hGW (weightedEvalTerm_mem_of_mem_weightMul (fun _ ⟨u, hu, hval⟩ ↦ hval ▸ hUV hu)
    ((Set.mul_subset_mul_left (Set.subset_iUnion _ ν)).trans hVG) hν)


end Terms

section Summable

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanAddGroup B] [CompleteSpace B]

/-- **The evaluation of a `T`-restricted series is summable.** Its terms tend to zero along the
cofinite filter, which in a complete nonarchimedean group is summability. -/
theorem summable_weightedEvalTerm {φ : A →+* B} (hφ : ContinuousAt φ 0) {T : Fin k → Set A}
    {b : Fin k → B} (hb : IsWeightBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    Summable (weightedEvalTerm φ b f) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_weightedEvalTerm_cofinite_zero hφ hb hf)

/-- **Summability under Wedhorn's coordinatewise hypothesis**, for an arbitrary weight family:
each weighted variable power-bounded as a set is enough. This is the theorem above read through
`TauCeti.Huber.isWeightBounded_of_isWeightedVarPowerBounded`, and it is the form Proposition 5.50
states. -/
theorem summable_weightedEvalTerm_of_isWeightedVarPowerBounded {φ : A →+* B}
    (hφ : ContinuousAt φ 0)
    {T : Fin k → Set A} {b : Fin k → B} (hb : IsWeightedVarPowerBounded φ T b)
    {f : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f) :
    Summable (weightedEvalTerm φ b f) :=
  summable_weightedEvalTerm hφ (isWeightBounded_of_isWeightedVarPowerBounded hb) hf

/-- **Summability under Wedhorn's own hypothesis.** At the one-weight family the condition on the
tuple is that each variable be power-bounded, which is how Proposition 5.50 states it; this is the
theorem above read through
`TauCeti.Huber.isWeightBounded_one_weight_iff_forall_isPowerBounded`. -/
theorem summable_weightedEvalTerm_of_forall_isPowerBounded {φ : A →+* B}
    (hφ : ContinuousAt φ 0) {b : Fin k → B} (hb : ∀ i, IsPowerBounded (b i))
    {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f) :
    Summable (weightedEvalTerm φ b f) :=
  summable_weightedEvalTerm hφ
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf

end Summable

end TauCeti.Huber

end
