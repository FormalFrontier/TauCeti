/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.Restricted.PowerSeries
public import TauCeti.Topology.Algebra.Nonarchimedean.Absorption
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Weighted restricted power series `A⟨X⟩_T`

For a commutative nonarchimedean ring `A` and a family `T` of subsets of `A` indexed by the
variables, Wedhorn defines the *weighted* restricted power series ring

```text
A⟨X⟩_T := { ∑ aν Xν ∈ A[[X]] ; aν ∈ Tν · U for every open subgroup U of A and almost all ν },
```

with the subgroups `U⟨X⟩ := { ∑ aν Xν ∈ A⟨X⟩_T ; aν ∈ Tν · U for all ν }` as a fundamental
system of neighbourhoods of zero. Here `Tν := T₁^ν₁ ⋯ Tₖ^νₖ`. Taking every `Tᵢ = {1}` recovers
the ordinary restricted series `A⟨X⟩`.

**Both of those claims need Wedhorn's standing hypothesis** `TauCeti.Huber.IsWeightFamily T`,
fixed at the start of his §5.6: without it `A⟨X⟩_T` is not multiplicatively closed and the
`U⟨X⟩` are not neighbourhoods of zero. The subring and topology constructions
(`weightedRestrictedSubring`, `weightedNhd`, `weightedTopology` and the maps into them) therefore
take it as an argument; the underlying weight operations `weightPow` and `weightMul` and the
predicate `IsWeightedRestricted` do not, since they are defined for any family. The
counterexample in `IsWeightFamily`'s docstring shows the hypothesis is not automatic.

## Main definitions

* `TauCeti.Huber.weightPow`: the subset `Tν = T₁^ν₁ ⋯ Tₖ^νₖ` of `A`.
* `TauCeti.Huber.weightMul`: the additive subgroup `Tν · U`.
* `TauCeti.Huber.IsWeightFamily`: Wedhorn's standing hypothesis on `T` — for every variable `i`,
  every `m` and every neighbourhood `U` of zero, the subgroup `Tᵢ^m · U` is again one. The
  subring and the topology below are defined only under it.
* `TauCeti.Huber.IsWeightedRestricted`: Wedhorn's condition (5.6.1) on a power series.
* `TauCeti.Huber.weightedRestrictedSubring`: `A⟨X⟩_T` as a subring of `A[[X]]`.
* `TauCeti.Huber.weightedNhd`: the subgroup `U⟨X⟩` of `A⟨X⟩_T`.
* `TauCeti.Huber.weightedTopology`: the ring topology they generate. `A⟨X⟩_T` also carries the
  group uniformity of that topology, with its `IsUniformAddGroup` and
  `UniformContinuousConstSMul` instances, so that its separated completion can be formed.
* `TauCeti.Huber.weightedC` and `TauCeti.Huber.weightedX`: the constant series and the variables.
* `TauCeti.Huber.weightedMap`: the morphism `A⟨X⟩_T → B⟨X⟩_S` induced by a continuous ring map
  carrying each weight into the corresponding one; `continuous_weightedMap` makes it a morphism of
  topological rings, and `weightedMap_id` with `weightedMap_comp` are the functor laws.

## Main results

* `TauCeti.Huber.IsWeightFamily.of_exists_isOpenMap_mul`, with
  `TauCeti.Huber.IsWeightFamily.of_exists_isUnit` and
  `TauCeti.Huber.IsWeightFamily.of_forall_openAddSubgroup`: the three ways to supply the standing
  hypothesis. The first is the roadmap's openness phrasing, in the form the argument needs —
  multiplication by an element of `Tᵢ` an open *map*, not merely of open image.
* `TauCeti.Huber.IsWeightedRestricted.mul`: `A⟨X⟩_T` is closed under multiplication, the point
  Wedhorn flags as not entirely clear; with the additive closure lemmas this gives the subring.
  `TauCeti.Huber.IsWeightedRestricted.finite_coeff_notMem` restates the predicate as finiteness of
  the exceptional set of coefficients.
* `TauCeti.Huber.weightedNhd_subgroups_basis`: the `U⟨X⟩` are a fundamental system of
  neighbourhoods of zero for a ring topology, with its contract
  (`hasBasis_nhds_zero_weightedTopology`, `isTopologicalRing_weightedTopology`,
  `nonarchimedeanRing_weightedTopology`, `continuous_weightedC`).
* `TauCeti.Huber.weightedRestrictedSubring_one_weight`: for the trivial weight this is the ordinary
  ring of restricted power series (Wedhorn Example 5.54).
* `TauCeti.Huber.weightedPolynomials`, the polynomials as a subring of `A⟨X⟩_T`, with
  `mem_weightedPolynomials_iff` identifying it with finite support and the generators
  `weightedC`/`weightedX` in it; `TauCeti.Huber.dense_weightedPolynomials` is Wedhorn 5.49(1),
  read off the predicate-level `exists_mvPolynomial_forall_coeff_sub_mem`.
* `TauCeti.Huber.weightedPolynomialEquiv`, with `discreteTopology_weightedRestrictedSubring`
  and `weightedPolynomials_eq_top`: over a discrete ring the weighted topology is discrete and
  `A⟨X⟩_T` is exactly the polynomial ring.
* `TauCeti.Huber.weightedRestrictedSubring_fin_zero` and
  `TauCeti.Huber.weightedRestrictedSubringFinZeroEquiv`, with
  `continuous_weightedRestrictedSubringFinZeroEquiv` and its `_symm`: in no variables every
  series is restricted, so `A⟨X⟩_T` is `A` — and topologically so, since the index `Fin 0 →₀ ℕ`
  is a singleton and the basic neighbourhood is cut out by that one coefficient. All of them are
  stated for an arbitrary `T : Fin 0 → Set A` and take no weight-family hypothesis:
  `TauCeti.Huber.isWeightFamily_fin_zero` supplies it, the condition being a statement about each
  index and there being none.
* `TauCeti.Huber.IsWeightedRestricted.map`, with `weightMul_map_le` and `image_weightPow`:
  restrictedness is preserved by a continuous ring map carrying each `T i` into `S i`. This is
  what `weightedMap` is built from; `weightedMap_weightedX` says it fixes the variables, while
  `weightedMap_weightedC` says it acts as `φ` on constants — the constants are moved, not fixed.
  `weightedMap_id` and `weightedMap_comp` are the functor laws.

## Scope

Wedhorn states (5.6.1) for an arbitrary index set `I`. This file formalises the finite-variable
case `I = Fin k`, which is what the roadmap's Layer 0.4 target needs; an arbitrary-index version
would run the weight through `Finsupp.prod` over the (finite) support of `ν`.

## Implementation notes

`Tν · U` is read as the additive subgroup *generated by* the products `t * u`, not as the
pointwise product set. Wedhorn's own statement forces this: he asserts that the `U⟨X⟩` are a
fundamental system of neighbourhoods of zero for a *ring* topology, so each must be an additive
subgroup, and the pointwise set `{t * u}` is not closed under addition.

The predicate carries no nonarchimedean hypothesis, matching (5.6.1), but it only *means*
coefficient convergence when the open additive subgroups are a neighbourhood basis of zero — the
setting Wedhorn works in throughout §5.6. Without that it can be vacuous: over `ℝ` with its usual
topology the only open additive subgroup is `ℝ` itself, so every power series is `T`-restricted
for the trivial weight. `TauCeti.Huber.isWeightedRestricted_one_weight_iff` therefore assumes
`NonarchimedeanAddGroup` — the additive condition is what rules that vacuity out, and no
multiplicative structure of the topology enters its proof.

If some `Tᵢ` is empty and `νᵢ > 0` then `Tν` is empty and `Tν · U = ⊥`, so the condition forces
those coefficients to vanish; the closure lemmas below need no nonemptiness hypothesis.

This construction is not the same as retopologising the ordinary `A⟨X⟩` by transporting along a
substitution `X ↦ f X`: there the weight multiplies the coefficient rather than the
neighbourhood, and the carrier does not vary with `T`. Here the carrier itself depends on `T`.

Nor is it Mathlib's `MvPowerSeries.IsRestricted`, despite that also being a weighted condition.
Mathlib weights by a polyradius `c : σ → ℝ` over a *normed* ring, asking that
`‖coeff t f‖ * ∏ i, c i ^ t i` tend to `0` along the cofinite filter. A Huber ring's topology is
nonarchimedean but in general carries no norm, so no polyradius is available to state that
condition, and the weight family here is a family of *subsets* `Tᵢ ⊆ A` acting on neighbourhood
subgroups rather than a family of reals scaling coefficient norms. The two do agree at the
trivial weight when the norm is *ultrametric*: the balls `{a ; ‖a‖ < r}` are then additive
subgroups, and every open subgroup contains one, so quantifying over all open subgroups is the
same as quantifying over the balls and the condition becomes `‖coeff ν f‖ → 0` along the
cofinite filter. Over a general normed ring they do not agree: over `ℝ`, as above, the condition
here is vacuous while Mathlib's still asks for `‖coeff ν f‖ → 0`. The unweighted predicate of
`TauCeti/RingTheory/Huber/Restricted/PowerSeries.lean` is a topological limit rather than a
condition on subgroups, and that file remarks on the comparison for it — in prose, not as a
proved declaration. Neither notion is a special case of the other in general.

The finite-family absorption fact the multiplicative arguments run on — finitely many fixed
elements are absorbed into their own targets by a single open subgroup — mentions no weight, so
it lives in `TauCeti/Topology/Algebra/Nonarchimedean/Absorption.lean`, built on Mathlib's
single-element `NonarchimedeanRing.left_mul_subset`.

Closure of `A⟨X⟩_T` under multiplication is the one non-obvious point of the construction —
Wedhorn writes "note that it is not entirely clear that `A⟨X⟩_T` is multiplicatively closed" — and
is `TauCeti.Huber.IsWeightedRestricted.mul` here. It is exactly what the standing hypothesis is
for.

## Provenance

The *construction* is new. The roadmap designates AINTLIB as the existing source for this row, so
its `AdicSpaces` weighted-series and localisation files were checked first: they contain no
`A⟨X⟩_T`, and AINTLIB's `TateAlgebraWedhorn` is a different object — it retopologises the ordinary
`A⟨X⟩` by transporting along a substitution rather than letting the carrier depend on `T`.

The *proofs*, however, follow `TauCeti/RingTheory/Huber/Restricted/PowerSeries.lean`
(TauCetiProject/TauCeti#2348), which is itself AINTLIB-derived — and not only in API layout. In
particular `TauCeti.Huber.IsWeightedRestricted.mul` follows the plan of `IsRestricted.mul` there:
choose `W` with `W · W ⊆ U`; take the finite sets of coefficients of `f` and `g` that fail the `W`
bound; find one open subgroup absorbing those finitely many bad coefficients into the target;
rule out the exceptional index set `(F + G_Z) ∪ (F_Z + G)`; and split each antidiagonal term by
whether neither, or exactly one, of its factors is bad.

What is new there is the weighting, and it is not cosmetic: the target `Tν · U` varies with the
index, so the absorbing subgroup has to work against a *family* of targets — which is what
`TauCeti.Huber.IsWeightFamily` is for and what
`NonarchimedeanRing.exists_openAddSubgroup_forall_mul_subset` was factored out to supply — and
the trichotomy has to land in `Tα · U` and `Tβ · U` separately before `mul_mem_weightMul_add`
recombines them at `α + β`. The unweighted proof needs none of that.

The API layout — the `isWeightedRestricted_zero/one/add/neg/mul` series, the subring with its
`mem_` lemma, and the algebra-map coercion — follows the same file.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48, equation (5.6.1),
  Proposition 5.49(1) for the density of the polynomials, and Example 5.54 for the case
  `Tᵢ = {1}`.
-/

open Filter Pointwise Topology

namespace TauCeti.Huber

public section

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The weight `Tν = T₁^ν₁ ⋯ Tₖ^νₖ` attached to a multi-index, as a subset of `A`. -/
def weightPow (T : Fin k → Set A) (ν : Fin k →₀ ℕ) : Set A := ∏ i, T i ^ ν i

omit [TopologicalSpace A] in
/-- Unfolding lemma for `TauCeti.Huber.weightPow`. -/
theorem weightPow_def (T : Fin k → Set A) (ν : Fin k →₀ ℕ) :
    weightPow T ν = ∏ i, T i ^ ν i := (rfl)

/-- The additive subgroup `Tν · U`. See the module docstring: the subgroup, not the pointwise
product set, is what Wedhorn's statement requires.

This is Mathlib's pointwise product of additive subgroups (`AddSubgroup.mul`, scoped to
`Pointwise`) applied to the subgroup generated by the weight. `weightMul_def` identifies it with
the subgroup generated by the products, which is the form the arguments below run on. -/
def weightMul (T : Fin k → Set A) (ν : Fin k →₀ ℕ) (U : AddSubgroup A) : AddSubgroup A :=
  AddSubgroup.closure (weightPow T ν) * U

omit [TopologicalSpace A] in
/-- `Tν · U` is the subgroup generated by the products `t * u`.

Both inclusions go through `AddSubgroup.mul_toAddSubmonoid`, which is how the subgroup product
exposes its elements: `AddSubmonoid.mul_induction_on` for `≤`, and `AddSubmonoid.mul_mem_mul` on
a generator for `≥`. -/
theorem weightMul_def (T : Fin k → Set A) (ν : Fin k →₀ ℕ) (U : AddSubgroup A) :
    weightMul T ν U = AddSubgroup.closure (weightPow T ν * (U : Set A)) := by
  refine le_antisymm (fun x hx ↦ ?_) (AddSubgroup.closure_le _ |>.mpr ?_)
  · refine AddSubmonoid.mul_induction_on hx (fun m hm n hn ↦ ?_)
      (fun _ _ h₁ h₂ ↦ AddSubgroup.add_mem _ h₁ h₂)
    refine AddSubgroup.closure_induction (p := fun m _ ↦ m * n ∈
      AddSubgroup.closure (weightPow T ν * (U : Set A))) (fun t ht ↦ ?_) ?_ ?_ ?_ hm
    · exact AddSubgroup.subset_closure ⟨t, ht, n, hn, rfl⟩
    · simp
    · intro y z _ _ hy hz
      simpa only [add_mul] using AddSubgroup.add_mem _ hy hz
    · intro y _ hy
      simpa only [neg_mul] using AddSubgroup.neg_mem _ hy
  · rintro _ ⟨t, ht, u, hu, rfl⟩
    exact AddSubmonoid.mul_mem_mul (AddSubgroup.subset_closure ht) hu

omit [TopologicalSpace A] in
/-- **Introduction for `weightMul`**: a product of a weight element and a `U` element lies in it. -/
theorem mul_mem_weightMul (T : Fin k → Set A) (ν : Fin k →₀ ℕ) (U : AddSubgroup A) {t u : A}
    (ht : t ∈ weightPow T ν) (hu : u ∈ U) : t * u ∈ weightMul T ν U :=
  AddSubmonoid.mul_mem_mul (AddSubgroup.subset_closure ht) hu

omit [TopologicalSpace A] in
/-- **Elimination for `weightMul`**: it is the least subgroup containing those products. -/
theorem weightMul_le {T : Fin k → Set A} {ν : Fin k →₀ ℕ} {U V : AddSubgroup A} :
    weightMul T ν U ≤ V ↔ ∀ t ∈ weightPow T ν, ∀ u ∈ U, t * u ∈ V := by
  rw [weightMul_def, AddSubgroup.closure_le]
  refine ⟨fun h t ht u hu ↦ h ⟨t, ht, u, hu, rfl⟩, ?_⟩
  rintro h _ ⟨t, ht, u, hu, rfl⟩
  exact h t ht u hu

omit [TopologicalSpace A] in
/-- **Elimination through a multiplication.** To land the whole of `a * (Tν · U)` inside a
subgroup `V` it is enough to land the generators `a * (t * u)`.  This is
`TauCeti.Huber.weightMul_le` read in `V.comap (AddMonoidHom.mulLeft a)`. -/
theorem mul_mem_of_forall_mul_mul_mem {T : Fin k → Set A} {ν : Fin k →₀ ℕ} {U V : AddSubgroup A}
    {a x : A} (h : ∀ t ∈ weightPow T ν, ∀ u ∈ U, a * (t * u) ∈ V) (hx : x ∈ weightMul T ν U) :
    a * x ∈ V :=
  weightMul_le (V := V.comap (AddMonoidHom.mulLeft a)) |>.mpr h hx

/-- Wedhorn's standing hypothesis on the weight family, fixed at the start of his §5.6: for every
variable `i`, every `m`, and every neighbourhood `U` of zero, the subgroup `Tᵢ^m · U` is again a
neighbourhood of zero.

Without it `A⟨X⟩_T` is not multiplicatively closed. Take `A = ℚ_p⟨Y, Z⟩`, `T = {Y}`, `f = Z X`
and `g = ∑ₙ Yⁿ pⁿ Xⁿ`: both are `T`-restricted, but the `Xᵏ` coefficient of `f * g` is
`Z Yᵏ⁻¹ pᵏ⁻¹`, which never lies in `Tᵏ · A = Yᵏ A`. Note that there `A` is complete, Tate and
Huber and `T` is finite, bounded and power-bounded — so none of those conditions substitute for
this one. What fails is exactly that `Y A` is not open. -/
def IsWeightFamily (T : Fin k → Set A) : Prop :=
  ∀ (i : Fin k) (m : ℕ) (U : Set A), U ∈ nhds (0 : A) →
    (AddSubgroup.closure (T i ^ m * U) : Set A) ∈ nhds (0 : A)

/-- Unfolding lemma for `TauCeti.Huber.IsWeightFamily`. -/
theorem isWeightFamily_iff {T : Fin k → Set A} :
    IsWeightFamily T ↔ ∀ (i : Fin k) (m : ℕ) (U : Set A), U ∈ nhds (0 : A) →
      (AddSubgroup.closure (T i ^ m * U) : Set A) ∈ nhds (0 : A) := (Iff.rfl)

/-- **The openness form of the standing hypothesis.** If some element of each `T i` multiplies
open sets to open sets, the family is a weight family.

This is the constructor for the roadmap's phrasing, which asks that each `Tᵢ · A` be open. Open
*image* is not by itself enough: it says the subgroup generated by `{t · a}` is open, whereas the
standing hypothesis needs `Tᵢ^m · U` to be a neighbourhood of zero for arbitrarily small `U`, i.e.
that multiplication by `t` is an open *map*. The two coincide under an open mapping theorem —
Henkel's, the Layer 0.6 target — which is not available here, so the map form is taken as the
hypothesis and `TauCeti.Huber.IsWeightFamily.of_exists_isUnit` is the case of it that needs no
such theorem. -/
theorem IsWeightFamily.of_exists_isOpenMap_mul {T : Fin k → Set A}
    (h : ∀ i, ∃ t ∈ T i, IsOpenMap (t * ·)) : IsWeightFamily T := by
  intro i m U hU
  obtain ⟨t, ht, hopen⟩ := h i
  refine Filter.mem_of_superset ?_ (AddSubgroup.subset_closure (k := T i ^ m * U))
  have hpow : IsOpenMap (t ^ m * · : A → A) := by
    induction m with
    | zero =>
      simp only [pow_zero, one_mul]
      exact IsOpenMap.id
    | succ n ih =>
      simpa only [pow_succ', mul_assoc, Function.comp_def] using hopen.comp ih
  have : (t ^ m * ·) '' U ∈ nhds ((t ^ m) * (0 : A)) :=
    hpow.image_mem_nhds (by simpa using hU)
  rw [mul_zero] at this
  refine Filter.mem_of_superset this ?_
  rintro _ ⟨u, hu, rfl⟩
  exact Set.mul_mem_mul (Set.pow_mem_pow ht) hu

/-- **Wedhorn's automatic case**: the standing hypothesis holds as soon as each weight contains a
unit.

One unit per index suffices — the other elements of `T i` are never used — and the existential
also carries the nonemptiness the statement needs: `(∅ : Set A) ^ m` is empty for `m > 0`, so the
subgroup it generates is `⊥`, a neighbourhood of zero only for the discrete topology.

This is `TauCeti.Huber.IsWeightFamily.of_exists_isOpenMap_mul` with its hypothesis discharged:
multiplication by a unit is an open map, needing no open mapping theorem. -/
theorem IsWeightFamily.of_exists_isUnit [SeparatelyContinuousMul A] {T : Fin k → Set A}
    (hu : ∀ i, ∃ t ∈ T i, IsUnit t) : IsWeightFamily T :=
  .of_exists_isOpenMap_mul fun i ↦
    let ⟨t, ht, htu⟩ := hu i
    ⟨t, ht, by simpa only [smul_eq_mul] using htu.isOpenMap_smul (α := A)⟩

/-- Wedhorn: the standing hypothesis is automatic when every `Tᵢ` is `{1}`, the important special
case, since then `Tᵢ^m · U` is the subgroup generated by `U`. -/
theorem isWeightFamily_one_weight : IsWeightFamily (fun _ : Fin k ↦ ({1} : Set A)) := by
  intro _ m U hU
  refine Filter.mem_of_superset hU fun u hu ↦ ?_
  exact AddSubgroup.subset_closure ⟨1, by simp, u, hu, by simp⟩

omit [TopologicalSpace A] in
/-- At the zero multi-index every factor is `T i ^ 0 = 1`, so the weight is the trivial
set `1 = {1}`. -/
@[simp]
theorem weightPow_zero (T : Fin k → Set A) : weightPow T 0 = 1 := by
  simp [weightPow]

omit [TopologicalSpace A] in
/-- At the zero multi-index the weight is trivial, so `T⁰ · U` is just `U`; in particular it is a
neighbourhood of zero whenever `U` is. -/
@[simp]
theorem weightMul_zero (T : Fin k → Set A) (U : AddSubgroup A) :
    weightMul T 0 U = U := by
  rw [weightMul_def, weightPow]
  simp

omit [TopologicalSpace A] in
/-- Weighting the zero subgroup gives the zero subgroup. -/
@[simp]
theorem weightMul_bot (T : Fin k → Set A) (ν : Fin k →₀ ℕ) :
    weightMul T ν (⊥ : AddSubgroup A) = ⊥ := by
  rw [weightMul_def]
  refine le_antisymm ((AddSubgroup.closure_le _).mpr ?_) bot_le
  rintro x ⟨s, -, u, hu, rfl⟩
  obtain rfl : u = 0 := by simpa using hu
  simp

/-- Wedhorn (5.6.1): a power series is *`T`-restricted* if, for every open subgroup `U` of `A`,
all but finitely many of its coefficients lie in `Tν · U`. -/
def IsWeightedRestricted (T : Fin k → Set A) (f : MvPowerSeries (Fin k) A) : Prop :=
  ∀ U : OpenAddSubgroup A,
    ∀ᶠ ν in cofinite, MvPowerSeries.coeff ν f ∈ weightMul T ν U.toAddSubgroup

/-- Unfolding lemma for `TauCeti.Huber.IsWeightedRestricted`. -/
theorem isWeightedRestricted_iff {T : Fin k → Set A} {f : MvPowerSeries (Fin k) A} :
    IsWeightedRestricted T f ↔ ∀ U : OpenAddSubgroup A,
      ∀ᶠ ν in cofinite, MvPowerSeries.coeff ν f ∈ weightMul T ν U.toAddSubgroup := (Iff.rfl)

/-- The zero series is `T`-restricted. -/
@[simp]
theorem isWeightedRestricted_zero (T : Fin k → Set A) :
    IsWeightedRestricted T (0 : MvPowerSeries (Fin k) A) := by
  intro U
  filter_upwards with ν
  simp

/-- The one series is `T`-restricted: every coefficient but the constant one vanishes. -/
@[simp]
theorem isWeightedRestricted_one (T : Fin k → Set A) :
    IsWeightedRestricted T (1 : MvPowerSeries (Fin k) A) := by
  classical
  intro U
  filter_upwards [(Set.finite_singleton (0 : Fin k →₀ ℕ)).compl_mem_cofinite] with ν hν
  rw [MvPowerSeries.coeff_one, ite_eq_right (by simpa using hν)]
  exact (weightMul T ν U.toAddSubgroup).zero_mem

omit [TopologicalSpace A] in
/-- Weights are multiplicative in the multi-index: `T^(α+β) = T^α · T^β`. -/
theorem weightPow_add (T : Fin k → Set A) (α β : Fin k →₀ ℕ) :
    weightPow T (α + β) = weightPow T α * weightPow T β := by
  simp only [weightPow, Finsupp.add_apply, pow_add]
  exact Finset.prod_mul_distrib

omit [TopologicalSpace A] in
/-- A product of an element of `T^α · V` with an element of `T^β · W` lies in
`T^(α+β) · (V · W)`. -/
theorem mul_mem_weightMul_add {T : Fin k → Set A} {α β : Fin k →₀ ℕ} {V W : AddSubgroup A} {x y : A}
    (hx : x ∈ weightMul T α V) (hy : y ∈ weightMul T β W) :
    x * y ∈ weightMul T (α + β) (AddSubgroup.closure ((V : Set A) * (W : Set A))) := by
  rw [mul_comm x y]
  refine mul_mem_of_forall_mul_mul_mem (fun t ht v hv ↦ ?_) hx
  rw [mul_comm y (t * v)]
  refine mul_mem_of_forall_mul_mul_mem (fun t' ht' w hw ↦ ?_) hy
  -- Regroup to `(weight) * (subgroup)`.  `ring_nf` normalises both sides to a common form that
  -- is neither of the two the next step needs, so the target shape is stated explicitly.
  rw [show t * v * (t' * w) = t * t' * (v * w) by ring]
  exact mul_mem_weightMul _ _ _ (weightPow_add T α β ▸ Set.mul_mem_mul ht ht')
    (AddSubgroup.subset_closure (Set.mul_mem_mul hv hw))

omit [TopologicalSpace A] in
/-- `Tν · U` is monotone in `U`. -/
theorem weightMul_mono (T : Fin k → Set A) (ν : Fin k →₀ ℕ) {U V : AddSubgroup A} (h : U ≤ V) :
    weightMul T ν U ≤ weightMul T ν V := by
  rw [weightMul_def, weightMul_def]
  exact AddSubgroup.closure_mono (Set.mul_subset_mul_left h)

omit [TopologicalSpace A] in
/-- **The unexceptional term of a convolution.** If `W · W ⊆ U`, then a product of an element of
`Tα · W` with an element of `Tβ · W` lies in `Tν · U` whenever `α + β = ν`. -/
theorem mul_mem_weightMul_of_mul_subset {T : Fin k → Set A} {α β ν : Fin k →₀ ℕ} (hν : α + β = ν)
    {W U : AddSubgroup A} (hWU : (W : Set A) * (W : Set A) ⊆ (U : Set A)) {a b : A}
    (ha : a ∈ weightMul T α W) (hb : b ∈ weightMul T β W) : a * b ∈ weightMul T ν U :=
  hν ▸ weightMul_mono T (α + β) ((AddSubgroup.closure_le _).mpr hWU) (mul_mem_weightMul_add ha hb)

omit [TopologicalSpace A] in
/-- Multiplying by a weight element shifts the multi-index: `T^β · (T^α · U) ⊆ T^(α+β) · U`. -/
theorem mul_mem_weightMul_add_of_mem_weightPow {T : Fin k → Set A} {α β : Fin k →₀ ℕ}
    {U : AddSubgroup A} {t x : A} (ht : t ∈ weightPow T β) (hx : x ∈ weightMul T α U) :
    t * x ∈ weightMul T (α + β) U := by
  refine mul_mem_of_forall_mul_mul_mem (fun t' ht' u hu ↦ ?_) hx
  -- As above: the goal must present as `(weight) * u` for `mul_mem_weightMul`, and only the
  -- weight factors commute past `u`, so the regrouping is stated rather than normalised.
  rw [show t * (t' * u) = t' * t * u by ring]
  exact mul_mem_weightMul _ _ _ (weightPow_add T α β ▸ Set.mul_mem_mul ht' ht) hu

omit [TopologicalSpace A] in
/-- At a single-variable multi-index the weight is the corresponding power: `T^(single i m)` is
`Tᵢ ^ m`. -/
theorem weightPow_single (T : Fin k → Set A) (i : Fin k) (m : ℕ) :
    weightPow T (Finsupp.single i m) = T i ^ m := by
  rw [weightPow, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

omit [TopologicalSpace A] in
/-- Splitting a multi-index splits the weight subgroup: `T^(α+β) · U` is generated by `T^α`
against `T^β · U`. -/
theorem weightMul_add_eq (T : Fin k → Set A) (α β : Fin k →₀ ℕ) (U : AddSubgroup A) :
    weightMul T (α + β) U
      = AddSubgroup.closure (weightPow T α * (weightMul T β U : Set A)) := by
  refine le_antisymm ?_ ?_
  · rw [weightMul_def, AddSubgroup.closure_le]
    rintro _ ⟨t, ht, u, hu, rfl⟩
    rw [weightPow_add] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    -- the goal's product is an unreduced beta-redex, so the witness is built directly
    exact AddSubgroup.subset_closure ⟨a, ha, b * u, mul_mem_weightMul T β U hb hu, by ring⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨t, ht, x, hx, rfl⟩
    exact add_comm α β ▸ mul_mem_weightMul_add_of_mem_weightPow ht hx

/-- **Wedhorn's derived hypothesis**: from the per-variable assumption that each `Tᵢ^m · U` is a
neighbourhood of zero it follows that `Tν · U` is one for every multi-index `ν`. Wedhorn states
this in a sentence: "Then `Tν U` is a neighborhood of `0` for all `ν`". -/
theorem IsWeightFamily.weightMul_mem_nhds {T : Fin k → Set A} (hT : IsWeightFamily T)
    (ν : Fin k →₀ ℕ) {U : AddSubgroup A} (hU : (U : Set A) ∈ nhds (0 : A)) :
    (weightMul T ν U : Set A) ∈ nhds (0 : A) := by
  induction ν using Finsupp.induction with
  | zero => rwa [weightMul_zero]
  | single_add i m ν' _ _ ih =>
      rw [weightMul_add_eq, weightPow_single]
      exact hT i m _ ih

/-- Over a nonarchimedean ring the standing hypothesis need only be checked on *open* subgroups:
those are cofinal in the neighbourhoods of zero, and `Tᵢ^m · V ≤ Tᵢ^m · U` for `V ⊆ U`. -/
theorem IsWeightFamily.of_forall_openAddSubgroup [NonarchimedeanAddGroup A] {T : Fin k → Set A}
    (h : ∀ (i : Fin k) (m : ℕ) (V : OpenAddSubgroup A),
      (weightMul T (Finsupp.single i m) V.toAddSubgroup : Set A) ∈ nhds (0 : A)) :
    IsWeightFamily T := by
  intro i m U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  refine Filter.mem_of_superset (h i m V) (SetLike.coe_subset_coe.mpr ?_)
  rw [weightMul_def, weightPow_single]
  exact AddSubgroup.closure_mono (Set.mul_subset_mul_left hVU)

/-- The subgroups `Tν · U` are themselves open, so they can be fed back into
`TauCeti.Huber.IsWeightedRestricted`, which quantifies over `OpenAddSubgroup A`. -/
theorem IsWeightFamily.isOpen_weightMul [SeparatelyContinuousAdd A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) (ν : Fin k →₀ ℕ) {U : AddSubgroup A}
    (hU : (U : Set A) ∈ nhds (0 : A)) : IsOpen (weightMul T ν U : Set A) :=
  AddSubgroup.isOpen_of_mem_nhds _ (hT.weightMul_mem_nhds ν hU)

/-- **The roadmap's phrasing of the standing hypothesis**: each `Tᵢ^m · A` is an open additive
subgroup of `A`. This is the `U = ⊤` case of `TauCeti.Huber.IsWeightFamily.isOpen_weightMul`.

Only this direction is proved. The roadmap (`AdicSpaces/README.md`, Layer 0.4) states the two
phrasings as equivalent, but recovering the condition for every neighbourhood `U` from the single
case `U = ⊤` is not derivable from the definitions here, and Wedhorn fixes the all-neighbourhoods
form as the standing hypothesis, so that is what `IsWeightFamily` says. -/
theorem IsWeightFamily.isOpen_weightMul_top [SeparatelyContinuousAdd A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) (i : Fin k) (m : ℕ) :
    IsOpen ((weightMul T (Finsupp.single i m) ⊤ : AddSubgroup A) : Set A) :=
  IsWeightFamily.isOpen_weightMul hT _ (by simp)

omit [TopologicalSpace A] in
/-- **The absorption step.** If multiplication by `a` carries the subgroup `Z` into `T^α · U`,
then it carries all of `T^β · Z` into `T^(α+β) · U`. -/
theorem mul_mem_weightMul_of_forall_mul_mem {T : Fin k → Set A} {α β : Fin k →₀ ℕ}
    {U Z : AddSubgroup A} {a b : A}
    (ha : ∀ z ∈ Z, a * z ∈ weightMul T α U) (hb : b ∈ weightMul T β Z) :
    a * b ∈ weightMul T (α + β) U := by
  refine mul_mem_of_forall_mul_mul_mem (fun t ht z hz ↦ ?_) hb
  rw [mul_left_comm]
  exact mul_mem_weightMul_add_of_mem_weightPow ht (ha z hz)

omit [TopologicalSpace A] in
/-- With every weight equal to `{1}`, the weight of any multi-index is `{1}`. -/
@[simp]
theorem weightPow_one_weight (ν : Fin k →₀ ℕ) :
    weightPow (fun _ : Fin k ↦ ({1} : Set A)) ν = {1} := by
  simp [weightPow]

omit [TopologicalSpace A] in
/-- With every weight equal to `{1}`, the subgroup `Tν · U` is `U` itself. -/
@[simp]
theorem weightMul_one_weight (ν : Fin k →₀ ℕ) (U : AddSubgroup A) :
    weightMul (fun _ : Fin k ↦ ({1} : Set A)) ν U = U := by
  rw [weightMul_def, weightPow_one_weight, Set.singleton_mul]
  simp

/-- **Wedhorn Example 5.54**: for the trivial weight `Tᵢ = {1}` the condition is the ordinary
restrictedness of `A⟨X⟩`, that the coefficients tend to zero along the cofinite filter. This is
the nontrivial witness that `TauCeti.Huber.IsWeightedRestricted` is not vacuous. -/
theorem isWeightedRestricted_one_weight_iff [NonarchimedeanAddGroup A]
    {f : MvPowerSeries (Fin k) A} :
    IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f ↔
      Tendsto (fun ν ↦ MvPowerSeries.coeff ν f) cofinite (nhds 0) := by
  rw [isWeightedRestricted_iff]
  constructor
  · intro h
    rw [tendsto_nhds]
    intro V hV h0V
    obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V (hV.mem_nhds h0V)
    filter_upwards [h U] with ν hν
    exact hUV (by simpa using hν)
  · intro h U
    have := (tendsto_nhds.mp h) _ U.isOpen (SetLike.mem_coe.mpr U.zero_mem)
    filter_upwards [this] with ν hν
    simpa using hν

/-- Anything with only finitely many nonzero coefficients is `T`-restricted, whatever the weight:
the zero coefficients meet every bound. This is the source of all the polynomial constructors
below. -/
theorem isWeightedRestricted_of_finite_support (T : Fin k → Set A)
    {f : MvPowerSeries (Fin k) A} (h : {ν | MvPowerSeries.coeff ν f ≠ 0}.Finite) :
    IsWeightedRestricted T f := by
  intro U
  rw [Filter.eventually_cofinite]
  refine h.subset fun ν hν ↦ ?_
  simp only [Set.mem_ofPred_eq] at hν ⊢
  exact fun hz ↦ hν (hz ▸ (weightMul T ν U.toAddSubgroup).zero_mem)

/-- A monomial is `T`-restricted. -/
@[simp]
theorem isWeightedRestricted_monomial (T : Fin k → Set A) (μ : Fin k →₀ ℕ) (a : A) :
    IsWeightedRestricted T (MvPowerSeries.monomial μ a) := by
  classical
  refine isWeightedRestricted_of_finite_support T ((Set.finite_singleton μ).subset fun ν hν ↦ ?_)
  simp only [Set.mem_ofPred_eq, MvPowerSeries.coeff_monomial] at hν
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  exact hν (ite_eq_right hne)

/-- A constant series is `T`-restricted. -/
@[simp]
theorem isWeightedRestricted_C (T : Fin k → Set A) (a : A) :
    IsWeightedRestricted T (MvPowerSeries.C a) := by
  simpa using isWeightedRestricted_monomial T 0 a

/-- Each variable is `T`-restricted. -/
@[simp]
theorem isWeightedRestricted_X (T : Fin k → Set A) (i : Fin k) :
    IsWeightedRestricted T (MvPowerSeries.X i : MvPowerSeries (Fin k) A) := by
  classical
  exact isWeightedRestricted_monomial T (Finsupp.single i 1) (1 : A)

/-- A sum of `T`-restricted series is `T`-restricted. -/
theorem IsWeightedRestricted.add {T : Fin k → Set A} {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) (hg : IsWeightedRestricted T g) :
    IsWeightedRestricted T (f + g) := by
  intro U
  filter_upwards [hf U, hg U] with ν hfν hgν
  simpa using (weightMul T ν U.toAddSubgroup).add_mem hfν hgν

/-- Weighted restrictedness, restated: for every open additive subgroup `U`, only finitely many
coefficients fail to lie in `Tν · U`. -/
theorem IsWeightedRestricted.finite_coeff_notMem {T : Fin k → Set A}
    {f : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f) (U : OpenAddSubgroup A) :
    {ν | MvPowerSeries.coeff ν f ∉ weightMul T ν U.toAddSubgroup}.Finite :=
  Filter.eventually_cofinite.mp (hf U)

/-- One open additive subgroup absorbing exceptional coefficients of two series at once: `Z` sends
`coeff α f * z` into `Tα · U` for every `α ∈ F`, and `coeff β g * z` into `Tβ · U` for every
`β ∈ G`. -/
private theorem exists_openAddSubgroup_forall_pair_weightMul_mem [NonarchimedeanRing A]
    {T : Fin k → Set A} (hT : IsWeightFamily T) (U : OpenAddSubgroup A)
    (F G : Finset (Fin k →₀ ℕ)) (f g : MvPowerSeries (Fin k) A) :
    ∃ Z : OpenAddSubgroup A,
      (∀ α ∈ F, ∀ z ∈ Z, MvPowerSeries.coeff α f * z ∈ weightMul T α U.toAddSubgroup) ∧
        ∀ β ∈ G, ∀ z ∈ Z, MvPowerSeries.coeff β g * z ∈ weightMul T β U.toAddSubgroup := by
  have hU : (U : Set A) ∈ nhds (0 : A) := U.isOpen.mem_nhds U.zero_mem
  obtain ⟨Z, hZ⟩ := NonarchimedeanRing.exists_openAddSubgroup_forall_mul_subset (F.disjSum G)
    (Sum.elim (fun α ↦ MvPowerSeries.coeff α f) fun β ↦ MvPowerSeries.coeff β g)
    (Sum.elim (fun α ↦ weightMul T α U.toAddSubgroup) fun β ↦ weightMul T β U.toAddSubgroup)
    (by rintro (α | β) _ <;> exact hT.weightMul_mem_nhds _ hU)
  exact ⟨Z, fun α hα z hz ↦ hZ (Sum.inl α) (Finset.inl_mem_disjSum.mpr hα) z hz,
    fun β hβ z hz ↦ hZ (Sum.inr β) (Finset.inr_mem_disjSum.mpr hβ) z hz⟩

/-- **`A⟨X⟩_T` is closed under multiplication** (Wedhorn 5.48, the point he flags as "not
entirely clear").

This is the substantive use of the standing hypothesis `TauCeti.Huber.IsWeightFamily` — the
neighbourhood half, `TauCeti.Huber.exists_weightedNhd_mul_mem`, uses it too — and the docstring
of that definition records what goes wrong without it. -/
theorem IsWeightedRestricted.mul [NonarchimedeanRing A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) (hg : IsWeightedRestricted T g) :
    IsWeightedRestricted T (f * g) := by
  -- Fix an open subgroup `U` and choose `W` with `W · W ⊆ U`.  The coefficients of `f` and `g`
  -- that fail the `W` bound form finite sets `F` and `G`.  The standing hypothesis makes each
  -- `Tα · U` a neighbourhood of zero, so one open subgroup `Z` absorbs every bad coefficient
  -- into its own `Tα · U`.  Writing `F_Z`, `G_Z` for the bad sets against `Z`, the exceptional
  -- set is `E = (F + G_Z) ∪ (F_Z + G)`, which is finite; for `ν ∉ E` every splitting
  -- `α + β = ν` has `α` bad, `β` bad, or neither, and each case lands in `Tν · U`.
  classical
  intro U
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.mul_subset U
  have hF := hf.finite_coeff_notMem W
  have hG := hg.finite_coeff_notMem W
  obtain ⟨Z, hZf, hZg⟩ := exists_openAddSubgroup_forall_pair_weightMul_mem hT U
    hF.toFinset hG.toFinset f g
  have hFZ := hf.finite_coeff_notMem Z
  have hGZ := hg.finite_coeff_notMem Z
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset ((hF.add hGZ).union (hFZ.add hG)) ?_
  intro ν hν
  by_contra hνE
  refine hν ?_
  rw [MvPowerSeries.coeff_mul]
  refine sum_mem fun p hp ↦ ?_
  have hsum : p.1 + p.2 = ν := Finset.mem_antidiagonal.mp hp
  by_cases hp1 : MvPowerSeries.coeff p.1 f ∈ weightMul T p.1 W.toAddSubgroup
  · by_cases hp2 : MvPowerSeries.coeff p.2 g ∈ weightMul T p.2 W.toAddSubgroup
    · -- both coefficients meet the `W` bound
      exact mul_mem_weightMul_of_mul_subset hsum hWU hp1 hp2
    · -- `p.2` is bad: absorb it, after commuting
      have hgood : MvPowerSeries.coeff p.1 f ∈ weightMul T p.1 Z.toAddSubgroup := by
        by_contra hbad
        exact hνE (Or.inr ⟨p.1, hbad, p.2, hp2, hsum⟩)
      rw [mul_comm, ← hsum, add_comm]
      exact mul_mem_weightMul_of_forall_mul_mem
        (fun z hz ↦ hZg p.2 (hG.mem_toFinset.mpr hp2) z hz) hgood
  · -- `p.1` is bad: absorb it
    have hgood : MvPowerSeries.coeff p.2 g ∈ weightMul T p.2 Z.toAddSubgroup := by
      by_contra hbad
      exact hνE (Or.inl ⟨p.1, hp1, p.2, hbad, hsum⟩)
    rw [← hsum]
    exact mul_mem_weightMul_of_forall_mul_mem
      (fun z hz ↦ hZf p.1 (hF.mem_toFinset.mpr hp1) z hz) hgood

/-- The negation of a `T`-restricted series is `T`-restricted. -/
theorem IsWeightedRestricted.neg {T : Fin k → Set A} {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) : IsWeightedRestricted T (-f) := by
  intro U
  filter_upwards [hf U] with ν hfν
  simpa using (weightMul T ν U.toAddSubgroup).neg_mem hfν

omit [TopologicalSpace A] in
/-- If *every* coefficient of `f` meets the `V` bound and every coefficient of `g` meets the `W`
bound, then every coefficient of `f * g` meets the `V · W` bound. Unlike
`TauCeti.Huber.IsWeightedRestricted.mul` there are no exceptional coefficients. -/
theorem coeff_mul_mem_weightMul {T : Fin k → Set A} {V W : AddSubgroup A}
    {f g : MvPowerSeries (Fin k) A}
    (hf : ∀ α, MvPowerSeries.coeff α f ∈ weightMul T α V)
    (hg : ∀ β, MvPowerSeries.coeff β g ∈ weightMul T β W) (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν (f * g)
      ∈ weightMul T ν (AddSubgroup.closure ((V : Set A) * (W : Set A))) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine sum_mem fun p hp ↦ ?_
  have hsum : p.1 + p.2 = ν := Finset.mem_antidiagonal.mp hp
  exact hsum ▸ mul_mem_weightMul_add (hf p.1) (hg p.2)

/-! ### The ring `A⟨X⟩_T` -/

/-- **Wedhorn's `A⟨X⟩_T`**: the weighted restricted power series form a subring of `A[[X]]`.

The weight family must satisfy Wedhorn's standing hypothesis
(`TauCeti.Huber.IsWeightFamily`); without it the carrier is not closed under multiplication, and
the docstring of that definition records the counterexample. -/
def weightedRestrictedSubring [NonarchimedeanRing A] (T : Fin k → Set A) (hT : IsWeightFamily T) :
    Subring (MvPowerSeries (Fin k) A) where
  carrier := {f | IsWeightedRestricted T f}
  mul_mem' := IsWeightedRestricted.mul hT
  one_mem' := isWeightedRestricted_one T
  add_mem' := IsWeightedRestricted.add
  zero_mem' := isWeightedRestricted_zero T
  neg_mem' := IsWeightedRestricted.neg

/-- Membership in `A⟨X⟩_T` is `T`-restrictedness. -/
@[simp]
theorem mem_weightedRestrictedSubring [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} {f : MvPowerSeries (Fin k) A} :
    f ∈ weightedRestrictedSubring T hT ↔ IsWeightedRestricted T f := (Iff.rfl)

/-- The constant-series embedding `A → A⟨X⟩_T`. -/
noncomputable def weightedC [NonarchimedeanRing A] (T : Fin k → Set A) (hT : IsWeightFamily T) :
    A →+* weightedRestrictedSubring T hT :=
  (MvPowerSeries.C : A →+* MvPowerSeries (Fin k) A).codRestrict _ (isWeightedRestricted_C T)

@[simp]
theorem coe_weightedC [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T} (a : A) :
    (weightedC T hT a : MvPowerSeries (Fin k) A) = MvPowerSeries.C a := (rfl)

/-- The variable `Xᵢ`, as an element of `A⟨X⟩_T`. -/
noncomputable def weightedX [NonarchimedeanRing A] (T : Fin k → Set A) (hT : IsWeightFamily T)
    (i : Fin k) :
    weightedRestrictedSubring T hT :=
  ⟨MvPowerSeries.X i, isWeightedRestricted_X T i⟩

@[simp]
theorem coe_weightedX [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T}
    (i : Fin k) :
    (weightedX T hT i : MvPowerSeries (Fin k) A) = MvPowerSeries.X i := (rfl)

/-- `A⟨X⟩_T` is an `A`-algebra, via the constant series. -/
noncomputable instance weightedRestrictedSubring.instAlgebra [NonarchimedeanRing A]
    (T : Fin k → Set A) (hT : IsWeightFamily T) : Algebra A (weightedRestrictedSubring T hT) :=
  (weightedC T hT).toAlgebra

@[simp]
theorem coe_algebraMap_weightedRestrictedSubring [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} (a : A) :
    ((algebraMap A (weightedRestrictedSubring T hT) a : weightedRestrictedSubring T hT) :
      MvPowerSeries (Fin k) A) = MvPowerSeries.C a := (rfl)

/-- **Wedhorn's neighbourhood subgroups** `U⟨X⟩`: the series all of whose coefficients — not
merely almost all — satisfy the `U` bound. These are the fundamental system of neighbourhoods of
zero for the topology on `A⟨X⟩_T`. -/
def weightedNhd [NonarchimedeanRing A] (T : Fin k → Set A) (hT : IsWeightFamily T)
    (U : AddSubgroup A) : AddSubgroup (weightedRestrictedSubring T hT) where
  carrier := {f | ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ weightMul T ν U}
  add_mem' hf hg ν := by simpa using (weightMul T ν U).add_mem (hf ν) (hg ν)
  zero_mem' ν := by simp
  neg_mem' hf ν := by simpa using (weightMul T ν U).neg_mem (hf ν)

/-- Membership in `U⟨X⟩` is the `U` bound on every coefficient. -/
@[simp]
theorem mem_weightedNhd [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T}
    {U : AddSubgroup A} {f : weightedRestrictedSubring T hT} :
    f ∈ weightedNhd T hT U ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ weightMul T ν U := (Iff.rfl)

/-- **Wedhorn Example 5.54, bundled**: for the trivial weight, `A⟨X⟩_T` *is* the ordinary ring of
restricted power series, not merely a predicate-level equivalent. -/
theorem weightedRestrictedSubring_one_weight [NonarchimedeanRing A] :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
      = restrictedMvPowerSeriesSubring k A := by
  ext f
  rw [mem_weightedRestrictedSubring, mem_restrictedMvPowerSeriesSubring,
    isWeightedRestricted_one_weight_iff, isRestricted_iff_coeff]

/-- The neighbourhood subgroups are monotone in `U`. -/
theorem weightedNhd_mono [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T}
    {U V : AddSubgroup A} (h : U ≤ V) : weightedNhd T hT U ≤ weightedNhd T hT V :=
  fun _ hf ν ↦ weightMul_mono T ν h (hf ν)

/-- **The multiplicative half of the neighbourhood basis**: if `W · W ⊆ U` then the product of two
elements of `W⟨X⟩` lies in `U⟨X⟩`. This is the condition
`RingSubgroupsBasis` calls `mul`, and unlike multiplicative closure of the ring it needs no
finiteness argument. -/
theorem mul_mem_weightedNhd [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} {W U : AddSubgroup A} (hWU : (W : Set A) * (W : Set A) ⊆ (U : Set A))
    {f g : weightedRestrictedSubring T hT} (hf : f ∈ weightedNhd T hT W)
    (hg : g ∈ weightedNhd T hT W) : f * g ∈ weightedNhd T hT U := by
  intro ν
  have := coeff_mul_mem_weightMul (T := T) (V := W) (W := W) hf hg ν
  exact weightMul_mono T ν ((AddSubgroup.closure_le _).mpr hWU) this

/-- **The left-multiplication half of the neighbourhood basis**: for a fixed `x ∈ A⟨X⟩_T` and an
open subgroup `U`, some `V⟨X⟩` is carried into `U⟨X⟩` by multiplication by `x`. This is the
condition `RingSubgroupsBasis` calls `leftMul`.

Unlike `TauCeti.Huber.mul_mem_weightedNhd` this does need the bad coefficients of `x` handled,
since `x` is only restricted rather than uniformly bounded — but no exceptional set of `ν`
survives, because the absorbing subgroup works for every `β` at once. -/
theorem exists_weightedNhd_mul_mem [NonarchimedeanRing A] {T : Fin k → Set A}
    (hT : IsWeightFamily T)
    (x : weightedRestrictedSubring T hT) (U : OpenAddSubgroup A) :
    ∃ V : OpenAddSubgroup A, ∀ g : weightedRestrictedSubring T hT,
      g ∈ weightedNhd T hT V.toAddSubgroup → x * g ∈ weightedNhd T hT U.toAddSubgroup := by
  classical
  have hUnhds : (U : Set A) ∈ nhds (0 : A) := U.isOpen.mem_nhds U.zero_mem
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.mul_subset U
  have hx : IsWeightedRestricted T (x : MvPowerSeries (Fin k) A) := x.2
  have hF := hx.finite_coeff_notMem W
  obtain ⟨Zx, hZx⟩ := NonarchimedeanRing.exists_openAddSubgroup_forall_mul_subset hF.toFinset
    (fun α ↦ MvPowerSeries.coeff α (x : MvPowerSeries (Fin k) A))
    (fun α ↦ weightMul T α U.toAddSubgroup) (fun α _ ↦ hT.weightMul_mem_nhds α hUnhds)
  refine ⟨W ⊓ Zx, fun g hg ν ↦ ?_⟩
  have hZleW : (W ⊓ Zx : OpenAddSubgroup A) ≤ W := inf_le_left
  have hZleZx : (W ⊓ Zx : OpenAddSubgroup A) ≤ Zx := inf_le_right
  rw [Subring.coe_mul, MvPowerSeries.coeff_mul]
  refine sum_mem fun p hp ↦ ?_
  have hsum : p.1 + p.2 = ν := Finset.mem_antidiagonal.mp hp
  by_cases hp1 : MvPowerSeries.coeff p.1 (x : MvPowerSeries (Fin k) A)
      ∈ weightMul T p.1 W.toAddSubgroup
  · -- `p.1` meets the `W` bound, and every coefficient of `g` meets the `W ⊓ Zx` bound
    exact mul_mem_weightMul_of_mul_subset hsum hWU hp1 (weightMul_mono T p.2 hZleW (hg p.2))
  · -- `p.1` is one of the finitely many bad coefficients: absorb it
    rw [← hsum]
    exact mul_mem_weightMul_of_forall_mul_mem
      (fun z hz ↦ hZx p.1 (hF.mem_toFinset.mpr hp1) z (hZleZx hz)) (hg p.2)

/-- **The neighbourhood basis of `A⟨X⟩_T`**: the subgroups `U⟨X⟩`, as `U` ranges over the open
subgroups of `A`, are a `RingSubgroupsBasis`. This is Wedhorn's assertion that they form a
fundamental system of neighbourhoods of zero for a ring topology. -/
theorem weightedNhd_subgroups_basis [NonarchimedeanRing A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) :
    RingSubgroupsBasis fun U : OpenAddSubgroup A ↦ weightedNhd T hT U.toAddSubgroup :=
  .of_comm _
    (fun U V ↦ ⟨U ⊓ V, le_inf (weightedNhd_mono inf_le_left) (weightedNhd_mono inf_le_right)⟩)
    (fun U ↦ by
      obtain ⟨W, hWU⟩ := NonarchimedeanRing.mul_subset U
      exact ⟨W, by
        rintro _ ⟨f, hf, g, hg, rfl⟩
        exact mul_mem_weightedNhd hWU hf hg⟩)
    (fun x U ↦ by
      obtain ⟨V, hV⟩ := exists_weightedNhd_mul_mem hT x U
      exact ⟨V, fun g hg ↦ hV g hg⟩)

/-- **Wedhorn's topology on `A⟨X⟩_T`** (Remark and Definition 5.48): the ring topology whose
neighbourhoods of zero are the `U⟨X⟩`.

Consumers should go through the contract lemmas below rather than unfolding this: the basis is
`hasBasis_nhds_zero_weightedTopology`, and `isTopologicalRing_weightedTopology` /
`nonarchimedeanRing_weightedTopology` give the structure.

It is an `instance` rather than a plain `def` so that a consumer of `A⟨X⟩_T` gets the topology,
and the `IsTopologicalRing` and `NonarchimedeanRing` structures below, by inference. Both `T` and
the standing hypothesis are implicit because they are read off the carrier's own type.

**On diamonds.** Mathlib does register a topology on `MvPowerSeries σ R`, but as a *scoped*
instance in `MvPowerSeries.WithPiTopology` (`Mathlib/RingTheory/MvPowerSeries/PiTopology.lean`).
It is therefore invisible here, and no file in this repository opens that scope; a downstream file
that did would get the induced subtype topology on the carrier alongside this instance, and would
have to say which it means. -/
noncomputable instance weightedTopology [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} : TopologicalSpace (weightedRestrictedSubring T hT) :=
  (weightedNhd_subgroups_basis hT).topology

/-- The `U⟨X⟩` are a basis of neighbourhoods of zero for `weightedTopology`. -/
theorem hasBasis_nhds_zero_weightedTopology [NonarchimedeanRing A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) :
    (nhds (0 : weightedRestrictedSubring T hT)).HasBasis (fun _ : OpenAddSubgroup A ↦ True)
      fun U ↦ (weightedNhd T hT U.toAddSubgroup : Set (weightedRestrictedSubring T hT)) :=
  (weightedNhd_subgroups_basis hT).hasBasis_nhds_zero

/-- `A⟨X⟩_T` is a topological ring. -/
instance isTopologicalRing_weightedTopology [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} : IsTopologicalRing (weightedRestrictedSubring T hT) :=
  (weightedNhd_subgroups_basis hT).toRingFilterBasis.isTopologicalRing

/-- `A⟨X⟩_T` is nonarchimedean: it inherits a basis of open additive subgroups at zero, as every
ring built from a `RingSubgroupsBasis` does. -/
instance nonarchimedeanRing_weightedTopology [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} : NonarchimedeanRing (weightedRestrictedSubring T hT) :=
  (weightedNhd_subgroups_basis hT).nonarchimedean

/-- The constant-series embedding `A → A⟨X⟩_T` is continuous.

A constant series has its only nonzero coefficient at `ν = 0`, where `T⁰ · U` is `U` itself, so
the open subgroup `U` already witnesses continuity at zero. -/
theorem continuous_weightedC [NonarchimedeanRing A] {T : Fin k → Set A} (hT : IsWeightFamily T) :
    Continuous (weightedC T hT) := by
  classical
  refine continuous_of_continuousAt_zero (weightedC T hT) ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_weightedTopology hT).tendsto_right_iff]
  intro U _
  filter_upwards [U.isOpen.mem_nhds U.zero_mem] with a ha ν
  rcases eq_or_ne ν 0 with rfl | hν
  · rw [weightMul_zero]
    simpa using ha
  · simp [coe_weightedC, MvPowerSeries.coeff_C, hν]


/-! ### Density of the polynomials -/

/-- A polynomial, read as a power series, has finitely many nonzero coefficients. Private: nothing
about the weighted construction enters, so this is a general fact about
`MvPolynomial.toMvPowerSeries` rather than something `TauCeti.Huber` should own a canonical name
for; it is used only by the two results below. -/
private theorem finite_support_toMvPowerSeries {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    {ν | MvPowerSeries.coeff ν (p : MvPowerSeries σ R) ≠ 0}.Finite :=
  p.support.finite_toSet.subset fun ν hν ↦ by
    simpa [MvPolynomial.coeff_coe, MvPolynomial.mem_support_iff] using hν

/-- Every polynomial is `T`-restricted, for any family `T`. -/
theorem isWeightedRestricted_toMvPowerSeries (T : Fin k → Set A) (p : MvPolynomial (Fin k) A) :
    IsWeightedRestricted T (p : MvPowerSeries (Fin k) A) :=
  isWeightedRestricted_of_finite_support T (finite_support_toMvPowerSeries p)

/-- **Wedhorn 5.49(1), the approximation step**, at predicate level: a `T`-restricted series is
approximated by a polynomial, coefficientwise inside `Tν · U`. Neither a nonarchimedean
hypothesis on `A` nor `IsWeightFamily T` is needed — only the ambient `[CommRing A]` and
`[TopologicalSpace A]` that `OpenAddSubgroup A` already asks for. -/
-- The polynomial is `f` truncated at the finitely many indices where its coefficient escapes
-- `Tν · U`; producing that finite set is what `TauCeti.Huber.IsWeightedRestricted` is for.
theorem exists_mvPolynomial_forall_coeff_sub_mem {T : Fin k → Set A}
    {f : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f) (U : OpenAddSubgroup A) :
    ∃ p : MvPolynomial (Fin k) A, ∀ ν, MvPowerSeries.coeff ν (f - (p : MvPowerSeries (Fin k) A))
      ∈ weightMul T ν U.toAddSubgroup := by
  classical
  have hbad := hf.finite_coeff_notMem U
  refine ⟨MvPowerSeries.truncFinset A hbad.toFinset f, fun ν ↦ ?_⟩
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncFinset]
  by_cases hν : ν ∈ hbad.toFinset
  · simp [hν]
  · have : MvPowerSeries.coeff ν f ∈ weightMul T ν U.toAddSubgroup := by
      by_contra hc
      exact hν (hbad.mem_toFinset.mpr hc)
    simpa [hν] using this

/-- **The coefficientwise inclusion of the polynomials into `A⟨X⟩_T`**, as a ring homomorphism.
Every polynomial is `T`-restricted, so it lands in `A⟨X⟩_T` and not merely in `A[[X]]`; its range
is `TauCeti.Huber.weightedPolynomials`. -/
noncomputable def weightedPolynomialHom [NonarchimedeanRing A] (T : Fin k → Set A)
    (hT : IsWeightFamily T) : MvPolynomial (Fin k) A →+* weightedRestrictedSubring T hT :=
  MvPolynomial.coeToMvPowerSeries.ringHom.codRestrict _
    (isWeightedRestricted_toMvPowerSeries T)

@[simp]
theorem coe_weightedPolynomialHom [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} (p : MvPolynomial (Fin k) A) :
    (weightedPolynomialHom T hT p : MvPowerSeries (Fin k) A) = (p : MvPowerSeries (Fin k) A) :=
  (rfl)

/-- The inclusion sends the polynomial constant `C a` to the constant series `weightedC a`. -/
@[simp]
theorem weightedPolynomialHom_C [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} (a : A) :
    weightedPolynomialHom T hT (MvPolynomial.C a) = weightedC T hT a :=
  Subtype.ext (by simp [coe_weightedC])

/-- The inclusion sends the polynomial variable `X i` to the weighted variable `weightedX i`. -/
@[simp]
theorem weightedPolynomialHom_X [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} (i : Fin k) :
    weightedPolynomialHom T hT (MvPolynomial.X i) = weightedX T hT i :=
  Subtype.ext (by simp [coe_weightedX])

/-- `A[X] ⊆ A⟨X⟩_T`, as a subring. -/
noncomputable def weightedPolynomials [NonarchimedeanRing A] (T : Fin k → Set A)
    (hT : IsWeightFamily T) : Subring (weightedRestrictedSubring T hT) :=
  (weightedPolynomialHom T hT).range

/-- Membership in `weightedPolynomials` is exactly having finitely many nonzero coefficients.

Deliberately not `@[simp]`: with this rewrite in the default set, the left-hand sides of
`weightedC_mem_weightedPolynomials` and `weightedX_mem_weightedPolynomials` stop being
simp-normal — simp turns them into `Set.Finite` goals it cannot then close — and `simpNF`
rejects them. The generator facts are the ones worth firing automatically. -/
theorem mem_weightedPolynomials_iff [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} {f : weightedRestrictedSubring T hT} :
    f ∈ weightedPolynomials T hT ↔
      {ν | MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ≠ 0}.Finite := by
  classical
  constructor
  · rintro ⟨p, rfl⟩
    simpa only [coe_weightedPolynomialHom] using finite_support_toMvPowerSeries p
  · intro hfin
    refine ⟨MvPowerSeries.truncFinset A hfin.toFinset (f : MvPowerSeries (Fin k) A), ?_⟩
    refine Subtype.ext (MvPowerSeries.ext fun ν ↦ ?_)
    rw [coe_weightedPolynomialHom, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncFinset]
    by_cases hν : ν ∈ hfin.toFinset
    · simp [hν]
    · simpa [hν] using (not_not.mp fun h ↦ hν (hfin.mem_toFinset.mpr h)).symm

/-- A constant series is a polynomial. -/
@[simp]
theorem weightedC_mem_weightedPolynomials [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} (a : A) : weightedC T hT a ∈ weightedPolynomials T hT :=
  ⟨MvPolynomial.C a, weightedPolynomialHom_C a⟩

/-- A weighted variable is a polynomial. -/
@[simp]
theorem weightedX_mem_weightedPolynomials [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} (i : Fin k) : weightedX T hT i ∈ weightedPolynomials T hT :=
  ⟨MvPolynomial.X i, weightedPolynomialHom_X i⟩

/-- **Wedhorn 5.49(1)**: the polynomials are dense in `A⟨X⟩_T`. -/
theorem dense_weightedPolynomials [NonarchimedeanRing A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) :
    Dense (weightedPolynomials T hT : Set (weightedRestrictedSubring T hT)) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  rw [← nhds_translation_add_neg x, Filter.mem_comap] at ht
  obtain ⟨V, hV, hVt⟩ := ht
  obtain ⟨U, -, hU⟩ := (hasBasis_nhds_zero_weightedTopology hT).mem_iff.mp hV
  obtain ⟨p, hp⟩ := exists_mvPolynomial_forall_coeff_sub_mem x.property U
  refine ⟨weightedPolynomialHom T hT p, hVt ?_, ⟨p, rfl⟩⟩
  refine hU ?_
  have hxp : x - weightedPolynomialHom T hT p ∈ weightedNhd T hT U.toAddSubgroup := fun ν ↦ by
    simpa only [AddSubgroupClass.coe_sub, coe_weightedPolynomialHom] using hp ν
  have hneg : (weightedPolynomialHom T hT p) - x ∈ weightedNhd T hT U.toAddSubgroup := by
    simpa only [neg_sub] using (weightedNhd T hT U.toAddSubgroup).neg_mem hxp
  simpa only [SetLike.mem_coe, sub_eq_add_neg] using hneg

/-- **Agreement on the generators propagates to the polynomials.** Two ring homomorphisms out of
`A⟨X⟩_T` that agree on every constant series and every variable agree on the whole polynomial
subring. No topology is involved. -/
theorem eqOn_weightedPolynomials [NonarchimedeanRing A] {T : Fin k → Set A}
    {hT : IsWeightFamily T} {B : Type*} [Semiring B]
    {f g : weightedRestrictedSubring T hT →+* B}
    (hC : ∀ a, f (weightedC T hT a) = g (weightedC T hT a))
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) :
    Set.EqOn f g (weightedPolynomials T hT : Set (weightedRestrictedSubring T hT)) := by
  have hcomp : f.comp (weightedPolynomialHom T hT) = g.comp (weightedPolynomialHom T hT) :=
    MvPolynomial.ringHom_ext (by simpa using hC) (by simpa using hX)
  exact Set.eqOn_range.mpr (congrArg (fun h : MvPolynomial (Fin k) A →+* B ↦ (h : _ → B)) hcomp)

/-- **A continuous homomorphism out of `A⟨X⟩_T` is determined by its values on the generators.**
Two of them agreeing on every constant series *and* every variable are equal. This is the
uniqueness half of Wedhorn 5.50: among *continuous* homomorphisms there is at most one extending a
given map on constants and sending each `Xᵢ` to a prescribed value.

Equality on the polynomial subring is propagated to the whole ring by its density, and that is
what continuity and the Hausdorff hypothesis are for. Whether uniqueness can fail without them is
not addressed here. -/
theorem weightedRestrictedSubring_ringHom_ext_of_continuous [NonarchimedeanRing A]
    {T : Fin k → Set A} (hT : IsWeightFamily T) {B : Type*} [Semiring B] [TopologicalSpace B]
    [T2Space B] {f g : weightedRestrictedSubring T hT →+* B} (hf : Continuous f)
    (hg : Continuous g) (hC : ∀ a, f (weightedC T hT a) = g (weightedC T hT a))
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) : f = g :=
  RingHom.coe_inj (hf.ext_on (dense_weightedPolynomials hT) hg (eqOn_weightedPolynomials hC hX))

/-! ### The discrete case

Over a discrete ring the picture collapses: `{0}` is an open subgroup, so a restricted series
has finitely many nonzero coefficients — `A⟨X⟩_T` *is* the polynomial ring — and the topology
generated by `U⟨X⟩` at `U = ⊥` is discrete. -/

/-- Over a discrete ring every weighted topology is discrete: `⊥⟨X⟩ = {0}` is open. -/
instance discreteTopology_weightedRestrictedSubring [NonarchimedeanRing A] [DiscreteTopology A]
    {T : Fin k → Set A} {hT : IsWeightFamily T} :
    DiscreteTopology (weightedRestrictedSubring T hT) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have h0 := (hasBasis_nhds_zero_weightedTopology hT).mem_of_mem
    (i := ⟨⊥, isOpen_discrete _⟩) trivial
  have heq : (weightedNhd T hT ((⟨⊥, isOpen_discrete _⟩ :
        OpenAddSubgroup A).toAddSubgroup) : Set (weightedRestrictedSubring T hT)) = {0} := by
    ext f
    simp only [SetLike.mem_coe, mem_weightedNhd, weightMul_bot, AddSubgroup.mem_bot,
      Set.mem_singleton_iff]
    exact ⟨fun h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ by simpa using h ν),
      fun h ν ↦ by simp [h]⟩
  rw [heq] at h0
  obtain ⟨t, hts, hto, ht0⟩ := mem_nhds_iff.mp h0
  obtain rfl : t = {0} := subset_antisymm hts (Set.singleton_subset_iff.mpr ht0)
  exact hto

/-- Over a discrete ring the restricted series are exactly the polynomials. -/
theorem weightedPolynomials_eq_top [NonarchimedeanRing A] [DiscreteTopology A]
    {T : Fin k → Set A} {hT : IsWeightFamily T} : weightedPolynomials T hT = ⊤ := by
  rw [Subring.eq_top_iff']
  intro f
  rw [mem_weightedPolynomials_iff]
  have h := (isWeightedRestricted_iff.mp (mem_weightedRestrictedSubring.mp f.2))
    ⟨⊥, isOpen_discrete _⟩
  simpa [weightMul_bot, Filter.eventually_cofinite] using h

/-- Over a discrete ring, the coefficientwise inclusion of the polynomials into `A⟨X⟩_T` is a
ring isomorphism. -/
noncomputable def weightedPolynomialEquiv [NonarchimedeanRing A] [DiscreteTopology A]
    (T : Fin k → Set A) (hT : IsWeightFamily T) :
    MvPolynomial (Fin k) A ≃+* weightedRestrictedSubring T hT :=
  RingEquiv.ofBijective (weightedPolynomialHom T hT)
    ⟨fun p q hpq ↦ MvPolynomial.coe_injective _ _ (by
        simpa only [coe_weightedPolynomialHom] using congrArg Subtype.val hpq),
      fun f ↦ by
        have hmem : f ∈ weightedPolynomials T hT := by
          rw [weightedPolynomials_eq_top (hT := hT)]
          exact Subring.mem_top f
        obtain ⟨p, hp⟩ := hmem
        exact ⟨p, hp⟩⟩

/-- The forward map of `weightedPolynomialEquiv` is the coefficientwise inclusion
`weightedPolynomialHom`, so its `coe_`/`_C`/`_X` lemmas apply. -/
@[simp]
theorem weightedPolynomialEquiv_apply [NonarchimedeanRing A] [DiscreteTopology A]
    {T : Fin k → Set A} {hT : IsWeightFamily T} (p : MvPolynomial (Fin k) A) :
    weightedPolynomialEquiv T hT p = weightedPolynomialHom T hT p := (rfl)

/-! ### Zero variables

At `k = 0` the coefficient index `Fin 0 →₀ ℕ` is a singleton: a series is its constant coefficient
and nothing else. So restrictedness is vacuous, and the basic neighbourhood cut out by a subgroup
`U` is exactly the series whose one coefficient lies in `U`, which is `U`.

Neither fact mentions the weight, so the whole section is stated for an arbitrary
`T : Fin 0 → Set A` — at `Fin 0` the only multi-index is `0`, and `weightMul T 0 U` is `U` for
every `T`. The weight-family hypothesis is not carried either: it quantifies over the index, so
`isWeightFamily_fin_zero` discharges it outright. -/

section ZeroVariables

variable (T : Fin 0 → Set A)

/-- **Every family of sets indexed by no variables is a weight family**, the condition being a
statement about each index and there being none. This is what lets the rest of this section drop
the hypothesis. -/
theorem isWeightFamily_fin_zero : IsWeightFamily T := fun i ↦ i.elim0

/-- **At zero variables every power series is restricted, whatever the weight.** There is only one
monomial, so every series has finite support. -/
@[simp]
theorem weightedRestrictedSubring_fin_zero [NonarchimedeanRing A] :
    weightedRestrictedSubring T (isWeightFamily_fin_zero T) = ⊤ := by
  ext f
  simpa using isWeightedRestricted_of_finite_support T (Set.toFinite _)

/-- **`A⟨⟩ = A`**: the restricted power series in no variables are `A` itself, as a ring. -/
noncomputable def weightedRestrictedSubringFinZeroEquiv [NonarchimedeanRing A] :
    weightedRestrictedSubring T (isWeightFamily_fin_zero T) ≃+* A :=
  (RingEquiv.subringCongr (weightedRestrictedSubring_fin_zero T)).trans <|
    Subring.topEquiv.trans (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv

/-- The zero-variable comparison is the constant coefficient. -/
@[simp]
theorem weightedRestrictedSubringFinZeroEquiv_apply [NonarchimedeanRing A]
    (f : weightedRestrictedSubring T (isWeightFamily_fin_zero T)) :
    weightedRestrictedSubringFinZeroEquiv T f =
      MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 0) A) := by
  simp [weightedRestrictedSubringFinZeroEquiv, RingEquiv.trans_apply,
    MvPowerSeries.isEmptyEquiv_apply]

/-- The zero-variable comparison is continuous. -/
theorem continuous_weightedRestrictedSubringFinZeroEquiv [NonarchimedeanRing A] :
    Continuous (weightedRestrictedSubringFinZeroEquiv T) := by
  refine continuous_of_continuousAt_zero
    (weightedRestrictedSubringFinZeroEquiv T).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology (isWeightFamily_fin_zero T)).tendsto_left_iff]
  intro V hV
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  refine ⟨U, trivial, fun f hf ↦ hUV ?_⟩
  have h := mem_weightedNhd.mp hf 0
  rw [weightMul_zero] at h
  simpa using h

/-- The inverse comparison sends `a` to the constant series. -/
@[simp]
theorem coe_weightedRestrictedSubringFinZeroEquiv_symm_apply [NonarchimedeanRing A] (a : A) :
    (((weightedRestrictedSubringFinZeroEquiv T).symm a :
        weightedRestrictedSubring T (isWeightFamily_fin_zero T)) :
      MvPowerSeries (Fin 0) A) = MvPowerSeries.C a := by
  simp [weightedRestrictedSubringFinZeroEquiv, RingEquiv.symm_trans_apply,
    MvPowerSeries.isEmptyEquiv_symm_apply]

/-- The inverse of the zero-variable comparison is continuous: it *is* the constant-series map
`weightedC`, whose continuity is already known. -/
theorem continuous_weightedRestrictedSubringFinZeroEquiv_symm [NonarchimedeanRing A] :
    Continuous (weightedRestrictedSubringFinZeroEquiv T).symm :=
  (continuous_weightedC (isWeightFamily_fin_zero T)).congr fun a ↦ Subtype.ext (by simp)

end ZeroVariables

/-! ### The uniform structure

`A⟨X⟩_T` carries the group uniformity of its additive topological group, so that its separated
completion can be formed. As with `weightedTopology` there is no diamond to fear: Mathlib's
uniformity on `MvPowerSeries` (like its topology) lives in the scoped
`MvPowerSeries.WithPiTopology`, so nothing else registers a `UniformSpace` on this carrier. -/

noncomputable instance [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T} :
    UniformSpace (weightedRestrictedSubring T hT) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T} :
    IsUniformAddGroup (weightedRestrictedSubring T hT) :=
  isUniformAddGroup_of_addCommGroup

instance [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T} :
    ContinuousConstSMul A (weightedRestrictedSubring T hT) :=
  ⟨fun a ↦ (continuous_const_mul (algebraMap A (weightedRestrictedSubring T hT) a)).congr
    fun f ↦ (Algebra.smul_def a f).symm⟩

instance [NonarchimedeanRing A] {T : Fin k → Set A} {hT : IsWeightFamily T} :
    UniformContinuousConstSMul A (weightedRestrictedSubring T hT) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

/-! ### Functoriality -/

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B]

omit [TopologicalSpace A] in
/-- The weight is monotone in the family. -/
theorem weightPow_mono {T S : Fin k → Set A} (h : ∀ i, T i ⊆ S i) (ν : Fin k →₀ ℕ) :
    weightPow T ν ⊆ weightPow S ν :=
  Finset.prod_le_prod' fun i _ ↦ Set.pow_subset_pow_left (h i)

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- A ring map carries the weight `Tν` onto the weight of the image family. -/
theorem image_weightPow (φ : A →+* B) (T : Fin k → Set A) (ν : Fin k →₀ ℕ) :
    φ '' weightPow T ν = weightPow (fun i ↦ φ '' T i) ν := by
  simp only [weightPow_def, Set.image_finsetProd, Set.image_pow]

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- **`weightMul` is functorial**: a ring map carrying each `T i` into `S i` and `U` into `V`
carries `Tν · U` into `Sν · V`. -/
theorem weightMul_map_le (φ : A →+* B) {T : Fin k → Set A} {S : Fin k → Set B}
    (hTS : ∀ i, φ '' T i ⊆ S i) (ν : Fin k →₀ ℕ) {U : AddSubgroup A} {V : AddSubgroup B}
    (hUV : U ≤ V.comap (φ : A →+ B)) :
    (weightMul T ν U).map (φ : A →+ B) ≤ weightMul S ν V := by
  rw [AddSubgroup.map_le_iff_le_comap]
  refine weightMul_le.mpr fun t ht u hu ↦ ?_
  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_coe, map_mul]
  exact mul_mem_weightMul S ν V
    (weightPow_mono hTS ν (image_weightPow φ T ν ▸ Set.mem_image_of_mem φ ht)) (hUV hu)

/-- **Restrictedness is functorial**: a continuous ring map carrying each `T i` into `S i`
carries `T`-restricted series to `S`-restricted ones. -/
theorem IsWeightedRestricted.map {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} (hTS : ∀ i, φ '' T i ⊆ S i) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    IsWeightedRestricted S (MvPowerSeries.map φ f) := by
  -- continuity is used exactly once: `φ ⁻¹' V` is the *open* subgroup `hf` gets applied to
  intro V
  filter_upwards [hf (OpenAddSubgroup.comap (φ : A →+ B) hφ V)] with ν hν
  rw [MvPowerSeries.coeff_map]
  exact weightMul_map_le φ hTS ν le_rfl ⟨_, hν, rfl⟩

/-- **The induced morphism `A⟨X⟩_T → B⟨X⟩_S`**: a continuous ring map `φ : A → B` carrying each
weight `T i` into `S i` induces one, acting coefficientwise.

The roadmap asks for functoriality as part of the §0.4 target; Wedhorn states the construction
(Remark and Definition 5.48) but numbers no separate result for the induced morphism, so this
carries no Wedhorn locator. The two weight families are given independently rather than taking
`S i := φ '' T i`, because the image of a weight family need not be one and the intended targets —
`S i` a bounded subset of `B` containing `φ '' T i` — are larger. -/
noncomputable def weightedMap [NonarchimedeanRing A] [NonarchimedeanRing B] {φ : A →+* B}
    (hφ : Continuous φ) {T : Fin k → Set A} {S : Fin k → Set B} (hT : IsWeightFamily T)
    (hS : IsWeightFamily S) (hTS : ∀ i, φ '' T i ⊆ S i) :
    weightedRestrictedSubring T hT →+* weightedRestrictedSubring S hS :=
  ((MvPowerSeries.map φ).comp (weightedRestrictedSubring T hT).subtype).codRestrict _
    fun f ↦ f.property.map hφ hTS

/-- `weightedMap` is `MvPowerSeries.map` with its codomain cut down, so its values coerce back to
the coefficientwise map. -/
@[simp]
theorem coe_weightedMap [NonarchimedeanRing A] [NonarchimedeanRing B] {φ : A →+* B}
    (hφ : Continuous φ) {T : Fin k → Set A} {S : Fin k → Set B} {hT : IsWeightFamily T}
    {hS : IsWeightFamily S} (hTS : ∀ i, φ '' T i ⊆ S i) (f : weightedRestrictedSubring T hT) :
    (weightedMap hφ hT hS hTS f : MvPowerSeries (Fin k) B) =
      MvPowerSeries.map φ (f : MvPowerSeries (Fin k) A) := (rfl)

/-- `weightedMap` is compatible with the constant-series embeddings. -/
@[simp]
theorem weightedMap_weightedC [NonarchimedeanRing A] [NonarchimedeanRing B] {φ : A →+* B}
    (hφ : Continuous φ) {T : Fin k → Set A} {S : Fin k → Set B} {hT : IsWeightFamily T}
    {hS : IsWeightFamily S} (hTS : ∀ i, φ '' T i ⊆ S i) (a : A) :
    weightedMap hφ hT hS hTS (weightedC T hT a) = weightedC S hS (φ a) :=
  Subtype.ext (by simp [MvPowerSeries.map_C])

/-- **`weightedMap` is continuous**, so the induced morphism is one of *topological* rings rather
than of the underlying rings only. -/
theorem continuous_weightedMap [NonarchimedeanRing A] [NonarchimedeanRing B] {φ : A →+* B}
    (hφ : Continuous φ) {T : Fin k → Set A} {S : Fin k → Set B} (hT : IsWeightFamily T)
    (hS : IsWeightFamily S) (hTS : ∀ i, φ '' T i ⊆ S i) :
    Continuous (weightedMap hφ hT hS hTS) := by
  -- the basic neighbourhood at `U = φ ⁻¹' V`, open by `hφ`, lands inside `V⟨X⟩`
  refine continuous_of_continuousAt_zero (weightedMap hφ hT hS hTS) ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_weightedTopology hS).tendsto_right_iff]
  intro V _
  refine Filter.mem_of_superset
    ((hasBasis_nhds_zero_weightedTopology hT).mem_of_mem (i := OpenAddSubgroup.comap
      (φ : A →+ B) hφ V) trivial) fun f hf ↦ ?_
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedNhd] at hf ⊢
  intro ν
  rw [coe_weightedMap, MvPowerSeries.coeff_map]
  exact weightMul_map_le φ hTS ν le_rfl ⟨_, hf ν, rfl⟩

/-- **The identity law**: the map induced by `RingHom.id` is the identity. -/
@[simp]
theorem weightedMap_id [NonarchimedeanRing A] {T : Fin k → Set A} (hT : IsWeightFamily T) :
    weightedMap (φ := RingHom.id A) (by simpa only [RingHom.coe_id] using continuous_id) hT hT
        (fun _ ↦ by simpa only [RingHom.coe_id] using (Set.image_id _).subset)
      = RingHom.id (weightedRestrictedSubring T hT) := by
  refine RingHom.ext fun f ↦ Subtype.ext ?_
  rw [coe_weightedMap, MvPowerSeries.map_id]
  rfl

/-- **The composition law**: the map induced by a composite is the composite of the induced maps.
With `weightedMap_id` this is what makes `A⟨X⟩_T` functorial in the pair `(A, T)`. -/
theorem weightedMap_comp [NonarchimedeanRing A] [NonarchimedeanRing B] {C : Type*} [CommRing C]
    [TopologicalSpace C] [NonarchimedeanRing C] {φ : A →+* B} {ψ : B →+* C} (hφ : Continuous φ)
    (hψ : Continuous ψ) {T : Fin k → Set A} {S : Fin k → Set B} {R : Fin k → Set C}
    (hT : IsWeightFamily T) (hS : IsWeightFamily S) (hR : IsWeightFamily R)
    (hTS : ∀ i, φ '' T i ⊆ S i) (hSR : ∀ i, ψ '' S i ⊆ R i) :
    weightedMap (φ := ψ.comp φ) (by simpa only [RingHom.coe_comp] using hψ.comp hφ) hT hR
        (fun i ↦ by
          simpa only [RingHom.coe_comp, Set.image_comp] using
            (Set.image_mono (hTS i)).trans (hSR i))
      = (weightedMap hψ hS hR hSR).comp (weightedMap hφ hT hS hTS) := by
  refine RingHom.ext fun f ↦ Subtype.ext ?_
  rw [coe_weightedMap, MvPowerSeries.map_comp]
  rfl

/-- `weightedMap` fixes the variables. -/
@[simp]
theorem weightedMap_weightedX [NonarchimedeanRing A] [NonarchimedeanRing B] {φ : A →+* B}
    (hφ : Continuous φ) {T : Fin k → Set A} {S : Fin k → Set B} {hT : IsWeightFamily T}
    {hS : IsWeightFamily S} (hTS : ∀ i, φ '' T i ⊆ S i) (i : Fin k) :
    weightedMap hφ hT hS hTS (weightedX T hT i) = weightedX S hS i :=
  Subtype.ext (by simp [MvPowerSeries.map_X])


end Functoriality


end

end TauCeti.Huber
