/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Data.Finsupp.Encodable
import TauCeti.Topology.LiftTendstoCofinite
import TauCeti.Order.Filter.ZeroAndBoundedAtFilter
import TauCeti.RingTheory.Huber.Bounded

/-!
# Restricted Power Series

This file defines restricted power series `A⟨T₁, …, Tₖ⟩`, following Wedhorn's *Adic Spaces*,
where the convergent/restricted power series ring is (5.6.1) in §5.6.

## Main definitions

* `IsRestricted`: A power series is **restricted** if its coefficients
  converge to `0` along the cofinite filter on multi-indices. The coefficients are asked only for
  a `0` and a topology, so the same predicate serves ring and module coefficients.
* `restrictedMvPowerSeriesSubring k A`: The subring of restricted power series in `k`
  variables over `A`, denoted `A⟨T₁, …, Tₖ⟩`.
* `restrictedMvPowerSeriesSubmodule k A M`: the `A`-submodule of restricted power series with
  coefficients in a topological `A`-module `M`, denoted `M⟨T₁, …, Tₖ⟩`. This is the object
  Wedhorn's Remark 8.29 compares with `M ⊗[A] A⟨T₁, …, Tₖ⟩`. It *is* Mathlib's
  `Filter.zeroAtFilterSubmodule` at the cofinite filter, under the Huber-theoretic name.
* `restrictedMvPowerSeriesSubringVal`: the inclusion `A⟨T₁, …, Tₖ⟩ → MvPowerSeries (Fin k) A` as
  an `A`-algebra map. `A⟨T⟩` is a `Subring` carrying an `Algebra A` instance rather than a
  `Subalgebra`, so `Subalgebra.val` does not apply.
* `isRestricted_of_hasFiniteSupport`: the introduction rule at module coefficients — finitely many
  nonzero coefficients suffice.
* `isRestricted_pi_iff`: restrictedness of a series with coefficients in a product is
  componentwise.
* `restrictedMvPowerSeriesSubringLinearEquiv`: at `M = A` the subring and the submodule of
  restricted series are `A`-linearly isomorphic.
* `restrictedMvPowerSeriesSubmoduleMap`: `M ↦ M⟨T₁, …, Tₖ⟩` is functorial in zero-continuous
  `A`-linear maps, with `IsRestricted.map` at the predicate level and the two functor laws.
* `restrictedMvPowerSeriesSubmoduleMap_surjective`: that functor preserves **open** surjections
  out of a module with a countable neighbourhood basis at `0` — the lifted coefficients can then
  be chosen to still tend to `0`, which lifting them one at a time does not give. This is what
  lets Wedhorn's Remark 8.29 descend from a presentation.
* `restrictedMvPowerSeriesSubmodule_ext`: coefficientwise agreement is equality in `M⟨T₁, …, Tₖ⟩`
  — the elimination rule `MvPowerSeries.ext` cannot supply at module coefficients.
* `coeff_coe_smul_restrictedMvPowerSeriesSubring`: the scalar action on `A⟨T₁, …, Tₖ⟩` is
  coefficientwise multiplication — the subring's action is `Algebra.smul_def`, not pointwise.
* `restrictedMvPowerSeriesSubmodulePiEquiv`: that criterion as an `A`-linear equivalence,
  `(∏ i, M i)⟨T₁, …, Tₖ⟩ ≃ₗ[A] ∏ i, M i⟨T₁, …, Tₖ⟩`.

## Provenance

This module is a port of AINTLIB's `projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean`,
the roadmap's designated prior formalisation of this material. Three groups, because the port and
this PR did different things to different declarations.

**AINTLIB's in definition, statement and proof.** `restrictedMvPowerSeriesSubring`,
`restrictedMvPowerSeriesSubring.instAlgebra`, `IsRestricted.finite_coeff_notMem`, the private
helpers `finite_shift_bad_set` and `coeff_mul_mem_of_forall_mem`, and `IsRestricted.mul` — the
convolution argument this file exists for. That convolution argument is AINTLIB's; what differs
here is three call sites renamed to `isRestricted_iff_coeff`, and the choice of absorbing
neighbourhood, which now comes from Mathlib's `exists_mem_nhds_zero_mul_subset` on the left and
`TauCeti.Huber.isBounded_finite` on the right, in place of AINTLIB's inline `Aᵐᵒᵖ` transport.

**AINTLIB's in statement, with proofs rewritten here.** Five: `isRestricted_zero`,
`IsRestricted.add` and `IsRestricted.neg`, which now delegate to Mathlib's `Filter.ZeroAtFilter`
API instead of reproving convergence; and `isRestricted_one` and `isRestricted_algebraMap`, which
were near-identical `tendsto_nhds`/`mem_cofinite` arguments and are now special cases of
`isRestricted_of_hasFiniteSupport`. `IsRestricted` itself is AINTLIB's statement at weaker
coefficient binders — `[Zero]` and a topology, where the original asked for a semiring.

**Original here.** `isRestricted_monomial`, `isRestricted_of_hasFiniteSupport`,
`IsRestricted.smul`, `restrictedMvPowerSeriesSubmodule`, `mem_restrictedMvPowerSeriesSubmodule`,
`isRestricted_pi_iff`, `restrictedMvPowerSeriesSubmodulePiEquiv` and
`restrictedMvPowerSeriesSubringLinearEquiv`, each with its computation lemmas, together with
`IsRestricted.map`, `restrictedMvPowerSeriesSubmoduleMap` with its laws and
`restrictedMvPowerSeriesSubmoduleMap_surjective`, and
`coeff_coe_smul_restrictedMvPowerSeriesSubring`.

**None of those has an AINTLIB counterpart**, for three different reasons.

`restrictedMvPowerSeriesSubmoduleMap_surjective` has none for the same reason as the rest of the
induced-map material: AINTLIB states restricted series over a coefficient *ring* only, so it has no
induced map at module coefficients and a fortiori no surjectivity statement about one. Wedhorn
Remark 8.29 is credited for the mathematics; the lifting construction it delegates to
(`TauCeti.exists_lift_tendsto_cofinite_nhds`) is original here too.

The two product statements — `isRestricted_pi_iff` and `restrictedMvPowerSeriesSubmodulePiEquiv` —
have none because the source states restrictedness only for a single coefficient module and never
for a product, so neither the criterion nor the equivalence packaging it appears there. Of those
two, `isRestricted_pi_iff`'s content is Mathlib's `tendsto_pi_nhds`, so what is original in it is
the statement rather than the argument, while the equivalence is original in both.

`IsRestricted.map`, `restrictedMvPowerSeriesSubmoduleMap` and its laws have none because the
source states restricted series only over a coefficient *ring*: there is no module argument there
to be functorial in, so no map to credit. The general filter content of `IsRestricted.map` is
`Filter.ZeroAtFilter.comp`, which this repo supplies.

`restrictedMvPowerSeriesSubringLinearEquiv` has none because the source never introduces the
submodule at all, so the subring is the only object it has to identify. The same holds of
`coeff_coe_smul_restrictedMvPowerSeriesSubring`, which computes an action the source never
states.

The name `isRestricted_iff` needs care: the port introduced it for the `coeff`-form unfolding
lemma, which is now `isRestricted_iff_coeff`. The statement the name carries here — unfolding
through `Filter.ZeroAtFilter` at coefficients asking only for a `0` and a topology — is new.

That originality claim was checked against **both** AINTLIB sources the roadmap designates for
this material, not only `RestrictedPowerSeries.lean`. AINTLIB's `TateAlgebra.lean`,
`TateAlgebraTopology.lean` and `TateAlgebraWedhorn.lean` build `TateAlgebra A` for a *ring* `A`
(`[CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]`) throughout; their `Submodule`
occurrences are ideals of that ring viewed as submodules, not coefficients in a module. There is
no `M⟨X⟩` there, and §0.5's "restricted series with coefficients in a complete topological module"
has no AINTLIB counterpart to credit.

The port additionally moves the declarations into the `TauCeti.Huber` namespace, opts into the
Lean module system with the definition bodies unexposed — hence the added `isRestricted_iff_coeff`,
`mem_restrictedMvPowerSeriesSubring` and `coe_algebraMap_restrictedMvPowerSeriesSubring` — tracks
the Mathlib rename of `Set.mem_setOf_eq` to
`Set.mem_ofPred_eq`, renames the predicate from AINTLIB's `IsRestrictedAdic` (nothing here is
adic), and drops hypotheses that the individual proofs never used.

This is *not* Mathlib's `MvPowerSeries.IsRestricted`, which is stated over a normed ring and
relative to a polyradius `c : σ → ℝ`, asking that `‖coeff t f‖ * ∏ i, c i ^ t i` tend to `0` along
the cofinite filter. The two conditions agree over a normed ring at `c = 1`, but neither is more
general: Mathlib's varies the radius, while `IsRestricted` here needs no norm — indeed no
multiplication, asking the coefficients for nothing beyond a `0` and a topology. It is the
norm-free form that Huber theory requires: Huber ring topologies are defined using an ideal of
definition and need not be induced by a norm. The nonarchimedean hypothesis enters only for
closure under multiplication, and hence for the subring but not for the submodule.

## Implementation notes

The restricted power series ring is defined as a subring of `MvPowerSeries (Fin k) A`
(the formal power series ring), cut out by the condition that coefficients tend to `0`.
This is the canonical concrete definition. `M⟨T₁, …, Tₖ⟩` is cut out of
`MvPowerSeries (Fin k) M` by the same condition, as an `A`-submodule.

**`IsRestricted` is Mathlib's `Filter.ZeroAtFilter` at the cofinite filter**, applied to the
coefficient function — see `isRestricted_iff`, which is `Iff.rfl`. The closure
lemmas delegate to `zero_zeroAtFilter` and `ZeroAtFilter.add`/`.neg`/`.smul`, and
`restrictedMvPowerSeriesSubmodule` *is* `Filter.zeroAtFilterSubmodule` at that filter rather than
a reconstruction of it. The Huber-specific names are kept because `M⟨T₁, …, Tₖ⟩` is the object the
roadmap names, but no closure property is proved here that Mathlib already has.

`isRestricted_iff` unfolds the predicate through `Filter.ZeroAtFilter`, which is the form the
delegations use and what module coefficients admit; `isRestricted_iff_coeff` unfolds it through
`MvPowerSeries.coeff`, the accessor to prefer wherever the coefficients form a semiring. The two
agree definitionally, because `coeff` is projection.

`isRestricted_of_hasFiniteSupport` delegates separately, through `tendsto_cofinite_pure_iff`, and
`isRestricted_one` and `isRestricted_algebraMap` are its special cases at `1` and at a constant.

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

/-- An element `f` of the multivariate power series ring `M⦃X₁, …, Xₖ⦄` is **restricted**
if its coefficients converge to `0` along the cofinite filter on multi-indices. That is,
for every open neighborhood `U` of `0` in `M`, all but finitely many coefficients of `f`
lie in `U`. This is the defining property of elements of `M⟨T₁, …, Tₖ⟩`, and of
`A⟨T₁, …, Tₖ⟩` in the case of ring coefficients.

The coefficients need carry no algebraic structure beyond a distinguished `0`: the condition is
about a family of points converging in `M`. Stronger binders appear below wherever the *statement*
names an operation, because that is where Mathlib's `MvPowerSeries` instances put the floor —
`f + g` needs `[AddMonoid M]` and `c • f` needs `[Module R M]` for the expression to be
well-formed at all, not because the convergence argument needs them. The module coefficients used
for `M⟨X⟩` are not a semiring, which is why the predicate itself must not ask for one.

See Wedhorn, (5.6.1) and §6.7. -/
def IsRestricted {k : ℕ} {M : Type*} [Zero M] [TopologicalSpace M]
    (f : MvPowerSeries (Fin k) M) : Prop :=
  Tendsto (fun s : Fin k →₀ ℕ => (f : (Fin k →₀ ℕ) → M) s) cofinite (nhds 0)

/-- **`IsRestricted` is `Filter.ZeroAtFilter` at the cofinite filter**, on the coefficient
function. Mathlib's predicate is the general notion — a function tending to `0` along a filter —
and restrictedness is its instance at `cofinite`. The body is not exposed, so this is how a
consumer at module coefficients recovers the defining condition. -/
theorem isRestricted_iff {k : ℕ} {M : Type*} [Zero M] [TopologicalSpace M]
    {f : MvPowerSeries (Fin k) M} :
    IsRestricted f ↔ Filter.ZeroAtFilter cofinite (f : (Fin k →₀ ℕ) → M) := (Iff.rfl)

/-- Unfolding lemma for `TauCeti.Huber.IsRestricted` over a semiring, through
`MvPowerSeries.coeff`. The body is not exposed, so this is how consumers recover the defining
convergence condition where the coefficients form a semiring. -/
theorem isRestricted_iff_coeff {k : ℕ} {A : Type*} [Semiring A] [TopologicalSpace A]
    {f : MvPowerSeries (Fin k) A} :
    IsRestricted f ↔
      Tendsto (fun s : Fin k →₀ ℕ => MvPowerSeries.coeff s f) cofinite (nhds 0) := (Iff.rfl)

/-- A series with coefficients in a product is restricted exactly when each of its components
is. No finiteness of `ι` is needed: the product topology is the topology of pointwise convergence,
so the criterion holds for an arbitrary product.

The two sides are **equivalent, not identical** — unlike `isRestricted_iff_coeff` and
`mem_restrictedMvPowerSeriesSubmodule`, whose `(Iff.rfl)` proofs mark a genuine defeq, this one
is not a definitional unfolding.

Deliberately **not** `@[simp]`: the right-hand side is a componentwise form that no other lemma in
this file can act on, so tagging it would rewrite `IsRestricted` goals at product coefficients into
a dead end for anything beyond the lemmas that already close them. -/
theorem isRestricted_pi_iff {k : ℕ} {ι : Type*} {M : ι → Type*} [∀ i, Zero (M i)]
    [∀ i, TopologicalSpace (M i)] {f : MvPowerSeries (Fin k) (∀ i, M i)} :
    IsRestricted f ↔ ∀ i, IsRestricted
      (show MvPowerSeries (Fin k) (M i) from fun s ↦ (f : (Fin k →₀ ℕ) → ∀ i, M i) s i) :=
  -- The content is Mathlib's `tendsto_pi_nhds`, which rests on `nhds_pi` — a proved lemma, not
  -- `rfl`, which is why the equivalence above is not a definitional one. It typechecks against
  -- this statement through three defeqs, none of them unfolded by a rewrite: `IsRestricted`'s
  -- unexposed body is the `Tendsto … cofinite (nhds 0)` of `isRestricted_iff_coeff`;
  -- `MvPowerSeries (Fin k) M` is `(Fin k →₀ ℕ) → M`, which is why the `show` ascription above is
  -- needed to state the component series at all; and the `0` of the product is the pointwise `0`,
  -- so `nhds 0` on either side is the same filter.
  tendsto_pi_nhds

/-- `0` is restricted: its coefficients are constantly `0`. -/
@[simp]
theorem isRestricted_zero (k : ℕ) (M : Type*) [Zero M] [TopologicalSpace M] :
    IsRestricted (0 : MvPowerSeries (Fin k) M) :=
  -- `(0 : MvPowerSeries (Fin k) M)` *is* the `Pi` zero: the instance is `inferInstanceAs`, so no
  -- coercion step is needed and none is available — Mathlib states no such lemma at `[Zero M]`.
  zero_zeroAtFilter _

/-- **A series with finite support is restricted.**

A sufficient condition, and the convenient introduction rule at module coefficients, where the
closure lemmas only combine existing members. `isRestricted_monomial` is its case at a single
index, and `isRestricted_one` and `isRestricted_algebraMap` follow from that. -/
theorem isRestricted_of_hasFiniteSupport {k : ℕ} {M : Type*} [Zero M] [TopologicalSpace M]
    {f : MvPowerSeries (Fin k) M}
    (hf : Function.HasFiniteSupport (f : (Fin k →₀ ℕ) → M)) : IsRestricted f :=
  (tendsto_cofinite_pure_iff.mpr hf).mono_right (pure_le_nhds 0)

/-- **A monomial is restricted**: its support is contained in `{n}`, and is empty when `a = 0`.

The constant series are the case `n = 0`: `isRestricted_one` and `isRestricted_algebraMap` follow
from `monomial 0 1` and `monomial 0 a`. Unlike `isRestricted_algebraMap` this needs no
commutativity, so it also covers `C a` over a noncommutative semiring. -/
@[simp]
theorem isRestricted_monomial {k : ℕ} {A : Type*} [Semiring A] [TopologicalSpace A]
    (n : Fin k →₀ ℕ) (a : A) : IsRestricted (MvPowerSeries.monomial n a) :=
  isRestricted_of_hasFiniteSupport <| (Set.finite_singleton n).subset fun s hs ↦ by
    have h : MvPowerSeries.coeff s (MvPowerSeries.monomial n a) ≠ 0 := by
      rwa [MvPowerSeries.coeff_apply]
    exact Set.mem_singleton_iff.mpr (MvPowerSeries.eq_of_coeff_monomial_ne_zero h)

/-- `1` is restricted: every coefficient but the `0`-th vanishes. -/
@[simp]
theorem isRestricted_one (k : ℕ) (A : Type*) [Semiring A] [TopologicalSpace A] :
    IsRestricted (1 : MvPowerSeries (Fin k) A) := by
  simpa using isRestricted_monomial (0 : Fin k →₀ ℕ) (1 : A)

/-- A sum of restricted series is restricted. -/
theorem IsRestricted.add {k : ℕ} {M : Type*} [AddMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] {f g : MvPowerSeries (Fin k) M}
    (hf : IsRestricted f) (hg : IsRestricted g) : IsRestricted (f + g) :=
  -- `(f + g)`'s coefficient function is the pointwise sum by definition: `MvPowerSeries`'
  -- `AddMonoid` instance is `inferInstanceAs` of the `Pi` one, so this is `rfl` and not a step.
  (isRestricted_iff.mp hf).add (isRestricted_iff.mp hg)

/-- The negation of a restricted series is restricted. -/
theorem IsRestricted.neg {k : ℕ} {M : Type*} [AddGroup M] [TopologicalSpace M]
    [ContinuousNeg M] {f : MvPowerSeries (Fin k) M}
    (hf : IsRestricted f) : IsRestricted (-f) :=
  -- As in `IsRestricted.add`: the `AddGroup` instance is the `Pi` one, so negation is pointwise
  -- by definition.
  (isRestricted_iff.mp hf).neg

/-- Scaling a restricted series by a constant leaves it restricted.

`R` need not be the coefficients' own ring: any semiring acting on `M` will do, and what the
scaling asks beyond that module structure is continuity of each `c • ·` in the vector variable,
which is `ContinuousConstSMul`. Stated so that consumers holding `IsRestricted` can use it
directly, as they can `IsRestricted.add` and `IsRestricted.neg`. -/
theorem IsRestricted.smul {k : ℕ} {R M : Type*} [Semiring R] [AddCommMonoid M]
    [TopologicalSpace M] [Module R M] [ContinuousConstSMul R M] {f : MvPowerSeries (Fin k) M}
    (hf : IsRestricted f) (c : R) : IsRestricted (c • f) :=
  -- As in `IsRestricted.add`: the `Module` instance is the `Pi` one, so the scalar action is
  -- pointwise by definition.
  (isRestricted_iff.mp hf).smul c

/-- A zero-preserving map that is continuous **at `0`** pushes restricted series forward: `φ ∘ f`
is restricted whenever `f` is. Restrictedness is convergence of the coefficients to `0` along
`cofinite`, so only the behaviour of `φ` at `0` is involved; global continuity is not needed.

`restrictedMvPowerSeriesSubmoduleMap` takes the same hypothesis, and not the stronger one, because
they do **not** coincide here: continuity at `0` upgrades to global continuity for a linear map
only when the topology is translation-invariant, and these modules carry `ContinuousAdd` rather
than `IsTopologicalAddGroup`. A caller holding `Continuous φ` passes `hφ.continuousAt`.

The `show` fixes the elaboration of the coefficient function as a `MvPowerSeries`: that type is a
plain `def` for `(Fin k →₀ ℕ) → N`, so without the ascription the lambda elaborates at the bare
function type and `IsRestricted` does not apply to it. -/
theorem IsRestricted.map {k : ℕ} {M N : Type*} [Zero M] [TopologicalSpace M] [Zero N]
    [TopologicalSpace N] {φ : M → N} (hφ : ContinuousAt φ 0) (h0 : φ 0 = 0)
    {f : MvPowerSeries (Fin k) M} (hf : IsRestricted f) :
    IsRestricted (show MvPowerSeries (Fin k) N from fun s ↦ φ ((f : (Fin k →₀ ℕ) → M) s)) :=
  isRestricted_iff.mpr (Filter.ZeroAtFilter.comp (isRestricted_iff.mp hf) hφ h0)

/-- Restrictedness, restated: for every open additive subgroup `W`, all but finitely many
coefficients lie in `W`. This is the form the convolution argument actually consumes. -/
theorem IsRestricted.finite_coeff_notMem {k : ℕ} {A : Type*} [Ring A]
    [TopologicalSpace A] {f : MvPowerSeries (Fin k) A} (hf : IsRestricted f)
    (W : OpenAddSubgroup A) : {s | MvPowerSeries.coeff s f ∉ (W : Set A)}.Finite := by
  have := (tendsto_nhds.mp (isRestricted_iff_coeff.mp hf)) _ W.isOpen
    (SetLike.mem_coe.mpr W.zero_mem)
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
  rw [isRestricted_iff_coeff]
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U (hU.mem_nhds h0U)
  obtain ⟨W, hWV⟩ := NonarchimedeanRing.mul_subset V
  set Sf := {s | MvPowerSeries.coeff s f ∉ (W : Set A)}
  set Sg := {s | MvPowerSeries.coeff s g ∉ (W : Set A)}
  have hSf : Sf.Finite := hf.finite_coeff_notMem W
  have hSg : Sg.Finite := hg.finite_coeff_notMem W
  -- One neighbourhood of `0` absorbing the finitely many large coefficients of both factors:
  -- `f`'s on the left, from Mathlib, and `g`'s on the right, from `isBounded_finite`.
  have hVnhds : (V : Set A) ∈ nhds (0 : A) := V.isOpen.mem_nhds V.zero_mem
  obtain ⟨T₁, hT₁mem, hT₁⟩ := exists_mem_nhds_zero_mul_subset
    (hSf.image fun a => MvPowerSeries.coeff a f).isCompact hVnhds
  have hBg := isBounded_finite (hSg.image fun b => MvPowerSeries.coeff b g)
  obtain ⟨T₂, hT₂mem, hT₂⟩ := isBounded_iff.mp hBg _ hVnhds
  set T := T₁ ∩ T₂
  have hT_nhds : T ∈ nhds (0 : A) := Filter.inter_mem hT₁mem hT₂mem
  have hgT : {s | MvPowerSeries.coeff s g ∉ T}.Finite :=
    (Filter.mem_cofinite.mp (isRestricted_iff_coeff.mp hg hT_nhds)).subset (fun s hs => hs)
  have hfT : {s | MvPowerSeries.coeff s f ∉ T}.Finite :=
    (Filter.mem_cofinite.mp (isRestricted_iff_coeff.mp hf hT_nhds)).subset (fun s hs => hs)
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
    (fun a ha y hy => hT₁ (Set.mul_mem_mul (Set.mem_image_of_mem _ ha) hy.1))
    (fun b hb x hx => hT₂ (Set.mul_mem_mul hx.2 (Set.mem_image_of_mem _ hb)))
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
  rw [MvPowerSeries.algebraMap_apply, ← MvPowerSeries.monomial_zero_eq_C_apply]
  exact isRestricted_monomial 0 a

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

/-- The inclusion `A⟨T₁, …, Tₖ⟩ → MvPowerSeries (Fin k) A` as an `A`-algebra map. `A⟨T⟩` is a
`Subring` carrying an `Algebra A` instance rather than a `Subalgebra`, so `Subalgebra.val` does
not apply. -/
noncomputable def restrictedMvPowerSeriesSubringVal {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] :
    restrictedMvPowerSeriesSubring k A →ₐ[A] MvPowerSeries (Fin k) A :=
  { (restrictedMvPowerSeriesSubring k A).subtype with
    commutes' := fun a ↦ by simp [coe_algebraMap_restrictedMvPowerSeriesSubring] }

/-- `restrictedMvPowerSeriesSubringVal` is the underlying series. Its body is not exposed, so this
is how a consumer computes with it. -/
@[simp]
theorem restrictedMvPowerSeriesSubringVal_apply {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (f : restrictedMvPowerSeriesSubring k A) :
    restrictedMvPowerSeriesSubringVal f = (f : MvPowerSeries (Fin k) A) := (rfl)

/-! ### Module coefficients -/

/-- `M⟨T₁, …, Tₖ⟩`: the restricted power series with coefficients in a topological `A`-module `M`,
as an `A`-submodule of `M⦃T₁, …, Tₖ⦄`.

This is the module-coefficient counterpart of `restrictedMvPowerSeriesSubring`, and it is what
Wedhorn's Remark 8.29 compares with `M ⊗[A] A⟨T₁, …, Tₖ⟩`. No multiplication is involved, so `M`
needs no ring structure and the nonarchimedean hypothesis that `restrictedMvPowerSeriesSubring`
carries is absent here: closure under the scalar action follows from continuity of each
`a • ·` alone. -/
def restrictedMvPowerSeriesSubmodule (k : ℕ) (A M : Type*) [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] :
    Submodule A (MvPowerSeries (Fin k) M) :=
  Filter.zeroAtFilterSubmodule A (Filter.cofinite : Filter (Fin k →₀ ℕ))

/-- Membership in `M⟨T₁, …, Tₖ⟩` is restrictedness. -/
@[simp]
theorem mem_restrictedMvPowerSeriesSubmodule {k : ℕ} {A M : Type*} [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M]
    {f : MvPowerSeries (Fin k) M} :
    f ∈ restrictedMvPowerSeriesSubmodule k A M ↔ IsRestricted f := (Iff.rfl)

/-- **Coefficientwise extensionality** for `M⟨T₁, …, Tₖ⟩`. Mathlib's `MvPowerSeries.ext` is stated
in a `Semiring` section, so it does not apply at module coefficients; without this a consumer has
to reach for `Subtype.ext (funext …)` and cross the `MvPowerSeries`-is-a-`def` gap by hand. -/
@[ext]
theorem restrictedMvPowerSeriesSubmodule_ext {k : ℕ} {A M : Type*} [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M]
    {f g : restrictedMvPowerSeriesSubmodule k A M}
    (h : ∀ s, ((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s =
      ((g : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s) : f = g :=
  Subtype.ext (funext h)

/-- **`M ↦ M⟨T₁, …, Tₖ⟩` is functorial**: an `A`-linear map continuous **at `0`** induces one on
restricted series, coefficientwise. Only continuity at `0` is used — see `IsRestricted.map`. -/
noncomputable def restrictedMvPowerSeriesSubmoduleMap {k : ℕ} {A M N : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] [AddCommMonoid N] [TopologicalSpace N] [Module A N]
    [ContinuousAdd N] [ContinuousConstSMul A N] (φ : M →ₗ[A] N) (hφ : ContinuousAt φ 0) :
    restrictedMvPowerSeriesSubmodule k A M →ₗ[A] restrictedMvPowerSeriesSubmodule k A N :=
  (φ.compLeft (Fin k →₀ ℕ)).restrict fun _ hf ↦
    mem_restrictedMvPowerSeriesSubmodule.mpr
      ((mem_restrictedMvPowerSeriesSubmodule.mp hf).map hφ (map_zero φ))

/-- `restrictedMvPowerSeriesSubmoduleMap` is `φ` coefficientwise. Its body is not exposed, so this
is how a consumer computes with it. -/
@[simp]
theorem coeff_restrictedMvPowerSeriesSubmoduleMap {k : ℕ} {A M N : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] [AddCommMonoid N] [TopologicalSpace N] [Module A N]
    [ContinuousAdd N] [ContinuousConstSMul A N] (φ : M →ₗ[A] N) (hφ : ContinuousAt φ 0)
    (f : restrictedMvPowerSeriesSubmodule k A M) (s : Fin k →₀ ℕ) :
    (((restrictedMvPowerSeriesSubmoduleMap (k := k) φ hφ f :
        restrictedMvPowerSeriesSubmodule k A N) : MvPowerSeries (Fin k) N) :
      (Fin k →₀ ℕ) → N) s = φ (((f : MvPowerSeries (Fin k) M) : (Fin k →₀ ℕ) → M) s) := (rfl)

/-- The identity induces the identity. -/
@[simp]
theorem restrictedMvPowerSeriesSubmoduleMap_id {k : ℕ} {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] :
    restrictedMvPowerSeriesSubmoduleMap (k := k) (LinearMap.id (R := A) (M := M))
      continuousAt_id = LinearMap.id :=
  LinearMap.ext fun _ ↦ restrictedMvPowerSeriesSubmodule_ext fun _ ↦ by
    simp [coeff_restrictedMvPowerSeriesSubmoduleMap]

/-- The induced maps compose. -/
@[simp]
theorem restrictedMvPowerSeriesSubmoduleMap_comp {k : ℕ} {A M N P : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] [AddCommMonoid N] [TopologicalSpace N] [Module A N]
    [ContinuousAdd N] [ContinuousConstSMul A N] [AddCommMonoid P] [TopologicalSpace P]
    [Module A P] [ContinuousAdd P] [ContinuousConstSMul A P]
    (ψ : N →ₗ[A] P) (hψ : ContinuousAt ψ 0) (φ : M →ₗ[A] N) (hφ : ContinuousAt φ 0) :
    (restrictedMvPowerSeriesSubmoduleMap ψ hψ).comp
        (restrictedMvPowerSeriesSubmoduleMap (k := k) φ hφ) =
      restrictedMvPowerSeriesSubmoduleMap (ψ.comp φ) (hψ.comp_of_eq hφ (map_zero φ)) :=
  LinearMap.ext fun _ ↦ restrictedMvPowerSeriesSubmodule_ext fun _ ↦ by
    simp [coeff_restrictedMvPowerSeriesSubmoduleMap]

/-- **A strict surjection stays surjective on restricted series.** If `φ` is a surjective
`A`-linear map which is continuous at `0` and carries the neighbourhoods of `0` onto
neighbourhoods of `0`, and `M` has a countable neighbourhood basis at `0`, then every restricted
series with coefficients in `N` is the image of one with coefficients in `M`.

Countability of `𝓝 (0 : M)` is what supplies the antitone basis the lifted coefficients are drawn
from, so it is a genuine restriction on `M` and not bookkeeping.

Surjectivity coefficientwise is immediate from surjectivity of `φ`; what is not, and what openness
supplies, is that the chosen preimages can be made to *converge*. Lifting each coefficient
independently can leave the lifts spread out even though the original coefficients tend to `0`, in
which case the lift is a power series but not a restricted one. See
`TauCeti.exists_lift_tendsto_cofinite_nhds`, where the choice is made.

This is the step Wedhorn's Remark 8.29 needs in order to descend from a presentation: applied to a
presentation `Aᵐ ↠ M`, together with the finite free case, it is what makes the comparison map for
a finitely generated `M` surjective.

The hypothesis is the filter inequality the proof actually consumes rather than `IsOpenMap φ`,
which is strictly stronger here: these modules carry `ContinuousAdd` rather than
`IsTopologicalAddGroup`, so without translation invariance global openness does not follow from
openness at `0`. A caller holding `IsOpenMap φ` — over a Tate ring, from
`TauCeti.Huber.IsTateRing.isOpenMap` — passes `map_zero φ ▸ hopen.nhds_le 0`. -/
theorem restrictedMvPowerSeriesSubmoduleMap_surjective {k : ℕ} {A M N : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] [(nhds (0 : M)).IsCountablyGenerated]
    [AddCommMonoid N] [TopologicalSpace N] [Module A N] [ContinuousAdd N]
    [ContinuousConstSMul A N] (φ : M →ₗ[A] N) (hφ : ContinuousAt φ 0)
    (hsurj : Function.Surjective φ)
    (hopen : nhds (0 : N) ≤ Filter.map φ (nhds (0 : M))) :
    Function.Surjective (restrictedMvPowerSeriesSubmoduleMap (k := k) φ hφ) := by
  intro g
  obtain ⟨f, hfg, hf⟩ := TauCeti.exists_lift_tendsto_cofinite_nhds φ hsurj hopen
    (fun s ↦ ((g : MvPowerSeries (Fin k) N) : (Fin k →₀ ℕ) → N) s)
    (isRestricted_iff.mp (mem_restrictedMvPowerSeriesSubmodule.mp g.2))
  -- `MvPowerSeries (Fin k) M` is a plain `def` for `(Fin k →₀ ℕ) → M`, and the lift `f` is produced
  -- at the bare function type. The `show` is what makes it elaborate as a series so that
  -- `IsRestricted` applies — the file's standing idiom, documented at `IsRestricted.map`.
  refine ⟨⟨show MvPowerSeries (Fin k) M from f,
      mem_restrictedMvPowerSeriesSubmodule.mpr (isRestricted_iff.mpr hf)⟩,
    restrictedMvPowerSeriesSubmodule_ext fun s ↦ ?_⟩
  rw [coeff_restrictedMvPowerSeriesSubmoduleMap]
  exact hfg s

/-- **`A⟨T₁, …, Tₖ⟩` as a submodule over itself**: at `M = A` the subring and the submodule cut
out the same series, so they are `A`-linearly isomorphic.

They are different structures over one carrier — `restrictedMvPowerSeriesSubring` is a `Subring`
carrying an `Algebra A` instance, `restrictedMvPowerSeriesSubmodule` is a `Submodule A` — so the
identification is not a coercion. It is what lets a statement about `M⟨T⟩` at `M = A` meet the
tensor-product API, which produces the subring. -/
noncomputable def restrictedMvPowerSeriesSubringLinearEquiv (k : ℕ) (A : Type*) [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] :
    restrictedMvPowerSeriesSubring k A ≃ₗ[A] restrictedMvPowerSeriesSubmodule k A A where
  toFun f := ⟨f.1, mem_restrictedMvPowerSeriesSubmodule.mpr
    (mem_restrictedMvPowerSeriesSubring.mp f.2)⟩
  invFun g := ⟨g.1, mem_restrictedMvPowerSeriesSubring.mpr
    (mem_restrictedMvPowerSeriesSubmodule.mp g.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  -- The subring's scalar action is `Algebra.smul_def`, the submodule's is pointwise; they agree
  -- on the underlying series but not syntactically, so this one field is not `rfl`.
  map_smul' a x := Subtype.ext <| by
    simp only [Algebra.smul_def, Subring.coe_mul, RingHom.id_apply,
      coe_algebraMap_restrictedMvPowerSeriesSubring, SetLike.val_smul]

/-- `restrictedMvPowerSeriesSubringLinearEquiv` is the identity on the underlying series. Its body
is not exposed, so this is how a consumer computes with it. -/
@[simp]
theorem coe_restrictedMvPowerSeriesSubringLinearEquiv {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (f : restrictedMvPowerSeriesSubring k A) :
    ((restrictedMvPowerSeriesSubringLinearEquiv k A f : restrictedMvPowerSeriesSubmodule k A A) :
      MvPowerSeries (Fin k) A) = (f : MvPowerSeries (Fin k) A) := (rfl)

/-- The scalar action on `A⟨T₁, …, Tₖ⟩` is coefficientwise multiplication.

The subring carries an `Algebra A` instance, so `a • f` is `algebraMap a * f` rather than a
pointwise action; this is the lemma that gets a consumer from one to the other. -/
@[simp]
theorem coeff_coe_smul_restrictedMvPowerSeriesSubring {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (a : A)
    (f : restrictedMvPowerSeriesSubring k A) (s : Fin k →₀ ℕ) :
    (((a • f : restrictedMvPowerSeriesSubring k A) : MvPowerSeries (Fin k) A) :
        (Fin k →₀ ℕ) → A) s =
      a * (((f : MvPowerSeries (Fin k) A) : (Fin k →₀ ℕ) → A) s) := by
  simp only [Algebra.smul_def, Subring.coe_mul, coe_algebraMap_restrictedMvPowerSeriesSubring,
    ← MvPowerSeries.coeff_apply]
  rw [← Algebra.smul_def, MvPowerSeries.coeff_smul]

/-- Its inverse is likewise the identity on the underlying series. -/
@[simp]
theorem coe_restrictedMvPowerSeriesSubringLinearEquiv_symm {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (g : restrictedMvPowerSeriesSubmodule k A A) :
    (((restrictedMvPowerSeriesSubringLinearEquiv k A).symm g :
      restrictedMvPowerSeriesSubring k A) : MvPowerSeries (Fin k) A) =
      (g : MvPowerSeries (Fin k) A) := (rfl)
/-- **`(∏ i, M i)⟨T₁, …, Tₖ⟩` is `∏ i, M i⟨T₁, …, Tₖ⟩`**: a restricted series valued in a product
is the tuple of its componentwise restricted series, `A`-linearly.

No finiteness of the index is needed. This is the target half of Wedhorn's Remark 8.29 in the
finite free case, where `M` is `Fin n → A`. -/
noncomputable def restrictedMvPowerSeriesSubmodulePiEquiv (k : ℕ) (A : Type*) {ι : Type*}
    (M : ι → Type*) [Semiring A] [∀ i, AddCommMonoid (M i)] [∀ i, TopologicalSpace (M i)]
    [∀ i, Module A (M i)] [∀ i, ContinuousAdd (M i)] [∀ i, ContinuousConstSMul A (M i)] :
    restrictedMvPowerSeriesSubmodule k A (∀ i, M i) ≃ₗ[A]
      ∀ i, restrictedMvPowerSeriesSubmodule k A (M i) where
  toFun f i := ⟨fun s ↦ f.1 s i, isRestricted_pi_iff.mp f.2 i⟩
  invFun g := ⟨fun s i ↦ (g i).1 s, isRestricted_pi_iff.mpr fun i ↦ (g i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `restrictedMvPowerSeriesSubmodulePiEquiv` reads off the `i`-th component. Its body is not
exposed, so this is how a consumer computes with it. -/
@[simp]
theorem restrictedMvPowerSeriesSubmodulePiEquiv_apply {k : ℕ} {A : Type*} {ι : Type*}
    {M : ι → Type*} [Semiring A] [∀ i, AddCommMonoid (M i)] [∀ i, TopologicalSpace (M i)]
    [∀ i, Module A (M i)] [∀ i, ContinuousAdd (M i)] [∀ i, ContinuousConstSMul A (M i)]
    (f : restrictedMvPowerSeriesSubmodule k A (∀ i, M i)) (i : ι) (s : Fin k →₀ ℕ) :
    ((restrictedMvPowerSeriesSubmodulePiEquiv k A M f i :
      MvPowerSeries (Fin k) (M i)) : (Fin k →₀ ℕ) → M i) s =
      ((f : MvPowerSeries (Fin k) (∀ i, M i)) : (Fin k →₀ ℕ) → ∀ i, M i) s i := (rfl)

/-- The inverse of `restrictedMvPowerSeriesSubmodulePiEquiv` assembles a tuple of restricted
series into one. -/
@[simp]
theorem restrictedMvPowerSeriesSubmodulePiEquiv_symm_apply {k : ℕ} {A : Type*} {ι : Type*}
    {M : ι → Type*} [Semiring A] [∀ i, AddCommMonoid (M i)] [∀ i, TopologicalSpace (M i)]
    [∀ i, Module A (M i)] [∀ i, ContinuousAdd (M i)] [∀ i, ContinuousConstSMul A (M i)]
    (g : ∀ i, restrictedMvPowerSeriesSubmodule k A (M i)) (s : Fin k →₀ ℕ) (i : ι) :
    ((((restrictedMvPowerSeriesSubmodulePiEquiv k A M).symm g :
        restrictedMvPowerSeriesSubmodule k A (∀ i, M i)) :
      MvPowerSeries (Fin k) (∀ i, M i)) : (Fin k →₀ ℕ) → ∀ i, M i) s i =
      ((g i : MvPowerSeries (Fin k) (M i)) : (Fin k →₀ ℕ) → M i) s := (rfl)

end TauCeti.Huber
