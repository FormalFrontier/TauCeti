/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Intertwiner.Dimension
public import TauCeti.RepresentationTheory.Compact.UnitaryModel
public import TauCeti.RepresentationTheory.Continuous.OrthogonalDecomposition
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite groups: normalized Haar, the `L²` pairing, and orthogonality

A finite group carrying the discrete topology is a compact topological group, so the whole
compact-group development applies to it. This file identifies the objects it produces with the
elementary finite-group ones: normalized Haar measure is `|G|⁻¹ • Measure.count`, the Haar integral
is the group average `|G|⁻¹ ∑ g, F g`, and the Haar average of the action operators of a
representation is the finite group average `|G|⁻¹ ∑ g, π g`, the Reynolds operator. (Mathlib's
algebraic counterpart of that operator is `Representation.averageMap`; this file does not connect
to it, only to the explicit sum.)

Everything the compact theory phrases as an `L²(G)` inner product then becomes a finite Hermitian
sum. Normalized Haar measure has full support on a discrete space and every function on a discrete
space is continuous, so a class in `Lp 𝕜 p (haarProb G)` *is* a function on `G` — the coercion is a
linear equivalence `Lp 𝕜 p (haarProb G) ≃ₗ[𝕜] (G → 𝕜)`, for any exponent — and at `p = 2` the inner
product is `|G|⁻¹ ∑ x, conj (f x) · g x`. Rewriting the compact statements along that identity turns
the two Schur orthogonality relations, and both branches — diagonal and off-diagonal — of the first
(row) character orthogonality relation, into their classical finite-group forms, and turns the
intertwiner count
`∫ g, χ_π(g⁻¹) · χ_ρ(g) ∂haarProb G = dim Hom_G(V, W)` into
`|G|⁻¹ ∑ g, χ_π(g⁻¹) · χ_ρ(g) = dim Hom_G(V, W)`, which is the shape Mathlib proves algebraically as
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`. (For a unitary `π` that Haar integral is
the `L²` inner product `⟪χ_π, χ_ρ⟫`, but no unitarity is needed for the count.) Each such
specialization carries the name of the compact statement it specializes, with the suffix `_sum`
recording that the Haar integral has become a group average.

The measure statement is proved without appealing to the Haar property of the counting measure, and
in fact without any topology: left invariance alone forces all singletons of a finite group to have
the same measure `c`, so a left-invariant probability measure is `c • Measure.count` by
`MeasureTheory.Measure.ext_of_singleton`, and evaluating both sides on `Set.univ` computes
`c = |G|⁻¹` from the total mass being `1`.

Everything downstream then follows by rewriting: `MeasureTheory.integral_fintype` turns a Bochner
integral against a measure on a finite space into the sum of its singleton weights, which the
measure computation has just identified.

## Main results

* `TauCeti.eq_smul_count_of_isMulLeftInvariant`: **a left-invariant probability measure on a finite
  group is the normalized counting measure** `|G|⁻¹ • Measure.count`. Since normalized Haar measure
  is one, `TauCeti.haarProb_eq_smul_count` is the special case that identifies it, and it also says
  that no other Haar probability measure exists; `TauCeti.haarProb_singleton` and
  `TauCeti.haarProb_apply` read off the measure of a singleton and of an arbitrary set.
* `TauCeti.haarProb_eq_uniformOn_univ`: it is Mathlib's uniform probability measure
  `ProbabilityTheory.uniformOn Set.univ`.
* `TauCeti.integral_haarProb`: **the Haar integral is the group average** `|G|⁻¹ • ∑ g, F g`, with
  `TauCeti.integral_haarProb_eq_inv_mul_sum` its `𝕜`-scalar form; `TauCeti.haarAverage_eq_smul_sum`
  says the same for the bundled averaging operator.
* `ContRepresentation.haarAverageMap_eq_smul_sum`: the Haar average of the action operators is the
  finite average `|G|⁻¹ • ∑ g, π g v`.
* `TauCeti.ae_haarProb_eq_top`: **normalized Haar measure on a finite discrete group has full
  support**, so its almost-everywhere filter is `⊤` and, by `TauCeti.eq_of_ae_eq_haarProb`, two
  functions agreeing almost everywhere agree everywhere. This is what makes an `L²` class on a
  finite group a genuine function; `TauCeti.coeFn_toLp_haarProb` is the case of it used throughout,
  that the class of a continuous function is that function.
* `TauCeti.lpHaarProbEquivFun`: **`L²(G)` is `G → 𝕜`**, by the linear equivalence taking an `Lp`
  class to its values; the previous item is its injectivity and finiteness is its surjectivity.
  Nothing in it depends on the exponent, so it is stated for every `p`.
* `TauCeti.inner_Lp_haarProb_eq_inv_mul_sum`: **the `L²(G)` inner product is the normalized
  Hermitian pairing** `|G|⁻¹ ∑ x, conj (f x) · g x` of those values, with
  `TauCeti.inner_toLp_haarProb_eq_inv_mul_sum` the form for two continuous functions.
* `ContRepresentation.schur_orthogonality_self_sum`,
  `ContRepresentation.schur_orthogonality_distinct_sum` and
  `ContRepresentation.schur_orthogonality_sum`: **the two Schur orthogonality relations as finite
  averages** of matrix coefficients, the middle one at the vanishing-intertwiner hypothesis of the
  compact theory and the last at a pair of inequivalent irreducibles, with
  `ContRepresentation.schur_orthogonality_basis_sum` the Kronecker-delta form of the first in an
  orthonormal basis.
* `ContRepresentation.character_orthonormal_distinct_sum`: **the off-diagonal branch of the first
  (row) character orthogonality relation as a finite average**. (The column sum over the irreducible
  characters, the second orthogonality relation, is not treated here.)
* `ContRepresentation.inner_gramOperator_eq_inv_mul_sum`: **the invariant form the unitarian trick
  averages into existence is the finite average** `|G|⁻¹ ∑ g, ⟪π g v, π g w⟫`, with
  `ContRepresentation.gramOperator_eq_smul_sum` the same identity at the level of the operator
  representing it and `ContRepresentation.inner_gramOperator_self_eq_inv_mul_sum` its diagonal.
* `ContRepresentation.exists_isUnitary_congr_of_finite`: **the unitarian trick for a finite group**,
  every finite-dimensional representation being conjugate to a unitary one.
* `ContRepresentation.exists_orthogonal_irreducible_decomposition_of_finite`: **Maschke's theorem in
  orthogonal form**, the finite shadow of complete reducibility: `π` itself is an internal direct
  sum of irreducible subrepresentations, orthogonal for the averaged inner product.

The counting identity `|G|⁻¹ ∑ g, χ_π g = dim V^G` that the compact-group character integral
generalizes then costs one rewrite. It is not given a name: Mathlib already proves it, as
`Representation.card_inv_mul_sum_char_eq_finrank`, and that lemma closes the `ContRepresentation`
statement outright, so only the route through the compact theory is new. The intertwiner count
`|G|⁻¹ ∑ g, χ_π(g⁻¹) · χ_ρ(g) = dim Hom_G(V, W)` is unnamed for the same reason: Mathlib proves it
as `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`, for the algebraic intertwiner space
`Representation.IntertwiningMap`, which in finite dimensions is the continuous one because every
linear map out of a finite-dimensional normed space is continuous. Both routes are exhibited by
anonymous `example`s, as are both branches of Mathlib's `Representation.char_orthonormal`: the
diagonal one is `TauCeti.ContRepresentation.character_orthonormal_self` read through the finite
pairing — Mathlib and `TauCeti.ClassFunction.characterPairing_ofCharacter_self` both already prove
that identity, so no name is claimed for it either — and the off-diagonal one is
`character_orthonormal_distinct_sum` with its intertwiner hypothesis discharged, for a pair of
inequivalent irreducibles, by the vanishing half of Schur's lemma.

## Implementation notes

Finiteness is spelled `[Finite G]` wherever that suffices — the measure-theoretic statements and the
equivalence `TauCeti.lpHaarProbEquivFun` — and `[Fintype G]` only where a sum over `Finset.univ`
appears in the statement itself, since a `Fintype` instance recovered from `Finite` inside a proof
would not be the one indexing that sum. The scalars and the exponent are weakened the same way:
`TauCeti.lpHaarProbEquivFun` needs only `[NontriviallyNormedField 𝕜]` and an arbitrary exponent —
not even `[Fact (1 ≤ p)]`, since `MeasureTheory.MemLp.of_discrete` produces the class of a function
at every exponent, whereas `ContinuousMap.toLp`, being a continuous linear map, needs a norm on
`Lp` and hence that hypothesis — and `[RCLike 𝕜]` and `p = 2` appear from the inner-product
statements on.
Cardinalities are written `Nat.card G` throughout, matching the rest of the roadmap;
`Nat.card_eq_fintype_card` converts.

`IsTopologicalGroup G`, `CompactSpace G`, `T2Space G` and `MeasurableSingletonClass G` are all
found by instance search from `[DiscreteTopology G]`, `[Finite G]` and `[BorelSpace G]`, so no
extra hypotheses are carried. Continuity of a representation is likewise automatic, by
`continuous_of_discreteTopology`, and is asked of the caller only where the *statement* needs it:
the two pairing lemmas are about the `L²` classes `matrixCoeffLp π hπ` and `characterLp π hπ`, which
take the continuity proof as an argument, so a caller of them holds one already. The orthogonality
relations ask for none: the Schur ones are stated as bare sums `∑ g, ⟪π g v, w⟫ · …`, and the
character one uses Mathlib's `Representation.character`, which is by
`TauCeti.ContRepresentation.coe_character` the function underlying `character π hπ`. Those
statements mention no measure either, so they ask for no measurable structure on `G`: their proofs
install `borel G` themselves, and the caller is left with a bare finite discrete group. The two
Maschke statements go one step further: mentioning no topology on `G` at all, they have their proof
install the discrete topology as well, and the caller is left with a bare finite group.

The scalar in the averaged sums is real, not `𝕜`: the Bochner integral being specialized is an
`ℝ`-integral, and `V` is not assumed to be an `ℝ`-`𝕜`-scalar tower. The conversion is confined to
`TauCeti.integral_haarProb_eq_inv_mul_sum`, whose integrand is `𝕜`-valued and which uses
`RCLike.real_smul_eq_coe_mul`; the character count then goes through that lemma.

## References

The compact-group theory specialized here is the one developed in the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
and each statement below is the finite case of the compact one named beside it. `haarProb G` is the
normalized counting measure `|G|⁻¹ • count`, and the counting identity
`dim V^G = |G|⁻¹ ∑ g, χ_π g` is the finite shadow of
`ContRepresentation.integral_character_eq_finrank_invariants`, matching Mathlib's
`FDRep.average_char_eq_finrank_invariants` for the purely algebraic theory. `L²(G)` is `G → 𝕜` by
`TauCeti.lpHaarProbEquivFun` and `⟪·, ·⟫_{L²(G)}` becomes the finite Hermitian pairing on it,
`schur_orthogonality_self`, `schur_orthogonality_distinct` and
`schur_orthogonality` become the classical orthogonality relations for matrix coefficients, and
`character_orthonormal_self` and `character_orthonormal_distinct` become the two branches of
Mathlib's `Representation.char_orthonormal`, exhibited by two anonymous `example`s. Finally
`exists_orthogonal_irreducible_decomposition` specializes, through the finite unitarian trick, to
`ContRepresentation.exists_orthogonal_irreducible_decomposition_of_finite`, whose blocks are
subrepresentations of the given representation, carried back along the unitarizing equivalence
`ContRepresentation.congrEquiv`. What that specialization adds to Mathlib's Maschke is the
orthogonality of the summands, which needs the inner product Mathlib's complements do not see; the
purely algebraic conclusion, that `π.toRepresentation.asModule` is a semisimple
`MonoidAlgebra 𝕜 G`-module whenever `|G|` is invertible in `𝕜`, is Mathlib's own instance and is
neither restated nor reproved here. Peter-Weyl for a finite group, that `peterWeylBasis` is the
matrix-coefficient basis of `k[G]`, is not proved here either.
-/

public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace TauCeti

section LeftInvariant

variable {G : Type*} [Group G] [Finite G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **A left-invariant probability measure on a finite group is the normalized counting measure.**

Left translation by `g` carries `{1}` to `{g}`, so left invariance forces all singletons to have
the same mass `c` and hence `μ = c • Measure.count` by `MeasureTheory.Measure.ext_of_singleton`;
evaluating both sides on `Set.univ` computes `c = |G|⁻¹` from the total mass being `1`. Neither a
topology nor the Haar property of the counting measure is needed. -/
theorem eq_smul_count_of_isMulLeftInvariant (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsProbabilityMeasure μ] : μ = (Nat.card G : ℝ≥0∞)⁻¹ • Measure.count := by
  have hone : ∀ g : G, μ {g} = μ {(1 : G)} := fun g ↦ by
    have h : (fun x ↦ g * x) ⁻¹' {g} = {(1 : G)} := by
      ext x
      simp
    rw [← measure_preimage_mul μ g {g}, h]
  have hsmul : μ = μ {(1 : G)} • Measure.count := by
    refine Measure.ext_of_singleton fun a ↦ ?_
    rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one, hone a]
  have hmass : μ {(1 : G)} * (Nat.card G : ℝ≥0∞) = 1 := by
    have h := congrArg (fun ν : Measure G ↦ ν univ) hsmul
    simpa [Measure.count_univ, ENat.card_eq_coe_natCard] using h.symm
  rw [hsmul, ENNReal.eq_inv_of_mul_eq_one_left hmass]

end LeftInvariant

section FiniteGroup

variable (G : Type*) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Normalized Haar measure on a finite discrete group is the normalized counting measure.**
Because `TauCeti.eq_smul_count_of_isMulLeftInvariant` needs only left invariance and total mass
one, this also says that no other Haar probability measure on `G` exists. -/
theorem haarProb_eq_smul_count :
    haarProb G = (Nat.card G : ℝ≥0∞)⁻¹ • Measure.count :=
  eq_smul_count_of_isMulLeftInvariant (haarProb G)

/-- **The normalized Haar measure of a singleton in a finite discrete group is `|G|⁻¹`.** -/
@[simp]
theorem haarProb_singleton (g : G) : haarProb G {g} = (Nat.card G : ℝ≥0∞)⁻¹ := by
  rw [haarProb_eq_smul_count G, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

/-- The normalized Haar measure of a set in a finite discrete group is the fraction of the group it
occupies. -/
theorem haarProb_apply (s : Set G) : haarProb G s = (s.ncard : ℝ≥0∞) / Nat.card G := by
  rw [haarProb_eq_smul_count G, Measure.smul_apply,
    Measure.count_apply_finite s s.toFinite, smul_eq_mul, ENNReal.div_eq_inv_mul,
    Set.ncard_eq_toFinset_card s s.toFinite]

/-- The real-valued normalized Haar measure of a singleton, in the form
`MeasureTheory.integral_fintype` consumes. -/
@[simp]
theorem haarProb_real_singleton (g : G) : (haarProb G).real {g} = (Nat.card G : ℝ)⁻¹ := by
  rw [measureReal_def, haarProb_singleton G g]
  simp

/-- The real-valued normalized Haar measure of a set in a finite discrete group. -/
theorem haarProb_real_apply (s : Set G) : (haarProb G).real s = s.ncard / Nat.card G := by
  rw [measureReal_def, haarProb_apply G s, ENNReal.toReal_div]
  simp

/-- Normalized Haar measure on a finite discrete group is Mathlib's uniform probability measure
`ProbabilityTheory.uniformOn Set.univ`. -/
theorem haarProb_eq_uniformOn_univ : haarProb G = ProbabilityTheory.uniformOn Set.univ := by
  obtain ⟨_⟩ := nonempty_fintype G
  refine Measure.ext_of_singleton fun a ↦ ?_
  rw [haarProb_singleton G a, ProbabilityTheory.uniformOn_univ, Measure.count_singleton,
    Nat.card_eq_fintype_card, one_div]

end FiniteGroup

section FintypeGroup

variable (G : Type*) [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **The Haar integral over a finite discrete group is the group average.** This is what makes
every averaging statement of the compact theory specialize to its finite-group counterpart. -/
theorem integral_haarProb (F : G → V) :
    ∫ g, F g ∂haarProb G = (Nat.card G : ℝ)⁻¹ • ∑ g, F g := by
  rw [integral_fintype Integrable.of_finite, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [haarProb_real_singleton G g]

/-- **The Haar integral of a `𝕜`-valued function over a finite discrete group is the group
average**, in the `𝕜`-scalar form the character theory consumes: `TauCeti.integral_haarProb` states
the same identity with the real scalar `(|G| : ℝ)⁻¹` acting on a general normed space. -/
theorem integral_haarProb_eq_inv_mul_sum {𝕜 : Type*} [RCLike 𝕜] (F : G → 𝕜) :
    ∫ g, F g ∂haarProb G = (Nat.card G : 𝕜)⁻¹ * ∑ g, F g := by
  rw [integral_haarProb G F, RCLike.real_smul_eq_coe_mul]
  simp

/-- The bundled Haar averaging operator of a finite discrete group is the group average. -/
theorem haarAverage_eq_smul_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V]
    [SMulCommClass ℝ 𝕜 V] (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = (Nat.card G : ℝ)⁻¹ • ∑ g, f g := by
  rw [haarAverage_apply, integral_haarProb]

end FintypeGroup

/-! ### The `L²` space of a finite group -/

section FullSupport

variable (G : Type*) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Normalized Haar measure on a finite discrete group has full support**, in the sharp form that
its almost-everywhere filter is the whole filter: every singleton has mass `|G|⁻¹ ≠ 0`, so the empty
set is the only null set. -/
@[simp]
theorem ae_haarProb_eq_top : ae (haarProb G) = ⊤ :=
  ae_eq_top.2 fun a ↦ by
    rw [haarProb_singleton]
    simp

/-- **Functions on a finite discrete group agreeing almost everywhere for normalized Haar measure
agree everywhere.** This is `TauCeti.ae_haarProb_eq_top` read as a statement about functions;
nothing is asked of the codomain, the fact being one about the measure alone.

In particular an element of `Lp 𝕜 p (haarProb G)`, which is only an almost-everywhere class, is
pinned down by its values: this is the sense in which `L²(G)` "is" `G → 𝕜`. -/
theorem eq_of_ae_eq_haarProb {α : Type*} {f g : G → α} (h : f =ᵐ[haarProb G] g) : f = g := by
  rw [ae_haarProb_eq_top] at h
  exact funext (Filter.eventually_top.mp h)

end FullSupport

section LpEquiv

variable (G : Type*) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞}

/-- **The `Lp` class of a continuous function on a finite discrete group is that function**, on the
nose and not merely almost everywhere, because normalized Haar measure has full support
(`TauCeti.eq_of_ae_eq_haarProb`).

This is not a `simp` lemma: `ContinuousMap.coe_toLp` already rewrites the left-hand side to
`⇑(f.toAEEqFun (haarProb G))`, so tagging it is a `simpNF` error. The value-level `simp` form of
the round trip through the equivalence below is `TauCeti.coeFn_lpHaarProbEquivFun_symm`. -/
theorem coeFn_toLp_haarProb [Fact (1 ≤ p)] (f : C(G, 𝕜)) :
    ⇑(ContinuousMap.toLp p (haarProb G) 𝕜 f) = f :=
  eq_of_ae_eq_haarProb G (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) (haarProb G) f)

variable (𝕜 p) in
/-- **`Lp` of a finite discrete group is the space of all functions on it**: taking underlying
functions is a `𝕜`-linear equivalence `Lp 𝕜 p (haarProb G) ≃ₗ[𝕜] (G → 𝕜)`.

It is injective because normalized Haar measure has full support (`TauCeti.eq_of_ae_eq_haarProb`),
so an `Lp` class is pinned down by its values, and surjective because `G` is finite and the measure
is finite: *every* function on `G` is then `p`-integrable, by `MeasureTheory.MemLp.of_discrete`, and
`MeasureTheory.MemLp.toLp` produces its class. Nothing depends on the exponent, not even `1 ≤ p`; at
`p = 2`, together with `TauCeti.inner_Lp_haarProb_eq_inv_mul_sum`, which computes the inner product
from exactly the values this equivalence reads off, it is the identification of `L²(G)` with `G → 𝕜`
carrying the normalized Hermitian pairing. -/
noncomputable def lpHaarProbEquivFun : Lp 𝕜 p (haarProb G) ≃ₗ[𝕜] (G → 𝕜) where
  toFun f := f
  map_add' f g := eq_of_ae_eq_haarProb G (Lp.coeFn_add f g)
  map_smul' c f := eq_of_ae_eq_haarProb G (Lp.coeFn_smul c f)
  invFun f := MemLp.toLp f MemLp.of_discrete
  left_inv _ := Lp.ext (MemLp.coeFn_toLp _)
  right_inv f := eq_of_ae_eq_haarProb G (MemLp.coeFn_toLp (f := f) MemLp.of_discrete)

/-- The equivalence `TauCeti.lpHaarProbEquivFun` reads off the values of an `Lp` class. -/
@[simp]
theorem lpHaarProbEquivFun_apply (f : Lp 𝕜 p (haarProb G)) (x : G) :
    lpHaarProbEquivFun G 𝕜 p f x = f x :=
  (rfl)

/-- **The inverse of `TauCeti.lpHaarProbEquivFun` has the values it was handed.** This is the
simp-normal form of the inverse: it is what makes the round trip through the equivalence reduce. -/
@[simp]
theorem coeFn_lpHaarProbEquivFun_symm (f : G → 𝕜) : ⇑((lpHaarProbEquivFun G 𝕜 p).symm f) = f :=
  eq_of_ae_eq_haarProb G (MemLp.coeFn_toLp (f := f) MemLp.of_discrete)

/-- The inverse of `TauCeti.lpHaarProbEquivFun` is `ContinuousMap.toLp`, every function on a
discrete space being continuous; this is the identification for the exponents at which that map
exists. It is not a simp lemma: `TauCeti.coeFn_lpHaarProbEquivFun_symm` is the value-level form, and
rewriting the inner term first would keep a round trip from reducing by
`LinearEquiv.apply_symm_apply`. -/
theorem lpHaarProbEquivFun_symm_apply [Fact (1 ≤ p)] (f : G → 𝕜) :
    (lpHaarProbEquivFun G 𝕜 p).symm f =
      ContinuousMap.toLp p (haarProb G) 𝕜 ⟨f, continuous_of_discreteTopology⟩ :=
  Lp.ext (.of_eq
    ((coeFn_lpHaarProbEquivFun_symm G f).trans
      (coeFn_toLp_haarProb G ⟨f, continuous_of_discreteTopology⟩).symm))

end LpEquiv

section InnerProduct

variable (G : Type*) [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {𝕜 : Type*} [RCLike 𝕜]

/-- **The `L²` inner product of a finite discrete group is the normalized Hermitian pairing**
`|G|⁻¹ ∑ x, conj (f x) * g x`.

This is the pairing carried by the identification `L²(G) = (G → 𝕜)` of
`TauCeti.lpHaarProbEquivFun`, whose underlying map is the coercion appearing on the right: the Haar
integral defining the `L²` inner product is the group average, by
`TauCeti.integral_haarProb_eq_inv_mul_sum`. The conjugation sits on the *first* argument, matching
Mathlib's convention that the inner product is conjugate-linear there. -/
theorem inner_Lp_haarProb_eq_inv_mul_sum (f g : Lp 𝕜 2 (haarProb G)) :
    ⟪f, g⟫_𝕜 = (Nat.card G : 𝕜)⁻¹ * ∑ x, (starRingEnd 𝕜) (f x) * g x := by
  rw [L2.inner_def,
    ← integral_haarProb_eq_inv_mul_sum (𝕜 := 𝕜) G fun x ↦ (starRingEnd 𝕜) (f x) * g x]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
    simp only [RCLike.inner_apply, mul_comm])

/-- The `L²` inner product of two *continuous* functions on a finite discrete group, the form in
which the matrix coefficients and the characters present themselves. -/
theorem inner_toLp_haarProb_eq_inv_mul_sum (f g : C(G, 𝕜)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 f, ContinuousMap.toLp 2 (haarProb G) 𝕜 g⟫_𝕜 =
      (Nat.card G : 𝕜)⁻¹ * ∑ x, (starRingEnd 𝕜) (f x) * g x := by
  rw [inner_Lp_haarProb_eq_inv_mul_sum]
  simp only [coeFn_toLp_haarProb]

end InnerProduct

end TauCeti

open MeasureTheory TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section Average

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

/-- **The Haar average of the action operators of a finite discrete group is the finite group
average** `|G|⁻¹ ∑ g, π g`, the Reynolds operator whose role normalized Haar measure plays in
`ContRepresentation.haarAverageMap`. Mathlib's algebraic counterpart of that operator is
`Representation.averageMap`; this lemma relates the Haar average to the explicit sum only. -/
theorem haarAverageMap_eq_smul_sum (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v : V) :
    haarAverageMap π hπ v = (Nat.card G : ℝ)⁻¹ • ∑ g, π g v := by
  rw [haarAverageMap_apply, integral_haarProb]

end Average

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Completeness of `V` is not an extra hypothesis: a finite-dimensional normed space over an
`RCLike` field is already complete. As in
`TauCeti/RepresentationTheory/Compact/Invariants.lean`, Mathlib keeps `FiniteDimensional.complete`
out of the global instance set, so it is installed here as a local instance. -/
local instance instCompleteSpaceFinite : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

/- **The finite-group counting identity** `|G|⁻¹ ∑ g, χ_π g = dim V^G`, the specialization of
`ContRepresentation.integral_character_eq_finrank_invariants` to a finite discrete group, and the
statement Mathlib proves algebraically as `Representation.card_inv_mul_sum_char_eq_finrank` (see
also `FDRep.average_char_eq_finrank_invariants`).

Mathlib's lemma, applied to `π.toRepresentation`, already closes this goal, so no name is claimed
for it here; what the compact theory contributes is the derivation below, in which the count is the
Haar integral of the character read off by `TauCeti.integral_haarProb_eq_inv_mul_sum`. -/
example (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g = (Module.finrank 𝕜 π.invariants : 𝕜) := by
  rw [← integral_character_eq_finrank_invariants π hπ, integral_haarProb_eq_inv_mul_sum]

end Trace

/-! ### Matrix coefficients and the Schur orthogonality relations -/

section MatrixCoefficient

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The `L²` pairing of two matrix coefficients of a finite group is a group average.** This is
the identity along which the Schur orthogonality relations become finite sums. -/
theorem inner_matrixCoeffLp_eq_inv_mul_sum (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜 =
      (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 * ⟪ρ g v', w'⟫_𝕜 := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, inner_toLp_haarProb_eq_inv_mul_sum]
  simp only [matrixCoeff_apply]

end MatrixCoefficient

section SchurSelf

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **The first Schur orthogonality relation for a finite group.** For a unitary irreducible
representation of dimension `d`,
`|G|⁻¹ ∑ g, conj ⟪π g v₁, w₁⟫ * ⟪π g v₂, w₂⟫ = d⁻¹ * (conj ⟪v₁, v₂⟫ * ⟪w₁, w₂⟫)`.

This is `TauCeti.ContRepresentation.schur_orthogonality_self` with the Haar integral of the
compact theory replaced by the group average; the normalization `|G|⁻¹` is exactly the one that
makes normalized Haar measure a probability measure. Neither continuity of `π` nor a measurable
structure on `G` is asked: the statement mentions no measure and no continuity proof, and the proof
installs the Borel structure it integrates against, `continuous_of_discreteTopology` supplying the
continuity. -/
theorem schur_orthogonality_self_sum (π : ContRepresentation 𝕜 G V)
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation)
    (v₁ w₁ v₂ w₂ : V) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v₁, w₁⟫_𝕜 * ⟪π g v₂, w₂⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ * ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  rw [← inner_matrixCoeffLp_eq_inv_mul_sum π continuous_of_discreteTopology π
      continuous_of_discreteTopology,
    schur_orthogonality_self π continuous_of_discreteTopology hunitary hirr]

/-- **The first Schur orthogonality relation for a finite group, in an orthonormal basis.** If
`πᵢⱼ(g) = ⟪π g eⱼ, eᵢ⟫`, then `|G|⁻¹ ∑ g, conj (πᵢⱼ g) * πₖₗ g = d⁻¹ δⱼₗ δᵢₖ`.

This is `TauCeti.ContRepresentation.schur_orthogonality_basis` with the Haar integral replaced by
the group average, and it is the form the matrix coefficients of a finite group present themselves
in: the index order and the placement of the conjugation are the ones fixed there, Kronecker deltas
being real. -/
theorem schur_orthogonality_basis_sum (π : ContRepresentation 𝕜 G V)
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation)
    {d : ℕ} (e : OrthonormalBasis (Fin d) 𝕜 V) (i j k l : Fin d) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g (e j), e i⟫_𝕜 * ⟪π g (e l), e k⟫_𝕜 =
      (d : 𝕜)⁻¹ * ((if j = l then (1 : 𝕜) else 0) * (if i = k then (1 : 𝕜) else 0)) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  rw [← inner_matrixCoeffLp_eq_inv_mul_sum π continuous_of_discreteTopology π
      continuous_of_discreteTopology,
    schur_orthogonality_basis π continuous_of_discreteTopology hunitary hirr]

end SchurSelf

section SchurDistinct

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W]

omit [FiniteDimensional 𝕜 V] in
/-- **Schur orthogonality for a finite group and a vanishing intertwiner space.** If the only
continuous intertwiner `π → ρ` is zero and `ρ` is unitary, then every matrix coefficient of `π` has
vanishing group average against every matrix coefficient of `ρ`. This is
`TauCeti.ContRepresentation.schur_orthogonality_distinct` read through the finite Hermitian
pairing; Schur's lemma is what supplies the hypothesis for a pair of inequivalent irreducibles, as
in `ContRepresentation.schur_orthogonality_sum` below. No continuity is asked of either
representation, for the reason given at `ContRepresentation.schur_orthogonality_self_sum`. -/
theorem schur_orthogonality_distinct_sum (π : ContRepresentation 𝕜 G V)
    (ρ : ContRepresentation 𝕜 G W) (hunitary : IsUnitary ρ)
    (hdistinct : ∀ f : ContIntertwiningMap π ρ, f.toContinuousLinearMap = 0)
    (v w : V) (v' w' : W) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 * ⟪ρ g v', w'⟫_𝕜 = 0 := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  rw [← inner_matrixCoeffLp_eq_inv_mul_sum π continuous_of_discreteTopology ρ
      continuous_of_discreteTopology,
    schur_orthogonality_distinct π continuous_of_discreteTopology ρ
      continuous_of_discreteTopology hunitary hdistinct]

/-- **The second Schur orthogonality relation for a finite group.** Matrix coefficients of
inequivalent irreducible representations, the second of them unitary, have vanishing group average,
this being `TauCeti.ContRepresentation.schur_orthogonality` read through the finite Hermitian
pairing. No continuity is asked of either representation, for the reason given at
`ContRepresentation.schur_orthogonality_self_sum`. -/
theorem schur_orthogonality_sum (π : ContRepresentation 𝕜 G V)
    (ρ : ContRepresentation 𝕜 G W) (hunitary : IsUnitary ρ)
    (hirrπ : Representation.IsIrreducible π.toRepresentation)
    (hirrρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) (v w : V) (v' w' : W) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 * ⟪ρ g v', w'⟫_𝕜 = 0 := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  rw [← inner_matrixCoeffLp_eq_inv_mul_sum π continuous_of_discreteTopology ρ
      continuous_of_discreteTopology,
    schur_orthogonality π continuous_of_discreteTopology ρ continuous_of_discreteTopology
      hunitary hirrπ hirrρ hne]

end SchurDistinct

/-! ### Characters -/

section Character

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ hρ

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **The `L²` pairing of two characters of a finite group is a group average.** -/
theorem inner_characterLp_eq_inv_mul_sum :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 =
      (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) (character π hπ g) * character ρ hρ g := by
  rw [characterLp_def, characterLp_def, inner_toLp_haarProb_eq_inv_mul_sum]

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] in
/- **The finite character sum counts the intertwiners**:
`|G|⁻¹ ∑ g, χ_π(g⁻¹) · χ_ρ(g) = dim Hom_G(V, W)`, the specialization of
`ContRepresentation.integral_character_mul_eq_finrank_contIntertwiningMap` to a finite discrete
group. No unitarity is needed: the inverse in the first factor is what the compact statement
carries, and only for a unitary representation does it become a complex conjugate.

No name is claimed, for the same reason as in the counting identity above: Mathlib proves this
identity as `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`, stated for the algebraic
intertwiner space `Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation`, which in
finite dimensions is the continuous one. What the compact theory contributes is the derivation
below, in which the count is the Haar integral read off by
`TauCeti.integral_haarProb_eq_inv_mul_sum`. -/
example :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g⁻¹ * character ρ hρ g
      = (Module.finrank 𝕜 (ContIntertwiningMap π ρ) : 𝕜) := by
  rw [← integral_character_mul_eq_finrank_contIntertwiningMap π ρ hπ hρ,
    integral_haarProb_eq_inv_mul_sum]

end Character

section CharacterOrthogonality

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V)

omit [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **The off-diagonal branch of first (row) character orthogonality for a finite group**: for a
*unitary* `π`, the group average of `conj χ_π · χ_ρ` vanishes when no nonzero continuous intertwiner
`ρ → π` exists, which for a pair of irreducibles is Schur's lemma. Unitarity is asked of `π` alone,
as in the compact source `TauCeti.ContRepresentation.character_orthonormal_distinct`. (The second
orthogonality relation, the column sum over the irreducible characters, is a different statement and
is not proved here.)

The characters are written as Mathlib's `Representation.character` of the underlying
representations, which is by `TauCeti.ContRepresentation.coe_character` the function underlying
`character π hπ`; so no continuity proof is asked of the caller, and no measurable structure on `G`
either, the statement mentioning neither. -/
theorem character_orthonormal_distinct_sum (ρ : ContRepresentation 𝕜 G W)
    (hunitary : IsUnitary π)
    (hdistinct : ∀ f : ContIntertwiningMap ρ π, f.toContinuousLinearMap = 0) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) (π.toRepresentation.character g) *
        ρ.toRepresentation.character g = 0 := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  rw [← coe_character π continuous_of_discreteTopology,
    ← coe_character ρ continuous_of_discreteTopology,
    ← inner_characterLp_eq_inv_mul_sum π continuous_of_discreteTopology ρ
      continuous_of_discreteTopology,
    character_orthonormal_distinct π continuous_of_discreteTopology ρ
      continuous_of_discreteTopology hunitary hdistinct]

variable (hπ : Continuous π)

include hπ

/- **The diagonal branch of first (row) character orthogonality for a finite group**, which is the
diagonal half of Mathlib's `Representation.char_orthonormal`, in its `χ_π(g) · χ_π(g⁻¹)` spelling,
obtained through the compact theory:
`TauCeti.ContRepresentation.character_orthonormal_self` says the character of an irreducible
unitary representation is an `L²` unit vector, `inner_characterLp_eq_inv_mul_sum` turns that pairing
into a group average, and unitarity turns the inverse into a conjugate by
`TauCeti.ContRepresentation.character_apply_inv`.

No name is claimed, for the same reason as in the two counting identities above: the identity is
already Mathlib's `Representation.char_orthonormal` (its diagonal branch) at `π.toRepresentation`,
and `TauCeti.ClassFunction.characterPairing_ofCharacter_self` proves it again for the character
pairing — both without unitarity, which is needed only to pass between the two spellings. What is
exhibited is that the compact-group normalization agrees with the finite-group one. -/
example [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g * character π hπ g⁻¹ = 1 := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  rw [← character_orthonormal_self π hπ hunitary hirr, inner_characterLp_eq_inv_mul_sum π hπ π hπ]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦ by
    rw [character_apply_inv π hπ hunitary, mul_comm])

/- **The off-diagonal half of Mathlib's `Representation.char_orthonormal`**, in the same spelling:
the characters of two inequivalent irreducibles have vanishing group average. This is
`character_orthonormal_distinct_sum` at the transposed pair `(ρ, π)`, whose intertwiner hypothesis
is discharged by the vanishing half of Schur's lemma,
`TauCeti.ContRepresentation.eq_zero_of_isEmpty_equiv`, exactly as `orthonormal_characterLp`
discharges it in the compact theory. So the substantive vanishing statement is reached, not
assumed: `character_orthonormal_distinct_sum` keeps the hypothesis of the compact theorem
`character_orthonormal_distinct` it specializes, and irreducibility enters here.

No name is claimed, for the same reason as above and in the two counting identities: with both
representations irreducible and inequivalent this is Mathlib's `Representation.char_orthonormal`
(its `IsEmpty (Equiv ρ π)` branch) at `π.toRepresentation` and `ρ.toRepresentation`. What the
compact theory contributes is the derivation. -/
example (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (hunitary : IsUnitary ρ)
    (hirrπ : Representation.IsIrreducible π.toRepresentation)
    (hirrρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g * character ρ hρ g⁻¹ = 0 := by
  rw [← character_orthonormal_distinct_sum ρ π hunitary
      fun f ↦ by simp [eq_zero_of_isEmpty_equiv hirrπ hirrρ hne f],
    ← coe_character ρ hρ, ← coe_character π hπ]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦ by
    rw [character_apply_inv ρ hρ hunitary, mul_comm])

end CharacterOrthogonality

/-! ### The unitarian trick and Maschke -/

section Unitarization

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- **The averaged invariant form of a finite group is the group average**
`⟪v, w⟫_G = |G|⁻¹ ∑ g, ⟪π g v, π g w⟫`. This is the form Weyl's unitarian trick averages into
existence, read off the Gram operator that represents it
(`TauCeti.ContRepresentation.inner_gramOperator`) through
`TauCeti.integral_haarProb_eq_inv_mul_sum`; for a finite group it is the classical averaging
`⟪·, ·⟫ ↦ |G|⁻¹ ∑ g, ⟪π g ·, π g ·⟫` of the finite-group proof, and the normalization `|G|⁻¹` is
the one that fixes the form on the invariants. -/
theorem inner_gramOperator_eq_inv_mul_sum (v w : V) :
    ⟪v, gramOperator π hπ w⟫_𝕜 = (Nat.card G : 𝕜)⁻¹ * ∑ g, ⟪π g v, π g w⟫_𝕜 := by
  rw [inner_gramOperator, integral_haarProb_eq_inv_mul_sum]

/-- **The averaged form of a finite group on the diagonal is the average of `‖π g v‖ ^ 2`.** This is
the finite form of the positive definiteness that makes the unitarian trick work: the average of
`|G|` nonnegative reals, one of which is `‖v‖ ^ 2` at `g = 1`, is positive for `v ≠ 0`. Compactness
of `G` enters the general statement `TauCeti.ContRepresentation.inner_gramOperator_self` only to
make `g ↦ ‖π g v‖ ^ 2` integrable; it is the *strict* positivity
`TauCeti.ContRepresentation.re_inner_gramOperator_self_pos` that also needs the compactness bound
on the operator norms from below. A finite group needs neither. -/
theorem inner_gramOperator_self_eq_inv_mul_sum (v : V) :
    ⟪gramOperator π hπ v, v⟫_𝕜 = (((Nat.card G : ℝ)⁻¹ * ∑ g, ‖π g v‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_gramOperator_self, integral_haarProb, smul_eq_mul]

/-- **The Gram operator of a finite group is the averaged sum of the operators `(π g)† ∘ (π g)`.**
This is `ContRepresentation.inner_gramOperator_eq_inv_mul_sum` at the level of operators:
each summand is the Gram operator of the pulled-back form `(v, w) ↦ ⟪π g v, π g w⟫`, and the Haar
average of the family is their group average. -/
theorem gramOperator_eq_smul_sum :
    gramOperator π hπ =
      (Nat.card G : 𝕜)⁻¹ • ∑ g, (ContinuousLinearMap.adjoint (π g)).comp (π g) := by
  refine ContinuousLinearMap.ext fun w ↦ ext_inner_left 𝕜 fun v ↦ ?_
  rw [inner_gramOperator_eq_inv_mul_sum, smul_apply, sum_apply, inner_smul_right, inner_sum]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦
    (ContinuousLinearMap.adjoint_inner_right (π g) v (π g w)).symm)

end Unitarization

section Maschke

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Finite G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **The unitarian trick for a finite group.** Every finite-dimensional representation of a finite
group on an inner product space is conjugate, by a continuous linear automorphism of the carrier,
to one preserving the inner product.

This is `TauCeti.ContRepresentation.exists_isUnitary_congr` with all of its compact-group
hypotheses discharged: the statement mentions neither a topology on `G` nor a measure, so the proof
installs the discrete topology and the Borel structure it averages against — a finite discrete
group is compact and every representation of it is continuous by `continuous_of_discreteTopology` —
and the caller is left with a bare finite group. The form being averaged is the explicit
`|G|⁻¹ ∑ g, ⟪π g ·, π g ·⟫` of `ContRepresentation.inner_gramOperator_eq_inv_mul_sum`. -/
theorem exists_isUnitary_congr_of_finite (π : ContRepresentation 𝕜 G V) :
    ∃ e : V ≃L[𝕜] V, IsUnitary (congr e π) := by
  let _ : TopologicalSpace G := ⊥
  have _ : DiscreteTopology G := ⟨rfl⟩
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  exact exists_isUnitary_congr π continuous_of_discreteTopology

/-- **Maschke's theorem in orthogonal form.** A finite-dimensional representation `π` of a finite
group on an inner product space is an internal direct sum of finitely many irreducible
subrepresentations, of dimensions adding up to `dim V`, which are moreover pairwise *orthogonal*
for an invariant inner product `⟪e ·, e ·⟫` obtained from the given one by a continuous linear
automorphism `e` of the carrier.

This is the finite shadow of complete reducibility, and all that is finite about it is the
production of `e`: unitarity is not assumed but produced, by the finite unitarian trick
`ContRepresentation.exists_isUnitary_congr_of_finite`, and the decomposition of `π` itself is then
`TauCeti.ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition_of_congr`, which
decomposes the unitary model and carries every block back along the equivalence of representations
`ContRepresentation.congrEquiv : π.Equiv (congr e π)` for an arbitrary group. The blocks are
therefore subrepresentations of `π` itself.

Distorting the inner product by `e` is unavoidable and is what "Maschke" costs here: Lean fixes one
inner product on `V`, and a representation of a finite group need not preserve it, only the average
`|G|⁻¹ ∑ g, ⟪π g ·, π g ·⟫` of its translates. So the blocks need not be orthogonal for `⟪·, ·⟫`,
and orthogonality is stated for the invariant form `⟪e ·, e ·⟫` that the unitarian trick produces —
equivalently, their images under `e` are the orthogonal family decomposing the unitary model
`congr e π`. It is that orthogonality which the compact theory contributes over Mathlib's Maschke,
which produces complements but no inner product; the plain semisimplicity is not restated here,
being already a Mathlib instance for every field in which `|G|` is invertible. -/
theorem exists_orthogonal_irreducible_decomposition_of_finite (π : ContRepresentation 𝕜 G V) :
    ∃ (e : V ≃L[𝕜] V) (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
      IsUnitary (congr e π) ∧
      (∀ i, (U i).toRepresentation.IsIrreducible) ∧
      (Pairwise fun i j ↦ ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪e v, e w⟫_𝕜 = 0) ∧
      DirectSum.IsInternal (fun i ↦ (U i).toSubmodule) ∧
      Module.finrank 𝕜 V = ∑ i, Module.finrank 𝕜 (U i).toSubmodule := by
  obtain ⟨e, he⟩ := exists_isUnitary_congr_of_finite π
  obtain ⟨n, U, hU⟩ := he.exists_orthogonal_irreducible_decomposition_of_congr
  exact ⟨e, n, U, he, hU⟩

end Maschke

end ContRepresentation
