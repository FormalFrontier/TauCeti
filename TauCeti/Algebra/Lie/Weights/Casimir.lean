/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Casimir
public import TauCeti.Algebra.Lie.Weights.InvariantForm
public import TauCeti.Algebra.Lie.Weights.Projection
public import TauCeti.Algebra.Lie.Weights.Trace

/-!
# The trace of the Casimir operator on a weight space

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a splitting Cartan subalgebra, and let `M` be a
finite-dimensional `L`-module. The Casimir element `Ω ∈ U(L)` is central
(`TauCeti.casimirElement_mem_center`), so the operator it induces on `M` commutes with the action
and therefore preserves each weight space `Mμ`. This file computes the trace of its restriction:

```text
tr_{Mμ}(Ω) = dim Mμ · ⟨μ, μ⟩
  + ∑_{α ∈ roots} ∑_{j ∈ weightString(M, α, μ) \ {0}} dim M_{μ + jα} · ⟨μ + jα, α⟩,
```

with `⟨·,·⟩` the invariant form `TauCeti.invForm` on `Module.Dual K H` and `weightString(M, α, μ)`
the `α`-string above `μ` of `TauCeti.weightString`, a `Finset ℕ` whose index `j = 0` is the `μ`
rung itself.

## The argument

`TauCeti.casimirElement_eq_sum` evaluates `Ω` against any basis `x` of `L` and its Killing-dual
basis `y`, so the operator `Ω` acts as `∑ᵢ π(xᵢ) π(yᵢ)`. Inserting the root-space projections of
`TauCeti/Algebra/Lie/Weights/Projection.lean` into both slots and using that the `χ`- and
`ψ`-root spaces pair to zero under the Killing form unless `χ + ψ = 0` leaves only the opposite
pairs `(π_χ, π_{-χ})`; this is `TauCeti.sum_apply_killingDualBasis_eq_sum_weight`, stated for an
arbitrary bilinear map so that both the operator identity here and the Casimir *eigenvalue* of
`TauCeti/Algebra/Lie/HighestWeight/Casimir.lean` are instances of it.

Each surviving summand acts by a vector of one root space followed by a vector of the opposite
root space, so it preserves `Mμ` and is a `TauCeti.raiseLowerEnd` of
`TauCeti/Algebra/Lie/Weights/Trace.lean`. The two kinds of summand are then read off:

* the summands at a **zero** weight are built from two elements of `H`, which act on `Mμ` by the
  scalars `μ` gives them (the honest weight spaces of
  `TauCeti/Algebra/Lie/Weights/Diagonalizable.lean`), so their traces sum to
  `dim Mμ · ⟨μ, μ⟩`;
* the summands at a **root** `α` have `⁅x, y⁆ = κ(x, y) α^♯`, and the coefficients `κ(x, y)` sum
  to the trace `1` of a root-space projection, so the string formula
  `TauCeti.trace_raiseLowerEnd_eq_sum_weightString_erase_zero` turns their traces into
  `∑_{j ∈ weightString(M, α, μ) \ {0}} dim M_{μ + jα} · ⟨μ + jα, α⟩`.

## Main definitions

* `TauCeti.casimirGenWeightSpaceEnd`: the Casimir operator of `M`, restricted to a generalized
  weight space.

## Main results

* `TauCeti.sum_apply_killingDualBasis_eq_sum_weight`: a sum along a basis and its Killing-dual
  basis splits along the opposite pairs of root-space projections.
* `TauCeti.representation_casimirElement_eq_sum_weight`: the Casimir operator of `M`, split along
  the root spaces.
* `TauCeti.representation_casimirElement_mem_genWeightSpace`: the Casimir operator preserves every
  generalized weight space.
* `TauCeti.casimirGenWeightSpaceEnd_eq_sum`: the restriction to a weight space, as a sum of
  raise-lower endomorphisms.
* `TauCeti.trace_casimirGenWeightSpaceEnd`: **the trace of the Casimir operator on a weight
  space.**

## References

This is the Casimir half of the "Freudenthal's multiplicity recursion" item of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`; the string half is
`TauCeti/Algebra/Lie/Weights/Trace.lean`. Combining the trace computed here with the Casimir
eigenvalue `⟨λ + ρ, λ + ρ⟩ - ⟨ρ, ρ⟩` of a highest weight module is what produces the recursion
itself.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.3.
-/

public section

namespace TauCeti

open Finset LieAlgebra LieModule Module
open LinearMap (trace)

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-! ### Splitting a Killing-dual-basis sum along the root spaces -/

variable (H) in
/-- **A Killing-dual-basis sum splits along the root spaces.** For a bilinear map `f`, the sum
`∑ᵢ f xᵢ yᵢ` along a basis of `L` and its Killing-dual basis is the sum over the weights `χ` of
`H` on `L` of the same expression with `π_χ` inserted in the first slot and `π_{-χ}` in the
second. Only these opposite pairs survive, because the Killing form pairs the `χ`-root space with
the `-χ`-root space alone. -/
theorem sum_apply_killingDualBasis_eq_sum_weight {W : Type*} [AddCommGroup W] [Module K W]
    {ι : Type*} [DecidableEq ι] [Fintype ι] (f : L →ₗ[K] L →ₗ[K] W) (bs : Module.Basis ι K L) :
    ∑ i, f (bs i) (killingDualBasis bs i) =
      ∑ χ : Weight K H L, ∑ i, f (genWeightSpaceProjection K H L χ (bs i))
        (genWeightSpaceProjection K H L (-χ) (killingDualBasis bs i)) := by
  have first : ∀ i, f (bs i) (killingDualBasis bs i) =
      ∑ χ : Weight K H L, f (genWeightSpaceProjection K H L χ (bs i)) (killingDualBasis bs i) := by
    intro i
    conv_lhs => rw [← sum_genWeightSpaceProjection_apply (K := K) (L := H) (bs i)]
    rw [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ first i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  have second : ∀ i, f (genWeightSpaceProjection K H L χ (bs i)) (killingDualBasis bs i) =
      ∑ ψ : Weight K H L, f (genWeightSpaceProjection K H L χ (bs i))
        (genWeightSpaceProjection K H L ψ (killingDualBasis bs i)) := by
    intro i
    conv_lhs =>
      rw [← sum_genWeightSpaceProjection_apply (K := K) (L := H) (killingDualBasis bs i)]
    rw [map_sum]
  rw [Finset.sum_congr rfl fun i _ ↦ second i, Finset.sum_comm]
  refine Finset.sum_eq_single (-χ) (fun ψ _ hψ ↦ ?_) (by simp)
  have hmove := sum_apply_killingDualBasis_of_isAdjointPair
    (f.comp (genWeightSpaceProjection K H L χ)) bs (isAdjointPair_genWeightSpaceProjection H ψ)
  simp only [LinearMap.comp_apply] at hmove
  rw [← hmove]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [genWeightSpaceProjection_apply_apply_of_ne (fun hc ↦ hψ (by rw [← hc, neg_neg])), map_zero,
    LinearMap.zero_apply]

variable (K M) in
/-- The `K`-bilinear map sending `(x, y)` to the endomorphism `m ↦ ⁅x, ⁅y, m⁆⁆` of `M`. It is the
map through which the Casimir operator is split along the root spaces. -/
private noncomputable def doubleBracketBilin : L →ₗ[K] L →ₗ[K] Module.End K M :=
  LinearMap.mk₂ K (fun x y : L ↦ toEnd K L M x * toEnd K L M y)
    (fun x₁ x₂ y ↦ by rw [map_add, add_mul]) (fun c x y ↦ by rw [map_smul, smul_mul_assoc])
    (fun x y₁ y₂ ↦ by rw [map_add, mul_add]) (fun c x y ↦ by rw [map_smul, mul_smul_comm])

omit [IsKilling K L] [FiniteDimensional K L] in
@[simp]
private theorem doubleBracketBilin_apply (x y : L) :
    doubleBracketBilin K M x y = toEnd K L M x * toEnd K L M y := (rfl)

variable (H) in
/-- **The Casimir operator, split along the root spaces.** For any basis `x` of `L` and its
Killing-dual basis `y`, the operator by which the Casimir element acts on `M` is the sum over the
weights `χ` of `H` on `L` of `∑ᵢ π(π_χ xᵢ) π(π_{-χ} yᵢ)`. -/
theorem representation_casimirElement_eq_sum_weight {ι : Type*} [DecidableEq ι] [Fintype ι]
    (bs : Module.Basis ι K L) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) =
      ∑ χ : Weight K H L, ∑ i, toEnd K L M (genWeightSpaceProjection K H L χ (bs i)) *
        toEnd K L M (genWeightSpaceProjection K H L (-χ) (killingDualBasis bs i)) := by
  rw [casimirElement_eq_sum bs, map_sum]
  simp only [map_mul, UniversalEnvelopingAlgebra.representation_ι]
  simpa only [doubleBracketBilin_apply] using
    sum_apply_killingDualBasis_eq_sum_weight H (doubleBracketBilin K M) bs

/-! ### Sums built from the extended weight

The extension `TauCeti.killingExtend` of a weight to a linear form on `L` lives in
`TauCeti/Algebra/Lie/Weights/InvariantForm.lean`; the two sums below are the ones that need the
root-space projections and the Killing-dual basis as well. -/

/-- **The extension of a weight sees only the zero weight**, so the products of its values on the
root-space projections of two vectors telescope to the product of its values on the vectors. -/
theorem sum_killingExtend_genWeightSpaceProjection_mul (lam : Module.Dual K H) (x y : L) :
    ∑ χ : Weight K H L, killingExtend lam (genWeightSpaceProjection K H L χ x) *
        killingExtend lam (genWeightSpaceProjection K H L χ y) =
      killingExtend lam x * killingExtend lam y := by
  conv_rhs =>
    rw [← sum_genWeightSpaceProjection_apply (K := K) (L := H) x,
      ← sum_genWeightSpaceProjection_apply (K := K) (L := H) y]
  rw [map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun χ _ ↦ (Finset.sum_eq_single
    (f := fun ψ : Weight K H L ↦ killingExtend lam (genWeightSpaceProjection K H L χ x) *
      killingExtend lam (genWeightSpaceProjection K H L ψ y))
    χ (fun ψ _ hψ ↦ ?_) (fun h ↦ absurd (Finset.mem_univ χ) h)).symm
  by_cases hχ : χ.IsZero
  · refine mul_eq_zero_of_right _ (killingExtend_apply_eq_zero lam (χ := ψ) ?_
      (genWeightSpaceProjection_apply_mem ψ y))
    exact fun hz ↦ hψ (Weight.ext fun z ↦ by rw [hz.eq, hχ.eq])
  · exact mul_eq_zero_of_left
      (killingExtend_apply_eq_zero lam hχ (genWeightSpaceProjection_apply_mem χ x)) _

omit [IsTriangularizable K H L] in
/-- **The squared length of a weight, read along a Killing-dual pair of bases.** The extension of
`lam` is the pairing with the vector representing `lam`, so expanding that vector in the basis
gives `⟨lam, lam⟩`. -/
theorem sum_killingExtend_mul_killingExtend_killingDualBasis {ι : Type*} [DecidableEq ι]
    [Fintype ι] (lam : Module.Dual K H) (bs : Module.Basis ι K L) :
    ∑ i, killingExtend lam (bs i) * killingExtend lam (killingDualBasis bs i) =
      invForm lam lam := by
  have hrep := congrArg (killingExtend lam)
    (sum_killingForm_smul_basis bs (((IsKilling.cartanEquivDual H).symm lam : H) : L))
  rw [map_sum] at hrep
  simp only [map_smul, smul_eq_mul, ← killingExtend_apply] at hrep
  rw [invForm_apply_apply, ← killingExtend_apply_cartan lam, ← hrep]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-! ### The Casimir operator on a weight space -/

omit [IsTriangularizable K H L] in
/-- **The Casimir operator preserves every generalized weight space.** It commutes with the Lie
action (`TauCeti.representation_casimirElement_lie`), hence with every power of
`toEnd x - mu x`. -/
theorem representation_casimirElement_mem_genWeightSpace {mu : H → K} {m : M}
    (hm : m ∈ genWeightSpace M mu) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m ∈
      genWeightSpace M mu := by
  have hcomm : ∀ x : H, Commute (toEnd K H M x - mu x • (1 : Module.End K M))
      (UniversalEnvelopingAlgebra.representation K L M (casimirElement K L)) := by
    intro x
    have h : Commute (toEnd K H M x)
        (UniversalEnvelopingAlgebra.representation K L M (casimirElement K L)) :=
      LinearMap.ext fun z ↦ (representation_casimirElement_lie (x : L) z).symm
    exact h.sub_left ((Commute.one_left _).smul_left _)
  rw [LieModule.mem_genWeightSpace] at hm ⊢
  intro x
  obtain ⟨k, hk⟩ := hm x
  refine ⟨k, ?_⟩
  calc ((toEnd K H M x - mu x • (1 : Module.End K M)) ^ k)
        (UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m)
      = (((toEnd K H M x - mu x • (1 : Module.End K M)) ^ k) *
          UniversalEnvelopingAlgebra.representation K L M (casimirElement K L)) m :=
        (Module.End.mul_apply _ _ _).symm
    _ = (UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) *
          ((toEnd K H M x - mu x • (1 : Module.End K M)) ^ k)) m := by rw [(hcomm x).pow_left k]
    _ = 0 := by rw [Module.End.mul_apply, hk, map_zero]

variable (M) in
/-- **The Casimir operator of a weight space**: the operator by which the Casimir element acts on
`M`, restricted to the generalized `mu`-weight space, which it preserves. -/
noncomputable def casimirGenWeightSpaceEnd (mu : H → K) : Module.End K (genWeightSpace M mu) :=
  LinearMap.restrict (UniversalEnvelopingAlgebra.representation K L M (casimirElement K L))
    fun _ hm ↦ representation_casimirElement_mem_genWeightSpace hm

omit [IsTriangularizable K H L] in
/-- The Casimir operator of a weight space is the restriction of the Casimir operator of `M`. -/
@[simp]
theorem coe_casimirGenWeightSpaceEnd_apply {mu : H → K} (m : genWeightSpace M mu) :
    (casimirGenWeightSpaceEnd M mu m : M) =
      UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) (m : M) := (rfl)

variable (H) in
/-- **The Casimir operator of a weight space, split along the root spaces.** Each summand raises
by a vector of the `χ`-root space and lowers by one of the `-χ`-root space, so it is a
`TauCeti.raiseLowerEnd`. -/
theorem casimirGenWeightSpaceEnd_eq_sum {ι : Type*} [DecidableEq ι] [Fintype ι]
    (bs : Module.Basis ι K L) (mu : H → K) :
    casimirGenWeightSpaceEnd M mu =
      ∑ χ : Weight K H L, ∑ i,
        raiseLowerEnd M (genWeightSpaceProjection_apply_mem χ (killingDualBasis bs i))
          (genWeightSpaceProjection_apply_mem (-χ) (bs i)) mu := by
  have hswap : ∑ χ : Weight K H L, ∑ i,
      toEnd K L M (genWeightSpaceProjection K H L χ (bs i)) *
        toEnd K L M (genWeightSpaceProjection K H L (-χ) (killingDualBasis bs i)) =
      ∑ χ : Weight K H L, ∑ i,
        toEnd K L M (genWeightSpaceProjection K H L (-χ) (bs i)) *
          toEnd K L M (genWeightSpaceProjection K H L χ (killingDualBasis bs i)) := by
    refine (Fintype.sum_equiv (Equiv.neg (Weight K H L)) _ _ fun χ ↦ ?_).symm
    simp only [Equiv.neg_apply, neg_neg]
  ext m
  have hval := DFunLike.congr_fun (representation_casimirElement_eq_sum_weight (M := M) H bs)
    (m : M)
  rw [hswap] at hval
  simp only [LinearMap.sum_apply, Module.End.mul_apply, toEnd_apply_apply] at hval
  simpa only [coe_casimirGenWeightSpaceEnd_apply, LinearMap.sum_apply,
    AddSubmonoidClass.coe_finsetSum, coe_raiseLowerEnd_apply] using hval

/-! ### The two kinds of summand -/

section Trace

variable [CharZero K] [IsAlgClosed K] [FiniteDimensional K M]

omit [IsTriangularizable K H L] in
/-- **The zero-weight summands are scalars.** A raise-lower endomorphism built from two elements
of the Cartan subalgebra acts on the `mu`-weight space by the scalar `mu` gives them, because the
weight spaces are honest simultaneous eigenspaces. -/
theorem trace_raiseLowerEnd_of_eq_zero {mu : Module.Dual K H} {alpha : H → K} (halpha : alpha = 0)
    {x y : L} (hx : x ∈ rootSpace H alpha) (hy : y ∈ rootSpace H (-alpha)) :
    trace K _ (raiseLowerEnd M hx hy (mu : H → K)) =
      finrank K (genWeightSpace M (mu : H → K)) • (killingExtend mu x * killingExtend mu y) := by
  subst halpha
  have hxH : x ∈ H := by
    rwa [LieAlgebra.rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] at hx
  have hyH : y ∈ H := by
    rwa [neg_zero, LieAlgebra.rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] at hy
  have key : raiseLowerEnd M hx hy (mu : H → K) =
      (killingExtend mu x * killingExtend mu y) • LinearMap.id := by
    refine LinearMap.ext fun m ↦ Subtype.ext ?_
    have hm := mem_genWeightSpace_iff_forall_lie_eq_smul.mp m.2
    rw [coe_raiseLowerEnd_apply, hm ⟨x, hxH⟩, lie_smul, hm ⟨y, hyH⟩, smul_smul,
      killingExtend_apply_cartan mu ⟨x, hxH⟩, killingExtend_apply_cartan mu ⟨y, hyH⟩]
    simp
  rw [key, map_smul, LinearMap.trace_id, smul_eq_mul, nsmul_eq_mul, mul_comm]

omit [IsAlgClosed K] in
/-- **The summands at a root sum to a string sum.** Each summand at the root `chi` lowers and
raises by root vectors whose bracket is a multiple of the vector representing `chi`, so the string
formula applies; the multiples sum to the trace `1` of a root-space projection. -/
theorem sum_trace_raiseLowerEnd_of_ne_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (bs : Module.Basis ι K L) {chi : Weight K H L} (hchi : (chi : Module.Dual K H) ≠ 0)
    (mu : Module.Dual K H) :
    ∑ i, trace K _ (raiseLowerEnd M
        (genWeightSpaceProjection_apply_mem chi (killingDualBasis bs i))
        (genWeightSpaceProjection_apply_mem (-chi) (bs i)) (mu : H → K)) =
      ∑ j ∈ (weightString M hchi mu).erase 0,
        finrank K (genWeightSpace M ((mu + j • (chi : Module.Dual K H) : Module.Dual K H) : H → K))
          • invForm (mu + j • (chi : Module.Dual K H)) (chi : Module.Dual K H) := by
  set alpha : Module.Dual K H := (chi : Module.Dual K H) with halpha
  set c : ι → K := fun i ↦ killingForm K L (genWeightSpaceProjection K H L chi
    (killingDualBasis bs i)) (genWeightSpaceProjection K H L (-chi) (bs i)) with hc
  -- The bracket of the two root vectors is `c i` times the vector representing `chi`.
  have hstep : ∀ i, trace K _ (raiseLowerEnd M
      (genWeightSpaceProjection_apply_mem chi (killingDualBasis bs i))
      (genWeightSpaceProjection_apply_mem (-chi) (bs i)) (mu : H → K)) =
      ∑ j ∈ (weightString M hchi mu).erase 0,
        finrank K (genWeightSpace M ((mu + j • alpha : Module.Dual K H) : H → K))
          • (c i * invForm (mu + j • alpha) alpha) := by
    intro i
    have hz : ⁅genWeightSpaceProjection K H L chi (killingDualBasis bs i),
        genWeightSpaceProjection K H L (-chi) (bs i)⁆ =
        ((c i • (IsKilling.cartanEquivDual H).symm alpha : H) : L) := by
      rw [IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
        (genWeightSpaceProjection_apply_mem chi (killingDualBasis bs i))
        (genWeightSpaceProjection_apply_mem (-chi) (bs i))]
      simp [hc, halpha]
    refine (trace_raiseLowerEnd_eq_sum_weightString_erase_zero (M := M) hchi
      (genWeightSpaceProjection_apply_mem chi (killingDualBasis bs i))
      (genWeightSpaceProjection_apply_mem (-chi) (bs i)) hz).trans
      (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [map_smul, smul_eq_mul, invForm_apply_apply]
  -- The coefficients sum to the trace of the projection onto the `-chi`-root space, which is `1`.
  have hcsum : ∑ i, c i = 1 := by
    have hnz : (-chi).IsNonZero := by
      intro h
      apply hchi
      rw [halpha]
      exact Weight.coe_toLinear_eq_zero_iff.mpr (by simpa using h.neg)
    have hcoef : ∀ i, c i = killingForm K L (genWeightSpaceProjection K H L (-chi) (bs i))
        (killingDualBasis bs i) := by
      intro i
      have h1 : killingForm K L (genWeightSpaceProjection K H L (-chi) (bs i))
          (killingDualBasis bs i) =
          killingForm K L (genWeightSpaceProjection K H L (-chi) (bs i))
            (genWeightSpaceProjection K H L chi (killingDualBasis bs i)) := by
        conv_lhs => rw [← genWeightSpaceProjection_apply_apply (-chi) (bs i)]
        rw [killingForm_genWeightSpaceProjection H (-chi), neg_neg]
      simp only [hc, h1]
      apply LieModule.traceForm_comm
    rw [Finset.sum_congr rfl fun i _ ↦ hcoef i, sum_killingForm_killingDualBasis_eq_trace,
      trace_genWeightSpaceProjection_eq_one H hnz]
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.smul_sum, ← Finset.sum_mul, hcsum, one_mul]

/-! ### The trace -/

variable (M) in
/-- **The trace of the Casimir operator on a weight space.** For a finite-dimensional module `M`
over a Killing-semisimple Lie algebra and a linear form `mu` on the Cartan subalgebra, the trace
of the Casimir operator on the `mu`-weight space of `M` is

`dim M_mu ⟨mu, mu⟩ + ∑_{α ∈ roots} ∑_{j ∈ weightString(M, α, mu) \ {0}} dim M_{mu + jα}
⟨mu + jα, α⟩`.

The inner sums run over the `α`-string above `mu` (`TauCeti.weightString`, a `Finset ℕ`) with the
`mu` rung `j = 0` removed, which is where the terms with a zero weight space are already absent. -/
theorem trace_casimirGenWeightSpaceEnd (mu : Module.Dual K H) :
    trace K _ (casimirGenWeightSpaceEnd M (mu : H → K)) =
      finrank K (genWeightSpace M (mu : H → K)) • invForm mu mu +
        ∑ a : H.root, ∑ j ∈ (weightString M
            (Weight.coe_toLinear_ne_zero_iff.mpr (H.isNonZero_coe_root a)) mu).erase 0,
          finrank K (genWeightSpace M ((mu + j • ((a : Weight K H L) : Module.Dual K H) :
              Module.Dual K H) : H → K))
            • invForm (mu + j • ((a : Weight K H L) : Module.Dual K H))
              ((a : Weight K H L) : Module.Dual K H) := by
  classical
  set bs := Module.finBasis K L
  set u : Weight K H L → K := fun chi ↦ ∑ i,
    killingExtend mu (genWeightSpaceProjection K H L chi (killingDualBasis bs i)) *
      killingExtend mu (genWeightSpaceProjection K H L chi (bs i)) with hu
  -- `u` vanishes at every root, and its total over all weights is `⟨mu, mu⟩`.
  have hu_root : ∀ chi ∈ H.root, u chi = 0 := fun chi hchi ↦
    Finset.sum_eq_zero fun i _ ↦ mul_eq_zero_of_left (killingExtend_apply_eq_zero mu
      (H.isNonZero_coe_root ⟨chi, hchi⟩)
      (genWeightSpaceProjection_apply_mem chi (killingDualBasis bs i))) _
  have hu_total : ∑ chi : Weight K H L, u chi = invForm mu mu := by
    rw [hu, Finset.sum_comm, ← sum_killingExtend_mul_killingExtend_killingDualBasis mu bs]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [sum_killingExtend_genWeightSpaceProjection_mul, mul_comm]
  rw [casimirGenWeightSpaceEnd_eq_sum H bs]
  simp only [map_sum]
  rw [← Finset.sum_sdiff (Finset.subset_univ H.root)]
  congr 1
  · -- The zero weight contributes `dim M_mu ⟨mu, mu⟩`.
    have hzero : ∀ chi ∈ Finset.univ \ H.root, ∑ i, trace K _ (raiseLowerEnd M
        (genWeightSpaceProjection_apply_mem chi (killingDualBasis bs i))
        (genWeightSpaceProjection_apply_mem (-chi) (bs i)) (mu : H → K)) =
        finrank K (genWeightSpace M (mu : H → K)) • u chi := by
      intro chi hchi
      have hz : chi.IsZero := not_not.mp (by simpa [LieSubalgebra.root] using
        (Finset.mem_sdiff.mp hchi).2)
      have hneg : -chi = chi := Weight.ext fun z ↦ by simp [hz.eq]
      rw [hu, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [trace_raiseLowerEnd_of_eq_zero hz.eq, hneg]
    rw [Finset.sum_congr rfl hzero, ← Finset.smul_sum, ← hu_total,
      ← Finset.sum_sdiff (Finset.subset_univ H.root), Finset.sum_eq_zero hu_root, add_zero]
  · rw [← Finset.sum_coe_sort H.root]
    exact Finset.sum_congr rfl fun a _ ↦ sum_trace_raiseLowerEnd_of_ne_zero bs
      (Weight.coe_toLinear_ne_zero_iff.mpr (H.isNonZero_coe_root a)) mu

end Trace

end TauCeti
