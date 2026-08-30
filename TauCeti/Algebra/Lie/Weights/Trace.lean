/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Submodule.Finrank
public import TauCeti.Algebra.Lie.Weights.String

public section

/-!
# The trace of a pair of opposite root vectors on a weight space

Let `H` be a nilpotent Lie subalgebra of `L` acting on a finite-dimensional module `M`, let
`α : H → K` be a linear form, and let `x` and `y` be root vectors of weights `α` and `-α` whose
bracket `⁅x, y⁆` lies in `H`, say `⁅x, y⁆ = z`.  Acting first by `x` and then by `y` carries the
`χ`-weight space of `M` back to itself; write `TauCeti.raiseLowerEnd` for the resulting
endomorphism.  Given a bound beyond which the spaces `M_{χ + jα}` vanish, this file computes its
trace:

```text
tr_{Mχ}(y ∘ x) = Σ_{j ≥ 1} dim M_{χ + jα} · (χ + jα)(z).
```

The argument is a ladder, with no `sl₂` representation theory and no complete reducibility.  Acting
by `x` and by `y` gives maps `Mχ → M_{α+χ}` and `M_{α+χ} → Mχ`, and swapping the two factors of a
composite does not change its trace, so `tr_{Mχ}(y ∘ x) = tr_{M_{α+χ}}(x ∘ y)`.  On `M_{α+χ}` the
Leibniz identity gives `x ∘ y - y ∘ x = z`, and the trace of `z` there is `dim M_{α+χ} · (α+χ)(z)`,
because `z` acts on a generalized weight space with the single generalized eigenvalue `(α+χ)(z)`
(`LieModule.trace_toEnd_genWeightSpace`).  Together these give the step

```text
tr_{Mχ}(y ∘ x) = tr_{M_{α+χ}}(y ∘ x) + dim M_{α+χ} · (α+χ)(z),
```

which telescopes up the `α`-string.  The initial-segment formulation assumes such an
eventual-vanishing bound explicitly.  When `K` has characteristic zero and `α` is a nonzero linear
form, the string leaves the weights of `M` after finitely many steps;
`TauCeti/Algebra/Lie/Weights/String.lean` packages that finite index set as `TauCeti.weightString`.

The identity is the computational input to **Freudenthal's multiplicity formula**: taking `x` and
`y` to be the root vectors of an `sl₂` triple attached to a positive root `α`, so that `z = α^∨`,
the right-hand side is `2 / ⟨α, α⟩` times the inner sum `Σ_{j ≥ 1} m_{μ + jα} ⟨μ + jα, α⟩` of that
recursion, by the normalization `⟨λ, α^∨⟩⟨α, α⟩ = 2⟨λ, α⟩` of the invariant form.

## Main definitions

* `TauCeti.rootVectorMap`: the action of a root vector of weight `α`, as a linear map from the
  `χ`-weight space to the `(α + χ)`-weight space.
* `TauCeti.raiseLowerEnd`: acting by a root vector of weight `α` and then by one of weight `-α`, as
  an endomorphism of the `χ`-weight space.

## Main results

* `TauCeti.trace_raiseLowerEnd_eq_trace_add_nsmul`: the ladder step, expressing the trace at `χ` in
  terms of the trace at `α + χ`.
* `TauCeti.trace_raiseLowerEnd_eq_sum_Ico`: the closed form, as a sum over an initial segment of
  `ℕ` reaching past the end of the `α`-string.
* `TauCeti.trace_raiseLowerEnd_eq_sum_weightString`: the same closed form, summed over the
  `α`-string above `χ` with its bottom index removed, which is the index set of the inner sum of
  Freudenthal's formula.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.3, where
  this trace computation is the lemma behind Freudenthal's formula.
* [Highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 7, "Freudenthal's multiplicity formula", to be proved "from the Casimir eigenvalue and the
  `sl₂`-string action of each `⟨eₐ, hₐ, fₐ⟩` on the weight spaces".  The string action is what is
  computed here.
-/

namespace TauCeti

open LieAlgebra LieModule Module
open LinearMap (trace)

universe u v w

section Defs

variable {K : Type u} {L : Type v} {M : Type w} [CommRing K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

variable (M) in
/-- The action of a root vector `x` of weight `α`, as a map from the `χ`-weight space of `M` to the
`ψ`-weight space, for `ψ = α + χ`.  The target weight is an argument rather than the literal sum,
so that the composites below stay in normal form. -/
def rootVectorMap {α χ ψ : H → K} {x : L} (hx : x ∈ rootSpace H α) (hψ : α + χ = ψ) :
    genWeightSpace M χ →ₗ[K] genWeightSpace M ψ :=
  (toEnd K L M x).restrict fun _ hm =>
    hψ ▸ mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H M α χ hx hm

@[simp]
theorem coe_rootVectorMap_apply {α χ ψ : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hψ : α + χ = ψ) (m : genWeightSpace M χ) :
    (rootVectorMap M hx hψ m : M) = ⁅x, (m : M)⁆ :=
  (rfl)

variable (M) in
/-- Acting by a root vector `x` of weight `α` and then by a root vector `y` of weight `-α`, as an
endomorphism of the `χ`-weight space of `M`. -/
def raiseLowerEnd {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (χ : H → K) : Module.End K (genWeightSpace M χ) :=
  rootVectorMap M hy (neg_add_cancel_left α χ) ∘ₗ rootVectorMap M hx rfl

@[simp]
theorem coe_raiseLowerEnd_apply {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (χ : H → K) (m : genWeightSpace M χ) :
    (raiseLowerEnd M hx hy χ m : M) = ⁅y, ⁅x, (m : M)⁆⁆ :=
  (rfl)

/-- **The Leibniz identity, read on a weight space.**  Lowering and then raising differs from
raising and then lowering by the action of `⁅x, y⁆`. -/
theorem rootVectorMap_comp_rootVectorMap_sub_raiseLowerEnd {α : H → K} {x y : L} {z : H}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α)) (hz : ⁅x, y⁆ = (z : L)) (χ : H → K) :
    rootVectorMap M hx (rfl : α + χ = α + χ) ∘ₗ rootVectorMap M hy (neg_add_cancel_left α χ)
        - raiseLowerEnd M hx hy (α + χ)
      = toEnd K H (genWeightSpace M (α + χ)) z := by
  ext m
  have h := leibniz_lie x y (m : M)
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    AddSubgroupClass.coe_sub, coe_rootVectorMap_apply, coe_raiseLowerEnd_apply,
    toEnd_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, ← hz]
  rw [h]
  abel

end Defs

section Trace

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {α : H → K} {x y : L} {z : H}

omit [FiniteDimensional K M] in
/-- A trivial weight space has dimension zero, so it contributes nothing to a multiplicity sum. -/
private theorem finrank_genWeightSpace_eq_zero {χ : H → K} (hχ : genWeightSpace M χ = ⊥) :
    finrank K (genWeightSpace M χ) = 0 := by
  rw [hχ, ← finrank_toSubmodule, LieSubmodule.bot_toSubmodule, finrank_bot]

omit [FiniteDimensional K M] in
/-- On a trivial weight space the raise-lower endomorphism vanishes. -/
theorem raiseLowerEnd_eq_zero (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α)) {χ : H → K}
    (hχ : genWeightSpace M χ = ⊥) : raiseLowerEnd M hx hy χ = 0 := by
  ext m
  have hm : (m : M) = 0 := by simpa [hχ] using m.2
  simp [hm]

/-- **The ladder step.**  The trace of `y ∘ x` on the `χ`-weight space exceeds its trace on the
`(α + χ)`-weight space by `dim M_{α+χ} · (α+χ)(z)`, where `z = ⁅x, y⁆`. -/
theorem trace_raiseLowerEnd_eq_trace_add_nsmul (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (hz : ⁅x, y⁆ = (z : L)) (χ : H → K) :
    trace K _ (raiseLowerEnd M hx hy χ)
      = trace K _ (raiseLowerEnd M hx hy (α + χ))
        + finrank K (genWeightSpace M (α + χ)) • (α + χ) z := by
  have hswap := LinearMap.trace_comp_comm' (R := K) (rootVectorMap M hx (rfl : α + χ = α + χ))
    (rootVectorMap M hy (neg_add_cancel_left α χ))
  have hcomm := congrArg (trace K (genWeightSpace M (α + χ)))
    (rootVectorMap_comp_rootVectorMap_sub_raiseLowerEnd (M := M) hx hy hz χ)
  rw [map_sub, trace_toEnd_genWeightSpace, sub_eq_iff_eq_add'] at hcomm
  -- Unfolding `raiseLowerEnd` exposes the two factors that `hswap` exchanges.
  rw [raiseLowerEnd, hswap, hcomm]

/-- **The closed form of the trace**, as a sum over an initial segment of `ℕ` reaching past the end
of the `α`-string above `χ`. -/
theorem trace_raiseLowerEnd_eq_sum_Ico (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α))
    (hz : ⁅x, y⁆ = (z : L)) (χ : H → K) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → genWeightSpace M (χ + j • α) = ⊥) :
    trace K _ (raiseLowerEnd M hx hy χ)
      = ∑ j ∈ Finset.Ico 1 N, finrank K (genWeightSpace M (χ + j • α)) • (χ + j • α) z := by
  have hterm : ∀ k : ℕ, N ≤ k →
      finrank K (genWeightSpace M (χ + k • α)) • (χ + k • α) z = 0 := fun k hk => by
    rw [finrank_genWeightSpace_eq_zero (hN k hk), zero_smul]
  -- The statement at the rung `χ + i • α`, proved by induction on the number of rungs `d` still
  -- available before the string is known to have ended.
  suffices h : ∀ d i : ℕ, N ≤ i + d →
      trace K _ (raiseLowerEnd M hx hy (χ + i • α))
        = ∑ j ∈ Finset.Ico (i + 1) N,
            finrank K (genWeightSpace M (χ + j • α)) • (χ + j • α) z by
    have key := h N 0 (by omega)
    rwa [zero_nsmul, add_zero] at key
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [raiseLowerEnd_eq_zero hx hy (hN i (by omega)), map_zero,
      Finset.Ico_eq_empty (by omega), Finset.sum_empty]
  | succ d ih =>
    intro i hi
    rcases le_or_gt N i with hiN | hiN
    · rw [raiseLowerEnd_eq_zero hx hy (hN i hiN), map_zero,
        Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have hshift : α + (χ + i • α) = χ + (i + 1) • α := by rw [succ_nsmul]; abel
    rw [trace_raiseLowerEnd_eq_trace_add_nsmul hx hy hz, hshift, ih (i + 1) (by omega)]
    rcases lt_or_ge (i + 1) N with hlt | hge
    · rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
      abel
    · rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega), Finset.sum_empty,
        hterm (i + 1) hge, add_zero]

end Trace

section WeightString

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] {H : LieSubalgebra K L} [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {α χ : Module.Dual K H} {x y : L} {z : H}

omit [CharZero K] [LieRing.IsNilpotent H] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] in
/-- Translating a linear weight by a multiple of another is the same operation before and after
forgetting linearity. -/
private theorem coe_add_nsmul (j : ℕ) :
    ((χ + j • α : Module.Dual K H) : H → K) = (χ : H → K) + j • (α : H → K) := by
  ext v
  simp

/-- **The closed form of the trace**, summed over the `α`-string above `χ` with its bottom index
removed.  This is the index set of the inner sum of Freudenthal's multiplicity formula. -/
theorem trace_raiseLowerEnd_eq_sum_weightString (hα : α ≠ 0)
    (hx : x ∈ rootSpace H (α : H → K)) (hy : y ∈ rootSpace H (-(α : H → K)))
    (hz : ⁅x, y⁆ = (z : L)) :
    trace K _ (raiseLowerEnd M hx hy (χ : H → K))
      = ∑ j ∈ (weightString M hα χ).erase 0,
          finrank K (genWeightSpace M ((χ : H → K) + j • (α : H → K)))
            • ((χ : H → K) + j • (α : H → K)) z := by
  classical
  obtain ⟨N, hN⟩ := exists_genWeightSpace_add_nsmul_eq_bot_of_le (M := M) hα χ
  simp only [coe_add_nsmul] at hN
  have hmem : ∀ j : ℕ, j ∈ weightString M hα χ ↔
      genWeightSpace M ((χ : H → K) + j • (α : H → K)) ≠ ⊥ := fun j => by
    rw [mem_weightString_iff, coe_add_nsmul]
  rw [trace_raiseLowerEnd_eq_sum_Ico hx hy hz _ hN]
  refine (Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)).symm
  · have hjw := (hmem j).mp (Finset.mem_of_mem_erase hj)
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    refine Finset.mem_Ico.mpr ⟨by omega, ?_⟩
    by_contra hjN
    exact hjw (hN j (by omega))
  · have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
    have hjnot : j ∉ weightString M hα χ := fun hj'' =>
      hj' (Finset.mem_erase.mpr ⟨hj0, hj''⟩)
    have hjw : genWeightSpace M ((χ : H → K) + j • (α : H → K)) = ⊥ := by
      by_contra hne
      exact hjnot ((hmem j).mpr hne)
    rw [finrank_genWeightSpace_eq_zero hjw, zero_smul]

end WeightString

end TauCeti
