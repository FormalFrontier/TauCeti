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

Let `H` be a nilpotent Lie subalgebra of `L` acting on a module `M` that is finite and free over a
principal ideal domain `K`, let `α : H → K` be a linear form, and let `x` and `y` be root vectors of
weights `α` and `-α` whose bracket `⁅x, y⁆` lies in `H`, say `⁅x, y⁆ = z`.  Acting first by `x` and
then by `y` carries the `χ`-weight space of `M` back to itself; write `TauCeti.raiseLowerEnd` for
the resulting endomorphism.  Given a rung `N` at which the space `M_{χ + Nα}` vanishes, this file
computes its trace:

```text
tr_{Mχ}(y ∘ x) = Σ_{1 ≤ j < N} dim M_{χ + jα} · (χ + jα)(z).
```

Over a field of characteristic zero and for a nonzero `α`, the `α`-string above `χ` is finite, and
the same computation takes the unbounded shape `Σ_{j ≥ 1}` that Freudenthal's formula uses, indexed
by that string with its bottom rung removed.

The argument is a ladder, with no `sl₂` representation theory and no complete reducibility.  Acting
by `x` and by `y` gives maps `Mχ → M_{α+χ}` and `M_{α+χ} → Mχ`, and swapping the two factors of a
composite does not change its trace, so `tr_{Mχ}(y ∘ x) = tr_{M_{α+χ}}(x ∘ y)`.  On `M_{α+χ}` the
Leibniz identity gives `x ∘ y - y ∘ x = z`, and the trace of `z` there is `dim M_{α+χ} · (α+χ)(z)`,
because `z` acts on a generalized weight space with the single generalized eigenvalue `(α+χ)(z)`
(`LieModule.trace_toEnd_genWeightSpace`).  Together these give the step

```text
tr_{Mχ}(y ∘ x) = tr_{M_{α+χ}}(y ∘ x) + dim M_{α+χ} · (α+χ)(z),
```

which telescopes down from a rung where the weight space is trivial: there `raiseLowerEnd` is
itself `0`, so the ladder terminates and the rungs beyond it never enter the telescope.  The
initial-segment formulation assumes such a vanishing rung explicitly.  When `K` is a field of
characteristic zero and `α` is a nonzero linear form, the string leaves the weights of `M`
after finitely many steps;
`TauCeti/Algebra/Lie/Weights/String.lean` packages that finite index set as `TauCeti.weightString`.

The identity is the computational input to **Freudenthal's multiplicity formula**: taking `x` and
`y` to be the root vectors of an `sl₂` triple attached to a positive root `α`, so that `z = α^∨`,
the right-hand side is `2 / ⟨α, α⟩` times the inner sum `Σ_{j ≥ 1} m_{μ + jα} ⟨μ + jα, α⟩` of that
recursion, by the normalization `⟨λ, α^∨⟩⟨α, α⟩ = 2⟨λ, α⟩` of the invariant form.

## Main definitions

* `TauCeti.raiseLowerEnd`: acting by a root vector of weight `α` and then by one of weight `-α`, as
  an endomorphism of the `χ`-weight space.

## Main results

* `TauCeti.trace_raiseLowerEnd_eq_trace_add_nsmul`: the ladder step, expressing the trace at `χ` in
  terms of the trace at `α + χ`.
* `TauCeti.trace_raiseLowerEnd_eq_sum_Ico`: the closed form, as a sum over `Finset.Ico 1 N` for a
  rung `N` at which the `α`-string above `χ` has a trivial weight space.
* `TauCeti.trace_raiseLowerEnd_eq_sum_weightString_erase_zero`: the same closed form, summed over
  the `α`-string above `χ` with its bottom index removed, which is the index set of the inner sum
  of Freudenthal's formula.

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

/-- Acting by a root vector on a weight vector is the bracket.  Mathlib states this elementwise
description only for the bundled `rootSpaceWeightSpaceProduct`, in
`coe_rootSpaceWeightSpaceProduct_tmul`, so the auxiliary bilinear map that this file uses is
unfolded once, here. -/
@[simp]
theorem coe_rootSpaceWeightSpaceProductAux_apply {χ₁ χ₂ χ₃ : H → K} (hχ : χ₁ + χ₂ = χ₃)
    (x : rootSpace H χ₁) (m : genWeightSpace M χ₂) :
    ((rootSpaceWeightSpaceProductAux K L H M hχ x m : genWeightSpace M χ₃) : M)
      = ⁅(x : L), (m : M)⁆ :=
  rfl

variable (M) in
/-- Acting by a root vector `x` of weight `α` and then by a root vector `y` of weight `-α`, as an
endomorphism of the `χ`-weight space of `M`. -/
def raiseLowerEnd {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (χ : H → K) : Module.End K (genWeightSpace M χ) :=
  rootSpaceWeightSpaceProductAux K L H M (neg_add_cancel_left α χ) ⟨y, hy⟩ ∘ₗ
    rootSpaceWeightSpaceProductAux K L H M rfl ⟨x, hx⟩

/-- `raiseLowerEnd` is the composite of the two root-vector actions, in that order. -/
theorem raiseLowerEnd_def {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (χ : H → K) :
    raiseLowerEnd M hx hy χ
      = rootSpaceWeightSpaceProductAux K L H M (neg_add_cancel_left α χ) ⟨y, hy⟩ ∘ₗ
        rootSpaceWeightSpaceProductAux K L H M rfl ⟨x, hx⟩ :=
  (rfl)

@[simp]
theorem coe_raiseLowerEnd_apply {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (χ : H → K) (m : genWeightSpace M χ) :
    (raiseLowerEnd M hx hy χ m : M) = ⁅y, ⁅x, (m : M)⁆⁆ := by
  rw [raiseLowerEnd_def]
  simp only [LinearMap.coe_comp, Function.comp_apply, coe_rootSpaceWeightSpaceProductAux_apply]

/-- `raiseLowerEnd` is the restriction to the `χ`-weight space of the composite of the two actions
on `M`, which is the shape in which a trace computation over a basis of `L` produces it. -/
theorem raiseLowerEnd_eq_restrict {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (χ : H → K)
    (h : ∀ m ∈ (genWeightSpace M χ).toSubmodule,
      (toEnd K L M y ∘ₗ toEnd K L M x) m ∈ (genWeightSpace M χ).toSubmodule) :
    raiseLowerEnd M hx hy χ = (toEnd K L M y ∘ₗ toEnd K L M x).restrict h := by
  ext m
  -- `simp` cannot close this: the goal spells the coercion of `m` through the Lie submodule,
  -- while `LinearMap.coe_restrict_apply` spells it through the carrier submodule.
  rw [coe_raiseLowerEnd_apply]
  exact (LinearMap.coe_restrict_apply h m).symm

/-- **The Leibniz identity, read on a weight space.**  Lowering and then raising differs from
raising and then lowering by the action of `⁅x, y⁆`. -/
private theorem rootSpaceWeightSpaceProductAux_comp_sub_raiseLowerEnd_eq_toEnd
    {α : H → K} {x y : L} {z : H}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α)) (hz : ⁅x, y⁆ = (z : L)) (χ : H → K) :
    rootSpaceWeightSpaceProductAux K L H M (rfl : α + χ = α + χ) ⟨x, hx⟩ ∘ₗ
        rootSpaceWeightSpaceProductAux K L H M (neg_add_cancel_left α χ) ⟨y, hy⟩
        - raiseLowerEnd M hx hy (α + χ)
      = toEnd K H (genWeightSpace M (α + χ)) z := by
  ext m
  have h := leibniz_lie x y (m : M)
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    AddSubgroupClass.coe_sub, coe_rootSpaceWeightSpaceProductAux_apply, coe_raiseLowerEnd_apply,
    toEnd_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, ← hz]
  rw [h]
  abel

/-- On a trivial weight space the raise-lower endomorphism vanishes. -/
@[simp]
theorem raiseLowerEnd_eq_zero {α : H → K} {x y : L} (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) {χ : H → K} (hχ : genWeightSpace M χ = ⊥) :
    raiseLowerEnd M hx hy χ = 0 := by
  ext m
  have hm : (m : M) = 0 := by simpa [hχ] using m.2
  simp [hm]

end Defs

section Trace

variable {K : Type u} {L : Type v} {M : Type w} [CommRing K] [IsDomain K]
  [IsPrincipalIdealRing K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M] {α : H → K} {x y : L} {z : H}

/-- **The ladder step.**  The trace of `y ∘ x` on the `χ`-weight space exceeds its trace on the
`(α + χ)`-weight space by `dim M_{α+χ} · (α+χ)(z)`, where `z = ⁅x, y⁆`. -/
theorem trace_raiseLowerEnd_eq_trace_add_nsmul (hx : x ∈ rootSpace H α)
    (hy : y ∈ rootSpace H (-α)) (hz : ⁅x, y⁆ = (z : L)) (χ : H → K) :
    trace K _ (raiseLowerEnd M hx hy χ)
      = trace K _ (raiseLowerEnd M hx hy (α + χ))
        + finrank K (genWeightSpace M (α + χ)) • (α + χ) z := by
  have hswap := LinearMap.trace_comp_comm' (R := K)
    (rootSpaceWeightSpaceProductAux K L H M (rfl : α + χ = α + χ) ⟨x, hx⟩)
    (rootSpaceWeightSpaceProductAux K L H M (neg_add_cancel_left α χ) ⟨y, hy⟩)
  have hcomm := congrArg (trace K (genWeightSpace M (α + χ)))
    (rootSpaceWeightSpaceProductAux_comp_sub_raiseLowerEnd_eq_toEnd (M := M) hx hy hz χ)
  rw [map_sub, trace_toEnd_genWeightSpace, sub_eq_iff_eq_add'] at hcomm
  -- `raiseLowerEnd_def` exposes the two factors that `hswap` exchanges.
  rw [raiseLowerEnd_def, hswap, hcomm]

/-- **The closed form of the trace**, as a sum over `Finset.Ico 1 N`, for any rung `N` at which the
`α`-string above `χ` has a trivial weight space.  The ladder terminates there, so nothing beyond
that rung is assumed. -/
theorem trace_raiseLowerEnd_eq_sum_Ico (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α))
    (hz : ⁅x, y⁆ = (z : L)) (χ : H → K) {N : ℕ} (hN : genWeightSpace M (χ + N • α) = ⊥) :
    trace K _ (raiseLowerEnd M hx hy χ)
      = ∑ j ∈ Finset.Ico 1 N, finrank K (genWeightSpace M (χ + j • α)) • (χ + j • α) z := by
  -- The statement at the rung `χ + i • α`, proved by induction on the number `d` of rungs between
  -- `i` and the terminal rung `N`.
  suffices h : ∀ d i : ℕ, i + d = N →
      trace K _ (raiseLowerEnd M hx hy (χ + i • α))
        = ∑ j ∈ Finset.Ico (i + 1) N,
            finrank K (genWeightSpace M (χ + j • α)) • (χ + j • α) z by
    have key := h N 0 (by omega)
    rwa [zero_nsmul, add_zero] at key
  intro d
  induction d with
  | zero =>
    intro i hi
    obtain rfl : i = N := by omega
    rw [raiseLowerEnd_eq_zero hx hy hN, map_zero, Finset.Ico_eq_empty (by omega),
      Finset.sum_empty]
  | succ d ih =>
    intro i hi
    have hshift : α + (χ + i • α) = χ + (i + 1) • α := by rw [succ_nsmul]; abel
    rw [trace_raiseLowerEnd_eq_trace_add_nsmul hx hy hz, hshift, ih (i + 1) (by omega)]
    rcases lt_or_ge (i + 1) N with hlt | hge
    · rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
      abel
    · obtain rfl : i + 1 = N := by omega
      rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega), Finset.sum_empty,
        LieSubmodule.finrank_eq_zero_of_eq_bot hN, zero_smul, add_zero]

end Trace

section WeightString

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] {H : LieSubalgebra K L} [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {α χ : Module.Dual K H} {x y : L} {z : H}

/-- **The closed form of the trace**, summed over the `α`-string above `χ` with its bottom index
removed.  This is the index set of the inner sum of Freudenthal's multiplicity formula. -/
theorem trace_raiseLowerEnd_eq_sum_weightString_erase_zero (hα : α ≠ 0)
    (hx : x ∈ rootSpace H (α : H → K)) (hy : y ∈ rootSpace H (-(α : H → K)))
    (hz : ⁅x, y⁆ = (z : L)) :
    trace K _ (raiseLowerEnd M hx hy (χ : H → K))
      = ∑ j ∈ (weightString M hα χ).erase 0,
          finrank K (genWeightSpace M ((χ + j • α : Dual K H) : H → K))
            • ((χ + j • α : Dual K H) : H → K) z := by
  classical
  -- The string API spells the shifted weight `↑(χ + j • α)`, the trace results `↑χ + j • ↑α`;
  -- `LinearMap.coe_add` and `LinearMap.coe_smul` pass between the two spellings.
  have hcoe : ∀ j : ℕ, ((χ + j • α : Dual K H) : H → K) = (χ : H → K) + j • (α : H → K) :=
    fun _ => by simp only [LinearMap.coe_add, LinearMap.coe_smul]
  obtain ⟨N, hN⟩ := exists_genWeightSpace_add_nsmul_eq_bot_of_le (M := M) hα χ
  have hN' : ∀ j : ℕ, N ≤ j → genWeightSpace M ((χ : H → K) + j • (α : H → K)) = ⊥ :=
    fun j hj => by rw [← hcoe]; exact hN j hj
  have hmem : ∀ j : ℕ, j ∈ weightString M hα χ ↔
      genWeightSpace M ((χ : H → K) + j • (α : H → K)) ≠ ⊥ :=
    fun j => by rw [mem_weightString_iff, hcoe]
  simp only [hcoe]
  rw [trace_raiseLowerEnd_eq_sum_Ico hx hy hz _ (hN' N le_rfl)]
  refine (Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)).symm
  · have hjw := (hmem j).mp (Finset.mem_of_mem_erase hj)
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    refine Finset.mem_Ico.mpr ⟨by omega, ?_⟩
    by_contra hjN
    exact hjw (hN' j (by omega))
  · have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
    have hjnot : j ∉ weightString M hα χ := fun hj'' =>
      hj' (Finset.mem_erase.mpr ⟨hj0, hj''⟩)
    have hjw : genWeightSpace M ((χ : H → K) + j • (α : H → K)) = ⊥ := by
      by_contra hne
      exact hjnot ((hmem j).mpr hne)
    rw [LieSubmodule.finrank_eq_zero_of_eq_bot hjw, zero_smul]

end WeightString

end TauCeti
