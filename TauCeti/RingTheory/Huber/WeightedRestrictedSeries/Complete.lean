/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Bounded
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.UniformFilterBasis

/-!
# Completeness of the weighted restricted power series over a complete base

Over a nonarchimedean ring `A` whose weights `Tν = T₁^ν₁ ⋯ Tₖ^νₖ` are bounded
(`TauCeti.Huber.IsBounded`), the weighted restricted power-series ring
`TauCeti.Huber.weightedRestrictedSubring` is Hausdorff whenever `A` is, and complete over a
complete uniform `A`. Boundedness is the whole of what the arguments need beyond Wedhorn's
standing hypothesis: the neighbourhood subgroup `U⟨X⟩` maps into `Tν · U` coefficientwise, and
boundedness of `Tν` says exactly that `Tν · U` still shrinks to zero with `U`, so the
coefficient maps are continuous — and uniformly continuous once `A` carries a uniformity.
Points are then separated coefficientwise, and a Cauchy filter of restricted series is
coefficientwise Cauchy, its coefficientwise limit is again restricted, and the filter converges
to it. Both facts are Wedhorn's Proposition 5.49 (*Adic Spaces*, arXiv:1910.05934v1) —
Hausdorffness is its part (2), and completeness is the step its part (3) is proved by, the one
that then identifies `A⟨X⟩_T` with the completion of `A[X]_T`. Its part (1), density of the
polynomials, is `TauCeti.Huber.dense_weightedPolynomials` in the parent module.

The trivial weight family `Tᵢ = {1}` is bounded, since `Tν` is then the singleton `{1}`, so the
ordinary restricted power-series ring `A⟨X⟩` gets each of the four facts by specialisation. It
is that case the comparison below runs on, and the two `T0Space`/`CompleteSpace` statements are
registered as instances there.

Hausdorffness is purely topological — it uses only continuity of the coefficient maps — so it
is proved in a section over a nonarchimedean ring with no uniformity of its own, which is the
setting the rest of the Huber development works in; the uniform hypotheses on `A` enter only
with completeness.

Consequently `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A` collapses:
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` identifies `A⟨X₁,…,Xₖ⟩` with the
plain restricted-series ring — the "comparison with the usual completed restricted
power-series algebra" milestone of roadmap Layer 0.5. Its hypotheses are completeness and
Hausdorffness of that ring itself rather than of `A`, which the instances here supply over a
complete Hausdorff base and which hold over a discrete base too, so that the comparison also
covers `TauCeti.Huber.IsStronglyNoetherian.of_discreteTopology`. It is packaged twice over
one and the same underlying map — as that ring isomorphism and as the `A`-algebra equivalence
`TauCeti.Huber.restrictedMvPowerSeriesCompletionAlgEquiv`, the two tied together by
`TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionAlgEquiv` and
`TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm` — and both it and its
inverse are uniformly continuous, hence continuous by `UniformContinuous.continuous`. Nothing
in that block is special to restricted series: every declaration in it specializes a generic
statement about `UniformSpace.Completion.completeRingEquivSelf` proved in
`TauCeti.Topology.Algebra.UniformRing`.

Three steps are named as `private` lemmas rather than exported as API. That the subring's
uniformity is the one its subgroup basis induces is definitional, and is named so that the
argument does not silently depend on the two being reducibly equal; it specializes Mathlib's
`AddGroupFilterBasis.cauchy_iff`, with a single use here. The passage of a Cauchy filter to its
coefficientwise limits — where `Tν · U` has to be closed, by
`TauCeti.Huber.IsWeightFamily.isOpen_weightMul` and `AddSubgroup.isClosed_of_isOpen` — is used
twice in the completeness proof. Boundedness of the trivial weight, read off
`TauCeti.Huber.weightPow_one_weight` and `TauCeti.Huber.isBounded_singleton`, is what all four
specialisations are discharged with.

## Main results

* `TauCeti.Huber.IsWeightFamily.continuous_coeff` and
  `TauCeti.Huber.IsWeightFamily.uniformContinuous_coeff` : the `ν`-th coefficient map of
  `A⟨X⟩_T` is continuous, and uniformly continuous over a uniform base, as soon as the single
  weight `Tν` is bounded.
* `TauCeti.Huber.t0Space_weightedRestrictedSubring` : Wedhorn 5.49(2) — with every weight
  bounded, `A⟨X⟩_T` over a Hausdorff base is Hausdorff.
* `TauCeti.Huber.completeSpace_weightedRestrictedSubring` : Wedhorn 5.49(3) — with every weight
  bounded, `A⟨X⟩_T` over a complete base is complete.
* `TauCeti.Huber.continuous_coeff_one_weight`,
  `TauCeti.Huber.t0Space_weightedRestrictedSubring_one_weight`,
  `TauCeti.Huber.uniformContinuous_coeff_one_weight` and
  `TauCeti.Huber.completeSpace_weightedRestrictedSubring_one_weight` : those four at the
  trivial weight family. The `T0Space` and `CompleteSpace` ones are the registered instances;
  the two coefficient-map results are theorems. This is the case the comparison needs.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` : the comparison — `A⟨X₁,…,Xₖ⟩` is
  the plain restricted-series ring, whenever that ring is complete and Hausdorff.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionAlgEquiv` : the same comparison as an
  `A`-algebra equivalence.
* `TauCeti.Huber.uniformContinuous_restrictedMvPowerSeriesCompletionEquiv` and
  `TauCeti.Huber.uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm` : the
  comparison and its inverse are uniformly continuous. The inverse is the canonical map into
  the completion, which is `TauCeti.Huber.coe_restrictedMvPowerSeriesCompletionEquiv_symm`.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) is the roadmap's designated prior
formalisation for this row. At commit `2baa76f742bdb4fb8ee323fabba41203bd390e08` its file
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean` states nothing about
completeness, Hausdorffness, or the completion of the restricted-series ring, so there was
nothing to port here; nothing was copied.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.49(2) and (3), for a bounded weight
  family — of which the trivial family `Tᵢ = {1}` is the case used below.
-/

public section

namespace TauCeti.Huber

open Filter

/-! ### The coefficient maps and Hausdorffness

Neither fact needs a uniformity on `A`: they hold over any nonarchimedean topological ring,
which is how `A` is fixed throughout the rest of the Huber development. -/

section Topology

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The `ν`-th coefficient map of `A⟨X⟩_T` is continuous** as soon as the weight `Tν` is
bounded: the neighbourhood subgroup `U⟨X⟩` maps into `Tν · U` coefficientwise, and boundedness
is exactly what makes `Tν · U` shrink with `U`. -/
theorem IsWeightFamily.continuous_coeff {T : Fin k → Set A} (hT : IsWeightFamily T)
    {ν : Fin k →₀ ℕ} (hb : IsBounded (weightPow T ν)) :
    Continuous fun f : weightedRestrictedSubring T hT ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) := by
  refine continuous_of_continuousAt_zero (AddMonoidHom.mk'
    (fun f : weightedRestrictedSubring T hT ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) fun _ _ ↦ by simp) ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_weightedTopology hT).tendsto_left_iff]
  intro V hV
  obtain ⟨W, hWV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  obtain ⟨N, hN, hNW⟩ := isBounded_iff.mp hb (W : Set A) (W.isOpen.mem_nhds W.zero_mem)
  obtain ⟨U, hUN⟩ := NonarchimedeanAddGroup.is_nonarchimedean N hN
  have hle : weightMul T ν U.toAddSubgroup ≤ W.toAddSubgroup :=
    weightMul_le.mpr fun t ht u hu ↦ hNW ⟨u, hUN hu, t, ht, mul_comm u t⟩
  exact ⟨U, trivial, fun f hf ↦ hWV (hle (mem_weightedNhd.mp hf ν))⟩

/-- **`A⟨X⟩_T` over a Hausdorff base is Hausdorff** (Wedhorn 5.49(2)) as soon as every weight is
bounded: the coefficient maps are then continuous, and they separate points. -/
theorem t0Space_weightedRestrictedSubring [T0Space A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) (hb : ∀ ν, IsBounded (weightPow T ν)) :
    T0Space (weightedRestrictedSubring T hT) :=
  t0Space_of_injective_of_continuous
    (f := fun f ν ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A))
    (fun _ _ h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ congrFun h ν))
    (continuous_pi fun ν ↦ hT.continuous_coeff (hb ν))

/-- The trivial weight family is bounded at every multi-index, since `Tν` is then `{1}`. This
is the whole of what the specialisations below need. -/
private theorem isBounded_weightPow_one_weight (ν : Fin k →₀ ℕ) :
    IsBounded (weightPow (fun _ : Fin k ↦ ({1} : Set A)) ν) := by
  simpa only [weightPow_one_weight] using isBounded_singleton (1 : A)

/-- At the trivial weight family the coefficient maps of `A⟨X⟩` are continuous: the
neighbourhood subgroup `U⟨X⟩` maps into `U` coefficientwise. -/
theorem continuous_coeff_one_weight (ν : Fin k →₀ ℕ) :
    Continuous fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) :=
  isWeightFamily_one_weight.continuous_coeff (isBounded_weightPow_one_weight ν)

/-- **Restricted series over a Hausdorff base are Hausdorff** (Wedhorn 5.49(2) at the trivial
weight family), the case registered as an instance. -/
instance t0Space_weightedRestrictedSubring_one_weight [T0Space A] :
    T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :=
  t0Space_weightedRestrictedSubring _ isBounded_weightPow_one_weight

/-- **A Cauchy filter on `A⟨X⟩_T` is uniformly Cauchy on each defining subgroup.** This is
Mathlib's `AddGroupFilterBasis.cauchy_iff` at the basis `weightedNhd_subgroups_basis`
registers, and it exists to name that step once: the uniformity carried by
`weightedRestrictedSubring` and the one the filter basis induces are the same structure, but
only definitionally, and the completeness proof below should not depend on that unfolding. -/
private theorem exists_mem_forall_sub_mem_weightedNhd {T : Fin k → Set A} {hT : IsWeightFamily T}
    {F : Filter (weightedRestrictedSubring T hT)} (hF : Cauchy F) (U : OpenAddSubgroup A) :
    ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ weightedNhd T hT U.toAddSubgroup :=
  ((weightedNhd_subgroups_basis hT).toRingFilterBasis.toAddGroupFilterBasis.cauchy_iff.mp hF).2 _
    ((weightedNhd_subgroups_basis hT).mem_addGroupFilterBasis U)

/-- **A Cauchy filter approaches its coefficientwise limits uniformly in the index**: for every
open subgroup `U` there is a single `F`-set on which every coefficient is already `Tν · U`-close
to its limit. The Cauchy bound holds between any two members of that set, and `Tν · U` is a
closed subgroup, so it survives the passage to the limit in the second variable. -/
private theorem exists_mem_forall_coeff_sub_mem_weightMul {T : Fin k → Set A}
    {hT : IsWeightFamily T} {F : Filter (weightedRestrictedSubring T hT)} (hF : Cauchy F)
    {a : (Fin k →₀ ℕ) → A} (ha : ∀ ν, Tendsto (fun f : weightedRestrictedSubring T hT ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) F (nhds (a ν)))
    (U : OpenAddSubgroup A) :
    ∃ M ∈ F, ∀ f ∈ M, ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) - a ν
      ∈ weightMul T ν U.toAddSubgroup := by
  have : F.NeBot := hF.1
  obtain ⟨M, hMF, hM⟩ := exists_mem_forall_sub_mem_weightedNhd hF U
  refine ⟨M, hMF, fun f hf ν ↦ ?_⟩
  have hcl : IsClosed (weightMul T ν U.toAddSubgroup : Set A) :=
    AddSubgroup.isClosed_of_isOpen _ (hT.isOpen_weightMul ν (U.isOpen.mem_nhds U.zero_mem))
  have h : a ν - MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)
      ∈ weightMul T ν U.toAddSubgroup :=
    hcl.mem_of_tendsto (Filter.Tendsto.sub (ha ν) tendsto_const_nhds)
      (Filter.eventually_of_mem hMF fun f' hf' ↦ by
        simpa using mem_weightedNhd.mp (hM f hf f' hf') ν)
  simpa using neg_mem h

end Topology

/-! ### Completeness -/

section Uniform

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A]

/-- **The `ν`-th coefficient map of `A⟨X⟩_T` is uniformly continuous** as soon as the weight
`Tν` is bounded: it is then a continuous additive group homomorphism. -/
theorem IsWeightFamily.uniformContinuous_coeff {T : Fin k → Set A} (hT : IsWeightFamily T)
    {ν : Fin k →₀ ℕ} (hb : IsBounded (weightPow T ν)) :
    UniformContinuous fun f : weightedRestrictedSubring T hT ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) :=
  uniformContinuous_addMonoidHom_of_continuous (f := AddMonoidHom.mk'
    (fun f : weightedRestrictedSubring T hT ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) fun _ _ ↦ by simp)
    (hT.continuous_coeff hb)

/-- **`A⟨X⟩_T` is complete over a complete base** when every weight is bounded. This is the step
Wedhorn 5.49(3) is proved by: a Cauchy filter is coefficientwise Cauchy, its coefficientwise
limit is again `T`-restricted, and the filter converges to it. -/
theorem completeSpace_weightedRestrictedSubring [CompleteSpace A] {T : Fin k → Set A}
    (hT : IsWeightFamily T) (hb : ∀ ν, IsBounded (weightPow T ν)) :
    CompleteSpace (weightedRestrictedSubring T hT) := by
  refine ⟨fun {F} hF ↦ ?_⟩
  choose a ha using fun ν ↦ CompleteSpace.complete (hF.map (hT.uniformContinuous_coeff (hb ν)))
  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries (Fin k) A, ∀ ν, MvPowerSeries.coeff ν g = a ν :=
    ⟨a, fun ν ↦ MvPowerSeries.coeff_apply a ν⟩
  -- The coefficientwise limit is again restricted: it is `Tν · U`-close to a restricted series.
  have hres : IsWeightedRestricted T g := by
    rw [isWeightedRestricted_iff]
    intro U
    obtain ⟨M, hMF, hM⟩ := exists_mem_forall_coeff_sub_mem_weightMul hF ha U
    obtain ⟨f₀, hf₀⟩ := hF.1.nonempty_of_mem hMF
    filter_upwards [isWeightedRestricted_iff.mp (mem_weightedRestrictedSubring.mp f₀.2) U] with ν hν
    simpa [hg] using sub_mem hν (hM f₀ hf₀ ν)
  refine ⟨⟨g, mem_weightedRestrictedSubring.mpr hres⟩, ?_⟩
  rw [← tendsto_id', ← tendsto_sub_nhds_zero_iff,
    (hasBasis_nhds_zero_weightedTopology hT).tendsto_right_iff]
  intro U _
  obtain ⟨M, hMF, hM⟩ := exists_mem_forall_coeff_sub_mem_weightMul hF ha U
  filter_upwards [hMF] with f hf
  rw [SetLike.mem_coe, mem_weightedNhd]
  intro ν
  simpa [map_sub, hg] using hM f hf ν

/-- At the trivial weight family the coefficient maps of `A⟨X⟩` are uniformly continuous:
they are continuous additive group homomorphisms. -/
theorem uniformContinuous_coeff_one_weight (ν : Fin k →₀ ℕ) :
    UniformContinuous fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) :=
  isWeightFamily_one_weight.uniformContinuous_coeff (isBounded_weightPow_one_weight ν)

/-- **The trivial-weight restricted-series subring is complete** whenever the base uniform
nonarchimedean commutative ring is complete, the case registered as an instance. -/
instance completeSpace_weightedRestrictedSubring_one_weight [CompleteSpace A] :
    CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :=
  completeSpace_weightedRestrictedSubring _ isBounded_weightPow_one_weight

end Uniform

/-! ### The comparison with `A⟨X₁,…,Xₖ⟩`

The hypotheses are completeness and Hausdorffness of the restricted-series ring itself, not
of `A`: the instances above supply them over a complete Hausdorff base, and over a discrete
base they hold because the ring is then discrete. Each declaration specializes a generic
statement about `UniformSpace.Completion.completeRingEquivSelf`. -/

section Comparison

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
    isWeightFamily_one_weight)]
  [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)]

variable (k A) in
/-- **The comparison equivalence of roadmap Layer 0.5**: when the plain restricted-series ring
is complete and Hausdorff, the completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` is that
ring. -/
noncomputable def restrictedMvPowerSeriesCompletionEquiv :
    restrictedMvPowerSeriesCompletion k A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  UniformSpace.Completion.completeRingEquivSelf _

/-- The comparison undoes the canonical inclusion: on a restricted series regarded as an element
of the completion, it returns that series. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquiv_coe
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionEquiv k A (f : restrictedMvPowerSeriesCompletion k A)
      = f :=
  UniformSpace.Completion.completeRingEquivSelf_coe _ f

/-- The inverse comparison **is** the canonical inclusion: it sends a restricted series to
itself, regarded as an element of the completion. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquiv_symm_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (restrictedMvPowerSeriesCompletionEquiv k A).symm f
      = (f : restrictedMvPowerSeriesCompletion k A) :=
  UniformSpace.Completion.completeRingEquivSelf_symm_apply _ f

/-- The inverse comparison **is** the canonical map into the completion, as a function. -/
theorem coe_restrictedMvPowerSeriesCompletionEquiv_symm :
    ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm
      = ((↑) : _ → restrictedMvPowerSeriesCompletion k A) :=
  UniformSpace.Completion.coe_completeRingEquivSelf_symm _

/-- The comparison is uniformly continuous: it is the uniform bijection between a complete
Hausdorff space and its completion. -/
theorem uniformContinuous_restrictedMvPowerSeriesCompletionEquiv :
    UniformContinuous ⇑(restrictedMvPowerSeriesCompletionEquiv k A) :=
  UniformSpace.Completion.uniformContinuous_completeRingEquivSelf _

/-- The inverse comparison is uniformly continuous: it is the canonical map into the
completion. -/
theorem uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm :
    UniformContinuous ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm :=
  UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm _

variable (k A) in
/-- **The comparison as an `A`-algebra equivalence**: the same identification, structure map
included. It is `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` rebundled, so the two
share an underlying map and the coercion lemmas for the latter apply to it. -/
noncomputable def restrictedMvPowerSeriesCompletionAlgEquiv :
    restrictedMvPowerSeriesCompletion k A ≃ₐ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  UniformSpace.Completion.completeAlgEquivSelf _ A

/-- The `A`-algebra equivalence has the same underlying map as the ring equivalence, so `simp`
normalises the algebra bundling onto the ring one. -/
@[simp]
theorem coe_restrictedMvPowerSeriesCompletionAlgEquiv :
    ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A)
      = ⇑(restrictedMvPowerSeriesCompletionEquiv k A) :=
  UniformSpace.Completion.coe_completeAlgEquivSelf _ A

/-- The inverses agree too, so the two bundlings normalise together in both directions. -/
@[simp]
theorem coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm :
    ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A).symm
      = ⇑(restrictedMvPowerSeriesCompletionEquiv k A).symm :=
  UniformSpace.Completion.coe_completeAlgEquivSelf_symm _ A

end Comparison

end TauCeti.Huber
