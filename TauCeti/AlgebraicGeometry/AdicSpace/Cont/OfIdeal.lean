/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal.Basic
public import TauCeti.RingTheory.Huber.Basic
import TauCeti.RingTheory.Huber.Continuous.OfCofinal
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Continuous points in `Spv (A, I)`: Wedhorn's Theorem 7.10 and Corollary 7.12

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.10 and Corollary 7.12.**

Theorem 7.10 identifies `Cont A` inside `Spv (A, IA)` for a pair of definition `(A₀, I)`, as the
locus where additionally `v(a) < 1` for every `a ∈ I`. This file proves the two conjuncts of the
inclusion — a continuous point lies in `Spv (A, IA)`, and it is sub-unit on the ideal of
definition — then the converse, and assembles the identification
`cont_eq_spvOfIdeal_inter_setOfPred_forall_vlt_one`. Corollary 7.12 follows: the sub-unit
condition is closed in `Spv A`, so `Cont A` is a closed subset of the subspace `Spv (A, IA)`.

For the inclusion, the argument needs no estimate and no pair of definition either. Membership in
`Spv (A, I)` is `cΓ_v(I) = Γ_v`, which by Lemma 7.4 follows from cofinality of `v` at every
element of a *spanning set*; and continuity turns topological nilpotence into cofinality. So the
hypothesis that carries the proof is exactly "spanned by topologically nilpotent elements", which
is what `mem_spvOfIdeal_of_span_of_isTopologicallyNilpotent_of_isContinuous` below assumes — and
of an ideal with the same radical as `I`, since `cΓ_v(I)` sees `I` only through its radical. The
extended ideal of a pair of definition is the case at hand, since the image of `I` spans `IA` and
its elements are topologically nilpotent.

Passing through a spanning set is essential, not a convenience. A general element of `IA` is a sum
`Σ xᵢ aᵢ` with `xᵢ ∈ I` and `aᵢ ∈ A` arbitrary, and such a sum need not be topologically
nilpotent — the nilpotence is a property of the generators, not of the ideal they generate.

## Main results

* `TauCeti.ValuationSpectrum.mem_spvOfIdeal_of_span_of_isTopologicallyNilpotent_of_isContinuous`
  : a continuous point lies in `Spv (A, I)` whenever some ideal with the same radical as `I` is
  spanned by topologically nilpotent elements.
* `TauCeti.ValuationSpectrum.mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous` and
  `TauCeti.ValuationSpectrum.cont_subset_spvOfIdeal_extendedIdealOfDefinition` : its reading at a
  pair of definition, in membership and subset form.
* `TauCeti.ValuationSpectrum.not_vle_one_of_isContinuous_of_mem_idealOfDefinition` : the other
  conjunct of the inclusion `⊆` — a continuous point is sub-unit on the ideal of definition.
* `TauCeti.ValuationSpectrum.isContinuous_of_mem_spvOfIdeal_of_forall_vlt_one` : the converse.
  Lemma 7.4 reads membership as cofinality on `IA` or a full characteristic group, and either
  branch feeds the cofinality engine
  `TauCeti.Huber.PairOfDefinition.isContinuous_of_forall_cofinalValue`.
* `TauCeti.ValuationSpectrum.cont_eq_spvOfIdeal_inter_setOfPred_forall_vlt_one` : **Theorem 7.10**,
  the resulting identification of `Cont A` inside `Spv (A, IA)`.
* `TauCeti.ValuationSpectrum.isClosed_val_preimage_cont` : **Corollary 7.12**, `Cont A` is a
  closed subset of `Spv (A, IA)`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Theorem 7.10, Corollary 7.12, and Lemma 7.4.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **A continuous point lies in `Spv (A, I)` when some ideal with the same radical is spanned by
topologically nilpotent elements.** This is the membership conjunct of the inclusion half of
Wedhorn Theorem 7.10: continuity makes the value at a topologically nilpotent element cofinal,
and Lemma 7.4 only ever asks for cofinality on a spanning set.

`cΓ_v(I)` depends on `I` only through its radical, so the spanning set need not generate `I`
itself — any `J` with `I.radical = J.radical` will do. The spanning set is not assumed finite and
no pair of definition appears; both enter only in the specialisation below. -/
theorem mem_spvOfIdeal_of_span_of_isTopologicallyNilpotent_of_isContinuous {I J : Ideal A}
    (hfg : ∃ K : Ideal A, K.FG ∧ I.radical = K.radical) {T : Set A} (hspan : Ideal.span T = J)
    (hrad : I.radical = J.radical) (hnil : ∀ t ∈ T, IsTopologicallyNilpotent t) {v : Spv A}
    (hv : v.IsContinuous) : v ∈ spvOfIdeal I hfg := by
  rw [mem_spvOfIdeal_iff]
  refine (characteristicSubgroupOfIdeal_eq_top_iff_forall_span (v := v.valuation) hfg hspan
    hrad).mpr (Or.inl fun t ht ↦ ?_)
  exact ((isContinuous_def _).mp hv).cofinalValue_of_isTopologicallyNilpotent (hnil t ht)

/-- **Wedhorn Theorem 7.10, the inclusion `Cont A ⊆ Spv (A, IA)`.** A continuous point of the
valuation spectrum of a Huber ring lies in `Spv (A, IA)` for the extended ideal of definition of
any pair of definition.

No finite-generation witness is asked of the caller: `IA` is finitely generated by
`TauCeti.Huber.PairOfDefinition.fg_extendedIdealOfDefinition`, so the canonical one is supplied
here. -/
theorem mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous (P : PairOfDefinition A)
    {v : Spv A} (hv : v.IsContinuous) :
    v ∈ spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ := by
  refine mem_spvOfIdeal_of_span_of_isTopologicallyNilpotent_of_isContinuous _
    (T := Subtype.val '' (P.idealOfDefinition : Set P.ringOfDefinition)) ?_ rfl ?_ hv
  · rw [P.extendedIdealOfDefinition_def, Ideal.map, Subring.coe_subtype]
  · rintro _ ⟨a, ha, rfl⟩
    exact P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha

/-- **Wedhorn Theorem 7.10, the inclusion `Cont A ⊆ Spv (A, IA)`**, as an inclusion of subsets. -/
theorem cont_subset_spvOfIdeal_extendedIdealOfDefinition (P : PairOfDefinition A) :
    cont A ⊆ spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ :=
  fun _ hv ↦
    mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous P ((mem_cont_iff _).mp hv)

omit [IsTopologicalRing A] in
/-- **A continuous point is sub-unit on the ideal of definition** — the other conjunct of
Wedhorn Theorem 7.10's inclusion `⊆`, beside the membership
`mem_spvOfIdeal_extendedIdealOfDefinition_of_isContinuous` above. An element of the ideal of
definition is topologically nilpotent, and a continuous valuation takes a value `< 1` at a
topologically nilpotent element. -/
theorem not_vle_one_of_isContinuous_of_mem_idealOfDefinition (P : PairOfDefinition A)
    {v : Spv A} (hv : v.IsContinuous) {a : P.ringOfDefinition}
    (ha : a ∈ P.idealOfDefinition) :
    ¬ v.toValuativeRel.vle 1 (a : A) := by
  have hlt : v.valuation (a : A) < 1 :=
    ((isContinuous_def v).mp hv).lt_one_of_isTopologicallyNilpotent
      (P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha)
  exact (valuation_lt_iff v (a : A) 1).mp (by simpa using hlt)

/-- **Wedhorn Theorem 7.10, the converse inclusion.** A point of `Spv (A, IA)` that is sub-unit
on the ideal of definition is continuous.

The sub-unit hypothesis quantifies over the ideal of definition `I` itself — through the
subring inclusion — and not over the extension `IA`. The `IA`-form would be the stronger
demand (the extension contains the image of `I` among much else), and it is not what Theorem
7.10's right-hand side supplies. -/
theorem isContinuous_of_mem_spvOfIdeal_of_forall_vlt_one (P : PairOfDefinition A) {v : Spv A}
    (hmem : v ∈ spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩)
    (h1 : ∀ a ∈ P.idealOfDefinition, v.toValuativeRel.vlt ((a : P.ringOfDefinition) : A) 1) :
    v.IsContinuous := by
  have hlt : ∀ a ∈ P.idealOfDefinition, v.valuation ((a : P.ringOfDefinition) : A) < 1 :=
    fun a ha ↦ not_le.mp fun hle ↦ h1 a ha ((valuation_le_iff v 1 _).mp (by simpa using hle))
  obtain ⟨s, hs⟩ := P.fg_idealOfDefinition
  rw [isContinuous_def]
  refine P.isContinuous_of_forall_cofinalValue v.valuation hs (fun a ha ↦ (hlt a ha).le) ?_
  rcases mem_spvOfIdeal_iff_forall_cofinalValue_or_characteristicSubgroup_eq_top.mp hmem
    with hcof | htop
  · refine fun t ht ↦ hcof _ ?_
    rw [P.extendedIdealOfDefinition_def]
    exact Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span ht)
  · exact fun t ht ↦ P.cofinalValue_of_hasFullCharacteristicGroup v.valuation
      (hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top.mpr htop) hlt
      (hs ▸ Ideal.subset_span ht)

/-- **Wedhorn Theorem 7.10.** The continuous points of the valuation spectrum of a Huber ring
are exactly the points of `Spv (A, IA)` that are sub-unit on the ideal of definition. -/
theorem cont_eq_spvOfIdeal_inter_setOfPred_forall_vlt_one (P : PairOfDefinition A) :
    cont A = spvOfIdeal P.extendedIdealOfDefinition
        ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ ∩
      {v : Spv A | ∀ a ∈ P.idealOfDefinition,
        v.toValuativeRel.vlt ((a : P.ringOfDefinition) : A) 1} := by
  ext v
  constructor
  · intro hv
    exact ⟨cont_subset_spvOfIdeal_extendedIdealOfDefinition P hv, fun a ha ↦
      not_vle_one_of_isContinuous_of_mem_idealOfDefinition P ((mem_cont_iff v).mp hv) ha⟩
  · rintro ⟨hmem, h1⟩
    exact (mem_cont_iff v).mpr (isContinuous_of_mem_spvOfIdeal_of_forall_vlt_one P hmem h1)

/-- **Wedhorn Corollary 7.12.** `Cont A` is a closed subset of `Spv (A, IA)`: by Theorem 7.10
its trace on the subspace is the sub-unit locus of the ideal of definition, which is closed
already in `Spv A`. -/
theorem isClosed_val_preimage_cont (P : PairOfDefinition A) :
    IsClosed (Subtype.val ⁻¹' cont A : Set (spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩)) := by
  rw [cont_eq_spvOfIdeal_inter_setOfPred_forall_vlt_one P, Set.preimage_inter,
    Subtype.coe_preimage_self, Set.univ_inter]
  have h : {v : Spv A | ∀ a ∈ P.idealOfDefinition,
      v.toValuativeRel.vlt ((a : P.ringOfDefinition) : A) 1}
      = {v : Spv A | ∀ b ∈ ((↑) : P.ringOfDefinition → A) ''
          (P.idealOfDefinition : Set P.ringOfDefinition), v.toValuativeRel.vlt b 1} := by
    ext v
    simp
  rw [h]
  exact (isClosed_setOfPred_forall_vlt_one _).preimage continuous_subtype_val

end TauCeti.ValuationSpectrum

end
