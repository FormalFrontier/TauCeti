/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# The trivial presentation: `A⟨T/1⟩` is the completion of `A`

The rational subset `R(T/1)` of `Spa (A, A⁺)` is the whole adic spectrum whenever the numerators
are sub-unit — in particular `R({1}/1) = Spa (A, A⁺)`, which is
`TauCeti.ValuationSpectrum.rationalSubset_singleton_one`. Its coordinate ring is therefore the
value the adic structure presheaf takes on *global sections*. The Tau Ceti AdicSpaces roadmap's
Layer 3.5 target identifies this value with `A` for a complete Hausdorff pair.

This file proves that, at the level of the localisation construction the presheaf is built from.
Everything rests on one computation: for numerators lying in the ring of definition, the
localisation topology at the denominator `1` is the topology `A` already carries.

```text
locSubring P T 1 A      = A₀                     the candidate ring of definition is A₀ itself
locIdealImage P T 1 A n = Iⁿ                     so the basic neighbourhoods are those of A
locTopology P T 1 A _   = ‹TopologicalSpace A›   and the two topologies agree
```

The uniformities then agree as well, so `A⟨T/1⟩` *is* the Hausdorff completion `Â` of `A`, and
when `A` is already complete and Hausdorff the structure map `A → A⟨T/1⟩` is an isomorphism of
topological rings.

## The hypothesis on the numerators

The exact subring and ideal computations ask the numerators to lie in `P.ringOfDefinition`, not
merely to be power-bounded. That is the honest hypothesis for a *fixed* pair of definition `P`: an
element of `A°` outside `A₀` enlarges `D = A₀[T]` past `A₀`, and `locSubring P T 1 A = A₀` is then
false. The topology and uniformity computations only require the numerators to be power-bounded:
adjoining a finite power-bounded family gives the same `D` and extended ideal as the localisation
construction, and the enlarged pair still induces the original topology. The universal-property
identification with `A` likewise does not change `P`.

## Main results

* `TauCeti.Huber.PairOfDefinition.hasDenominatorPower_denom_one`: at the denominator `1` the
  standing hypothesis of the construction is automatic, for every numerator set and every
  localisation.
* `TauCeti.Huber.PairOfDefinition.locSubring_denom_one` and
  `TauCeti.Huber.PairOfDefinition.locIdealImage_denom_one`: the candidate ring of definition and
  the basic neighbourhoods of zero are those of `A`.
* `TauCeti.Huber.PairOfDefinition.locTopology_denom_one`: **the localisation topology at the
  denominator `1` is the topology of `A`**, and
  `TauCeti.Huber.PairOfDefinition.locUniformSpace_denom_one` says the same of the uniformity, so
  `A⟨T/1⟩` is the Hausdorff completion of `A`.
* `TauCeti.Huber.PairOfDefinition.toCompletionLoc_denom_one_bijective` and
  `TauCeti.Huber.PairOfDefinition.toCompletionLocEquivDenomOne`: **`𝒪_X(X) ≅ A`.** For `A`
  complete and Hausdorff the structure map `A → A⟨T/1⟩` is a ring isomorphism, and
  `TauCeti.Huber.PairOfDefinition.toCompletionLocHomeomorphDenomOne` upgrades it to a
  homeomorphism, so the isomorphism is one of topological rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51
  for `A⟨T/s⟩` itself, and §8.1 for the structure presheaf whose global sections this computes.
-/

open Filter Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

namespace PairOfDefinition

variable {A : Type*} [CommRing A]

section Topological

variable [TopologicalSpace A] (P : PairOfDefinition A) (T : Finset A)

/-- **At the denominator `1` the standing hypothesis is automatic.** Every `b/1` is the image of
`b`, and the elements of `I` already lie in `A₀ ⊆ D`, so `N = 1` works — for every numerator set
and every localisation away from `1`. -/
theorem hasDenominatorPower_denom_one (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away (1 : A) S] : HasDenominatorPower P T 1 S := by
  refine (hasDenominatorPower_iff P T 1 S).mpr ⟨1, fun b _ ↦ ?_⟩
  rw [← one_mul (b : A), divBy_mul_cancel_left]
  exact algebraMap_mem_locSubring P T 1 S b.2

variable (hT : ∀ t ∈ T, t ∈ P.ringOfDefinition)

include hT

/-- **The candidate ring of definition of the trivial presentation is `A₀`.** The adjoined
fractions `t/1` are the numerators themselves, and those were assumed to lie in `A₀`. -/
@[simp]
theorem locSubring_denom_one : locSubring P T 1 A = P.ringOfDefinition := by
  refine le_antisymm ((locSubring_le_iff P T 1 A).mpr ⟨fun a ha ↦ ?_, fun t ht ↦ ?_⟩) fun a ha ↦ ?_
  · simpa using ha
  · rw [← one_mul t, divBy_mul_cancel_left]
    exact hT t ht
  · simpa using algebraMap_mem_locSubring P T 1 A ha

/-- **The basic neighbourhoods of the trivial presentation are those of `A`.** With `D = A₀` the
ideal `J = I · D` is `I` itself, so the `n`-th neighbourhood of zero is the image of `Iⁿ`. -/
@[simp]
theorem locIdealImage_denom_one (n : ℕ) : locIdealImage P T 1 A n = P.idealImage n := by
  have hle : locSubring P T 1 A ≤ P.ringOfDefinition := (locSubring_denom_one P T hT).le
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨d, hd, rfl⟩ := (mem_locIdealImage_iff P T 1 A n).mp hx
    clear hx
    rw [locIdeal_pow_eq_span] at hd
    induction hd using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact (P.mem_idealImage n).mpr ⟨b, hb, (toLocSubring_apply P T 1 A b).symm⟩
    | zero => simp
    | add y z _ _ hy hz => simpa using (P.idealImage n).add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, MulMemClass.coe_mul]
      exact P.mul_mem_idealImage (hle r.2) hy
  · obtain ⟨y, hy, rfl⟩ := (P.mem_idealImage n).mp hx
    simpa using algebraMap_mem_locIdealImage P T 1 A hy

end Topological

section Topological

variable [TopologicalSpace A] (P : PairOfDefinition A) (T : Finset A)

private theorem locSubring_denom_one_powerBounded [IsTopologicalRing A]
    (hTpb : ∀ t ∈ T, IsPowerBounded t) :
    locSubring P T 1 A = (P.adjoin T hTpb).ringOfDefinition := by
  rw [adjoin_ringOfDefinition]
  refine le_antisymm ((locSubring_le_iff P T 1 A).mpr
    ⟨fun a ha ↦ ?_, fun t ht ↦ ?_⟩) ?_
  · simpa using P.le_adjoin T hTpb ha
  · rw [← one_mul t, divBy_mul_cancel_left]
    simpa using P.mem_adjoin_of_mem T hTpb ht
  · rw [Subring.closure_le]
    rintro a (ha | ha)
    · simpa using algebraMap_mem_locSubring P T 1 A ha
    · have ht := divBy_mem_locSubring P T 1 A ha
      rw [← one_mul a, divBy_mul_cancel_left] at ht
      exact ht

private noncomputable def locSubringEquivAdjoin [IsTopologicalRing A]
    (hTpb : ∀ t ∈ T, IsPowerBounded t) :
    locSubring P T 1 A ≃+* (P.adjoin T hTpb).ringOfDefinition :=
  RingEquiv.subringCongr (locSubring_denom_one_powerBounded P T hTpb)

private theorem locIdeal_map_denom_one_powerBounded [IsTopologicalRing A]
    (hTpb : ∀ t ∈ T, IsPowerBounded t) :
    Ideal.map (locSubringEquivAdjoin P T hTpb).toRingHom (locIdeal P T 1 A) =
      (P.adjoin T hTpb).idealOfDefinition := by
  rw [locIdeal_def, Ideal.map_map, adjoin_idealOfDefinition]
  congr 1
  ext x
  exact toLocSubring_apply P T 1 A x

private theorem locIdealImage_denom_one_powerBounded [IsTopologicalRing A]
    (hTpb : ∀ t ∈ T, IsPowerBounded t) (n : ℕ) :
    locIdealImage P T 1 A n = (P.adjoin T hTpb).idealImage n := by
  ext x
  rw [mem_locIdealImage_iff, (P.adjoin T hTpb).mem_idealImage]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨locSubringEquivAdjoin P T hTpb d, ?_, rfl⟩
    have hd' : locSubringEquivAdjoin P T hTpb d ∈
        Ideal.map (locSubringEquivAdjoin P T hTpb).toRingHom (locIdeal P T 1 A ^ n) :=
      Ideal.mem_map_of_mem _ hd
    rwa [Ideal.map_pow, locIdeal_map_denom_one_powerBounded P T hTpb] at hd'
  · rintro ⟨q, hq, rfl⟩
    have hq' : q ∈
        Ideal.map (locSubringEquivAdjoin P T hTpb).toRingHom (locIdeal P T 1 A ^ n) := by
      rwa [Ideal.map_pow, locIdeal_map_denom_one_powerBounded P T hTpb]
    obtain ⟨d, hd, hed⟩ := (Ideal.mem_map_iff_of_surjective _
      (locSubringEquivAdjoin P T hTpb).surjective).mp hq'
    exact ⟨d, hd, congrArg Subtype.val hed⟩

/-- **The localisation topology at the denominator `1` is the topology of `A`.**

The localisation's basic neighbourhoods are the ideal images for the pair obtained by adjoining
the power-bounded numerators to `P`. That pair still defines the topology of `A`, so the two ring
topologies are equal. -/
@[simp]
theorem locTopology_denom_one [IsTopologicalRing A]
    (hTpb : ∀ t ∈ T, IsPowerBounded t) :
    locTopology P T 1 A (hasDenominatorPower_denom_one P T A) = ‹TopologicalSpace A› := by
  have hbasis : (@nhds A (locTopology P T 1 A (hasDenominatorPower_denom_one P T A)) 0).HasBasis
      (fun _ : ℕ ↦ True) fun n ↦ ((P.adjoin T hTpb).idealImage n : Set A) := by
    simpa only [locIdealImage_denom_one_powerBounded P T hTpb] using
      hasBasis_nhds_zero_locTopology P T 1 A (hasDenominatorPower_denom_one P T A)
  have hgroup := @IsTopologicalRing.to_topologicalAddGroup A _
    (locTopology P T 1 A (hasDenominatorPower_denom_one P T A))
    (isTopologicalRing_locTopology P T 1 A (hasDenominatorPower_denom_one P T A))
  exact IsTopologicalAddGroup.ext hgroup inferInstance
    (hbasis.eq_of_same_basis (P.adjoin T hTpb).hasBasis_nhds_zero)

end Topological

section Uniform

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] (P : PairOfDefinition A)
  (T : Finset A) (hTpb : ∀ t ∈ T, IsPowerBounded t)

include hTpb

/-- **The uniformity of the trivial presentation is the uniformity of `A`.** Both are the right
uniformity of one and the same topological group topology, by `locTopology_denom_one` and
`IsUniformAddGroup.rightUniformSpace_eq`.

This is what makes `A⟨T/1⟩` *equal to*, and not merely isomorphic to, the Hausdorff completion
`Â` of `A`: the completion is formed from the uniformity, and the two uniformities agree. -/
@[simp]
theorem locUniformSpace_denom_one :
    locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A) = ‹UniformSpace A› := by
  have hloc := @IsUniformAddGroup.rightUniformSpace_eq A
    (locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)) _
    (isUniformAddGroup_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A))
  have hamb := @IsUniformAddGroup.rightUniformSpace_eq A ‹UniformSpace A› _ ‹IsUniformAddGroup A›
  refine hloc.symm.trans (Eq.trans ?_ hamb)
  congr 1
  · rw [locUniformSpace_toTopologicalSpace]
    exact locTopology_denom_one P T hTpb
  · exact proof_irrel_heq _ _

end Uniform

section CompleteSeparated

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
  (P : PairOfDefinition A) (T : Finset A) (hTpb : ∀ t ∈ T, IsPowerBounded t)

include hTpb

/-- **The retraction `A⟨T/1⟩ → A`.** `A` is itself a complete Hausdorff target for which `1` is a
unit and every fraction `t/1 = t` is power-bounded, so the identity of `A` extends across the
completed localisation: this is the universal property of `A⟨T/s⟩` at `s = 1`.

Only its existence is recorded; `toCompletionLocEquivDenomOne` is what a consumer uses. -/
private theorem exists_retraction_denom_one :
    letI := isUniformAddGroup_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
    letI := isTopologicalRing_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
    ∃ g : @UniformSpace.Completion A
        (locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)) →+* A,
      Continuous g ∧
        g.comp (toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)) = RingHom.id A := by
  have := P.toNonarchimedeanRing
  have hs : IsUnit ((RingHom.id A) 1) := by simp
  have hunit : ((hs.unit⁻¹ : Aˣ) : A) = 1 := by simp
  obtain ⟨g, hg, -⟩ := existsUnique_continuous_ringHom_completion_locTopology P T 1 A
    (hasDenominatorPower_denom_one P T A) (φ := RingHom.id A)
    (by simpa using continuousAt_id (x := (0 : A))) hs fun t ht ↦ by
      rw [hunit, mul_one]
      exact hTpb t ht
  exact ⟨g, hg⟩

/-- The retraction is a left inverse of the structure map: that is the equation the universal
property produced. -/
private theorem retraction_toCompletionLoc_denom_one (a : A) :
    (exists_retraction_denom_one P T hTpb).choose
      (toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A) a) = a :=
  congrArg (fun k : A →+* A ↦ k a) (exists_retraction_denom_one P T hTpb).choose_spec.2

/-- The retraction is a right inverse as well: the composite in the other order is a continuous
endomorphism of `A⟨T/1⟩` fixing the structure map, and `eq_id_of_comp_toCompletionLoc_eq_self`
says the identity is the only one. -/
private theorem toCompletionLoc_retraction_denom_one
    (x : @UniformSpace.Completion A
      (locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A))) :
    toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)
      ((exists_retraction_denom_one P T hTpb).choose x) = x := by
  have hspec := (exists_retraction_denom_one P T hTpb).choose_spec
  have hcomp : ((toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)).comp
        (exists_retraction_denom_one P T hTpb).choose).comp
      (toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)) =
      toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A) := by
    rw [RingHom.comp_assoc, hspec.2, RingHom.comp_id]
  have hid := eq_id_of_comp_toCompletionLoc_eq_self P T 1 A
    (hasDenominatorPower_denom_one P T A) _
    ((continuous_toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)).comp
      hspec.1) hcomp
  exact congrArg (fun k ↦ k x) hid

/-- **The structure map of the trivial presentation is bijective.** -/
theorem toCompletionLoc_denom_one_bijective :
    Function.Bijective (toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)) :=
  ⟨Function.LeftInverse.injective (retraction_toCompletionLoc_denom_one P T hTpb),
    fun x ↦ ⟨_, toCompletionLoc_retraction_denom_one P T hTpb x⟩⟩

/-- **`𝒪_X(X) ≅ A`.** For a complete Hausdorff `A` the structure map `A → A⟨T/1⟩` of the trivial
presentation is a ring isomorphism, giving the global-sections identification targeted by Layer
3.5 of the Tau Ceti AdicSpaces roadmap.

The proof is the universal property, not the topology computation above. `A` is itself a complete
Hausdorff target through which the identity factors, and `A⟨T/1⟩` admits at most one continuous
endomorphism over `A`, so the retraction obtained is a two-sided inverse of the structure map. -/
noncomputable def toCompletionLocEquivDenomOne :
    letI := isUniformAddGroup_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
    letI := isTopologicalRing_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
    A ≃+* @UniformSpace.Completion A
      (locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)) :=
  letI := isUniformAddGroup_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
  letI := isTopologicalRing_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
  { toFun := toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)
    invFun := (exists_retraction_denom_one P T hTpb).choose
    left_inv := retraction_toCompletionLoc_denom_one P T hTpb
    right_inv := toCompletionLoc_retraction_denom_one P T hTpb
    map_mul' := map_mul _
    map_add' := map_add _ }

/-- The isomorphism is the structure map. -/
@[simp]
theorem toCompletionLocEquivDenomOne_apply (a : A) :
    letI := isUniformAddGroup_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
    letI := isTopologicalRing_locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)
    toCompletionLocEquivDenomOne P T hTpb a =
      toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A) a := (rfl)

/-- **`𝒪_X(X) ≅ A` as topological rings.** The ring isomorphism of
`toCompletionLocEquivDenomOne` is a homeomorphism for `A`'s own topology: the structure map is
continuous by `continuous_toCompletionLoc`, and its inverse is the retraction, which the universal
property produced continuous. -/
noncomputable def toCompletionLocHomeomorphDenomOne :
    A ≃ₜ @UniformSpace.Completion A
      (locUniformSpace P T 1 A (hasDenominatorPower_denom_one P T A)) where
  toFun := toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)
  invFun := (exists_retraction_denom_one P T hTpb).choose
  left_inv := retraction_toCompletionLoc_denom_one P T hTpb
  right_inv := toCompletionLoc_retraction_denom_one P T hTpb
  continuous_toFun := continuous_toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A)
  continuous_invFun := (exists_retraction_denom_one P T hTpb).choose_spec.1

/-- The homeomorphism is the structure map. -/
@[simp]
theorem toCompletionLocHomeomorphDenomOne_apply (a : A) :
    toCompletionLocHomeomorphDenomOne P T hTpb a =
      toCompletionLoc P T 1 A (hasDenominatorPower_denom_one P T A) a := (rfl)

end CompleteSeparated

end PairOfDefinition

end

end TauCeti.Huber
