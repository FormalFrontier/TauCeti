/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic
public import TauCeti.Topology.Category.TopCommRingCat.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Limits of complete separated topological rings

Roadmap Layer 3.2's second half: the full subcategory
`TauCeti.CompleteSeparatedTopCommRingCat` has products and equalizers, and the inclusion into
`TopCommRingCat` creates them. Both come from the closure instances proved here:
`CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits` supplies the limits, and
`CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion` their creation by the
inclusion. The equalizer closure is where separatedness of the codomain is used: the
equalizing locus is closed in a Hausdorff codomain, and a closed subring of a complete
separated ring is complete separated (`IsCompleteSeparated.of_isClosedEmbedding`, in
`CompleteSeparated/Basic.lean`).

## Main results

* `HasLimits CompleteSeparatedTopCommRingCat`: all small limits, obtained from the products and
  equalizers below through `has_limits_of_hasEqualizers_and_products`.
* The `IsClosedUnderLimitsOfShape` instances for discrete shapes and parallel pairs. These are
  what the inclusion needs in order to create the limits, so
  `TauCeti.CompleteSeparatedTopCommRingCat` acquires products and equalizers, and its inclusion
  acquires `CreatesLimitsOfShape` for both shapes, by synthesis alone — as the `example`s below
  record.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1 — the structure presheaf of §8.1 takes values
  in complete separated topological rings, and the sheaf condition of §8.2 is an equalizer of a
  pair of maps between products in that category, so both shapes are needed there.
-/

public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.TopCommRingCat

/-- Complete separated objects are closed under products in `TopCommRingCat`. -/
instance {β : Type v} :
    (isCompleteSeparated.{max u v}).IsClosedUnderLimitsOfShape (Discrete β) :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact ObjectProperty.prop_of_iso _
      (IsLimit.conePointsIsoOfNatIso (piFanIsLimit fun b ↦ F.obj ⟨b⟩) (limit.isLimit F)
        Discrete.natIsoFunctor.symm)
      ((isCompleteSeparated_iff _).mpr (IsCompleteSeparated.pi (f := fun b ↦ F.obj ⟨b⟩)
        fun b ↦ (isCompleteSeparated_iff _).mp (hF ⟨b⟩))))

/-- Complete separated objects are closed under equalizers: the equalizing locus of two
morphisms into a Hausdorff codomain is a closed subring. -/
instance : (isCompleteSeparated.{u}).IsClosedUnderLimitsOfShape WalkingParallelPair :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    set f := F.map WalkingParallelPairHom.left
    set g := F.map WalkingParallelPairHom.right
    have : T2Space (F.obj .one) := ((isCompleteSeparated_iff _).mp (hF .one)).t2Space
    have hcl : IsClosed (RingHom.eqLocus f.val g.val : Set (F.obj .zero)) := by
      have hset : ((RingHom.eqLocus f.val g.val : Subring _) : Set (F.obj .zero)) =
          {x | f.val x = g.val x} := Set.ext fun _ ↦ RingHom.mem_eqLocus
      rw [hset]
      exact isClosed_eq f.2 g.2
    -- `equalizerFork` is `Fork.ofι` on `(RingHom.eqLocus f.val g.val).subtype`, so the
    -- underlying function of its `ι` is `Subtype.val`. Name that reduction here rather than
    -- letting the definitional equality carry the closed embedding silently.
    have hι : ⇑((equalizerFork f g).ι) =
        ((↑) : ↥(RingHom.eqLocus f.val g.val) → F.obj .zero) := rfl
    exact ObjectProperty.prop_of_iso _
      (IsLimit.conePointsIsoOfNatIso (equalizerForkIsLimit f g) (limit.isLimit F)
        (diagramIsoParallelPair F).symm)
      ((isCompleteSeparated_iff _).mpr (IsCompleteSeparated.of_isClosedEmbedding
        (equalizerFork f g).ι (hι ▸ hcl.isClosedEmbedding_subtypeVal)
        ((isCompleteSeparated_iff _).mp (hF .zero)))))

end TauCeti.TopCommRingCat

namespace TauCeti.CompleteSeparatedTopCommRingCat

-- Neither the limits nor their creation needs an instance of its own: both follow from the
-- closure instances above by synthesis alone, through
-- `hasLimitsOfShape_of_closedUnderLimits` and `createsLimitsOfShapeFullSubcategoryInclusion`
-- respectively. These `example`s pin that down, so that losing either would break the build.
example : HasProducts.{v} CompleteSeparatedTopCommRingCat.{max u v} := inferInstance

example : HasEqualizers CompleteSeparatedTopCommRingCat.{u} := inferInstance

noncomputable example {β : Type v} :
    CreatesLimitsOfShape (Discrete β) (TopCommRingCat.isCompleteSeparated.{max u v}).ι :=
  inferInstance

noncomputable example :
    CreatesLimitsOfShape WalkingParallelPair (TopCommRingCat.isCompleteSeparated.{u}).ι :=
  inferInstance

/-- **All small limits**, from the products and equalizers above. This is what lets a limit be
formed over a general shape rather than only over discrete shapes and parallel pairs; the
structure presheaf of an adic space is a limit over a category of rational presentations, which
is neither. -/
noncomputable instance : HasLimits CompleteSeparatedTopCommRingCat.{u} :=
  has_limits_of_hasEqualizers_and_products

end TauCeti.CompleteSeparatedTopCommRingCat
