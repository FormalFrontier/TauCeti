/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Opposite
public import TauCeti.CategoryTheory.Exact.Split
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

/-!
# Bicartesian squares in exact categories

A pushout of an inflation in an exact category is also a pullback.  Dually, a pullback of a
deflation is also a pushout.  Thus the base-change squares supplied by Quillen's E2 and E2op
axioms are bicartesian.

The proof uses the standard biproduct criterion for a commutative square.  For a square

```text
W --f--> X
|        |
g        h
v        v
Y --i--> Z,
```

Mathlib identifies the pushout property with `Z` being the cokernel in the sequence

```text
W --(f,-g)--> X ⊞ Y --(h,i)--> Z.
```

When `f` is an inflation, `(f,-g)` is an inflation as well: it factors as the split graph
inclusion `(1,-g)` followed by `f ⊞ 1`.  Its distinguished cokernel is uniquely isomorphic to
the pushout cokernel, so the displayed sequence is a conflation.  Its kernel property is exactly
the pullback property.  The statement for deflations follows by passing to the opposite exact
category.

## Main results

* `TauCeti.ExactStructure.conflation_shortComplex_of_isPushout_of_isInflation` packages a
  pushout of an inflation as its associated conflation.
* `TauCeti.ExactStructure.isPullback_of_isPushout_of_isInflation` proves that such a pushout is
  also a pullback.
* `TauCeti.ExactStructure.isPushout_of_isPullback_of_isDeflation` is the dual statement.
* `TauCeti.ExactStructure.bicartesianSq_of_isPushout_of_isInflation` and
  `TauCeti.ExactStructure.bicartesianSq_of_isPullback_of_isDeflation` bundle the conclusions as
  `CategoryTheory.BicartesianSq`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Proposition 2.12.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The elementary triangular automorphism sending the graph of `-g` to the first biproduct
inclusion. -/
private noncomputable def graphIso {W Y : C} (g : W ⟶ Y) : W ⊞ Y ≅ W ⊞ Y where
  hom := biprod.desc (biprod.inl + g ≫ biprod.inr) biprod.inr
  inv := biprod.desc (biprod.inl - g ≫ biprod.inr) biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp

/-- The graph map `(1, -g) : W ⟶ W ⊞ Y` is an inflation in every exact structure. -/
private theorem isInflation_graph (E : ExactStructure C) {W Y : C} (g : W ⟶ Y) :
    E.IsInflation (biprod.lift (𝟙 W) (-g)) := by
  apply E.isInflation_of_split_isInflation
  rw [split_isInflation_iff]
  exact ⟨Y, graphIso g, by simp [graphIso]⟩

/-- For a commutative square whose top map is an inflation, the first map `(f,-g)` of the
associated biproduct short complex is again an inflation. -/
private theorem isInflation_shortComplex_f (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hf : E.IsInflation f) : E.IsInflation sq.shortComplex.f := by
  have hgraph : E.IsInflation (biprod.lift (𝟙 W) (-g)) := isInflation_graph E g
  have hsum : E.IsInflation (biprod.map f (𝟙 Y)) := E.isInflation_biprod_id hf Y
  have hfac : biprod.lift (𝟙 W) (-g) ≫ biprod.map f (𝟙 Y) =
      biprod.lift f (-g) := by
    apply biprod.hom_ext <;> simp
  -- Rewriting cannot key through the unexposed `IsInflation` abbreviation.
  change E.inflations (biprod.lift f (-g))
  rw [← hfac]
  exact E.isInflation_comp _ _ hgraph hsum

/-- The sign change on the second summand of a binary biproduct. -/
private noncomputable def biprodSignIso (X Y : C) : X ⊞ Y ≅ X ⊞ Y where
  hom := biprod.map (𝟙 X) (-𝟙 Y)
  inv := biprod.map (𝟙 X) (-𝟙 Y)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- Changing the sign of the lower-left map converts the cokernel convention for a square into
the kernel convention. -/
private noncomputable def shortComplexIso
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) : sq.shortComplex ≅ sq.shortComplex' :=
  ShortComplex.isoMk (Iso.refl _) (biprodSignIso X Y) (Iso.refl _)
    (by
      dsimp [CommSq.shortComplex, CommSq.shortComplex', biprodSignIso]
      apply biprod.hom_ext <;> simp [Category.assoc])
    (by
      dsimp [CommSq.shortComplex, CommSq.shortComplex', biprodSignIso]
      apply biprod.hom_ext' <;> simp)

/-- The biproduct short complex associated to a pushout square of an inflation is a
conflation.

Its maps are `(f,-g) : W ⟶ X ⊞ Y` and `(h,i) : X ⊞ Y ⟶ Z`.  This is the
kernel--cokernel sequence underlying the bicartesian-square criterion. -/
theorem conflation_shortComplex_of_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    E.Conflation hsq.toCommSq.shortComplex := by
  let sq := hsq.toCommSq
  have hfirst : E.IsInflation sq.shortComplex.f := E.isInflation_shortComplex_f sq hf
  obtain ⟨Q, q, hq, hT⟩ :=
    (ConflationClass.isInflation_iff E.toConflationClass sq.shortComplex.f).mp hfirst
  let T := ShortComplex.mk sq.shortComplex.f q hq
  have hT' : E.Conflation T := by simpa [T] using hT
  have hpairT : IsKernelCokernelPair T := E.isKernelCokernelPair T hT'
  have hpushoutCokernel : IsColimit sq.cokernelCofork := hsq.isColimitCokernelCofork
  let e : Q ≅ Z :=
    IsColimit.coconePointUniqueUpToIso hpairT.gIsCokernel hpushoutCokernel
  have he : q ≫ e.hom = sq.shortComplex.g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hpairT.gIsCokernel hpushoutCokernel
      WalkingParallelPair.one
  exact E.conflation_of_iso (S := T) (T := sq.shortComplex)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by dsimp [T]; rw [Category.id_comp, Category.comp_id])
      (by dsimp [T]; rw [Category.id_comp]; exact he.symm)) hT'

/-- **A pushout square of an inflation in an exact category is a pullback square.** -/
theorem isPullback_of_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    IsPullback f g h i := by
  let sq := hsq.toCommSq
  have hconflation := E.conflation_shortComplex_of_isPushout_of_isInflation hf hsq
  have hpair := E.isKernelCokernelPair sq.shortComplex hconflation
  have hpair' : IsKernelCokernelPair sq.shortComplex' :=
    hpair.of_iso (shortComplexIso sq)
  exact IsPullback.of_isLimit' sq
    (sq.isLimitEquivIsLimitKernelFork.symm hpair'.fIsKernel)

/-- A pushout square of an inflation, bundled as a bicartesian square. -/
theorem bicartesianSq_of_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.of_isPullback_isPushout
    (E.isPullback_of_isPushout_of_isInflation hf hsq) hsq

/-- **A pullback square of a deflation in an exact category is a pushout square.** -/
theorem isPushout_of_isPullback_of_isDeflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hh : E.IsDeflation h) (hsq : IsPullback f g h i) :
    IsPushout f g h i := by
  have hop : IsPushout h.op i.op f.op g.op := hsq.op.flip
  have hhop : E.op.IsInflation h.op := by simpa using hh
  have hpull : IsPullback h.op i.op f.op g.op :=
    E.op.isPullback_of_isPushout_of_isInflation hhop hop
  simpa using hpull.unop.flip

/-- A pullback square of a deflation, bundled as a bicartesian square. -/
theorem bicartesianSq_of_isPullback_of_isDeflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hh : E.IsDeflation h) (hsq : IsPullback f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.of_isPullback_isPushout hsq
    (E.isPushout_of_isPullback_of_isDeflation hh hsq)

end ExactStructure

end TauCeti
