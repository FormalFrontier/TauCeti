/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange

/-!
# Isogenies of abelian varieties

An isogeny of abelian varieties is a homomorphism whose underlying scheme morphism is finite and
surjective. This definition works over an arbitrary field: it does not impose separability, so it
includes inseparable isogenies in positive characteristic.

Rather than duplicate Mathlib's two scheme-morphism properties, `AbelianVariety.isogenies K` is
their infimum pulled back along `AbelianVariety.Hom.toSchemeFunctor`. Consequently identities,
composites, and morphisms isomorphic to isogenies are handled by Mathlib's generic
`MorphismProperty` API. The abbreviation `AbelianVariety.IsIsogeny f` gives the usual predicate on
a homomorphism.

## Main results

* `AbelianVariety.IsIsogeny.comp` composes isogenies;
* `AbelianVariety.IsIsogeny.baseChange` shows that an isogeny remains one after extending the
  ground field;
* `AbelianVariety.isIsogeny_mulBy_neg_one` supplies the multiplication-by-negative-one isogeny.

This is the property-level prerequisite for `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E,
item "`[n]` as an isogeny". The general theorem for nonzero `n` requires the later torsion theory
and is not asserted here. No external formalization is vendored. The definition and closure proofs
reuse Mathlib's `AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Surjective` morphism properties,
including their stability under composition, isomorphism, and base change.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- The morphism property of being an isogeny of abelian varieties over `K`: the underlying
scheme morphism is finite and surjective. -/
def isogenies (K : Type u) [Field K] : MorphismProperty (AbelianVariety K) :=
  (@IsFinite ⊓ @Surjective : MorphismProperty Scheme).inverseImage Hom.toSchemeFunctor

/-- A homomorphism of abelian varieties is an isogeny if its underlying scheme morphism is finite
and surjective. -/
abbrev IsIsogeny {A B : AbelianVariety K} (f : A ⟶ B) : Prop :=
  isogenies K f

/-- A homomorphism is an isogeny exactly when its underlying scheme morphism is finite and
surjective. -/
@[simp]
lemma isIsogeny_iff {A B : AbelianVariety K} (f : A ⟶ B) :
    IsIsogeny f ↔ IsFinite (Hom.toSchemeHom f) ∧ Surjective (Hom.toSchemeHom f) :=
  by
    letI : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme) :=
      MorphismProperty.respectsIso_of_isStableUnderComposition
        (fun _ _ g (_ : IsIso g) ↦ inferInstance)
    have hcancel (P : MorphismProperty Scheme) [P.RespectsIso] :
        P (eqToHom (Hom.toSchemeFunctor_obj A) ≫ Hom.toSchemeHom f ≫
          eqToHom (Hom.toSchemeFunctor_obj B).symm) ↔ P (Hom.toSchemeHom f) := by
      rw [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
    change
      (IsFinite ((Hom.toSchemeFunctor (K := K)).map f) ∧
        Surjective ((Hom.toSchemeFunctor (K := K)).map f)) ↔ _
    rw [Hom.toSchemeFunctor_map]
    exact and_congr (hcancel @IsFinite) (hcancel @Surjective)

/-- Isogenies contain identities and are stable under composition. -/
instance : (isogenies K).IsMultiplicative := by
  unfold isogenies
  letI : (@IsFinite ⊓ @Surjective : MorphismProperty Scheme).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf
  infer_instance

/-- Being an isogeny is invariant under isomorphisms of arrows. -/
instance : (isogenies K).RespectsIso := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro A B f _
  -- Expose the mapped arrow so the scheme-level isomorphism instances close both conjuncts.
  change IsFinite ((Hom.toSchemeFunctor (K := K)).map f) ∧
    Surjective ((Hom.toSchemeFunctor (K := K)).map f)
  constructor <;> infer_instance

/-- The identity homomorphism is an isogeny. -/
lemma isIsogeny_id (A : AbelianVariety K) : IsIsogeny (𝟙 A) :=
  (isogenies K).id_mem A

/-- Every isomorphism of abelian varieties is an isogeny. -/
lemma isIsogeny_of_isIso {A B : AbelianVariety K} (f : A ⟶ B) [IsIso f] : IsIsogeny f :=
  (isogenies K).of_isIso f

namespace IsIsogeny

variable {A B C : AbelianVariety K} {f : A ⟶ B} {g : B ⟶ C}

/-- The underlying scheme morphism of an isogeny is finite. -/
lemma isFinite (hf : IsIsogeny f) : IsFinite (Hom.toSchemeHom f) :=
  (isIsogeny_iff f).mp hf |>.1

/-- The underlying scheme morphism of an isogeny is surjective. -/
lemma surjective (hf : IsIsogeny f) : Surjective (Hom.toSchemeHom f) :=
  (isIsogeny_iff f).mp hf |>.2

/-- A composite of isogenies is an isogeny. -/
lemma comp (hf : IsIsogeny f) (hg : IsIsogeny g) : IsIsogeny (f ≫ g) :=
  (isogenies K).comp_mem f g hf hg

/-- A scheme-morphism property stable under base change holds for the underlying morphism of a
base-changed abelian-variety homomorphism. -/
private lemma baseChange_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange] [P.IsMultiplicative] (hf : P (Hom.toSchemeHom f))
    (L : Type u) [Field L] [Algebra K L] :
    P (Hom.toSchemeHom (Hom.baseChange f L)) := by
  rw [Hom.toSchemeHom_baseChange]
  simp only [Over.comp_left, Over.eqToHom_left]
  apply P.comp_mem
  · exact P.of_isIso _
  · apply P.comp_mem
    · exact P.overPullbackMap _ _ hf
    · exact P.of_isIso _

/-- Extending the ground field preserves isogenies. -/
lemma baseChange (hf : IsIsogeny f) (L : Type u) [Field L] [Algebra K L] :
    IsIsogeny (Hom.baseChange f L) := by
  rw [isIsogeny_iff] at hf ⊢
  exact ⟨baseChange_property @IsFinite hf.1 L, baseChange_property @Surjective hf.2 L⟩

end IsIsogeny

/-! ### A multiplication isogeny -/

/-- Multiplication by negative one is an isogeny. -/
lemma isIsogeny_mulBy_neg_one (A : AbelianVariety K) : IsIsogeny (mulBy A (-1)) := by
  have hsq : mulBy A (-1) ≫ mulBy A (-1) = 𝟙 A := by
    simpa using (mulBy_mul A (-1) (-1)).symm
  letI : IsIso (mulBy A (-1)) := IsIso.mk ⟨mulBy A (-1), hsq, hsq⟩
  exact isIsogeny_of_isIso _

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
