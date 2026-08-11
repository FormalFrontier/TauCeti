/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Mayer-Vietoris for the cohomology of a sheaf of modules on a scheme

`TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` defines the cohomology `Hⁿ(X, M)` of a sheaf of
modules on a scheme, and the cohomology `Hⁿ(U, M)` of an open subset. This file adds the long
exact Mayer-Vietoris sequence of a covering of `X` by two open subsets `U` and `V`:

`⋯ ⟶ Hⁿ(X, M) ⟶ Hⁿ(U, M) ⊞ Hⁿ(V, M) ⟶ Hⁿ(U ⊓ V, M) ⟶ Hⁿ⁺¹(X, M) ⟶ ⋯`

## Main declarations

* `Scheme.Modules.mayerVietorisCoverSquare` is the Mayer-Vietoris square of a covering of `X` by
  two opens, `Scheme.Modules.mayerVietorisSequence` is the six-term piece of the resulting long
  exact sequence, `Scheme.Modules.mayerVietorisSequence_eq` identifies each of its objects and
  arrows with restriction maps and the connecting map `Scheme.Modules.mayerVietorisδ`, and
  `Scheme.Modules.mayerVietorisSequence_exact` is its exactness;
* `Scheme.Modules.epi_mayerVietorisδ`: if `Hⁿ⁺¹(U, M)` and `Hⁿ⁺¹(V, M)` vanish, then the
  connecting map `Hⁿ(U ⊓ V, M) ⟶ Hⁿ⁺¹(X, M)` is an epimorphism;
* `Scheme.Modules.subsingleton_cohomology_succ`: if moreover `Hⁿ(U ⊓ V, M)` vanishes, then
  `Hⁿ⁺¹(X, M)` vanishes, and `Scheme.Modules.subsingleton_cohomology_of_two_le` applies this at
  degree `n - 1` under uniform positive-degree acyclicity hypotheses.

The last two statements are the shape in which Mayer-Vietoris is used on a curve: a separated
scheme covered by two affine opens has no cohomology above degree one, once the acyclicity of
affines is available. That acyclicity is not proved here.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: … vanishing above dimension (`H² = 0` on a curve)". No formalization is
vendored: the long exact sequence is Mathlib's
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact`, the square attached to
two open subsets is Mathlib's `TopologicalSpace.Opens.mayerVietorisSquare'`, and the comparison
between the cohomology of the terminal open subset and the cohomology of the site comes from
`TauCeti/CategoryTheory/Sites/SheafCohomology/Terminal.lean` through
`Scheme.Modules.cohomologyOnTopIso`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

section Cover

variable {U V : Opens X} (hUV : U ⊔ V = ⊤)

/-- The Mayer-Vietoris square of a covering of a scheme by two open subsets. Its corners are
`U ⊓ V`, `U`, `V` and the whole space, as recorded by `mayerVietorisCoverSquare_X₁` and friends. -/
def mayerVietorisCoverSquare : (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := U ⊓ V, X₂ := U, X₃ := V, X₄ := ⊤
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ }
    hUV.symm rfl

-- The four corner lemmas hold by definition. Their proofs are written `(rfl)` rather than `rfl`
-- so that they are checked as ordinary proofs rather than as exported definitional unfoldings,
-- which lets `mayerVietorisCoverSquare` keep its body private.
@[simp] lemma mayerVietorisCoverSquare_X₁ : (mayerVietorisCoverSquare hUV).X₁ = U ⊓ V := (rfl)

@[simp] lemma mayerVietorisCoverSquare_X₂ : (mayerVietorisCoverSquare hUV).X₂ = U := (rfl)

@[simp] lemma mayerVietorisCoverSquare_X₃ : (mayerVietorisCoverSquare hUV).X₃ = V := (rfl)

@[simp] lemma mayerVietorisCoverSquare_X₄ : (mayerVietorisCoverSquare hUV).X₄ = ⊤ := (rfl)

/-- The connecting map `Hⁿ⁰(U ⊓ V, M) ⟶ Hⁿ¹(X, M)` of the Mayer-Vietoris sequence. -/
def mayerVietorisδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyOn M n₀ (U ⊓ V) ⟶ cohomologyOn M n₁ ⊤ :=
  (mayerVietorisCoverSquare hUV).δ ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n₀ n₁ h

/-- Six consecutive terms of the Mayer-Vietoris long exact sequence, running from `Hⁿ⁰(X, M)` to
`Hⁿ¹(U ⊓ V, M)`. -/
def mayerVietorisSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : ComposableArrows AddCommGrpCat.{u} 5 :=
  (mayerVietorisCoverSquare hUV).sequence
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n₀ n₁ h

/-- Every object and every arrow of the Mayer-Vietoris sequence: the two maps to a biproduct are
the pairs of restriction maps from `X`, the two maps out of a biproduct are the differences of the
restriction maps to `U ⊓ V`, and the middle map is the connecting map. -/
@[simp]
lemma mayerVietorisSequence_eq (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    mayerVietorisSequence M hUV n₀ n₁ h =
      ComposableArrows.mk₅
        (biprod.lift (cohomologyOnRes M n₀ (le_top : U ≤ ⊤))
          (cohomologyOnRes M n₀ (le_top : V ≤ ⊤)))
        (biprod.desc (cohomologyOnRes M n₀ (inf_le_left : U ⊓ V ≤ U))
          (-cohomologyOnRes M n₀ (inf_le_right : U ⊓ V ≤ V)))
        (mayerVietorisδ M hUV n₀ n₁ h)
        (biprod.lift (cohomologyOnRes M n₁ (le_top : U ≤ ⊤))
          (cohomologyOnRes M n₁ (le_top : V ≤ ⊤)))
        (biprod.desc (cohomologyOnRes M n₁ (inf_le_left : U ⊓ V ≤ U))
          (-cohomologyOnRes M n₁ (inf_le_right : U ⊓ V ≤ V))) :=
  (rfl)

/-- The Mayer-Vietoris sequence of a covering by two open subsets is exact. -/
theorem mayerVietorisSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mayerVietorisSequence M hUV n₀ n₁ h).Exact :=
  (mayerVietorisCoverSquare hUV).sequence_exact _ _ _ _

include hUV in
/-- If the degree `n + 1` cohomology of both members of a two-element open cover vanishes, then
the Mayer-Vietoris connecting map onto `Hⁿ⁺¹(X, M)` is an epimorphism. -/
theorem epi_mayerVietorisδ (n : ℕ)
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Epi (mayerVietorisδ M hUV n (n + 1) rfl) := by
  set F := (_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M
  set S := mayerVietorisCoverSquare hUV
  -- both components of the map to the biproduct land in a zero object
  have hg : S.toBiprod F (n + 1) = 0 := by
    refine biprod.hom_ext _ _ ?_ ?_
    · exact (AddCommGrpCat.isZero_of_subsingleton (G := cohomologyOn M (n + 1) U)).eq_of_tgt _ _
    · exact (AddCommGrpCat.isZero_of_subsingleton (G := cohomologyOn M (n + 1) V)).eq_of_tgt _ _
  -- the piece of the Mayer-Vietoris sequence around `Hⁿ⁺¹(X, M)`
  have hex : (ShortComplex.mk (S.δ F n (n + 1) rfl) (S.toBiprod F (n + 1))
      (S.δ_toBiprod _ _ _ _)).Exact :=
    (mayerVietorisSequence_exact M hUV n (n + 1) rfl).exact' 2 3 4
  exact hex.epi_f hg

include hUV in
/-- A scheme covered by two open subsets whose degree `n + 1` cohomology vanishes, and whose
intersection has vanishing degree `n` cohomology, has vanishing degree `n + 1` cohomology. -/
theorem subsingleton_cohomology_succ (n : ℕ)
    (hInter : Subsingleton (cohomologyOn M n (U ⊓ V)))
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Subsingleton (Cohomology M (n + 1)) := by
  have hsurj : Function.Surjective (mayerVietorisδ M hUV n (n + 1) rfl) :=
    (AddCommGrpCat.epi_iff_surjective _).mp (epi_mayerVietorisδ M hUV n hU hV)
  have hTop : Subsingleton (cohomologyOn M (n + 1) ⊤) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    exact congrArg _ (hInter.elim x y)
  exact (cohomologyOnTopIso M (n + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

include hUV in
/-- A scheme covered by two open subsets which, together with their intersection, are acyclic in
positive degrees has no cohomology in degrees at least two.

This is the form Mayer-Vietoris takes on a separated scheme covered by two affine opens: the
intersection is then affine as well, and Serre's acyclicity of affines supplies the hypotheses. -/
theorem subsingleton_cohomology_of_two_le (n : ℕ) (hn : 2 ≤ n)
    (hU : ∀ i, 0 < i → Subsingleton (cohomologyOn M i U))
    (hV : ∀ i, 0 < i → Subsingleton (cohomologyOn M i V))
    (hInter : ∀ i, 0 < i → Subsingleton (cohomologyOn M i (U ⊓ V))) :
    Subsingleton (Cohomology M n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact subsingleton_cohomology_succ M hUV m (hInter m (by omega)) (hU _ (by omega))
    (hV _ (by omega))

end Cover

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
