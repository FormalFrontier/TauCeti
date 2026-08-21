/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Mayer-Vietoris for the cohomology of a sheaf of modules on a scheme

`TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` defines the cohomology `Hⁿ(X, M)` of a sheaf of
modules on a scheme, and the cohomology `Hⁿ(U, M)` of an open subset. This file adds the long
exact Mayer-Vietoris sequence of two open subsets `U` and `V`:

`⋯ ⟶ Hⁿ(U ⊔ V, M) ⟶ Hⁿ(U, M) ⊞ Hⁿ(V, M) ⟶ Hⁿ(U ⊓ V, M) ⟶ Hⁿ⁺¹(U ⊔ V, M) ⟶ ⋯`

together with the vanishing it gives when `U` and `V` cover `X`.

## Main declarations

* `Scheme.Modules.mayerVietorisSequence` is the six-term piece of the long exact sequence,
  `Scheme.Modules.mayerVietorisSequence_def` identifies each of its objects and arrows with
  restriction maps and the connecting map `Scheme.Modules.mayerVietorisδ`, and
  `Scheme.Modules.mayerVietorisSequence_exact` is its exactness;
* `Scheme.Modules.epi_mayerVietorisδ`: if `Hⁿ⁺¹(U, M)` and `Hⁿ⁺¹(V, M)` vanish, then the
  connecting map `Hⁿ(U ⊓ V, M) ⟶ Hⁿ⁺¹(U ⊔ V, M)` is an epimorphism;
* `Scheme.Modules.subsingleton_cohomologyOn_sup_succ`: if moreover `Hⁿ(U ⊓ V, M)` vanishes,
  then `Hⁿ⁺¹(U ⊔ V, M)` vanishes; `Scheme.Modules.subsingleton_cohomology_succ` specializes
  this to `Hⁿ⁺¹(X, M)` when `U ⊔ V = ⊤`, and
  `Scheme.Modules.subsingleton_cohomology_of_two_le` applies this at degree `n - 1` under
  uniform positive-degree acyclicity hypotheses.

The last two statements are the shape in which Mayer-Vietoris is used on a curve: a separated
scheme covered by two affine opens has no cohomology above degree one in coefficients for which
the affine opens are acyclic. For quasi-coherent `M`, Serre's acyclicity of affines will supply
that input after the still-missing comparison `Sheaf.H' F i U ≅ Sheaf.H (F.over U) i` is
established. The coefficients `M : X.Modules` here are arbitrary, and the acyclicity is taken as
a hypothesis rather than proved.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: … vanishing above dimension (`H² = 0` on a curve)". No formalization is
vendored: the long exact sequence is Mathlib's
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact`, the square attached to
two open subsets is Mathlib's `TopologicalSpace.Opens.mayerVietorisSquare`, and the comparison
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

section MayerVietoris

variable (U V : Opens X)

/-- The connecting map `Hⁿ⁰(U ⊓ V, M) ⟶ Hⁿ¹(U ⊔ V, M)` of the Mayer-Vietoris sequence of two
open subsets. -/
noncomputable abbrev mayerVietorisδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyOn M n₀ (U ⊓ V) ⟶ cohomologyOn M n₁ (U ⊔ V) :=
  (Opens.mayerVietorisSquare U V).δ
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n₀ n₁ h

/-- Six consecutive terms of the Mayer-Vietoris long exact sequence of two open subsets, running
from `Hⁿ⁰(U ⊔ V, M)` to `Hⁿ¹(U ⊓ V, M)`. -/
noncomputable abbrev mayerVietorisSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (Opens.mayerVietorisSquare U V).sequence
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n₀ n₁ h

/-- Every object and every arrow of the Mayer-Vietoris sequence: the two maps to a biproduct are
the pairs of restriction maps from `U ⊔ V`, the two maps out of a biproduct are the differences of
the restriction maps to `U ⊓ V`, and the middle map is the connecting map. -/
@[simp]
lemma mayerVietorisSequence_def (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    mayerVietorisSequence M U V n₀ n₁ h =
      ComposableArrows.mk₅
        (biprod.lift (cohomologyOnRes M n₀ (le_sup_left : U ≤ U ⊔ V))
          (cohomologyOnRes M n₀ (le_sup_right : V ≤ U ⊔ V)))
        (biprod.desc (cohomologyOnRes M n₀ (inf_le_left : U ⊓ V ≤ U))
          (-cohomologyOnRes M n₀ (inf_le_right : U ⊓ V ≤ V)))
        (mayerVietorisδ M U V n₀ n₁ h)
        (biprod.lift (cohomologyOnRes M n₁ (le_sup_left : U ≤ U ⊔ V))
          (cohomologyOnRes M n₁ (le_sup_right : V ≤ U ⊔ V)))
        (biprod.desc (cohomologyOnRes M n₁ (inf_le_left : U ⊓ V ≤ U))
          (-cohomologyOnRes M n₁ (inf_le_right : U ⊓ V ≤ V))) :=
  -- This is definitional after unfolding Mathlib's `toBiprod` and `fromBiprod` together with
  -- the four structure maps of `Opens.mayerVietorisSquare`.
  rfl

/-- The Mayer-Vietoris sequence of two open subsets is exact. -/
theorem mayerVietorisSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mayerVietorisSequence M U V n₀ n₁ h).Exact :=
  (Opens.mayerVietorisSquare U V).sequence_exact _ _ _ _

/-- If the degree `n + 1` cohomology of both of two open subsets vanishes, then the Mayer-Vietoris
connecting map onto `Hⁿ⁺¹(U ⊔ V, M)` is an epimorphism. -/
theorem epi_mayerVietorisδ (n : ℕ)
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Epi (mayerVietorisδ M U V n (n + 1) rfl) :=
  TauCeti.CategoryTheory.GrothendieckTopology.MayerVietorisSquare.epi_δ
    (Opens.mayerVietorisSquare U V)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n + 1) rfl hU hV

variable {U V}

/-- If the degree `n + 1` cohomology of both of two open subsets vanishes, and their intersection
has vanishing degree `n` cohomology, then their union has vanishing degree `n + 1` cohomology. -/
theorem subsingleton_cohomologyOn_sup_succ (n : ℕ)
    (hInter : Subsingleton (cohomologyOn M n (U ⊓ V)))
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Subsingleton (cohomologyOn M (n + 1) (U ⊔ V)) :=
  TauCeti.CategoryTheory.GrothendieckTopology.MayerVietorisSquare.subsingleton_H'_X₄
    (Opens.mayerVietorisSquare U V)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n + 1) rfl hInter hU hV

/-- A scheme covered by two open subsets whose degree `n + 1` cohomology vanishes, and whose
intersection has vanishing degree `n` cohomology, has vanishing degree `n + 1` cohomology. -/
theorem subsingleton_cohomology_succ (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hInter : Subsingleton (cohomologyOn M n (U ⊓ V)))
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Subsingleton (Cohomology M (n + 1)) := by
  have hTop := subsingleton_cohomologyOn_sup_succ M n hInter hU hV
  rw [hUV] at hTop
  exact (cohomologyOnTopIso M (n + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- A scheme covered by two open subsets which, together with their intersection, are acyclic in
positive degrees has no cohomology in degrees at least two.

This is the form Mayer-Vietoris takes on a separated scheme covered by two affine opens: the
intersection is then affine as well. For quasi-coherent `M`, applying Serre's acyclicity requires
the still-missing comparison `Sheaf.H' F i U ≅ Sheaf.H (F.over U) i`; for a general
`M : X.Modules` the hypotheses have to come from elsewhere. -/
theorem subsingleton_cohomology_of_two_le (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n)
    (hU : ∀ i, 0 < i → Subsingleton (cohomologyOn M i U))
    (hV : ∀ i, 0 < i → Subsingleton (cohomologyOn M i V))
    (hInter : ∀ i, 0 < i → Subsingleton (cohomologyOn M i (U ⊓ V))) :
    Subsingleton (Cohomology M n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact subsingleton_cohomology_succ M hUV m (hInter m (by omega)) (hU _ (by omega))
    (hV _ (by omega))

end MayerVietoris

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
