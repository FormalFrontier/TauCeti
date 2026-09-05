/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Vanishing consequences of the Mayer-Vietoris sequence

For a Mayer-Vietoris square `S` in a site, where `S.X₄` is covered by `S.X₂` and `S.X₃`
meeting in `S.X₁`, Mathlib provides a long exact sequence relating the cohomology of an abelian
sheaf `F` on those four objects. This file records the two consequences that a vanishing
argument needs:

* `epi_δ`: the connecting map `Hⁿ⁰(S.X₁) ⟶ Hⁿ¹(S.X₄)` is an epimorphism as soon as the degree
  `n₁` cohomology of `F` vanishes on `S.X₂` and on `S.X₃`;
* `subsingleton_H'_X₄`: if in addition the degree `n₀` cohomology of `F` vanishes on `S.X₁`,
  then its degree `n₁` cohomology vanishes on `S.X₄`.

So the cohomology of a covered object vanishes once it vanishes on the covering objects and on
their intersection one degree lower; this is the form in which Mayer-Vietoris is applied to a
scheme covered by two open subsets.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- If the cohomology of the two side objects vanishes in degree `n₁`, then the connecting map
from degree `n₀` to degree `n₁` is an epimorphism. -/
theorem epi_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Epi (S.δ F n₀ n₁ h) := by
  have hg : S.toBiprod F n₁ = 0 :=
    ((biprod_isZero_iff _ _).2
      ⟨AddCommGrpCat.isZero_of_subsingleton _,
        AddCommGrpCat.isZero_of_subsingleton _⟩).eq_of_tgt _ _
  have hex := (S.sequence_exact F n₀ n₁ h).exact' 2 3 4
  exact hex.epi_f hg

/-- If the lower-left and the two side cohomology groups in consecutive degrees vanish, then the
upper-right cohomology group vanishes. -/
theorem subsingleton_H'_X₄ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (F.H' n₀ S.X₁))
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Subsingleton (F.H' n₁ S.X₄) := by
  have hsurj : Function.Surjective (S.δ F n₀ n₁ h) :=
    (AddCommGrpCat.epi_iff_surjective _).mp (S.epi_δ F n₀ n₁ h h₂ h₃)
  exact hsurj.subsingleton

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare
