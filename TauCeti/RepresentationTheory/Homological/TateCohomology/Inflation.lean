/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Inflation in positive-degree Tate cohomology

For a normal subgroup `S` of a finite group `G`, ordinary group cohomology has the canonical
inflation map

`H^n(G/S, M^S) ⟶ H^n(G, M)`.

In positive degrees, Mathlib identifies Tate cohomology naturally with ordinary group
cohomology. This file transports ordinary inflation across that identification. The resulting
map is natural in the coefficient representation, and the comparison square with ordinary
inflation commutes by construction.

Tate degree zero is deliberately excluded: there it is a quotient by the norm and does not carry
this naive inflation map.

## Main definitions

* `TauCeti.TateCohomology.inflNatTrans`: positive-degree Tate inflation as a natural
  transformation in the coefficients.
* `TauCeti.TateCohomology.infl`: its value on a representation.
* `TauCeti.TateCohomology.infl_comp_isoGroupCohomology_hom`: comparison with ordinary
  cohomological inflation.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Inflation in positive-degree Tate cohomology.** For a normal subgroup `S ◁ G`, this is
the natural transformation

`Ĥ^n(G/S, M^S) ⟶ Ĥ^n(G, M)`,

obtained by transporting ordinary cohomological inflation across Mathlib's natural comparison
between positive-degree Tate cohomology and group cohomology. -/
def inflNatTrans (S : Subgroup G) [S.Normal] (n : ℕ) [NeZero n] :
    Rep.quotientToInvariantsFunctor R S ⋙ tateCohomologyFunctor n ⟶
      tateCohomologyFunctor n :=
  (Functor.whiskerLeft (Rep.quotientToInvariantsFunctor R S)
      (_root_.TateCohomology.isoGroupCohomology n).hom) ≫
    groupCohomology.infNatTrans R S n ≫
      (_root_.TateCohomology.isoGroupCohomology n).inv

/-- Positive-degree Tate inflation on a coefficient representation. -/
def infl (S : Subgroup G) [S.Normal] (M : Rep R G) (n : ℕ) [NeZero n] :
    tateCohomology ((Rep.quotientToInvariantsFunctor R S).obj M) n ⟶
      tateCohomology M n :=
  (inflNatTrans S n).app M

/-- Evaluating the natural transformation of positive-degree Tate inflation gives `infl`. -/
@[simp]
theorem inflNatTrans_app (S : Subgroup G) [S.Normal] (M : Rep R G) (n : ℕ) [NeZero n] :
    (inflNatTrans S n).app M = infl S M n := by
  simp [infl]

/-- The defining expression for positive-degree Tate inflation: compare with ordinary
cohomology, inflate there, and compare back. -/
theorem infl_def (S : Subgroup G) [S.Normal] (M : Rep R G) (n : ℕ) [NeZero n] :
    infl S M n =
      (_root_.TateCohomology.isoGroupCohomology n).hom.app
          ((Rep.quotientToInvariantsFunctor R S).obj M) ≫
        (groupCohomology.infNatTrans R S n).app M ≫
          (_root_.TateCohomology.isoGroupCohomology n).inv.app M := by
  simp [infl, inflNatTrans]

/-- Positive-degree Tate inflation agrees with ordinary inflation under Mathlib's canonical
Tate-to-ordinary comparison. -/
@[reassoc]
theorem infl_comp_isoGroupCohomology_hom (S : Subgroup G) [S.Normal]
    (M : Rep R G) (n : ℕ) [NeZero n] :
    infl S M n ≫ (_root_.TateCohomology.isoGroupCohomology n).hom.app M =
      (_root_.TateCohomology.isoGroupCohomology n).hom.app
          ((Rep.quotientToInvariantsFunctor R S).obj M) ≫
        (groupCohomology.infNatTrans R S n).app M := by
  simp only [infl_def, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Positive-degree Tate inflation is natural in the coefficient representation. -/
@[reassoc]
theorem map_comp_infl (S : Subgroup G) [S.Normal] {M N : Rep R G} (f : M ⟶ N)
    (n : ℕ) [NeZero n] :
    (tateCohomologyFunctor n).map (Rep.quotientToInvariantsFunctor R S |>.map f) ≫
        infl S N n =
      infl S M n ≫ (tateCohomologyFunctor n).map f :=
  (inflNatTrans S n).naturality f

end TauCeti.TateCohomology
