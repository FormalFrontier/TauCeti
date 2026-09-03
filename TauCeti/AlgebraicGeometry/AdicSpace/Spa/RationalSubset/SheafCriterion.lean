/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.CategoryTheory.Sites.TopologicalBasis

/-!
# Sheaves on `Spa(A,A⁺)` are detected on rational covers

Rational subsets form a basis of `Spa(A,A⁺)` (`isTopologicalBasis_spaRationalFamily`), and a
presheaf on a space is a sheaf exactly when it is a sheaf for covers by basis elements
(`isSheaf_iff_isSheafFor_basisCoverage_comp`). Putting the two together, sheafhood on the adic
spectrum is decided by the rational covers alone.

This is the fourth bullet of roadmap Layer 3.5, instantiated at the basis the roadmap names. It is
stated for an arbitrary presheaf, so it does not mention the structure presheaf; applying it to
`𝒪_X` is what turns the definition of sheafiness into Wedhorn's rational-cover condition.

## Main results

* `TauCeti.ValuationSpectrum.isSheaf_iff_isSheafFor_rationalCover` : the criterion.

The rational basis itself, in the `Opens` form this consumes, is
`TauCeti.ValuationSpectrum.isBasis_spaRationalOpens` in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.3 for rational subsets and
  §8.1–§8.2 for the sheaf condition on them.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory _root_.TopologicalSpace TauCeti.Huber TauCeti.TopologicalSpace.Opens

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Sheafhood on `Spa(A,A⁺)` is decided by rational covers.** A presheaf valued in any category
is a sheaf for the topology of the adic spectrum exactly when it satisfies the sheaf condition for
every cover of an open by rational subsets.

Nothing here is specific to the structure presheaf: the statement quantifies over presheaves, and
`𝒪_X` is one instance. -/
theorem isSheaf_iff_isSheafFor_rationalCover [IsHuberRing A] (Aplus : Subring A) {C : Type*}
    [Category C] (P : (Opens ↥(spa Aplus))ᵒᵖ ⥤ C) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus)) P ↔
      ∀ (E : C) ⦃U : Opens ↥(spa Aplus)⦄ (R : Presieve U),
        IsBasisCover (spaRationalOpens Aplus) R →
        Presieve.IsSheafFor (P ⋙ coyoneda.obj (Opposite.op E)) R :=
  isSheaf_iff_isSheafFor_basisCoverage_comp (isBasis_spaRationalOpens Aplus) P

end

end TauCeti.ValuationSpectrum
