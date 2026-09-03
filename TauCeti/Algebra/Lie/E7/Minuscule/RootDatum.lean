/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier

/-!
# Torus characters of the type-E7 minuscule carrier in its named root datum

`TauCeti.E7Minuscule.groupScheme` is the full-weight Chevalley carrier obtained from the
56-dimensional minuscule representation of the type-`E₇` Serre presentation. Its fourteen
numbered simple root subgroups and rank-seven split weight torus are explicit. The carrier's
conjugation equation initially describes the root character as
`DynkinType.E7.rootGeneratorWeight DynkinType.valid_E7`, hence as a Cartan-matrix row.

This file rewrites that equation against the uniform simply connected root datum used by
downstream consumers. The identities
`DynkinType.rootGeneratorWeight_inl_eq_root_simpleIndex` and
`DynkinType.rootGeneratorWeight_inr_eq_neg_root_simpleIndex` identify the character of the
`i`-th raising subgroup with

```text
(E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i)
```

and the lowering character with its negative. The results below substitute those identities into
the carrier's scheme-level conjugation equation. They therefore certify that the explicit
minuscule carrier and `DynkinType.simplyConnectedRootDatum` use the same Bourbaki numbering and
the same character lattice.

This file does not assert reductivity, maximality of the weight torus, existence of all root
subgroups, or an identification of the carrier with an independently defined algebraic group. It
packages only the named simple-root pinning equations already justified by the construction.

## Main results

* `TauCeti.E7Minuscule.weightTorus_conj_rootSubgroup_root_simpleIndex`: conjugation by the
  weight torus on a positive simple root subgroup is governed by the corresponding root of the
  uniform simply connected `E₇` datum.
* `TauCeti.E7Minuscule.weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the analogous
  equation for a negative simple root.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.

The interface follows `TauCeti/Algebra/Lie/E6/Minuscule/RootDatum.lean`, added in
[TauCetiProject/TauCeti#5278](https://github.com/TauCetiProject/TauCeti/pull/5278). The
root-character proofs consume the generic `DynkinType` identities directly, resolving the
definitional difference between `Fin 7` and `Fin DynkinType.E7.rank` locally at each rewrite.

This advances the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` consumes it: the type-`E₇` carrier must be traceable from
`ValidLieTypeIndex.dynkinType` to `DynkinType.simplyConnectedRootDatum`, with its numbered root
subgroups governed by characters of that datum.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.E7Minuscule

open DynkinType

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The torus conjugation equation at a named positive simple root.** A point `s` of the split
weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform simply
connected type-`E₇` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : E7.Valid) (i : Fin 7)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 7)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inl i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                ((E7.simplyConnectedRootDatum ht).root
                  (E7.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  have hroot : E7.rootGeneratorWeight valid_E7 (.inl i) =
      (E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i) := by
    simpa only [rank_E7] using
      E7.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A point `s` of the split
weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : E7.Valid) (i : Fin 7)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 7)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inr i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                (-(E7.simplyConnectedRootDatum ht).root
                  (E7.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  have hroot : E7.rootGeneratorWeight valid_E7 (.inr i) =
      -(E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i) := by
    simpa only [rank_E7] using
      E7.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

end TauCeti.E7Minuscule
