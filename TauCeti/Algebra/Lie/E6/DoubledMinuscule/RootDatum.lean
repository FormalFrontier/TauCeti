/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme
public import TauCeti.Algebra.Lie.E6.Minuscule.RootDatum

/-!
# Torus characters of the doubled type E6 minuscule carrier

`TauCeti.E6DoubledMinuscule.groupScheme` and the twenty-seven-dimensional
`TauCeti.E6Minuscule.groupScheme` use the same type-`E₆` Serre generators and hence the same
numbered root characters. The smaller carrier already identifies those characters with the
Bourbaki simple roots in the uniform simply connected root datum. This file transports that
identification to the doubled carrier and rewrites its torus-conjugation equations against the
named positive and negative simple roots.

These results certify that the doubled carrier's numbered root subgroups and represented split
torus use the same character lattice and numbering as
`TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`. They do not assert reductivity, maximality of
the torus, existence of all root subgroups, or an isomorphism with an independently defined pinned
group scheme.

## Main results

* `TauCeti.E6DoubledMinuscule.rootGeneratorWeight_inl_eq_root_simpleIndex`: the raising-subgroup
  character is the corresponding simple root of the uniform simply connected datum.
* `TauCeti.E6DoubledMinuscule.rootGeneratorWeight_inr_eq_neg_root_simpleIndex`: the
  lowering-subgroup character is the negative of that simple root.
* `TauCeti.E6DoubledMinuscule.weightTorus_conj_rootSubgroup_root_simpleIndex` and
  `TauCeti.E6DoubledMinuscule.weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the doubled
  carrier's torus-conjugation equations at the named positive and negative simple roots.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The root-character identifications reuse
`TauCeti/Algebra/Lie/E6/Minuscule/RootDatum.lean`, since the character depends only on the common
Serre generators, while the conjugation wrappers specialize the doubled carrier's existing
pinning equation.

This advances the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose doubled type-`E₆` carrier must use the roots and
Bourbaki numbering of `DynkinType.simplyConnectedRootDatum`.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.E6DoubledMinuscule

open DynkinType

/-! ## The numbered subgroups sit at the named simple roots -/

/-- **The `i`-th raising subgroup sits at the `i`-th simple root of the uniform type-`E₆`
datum.** The doubled and ordinary minuscule carriers use the same representation-independent
numbered root character. -/
theorem rootGeneratorWeight_inl_eq_root_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    E6Minuscule.rootGeneratorWeight (.inl i) =
      (E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i) :=
  E6Minuscule.rootGeneratorWeight_inl_eq_root_simpleIndex ht i

/-- **The `i`-th lowering subgroup sits at the negative of the `i`-th simple root of the uniform
type-`E₆` datum.** -/
theorem rootGeneratorWeight_inr_eq_neg_root_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    E6Minuscule.rootGeneratorWeight (.inr i) =
      -(E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i) :=
  E6Minuscule.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The doubled carrier's torus conjugation equation at a named positive simple root.** A point
of the split weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `α_i(s)u`, where `α_i` belongs to the uniform simply connected
type-`E₆` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : E6.Valid) (i : Fin 6)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 6)).X)
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
                ((E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  rw [← rootGeneratorWeight_inl_eq_root_simpleIndex]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The doubled carrier's torus conjugation equation at a named negative simple root.** A point
of the split weight torus acts on the lowering subgroup through the negative simple-root
character. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : E6.Valid) (i : Fin 6)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 6)).X)
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
                (-(E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  rw [← rootGeneratorWeight_inr_eq_neg_root_simpleIndex]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

end TauCeti.E6DoubledMinuscule
