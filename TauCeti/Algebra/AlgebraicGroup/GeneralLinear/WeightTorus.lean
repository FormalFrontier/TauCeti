/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus

/-!
# Weight tori in the general linear group scheme

Let `wt : Fin N → κ → ℤ` be a finite family of characters of the split torus `𝔾ₘ^κ`. Each
character gives a diagonal entry, and together they define a group-scheme morphism

```text
𝔾ₘ^κ → GL_N,     s ↦ diag(∏_j s_j ^ wt(i,j)).
```

This file constructs the morphism by factoring it through the diagonal torus of `GL_N`. On
character lattices, the factorization is the homomorphism sending the `i`-th coordinate character
to `wt i`; contravariance of diagonalizable groups gives the required map of split tori. The
scheme-valued point formula then follows from the existing point comparisons for diagonalizable
groups and the diagonal torus.

The construction is the scheme-level realization of `TauCeti.basisWeightTorus`. In particular,
when `wt` is the weight function of a finite free admissible lattice, it supplies the split-torus
morphism in the pinned Chevalley--Demazure construction of Layer 9 of the ReductiveGroups roadmap.
No faithfulness is asserted: an arbitrary weight family may have a common kernel.

## Main declarations

* `TauCeti.GeneralLinear.weightCharacterMap`: the homomorphism on character lattices.
* `TauCeti.GeneralLinear.weightTorus`: the represented morphism `𝔾ₘ^κ → GL_N`.
* `TauCeti.GeneralLinear.schemePointsMulEquiv_weightTorus`: its diagonal matrix on
  scheme-valued points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.GeneralLinear

universe u

variable {R κ : Type u} [CommRing R] {N : ℕ}

section Construction

variable [Finite κ]

/-- The character-lattice map associated to a family of weights. It sends the standard
character at `i : Fin N` to the finitely supported function corresponding to `wt i`.

Contravariance turns this map into a morphism from the rank-`κ` split torus to the rank-`N`
diagonal torus. -/
noncomputable def weightCharacterMap (wt : Fin N → κ → ℤ) :
    Multiplicative (ULift.{u} (Fin N) →₀ ℤ) →*
      Multiplicative (κ →₀ ℤ) :=
  AddMonoidHom.toMultiplicative
    (Finsupp.linearCombination ℤ fun i : ULift.{u} (Fin N) =>
      Finsupp.equivFunOnFinite.symm (wt i.down)).toAddMonoidHom

/-- The weight character-lattice map takes a standard character to the corresponding weight. -/
@[simp]
theorem weightCharacterMap_ofAdd_single (wt : Fin N → κ → ℤ) (i : Fin N) :
    weightCharacterMap wt
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) =
      Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i)) := by
  apply congrArg Multiplicative.ofAdd
  simp

/-- The group-scheme morphism from a split torus to `GL_N` prescribed by a family of weights.
It factors through the diagonal torus: the `i`-th diagonal entry is the character `wt i`. -/
noncomputable def weightTorus (wt : Fin N → κ → ℤ) :
    SplitTorus.groupScheme R κ ⟶ groupScheme R N :=
  DiagonalizableGroup.groupSchemeMap R
      (FGCommGrpCat.ofHom (weightCharacterMap wt)) ≫
    diagonalTorus

private theorem weightTorus_hom (wt : Fin N → κ → ℤ) :
    (weightTorus (R := R) wt).hom.hom =
      (DiagonalizableGroup.groupSchemeMap R
          (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom.hom ≫
        diagonalTorus.hom.hom :=
  rfl

end Construction

variable [Fintype κ]
variable {A : Type u} [CommRing A] [Algebra R A]

/-- On scheme-valued points, the weight torus is the diagonal matrix whose `i`-th diagonal entry
is the value of the character `wt i`. -/
@[simp]
theorem schemePointsMulEquiv_weightTorus (wt : Fin N → κ → ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R κ).X) :
    schemePointsMulEquiv N A (p ≫ (weightTorus (R := R) wt).hom.hom) =
      diagGL (fun i => torusCharacter
        (SplitTorus.schemePointsMulEquiv (R := R) (A := A) p) (wt i)) := by
  rw [weightTorus_hom, ← Category.assoc]
  rw [schemePointsMulEquiv_diagonalTorus]
  congr 1
  funext i
  rw [diagonalTorusCoordinates_apply]
  let chi := DiagonalizableGroup.schemePointsMulEquiv
    (R := R) (A := A) (SplitTorus.characterGroup κ) p
  have hcoordinate :
      SplitTorus.schemePointsMulEquiv (R := R) (A := A)
          (p ≫ (DiagonalizableGroup.groupSchemeMap R
            (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom.hom) (ULift.up i) =
        chi (weightCharacterMap wt
          (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1))) := by
    calc
      _ = DiagonalizableGroup.schemePointsMulEquiv
          (R := R) (A := A) (SplitTorus.characterGroup (ULift.{u} (Fin N)))
            (p ≫ (DiagonalizableGroup.groupSchemeMap R
              (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom.hom)
              (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1) :
                SplitTorus.characterGroup (ULift.{u} (Fin N))) := by
        apply Units.ext
        rw [SplitTorus.schemePointsMulEquiv_apply_coe]
        exact (DiagonalizableGroup.schemePointsMulEquiv_apply_coe
          (R := R) (A := A) (SplitTorus.characterGroup (ULift.{u} (Fin N))) _ _).symm
      _ = _ := by
        rw [DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap]
        rfl
  rw [hcoordinate, weightCharacterMap_ofAdd_single]
  let m := Finsupp.equivFunOnFinite.symm (wt i)
  calc
    chi (Multiplicative.ofAdd m) =
        DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
          (R := R) (A := A)
            (p ≫ (SplitTorus.characterGroupSchemeMap (R := R) m).hom.hom) := by
      rw [SplitTorus.characterGroupSchemeMap_def]
      exact (DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap
          (R := R) (A := A) (SplitTorus.characterGroup κ)
            (Multiplicative.ofAdd m) p).symm
    _ = m.prod fun j n =>
        SplitTorus.schemePointsMulEquiv (R := R) (A := A) p j ^ n :=
      SplitTorus.multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap m p
    _ = ∏ j, SplitTorus.schemePointsMulEquiv (R := R) (A := A) p j ^ wt i j := by
      rw [Finsupp.prod_fintype _ _ (fun _ => zpow_zero _)]
      simp only [m, Finsupp.equivFunOnFinite_symm_apply_apply]
    _ = torusCharacter
        (SplitTorus.schemePointsMulEquiv (R := R) (A := A) p) (wt i) := by
      rw [torusCharacter_def]

end TauCeti.GeneralLinear
