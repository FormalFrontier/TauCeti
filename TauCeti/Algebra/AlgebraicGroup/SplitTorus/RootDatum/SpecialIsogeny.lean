/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Special root-datum isogenies on split tori

The special isogenies of the pinned `B₂`, `G₂`, and `F₄` root data induce endomorphisms of
their split maximal tori. Their action on scheme-valued points is given by the Laurent monomials
specified by the special-isogeny matrices, and their squares are the coordinatewise power maps of
degrees two, three, and two. These are the maximal-torus restrictions of the corresponding special
isogenies of pinned reductive groups.

## Main definitions

* `TauCeti.DynkinType.b2SpecialTorusEnd`, `TauCeti.DynkinType.g2SpecialTorusEnd`, and
  `TauCeti.DynkinType.f4SpecialTorusEnd`: the split-torus morphisms prescribed by the three
  special root-datum isogenies.

## Main results

* `TauCeti.DynkinType.schemePointsMulEquiv_b2SpecialTorusEnd` and its `G₂` and `F₄`
  counterparts: the coordinate action of the special torus maps on scheme-valued points.
* `TauCeti.DynkinType.b2SpecialTorusEnd_comp_self`,
  `TauCeti.DynkinType.g2SpecialTorusEnd_comp_self`, and
  `TauCeti.DynkinType.f4SpecialTorusEnd_comp_self`: the special torus maps square to the
  characteristic power maps.
* `TauCeti.DynkinType.mapValue_frobenius_two_eq_comp_b2SpecialTorusEnd_sq` and its `G₂` and
  `F₄` counterparts: on points in the defining characteristic, these squares are Frobenius.

## References

* SGA 3, Exposés XXI–XXII.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
-/

public section

open CategoryTheory
open AlgebraicGeometry

namespace TauCeti

namespace DynkinType

/-! ### The special isogenies on split maximal tori -/

variable (R : Type) [CommRing R]

/-- The split-torus morphism prescribed by the pinned `B₂` special root-datum isogeny. -/
noncomputable def b2SpecialTorusEnd :
    SplitTorus.groupScheme R (Fin 2) ⟶ SplitTorus.groupScheme R (Fin 2) :=
  SplitTorus.ofLinearMap R b2SpecialIsogeny.weightMap

/-- The split-torus morphism prescribed by the pinned `G₂` special root-datum isogeny. -/
noncomputable def g2SpecialTorusEnd :
    SplitTorus.groupScheme R (Fin 2) ⟶ SplitTorus.groupScheme R (Fin 2) :=
  SplitTorus.ofLinearMap R g2SpecialIsogeny.weightMap

/-- The split-torus morphism prescribed by the pinned `F₄` special root-datum isogeny. -/
noncomputable def f4SpecialTorusEnd :
    SplitTorus.groupScheme R (Fin 4) ⟶ SplitTorus.groupScheme R (Fin 4) :=
  SplitTorus.ofLinearMap R f4SpecialIsogeny.weightMap

/-- On scheme-valued points, the `B₂` special torus endomorphism sends
`(x₀, x₁)` to `(x₁², x₀)`. -/
@[simp]
theorem schemePointsMulEquiv_b2SpecialTorusEnd {A : Type} [CommRing A] [Algebra R A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (Fin 2)).X) (i : Fin 2) :
    SplitTorus.schemePointsMulEquiv (R := R) (A := A)
        (p ≫ (b2SpecialTorusEnd R).hom.hom) i =
      ![SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 1 ^ (2 : ℤ),
        SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 0] i := by
  rw [b2SpecialTorusEnd, SplitTorus.schemePointsMulEquiv_ofLinearMap,
    b2SpecialIsogeny_weightMap]
  fin_cases i <;>
    simp [b2SpecialIsogenyMatrix_def]

/-- On scheme-valued points, the `G₂` special torus endomorphism sends
`(x₀, x₁)` to `(x₁, x₀³)`. -/
@[simp]
theorem schemePointsMulEquiv_g2SpecialTorusEnd {A : Type} [CommRing A] [Algebra R A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (Fin 2)).X) (i : Fin 2) :
    SplitTorus.schemePointsMulEquiv (R := R) (A := A)
        (p ≫ (g2SpecialTorusEnd R).hom.hom) i =
      ![SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 1,
        SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 0 ^ (3 : ℤ)] i := by
  rw [g2SpecialTorusEnd, SplitTorus.schemePointsMulEquiv_ofLinearMap,
    g2SpecialIsogeny_weightMap]
  fin_cases i <;>
    simp [g2SpecialIsogenyMatrix_def]

/-- On scheme-valued points, the `F₄` special torus endomorphism sends
`(x₀, x₁, x₂, x₃)` to `(x₃², x₂², x₁, x₀)`. -/
@[simp]
theorem schemePointsMulEquiv_f4SpecialTorusEnd {A : Type} [CommRing A] [Algebra R A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (Fin 4)).X) (i : Fin 4) :
    SplitTorus.schemePointsMulEquiv (R := R) (A := A)
        (p ≫ (f4SpecialTorusEnd R).hom.hom) i =
      ![SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 3 ^ (2 : ℤ),
        SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 2 ^ (2 : ℤ),
        SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 1,
        SplitTorus.schemePointsMulEquiv (R := R) (A := A) p 0] i := by
  rw [f4SpecialTorusEnd, SplitTorus.schemePointsMulEquiv_ofLinearMap,
    f4SpecialIsogeny_weightMap]
  fin_cases i <;>
    simp [f4SpecialIsogenyMatrix_def, Fin.prod_univ_succ]

/-- **The square of the `B₂` special torus endomorphism is the coordinatewise square map.** -/
@[simp]
theorem b2SpecialTorusEnd_comp_self :
    b2SpecialTorusEnd R ≫ b2SpecialTorusEnd R = SplitTorus.powEnd R (Fin 2) 2 := by
  rw [b2SpecialTorusEnd, SplitTorus.ofLinearMap_comp, SplitTorus.powEnd_def]
  congr 1
  have h := congrArg RootPairingIsogeny.weightMap b2SpecialIsogeny_mul_self
  simpa [RootPairingIsogeny.mul_def] using h

/-- **The square of the `G₂` special torus endomorphism is the coordinatewise cube map.** -/
@[simp]
theorem g2SpecialTorusEnd_comp_self :
    g2SpecialTorusEnd R ≫ g2SpecialTorusEnd R = SplitTorus.powEnd R (Fin 2) 3 := by
  rw [g2SpecialTorusEnd, SplitTorus.ofLinearMap_comp, SplitTorus.powEnd_def]
  congr 1
  have h := congrArg RootPairingIsogeny.weightMap g2SpecialIsogeny_mul_self
  simpa [RootPairingIsogeny.mul_def] using h

/-- **The square of the `F₄` special torus endomorphism is the coordinatewise square map.** -/
@[simp]
theorem f4SpecialTorusEnd_comp_self :
    f4SpecialTorusEnd R ≫ f4SpecialTorusEnd R = SplitTorus.powEnd R (Fin 4) 2 := by
  rw [f4SpecialTorusEnd, SplitTorus.ofLinearMap_comp, SplitTorus.powEnd_def]
  congr 1
  have h := congrArg RootPairingIsogeny.weightMap f4SpecialIsogeny_mul_self
  simpa [RootPairingIsogeny.mul_def] using h

/-! ### Frobenius square relations on points -/

/-- **On points in characteristic two, the square of the `B₂` special torus endomorphism is
Frobenius.** -/
theorem mapValue_frobenius_two_eq_comp_b2SpecialTorusEnd_sq
    {A : Type} [CommRing A] [ExpChar A 2]
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 2)).X) :
    (Spec.map (CommRingCat.ofHom (frobenius A 2).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q =
      q ≫ ((b2SpecialTorusEnd ℤ ≫ b2SpecialTorusEnd ℤ).hom.hom) := by
  rw [b2SpecialTorusEnd_comp_self]
  exact SplitTorus.mapValue_frobenius_eq_comp_powEnd 2 q

/-- **On points in characteristic three, the square of the `G₂` special torus endomorphism is
Frobenius.** -/
theorem mapValue_frobenius_three_eq_comp_g2SpecialTorusEnd_sq
    {A : Type} [CommRing A] [ExpChar A 3]
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 2)).X) :
    (Spec.map (CommRingCat.ofHom (frobenius A 3).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q =
      q ≫ ((g2SpecialTorusEnd ℤ ≫ g2SpecialTorusEnd ℤ).hom.hom) := by
  rw [g2SpecialTorusEnd_comp_self]
  exact SplitTorus.mapValue_frobenius_eq_comp_powEnd 3 q

/-- **On points in characteristic two, the square of the `F₄` special torus endomorphism is
Frobenius.** -/
theorem mapValue_frobenius_two_eq_comp_f4SpecialTorusEnd_sq
    {A : Type} [CommRing A] [ExpChar A 2]
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 4)).X) :
    (Spec.map (CommRingCat.ofHom (frobenius A 2).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q =
      q ≫ ((f4SpecialTorusEnd ℤ ≫ f4SpecialTorusEnd ℤ).hom.hom) := by
  rw [f4SpecialTorusEnd_comp_self]
  exact SplitTorus.mapValue_frobenius_eq_comp_powEnd 2 q

end DynkinType

end TauCeti
