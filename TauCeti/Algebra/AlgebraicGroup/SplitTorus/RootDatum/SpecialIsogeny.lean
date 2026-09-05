/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Special root-datum isogenies on split tori

An integral linear map between coordinate character lattices induces, contravariantly, a
morphism of the corresponding split tori. This file builds that bridge and applies it to the
special isogenies of the pinned `B₂`, `G₂`, and `F₄` root data. These are the torus
components prescribed for the eventual group-scheme isogenies, and they square to the
coordinatewise power maps of degrees two, three, and two.

This is the maximal-torus restriction required by the Layer 9 target "Special isogenies in
characteristics two and three" of `TauCetiRoadmap/ReductiveGroups/README.md`. The full target
still requires extensions to the pinned reductive group schemes and formulas on their root
subgroups.

## Main definitions

* `TauCeti.SplitTorus.characterMapOfLinearMap`: the homomorphism of character groups induced by
  an integral linear map between coordinate lattices.
* `TauCeti.SplitTorus.ofLinearMap`: the resulting contravariant morphism of split tori.
* `TauCeti.SplitTorus.powEnd`: the coordinatewise integer power endomorphism of a split torus.
* `TauCeti.DynkinType.b2SpecialTorusEnd`, `TauCeti.DynkinType.g2SpecialTorusEnd`, and
  `TauCeti.DynkinType.f4SpecialTorusEnd`: the split-torus morphisms prescribed by the three
  special root-datum isogenies.

## Main results

* `TauCeti.SplitTorus.schemePointsMulEquiv_ofLinearMap`: the induced map on points is the Laurent
  monomial specified by the image of a basis character.
* `TauCeti.SplitTorus.schemePointsMulEquiv_powEnd`: `powEnd n` raises every coordinate to `n`.
* `TauCeti.DynkinType.b2SpecialTorusEnd_comp_self`,
  `TauCeti.DynkinType.g2SpecialTorusEnd_comp_self`, and
  `TauCeti.DynkinType.f4SpecialTorusEnd_comp_self`: the special torus maps square to the
  characteristic power maps.

## References

* SGA 3, Exposés XXI–XXII.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
-/

public section

open CategoryTheory
open AlgebraicGeometry

namespace TauCeti

universe u

namespace SplitTorus

variable {R A sigma tau upsilon : Type u} [CommRing R] [CommRing A]
variable [Algebra R A] [Finite sigma] [Finite tau] [Finite upsilon]

/-- Convert an integral linear map between finite coordinate lattices into the corresponding
homomorphism of free multiplicative character groups. -/
noncomputable def characterMapOfLinearMap (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    Multiplicative (sigma →₀ ℤ) →* Multiplicative (tau →₀ ℤ) :=
  AddMonoidHom.toMultiplicative
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ tau).symm.toLinearMap.comp
      (f.comp (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma).toLinearMap)).toAddMonoidHom

/-- The additive representative of `characterMapOfLinearMap f` is obtained by transporting
`f` across the finite-support/function equivalence. -/
@[simp]
theorem characterMapOfLinearMap_ofAdd (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ))
    (x : sigma →₀ ℤ) :
    characterMapOfLinearMap f (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd
        ((Finsupp.linearEquivFunOnFinite ℤ ℤ tau).symm
          (f (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma x))) := by
  rfl

/-- The character-group map associated to a composite integral linear map is the composite of
the character-group maps. -/
@[simp]
theorem characterMapOfLinearMap_comp (g : (tau → ℤ) →ₗ[ℤ] (upsilon → ℤ))
    (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    (characterMapOfLinearMap g).comp (characterMapOfLinearMap f) =
      characterMapOfLinearMap (g ∘ₗ f) := by
  apply MonoidHom.ext
  intro x
  change Multiplicative.ofAdd
      ((Finsupp.linearEquivFunOnFinite ℤ ℤ upsilon).symm
        (g (Finsupp.linearEquivFunOnFinite ℤ ℤ tau
          ((Finsupp.linearEquivFunOnFinite ℤ ℤ tau).symm
            (f (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma x.toAdd)))))) =
    Multiplicative.ofAdd
      ((Finsupp.linearEquivFunOnFinite ℤ ℤ upsilon).symm
        (g (f (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma x.toAdd))))
  rw [LinearEquiv.apply_symm_apply]

/-- The identity linear map induces the identity character-group map. -/
@[simp]
theorem characterMapOfLinearMap_id :
    characterMapOfLinearMap (LinearMap.id : (sigma → ℤ) →ₗ[ℤ] (sigma → ℤ)) =
      MonoidHom.id _ := by
  ext x
  simp

/-- The character-group morphism associated to an integral linear map between finite coordinate
lattices. -/
noncomputable def characterGroupMapOfLinearMap (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    characterGroup sigma ⟶ characterGroup tau :=
  FGCommGrpCat.ofHom (characterMapOfLinearMap f)

/-- The underlying monoid homomorphism of `characterGroupMapOfLinearMap`. -/
@[simp]
theorem toMonoidHom_characterGroupMapOfLinearMap
    (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    FGCommGrpCat.toMonoidHom (characterGroupMapOfLinearMap f) =
      characterMapOfLinearMap f := by
  rfl

/-- Composition of linear maps becomes composition of the associated character-group
morphisms. -/
@[simp]
theorem characterGroupMapOfLinearMap_comp
    (g : (tau → ℤ) →ₗ[ℤ] (upsilon → ℤ))
    (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    characterGroupMapOfLinearMap f ≫ characterGroupMapOfLinearMap g =
      characterGroupMapOfLinearMap (g ∘ₗ f) := by
  apply FGCommGrpCat.hom_ext
  rw [FGCommGrpCat.toMonoidHom_comp,
    toMonoidHom_characterGroupMapOfLinearMap,
    toMonoidHom_characterGroupMapOfLinearMap,
    toMonoidHom_characterGroupMapOfLinearMap,
    characterMapOfLinearMap_comp]

/-- The identity linear map induces the identity character-group morphism. -/
@[simp]
theorem characterGroupMapOfLinearMap_id :
    characterGroupMapOfLinearMap
      (LinearMap.id : (sigma → ℤ) →ₗ[ℤ] (sigma → ℤ)) = 𝟙 _ := by
  apply FGCommGrpCat.hom_ext
  simp

/-- **The contravariant split-torus morphism induced by an integral map of coordinate character
lattices.** If `f : X⁺(T_sigma) → X⁺(T_tau)`, then `ofLinearMap R f` is the corresponding
morphism `T_tau → T_sigma`. -/
noncomputable def ofLinearMap (R : Type u) [CommRing R]
    (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    groupScheme R tau ⟶ groupScheme R sigma :=
  DiagonalizableGroup.groupSchemeMap R (characterGroupMapOfLinearMap f)

/-- Contravariance reverses composition of integral character-lattice maps. -/
@[simp]
theorem ofLinearMap_comp (g : (tau → ℤ) →ₗ[ℤ] (upsilon → ℤ))
    (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    ofLinearMap R g ≫ ofLinearMap R f = ofLinearMap R (g ∘ₗ f) := by
  rw [ofLinearMap, ofLinearMap, ofLinearMap,
    ← DiagonalizableGroup.groupSchemeMap_comp, characterGroupMapOfLinearMap_comp]

/-- The identity character-lattice map induces the identity split-torus morphism. -/
@[simp]
theorem ofLinearMap_id :
    ofLinearMap R (LinearMap.id : (sigma → ℤ) →ₗ[ℤ] (sigma → ℤ)) = 𝟙 _ := by
  rw [ofLinearMap, characterGroupMapOfLinearMap_id,
    DiagonalizableGroup.groupSchemeMap_id]

/-- On scheme-valued points, `ofLinearMap R f` is the Laurent monomial map prescribed by the
images under `f` of the standard basis characters. -/
@[simp]
theorem schemePointsMulEquiv_ofLinearMap
    (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ))
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R tau).X) (i : sigma) :
    schemePointsMulEquiv (R := R) (A := A)
        (p ≫ (ofLinearMap R f).hom.hom) i =
      ((Finsupp.linearEquivFunOnFinite ℤ ℤ tau).symm
          (f (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma (Finsupp.single i 1)))).prod
        fun j n ↦ schemePointsMulEquiv (R := R) (A := A) p j ^ n := by
  rw [schemePointsMulEquiv_eq_freeAbelianCharEquiv, freeAbelianCharEquiv_apply,
    ofLinearMap, DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap,
    MonoidHom.comp_apply, toMonoidHom_characterGroupMapOfLinearMap,
    characterMapOfLinearMap_ofAdd]
  let chi := DiagonalizableGroup.schemePointsMulEquiv
    (R := R) (A := A) (characterGroup tau) p
  let m := (Finsupp.linearEquivFunOnFinite ℤ ℤ tau).symm
    (f (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma (Finsupp.single i 1)))
  have h := freeAbelianCharEquiv_symm_apply_ofAdd (freeAbelianCharEquiv chi) m
  rw [freeAbelianCharEquiv.symm_apply_apply] at h
  simpa only [schemePointsMulEquiv_eq_freeAbelianCharEquiv] using h

/-- The coordinatewise `n`-th power endomorphism of a split torus. -/
noncomputable def powEnd (R : Type u) [CommRing R] (sigma : Type u) [Finite sigma] (n : ℤ) :
    groupScheme R sigma ⟶ groupScheme R sigma :=
  ofLinearMap R (n • LinearMap.id)

/-- Power endomorphisms multiply their exponents under composition. -/
@[simp]
theorem powEnd_comp (m n : ℤ) :
    powEnd R sigma m ≫ powEnd R sigma n = powEnd R sigma (m * n) := by
  rw [powEnd, powEnd, powEnd, ofLinearMap_comp]
  congr 1
  ext x i
  simp [mul_comm]

/-- The first power endomorphism is the identity split-torus morphism. -/
@[simp]
theorem powEnd_one : powEnd R sigma 1 = 𝟙 _ := by
  simp [powEnd]

/-- On scheme-valued points, `powEnd n` raises every coordinate to the integer power `n`. -/
@[simp]
theorem schemePointsMulEquiv_powEnd (n : ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R sigma).X) (i : sigma) :
    schemePointsMulEquiv (R := R) (A := A)
        (p ≫ (powEnd R sigma n).hom.hom) i =
      schemePointsMulEquiv (R := R) (A := A) p i ^ n := by
  rw [powEnd, schemePointsMulEquiv_ofLinearMap]
  classical
  have h :
      (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma).symm
          ((n • (LinearMap.id : (sigma → ℤ) →ₗ[ℤ] (sigma → ℤ)))
            (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma (Finsupp.single i 1))) =
        Finsupp.single i n := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma).injective
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.linearEquivFunOnFinite_single]
    · simp [Finsupp.linearEquivFunOnFinite_single, hji]
  rw [h]
  simp

end SplitTorus

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

/-- **The square of the `B₂` special torus endomorphism is the coordinatewise square map.** -/
@[simp]
theorem b2SpecialTorusEnd_comp_self :
    b2SpecialTorusEnd R ≫ b2SpecialTorusEnd R = SplitTorus.powEnd R (Fin 2) 2 := by
  rw [b2SpecialTorusEnd, SplitTorus.ofLinearMap_comp, SplitTorus.powEnd]
  congr 1
  have h := congrArg RootPairingIsogeny.weightMap b2SpecialIsogeny_mul_self
  simpa [RootPairingIsogeny.mul_def] using h

/-- **The square of the `G₂` special torus endomorphism is the coordinatewise cube map.** -/
@[simp]
theorem g2SpecialTorusEnd_comp_self :
    g2SpecialTorusEnd R ≫ g2SpecialTorusEnd R = SplitTorus.powEnd R (Fin 2) 3 := by
  rw [g2SpecialTorusEnd, SplitTorus.ofLinearMap_comp, SplitTorus.powEnd]
  congr 1
  have h := congrArg RootPairingIsogeny.weightMap g2SpecialIsogeny_mul_self
  simpa [RootPairingIsogeny.mul_def] using h

/-- **The square of the `F₄` special torus endomorphism is the coordinatewise square map.** -/
@[simp]
theorem f4SpecialTorusEnd_comp_self :
    f4SpecialTorusEnd R ≫ f4SpecialTorusEnd R = SplitTorus.powEnd R (Fin 4) 2 := by
  rw [f4SpecialTorusEnd, SplitTorus.ofLinearMap_comp, SplitTorus.powEnd]
  congr 1
  have h := congrArg RootPairingIsogeny.weightMap f4SpecialIsogeny_mul_self
  simpa [RootPairingIsogeny.mul_def] using h

end DynkinType

end TauCeti
