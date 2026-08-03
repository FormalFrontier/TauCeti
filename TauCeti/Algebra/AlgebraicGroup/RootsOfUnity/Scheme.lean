/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Inclusion
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion

/-!
# The roots-of-unity group scheme

For a commutative ring `R` and a natural number `n`, the roots-of-unity group scheme is the
diagonalizable group

`mu_n = D(ULift (Multiplicative (ZMod n)))`.

The universe lift places the character group in the universe of `R`, as required by the
current scheme-level diagonalizable-group API. This file synchronizes that presentation with
the existing group-algebra and functor-of-points presentations:

* scheme-valued points of `mu_n` are the subgroup `rootsOfUnity n A` of the units of a value
  algebra `A`;
* the quotient of lifted character groups induced by `Z -> Z/n` gives a group-scheme morphism
  `mu_n -> G_m` whose action on points is the usual inclusion of roots of unity into units;
* this morphism is a closed immersion, since its coordinate map is the surjective group-algebra
  map induced by the quotient of character groups.

All statements include `n = 0`, `n = 1`, and the zero base and value rings. The classical
quotient presentation by `T ^ n - 1` and the realization as the kernel of the power map are
separate constructions.

This advances Layer 4 and the worked-examples lane of the reductive-groups roadmap by keeping
the Hopf-algebra, group-scheme, and functor-of-points descriptions of `mu_n` synchronized.

## Main declarations

* `TauCeti.RootsOfUnityGroup.characterGroup`: the same-universe character group of `mu_n`.
* `TauCeti.RootsOfUnityGroup.groupScheme`: `mu_n` as a diagonalizable group scheme.
* `TauCeti.RootsOfUnityGroup.schemePointsMulEquiv`: scheme-valued points are `n`th roots of
  unity.
* `TauCeti.RootsOfUnityGroup.characterQuotient`: the lifted quotient of character groups
  defining `mu_n -> G_m` contravariantly.
* `TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap`: the group-scheme inclusion
  `mu_n -> G_m`.
* `TauCeti.RootsOfUnityGroup.isClosedImmersion_inclusionGroupSchemeMap`: the inclusion is a
  closed immersion.

## References

Milne, *Algebraic Groups*, Definition 12.7 and Theorems 12.8--12.9, describes the
contravariant construction `D(M)` and its behavior on quotients of character groups.
-/

public section

open CategoryTheory
open AlgebraicGeometry
open WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace RootsOfUnityGroup

/-- The cyclic character group `Multiplicative (ZMod n)` is finitely generated for every
`n`, including `n = 0`, as a quotient of `Multiplicative Z`. -/
noncomputable instance instFGMultiplicativeZMod (n : ℕ) :
    Group.FG (Multiplicative (ZMod n)) :=
  Group.fg_of_surjective (toMultiplicativeZMod_surjective n)

/-- The character group defining `mu_n`, lifted into the universe of the base ring. -/
noncomputable abbrev characterGroup (n : ℕ) : FGCommGrpCat.{u} :=
  FGCommGrpCat.of (ULift.{u} (Multiplicative (ZMod n)))

/-- The roots-of-unity group scheme
`mu_n = D(ULift (Multiplicative (ZMod n)))` over `Spec R`. -/
noncomputable abbrev groupScheme (R : Type u) [CommRing R] (n : ℕ) :
    Grp (Over (Spec (CommRingCat.of R))) :=
  DiagonalizableGroup.groupScheme R (characterGroup n)

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Scheme-valued points of `mu_n` over `Spec R` are the `n`th roots of unity in the value
algebra.

The generic diagonalizable-group character is transported across `MulEquiv.ulift`, extended
to an unlifted group-algebra point, and then read by the existing roots-of-unity points
equivalence. -/
noncomputable def schemePointsMulEquiv (n : ℕ) :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) ≃* rootsOfUnity n A :=
  (((DiagonalizableGroup.schemePointsMulEquiv (R := R) (A := A)
      (characterGroup n)).trans
    (MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃*
      Multiplicative (ZMod n)).monoidHomCongrLeft).trans
    (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
      (G := Multiplicative (ZMod n))).symm).trans
    (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n)

/-- A scheme-valued point of `mu_n`, viewed as a root of unity, is obtained by evaluating
its coordinate-algebra point on the lifted standard generator. -/
@[simp]
theorem schemePointsMulEquiv_apply_coe (n : ℕ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) :
    ((schemePointsMulEquiv (R := R) (A := A) n p : Aˣ) : A) =
      (DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := R) (A := A) (characterGroup n) p).ofConv
        (MonoidAlgebra.single (ULift.up (generator n)) 1) := by
  let chi := DiagonalizableGroup.schemePointsMulEquiv
    (R := R) (A := A) (characterGroup n) p
  let f := (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
    (G := Multiplicative (ZMod n))).symm
      ((MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃*
        Multiplicative (ZMod n)).monoidHomCongrLeft chi)
  calc
    ((schemePointsMulEquiv (R := R) (A := A) n p : Aˣ) : A) =
        ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A) := by
      rfl
    _ = f.ofConv (MonoidAlgebra.single (generator n) 1) := by
      rw [RootsOfUnityGroup.pointsMulEquiv_apply]
    _ = (chi (ULift.up (generator n)) : A) := by
      dsimp [f]
      rw [DiagonalizableGroup.point_single_one]
      rfl
    _ = _ := by
      dsimp [chi]
      rw [DiagonalizableGroup.schemePointsMulEquiv_apply_coe]

/-- The scheme point associated to a root of unity evaluates the lifted standard generator
at that root. -/
theorem schemePointsMulEquiv_symm_apply_single_generator (n : ℕ)
    (ζ : rootsOfUnity n A) :
    (DiagonalizableGroup.groupSchemePointsMulEquiv
      (R := R) (A := A) (characterGroup n)
        ((schemePointsMulEquiv (R := R) (A := A) n).symm ζ)).ofConv
      (MonoidAlgebra.single (ULift.up (generator n)) 1) =
        ((ζ : Aˣ) : A) := by
  rw [← schemePointsMulEquiv_apply_coe]
  simp

/-- The scheme point associated to a root of unity evaluates scalar multiples of the lifted
standard generator by scalar multiplication of that root. -/
@[simp]
theorem schemePointsMulEquiv_symm_apply_single_generator_smul (n : ℕ)
    (ζ : rootsOfUnity n A) (r : R) :
    (DiagonalizableGroup.groupSchemePointsMulEquiv
      (R := R) (A := A) (characterGroup n)
        ((schemePointsMulEquiv (R := R) (A := A) n).symm ζ)).ofConv
      (MonoidAlgebra.single (ULift.up (generator n)) r) =
        r • ((ζ : Aˣ) : A) := by
  let f := (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n).symm ζ
  let chi := DiagonalizableGroup.pointsMulEquiv
    (R := R) (A := A) (G := Multiplicative (ZMod n)) f
  have hp :
      (schemePointsMulEquiv (R := R) (A := A) n).symm ζ =
        (DiagonalizableGroup.schemePointsMulEquiv
          (R := R) (A := A) (characterGroup n)).symm
            (((MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃*
              Multiplicative (ZMod n)).monoidHomCongrLeft).symm chi) := by
    rfl
  rw [hp, DiagonalizableGroup.schemePointsMulEquiv_symm_apply,
    MulEquiv.apply_symm_apply]
  calc
    ((DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
        (G := characterGroup n)).symm
          (((MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃*
            Multiplicative (ZMod n)).monoidHomCongrLeft).symm chi)).ofConv
          (MonoidAlgebra.single (ULift.up (generator n)) r) =
        f.ofConv (MonoidAlgebra.single (generator n) r) := by
      rw [DiagonalizableGroup.pointsMulEquiv_symm_apply, ofConv_toConv,
        DiagonalizableGroup.point_single]
      dsimp [chi]
      change r •
          ((DiagonalizableGroup.charOfPoint f.ofConv (generator n) : Aˣ) : A) = _
      rw [DiagonalizableGroup.charOfPoint_apply_coe]
      rw [show MonoidAlgebra.single (generator n) r =
        r • MonoidAlgebra.single (generator n) (1 : R) by simp, map_smul]
    _ = _ := RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator_smul
      (R := R) (A := A) n ζ r

/-- The scheme-valued roots-of-unity comparison is natural in the value algebra. -/
theorem schemePointsMulEquiv_mapValue (n : ℕ) (phi : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) :
    schemePointsMulEquiv (R := R) (A := B) n
        ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) =
      restrictRootsOfUnity phi.toMonoidHom n
        (schemePointsMulEquiv (R := R) (A := A) n p) := by
  ext
  rw [schemePointsMulEquiv_apply_coe]
  change _ = phi (((schemePointsMulEquiv (R := R) (A := A) n p : Aˣ) : A))
  rw [schemePointsMulEquiv_apply_coe,
    DiagonalizableGroup.groupSchemePointsMulEquiv_mapValue]
  rfl

/-! ### The closed inclusion into the multiplicative group scheme -/

/-- The quotient `Multiplicative Z -> Multiplicative (ZMod n)`, transported between the
same-universe character groups defining `G_m` and `mu_n`.

This lifted lattice map is public so later scheme-kernel constructions can reuse the exact
coordinate map without reconstructing universe transports from the scheme morphism. -/
noncomputable def characterQuotient (n : ℕ) :
    DiagonalizableGroup.multiplicativeCharacterGroup ⟶ characterGroup n :=
  FGCommGrpCat.ofHom <|
    (MulEquiv.ulift.symm : Multiplicative (ZMod n) ≃*
      ULift.{u} (Multiplicative (ZMod n))).toMonoidHom.comp <|
      (toMultiplicativeZMod n).comp
        (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃*
          Multiplicative ℤ).toMonoidHom

/-- The lifted character quotient sends the lift of an integer character to the lift of its
residue class. -/
@[simp]
theorem characterQuotient_apply_up (n : ℕ) (x : Multiplicative ℤ) :
    FGCommGrpCat.toMonoidHom (characterQuotient.{u} n) (ULift.up x) =
      ULift.up (toMultiplicativeZMod n x) := by
  rfl

/-- The lifted character quotient defining `mu_n -> G_m` is surjective for every `n`. -/
theorem characterQuotient_surjective (n : ℕ) :
    Function.Surjective (FGCommGrpCat.toMonoidHom (characterQuotient.{u} n)) := by
  intro y
  rcases y with ⟨y⟩
  obtain ⟨x, hx⟩ := toMultiplicativeZMod_surjective n y
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- The group-scheme morphism `mu_n -> G_m` induced contravariantly by the lifted quotient
of character groups. -/
noncomputable def inclusionGroupSchemeMap (R : Type u) [CommRing R] (n : ℕ) :
    groupScheme R n ⟶ DiagonalizableGroup.multiplicativeGroupScheme R :=
  DiagonalizableGroup.groupSchemeMap R (characterQuotient n)

/-- The roots-of-unity group-scheme inclusion is the contravariant diagonalizable image of
`characterQuotient`. -/
theorem inclusionGroupSchemeMap_def (n : ℕ) :
    inclusionGroupSchemeMap R n =
      DiagonalizableGroup.groupSchemeMap R (characterQuotient n) := by
  rfl

/-- On scheme-valued points, `mu_n -> G_m` is the established inclusion of roots of unity
into units. -/
@[simp high]
theorem multiplicativeGroupSchemePointsMulEquiv_inclusionGroupSchemeMap (n : ℕ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) :
    DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := R) (A := A)
        (p ≫ (inclusionGroupSchemeMap R n).hom.hom) =
      (schemePointsMulEquiv (R := R) (A := A) n p : Aˣ) := by
  rw [DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_apply,
    inclusionGroupSchemeMap_def,
    DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap,
    MonoidHom.comp_apply, characterQuotient_apply_up,
    toMultiplicativeZMod_ofAdd_one]
  let chi := DiagonalizableGroup.schemePointsMulEquiv
    (R := R) (A := A) (characterGroup n) p
  let f := (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
    (G := Multiplicative (ZMod n))).symm
      ((MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃*
        Multiplicative (ZMod n)).monoidHomCongrLeft chi)
  calc
    chi (ULift.up (generator n)) =
        DiagonalizableGroup.charOfPoint (inclusion n f).ofConv
          (Multiplicative.ofAdd 1) := by
      rw [charOfPoint_inclusion, MonoidHom.comp_apply,
        toMultiplicativeZMod_ofAdd_one]
      dsimp [f]
      rw [DiagonalizableGroup.charOfPoint_point]
      rfl
    _ = (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f : Aˣ) :=
      charOfPoint_inclusion_ofAdd_one n f
    _ = (schemePointsMulEquiv (R := R) (A := A) n p : Aˣ) := by
      rfl

/-- The comparison between the scheme inclusion and the inclusion of roots into units is
natural in the value algebra. -/
theorem multiplicativeGroupSchemePointsMulEquiv_inclusionGroupSchemeMap_mapValue
    (n : ℕ) (phi : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) :
    DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := R) (A := B)
        (((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) ≫
            (inclusionGroupSchemeMap R n).hom.hom) =
      Units.map phi.toMonoidHom
        (schemePointsMulEquiv (R := R) (A := A) n p : Aˣ) := by
  rw [Category.assoc,
    DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_mapValue,
    multiplicativeGroupSchemePointsMulEquiv_inclusionGroupSchemeMap]

/-- The coordinate map induced by the lifted character quotient is surjective. -/
theorem coordinateMap_characterQuotient_surjective (n : ℕ) :
    Function.Surjective
      (FiniteTypeCommHopfAlgCat.toBialgHom
        (DiagonalizableGroup.coordinateMap R (characterQuotient.{u} n))) := by
  rw [DiagonalizableGroup.toBialgHom_coordinateMap]
  intro y
  change MonoidAlgebra R (characterGroup n) at y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := R)
    (f := FGCommGrpCat.toMonoidHom (characterQuotient.{u} n))
    (characterQuotient_surjective n) y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  unfold MonoidAlgebra.mapDomainBialgHom
  apply MonoidAlgebra.coeff_injective
  exact hx

/-- The group-scheme morphism `mu_n -> G_m` is a closed immersion. -/
instance isClosedImmersion_inclusionGroupSchemeMap (n : ℕ) :
    IsClosedImmersion (inclusionGroupSchemeMap R n).hom.hom.left := by
  let e₁ :=
    (eqToHom (DiagonalizableGroup.groupScheme_def R (characterGroup n))).hom.hom.left
  let e₂ :=
    (eqToHom (DiagonalizableGroup.groupScheme_def R
      DiagonalizableGroup.multiplicativeCharacterGroup).symm).hom.hom.left
  let c := ((hopfSpec (CommRingCat.of R)).map
    (DiagonalizableGroup.coordinateMap R
      (characterQuotient.{u} n)).hom.op).hom.hom.left
  have he₁ : IsIso e₁ :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (DiagonalizableGroup.groupScheme_def R (characterGroup n))))).isIso_hom
  have he₂ : IsIso e₂ :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (DiagonalizableGroup.groupScheme_def R
          DiagonalizableGroup.multiplicativeCharacterGroup).symm))).isIso_hom
  have hc : IsClosedImmersion c :=
    (CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff _).2
      (coordinateMap_characterQuotient_surjective (R := R) n)
  have hc₂ : IsClosedImmersion (c ≫ e₂) :=
    (@MorphismProperty.cancel_right_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ c e₂ he₂).2 hc
  have he₁c₂ : IsClosedImmersion (e₁ ≫ (c ≫ e₂)) :=
    (@MorphismProperty.cancel_left_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ e₁ (c ≫ e₂) he₁).2 hc₂
  rw [inclusionGroupSchemeMap_def, DiagonalizableGroup.groupSchemeMap_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  exact he₁c₂

end RootsOfUnityGroup

end TauCeti
