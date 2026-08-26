/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme

/-!
# Relabelling the coordinates of a split torus

A permutation `τ` of the index set of the rank-`sigma` split torus permutes its coordinates, hence
acts on its character lattice `sigma →₀ ℤ`, on its coordinate Hopf algebra, and on the group scheme
itself. This file records that action at all three levels, together with its two structural
identities: it is multiplicative in `τ` and trivial at the identity permutation.

The character-lattice map sends a character `χ` to `χ ∘ τ⁻¹`. On points, a character is
precomposed with this map, so a coordinate tuple `d` becomes `d ∘ τ`. A consumer that has to
check a finite-order
relation for a relabelling — the graph automorphism of a Chevalley group is the case this file was
written for — gets it from the two identities below and the order of `τ` in `Equiv.Perm sigma`,
with no further computation.

## Main declarations

* `TauCeti.SplitTorus.characterRelabel`: the induced automorphism of the character lattice.
* `TauCeti.SplitTorus.characterRelabelHom`: the same map, read in `FGCommGrpCat`.
* `TauCeti.SplitTorus.relabelCoordinateMap`: the induced automorphism of the coordinate
  Hopf algebra.
* `TauCeti.SplitTorus.relabel`: the induced automorphism of the split-torus group scheme.
* `TauCeti.SplitTorus.relabelIso`: the same automorphism as a bundled isomorphism.
* `TauCeti.SplitTorus.schemePointsMulEquiv_relabel`: its action on coordinate tuples.

## Universes

The character lattice and the coordinate Hopf algebra are relabelled for a base ring in an
arbitrary universe. From `relabel` onwards the base ring and the index set must share a universe:
`TauCeti.SplitTorus.groupScheme` takes `(R sigma : Type u)`, and its scheme-valued points take the
value algebra in that same universe, because Mathlib's `hopfSpec` and `Spec.mapMulEquiv` are
same-universe.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open CategoryTheory

namespace TauCeti.SplitTorus

universe u v

variable {sigma : Type u}

/-- **Relabelling the characters of the rank-`sigma` split torus along a permutation of `sigma`.**
It sends the character `χ` to `χ ∘ τ⁻¹`. -/
noncomputable def characterRelabel (τ : Equiv.Perm sigma) :
    Multiplicative (sigma →₀ ℤ) ≃* Multiplicative (sigma →₀ ℤ) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr τ)

/-- Relabelling a character reindexes its coordinate function. -/
@[simp]
theorem characterRelabel_apply (τ : Equiv.Perm sigma) (x : Multiplicative (sigma →₀ ℤ)) :
    characterRelabel τ x =
      Multiplicative.ofAdd (Finsupp.equivMapDomain τ (Multiplicative.toAdd x)) := (rfl)

/-- Relabelling an additively written character. -/
theorem characterRelabel_ofAdd (τ : Equiv.Perm sigma) (f : sigma →₀ ℤ) :
    characterRelabel τ (Multiplicative.ofAdd f) =
      Multiplicative.ofAdd (Finsupp.equivMapDomain τ f) := (rfl)

/-- Relabelling is multiplicative in the permutation. -/
@[simp]
theorem characterRelabel_comp (τ ν : Equiv.Perm sigma) :
    (characterRelabel τ : Multiplicative (sigma →₀ ℤ) →* Multiplicative (sigma →₀ ℤ)).comp
        (characterRelabel ν) =
      (characterRelabel (τ * ν) : Multiplicative (sigma →₀ ℤ) →* Multiplicative (sigma →₀ ℤ)) := by
  refine MonoidHom.ext fun x => ?_
  -- Coercion from the bundled multiplicative equivalence exposes its additive `Finsupp` map only
  -- by definitional equality; the named `equivMapDomain_trans` lemma applies at that layer.
  change Multiplicative.ofAdd
      (Finsupp.equivMapDomain τ (Finsupp.equivMapDomain ν (Multiplicative.toAdd x))) =
    Multiplicative.ofAdd
      (Finsupp.equivMapDomain (ν.trans τ) (Multiplicative.toAdd x))
  exact congrArg Multiplicative.ofAdd
    (Finsupp.equivMapDomain_trans ν τ (Multiplicative.toAdd x)).symm

/-- Relabelling by the identity permutation is the identity. -/
@[simp]
theorem characterRelabel_one :
    (characterRelabel (sigma := sigma) 1 :
      Multiplicative (sigma →₀ ℤ) →* Multiplicative (sigma →₀ ℤ)) = MonoidHom.id _ := by
  refine MonoidHom.ext fun x => ?_
  -- As above, expose the additive representative of the bundled multiplicative equivalence.
  change Multiplicative.ofAdd
      (Finsupp.equivMapDomain (Equiv.refl sigma) (Multiplicative.toAdd x)) = x
  rw [Finsupp.equivMapDomain_refl]
  rfl

variable [Finite sigma]

/-- The relabelling of the character group, read as a morphism of finitely generated commutative
groups. -/
noncomputable def characterRelabelHom (τ : Equiv.Perm sigma) :
    characterGroup sigma ⟶ characterGroup sigma :=
  FGCommGrpCat.ofHom (characterRelabel τ)

/-- The underlying monoid homomorphism of `characterRelabelHom`. -/
@[simp]
theorem toMonoidHom_characterRelabelHom (τ : Equiv.Perm sigma) :
    FGCommGrpCat.toMonoidHom (characterRelabelHom τ) =
      characterRelabel τ :=
  (rfl)

/-- Relabelling of character groups is multiplicative in the permutation. -/
@[simp]
theorem characterRelabelHom_comp (τ ν : Equiv.Perm sigma) :
    characterRelabelHom ν ≫ characterRelabelHom τ =
      characterRelabelHom (sigma := sigma) (τ * ν) := by
  apply FGCommGrpCat.hom_ext
  rw [FGCommGrpCat.toMonoidHom_comp, toMonoidHom_characterRelabelHom,
    toMonoidHom_characterRelabelHom, toMonoidHom_characterRelabelHom,
    characterRelabel_comp]

/-- Relabelling of character groups by the identity permutation is the identity. -/
@[simp]
theorem characterRelabelHom_one :
    characterRelabelHom (sigma := sigma) 1 = CategoryStruct.id _ := by
  apply FGCommGrpCat.hom_ext
  rw [toMonoidHom_characterRelabelHom, characterRelabel_one,
    FGCommGrpCat.toMonoidHom_id]

section CoordinateRing

variable (R : Type v) [CommRing R]

/-- **The relabelling automorphism of the coordinate Hopf algebra of the split torus.** -/
noncomputable def relabelCoordinateMap (τ : Equiv.Perm sigma) :
    (DiagonalizableGroup.coordinateRing R (characterGroup sigma)).obj ⟶
      (DiagonalizableGroup.coordinateRing R (characterGroup sigma)).obj :=
  (DiagonalizableGroup.coordinateMap R (characterRelabelHom τ)).hom

/-- The bialgebra morphism underlying the coordinate relabelling. -/
theorem hom_relabelCoordinateMap (τ : Equiv.Perm sigma) :
    (relabelCoordinateMap R τ).hom =
      MonoidAlgebra.mapDomainBialgHom R (characterRelabel τ) :=
  (rfl)

/-- Coordinate relabelling is multiplicative in the permutation. -/
@[simp]
theorem relabelCoordinateMap_comp (τ ν : Equiv.Perm sigma) :
    relabelCoordinateMap R τ ≫ relabelCoordinateMap R ν =
      relabelCoordinateMap (sigma := sigma) R (ν * τ) := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [_root_.CommHopfAlgCat.hom_comp, hom_relabelCoordinateMap, hom_relabelCoordinateMap,
    hom_relabelCoordinateMap, ← MonoidAlgebra.mapDomainBialgHom_comp, characterRelabel_comp]

/-- Coordinate relabelling by the identity permutation is the identity. -/
@[simp]
theorem relabelCoordinateMap_one :
    relabelCoordinateMap (sigma := sigma) R 1 = CategoryStruct.id _ := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [hom_relabelCoordinateMap, characterRelabel_one, MonoidAlgebra.mapDomainBialgHom_id]
  rfl

noncomputable instance isIso_relabelCoordinateMap (τ : Equiv.Perm sigma) :
    IsIso (relabelCoordinateMap (sigma := sigma) R τ) := by
  apply IsIso.mk
  refine ⟨relabelCoordinateMap R τ⁻¹, ?_, ?_⟩
  · rw [relabelCoordinateMap_comp, inv_mul_cancel, relabelCoordinateMap_one]
  · rw [relabelCoordinateMap_comp, mul_inv_cancel, relabelCoordinateMap_one]

/-- Coordinate relabelling is injective, as the underlying map of an isomorphism. -/
theorem relabelCoordinateMap_injective (τ : Equiv.Perm sigma) :
    Function.Injective (relabelCoordinateMap (sigma := sigma) R τ).hom :=
  (ConcreteCategory.bijective_of_isIso
    (relabelCoordinateMap (sigma := sigma) R τ)).1

end CoordinateRing

section GroupScheme

variable (R : Type u) [CommRing R]

/-- **The relabelling automorphism of the split-torus group scheme.** On points a character is
precomposed with `characterRelabel τ`, so the coordinate tuple `d` becomes `d ∘ τ`. -/
noncomputable def relabel (τ : Equiv.Perm sigma) :
    groupScheme R sigma ⟶ groupScheme R sigma :=
  DiagonalizableGroup.groupSchemeMap R (characterRelabelHom τ)

/-- Relabelling of group schemes is multiplicative in the permutation. -/
@[simp]
theorem relabel_comp (τ ν : Equiv.Perm sigma) :
    relabel R τ ≫ relabel R ν = relabel (sigma := sigma) R (τ * ν) := by
  rw [relabel, relabel, relabel, ← DiagonalizableGroup.groupSchemeMap_comp,
    characterRelabelHom_comp]

/-- Relabelling by the identity permutation is the identity. -/
@[simp]
theorem relabel_one : relabel (sigma := sigma) R 1 = CategoryStruct.id _ := by
  rw [relabel, characterRelabelHom_one, DiagonalizableGroup.groupSchemeMap_id]

noncomputable instance isIso_relabel (τ : Equiv.Perm sigma) :
    IsIso (relabel (sigma := sigma) R τ) := by
  apply IsIso.mk
  refine ⟨relabel R τ⁻¹, ?_, ?_⟩
  · rw [relabel_comp, mul_inv_cancel, relabel_one]
  · rw [relabel_comp, inv_mul_cancel, relabel_one]

/-- The relabelling automorphism of the split torus, bundled as an isomorphism. -/
noncomputable def relabelIso (τ : Equiv.Perm sigma) : Aut (groupScheme R sigma) :=
  asIso (relabel R τ)

@[simp]
theorem relabelIso_hom (τ : Equiv.Perm sigma) :
    (relabelIso (sigma := sigma) R τ).hom = relabel R τ :=
  by simp [relabelIso]

/-- The inverse of the bundled relabelling is relabelling by the inverse permutation. -/
@[simp]
theorem relabelIso_inv (τ : Equiv.Perm sigma) :
    (relabelIso (sigma := sigma) R τ).inv = relabel R τ⁻¹ := by
  rw [relabelIso, asIso_inv]
  symm
  apply IsIso.eq_inv_of_hom_inv_id
  simp

/-- Bundled relabelling is multiplicative, with the order reversed by categorical composition. -/
@[simp]
theorem relabelIso_mul (τ ν : Equiv.Perm sigma) :
    relabelIso (sigma := sigma) R (τ * ν) = relabelIso R ν * relabelIso R τ := by
  apply Iso.ext
  rw [relabelIso_hom, CategoryTheory.Aut.Aut_mul_def]
  -- The `hom` of `Iso.trans` is its categorical composite by definition.
  change relabel R (τ * ν) = (relabelIso R τ).hom ≫ (relabelIso R ν).hom
  rw [relabelIso_hom, relabelIso_hom, relabel_comp]

/-- Bundled relabelling by the identity permutation is the identity automorphism. -/
@[simp]
theorem relabelIso_one : relabelIso (sigma := sigma) R 1 = 1 := by
  apply Iso.ext
  rw [relabelIso_hom, relabel_one]
  rfl

/-- The forward morphism of a power of a relabelling is relabelling by the corresponding
permutation power. -/
@[simp]
theorem relabelIso_pow_hom (τ : Equiv.Perm sigma) (m : ℕ) :
    ((relabelIso (sigma := sigma) R τ) ^ m).hom = relabel R (τ ^ m) := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, relabel_one]
      rfl
  | succ m ih =>
      rw [pow_succ]
      -- Powers in `Aut` reduce definitionally to reverse categorical composition on homs.
      change relabel R τ ≫ ((relabelIso R τ) ^ m).hom = _
      rw [ih, relabel_comp, ← pow_succ']

/-- On scheme-valued points, relabelling sends a coordinate tuple `d` to `d ∘ τ`. -/
@[simp]
theorem schemePointsMulEquiv_relabel {A : Type u} [CommRing A] [Algebra R A]
    (τ : Equiv.Perm sigma)
    (p : (AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
      (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R sigma).X)
    (i : sigma) :
    schemePointsMulEquiv (p ≫ (relabel R τ).hom.hom) i =
      schemePointsMulEquiv p (τ i) := by
  rw [relabel, schemePointsMulEquiv_eq_freeAbelianCharEquiv,
    schemePointsMulEquiv_eq_freeAbelianCharEquiv,
    DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap,
    toMonoidHom_characterRelabelHom, freeAbelianCharEquiv_apply,
    MonoidHom.comp_apply]
  let chi := DiagonalizableGroup.schemePointsMulEquiv
    (R := R) (A := A) (characterGroup sigma) p
  -- The point-coordinate equivalence evaluates basis characters only after unfolding its
  -- presentation through the free abelian character equivalence.
  change chi (characterRelabel τ (Multiplicative.ofAdd (Finsupp.single i 1))) =
    chi (Multiplicative.ofAdd (Finsupp.single (τ i) 1))
  rw [characterRelabel_ofAdd, Finsupp.equivMapDomain_single]
  rfl

/-- The group-scheme relabelling is the spectrum of the coordinate relabelling, read across the
canonical presentation of the split torus. -/
theorem relabel_def (τ : Equiv.Perm sigma) :
    relabel R τ =
      eqToHom (DiagonalizableGroup.groupScheme_def R (characterGroup sigma)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (relabelCoordinateMap R τ).op ≫
        eqToHom (DiagonalizableGroup.groupScheme_def R (characterGroup sigma)).symm :=
  DiagonalizableGroup.groupSchemeMap_def R (characterRelabelHom τ)

end GroupScheme

end TauCeti.SplitTorus
