/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter

/-!
# The finite-rank split torus as a group scheme

For a finite index type `sigma`, the split torus with character lattice `sigma →₀ ℤ` is
the diagonalizable group scheme
`D(Multiplicative (sigma →₀ ℤ))`. This file synchronizes that scheme presentation with
the existing functor-of-points and character--cocharacter APIs:

* its scheme-valued points over an `R`-algebra `A` are the coordinate family `sigma → Aˣ`;
* a character `m : sigma →₀ ℤ` is an actual group-scheme morphism to `𝔾ₘ`, acting on
  points by the Laurent monomial `∏ i, x_i ^ m_i`;
* a cocharacter is an actual group-scheme morphism from `𝔾ₘ`, acting coordinatewise by
  integer powers;
* their composite is the power map whose exponent is the existing perfect lattice pairing.

The scheme-valued point comparison uses the same-universe diagonalizable-group bridge from
`DiagonalizableGroup.Scheme.Points`; this is why both the base ring and finite index type live
in the same universe. Ordinary character and cocharacter exponents remain in `ℤ`.

This advances Layer 4 of the reductive-groups roadmap
(`TauCetiRoadmap/ReductiveGroups/README.md`): the finite-rank split torus, its
character and cocharacter lattices, and their perfect pairing now have a synchronized
group-scheme realization.

## Main declarations

* `TauCeti.SplitTorus.groupScheme`: the finite-rank split torus group scheme.
* `TauCeti.SplitTorus.schemePointsMulEquiv`: its scheme-valued points are `sigma → Aˣ`.
* `TauCeti.SplitTorus.characterGroupSchemeMap`: a lattice character as a group-scheme
  morphism to `𝔾ₘ`.
* `TauCeti.SplitTorus.cocharacterGroupSchemeMap`: a lattice cocharacter as a group-scheme
  morphism from `𝔾ₘ`.
* `TauCeti.SplitTorus.cocharacterGroupSchemeMap_comp_characterGroupSchemeMap`: composition
  realizes the perfect lattice pairing as a power map.

## References

Milne, *Algebraic Groups*, Definition 12.7 and Theorems 12.8--12.9, describes split tori
through diagonalizable groups. The coordinate computations reuse Tau Ceti's
`freeAbelianCharEquiv`, `SplitTorus.cocharEquiv`, and `SplitTorus.latticePairing`.
-/

public section

open CategoryTheory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace SplitTorus

variable {R A B sigma : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- A finite-rank free character lattice, written multiplicatively, is finitely generated. -/
instance instFGMultiplicativeFinsuppInt [Finite sigma] :
    Group.FG (Multiplicative (sigma →₀ ℤ)) := by
  exact AddGroup.fg_iff_mul_fg.mp
    (Module.Finite.iff_addGroup_fg.mp
      (inferInstance : Module.Finite ℤ (sigma →₀ ℤ)))

/-- The finitely generated character group of the split torus indexed by `sigma`. -/
noncomputable abbrev characterGroup (sigma : Type u) [Finite sigma] : FGCommGrpCat.{u} :=
  FGCommGrpCat.of (Multiplicative (sigma →₀ ℤ))

/-- The finite-rank split torus with character lattice `sigma →₀ ℤ`, as a group scheme
over `Spec R`. -/
noncomputable abbrev groupScheme (R sigma : Type u) [CommRing R] [Finite sigma] :
    Grp (Over (Spec (CommRingCat.of R))) :=
  DiagonalizableGroup.groupScheme R (characterGroup sigma)

/-- Scheme-valued points of the finite-rank split torus are coordinate families of units. -/
@[expose] noncomputable def schemePointsMulEquiv [Finite sigma] :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R sigma).X) ≃* (sigma → Aˣ) :=
  (DiagonalizableGroup.schemePointsMulEquiv (R := R) (A := A)
    (characterGroup sigma)).trans freeAbelianCharEquiv

/-- The `i`-th coordinate of a scheme-valued point is its value on the group-algebra
monomial for the `i`-th standard character. -/
@[simp]
theorem schemePointsMulEquiv_apply_coe [Finite sigma]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R sigma).X) (i : sigma) :
    (schemePointsMulEquiv (R := R) (A := A) p i : A) =
      (DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := R) (A := A) (characterGroup sigma) p).ofConv
        (MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.single i 1)) 1) := by
  rw [schemePointsMulEquiv, MulEquiv.trans_apply, freeAbelianCharEquiv_apply,
    DiagonalizableGroup.schemePointsMulEquiv_apply_coe]
  rfl

/-- The inverse coordinate equivalence is the spectrum morphism extending the free-abelian
character determined by the coordinate family. -/
theorem schemePointsMulEquiv_symm_apply [Finite sigma]
    (c : sigma → Aˣ) :
    (schemePointsMulEquiv (R := R) (A := A)).symm c =
      (DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := R) (A := A) (characterGroup sigma)).symm
          ((pointsMulEquiv (R := R) (A := A)).symm c) := by
  rw [schemePointsMulEquiv, MulEquiv.symm_trans_apply,
    DiagonalizableGroup.schemePointsMulEquiv_symm_apply]
  congr 1
  rw [DiagonalizableGroup.pointsMulEquiv_symm_apply, pointsMulEquiv_symm_apply]

/-- The split-torus scheme-points equivalence is natural in the value algebra. -/
theorem schemePointsMulEquiv_mapValue [Finite sigma] (phi : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R sigma).X) :
    schemePointsMulEquiv (R := R) (A := B)
        ((Spec.map (CommRingCat.ofHom phi.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫ p) =
      fun i => Units.map phi.toMonoidHom
        (schemePointsMulEquiv (R := R) (A := A) p i) := by
  rw [schemePointsMulEquiv, MulEquiv.trans_apply,
    DiagonalizableGroup.schemePointsMulEquiv_mapValue]
  ext i
  rw [freeAbelianCharEquiv_comp, schemePointsMulEquiv, MulEquiv.trans_apply]

/-! ### Characters and cocharacters as group-scheme morphisms -/

/-- A character in the split torus character lattice gives a group-scheme morphism to
the multiplicative group scheme. -/
@[expose] noncomputable def characterGroupSchemeMap [Finite sigma] (m : sigma →₀ ℤ) :
    groupScheme R sigma ⟶ DiagonalizableGroup.multiplicativeGroupScheme R :=
  DiagonalizableGroup.characterGroupSchemeMap (R := R) (characterGroup sigma)
    (Multiplicative.ofAdd m)

/-- On scheme-valued points, a split-torus character is the Laurent monomial with exponent
vector `m`. -/
theorem multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap [Finite sigma]
    (m : sigma →₀ ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R sigma).X) :
    DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := R) (A := A) (p ≫ (characterGroupSchemeMap (R := R) m).hom.hom) =
      m.prod fun i n => schemePointsMulEquiv (R := R) (A := A) p i ^ n := by
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply]
  calc
    _ = DiagonalizableGroup.schemePointsMulEquiv
        (R := R) (A := A) (characterGroup sigma) p
          (Multiplicative.ofAdd m : characterGroup sigma) := by
      exact
        DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_characterGroupSchemeMap
          (R := R) (A := A) (characterGroup sigma)
            (Multiplicative.ofAdd m : characterGroup sigma) p
    _ = _ := by
      let chi : Multiplicative (sigma →₀ ℤ) →* Aˣ :=
        DiagonalizableGroup.schemePointsMulEquiv
          (R := R) (A := A) (characterGroup sigma) p
      -- `characterGroup sigma` is the bundled abbreviation for the free multiplicative
      -- lattice; this aligns that representation with the unbundled character `chi`.
      change chi (Multiplicative.ofAdd m) =
        m.prod fun i n => freeAbelianCharEquiv chi i ^ n
      conv_lhs =>
        rw [← freeAbelianCharEquiv.symm_apply_apply chi,
          freeAbelianCharEquiv_symm_apply_ofAdd]

/-- A split-torus cocharacter gives a group-scheme morphism from the multiplicative group
scheme. -/
@[expose] noncomputable def cocharacterGroupSchemeMap [Finite sigma]
    (psi : Multiplicative (sigma →₀ ℤ) →* Multiplicative ℤ) :
    DiagonalizableGroup.multiplicativeGroupScheme R ⟶ groupScheme R sigma :=
  DiagonalizableGroup.cocharacterGroupSchemeMap (R := R) (characterGroup sigma) psi

/-- On scheme-valued points, a split-torus cocharacter raises the input unit to the
integer specified by each cocharacter coordinate. -/
theorem schemePointsMulEquiv_cocharacterGroupSchemeMap [Finite sigma]
    (psi : Multiplicative (sigma →₀ ℤ) →* Multiplicative ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (DiagonalizableGroup.multiplicativeGroupScheme R).X) (i : sigma) :
    schemePointsMulEquiv (R := R) (A := A)
        (p ≫ (cocharacterGroupSchemeMap (R := R) (sigma := sigma) psi).hom.hom) i =
      DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := R) (A := A) p ^ cocharEquiv psi i := by
  rw [schemePointsMulEquiv, MulEquiv.trans_apply, freeAbelianCharEquiv_apply,
    cocharacterGroupSchemeMap,
    DiagonalizableGroup.schemePointsMulEquiv_cocharacterGroupSchemeMap,
    cocharEquiv_apply]

/-- Composing a split-torus cocharacter with a character is the power map whose exponent
is their perfect lattice pairing. -/
theorem cocharacterGroupSchemeMap_comp_characterGroupSchemeMap [Finite sigma]
    (m : sigma →₀ ℤ)
    (psi : Multiplicative (sigma →₀ ℤ) →* Multiplicative ℤ) :
    cocharacterGroupSchemeMap (R := R) (sigma := sigma) psi ≫
        characterGroupSchemeMap (R := R) m =
      DiagonalizableGroup.powEndGroupSchemeMap (R := R)
        (latticePairing m (Additive.ofMul psi)) := by
  rw [cocharacterGroupSchemeMap, characterGroupSchemeMap, latticePairing_ofMul]
  exact DiagonalizableGroup.cocharacterGroupSchemeMap_comp_characterGroupSchemeMap
    (R := R) (characterGroup sigma) (Multiplicative.ofAdd m) psi

end SplitTorus

end TauCeti
