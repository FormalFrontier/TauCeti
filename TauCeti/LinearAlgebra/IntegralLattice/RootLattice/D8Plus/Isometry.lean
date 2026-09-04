/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.D8Plus.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE
public import TauCeti.LinearAlgebra.RootSystem.E8Coordinates

/-!
# The spinor glue lattice `D₈⁺` is the `E₈` root lattice

The lattice `D₈⁺ = D₈ ∪ (s + D₈)` built by gluing the rank-eight checkerboard lattice along its
spinor class is even and unimodular.  This file proves the sharper statement that it *is* the
root lattice of type `E₈`, by exhibiting an explicit isometry

```text
E₈ ≃ D₈⁺.
```

The isometry is the rational linear map carrying the `i`-th standard coordinate vector of the
simple-root model of `E₈` to the `i`-th vector of Bourbaki's plate VII, written in the
Conway--Sloane coordinates of `D₈`:

```text
α₁ = (e₁ - e₂ - e₃ - e₄ - e₅ - e₆ - e₇ + e₈) / 2,
α₂ = e₁ + e₂,   α₃ = e₂ - e₁,   α₄ = e₃ - e₂,   α₅ = e₄ - e₃,
α₆ = e₅ - e₄,   α₇ = e₆ - e₅,   α₈ = e₇ - e₆.
```

Only `α₁` leaves the checkerboard lattice, and it does so by exactly the Conway--Sloane spinor
vector `s = (e₁ + ⋯ + e₈) / 2`, so all eight vectors lie in `D₈⁺`.

Three facts turn that list into an isometry of integral lattices.

* Their Gram matrix for the standard dot product is `CartanMatrix.E 8`.  This is checked from
  doubled integer coordinates, so the verification is a decidable statement about integer
  matrices.
* The associated linear map is injective, because the `E₈` form is nondegenerate and the map
  intertwines the two forms; an injective endomorphism of `ℚ⁸` is bijective.
* Its image is the whole of `D₈⁺`.  One inclusion is the membership check above.  For the other,
  a vector `x ∈ D₈⁺` has a rational preimage `u`, and `⟨u, v⟩_{E₈} = ⟨x, Φ v⟩` is an integer for
  every `v` in the `E₈` carrier because `D₈⁺` is integral; so `u` lies in the dual of the `E₈`
  root lattice, which is the `E₈` root lattice itself.

The last step is where unimodularity of `E₈` enters, and it is what makes the inclusion an
equality without any determinant computation.  In particular the conclusion is a genuine lattice
isometry and not the invalid inference that two even unimodular rank-eight lattices must be
isometric.

Being an isometry, it transports every invariant: `D₈⁺` inherits the `E₈` root system's
determinant `1` and trivial discriminant group.  The resulting cardinality agrees with what the
general overlattice comparison `A_{L_H} ≅ H⊥ / H` predicts for the order-two spinor glue subgroup
`H`.

## Main declarations

* `TauCeti.IntegralLattice.e8GlueRoot`: the eight Bourbaki simple roots of `E₈`, in the
  coordinates of the Conway--Sloane model of `D₈`, read off the library's shared integral table
  `TauCeti.DynkinType.e8DoubledSimpleRoot`.
* `TauCeti.IntegralLattice.form_e8GlueRoot_e8GlueRoot`: their Gram matrix is `CartanMatrix.E 8`.
* `TauCeti.IntegralLattice.e8GlueRoot_mem_d8PlusCarrier`: they lie in `D₈⁺`.
* `TauCeti.IntegralLattice.span_range_e8GlueRoot`: they span `D₈⁺` over `ℤ`.
* `TauCeti.IntegralLattice.e8GlueMap`: the rational comparison map.
* `TauCeti.IntegralLattice.typeE₈IsometryD8Plus`: **the isometry `E₈ ≃ D₈⁺`**, whose inverse
  `typeE₈IsometryD8Plus.symm` is the isometry `D₈⁺ ≃ E₈`.
* `TauCeti.IntegralLattice.d8PlusDiscriminantQuadraticIsometry`: the discriminant quadratic form
  of `D₈⁺` is that of `E₈`.
* `TauCeti.IntegralLattice.natCard_orthogonalQuotient_d8SpinorSubgroup`: the general comparison
  gives `H⊥ / H` cardinality one, as predicted by the direct `E₈` computation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plate VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, §4.8.1.
* W. Ebeling, *Lattices and Codes*, Chapter 3.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5, the `D₈ ⊂ E₈` glue calculation.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Module

/-! ## The Bourbaki simple roots in Conway--Sloane coordinates -/

/-- The `i`-th simple root of `E₈` in Bourbaki's numbering, written in the standard coordinates of
the Conway--Sloane model of `D₈`.

The coordinates are read off the library's shared integral table
`TauCeti.DynkinType.e8DoubledSimpleRoot`, whose row `i` is `2αᵢ₊₁` in exactly these coordinates.
The doubling there clears the halves in `α₁`, so that every check on these vectors reduces to a
decidable statement about integers. -/
def e8GlueRoot (i : Fin 8) : Fin 8 → ℚ :=
  fun j ↦ (DynkinType.e8DoubledSimpleRoot i j : ℚ) / 2

/-- The coordinates of a glue root are half the corresponding doubled integer coordinates. -/
@[simp]
theorem e8GlueRoot_apply (i j : Fin 8) :
    e8GlueRoot i j = (DynkinType.e8DoubledSimpleRoot i j : ℚ) / 2 := by
  rw [e8GlueRoot]

/-! ## The Gram matrix -/

/-- **The Gram matrix of the eight glue roots is the Cartan matrix of type `E₈`.** -/
theorem form_e8GlueRoot_e8GlueRoot (i j : Fin 8) :
    (checkerboardLattice 8).form (e8GlueRoot i) (e8GlueRoot j) =
      (((CartanMatrix.E 8) i j : ℤ) : ℚ) := by
  have hcast : ∑ k, (DynkinType.e8DoubledSimpleRoot i k : ℚ) *
      (DynkinType.e8DoubledSimpleRoot j k : ℚ) = 4 * (((CartanMatrix.E 8) i j : ℤ) : ℚ) := by
    exact_mod_cast DynkinType.sum_e8DoubledSimpleRoot_mul_e8DoubledSimpleRoot i j
  rw [checkerboardLattice_form_apply]
  have hsplit : ∑ k, e8GlueRoot i k * e8GlueRoot j k
      = (∑ k, ((DynkinType.e8DoubledSimpleRoot i k : ℚ) *
        (DynkinType.e8DoubledSimpleRoot j k : ℚ))) / 4 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [e8GlueRoot_apply, e8GlueRoot_apply]; ring
  rw [hsplit, hcast]
  ring

/-! ## Membership in the glue lattice -/

/-- The integer coordinates of the glue root `αᵢ₊₁`, after subtracting the spinor vector in the
one case `i = 0` where the root is not already a checkerboard vector. -/
private def e8GlueShift (i j : Fin 8) : ℤ :=
  (DynkinType.e8DoubledSimpleRoot i j - if i = 0 then 1 else 0) / 2

private theorem two_mul_e8GlueShift (i j : Fin 8) :
    2 * e8GlueShift i j = DynkinType.e8DoubledSimpleRoot i j - if i = 0 then 1 else 0 := by
  rw [e8GlueShift, mul_comm]
  exact Int.ediv_mul_cancel (DynkinType.e8DoubledSimpleRoot_two_dvd_sub_ite i j)

/-- Every shifted glue root is an integer vector of even coordinate sum, hence a checkerboard
vector. -/
private theorem e8GlueShift_mem_checkerboardLattice (i : Fin 8) :
    (fun j ↦ ((e8GlueShift i j : ℤ) : ℚ)) ∈ (checkerboardLattice 8).carrier := by
  rw [checkerboardLattice_carrier]
  exact mem_checkerboardCarrier_of (e8GlueShift i) (fun _ ↦ rfl)
    (DynkinType.e8DoubledSimpleRoot_shift_half_sum_even i)

/-- The first glue root differs from the spinor vector by a checkerboard vector. -/
private theorem e8GlueRoot_zero_sub_spinor :
    e8GlueRoot 0 - checkerboardSpinor 8 = fun j ↦ ((e8GlueShift 0 j : ℤ) : ℚ) := by
  funext j
  have h : ((2 * e8GlueShift 0 j : ℤ) : ℚ)
      = ((DynkinType.e8DoubledSimpleRoot 0 j - 1 : ℤ) : ℚ) := by
    rw [two_mul_e8GlueShift]
    simp
  push_cast at h
  rw [Pi.sub_apply, e8GlueRoot_apply, checkerboardSpinor_apply]
  linarith

/-- Every glue root other than the first is already a checkerboard vector. -/
private theorem e8GlueRoot_of_ne_zero (i : Fin 8) (hi : i ≠ 0) :
    e8GlueRoot i = fun j ↦ ((e8GlueShift i j : ℤ) : ℚ) := by
  funext j
  have h : ((2 * e8GlueShift i j : ℤ) : ℚ)
      = ((DynkinType.e8DoubledSimpleRoot i j : ℤ) : ℚ) := by
    rw [two_mul_e8GlueShift]
    simp [hi]
  push_cast at h
  rw [e8GlueRoot_apply]
  linarith

/-- **Every glue root lies in `D₈⁺`**: the first differs from the spinor vector by a checkerboard
vector, and the other seven are checkerboard vectors. -/
theorem e8GlueRoot_mem_d8PlusCarrier (i : Fin 8) : e8GlueRoot i ∈ d8PlusCarrier.1 := by
  rw [mem_d8PlusCarrier_iff]
  rcases eq_or_ne i 0 with rfl | hi
  · exact Or.inr (e8GlueRoot_zero_sub_spinor ▸ e8GlueShift_mem_checkerboardLattice 0)
  · exact Or.inl (e8GlueRoot_of_ne_zero i hi ▸ e8GlueShift_mem_checkerboardLattice i)

/-! ## The comparison map -/

/-- The simple roots of the `E₈` root lattice are the standard coordinate vectors. -/
private theorem typeE₈SimpleRoot_eq_basisFun (i : Fin 8) :
    typeE₈SimpleRoot i = Pi.basisFun ℚ (Fin 8) i := by
  funext j
  rw [typeE₈SimpleRoot_apply, Pi.basisFun_apply, Pi.single_apply]

/-- The rational linear map sending the `i`-th simple root of the `E₈` root lattice to the `i`-th
glue root of `D₈⁺`. -/
noncomputable def e8GlueMap : (Fin 8 → ℚ) →ₗ[ℚ] (Fin 8 → ℚ) :=
  (Pi.basisFun ℚ (Fin 8)).constr ℚ e8GlueRoot

/-- The comparison map sends the `i`-th standard coordinate vector to the `i`-th glue root.

This is the internal spelling: `Pi.basisFun_apply` rewrites beneath its left-hand side, so the
exported form is the sealed simple-root one `e8GlueMap_typeE₈SimpleRoot`. -/
private theorem e8GlueMap_basisFun (i : Fin 8) :
    e8GlueMap (Pi.basisFun ℚ (Fin 8) i) = e8GlueRoot i := by
  rw [e8GlueMap]
  exact (Pi.basisFun ℚ (Fin 8)).constr_basis ℚ e8GlueRoot i

/-- The comparison map sends the `i`-th simple root of `E₈` to the `i`-th glue root. -/
@[simp]
theorem e8GlueMap_typeE₈SimpleRoot (i : Fin 8) :
    e8GlueMap (typeE₈SimpleRoot i) = e8GlueRoot i := by
  rw [typeE₈SimpleRoot_eq_basisFun]
  exact e8GlueMap_basisFun i

/-- **The comparison map intertwines the two forms**: the standard dot product pulled back along
it is the `E₈` form. -/
theorem form_comp_e8GlueMap :
    (checkerboardLattice 8).form.comp e8GlueMap e8GlueMap = typeE₈RootLattice.form := by
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℚ (Fin 8)) fun i j ↦ ?_
  rw [LinearMap.BilinForm.comp_apply, e8GlueMap_basisFun, e8GlueMap_basisFun,
    form_e8GlueRoot_e8GlueRoot, ← typeE₈SimpleRoot_eq_basisFun,
    ← typeE₈SimpleRoot_eq_basisFun, form_typeE₈SimpleRoot_typeE₈SimpleRoot]

/-- The comparison map carries the `E₈` form to the standard dot product. -/
theorem form_e8GlueMap (x y : Fin 8 → ℚ) :
    (checkerboardLattice 8).form (e8GlueMap x) (e8GlueMap y) = typeE₈RootLattice.form x y := by
  conv_rhs => rw [← form_comp_e8GlueMap]
  rw [LinearMap.BilinForm.comp_apply]

/-- The comparison map is injective, because the `E₈` form is nondegenerate. -/
private theorem e8GlueMap_injective : Function.Injective e8GlueMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine typeE₈RootLattice.form_nondegenerate.1 x fun y ↦ ?_
  rw [← form_e8GlueMap x y, hx]
  simp

/-- The comparison map as a rational linear equivalence: an injective endomorphism of a
finite-dimensional space is bijective. -/
private noncomputable def e8GlueEquiv : (Fin 8 → ℚ) ≃ₗ[ℚ] (Fin 8 → ℚ) :=
  LinearEquiv.ofBijective e8GlueMap
    ⟨e8GlueMap_injective, LinearMap.injective_iff_surjective.mp e8GlueMap_injective⟩

@[simp]
private theorem e8GlueEquiv_apply (x : Fin 8 → ℚ) : e8GlueEquiv x = e8GlueMap x := by
  rw [e8GlueEquiv]
  exact LinearEquiv.ofBijective_apply _ _

/-! ## The image of the `E₈` carrier -/

/-- The comparison equivalence carries the `E₈` carrier onto the integral span of the glue
roots. -/
private theorem map_carrier_e8GlueEquiv :
    typeE₈RootLattice.carrier.map (e8GlueEquiv.restrictScalars ℤ).toLinearMap =
      Submodule.span ℤ (Set.range e8GlueRoot) := by
  have hrange : ⇑(e8GlueEquiv.restrictScalars ℤ).toLinearMap ∘ ⇑(Pi.basisFun ℚ (Fin 8))
      = e8GlueRoot := by
    funext i
    exact (e8GlueEquiv_apply _).trans (e8GlueMap_basisFun i)
  rw [typeE₈RootLattice_carrier, Submodule.map_span, ← Set.range_comp, hrange]

private theorem span_range_e8GlueRoot_le :
    Submodule.span ℤ (Set.range e8GlueRoot) ≤ d8PlusCarrier.1 := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact e8GlueRoot_mem_d8PlusCarrier i

/-- **The glue roots span `D₈⁺` over `ℤ`.**

One inclusion is the membership of each root.  For the other, the preimage of a vector of `D₈⁺`
pairs integrally with the whole `E₈` carrier, because `D₈⁺` is an integral lattice containing the
image of that carrier; so the preimage lies in the dual of the `E₈` root lattice, which by
unimodularity is the `E₈` root lattice itself. -/
theorem span_range_e8GlueRoot :
    Submodule.span ℤ (Set.range e8GlueRoot) = d8PlusCarrier.1 := by
  refine le_antisymm span_range_e8GlueRoot_le fun x hx ↦ ?_
  have hxmem : x ∈ d8PlusLattice.carrier := by
    rw [d8PlusLattice_carrier]
    exact hx
  have hxu : e8GlueMap (e8GlueEquiv.symm x) = x := by
    rw [← e8GlueEquiv_apply]
    exact e8GlueEquiv.apply_symm_apply x
  have hdual : e8GlueEquiv.symm x ∈ typeE₈RootLattice.dualCarrier := by
    intro v hv
    have hv' : e8GlueMap v ∈ d8PlusLattice.carrier := by
      rw [d8PlusLattice_carrier]
      refine span_range_e8GlueRoot_le ?_
      rw [← map_carrier_e8GlueEquiv]
      exact ⟨v, hv, (e8GlueEquiv_apply v).symm ▸ rfl⟩
    have hpair := d8PlusLattice.le_dual hxmem (e8GlueMap v) hv'
    rw [d8PlusLattice_form] at hpair
    rwa [← form_e8GlueMap _ v, hxu]
  rw [dualCarrier_typeE₈RootLattice] at hdual
  rw [← map_carrier_e8GlueEquiv]
  exact ⟨e8GlueEquiv.symm x, hdual, (e8GlueEquiv_apply _).trans hxu⟩

/-! ## The isometry -/

/-- **The `E₈` root lattice is isometric to the spinor glue lattice `D₈⁺`.**

The underlying rational equivalence sends the `i`-th simple root of `E₈` to the `i`-th vector of
Bourbaki's plate VII in Conway--Sloane coordinates. -/
noncomputable def typeE₈IsometryD8Plus : Isometry typeE₈RootLattice d8PlusLattice where
  toIsometryEquiv :=
    { toLinearEquiv := e8GlueEquiv
      map_app' := fun x y ↦ by
        rw [d8PlusLattice_form]
        exact form_e8GlueMap x y }
  map_carrier := by
    rw [map_carrier_e8GlueEquiv, span_range_e8GlueRoot, d8PlusLattice_carrier]

@[simp]
theorem typeE₈IsometryD8Plus_apply (x : Fin 8 → ℚ) :
    typeE₈IsometryD8Plus x = e8GlueMap x := by
  rw [typeE₈IsometryD8Plus]
  exact e8GlueEquiv_apply x

/-- **The isometry sends the `i`-th `E₈` simple root to the `i`-th glue root.** -/
theorem typeE₈IsometryD8Plus_typeE₈SimpleRoot (i : Fin 8) :
    typeE₈IsometryD8Plus (typeE₈SimpleRoot i) = e8GlueRoot i := by
  rw [typeE₈IsometryD8Plus_apply, e8GlueMap_typeE₈SimpleRoot]

/-! ## Cardinality from the general overlattice comparison -/

/-- **The discriminant quadratic form of `D₈⁺` is the discriminant quadratic form of `E₈`.**

The isometry is all that this declaration states.  That the target is in turn the trivial form
on a trivial group is recorded separately, by
`instSubsingletonDiscriminantGroupTypeE₈RootLattice` and
`discriminantQuadraticMap_typeE₈RootLattice`. -/
noncomputable def d8PlusDiscriminantQuadraticIsometry :
    FiniteQuadraticModule.Isometry (d8PlusLattice.discriminantQuadraticModule isEven_d8PlusLattice)
      (typeE₈RootLattice.discriminantQuadraticModule isEven_typeE₈RootLattice) :=
  typeE₈IsometryD8Plus.symm.discriminantQuadraticIsometry isEven_d8PlusLattice

/-- **The orthogonal quotient has the cardinality predicted by the direct `E₈` computation.**

Nikulin's comparison identifies the discriminant group of the glued lattice `D₈⁺` with
`H⊥ / H` for the order-two spinor glue subgroup `H`; the isometry above identifies it with the
discriminant group of `E₈`.  This theorem records the resulting cardinality of `H⊥ / H`. -/
theorem natCard_orthogonalQuotient_d8SpinorSubgroup :
    Nat.card (((checkerboardLattice 8).discriminantQuadraticModule
      (isEven_checkerboardLattice 8)).orthogonalQuotient d8SpinorSubgroup
        isIsotropic_d8SpinorSubgroup) = 1 := by
  have hM := ((checkerboardLattice 8).isEven_intermediateCarrierOfDiscriminantSubgroup_iff
    (isEven_checkerboardLattice 8) d8SpinorSubgroup).mpr isIsotropic_d8SpinorSubgroup
  rw [natCard_orthogonalQuotient_of_subgroup (checkerboardLattice 8)
    (isEven_checkerboardLattice 8) isIsotropic_d8SpinorSubgroup,
    toIntegralLattice_eq_d8PlusLattice hM, discriminant_d8PlusLattice]

end IntegralLattice

end TauCeti
