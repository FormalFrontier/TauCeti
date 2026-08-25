/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# The discriminant form of an even overlattice

Let `L` be an even nondegenerate integral lattice and let `L ≤ M ≤ Lᵛ` be an even intermediate
carrier, that is an even overlattice of `L` inside the common rational ambient space. The
correspondence of `TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic` attaches to `M`
the subgroup `H = M / L` of the discriminant group `A_L = Lᵛ / L`, and evenness of `M` is exactly
isotropy of `H` for the discriminant quadratic form. This file computes the discriminant quadratic
module of `M` itself:

```text
A_M ≅ H⊥ / H,   H = M / L ≤ A_L.
```

This is the last step of Nikulin's gluing recipe, and it is what identifies the discriminant form
of a glued lattice without recomputing a dual lattice from scratch. The proof is the composite

```text
Mᵛ ↪ Lᵛ ↠ A_L,
```

which lands in `H⊥` because the dual of an intermediate carrier corresponds to the orthogonal
complement of its subgroup, is surjective onto `H⊥` for the same reason, and whose fibre over `H`
is exactly `M`. The composite therefore descends to an additive bijection `A_M ≃ H⊥ / H`, and it
preserves the half-norm quadratic form because both sides are represented by `B(x, x) / 2` modulo
`ℤ` at the same ambient vector `x`.

Two consequences are recorded. The order of `H⊥ / H` is the discriminant of `M`, and `M` is
unimodular exactly when `H⊥ / H` is trivial — the quotient-side reading of the Lagrangian
criterion of `TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual`. The isometry is also
restated for the overlattice `L_H` glued along a quadratic-isotropic subgroup `H ≤ A_L`, which is
the form in which the ADE glue calculations use it.

The comparison is natural. An isometry `e : L ≅ L'` transports the intermediate carrier `M`, and
also restricts to an isometry of the overlattices themselves; the discriminant subgroups and their
orthogonal complements correspond under the induced isometry of discriminant modules, and the
square built from the two comparison isometries commutes.

One thing is deliberately left out: the bilinear analogue for a merely integral overlattice of an
odd lattice needs the orthogonal quotient of a finite *bilinear* module, which the library does
not yet have.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier.discriminantOrthogonalQuotientIsometry`: the
  isometry `A_M ≅ H⊥ / H` of finite quadratic modules.
* `TauCeti.IntegralLattice.IntermediateCarrier.discriminantOrthogonalQuotientIsometry_mk`: its
  value on the class of a vector of `Mᵛ`.
* `TauCeti.IntegralLattice.IntermediateCarrier.natCard_orthogonalQuotient`: the order of
  `H⊥ / H` is the discriminant of `M`.
* `TauCeti.IntegralLattice.IntermediateCarrier.subsingleton_orthogonalQuotient_iff_isUnimodular`:
  `M` is unimodular exactly when `H⊥ / H` is trivial.
* `TauCeti.IntegralLattice.Isometry.discriminantOrthogonalQuotientIsometry_naturality`: the
  comparison isometry is natural under a lattice isometry.
* `TauCeti.IntegralLattice.discriminantOrthogonalQuotientIsometryOfSubgroup`: the same isometry
  read as `A_(L_H) ≅ H⊥ / H` for a quadratic-isotropic subgroup `H` of `A_L`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1, stated there in the full-norm `ℚ/2ℤ` convention.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {L : IntegralLattice V} [L.IsNondegenerate] {M : L.IntermediateCarrier}

namespace IntermediateCarrier

/-- The discriminant class in `A_L` of a vector of `Mᵛ`. -/
noncomputable def IsIntegral.dualClassHom (hM : IsIntegral M) :
    hM.toIntegralLattice.dualCarrier →ₗ[ℤ] L.DiscriminantGroup :=
  L.carrierInDual.mkQ.comp (Submodule.inclusion hM.dualCarrier_le)

@[simp]
theorem IsIntegral.dualClassHom_apply (hM : IsIntegral M)
    (y : hM.toIntegralLattice.dualCarrier) :
    hM.dualClassHom y = Submodule.Quotient.mk ⟨(y : V), hM.dualCarrier_le y.2⟩ := (rfl)

/-- The discriminant class of a vector of `Mᵛ` is orthogonal to `H = M / L`, because the dual
of an intermediate carrier corresponds to the orthogonal complement of its subgroup. -/
theorem IsIntegral.dualClassHom_mem_orthogonalComplement (hM : IsIntegral M)
    (y : hM.toIntegralLattice.dualCarrier) :
    hM.dualClassHom y ∈
      L.discriminantBilinearModule.orthogonalComplement (L.discriminantSubgroup M) := by
  rw [← discriminantSubgroup_dual, hM.dualClassHom_apply]
  exact (L.mk_mem_discriminantSubgroup_iff (dual M) _).mpr
    (by rw [← hM.toIntegralLattice_dualCarrier]; exact y.2)

/-! ## The comparison isometry -/

variable (hL : L.IsEven) (hM : IsEven M)

/-- The homomorphism `Mᵛ → H⊥ / H` sending a dual vector of `M` to the class of its discriminant
class in `A_L`. -/
private noncomputable def dualCarrierToOrthogonalQuotient :
    hM.isIntegral.toIntegralLattice.dualCarrier →+
      (L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM) :=
  ((L.discriminantQuadraticModule hL).orthogonalQuotientMk _
      ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)).comp
    (AddMonoidHom.codRestrict hM.isIntegral.dualClassHom.toAddMonoidHom
      (L.discriminantBilinearModule.orthogonalComplement (L.discriminantSubgroup M))
      hM.isIntegral.dualClassHom_mem_orthogonalComplement)

/-- The homomorphism `Mᵛ → H⊥ / H` unfolded on a vector of `Mᵛ`. -/
private theorem dualCarrierToOrthogonalQuotient_apply
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    dualCarrierToOrthogonalQuotient hL hM y =
      (L.discriminantQuadraticModule hL).orthogonalQuotientMk _
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)
        ⟨hM.isIntegral.dualClassHom y,
          hM.isIntegral.dualClassHom_mem_orthogonalComplement y⟩ := (rfl)

/-- A dual vector of `M` has trivial class in `H⊥ / H` exactly when it already lies in `M`. -/
private theorem dualCarrierToOrthogonalQuotient_eq_zero_iff
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    dualCarrierToOrthogonalQuotient hL hM y = 0 ↔ (y : V) ∈ M.1 :=
  ((L.discriminantQuadraticModule hL).orthogonalQuotientMk_eq_zero_iff
      (L.discriminantSubgroup M) ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)
      ⟨hM.isIntegral.dualClassHom y,
        hM.isIntegral.dualClassHom_mem_orthogonalComplement y⟩).trans
    (L.mk_mem_discriminantSubgroup_iff M _)

/-- The induced homomorphism `A_M → H⊥ / H` on the discriminant group of the overlattice. -/
private noncomputable def discriminantOrthogonalQuotientHom :
    hM.isIntegral.toIntegralLattice.DiscriminantGroup →ₗ[ℤ]
      (L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM) :=
  Submodule.liftQ _ (dualCarrierToOrthogonalQuotient hL hM).toIntLinearMap (by
    intro y hy
    rw [LinearMap.mem_ker]
    refine (dualCarrierToOrthogonalQuotient_eq_zero_iff hL hM y).mpr ?_
    rw [← hM.isIntegral.toIntegralLattice_carrier]
    exact (hM.isIntegral.toIntegralLattice.mem_carrierInDual_iff y).mp hy)

/-- The induced homomorphism on `A_M` is computed by its representative homomorphism. -/
private theorem discriminantOrthogonalQuotientHom_mk
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    discriminantOrthogonalQuotientHom hL hM (Submodule.Quotient.mk y) =
      dualCarrierToOrthogonalQuotient hL hM y := (rfl)

/-- A vector of `Mᵛ` whose discriminant class lies in `H` already lies in `M`, so the induced
homomorphism is injective. -/
private theorem discriminantOrthogonalQuotientHom_injective :
    Function.Injective (discriminantOrthogonalQuotientHom hL hM) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
  induction a using Submodule.Quotient.induction_on with
  | _ y =>
    rw [discriminantOrthogonalQuotientHom_mk,
      dualCarrierToOrthogonalQuotient_eq_zero_iff] at ha
    rw [Submodule.Quotient.mk_eq_zero, hM.isIntegral.toIntegralLattice.mem_carrierInDual_iff,
      hM.isIntegral.toIntegralLattice_carrier]
    exact ha

/-- Every class of `H⊥` is the discriminant class of a vector of `Mᵛ`, so the induced
homomorphism is surjective. -/
private theorem discriminantOrthogonalQuotientHom_surjective :
    Function.Surjective (discriminantOrthogonalQuotientHom hL hM) := by
  intro q
  obtain ⟨z, rfl⟩ := (L.discriminantQuadraticModule hL).orthogonalQuotientMk_surjective
    (L.discriminantSubgroup M) ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM) q
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective L.carrierInDual z.1
  have hxdual : (x : V) ∈ (dual M).1 := by
    refine (L.mk_mem_discriminantSubgroup_iff (dual M) x).mp ?_
    rw [discriminantSubgroup_dual, hx]
    exact z.2
  have hy : (x : V) ∈ hM.isIntegral.toIntegralLattice.dualCarrier := by
    rw [hM.isIntegral.toIntegralLattice_dualCarrier]
    exact hxdual
  refine ⟨Submodule.Quotient.mk ⟨(x : V), hy⟩, ?_⟩
  rw [discriminantOrthogonalQuotientHom_mk, dualCarrierToOrthogonalQuotient_apply]
  exact congrArg _ (Subtype.ext hx)

/-- The quadratic value in `H⊥ / H` of the class of a dual vector of `M` is the ambient
half-norm. -/
private theorem quadratic_dualCarrierToOrthogonalQuotient
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    ((L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)).quadratic
        (dualCarrierToOrthogonalQuotient hL hM y) =
      ((L.form y y / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  ((L.discriminantQuadraticModule hL).orthogonalQuotient_quadratic_mk
      (L.discriminantSubgroup M) ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)
      ⟨hM.isIntegral.dualClassHom y,
        hM.isIntegral.dualClassHom_mem_orthogonalComplement y⟩).trans
    ((L.discriminantQuadraticModule_quadratic hL _).trans
      (L.discriminantQuadraticMap_mk hL ⟨(y : V), hM.isIntegral.dualCarrier_le y.2⟩))

/-- The quadratic value in `A_M` of the class of a dual vector of `M` is the ambient
half-norm. -/
theorem quadratic_discriminantQuadraticModule_toIntegralLattice_mk
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    (hM.isIntegral.toIntegralLattice.discriminantQuadraticModule
        hM.isEven_toIntegralLattice).quadratic (Submodule.Quotient.mk y) =
      ((L.form y y / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticModule_quadratic, discriminantQuadraticMap_mk,
    hM.isIntegral.toIntegralLattice_form]

/-- **The discriminant form of an even overlattice.** For an even overlattice `L ≤ M ≤ Lᵛ` with
subgroup `H = M / L` of the discriminant group of `L`, the discriminant quadratic module of `M`
is `H⊥ / H`.

This is Nikulin's Proposition 1.4.1, in the half-norm `ℚ/ℤ` convention. -/
noncomputable def discriminantOrthogonalQuotientIsometry :
    FiniteQuadraticModule.Isometry
      (hM.isIntegral.toIntegralLattice.discriminantQuadraticModule
        hM.isEven_toIntegralLattice)
      ((L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)) where
  toLinearEquiv :=
    LinearEquiv.ofBijective (discriminantOrthogonalQuotientHom hL hM)
      ⟨discriminantOrthogonalQuotientHom_injective hL hM,
        discriminantOrthogonalQuotientHom_surjective hL hM⟩
  map_app' a := by
    induction a using Submodule.Quotient.induction_on with
    | _ y =>
      exact (quadratic_dualCarrierToOrthogonalQuotient hL hM y).trans
        (quadratic_discriminantQuadraticModule_toIntegralLattice_mk hM y).symm

/-- **The representative formula.** The comparison isometry sends the class in `A_M` of a dual
vector of `M` to the class in `H⊥ / H` of its discriminant class in `A_L`. -/
@[simp]
theorem discriminantOrthogonalQuotientIsometry_mk
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    discriminantOrthogonalQuotientIsometry hL hM (Submodule.Quotient.mk y) =
      (L.discriminantQuadraticModule hL).orthogonalQuotientMk _
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)
        ⟨hM.isIntegral.dualClassHom y,
          hM.isIntegral.dualClassHom_mem_orthogonalComplement y⟩ := (rfl)

/-- The quadratic value in `H⊥ / H` of the image of the class of a dual vector of `M` is the
ambient half-norm. -/
theorem quadratic_discriminantOrthogonalQuotientIsometry_mk
    (y : hM.isIntegral.toIntegralLattice.dualCarrier) :
    ((L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)).quadratic
        (discriminantOrthogonalQuotientIsometry hL hM (Submodule.Quotient.mk y)) =
      ((L.form y y / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  quadratic_dualCarrierToOrthogonalQuotient hL hM y

/-- The pairing in `H⊥ / H` of the images of the classes of two dual vectors of `M` is the
ambient form modulo `ℤ`. -/
theorem pairing_discriminantOrthogonalQuotientIsometry_mk
    (y z : hM.isIntegral.toIntegralLattice.dualCarrier) :
    ((L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)).toFiniteBilinearModule.pairing
        (discriminantOrthogonalQuotientIsometry hL hM (Submodule.Quotient.mk y))
        (discriminantOrthogonalQuotientIsometry hL hM (Submodule.Quotient.mk z)) =
      ((L.form y z : ℚ) : AddCircle (1 : ℚ)) :=
  ((L.discriminantQuadraticModule hL).orthogonalQuotient_pairing_mk
      (L.discriminantSubgroup M) ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)
      ⟨hM.isIntegral.dualClassHom y,
        hM.isIntegral.dualClassHom_mem_orthogonalComplement y⟩
      ⟨hM.isIntegral.dualClassHom z,
        hM.isIntegral.dualClassHom_mem_orthogonalComplement z⟩).trans
    ((L.discriminantBilinearModule_pairing _ _).trans
      (L.discriminantPairing_mk ⟨(y : V), hM.isIntegral.dualCarrier_le y.2⟩
        ⟨(z : V), hM.isIntegral.dualCarrier_le z.2⟩))

/-! ## Numerical consequences -/

/-- **The order of `H⊥ / H` is the discriminant of the overlattice.** -/
theorem natCard_orthogonalQuotient :
    Nat.card ((L.discriminantQuadraticModule hL).orthogonalQuotient (L.discriminantSubgroup M)
        ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)) =
      hM.isIntegral.toIntegralLattice.discriminant :=
  (Nat.card_congr
      (discriminantOrthogonalQuotientIsometry hL hM).toLinearEquiv.toEquiv).symm.trans
    hM.isIntegral.toIntegralLattice.natCard_discriminantGroup

/-- **An even overlattice is unimodular exactly when `H⊥ / H` is trivial.** -/
theorem subsingleton_orthogonalQuotient_iff_isUnimodular :
    Subsingleton ((L.discriminantQuadraticModule hL).orthogonalQuotient
        (L.discriminantSubgroup M) ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)) ↔
      hM.isIntegral.toIntegralLattice.IsUnimodular := by
  rw [hM.isIntegral.toIntegralLattice.isUnimodular_iff_subsingleton_discriminantGroup]
  exact Equiv.subsingleton_congr
    (discriminantOrthogonalQuotientIsometry hL hM).toLinearEquiv.toEquiv.symm

end IntermediateCarrier

open IntermediateCarrier

/-! ## The comparison isometry read on subgroups -/

variable (L)

/-- **The discriminant form of a glued even overlattice:** `A_(L_H) ≅ H⊥ / H` for a
quadratic-isotropic subgroup `H` of the discriminant group of an even nondegenerate lattice.

This is the form in which the ADE glue calculations use the comparison isometry. -/
noncomputable def discriminantOrthogonalQuotientIsometryOfSubgroup (hL : L.IsEven)
    {H : AddSubgroup L.DiscriminantGroup}
    (hH : (L.discriminantQuadraticModule hL).IsIsotropic H) :
    let hM := (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).mpr hH
    FiniteQuadraticModule.Isometry
      (hM.isIntegral.toIntegralLattice.discriminantQuadraticModule
        hM.isEven_toIntegralLattice)
      ((L.discriminantQuadraticModule hL).orthogonalQuotient H hH) := by
  let hM := (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).mpr hH
  exact (discriminantOrthogonalQuotientIsometry hL hM).trans
    ((L.discriminantQuadraticModule hL).orthogonalQuotientCongr
      ((isEven_iff_isIsotropic_discriminantSubgroup hL _).mp hM) hH
      (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H))

/-- The subgroup-level comparison isometry sends a representative to its discriminant class in
`H⊥ / H`. -/
@[simp]
theorem discriminantOrthogonalQuotientIsometryOfSubgroup_mk (hL : L.IsEven)
    {H : AddSubgroup L.DiscriminantGroup}
    (hH : (L.discriminantQuadraticModule hL).IsIsotropic H) :
    let hM := (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).mpr hH
    ∀ y : hM.isIntegral.toIntegralLattice.dualCarrier,
      L.discriminantOrthogonalQuotientIsometryOfSubgroup hL hH (Submodule.Quotient.mk y) =
        (L.discriminantQuadraticModule hL).orthogonalQuotientMk H hH
          ⟨hM.isIntegral.dualClassHom y,
            by
              have hmem := hM.isIntegral.dualClassHom_mem_orthogonalComplement y
              rw [L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup] at hmem
              exact hmem⟩ := by
  dsimp only
  intro y
  let hM := (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).mpr hH
  rw [discriminantOrthogonalQuotientIsometryOfSubgroup]
  refine (FiniteQuadraticModule.Isometry.trans_apply _ _ _).trans ?_
  rw [discriminantOrthogonalQuotientIsometry_mk]
  exact (L.discriminantQuadraticModule hL).orthogonalQuotientCongr_orthogonalQuotientMk
    ((isEven_iff_isIsotropic_discriminantSubgroup hL _).mp hM) hH
    (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H)
    ⟨hM.isIntegral.dualClassHom y,
      hM.isIntegral.dualClassHom_mem_orthogonalComplement y⟩

/-- **The order of `H⊥ / H` is the discriminant of the overlattice glued along `H`.** -/
theorem natCard_orthogonalQuotient_of_subgroup (hL : L.IsEven)
    {H : AddSubgroup L.DiscriminantGroup}
    (hH : (L.discriminantQuadraticModule hL).IsIsotropic H) :
    let hM := (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).mpr hH
    Nat.card ((L.discriminantQuadraticModule hL).orthogonalQuotient H hH) =
      hM.isIntegral.toIntegralLattice.discriminant := by
  let hM := (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).mpr hH
  exact (Nat.card_congr (L.discriminantOrthogonalQuotientIsometryOfSubgroup hL
      hH).toLinearEquiv.toEquiv).symm.trans
    hM.isIntegral.toIntegralLattice.natCard_discriminantGroup

variable {L}

/-! ## Naturality under a lattice isometry -/

section Naturality

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {L' : IntegralLattice W} [L'.IsNondegenerate]

namespace Isometry

/-- **Naturality of the comparison isometry `A_M ≅ H⊥ / H`, on a discriminant class.** The
equation identifies comparison after transport on `A_M` with transport after comparison. -/
theorem discriminantOrthogonalQuotientIsometry_naturality_apply (e : Isometry L L')
    (hL : L.IsEven) {P : L.IntermediateCarrier} (hP : IntermediateCarrier.IsEven P)
    (q : hP.isIntegral.toIntegralLattice.DiscriminantGroup) :
    discriminantOrthogonalQuotientIsometry (e.isEven_iff.mp hL)
        ((e.isEven_intermediateCarrierEquiv_iff P).mpr hP)
        ((e.toIntegralLatticeIsometry hP.isIntegral).discriminantQuadraticIsometry
          hP.isEven_toIntegralLattice q) =
      (e.discriminantQuadraticIsometry hL).orthogonalQuotientEquiv
        ((isEven_iff_isIsotropic_discriminantSubgroup hL P).mp hP)
        (by
          rw [discriminantQuadraticIsometry_toAddEquiv]
          exact (e.discriminantSubgroup_intermediateCarrierEquiv P).symm)
        (discriminantOrthogonalQuotientIsometry hL hP q) := by
  symm
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    rw [discriminantOrthogonalQuotientIsometry_mk, discriminantQuadraticIsometry_mk,
      discriminantOrthogonalQuotientIsometry_mk]
    refine Eq.trans (FiniteQuadraticModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk
      _ _ _ _) ?_
    have hclass : (e.discriminantQuadraticIsometry hL) (hP.isIntegral.dualClassHom y) =
          ((e.isEven_intermediateCarrierEquiv_iff P).mpr hP).isIntegral.dualClassHom
            ((e.toIntegralLatticeIsometry hP.isIntegral).dualCarrierEquiv y) := by
      rw [discriminantQuadraticIsometry_apply,
        IntermediateCarrier.IsIntegral.dualClassHom_apply, discriminantGroupEquiv_mk,
        IntermediateCarrier.IsIntegral.dualClassHom_apply]
      exact congrArg _ (Subtype.ext (by simp))
    exact congrArg _ (Subtype.ext hclass)

/-- **Naturality of the comparison isometry `A_M ≅ H⊥ / H`.** An isometry `e : L ≅ L'` of even
nondegenerate lattices transports an even intermediate carrier `P` of `L` to one of `L'`, and the
square built from the two comparison isometries, the induced isometry of the discriminant
quadratic modules of the two overlattices, and the transported orthogonal quotient commutes. -/
theorem discriminantOrthogonalQuotientIsometry_naturality (e : Isometry L L') (hL : L.IsEven)
    {P : L.IntermediateCarrier} (hP : IntermediateCarrier.IsEven P) :
    ((e.toIntegralLatticeIsometry hP.isIntegral).discriminantQuadraticIsometry
          hP.isEven_toIntegralLattice).trans
        (discriminantOrthogonalQuotientIsometry (e.isEven_iff.mp hL)
          ((e.isEven_intermediateCarrierEquiv_iff P).mpr hP)) =
        (discriminantOrthogonalQuotientIsometry hL hP).trans
        ((e.discriminantQuadraticIsometry hL).orthogonalQuotientEquiv
          ((isEven_iff_isIsotropic_discriminantSubgroup hL P).mp hP)
          (by
            rw [discriminantQuadraticIsometry_toAddEquiv]
            exact (e.discriminantSubgroup_intermediateCarrierEquiv P).symm)) :=
  DFunLike.ext _ _ fun q ↦
    e.discriminantOrthogonalQuotientIsometry_naturality_apply hL hP q

end Isometry

end Naturality

end IntegralLattice

end TauCeti
