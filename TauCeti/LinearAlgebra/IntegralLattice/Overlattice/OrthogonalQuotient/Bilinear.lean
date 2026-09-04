/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Quotient
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# The discriminant bilinear form of an integral overlattice

Let `L` be a nondegenerate integral lattice, not assumed even, and let `L ≤ M ≤ Lᵛ` be an integral
intermediate carrier, that is an integral overlattice of `L` inside the common rational ambient
space. The correspondence of `TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic`
attaches to `M` the subgroup `H = M / L` of the discriminant group `A_L = Lᵛ / L`, and integrality
of `M` is exactly isotropy of `H` for the discriminant *bilinear* form. This file computes the
discriminant bilinear module of `M` itself:

```text
A_M ≅ H⊥ / H,   H = M / L ≤ A_L.
```

The proof is the composite

```text
Mᵛ ↪ Lᵛ ↠ A_L,
```

which lands in `H⊥` because the dual of an intermediate carrier corresponds to the orthogonal
complement of its subgroup, is surjective onto `H⊥` for the same reason, and whose fibre over `H`
is exactly `M`. The composite therefore descends to an additive bijection `A_M ≃ H⊥ / H`, and it
preserves the pairing because both sides are represented by `B(x, y)` modulo `ℤ` at the same pair
of ambient vectors.

Two consequences are recorded. The order of `H⊥ / H` is the discriminant of `M`, and `M` is
unimodular exactly when `H⊥ / H` is trivial — the quotient-side reading of the Lagrangian
criterion of `TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual`. The isometry is also
restated for the overlattice `L_H` glued along a bilinear-isotropic subgroup `H ≤ A_L`, and it is
natural: an isometry `e : L ≅ L'` transports everything in sight and the resulting square
commutes.

This is the elementary intermediate-lattice analogue of the even-overlattice comparison of
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic`, and must not be
read as a statement about the quadratic discriminant form, which an odd lattice does not carry.
The two comparisons descend the same map, the discriminant class `IsIntegral.dualClassHom` of a
dual vector of `M`, along the bilinear and the quadratic orthogonal quotient of `A_L` respectively.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier.discriminantBilinearOrthogonalQuotientIsometry`:
  the isometry `A_M ≅ H⊥ / H` of finite bilinear modules.
* `TauCeti.IntegralLattice.IntermediateCarrier.discriminantBilinearOrthogonalQuotientIsometry_mk`:
  its value on the class of a vector of `Mᵛ`.
* `TauCeti.IntegralLattice.IntermediateCarrier.natCard_discriminantBilinearOrthogonalQuotient`
  and
  `subsingleton_discriminantBilinearOrthogonalQuotient_iff_isUnimodular`:
  the order of `H⊥ / H` is the discriminant of `M`, and `M` is unimodular exactly when
  `H⊥ / H` is trivial.
* `TauCeti.IntegralLattice.discriminantBilinearOrthogonalQuotientIsometryOfSubgroup`: the same
  isometry read as `A_(L_H) ≅ H⊥ / H` for a bilinear-isotropic subgroup `H` of `A_L`.
* `TauCeti.IntegralLattice.Isometry.discriminantBilinearOrthogonalQuotientIsometry_naturality`:
  the comparison isometry is natural under a lattice isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1, which is the even refinement of the comparison proved here.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {L : IntegralLattice V} [L.IsNondegenerate] {M : L.IntermediateCarrier}

namespace IntermediateCarrier

/-! ## The comparison isometry -/

variable (hM : IsIntegral M)

/-- The homomorphism `Mᵛ → H⊥ / H` sending a dual vector of `M` to the class of its discriminant
class in `A_L`. -/
private noncomputable def dualCarrierToBilinearOrthogonalQuotient :
    hM.toIntegralLattice.dualCarrier →+
      L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M) :=
  (L.discriminantBilinearModule.orthogonalQuotientMk _).comp
    (AddMonoidHom.codRestrict hM.dualClassHom.toAddMonoidHom
      (L.discriminantBilinearModule.orthogonalComplement (L.discriminantSubgroup M))
      hM.dualClassHom_mem_orthogonalComplement)

/-- The homomorphism `Mᵛ → H⊥ / H` unfolded on a vector of `Mᵛ`. -/
private theorem dualCarrierToBilinearOrthogonalQuotient_apply
    (y : hM.toIntegralLattice.dualCarrier) :
    dualCarrierToBilinearOrthogonalQuotient hM y =
      L.discriminantBilinearModule.orthogonalQuotientMk _
        ⟨hM.dualClassHom y, hM.dualClassHom_mem_orthogonalComplement y⟩ := (rfl)

/-- A dual vector of `M` has trivial class in `H⊥ / H` exactly when it already lies in `M`. -/
private theorem dualCarrierToBilinearOrthogonalQuotient_eq_zero_iff
    (y : hM.toIntegralLattice.dualCarrier) :
    dualCarrierToBilinearOrthogonalQuotient hM y = 0 ↔ (y : V) ∈ M.1 :=
  (L.discriminantBilinearModule.orthogonalQuotientMk_eq_zero_iff
      (L.discriminantSubgroup M)
      ⟨hM.dualClassHom y, hM.dualClassHom_mem_orthogonalComplement y⟩).trans (by
    -- Remove the exposed discriminant-module carrier and orthogonal-complement subtype projections.
    change hM.dualClassHom y ∈ L.discriminantSubgroup M ↔ (y : V) ∈ M.1
    rw [hM.dualClassHom_apply]
    exact L.mk_mem_discriminantSubgroup_iff M _)

/-- The induced homomorphism `A_M → H⊥ / H` on the discriminant group of the overlattice. -/
private noncomputable def discriminantBilinearOrthogonalQuotientHom :
    hM.toIntegralLattice.DiscriminantGroup →ₗ[ℤ]
      L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M) :=
  Submodule.liftQ _ (dualCarrierToBilinearOrthogonalQuotient hM).toIntLinearMap (by
    intro y hy
    rw [LinearMap.mem_ker]
    refine (dualCarrierToBilinearOrthogonalQuotient_eq_zero_iff hM y).mpr ?_
    rw [← hM.toIntegralLattice_carrier]
    exact (hM.toIntegralLattice.mem_carrierInDual_iff y).mp hy)

/-- The induced homomorphism on `A_M` is computed by its representative homomorphism. -/
private theorem discriminantBilinearOrthogonalQuotientHom_mk
    (y : hM.toIntegralLattice.dualCarrier) :
    discriminantBilinearOrthogonalQuotientHom hM (Submodule.Quotient.mk y) =
      dualCarrierToBilinearOrthogonalQuotient hM y := (rfl)

/-- A vector of `Mᵛ` whose discriminant class lies in `H` already lies in `M`, so the induced
homomorphism is injective. -/
private theorem discriminantBilinearOrthogonalQuotientHom_injective :
    Function.Injective (discriminantBilinearOrthogonalQuotientHom hM) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
  induction a using Submodule.Quotient.induction_on with
  | _ y =>
    rw [discriminantBilinearOrthogonalQuotientHom_mk,
      dualCarrierToBilinearOrthogonalQuotient_eq_zero_iff] at ha
    rw [Submodule.Quotient.mk_eq_zero, hM.toIntegralLattice.mem_carrierInDual_iff,
      hM.toIntegralLattice_carrier]
    exact ha

/-- Every class of `H⊥` is the discriminant class of a vector of `Mᵛ`, so the induced
homomorphism is surjective. -/
private theorem discriminantBilinearOrthogonalQuotientHom_surjective :
    Function.Surjective (discriminantBilinearOrthogonalQuotientHom hM) := by
  intro q
  obtain ⟨z, rfl⟩ := L.discriminantBilinearModule.orthogonalQuotientMk_surjective
    (L.discriminantSubgroup M) q
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective L.carrierInDual z.1
  have hxdual : (x : V) ∈ (dual M).1 := by
    refine (L.mk_mem_discriminantSubgroup_iff (dual M) x).mp ?_
    rw [discriminantSubgroup_dual, hx]
    exact z.2
  have hy : (x : V) ∈ hM.toIntegralLattice.dualCarrier := by
    rw [hM.toIntegralLattice_dualCarrier]
    exact hxdual
  have hclass : hM.dualClassHom ⟨(x : V), hy⟩ = z.1 := by
    rw [hM.dualClassHom_apply]
    exact hx
  refine ⟨Submodule.Quotient.mk ⟨(x : V), hy⟩, ?_⟩
  rw [discriminantBilinearOrthogonalQuotientHom_mk,
    dualCarrierToBilinearOrthogonalQuotient_apply]
  exact congrArg _ (Subtype.ext hclass)

/-- The pairing in `H⊥ / H` of the classes of two dual vectors of `M` is the ambient form
modulo `ℤ`. -/
private theorem pairing_dualCarrierToBilinearOrthogonalQuotient
    (y z : hM.toIntegralLattice.dualCarrier) :
    (L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M)).pairing
        (dualCarrierToBilinearOrthogonalQuotient hM y)
        (dualCarrierToBilinearOrthogonalQuotient hM z) =
      ((L.form y z : ℚ) : AddCircle (1 : ℚ)) := by
  refine (L.discriminantBilinearModule.orthogonalQuotient_pairing_mk
    (L.discriminantSubgroup M) _ _).trans ?_
  refine (L.discriminantBilinearModule_pairing _ _).trans ?_
  -- Remove the exposed discriminant-module carrier and orthogonal-complement subtype projections.
  change L.discriminantPairing (hM.dualClassHom y) (hM.dualClassHom z) = _
  rw [hM.dualClassHom_apply, hM.dualClassHom_apply]
  exact L.discriminantPairing_mk ⟨(y : V), hM.dualCarrier_le y.2⟩
    ⟨(z : V), hM.dualCarrier_le z.2⟩

/-- The pairing in `A_M` of the classes of two dual vectors of `M` is the ambient form
modulo `ℤ`. -/
theorem pairing_discriminantBilinearModule_toIntegralLattice_mk
    (y z : hM.toIntegralLattice.dualCarrier) :
    hM.toIntegralLattice.discriminantBilinearModule.pairing (Submodule.Quotient.mk y)
        (Submodule.Quotient.mk z) = ((L.form y z : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantBilinearModule_pairing, discriminantPairing_mk, hM.toIntegralLattice_form]

/-- **The discriminant bilinear form of an integral overlattice.** For an integral overlattice
`L ≤ M ≤ Lᵛ` with subgroup `H = M / L` of the discriminant group of `L`, the discriminant
bilinear module of `M` is `H⊥ / H`.

Neither `L` nor `M` is assumed even; this is the elementary bilinear analogue of Nikulin's
Proposition 1.4.1. -/
noncomputable def discriminantBilinearOrthogonalQuotientIsometry :
    FiniteBilinearModule.Isometry hM.toIntegralLattice.discriminantBilinearModule
      (L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M)) where
  toAddEquiv :=
    AddEquiv.ofBijective (discriminantBilinearOrthogonalQuotientHom hM).toAddMonoidHom
      ⟨discriminantBilinearOrthogonalQuotientHom_injective hM,
        discriminantBilinearOrthogonalQuotientHom_surjective hM⟩
  map_pairing' a b := by
    induction a using Submodule.Quotient.induction_on with
    | _ y =>
      induction b using Submodule.Quotient.induction_on with
      | _ z =>
        exact (pairing_dualCarrierToBilinearOrthogonalQuotient hM y z).trans
          (pairing_discriminantBilinearModule_toIntegralLattice_mk hM y z).symm

/-- **The representative formula.** The comparison isometry sends the class in `A_M` of a dual
vector of `M` to the class in `H⊥ / H` of its discriminant class in `A_L`. -/
@[simp]
theorem discriminantBilinearOrthogonalQuotientIsometry_mk
    (y : hM.toIntegralLattice.dualCarrier) :
    discriminantBilinearOrthogonalQuotientIsometry hM (Submodule.Quotient.mk y) =
      L.discriminantBilinearModule.orthogonalQuotientMk _
        ⟨hM.dualClassHom y, hM.dualClassHom_mem_orthogonalComplement y⟩ := (rfl)

/-- The pairing in `H⊥ / H` of the images of the classes of two dual vectors of `M` is the
ambient form modulo `ℤ`. -/
theorem pairing_discriminantBilinearOrthogonalQuotientIsometry_mk
    (y z : hM.toIntegralLattice.dualCarrier) :
    (L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M)).pairing
        (discriminantBilinearOrthogonalQuotientIsometry hM (Submodule.Quotient.mk y))
        (discriminantBilinearOrthogonalQuotientIsometry hM (Submodule.Quotient.mk z)) =
      ((L.form y z : ℚ) : AddCircle (1 : ℚ)) :=
  pairing_dualCarrierToBilinearOrthogonalQuotient hM y z

/-! ## Numerical consequences -/

/-- **The order of `H⊥ / H` is the discriminant of the overlattice.** -/
theorem natCard_discriminantBilinearOrthogonalQuotient :
    Nat.card (L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M)) =
      hM.toIntegralLattice.discriminant :=
  (Nat.card_congr
      (discriminantBilinearOrthogonalQuotientIsometry hM).toAddEquiv.toEquiv).symm.trans
    hM.toIntegralLattice.natCard_discriminantGroup

/-- **An integral overlattice is unimodular exactly when `H⊥ / H` is trivial.** -/
theorem subsingleton_discriminantBilinearOrthogonalQuotient_iff_isUnimodular :
    Subsingleton
        (L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup M)) ↔
      hM.toIntegralLattice.IsUnimodular := by
  rw [hM.toIntegralLattice.isUnimodular_iff_subsingleton_discriminantGroup]
  exact Equiv.subsingleton_congr
    (discriminantBilinearOrthogonalQuotientIsometry hM).toAddEquiv.toEquiv.symm

end IntermediateCarrier

open IntermediateCarrier

/-! ## The comparison isometry read on subgroups -/

variable (L)

/-- **The discriminant bilinear form of a glued integral overlattice:** `A_(L_H) ≅ H⊥ / H` for a
bilinear-isotropic subgroup `H` of the discriminant group of a nondegenerate integral lattice. -/
noncomputable def discriminantBilinearOrthogonalQuotientIsometryOfSubgroup
    {H : AddSubgroup L.DiscriminantGroup}
    (hH : L.discriminantBilinearModule.IsIsotropic H) :
    let hM := (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
    FiniteBilinearModule.Isometry hM.toIntegralLattice.discriminantBilinearModule
      (L.discriminantBilinearModule.orthogonalQuotient H) := by
  let hM := (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
  exact (discriminantBilinearOrthogonalQuotientIsometry hM).trans
    (L.discriminantBilinearModule.orthogonalQuotientCongr
      (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H))

/-- The subgroup-level comparison isometry sends a representative to its discriminant class in
`H⊥ / H`. -/
@[simp]
theorem discriminantBilinearOrthogonalQuotientIsometryOfSubgroup_mk
    {H : AddSubgroup L.DiscriminantGroup}
    (hH : L.discriminantBilinearModule.IsIsotropic H) :
    let hM := (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
    ∀ y : hM.toIntegralLattice.dualCarrier,
      L.discriminantBilinearOrthogonalQuotientIsometryOfSubgroup hH (Submodule.Quotient.mk y) =
        L.discriminantBilinearModule.orthogonalQuotientMk H
          ⟨hM.dualClassHom y,
            by
              have hmem := hM.dualClassHom_mem_orthogonalComplement y
              rw [L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup] at hmem
              exact hmem⟩ := by
  dsimp only
  intro y
  let hM := (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
  rw [discriminantBilinearOrthogonalQuotientIsometryOfSubgroup]
  refine (FiniteBilinearModule.Isometry.trans_apply _ _ _).trans ?_
  rw [discriminantBilinearOrthogonalQuotientIsometry_mk]
  exact L.discriminantBilinearModule.orthogonalQuotientCongr_orthogonalQuotientMk
    (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H)
    ⟨hM.dualClassHom y, hM.dualClassHom_mem_orthogonalComplement y⟩

/-- **The order of `H⊥ / H` is the discriminant of the overlattice glued along `H`.** -/
theorem natCard_discriminantBilinearOrthogonalQuotient_of_subgroup
    {H : AddSubgroup L.DiscriminantGroup}
    (hH : L.discriminantBilinearModule.IsIsotropic H) :
    let hM := (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
    Nat.card (L.discriminantBilinearModule.orthogonalQuotient H) =
      hM.toIntegralLattice.discriminant := by
  let hM := (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
  exact (Nat.card_congr (L.discriminantBilinearOrthogonalQuotientIsometryOfSubgroup
      hH).toAddEquiv.toEquiv).symm.trans
    hM.toIntegralLattice.natCard_discriminantGroup

variable {L}

/-! ## Naturality under a lattice isometry -/

section Naturality

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {L' : IntegralLattice W} [L'.IsNondegenerate]

namespace Isometry

/-- **Naturality of the comparison isometry `A_M ≅ H⊥ / H`, on a discriminant class.** The
equation identifies comparison after transport on `A_M` with transport after comparison. -/
theorem discriminantBilinearOrthogonalQuotientIsometry_naturality_apply (e : Isometry L L')
    {P : L.IntermediateCarrier} (hP : IntermediateCarrier.IsIntegral P)
    (q : hP.toIntegralLattice.DiscriminantGroup) :
    discriminantBilinearOrthogonalQuotientIsometry
        ((e.isIntegral_intermediateCarrierEquiv_iff P).mpr hP)
        ((e.toIntegralLatticeIsometry hP).discriminantBilinearIsometry q) =
      e.discriminantBilinearIsometry.orthogonalQuotientEquiv
        (by
          rw [discriminantBilinearIsometry_toAddEquiv]
          exact (e.discriminantSubgroup_intermediateCarrierEquiv P).symm)
        (discriminantBilinearOrthogonalQuotientIsometry hP q) := by
  symm
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    rw [discriminantBilinearOrthogonalQuotientIsometry_mk, discriminantBilinearIsometry_mk,
      discriminantBilinearOrthogonalQuotientIsometry_mk]
    refine Eq.trans (FiniteBilinearModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk
      _ _ _) ?_
    have hclass : e.discriminantBilinearIsometry (hP.dualClassHom y) =
          ((e.isIntegral_intermediateCarrierEquiv_iff P).mpr hP).dualClassHom
            ((e.toIntegralLatticeIsometry hP).dualCarrierEquiv y) := by
      rw [discriminantBilinearIsometry_apply,
        IntermediateCarrier.IsIntegral.dualClassHom_apply, discriminantGroupEquiv_mk,
        IntermediateCarrier.IsIntegral.dualClassHom_apply]
      exact congrArg _ (Subtype.ext (by simp))
    exact congrArg _ (Subtype.ext hclass)

/-- **Naturality of the comparison isometry `A_M ≅ H⊥ / H`.** An isometry `e : L ≅ L'` of
nondegenerate integral lattices transports an integral intermediate carrier `P` of `L` to one of
`L'`, and the square built from the two comparison isometries, the induced isometry of the
discriminant bilinear modules of the two overlattices, and the transported orthogonal quotient
commutes. -/
theorem discriminantBilinearOrthogonalQuotientIsometry_naturality (e : Isometry L L')
    {P : L.IntermediateCarrier} (hP : IntermediateCarrier.IsIntegral P) :
    ((e.toIntegralLatticeIsometry hP).discriminantBilinearIsometry).trans
        (discriminantBilinearOrthogonalQuotientIsometry
          ((e.isIntegral_intermediateCarrierEquiv_iff P).mpr hP)) =
      (discriminantBilinearOrthogonalQuotientIsometry hP).trans
        (e.discriminantBilinearIsometry.orthogonalQuotientEquiv
          (by
            rw [discriminantBilinearIsometry_toAddEquiv]
            exact (e.discriminantSubgroup_intermediateCarrierEquiv P).symm)) :=
  FiniteBilinearModule.Isometry.ext fun q ↦ by
    rw [FiniteBilinearModule.Isometry.trans_apply, FiniteBilinearModule.Isometry.trans_apply]
    exact e.discriminantBilinearOrthogonalQuotientIsometry_naturality_apply hP q

end Isometry

end Naturality

end IntegralLattice

end TauCeti
