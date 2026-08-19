/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Basic

/-!
# Integral and even overlattices via isotropic subgroups

Let `L` be an integral lattice. This file refines the intermediate-carrier correspondence of
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Basic` by the two properties an intermediate
carrier `L ≤ M ≤ Lᵛ` can enjoy: `M` is *integral* when the rational form takes integer values on
pairs of its vectors, and `M` is *even* when every self-pairing of its vectors is an even integer.
Evenness implies integrality by polarization, mirroring the classical fact that even lattices are
integral.

The characteristic results locate both classes inside the discriminant group. A carrier `M` is
integral exactly when the discriminant bilinear pairing vanishes on the subgroup `M / L` of
`A_L = Lᵛ / L`, and, when `L` is even, `M` is even exactly when the discriminant quadratic map
vanishes on `M / L`. Restricting the intermediate-carrier order isomorphism accordingly packages
the two gluing correspondences: integral carriers correspond to bilinear-isotropic subgroups, and
even carriers of an even lattice correspond to quadratic-isotropic subgroups.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral`: integrality of an intermediate
  carrier.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsEven`: evenness of an intermediate carrier.
* `TauCeti.IntegralLattice.IntermediateCarrier.isIntegral_iff_isIsotropic_discriminantSubgroup`:
  integral carriers are cut out by bilinear isotropy in the discriminant group.
* `TauCeti.IntegralLattice.IntermediateCarrier.isEven_iff_isIsotropic_discriminantSubgroup`: even
  carriers of an even lattice are cut out by quadratic isotropy in the discriminant group.
* `TauCeti.IntegralLattice.integralIntermediateCarrierOrderIsoIsotropicSubgroup`: the restriction
  of the intermediate-carrier order isomorphism to integral carriers.
* `TauCeti.IntegralLattice.evenIntermediateCarrierOrderIsoIsotropicSubgroup`: the restriction of
  the intermediate-carrier order isomorphism to even carriers of an even lattice.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1. The quadratic statement here is that proposition in the half-norm `ℚ/ℤ`
  convention; the bilinear statement is its elementary intermediate-lattice analogue.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
* `TauCetiRoadmap/IntegralLattices/Suggested.lean` (`integralOverlatticeEquivIsotropicSubgroup`,
  `evenOverlatticeEquivIsotropicSubgroup`).
-/

public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace IntermediateCarrier

/-- An intermediate carrier is integral when the rational form pairs its vectors integrally. -/
def IsIntegral (M : L.IntermediateCarrier) : Prop :=
  ∀ x ∈ M.1, ∀ y ∈ M.1, L.form x y ∈ (1 : Submodule ℤ ℚ)

/-- Integrality of an intermediate carrier, unfolded to its defining property. -/
theorem isIntegral_def {M : L.IntermediateCarrier} :
    IsIntegral M ↔ ∀ x ∈ M.1, ∀ y ∈ M.1, L.form x y ∈ (1 : Submodule ℤ ℚ) :=
  Iff.rfl

/-- An intermediate carrier is even when every self-pairing of its vectors is an even integer. -/
def IsEven (M : L.IntermediateCarrier) : Prop :=
  ∀ x ∈ M.1, ∃ n : ℤ, L.form x x = ((2 * n : ℤ) : ℚ)

/-- Evenness of an intermediate carrier, unfolded to its defining property. -/
theorem isEven_def {M : L.IntermediateCarrier} :
    IsEven M ↔ ∀ x ∈ M.1, ∃ n : ℤ, L.form x x = ((2 * n : ℤ) : ℚ) :=
  Iff.rfl

/-- The bottom intermediate carrier, the lattice itself, is integral. -/
theorem isIntegral_bot : IsIntegral (⊥ : L.IntermediateCarrier) := by
  intro x hx y hy
  rw [Set.Icc.coe_bot] at hx hy
  exact L.le_dual hx y hy

/-- The bottom intermediate carrier is even exactly when the lattice itself is even. -/
theorem isEven_bot_iff : IsEven (⊥ : L.IntermediateCarrier) ↔ L.IsEven := by
  rw [L.isEven_iff_forall_norm]
  constructor
  · intro h x
    obtain ⟨n, hn⟩ := h (x : V) (by rw [Set.Icc.coe_bot]; exact x.2)
    refine ⟨n, ?_⟩
    rw [L.norm_apply, hn]
    push_cast
    ring
  · intro h x hx
    rw [Set.Icc.coe_bot] at hx
    obtain ⟨n, hn⟩ := h ⟨x, hx⟩
    rw [L.norm_apply] at hn
    refine ⟨n, ?_⟩
    push_cast
    simpa using hn

/-- Evenness of an intermediate carrier implies its integrality, by polarization. -/
theorem IsEven.isIntegral {M : L.IntermediateCarrier} (hM : IsEven M) : IsIntegral M := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := hM (x + y) (M.1.add_mem hx hy)
  obtain ⟨b, hb⟩ := hM x hx
  obtain ⟨c, hc⟩ := hM y hy
  have hexpand : L.form (x + y) (x + y) =
      L.form x x + L.form x y + (L.form y x + L.form y y) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  have hyx : L.form y x = L.form x y := by simpa using L.isSymm.eq y x
  refine Submodule.mem_one.mpr ⟨a - b - c, ?_⟩
  rw [eq_intCast]
  push_cast at ha hb hc ⊢
  linarith [hexpand, hyx, ha, hb, hc]

variable [L.IsNondegenerate]

/-- **Integrality is bilinear isotropy.** An intermediate carrier is integral exactly when the
discriminant bilinear pairing vanishes on its subgroup of the discriminant group. -/
theorem isIntegral_iff_isIsotropic_discriminantSubgroup (M : L.IntermediateCarrier) :
    IsIntegral M ↔ L.discriminantBilinearModule.IsIsotropic (L.discriminantSubgroup M) := by
  constructor
  · intro hM
    refine L.discriminantBilinearModule.isIsotropic_def.mpr ?_
    intro x hx y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [discriminantBilinearModule_pairing, discriminantPairing_mk]
    exact (coe_eq_zero_iff_mem_one _).mpr
      (hM x ((L.mk_mem_discriminantSubgroup_iff M x).mp hx) y
        ((L.mk_mem_discriminantSubgroup_iff M y).mp hy))
  · intro hH x hx y hy
    have hxd : x ∈ L.dualCarrier := M.2.2 hx
    have hyd : y ∈ L.dualCarrier := M.2.2 hy
    have h0 := L.discriminantBilinearModule.isIsotropic_def.mp hH (Submodule.Quotient.mk ⟨x, hxd⟩)
      ((L.mk_mem_discriminantSubgroup_iff M ⟨x, hxd⟩).mpr hx)
      (Submodule.Quotient.mk ⟨y, hyd⟩)
      ((L.mk_mem_discriminantSubgroup_iff M ⟨y, hyd⟩).mpr hy)
    rw [discriminantBilinearModule_pairing, discriminantPairing_mk] at h0
    exact (coe_eq_zero_iff_mem_one _).mp h0

/-- **Evenness is quadratic isotropy.** For an even lattice, an intermediate carrier is even
exactly when the discriminant quadratic map vanishes on its subgroup of the discriminant group. -/
theorem isEven_iff_isIsotropic_discriminantSubgroup (hL : L.IsEven) (M : L.IntermediateCarrier) :
    IsEven M ↔ (L.discriminantQuadraticModule hL).IsIsotropic (L.discriminantSubgroup M) := by
  constructor
  · intro hM
    refine (L.discriminantQuadraticModule hL).isIsotropic_def.mpr ?_
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [discriminantQuadraticModule_quadratic, discriminantQuadraticMap_mk]
    obtain ⟨n, hn⟩ := hM x ((L.mk_mem_discriminantSubgroup_iff M x).mp hx)
    refine (coe_eq_zero_iff_mem_one _).mpr (Submodule.mem_one.mpr ⟨n, ?_⟩)
    rw [eq_intCast, hn]
    push_cast
    ring
  · intro hH x hx
    have hxd : x ∈ L.dualCarrier := M.2.2 hx
    have h0 := (L.discriminantQuadraticModule hL).isIsotropic_def.mp hH
      (Submodule.Quotient.mk ⟨x, hxd⟩)
      ((L.mk_mem_discriminantSubgroup_iff M ⟨x, hxd⟩).mpr hx)
    rw [discriminantQuadraticModule_quadratic, discriminantQuadraticMap_mk] at h0
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp ((coe_eq_zero_iff_mem_one _).mp h0)
    rw [eq_intCast] at hn
    refine ⟨n, ?_⟩
    have hn' : (n : ℚ) = L.form x x / 2 := by simpa using hn
    push_cast
    linarith [hn']

end IntermediateCarrier

open IntermediateCarrier

variable (L : IntegralLattice V) [L.IsNondegenerate]

/-- The inverse-image carrier of a subgroup is integral exactly when the subgroup is
bilinear-isotropic. -/
theorem isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff
    (H : AddSubgroup L.DiscriminantGroup) :
    IsIntegral (L.intermediateCarrierOfDiscriminantSubgroup H) ↔
      L.discriminantBilinearModule.IsIsotropic H := by
  rw [isIntegral_iff_isIsotropic_discriminantSubgroup,
    L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]

/-- For an even lattice, the inverse-image carrier of a subgroup is even exactly when the
subgroup is quadratic-isotropic. -/
theorem isEven_intermediateCarrierOfDiscriminantSubgroup_iff (hL : L.IsEven)
    (H : AddSubgroup L.DiscriminantGroup) :
    IntermediateCarrier.IsEven (L.intermediateCarrierOfDiscriminantSubgroup H) ↔
      (L.discriminantQuadraticModule hL).IsIsotropic H := by
  rw [isEven_iff_isIsotropic_discriminantSubgroup hL,
    L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]

/-- **Integral overlattices correspond to bilinear-isotropic subgroups.** The intermediate-carrier
order isomorphism restricts to the integral carriers on one side and the bilinear-isotropic
subgroups of the discriminant group on the other. -/
def integralIntermediateCarrierOrderIsoIsotropicSubgroup :
    {M : L.IntermediateCarrier // IsIntegral M} ≃o
      {H : AddSubgroup L.DiscriminantGroup // L.discriminantBilinearModule.IsIsotropic H} where
  toEquiv :=
    { toFun := fun M ↦ ⟨L.discriminantSubgroup M.1,
        (isIntegral_iff_isIsotropic_discriminantSubgroup M.1).mp M.2⟩
      invFun := fun H ↦ ⟨L.intermediateCarrierOfDiscriminantSubgroup H.1,
        (L.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H.1).mpr H.2⟩
      left_inv := fun M ↦ Subtype.ext
        (L.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup M.1)
      right_inv := fun H ↦ Subtype.ext
        (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H.1) }
  map_rel_iff' {M N} := by
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, L.discriminantSubgroup_le_iff]
    exact Subtype.coe_le_coe

/-- The restricted integral-carrier order isomorphism acts by the discriminant-subgroup
construction. -/
@[simp]
theorem integralIntermediateCarrierOrderIsoIsotropicSubgroup_apply_coe
    (M : {M : L.IntermediateCarrier // IsIntegral M}) :
    (L.integralIntermediateCarrierOrderIsoIsotropicSubgroup M :
      AddSubgroup L.DiscriminantGroup) = L.discriminantSubgroup M.1 := by
  simp only [integralIntermediateCarrierOrderIsoIsotropicSubgroup, RelIso.coe_fn_mk,
    Equiv.coe_fn_mk]

/-- The inverse of the restricted integral-carrier order isomorphism acts by the inverse-image
construction. -/
@[simp]
theorem integralIntermediateCarrierOrderIsoIsotropicSubgroup_symm_apply_coe
    (H : {H : AddSubgroup L.DiscriminantGroup // L.discriminantBilinearModule.IsIsotropic H}) :
    (L.integralIntermediateCarrierOrderIsoIsotropicSubgroup.symm H : L.IntermediateCarrier) =
      L.intermediateCarrierOfDiscriminantSubgroup H.1 := by
  simp only [integralIntermediateCarrierOrderIsoIsotropicSubgroup, OrderIso.symm_mk,
    RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]

/-- **Even overlattices correspond to quadratic-isotropic subgroups.** For an even lattice, the
intermediate-carrier order isomorphism restricts to the even carriers on one side and the
quadratic-isotropic subgroups of the discriminant group on the other. -/
def evenIntermediateCarrierOrderIsoIsotropicSubgroup (hL : L.IsEven) :
    {M : L.IntermediateCarrier // IntermediateCarrier.IsEven M} ≃o
      {H : AddSubgroup L.DiscriminantGroup //
        (L.discriminantQuadraticModule hL).IsIsotropic H} where
  toEquiv :=
    { toFun := fun M ↦ ⟨L.discriminantSubgroup M.1,
        (isEven_iff_isIsotropic_discriminantSubgroup hL M.1).mp M.2⟩
      invFun := fun H ↦ ⟨L.intermediateCarrierOfDiscriminantSubgroup H.1,
        (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H.1).mpr H.2⟩
      left_inv := fun M ↦ Subtype.ext
        (L.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup M.1)
      right_inv := fun H ↦ Subtype.ext
        (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H.1) }
  map_rel_iff' {M N} := by
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, L.discriminantSubgroup_le_iff]
    exact Subtype.coe_le_coe

/-- The restricted even-carrier order isomorphism acts by the discriminant-subgroup
construction. -/
@[simp]
theorem evenIntermediateCarrierOrderIsoIsotropicSubgroup_apply_coe (hL : L.IsEven)
    (M : {M : L.IntermediateCarrier // IntermediateCarrier.IsEven M}) :
    (L.evenIntermediateCarrierOrderIsoIsotropicSubgroup hL M :
      AddSubgroup L.DiscriminantGroup) = L.discriminantSubgroup M.1 := by
  simp only [evenIntermediateCarrierOrderIsoIsotropicSubgroup, RelIso.coe_fn_mk,
    Equiv.coe_fn_mk]

/-- The inverse of the restricted even-carrier order isomorphism acts by the inverse-image
construction. -/
@[simp]
theorem evenIntermediateCarrierOrderIsoIsotropicSubgroup_symm_apply_coe (hL : L.IsEven)
    (H : {H : AddSubgroup L.DiscriminantGroup //
      (L.discriminantQuadraticModule hL).IsIsotropic H}) :
    ((L.evenIntermediateCarrierOrderIsoIsotropicSubgroup hL).symm H : L.IntermediateCarrier) =
      L.intermediateCarrierOfDiscriminantSubgroup H.1 := by
  simp only [evenIntermediateCarrierOrderIsoIsotropicSubgroup, OrderIso.symm_mk,
    RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]

end IntegralLattice

end TauCeti
