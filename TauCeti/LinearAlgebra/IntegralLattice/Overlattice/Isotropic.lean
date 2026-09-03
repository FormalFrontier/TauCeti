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
carrier `L ≤ M ≤ Lᵛ` can enjoy: `M` is *integral* when it lies in its own dual submodule, so the
rational form pairs its vectors integrally, and `M` is *even* when the norm of each of its
vectors is twice an integer. Evenness implies integrality by polarization, mirroring the
classical fact that even lattices are integral.

The characteristic results locate both classes inside the discriminant group, in two stages. For
any integral lattice, `M` is integral exactly when the discriminant pairing vanishes on the
subgroup `M / L` of `A_L = Lᵛ / L`, and, when `L` is even, `M` is even exactly when the
discriminant quadratic map vanishes on `M / L`. When `L` is moreover nondegenerate — so that the
discriminant group packages as a finite bilinear or quadratic module — these become isotropy of
`M / L`, and restricting the intermediate-carrier order isomorphism accordingly packages the two
gluing correspondences: integral carriers correspond to bilinear-isotropic subgroups, and even
carriers of an even lattice correspond to quadratic-isotropic subgroups.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral`: integrality of an intermediate
  carrier.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsEven`: evenness of an intermediate carrier.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.toIntegralLattice`: an integral
  intermediate carrier, as an integral lattice for the same ambient form.
* `TauCeti.IntegralLattice.IntermediateCarrier.isIntegral_iff_forall_discriminantPairing_eq_zero`:
  integral carriers are cut out by vanishing of the discriminant pairing.
* `TauCeti.IntegralLattice.IntermediateCarrier.isEven_iff_forall_discriminantQuadraticMap_eq_zero`:
  even carriers of an even lattice are cut out by vanishing of the discriminant quadratic map.
* `TauCeti.IntegralLattice.IntermediateCarrier.isIntegral_iff_isIsotropic_discriminantSubgroup`,
  `TauCeti.IntegralLattice.IntermediateCarrier.isEven_iff_isIsotropic_discriminantSubgroup`: the
  isotropy forms of the two criteria, for a nondegenerate lattice.
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

/-- An intermediate carrier is integral when it lies in its own dual submodule, the shape of
`IntegralLattice.le_dual`. -/
def IsIntegral (M : L.IntermediateCarrier) : Prop :=
  M.1 ≤ L.form.dualSubmodule M.1

/-- Integrality of an intermediate carrier, unfolded to elementwise integrality of the form. -/
theorem isIntegral_def {M : L.IntermediateCarrier} :
    IsIntegral M ↔ ∀ x ∈ M.1, ∀ y ∈ M.1, L.form x y ∈ (1 : Submodule ℤ ℚ) :=
  Iff.rfl

/-- An intermediate carrier is even when every norm of its vectors is twice an integer, the
normal form of `IntegralLattice.isEven_iff_forall_norm`. -/
def IsEven (M : L.IntermediateCarrier) : Prop :=
  ∀ x ∈ M.1, ∃ n : ℤ, L.norm x = 2 * n

/-- Evenness of an intermediate carrier, unfolded to its defining property. -/
theorem isEven_def {M : L.IntermediateCarrier} :
    IsEven M ↔ ∀ x ∈ M.1, ∃ n : ℤ, L.norm x = 2 * n :=
  Iff.rfl

/-- The bottom intermediate carrier, the lattice itself, is integral. -/
@[simp]
theorem isIntegral_bot : IsIntegral (⊥ : L.IntermediateCarrier) := by
  simp only [IsIntegral, Set.Icc.coe_bot]
  exact L.le_dual

/-- The bottom intermediate carrier is even exactly when the lattice itself is even. -/
@[simp]
theorem isEven_bot_iff : IsEven (⊥ : L.IntermediateCarrier) ↔ L.IsEven := by
  rw [L.isEven_iff_forall_norm]
  constructor
  · intro h x
    exact h x (by rw [Set.Icc.coe_bot]; exact x.2)
  · intro h x hx
    rw [Set.Icc.coe_bot] at hx
    exact h ⟨x, hx⟩

/-- Integrality descends along containment of intermediate carriers. -/
theorem IsIntegral.mono {M N : L.IntermediateCarrier} (hN : IsIntegral N) (h : M ≤ N) :
    IsIntegral M := by
  have h' : M.1 ≤ N.1 := Subtype.coe_le_coe.mpr h
  rw [isIntegral_def] at hN ⊢
  intro x hx y hy
  exact hN x (h' hx) y (h' hy)

/-- Evenness descends along containment of intermediate carriers. -/
theorem IsEven.mono {M N : L.IntermediateCarrier} (hN : IsEven N) (h : M ≤ N) :
    IsEven M := fun x hx ↦ hN x (Subtype.coe_le_coe.mpr h hx)

/-- Evenness of an intermediate carrier implies its integrality, by polarization. -/
theorem IsEven.isIntegral {M : L.IntermediateCarrier} (hM : IsEven M) : IsIntegral M := by
  rw [isIntegral_def]
  intro x hx y hy
  obtain ⟨a, ha⟩ := hM (x + y) (M.1.add_mem hx hy)
  obtain ⟨b, hb⟩ := hM x hx
  obtain ⟨c, hc⟩ := hM y hy
  have hadd := L.norm_add x y
  refine Submodule.mem_one.mpr ⟨a - b - c, ?_⟩
  rw [eq_intCast]
  push_cast at ha hb hc ⊢
  linarith [hadd, ha, hb, hc]

section IsLattice

variable {M : L.IntermediateCarrier} [M.1.IsLattice ℚ]

/-- An integral intermediate carrier which is itself a full `ℤ`-lattice is an integral lattice,
for the same ambient rational form. Over a nondegenerate lattice every intermediate carrier is
such a lattice, by `TauCeti.IntegralLattice.instIsLatticeIntermediateCarrier`. -/
def IsIntegral.toIntegralLattice (hM : IsIntegral M) : IntegralLattice V :=
  IntegralLattice.ofSubmodule M.1 L.form L.isSymm fun _ hx ↦
    L.form.mem_dualSubmodule.mpr fun _ hy ↦ isIntegral_def.mp hM _ hx _ hy

/-- The carrier of the integral lattice attached to an integral intermediate carrier. -/
@[simp]
theorem IsIntegral.toIntegralLattice_carrier (hM : IsIntegral M) :
    hM.toIntegralLattice.carrier = M.1 := by
  rw [toIntegralLattice, IntegralLattice.ofSubmodule_carrier]

/-- The integral lattice attached to an integral intermediate carrier keeps the ambient form. -/
@[simp]
theorem IsIntegral.toIntegralLattice_form (hM : IsIntegral M) :
    hM.toIntegralLattice.form = L.form := by
  rw [toIntegralLattice, IntegralLattice.ofSubmodule_form]

/-- Regarding the lattice itself as an intermediate carrier returns the lattice. -/
@[simp]
theorem IsIntegral.toIntegralLattice_bot (hM : IsIntegral (⊥ : L.IntermediateCarrier)) :
    hM.toIntegralLattice = L :=
  IntegralLattice.ext
    (by rw [hM.toIntegralLattice_carrier, Set.Icc.coe_bot]) hM.toIntegralLattice_form

/-- An even intermediate carrier is an even integral lattice. -/
theorem IsEven.isEven_toIntegralLattice (hM : IsEven M) :
    hM.isIntegral.toIntegralLattice.IsEven := by
  rw [isEven_iff_forall_norm]
  intro x
  have hx : (x : V) ∈ M.1 := by
    rw [← hM.isIntegral.toIntegralLattice_carrier]
    exact x.2
  obtain ⟨n, hn⟩ := isEven_def.mp hM (x : V) hx
  exact ⟨n, by rw [norm_apply, IsIntegral.toIntegralLattice_form, ← norm_apply]; exact hn⟩

end IsLattice

/-- An overlattice of a nondegenerate integral lattice is nondegenerate: it carries the same
ambient form. -/
instance IsIntegral.instIsNondegenerate [L.IsNondegenerate] {M : L.IntermediateCarrier}
    (hM : IsIntegral M) : hM.toIntegralLattice.IsNondegenerate :=
  ⟨by rw [hM.toIntegralLattice_form]; exact L.form_nondegenerate⟩

/-- **Integrality is vanishing of the discriminant pairing.** An intermediate carrier is
integral exactly when the discriminant pairing vanishes on its subgroup of the discriminant
group. No nondegeneracy is required. -/
theorem isIntegral_iff_forall_discriminantPairing_eq_zero (M : L.IntermediateCarrier) :
    IsIntegral M ↔ ∀ x ∈ L.discriminantSubgroup M, ∀ y ∈ L.discriminantSubgroup M,
      L.discriminantPairing x y = 0 := by
  rw [isIntegral_def]
  constructor
  · intro hM x hx y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact (L.discriminantPairing_mk_eq_zero_iff x y).mpr
      (hM x ((L.mk_mem_discriminantSubgroup_iff M x).mp hx) y
        ((L.mk_mem_discriminantSubgroup_iff M y).mp hy))
  · intro hH x hx y hy
    have hxd : x ∈ L.dualCarrier := M.2.2 hx
    have hyd : y ∈ L.dualCarrier := M.2.2 hy
    exact (L.discriminantPairing_mk_eq_zero_iff ⟨x, hxd⟩ ⟨y, hyd⟩).mp
      (hH _ ((L.mk_mem_discriminantSubgroup_iff M ⟨x, hxd⟩).mpr hx)
        _ ((L.mk_mem_discriminantSubgroup_iff M ⟨y, hyd⟩).mpr hy))

/-- **Evenness is vanishing of the discriminant quadratic map.** For an even lattice, an
intermediate carrier is even exactly when the discriminant quadratic map vanishes on its
subgroup of the discriminant group. No nondegeneracy is required. -/
theorem isEven_iff_forall_discriminantQuadraticMap_eq_zero (hL : L.IsEven)
    (M : L.IntermediateCarrier) :
    IsEven M ↔ ∀ x ∈ L.discriminantSubgroup M, L.discriminantQuadraticMap hL x = 0 := by
  constructor
  · intro hM x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := hM x ((L.mk_mem_discriminantSubgroup_iff M x).mp hx)
    refine (L.discriminantQuadraticMap_mk_eq_zero_iff hL x).mpr ⟨n, ?_⟩
    rw [← L.norm_apply, hn]
    push_cast
    ring
  · intro hH x hx
    have hxd : x ∈ L.dualCarrier := M.2.2 hx
    obtain ⟨n, hn⟩ := (L.discriminantQuadraticMap_mk_eq_zero_iff hL ⟨x, hxd⟩).mp
      (hH _ ((L.mk_mem_discriminantSubgroup_iff M ⟨x, hxd⟩).mpr hx))
    refine ⟨n, ?_⟩
    rw [L.norm_apply]
    simpa using hn

variable [L.IsNondegenerate]

/-- **Integrality is bilinear isotropy.** For a nondegenerate lattice, an intermediate carrier
is integral exactly when its subgroup of the discriminant group is isotropic in the discriminant
bilinear module. -/
theorem isIntegral_iff_isIsotropic_discriminantSubgroup (M : L.IntermediateCarrier) :
    IsIntegral M ↔ L.discriminantBilinearModule.IsIsotropic (L.discriminantSubgroup M) := by
  rw [isIntegral_iff_forall_discriminantPairing_eq_zero]
  constructor
  · intro h
    exact L.discriminantBilinearModule.isIsotropic_def.mpr fun x hx y hy ↦
      (L.discriminantBilinearModule_pairing x y).trans (h x hx y hy)
  · intro h x hx y hy
    exact (L.discriminantBilinearModule_pairing x y).symm.trans
      (L.discriminantBilinearModule.isIsotropic_def.mp h x hx y hy)

/-- **Evenness is quadratic isotropy.** For an even nondegenerate lattice, an intermediate
carrier is even exactly when its subgroup of the discriminant group is isotropic in the
discriminant quadratic module. -/
theorem isEven_iff_isIsotropic_discriminantSubgroup (hL : L.IsEven) (M : L.IntermediateCarrier) :
    IsEven M ↔ (L.discriminantQuadraticModule hL).IsIsotropic (L.discriminantSubgroup M) := by
  rw [isEven_iff_forall_discriminantQuadraticMap_eq_zero hL]
  constructor
  · intro h
    exact (L.discriminantQuadraticModule hL).isIsotropic_def.mpr fun x hx ↦
      (L.discriminantQuadraticModule_quadratic hL x).trans (h x hx)
  · intro h x hx
    exact (L.discriminantQuadraticModule_quadratic hL x).symm.trans
      ((L.discriminantQuadraticModule hL).isIsotropic_def.mp h x hx)

end IntermediateCarrier

open IntermediateCarrier

variable (L : IntegralLattice V)

/-- Restrict the intermediate-carrier order isomorphism along a predicate characterization: a
predicate on carriers matching a predicate on discriminant subgroups induces an order
isomorphism of the corresponding subtypes. -/
private def restrictOrderIso {p : L.IntermediateCarrier → Prop}
    {q : AddSubgroup L.DiscriminantGroup → Prop}
    (h : ∀ M, p M ↔ q (L.discriminantSubgroup M)) :
    {M : L.IntermediateCarrier // p M} ≃o {H : AddSubgroup L.DiscriminantGroup // q H} where
  toEquiv :=
    { toFun := fun M ↦ ⟨L.discriminantSubgroup M.1, (h M.1).mp M.2⟩
      invFun := fun H ↦ ⟨L.intermediateCarrierOfDiscriminantSubgroup H.1, (h _).mpr (by
        rw [L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]
        exact H.2)⟩
      left_inv := fun M ↦ Subtype.ext
        (L.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup M.1)
      right_inv := fun H ↦ Subtype.ext
        (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H.1) }
  map_rel_iff' {M N} := by
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, L.discriminantSubgroup_le_iff]
    exact Subtype.coe_le_coe

variable [L.IsNondegenerate]

/-- The inverse-image carrier of a subgroup is integral exactly when the subgroup is
bilinear-isotropic. -/
@[simp]
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
      {H : AddSubgroup L.DiscriminantGroup // L.discriminantBilinearModule.IsIsotropic H} :=
  L.restrictOrderIso fun M ↦ isIntegral_iff_isIsotropic_discriminantSubgroup M

/-- The restricted integral-carrier order isomorphism acts by the discriminant-subgroup
construction. -/
@[simp]
theorem integralIntermediateCarrierOrderIsoIsotropicSubgroup_apply_coe
    (M : {M : L.IntermediateCarrier // IsIntegral M}) :
    (L.integralIntermediateCarrierOrderIsoIsotropicSubgroup M :
      AddSubgroup L.DiscriminantGroup) = L.discriminantSubgroup M.1 := by
  simp only [integralIntermediateCarrierOrderIsoIsotropicSubgroup, restrictOrderIso,
    RelIso.coe_fn_mk, Equiv.coe_fn_mk]

/-- The inverse of the restricted integral-carrier order isomorphism acts by the inverse-image
construction. -/
@[simp]
theorem integralIntermediateCarrierOrderIsoIsotropicSubgroup_symm_apply_coe
    (H : {H : AddSubgroup L.DiscriminantGroup // L.discriminantBilinearModule.IsIsotropic H}) :
    (L.integralIntermediateCarrierOrderIsoIsotropicSubgroup.symm H : L.IntermediateCarrier) =
      L.intermediateCarrierOfDiscriminantSubgroup H.1 := by
  simp only [integralIntermediateCarrierOrderIsoIsotropicSubgroup, restrictOrderIso,
    OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]

/-- **Even overlattices correspond to quadratic-isotropic subgroups.** For an even lattice, the
intermediate-carrier order isomorphism restricts to the even carriers on one side and the
quadratic-isotropic subgroups of the discriminant group on the other. -/
def evenIntermediateCarrierOrderIsoIsotropicSubgroup (hL : L.IsEven) :
    {M : L.IntermediateCarrier // IntermediateCarrier.IsEven M} ≃o
      {H : AddSubgroup L.DiscriminantGroup //
        (L.discriminantQuadraticModule hL).IsIsotropic H} :=
  L.restrictOrderIso fun M ↦ isEven_iff_isIsotropic_discriminantSubgroup hL M

/-- The restricted even-carrier order isomorphism acts by the discriminant-subgroup
construction. -/
@[simp]
theorem evenIntermediateCarrierOrderIsoIsotropicSubgroup_apply_coe (hL : L.IsEven)
    (M : {M : L.IntermediateCarrier // IntermediateCarrier.IsEven M}) :
    (L.evenIntermediateCarrierOrderIsoIsotropicSubgroup hL M :
      AddSubgroup L.DiscriminantGroup) = L.discriminantSubgroup M.1 := by
  simp only [evenIntermediateCarrierOrderIsoIsotropicSubgroup, restrictOrderIso,
    RelIso.coe_fn_mk, Equiv.coe_fn_mk]

/-- The inverse of the restricted even-carrier order isomorphism acts by the inverse-image
construction. -/
@[simp]
theorem evenIntermediateCarrierOrderIsoIsotropicSubgroup_symm_apply_coe (hL : L.IsEven)
    (H : {H : AddSubgroup L.DiscriminantGroup //
      (L.discriminantQuadraticModule hL).IsIsotropic H}) :
    ((L.evenIntermediateCarrierOrderIsoIsotropicSubgroup hL).symm H : L.IntermediateCarrier) =
      L.intermediateCarrierOfDiscriminantSubgroup H.1 := by
  simp only [evenIntermediateCarrierOrderIsoIsotropicSubgroup, restrictOrderIso,
    OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]

end IntegralLattice

end TauCeti
