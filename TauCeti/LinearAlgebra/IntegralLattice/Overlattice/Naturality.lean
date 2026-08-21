/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic

/-!
# Naturality of the overlattice correspondence

The intermediate-carrier correspondence of
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Basic` attaches to an integral lattice `L` the
order isomorphism between carriers `L ≤ P ≤ Lᵛ` and subgroups of `A_L = Lᵛ / L`, and
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic` cuts out the integral and even
carriers inside it. This file proves that the whole package is natural, in the two directions the
theory uses it.

An isometry `e : L ≃ M` transports intermediate carriers along its ambient equivalence, and the
resulting order isomorphism commutes with the discriminant-subgroup correspondence: the subgroup
of `A_M` attached to `e(P)` is the image of the subgroup of `A_L` attached to `P` under the
induced equivalence `A_L ≃ A_M`. Integrality and evenness of an intermediate carrier are
invariants of the transport, so the two refined correspondences are natural as well. For
nondegenerate lattices, orthogonal complements and isotropy transport directly through the
generic finite-bilinear-module API applied to the induced discriminant bilinear isometry.

For an orthogonal direct sum, a pair of intermediate carriers assembles into the intermediate
carrier `P₁ ⊕ P₂` of `L ⊥ M`, order-embedding the pairs into the carriers of the sum. Its
subgroup of `A_(L ⊥ M) ≃ A_L × A_M` is the product subgroup, and it is integral, respectively
even, exactly when both components are.

## Main declarations

* `TauCeti.IntegralLattice.Isometry.intermediateCarrierEquiv`: transport of intermediate carriers
  along a lattice isometry.
* `TauCeti.IntegralLattice.Isometry.discriminantSubgroup_intermediateCarrierEquiv` and
  `IntegralLattice.Isometry.intermediateCarrierEquiv_intermediateCarrierOfDiscriminantSubgroup`:
  the transport commutes with the discriminant-subgroup correspondence and with its inverse-image
  construction.
* `TauCeti.IntegralLattice.Isometry.isIntegral_intermediateCarrierEquiv_iff` and
  `TauCeti.IntegralLattice.Isometry.isEven_intermediateCarrierEquiv_iff`: integrality and evenness
  of an intermediate carrier are isometry invariants.
* `TauCeti.IntegralLattice.Isometry.integralIntermediateCarrierEquiv` and
  `TauCeti.IntegralLattice.Isometry.evenIntermediateCarrierEquiv`: the corresponding transports
  restricted to integral and even intermediate carriers.
* `TauCeti.IntegralLattice.orthogonalSumIntermediateCarrier`: the intermediate carrier of an
  orthogonal sum assembled from a pair of intermediate carriers.
* `TauCeti.IntegralLattice.map_discriminantSubgroup_orthogonalSumIntermediateCarrier` and
  `IntegralLattice.orthogonalSumIntermediateCarrier_intermediateCarrierOfDiscriminantSubgroup`:
  its subgroup of the discriminant group is the product subgroup, in both directions.
* `TauCeti.IntegralLattice.isIntegral_orthogonalSumIntermediateCarrier_iff` and
  `TauCeti.IntegralLattice.isEven_orthogonalSumIntermediateCarrier_iff`: integrality and evenness
  of an assembled carrier are componentwise.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} {W : Type v} {U : Type w}
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]

/-! ## Transport along a lattice isometry -/

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- **An isometry transports intermediate carriers.** The ambient equivalence of a lattice
isometry maps the carrier onto the carrier and the dual carrier onto the dual carrier, so it
restricts to an order isomorphism between the intervals of intermediate carriers. -/
def intermediateCarrierEquiv (e : Isometry L M) :
    L.IntermediateCarrier ≃o M.IntermediateCarrier :=
  (OrderIso.Icc (Submodule.orderIsoMapComap e.ambientEquiv) L.carrier L.dualCarrier).trans
    (OrderIso.setCongr _ _ (by
      simp only [Submodule.orderIsoMapComap_apply]
      have hambient : e.ambientEquiv.toLinearMap =
          ((e : V ≃ₗ[ℚ] W).restrictScalars ℤ).toLinearMap := by
        ext x
        simp
      rw [e.map_dualCarrier_ambientEquiv, hambient, e.map_carrier]))

/-- The carrier transported along an isometry is the image of the original carrier. -/
theorem intermediateCarrierEquiv_apply_coe (e : Isometry L M) (P : L.IntermediateCarrier) :
    (e.intermediateCarrierEquiv P).1 = P.1.map e.ambientEquiv.toLinearMap :=
  -- Mathlib's `OrderIso.Icc` and `OrderIso.setCongr` both act by the underlying map on the
  -- coerced element, and `⇑e.ambientEquiv` is `⇑e.ambientEquiv.toLinearMap`, so both sides are
  -- definitionally the same submodule. The parentheses keep `intermediateCarrierEquiv` sealed.
  (rfl)

/-- Membership in a transported carrier is membership of the preimage in the original carrier. -/
@[simp]
theorem mem_intermediateCarrierEquiv_iff (e : Isometry L M) (P : L.IntermediateCarrier) (y : W) :
    y ∈ (e.intermediateCarrierEquiv P).1 ↔ e.symm y ∈ P.1 := by
  rw [intermediateCarrierEquiv_apply_coe, Submodule.mem_map_equiv]
  simp

/-- The image of a vector lies in the transported carrier exactly when the vector lies in the
original carrier. -/
theorem apply_mem_intermediateCarrierEquiv_iff (e : Isometry L M) (P : L.IntermediateCarrier)
    (x : V) : e x ∈ (e.intermediateCarrierEquiv P).1 ↔ x ∈ P.1 := by
  rw [mem_intermediateCarrierEquiv_iff, symm_apply_apply]

/-- The identity isometry transports every intermediate carrier to itself. -/
@[simp]
theorem intermediateCarrierEquiv_refl (L : IntegralLattice V) :
    (Isometry.refl L).intermediateCarrierEquiv = OrderIso.refl L.IntermediateCarrier := by
  refine RelIso.ext fun P ↦ Subtype.ext (Submodule.ext fun x ↦ ?_)
  have h := (Isometry.refl L).apply_mem_intermediateCarrierEquiv_iff P x
  rwa [refl_apply] at h

/-- The transport along an inverse isometry is the inverse transport. -/
@[simp]
theorem intermediateCarrierEquiv_symm (e : Isometry L M) :
    e.symm.intermediateCarrierEquiv = e.intermediateCarrierEquiv.symm := by
  refine RelIso.ext fun P ↦ ?_
  refine e.intermediateCarrierEquiv.injective ?_
  rw [OrderIso.apply_symm_apply]
  refine Subtype.ext (Submodule.ext fun y ↦ ?_)
  rw [mem_intermediateCarrierEquiv_iff, mem_intermediateCarrierEquiv_iff, symm_symm,
    apply_symm_apply]

/-- Membership in an inversely transported carrier is membership of the image in the original
carrier. -/
@[simp]
theorem mem_intermediateCarrierEquiv_symm_iff (e : Isometry L M) (Q : M.IntermediateCarrier)
    (x : V) : x ∈ (e.intermediateCarrierEquiv.symm Q).1 ↔ e x ∈ Q.1 := by
  rw [← intermediateCarrierEquiv_symm, mem_intermediateCarrierEquiv_iff, symm_symm]

/-- The transport along a composite isometry is the composite transport. -/
@[simp]
theorem intermediateCarrierEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).intermediateCarrierEquiv =
      e.intermediateCarrierEquiv.trans f.intermediateCarrierEquiv := by
  refine RelIso.ext fun P ↦ Subtype.ext (Submodule.ext fun z ↦ ?_)
  rw [OrderIso.trans_apply, mem_intermediateCarrierEquiv_iff, mem_intermediateCarrierEquiv_iff,
    mem_intermediateCarrierEquiv_iff]
  rw [symm_trans, trans_apply]

/-! ## Naturality of the discriminant-subgroup correspondence -/

/-- A discriminant class of the target lattice lies in the subgroup of a transported carrier
exactly when its preimage lies in the subgroup of the original carrier. -/
theorem mem_discriminantSubgroup_intermediateCarrierEquiv_iff (e : Isometry L M)
    (P : L.IntermediateCarrier) (y : M.DiscriminantGroup) :
    y ∈ M.discriminantSubgroup (e.intermediateCarrierEquiv P) ↔
      e.discriminantGroupEquiv.symm y ∈ L.discriminantSubgroup P := by
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    rw [M.mk_mem_discriminantSubgroup_iff, mem_intermediateCarrierEquiv_iff,
      discriminantGroupEquiv_symm_mk, L.mk_mem_discriminantSubgroup_iff,
      coe_dualCarrierEquiv_apply]

/-- **The transport commutes with the discriminant-subgroup correspondence.** The subgroup of
`A_M` attached to a transported intermediate carrier is the image, under the induced equivalence
of discriminant groups, of the subgroup of `A_L` attached to the original carrier. -/
@[simp]
theorem discriminantSubgroup_intermediateCarrierEquiv (e : Isometry L M)
    (P : L.IntermediateCarrier) :
    M.discriminantSubgroup (e.intermediateCarrierEquiv P) =
      (L.discriminantSubgroup P).map e.discriminantGroupEquiv.toAddEquiv := by
  ext y
  rw [mem_discriminantSubgroup_intermediateCarrierEquiv_iff, AddSubgroup.mem_map]
  constructor
  · intro hy
    refine ⟨e.discriminantGroupEquiv.symm y, hy, ?_⟩
    simp
  · rintro ⟨z, hz, rfl⟩
    simpa using hz

/-- **The transport commutes with the inverse-image construction.** Transporting the carrier
`L_H` attached to a subgroup `H ≤ A_L` gives the carrier attached to the image of `H` in
`A_M`. -/
theorem intermediateCarrierEquiv_intermediateCarrierOfDiscriminantSubgroup (e : Isometry L M)
    (H : AddSubgroup L.DiscriminantGroup) :
    e.intermediateCarrierEquiv (L.intermediateCarrierOfDiscriminantSubgroup H) =
      M.intermediateCarrierOfDiscriminantSubgroup
        (H.map e.discriminantGroupEquiv.toAddEquiv) := by
  refine M.intermediateCarrierOrderIsoDiscriminantSubgroup.injective ?_
  rw [intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    discriminantSubgroup_intermediateCarrierEquiv,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]

/-! ## Invariance of integrality and evenness -/

/-- **Integrality of an intermediate carrier is an isometry invariant.** -/
@[simp]
theorem isIntegral_intermediateCarrierEquiv_iff (e : Isometry L M) (P : L.IntermediateCarrier) :
    IntermediateCarrier.IsIntegral (e.intermediateCarrierEquiv P) ↔
      IntermediateCarrier.IsIntegral P := by
  rw [IntermediateCarrier.isIntegral_def, IntermediateCarrier.isIntegral_def]
  constructor
  · intro h x hx y hy
    have hxy := h (e x) ((e.apply_mem_intermediateCarrierEquiv_iff P x).mpr hx)
      (e y) ((e.apply_mem_intermediateCarrierEquiv_iff P y).mpr hy)
    rwa [e.map_app] at hxy
  · intro h x hx y hy
    have hxy := h (e.symm x) ((e.mem_intermediateCarrierEquiv_iff P x).mp hx)
      (e.symm y) ((e.mem_intermediateCarrierEquiv_iff P y).mp hy)
    rwa [← e.map_app (e.symm x) (e.symm y), apply_symm_apply, apply_symm_apply] at hxy

/-- **Evenness of an intermediate carrier is an isometry invariant.** -/
@[simp]
theorem isEven_intermediateCarrierEquiv_iff (e : Isometry L M) (P : L.IntermediateCarrier) :
    IntermediateCarrier.IsEven (e.intermediateCarrierEquiv P) ↔
      IntermediateCarrier.IsEven P := by
  rw [IntermediateCarrier.isEven_def, IntermediateCarrier.isEven_def]
  constructor
  · intro h x hx
    obtain ⟨n, hn⟩ := h (e x) ((e.apply_mem_intermediateCarrierEquiv_iff P x).mpr hx)
    exact ⟨n, by rwa [e.norm_apply] at hn⟩
  · intro h x hx
    obtain ⟨n, hn⟩ := h (e.symm x) ((e.mem_intermediateCarrierEquiv_iff P x).mp hx)
    exact ⟨n, by rwa [← e.norm_apply (e.symm x), apply_symm_apply] at hn⟩

/-- Restriction of the intermediate-carrier transport to the carriers cut out by a pair of
predicates corresponding under the transport. -/
private def intermediateCarrierEquivSubtype (e : Isometry L M)
    {p : L.IntermediateCarrier → Prop} {q : M.IntermediateCarrier → Prop}
    (h : ∀ P, p P ↔ q (e.intermediateCarrierEquiv P)) :
    {P : L.IntermediateCarrier // p P} ≃o {Q : M.IntermediateCarrier // q Q} where
  toEquiv := e.intermediateCarrierEquiv.toEquiv.subtypeEquiv h
  map_rel_iff' := e.intermediateCarrierEquiv.le_iff_le

/-- A restricted transport acts through `intermediateCarrierEquiv` on underlying intermediate
carriers. -/
@[simp]
private theorem intermediateCarrierEquivSubtype_apply_coe (e : Isometry L M)
    {p : L.IntermediateCarrier → Prop} {q : M.IntermediateCarrier → Prop}
    (h : ∀ P, p P ↔ q (e.intermediateCarrierEquiv P)) (P : {P : L.IntermediateCarrier // p P}) :
    (e.intermediateCarrierEquivSubtype h P : M.IntermediateCarrier) =
      e.intermediateCarrierEquiv P.1 :=
  (rfl)

/-- The inverse of a restricted transport acts through the inverse intermediate-carrier
transport. -/
@[simp]
private theorem intermediateCarrierEquivSubtype_symm_apply_coe (e : Isometry L M)
    {p : L.IntermediateCarrier → Prop} {q : M.IntermediateCarrier → Prop}
    (h : ∀ P, p P ↔ q (e.intermediateCarrierEquiv P)) (Q : {Q : M.IntermediateCarrier // q Q}) :
    ((e.intermediateCarrierEquivSubtype h).symm Q : L.IntermediateCarrier) =
      e.intermediateCarrierEquiv.symm Q.1 :=
  (rfl)

/-- **An isometry transports integral intermediate carriers.** This is the restriction of
`intermediateCarrierEquiv` to the integral carriers on both sides. -/
def integralIntermediateCarrierEquiv (e : Isometry L M) :
    {P : L.IntermediateCarrier // IntermediateCarrier.IsIntegral P} ≃o
      {Q : M.IntermediateCarrier // IntermediateCarrier.IsIntegral Q} :=
  e.intermediateCarrierEquivSubtype fun P ↦ (e.isIntegral_intermediateCarrierEquiv_iff P).symm

/-- The integral-carrier transport acts through `intermediateCarrierEquiv` on underlying
intermediate carriers. -/
@[simp]
theorem integralIntermediateCarrierEquiv_apply_coe (e : Isometry L M)
    (P : {P : L.IntermediateCarrier // IntermediateCarrier.IsIntegral P}) :
    (e.integralIntermediateCarrierEquiv P : M.IntermediateCarrier) =
      e.intermediateCarrierEquiv P.1 :=
  e.intermediateCarrierEquivSubtype_apply_coe _ P

/-- The inverse integral-carrier transport acts through the inverse intermediate-carrier
transport. -/
@[simp]
theorem integralIntermediateCarrierEquiv_symm_apply_coe (e : Isometry L M)
    (Q : {Q : M.IntermediateCarrier // IntermediateCarrier.IsIntegral Q}) :
    (e.integralIntermediateCarrierEquiv.symm Q : L.IntermediateCarrier) =
      e.intermediateCarrierEquiv.symm Q.1 :=
  e.intermediateCarrierEquivSubtype_symm_apply_coe _ Q

/-- The identity isometry acts identically on integral intermediate carriers. -/
@[simp]
theorem integralIntermediateCarrierEquiv_refl (L : IntegralLattice V) :
    (Isometry.refl L).integralIntermediateCarrierEquiv =
      OrderIso.refl {P : L.IntermediateCarrier // IntermediateCarrier.IsIntegral P} :=
  RelIso.ext fun P ↦ Subtype.ext (by simp)

/-- Integral-carrier transport along an inverse isometry is inverse transport. -/
@[simp]
theorem integralIntermediateCarrierEquiv_symm (e : Isometry L M) :
    e.symm.integralIntermediateCarrierEquiv = e.integralIntermediateCarrierEquiv.symm :=
  RelIso.ext fun Q ↦ Subtype.ext (by simp)

/-- Integral-carrier transport along a composite isometry is composite transport. -/
@[simp]
theorem integralIntermediateCarrierEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).integralIntermediateCarrierEquiv =
      e.integralIntermediateCarrierEquiv.trans f.integralIntermediateCarrierEquiv :=
  RelIso.ext fun P ↦ Subtype.ext (by simp)

/-- **An isometry transports even intermediate carriers.** This is the restriction of
`intermediateCarrierEquiv` to the even carriers on both sides. -/
def evenIntermediateCarrierEquiv (e : Isometry L M) :
    {P : L.IntermediateCarrier // IntermediateCarrier.IsEven P} ≃o
      {Q : M.IntermediateCarrier // IntermediateCarrier.IsEven Q} :=
  e.intermediateCarrierEquivSubtype fun P ↦ (e.isEven_intermediateCarrierEquiv_iff P).symm

/-- The even-carrier transport acts through `intermediateCarrierEquiv` on underlying intermediate
carriers. -/
@[simp]
theorem evenIntermediateCarrierEquiv_apply_coe (e : Isometry L M)
    (P : {P : L.IntermediateCarrier // IntermediateCarrier.IsEven P}) :
    (e.evenIntermediateCarrierEquiv P : M.IntermediateCarrier) =
      e.intermediateCarrierEquiv P.1 :=
  e.intermediateCarrierEquivSubtype_apply_coe _ P

/-- The inverse even-carrier transport acts through the inverse intermediate-carrier transport. -/
@[simp]
theorem evenIntermediateCarrierEquiv_symm_apply_coe (e : Isometry L M)
    (Q : {Q : M.IntermediateCarrier // IntermediateCarrier.IsEven Q}) :
    (e.evenIntermediateCarrierEquiv.symm Q : L.IntermediateCarrier) =
      e.intermediateCarrierEquiv.symm Q.1 :=
  e.intermediateCarrierEquivSubtype_symm_apply_coe _ Q

/-- The identity isometry acts identically on even intermediate carriers. -/
@[simp]
theorem evenIntermediateCarrierEquiv_refl (L : IntegralLattice V) :
    (Isometry.refl L).evenIntermediateCarrierEquiv =
      OrderIso.refl {P : L.IntermediateCarrier // IntermediateCarrier.IsEven P} :=
  RelIso.ext fun P ↦ Subtype.ext (by simp)

/-- Even-carrier transport along an inverse isometry is inverse transport. -/
@[simp]
theorem evenIntermediateCarrierEquiv_symm (e : Isometry L M) :
    e.symm.evenIntermediateCarrierEquiv = e.evenIntermediateCarrierEquiv.symm :=
  RelIso.ext fun Q ↦ Subtype.ext (by simp)

/-- Even-carrier transport along a composite isometry is composite transport. -/
@[simp]
theorem evenIntermediateCarrierEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).evenIntermediateCarrierEquiv =
      e.evenIntermediateCarrierEquiv.trans f.evenIntermediateCarrierEquiv :=
  RelIso.ext fun P ↦ Subtype.ext (by simp)

end Isometry

/-! ## Orthogonal direct sums -/

section OrthogonalSum

variable (L : IntegralLattice V) (M : IntegralLattice W)

/-- The intermediate carrier of an orthogonal sum assembled from a pair of intermediate
carriers. -/
def orthogonalSumIntermediateCarrier (P : L.IntermediateCarrier) (Q : M.IntermediateCarrier) :
    (L.orthogonalSum M).IntermediateCarrier :=
  ⟨P.1.prod Q.1, by
    constructor
    · rw [orthogonalSum_carrier]
      exact Submodule.prod_mono P.2.1 Q.2.1
    · rw [L.dualCarrier_orthogonalSum M]
      exact Submodule.prod_mono P.2.2 Q.2.2⟩

variable {L M}

/-- Membership in an assembled intermediate carrier is componentwise membership. -/
@[simp]
theorem mem_orthogonalSumIntermediateCarrier_iff (P : L.IntermediateCarrier)
    (Q : M.IntermediateCarrier) (p : V × W) :
    p ∈ (orthogonalSumIntermediateCarrier L M P Q).1 ↔ p.1 ∈ P.1 ∧ p.2 ∈ Q.1 :=
  Submodule.mem_prod

/-- Assembling the two carriers gives the carrier of the orthogonal sum. -/
@[simp]
theorem orthogonalSumIntermediateCarrier_bot :
    orthogonalSumIntermediateCarrier L M ⊥ ⊥ = ⊥ := by
  refine Subtype.ext (Submodule.ext fun p ↦ ?_)
  rw [mem_orthogonalSumIntermediateCarrier_iff, Set.Icc.coe_bot, Set.Icc.coe_bot,
    Set.Icc.coe_bot, orthogonalSum_carrier, Submodule.mem_prod]

/-- Assembling the two dual carriers gives the dual carrier of the orthogonal sum. -/
@[simp]
theorem orthogonalSumIntermediateCarrier_top :
    orthogonalSumIntermediateCarrier L M ⊤ ⊤ = ⊤ := by
  refine Subtype.ext (Submodule.ext fun p ↦ ?_)
  rw [mem_orthogonalSumIntermediateCarrier_iff, Set.Icc.coe_top, Set.Icc.coe_top,
    Set.Icc.coe_top, L.dualCarrier_orthogonalSum M, Submodule.mem_prod]

/-- **Assembling intermediate carriers is an order embedding.** One assembled carrier is
contained in another exactly when both components are. -/
@[simp]
theorem orthogonalSumIntermediateCarrier_le_iff (P P' : L.IntermediateCarrier)
    (Q Q' : M.IntermediateCarrier) :
    orthogonalSumIntermediateCarrier L M P Q ≤ orthogonalSumIntermediateCarrier L M P' Q' ↔
      P ≤ P' ∧ Q ≤ Q' := by
  rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, ← Subtype.coe_le_coe]
  constructor
  · intro h
    refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · exact ((mem_orthogonalSumIntermediateCarrier_iff P' Q' (x, 0)).mp
        (h ((mem_orthogonalSumIntermediateCarrier_iff P Q (x, 0)).mpr ⟨hx, zero_mem _⟩))).1
    · exact ((mem_orthogonalSumIntermediateCarrier_iff P' Q' (0, y)).mp
        (h ((mem_orthogonalSumIntermediateCarrier_iff P Q (0, y)).mpr ⟨zero_mem _, hy⟩))).2
  · rintro ⟨hP, hQ⟩ p hp
    rw [mem_orthogonalSumIntermediateCarrier_iff] at hp ⊢
    exact ⟨hP hp.1, hQ hp.2⟩

/-- **The discriminant subgroup of an assembled carrier is the product subgroup.** Under the
canonical equivalence `A_(L ⊥ M) ≃ A_L × A_M`, a class lies in the subgroup of the assembled
carrier exactly when each component lies in the subgroup of the corresponding component
carrier. -/
@[simp]
theorem mem_discriminantSubgroup_orthogonalSumIntermediateCarrier_iff
    (P : L.IntermediateCarrier) (Q : M.IntermediateCarrier)
    (z : (L.orthogonalSum M).DiscriminantGroup) :
    z ∈ (L.orthogonalSum M).discriminantSubgroup (orthogonalSumIntermediateCarrier L M P Q) ↔
      (L.discriminantGroupOrthogonalSumEquiv M z).1 ∈ L.discriminantSubgroup P ∧
        (L.discriminantGroupOrthogonalSumEquiv M z).2 ∈ M.discriminantSubgroup Q := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    rw [(L.orthogonalSum M).mk_mem_discriminantSubgroup_iff,
      mem_orthogonalSumIntermediateCarrier_iff, L.discriminantGroupOrthogonalSumEquiv_mk M,
      L.mk_mem_discriminantSubgroup_iff, M.mk_mem_discriminantSubgroup_iff]
    simp only [orthogonalSumDualCarrierEquiv_apply]

/-- **The discriminant subgroup of an assembled carrier is the product subgroup**, as an equality
of subgroups of `A_L × A_M`. -/
@[simp]
theorem map_discriminantSubgroup_orthogonalSumIntermediateCarrier (P : L.IntermediateCarrier)
    (Q : M.IntermediateCarrier) :
    ((L.orthogonalSum M).discriminantSubgroup
        (orthogonalSumIntermediateCarrier L M P Q)).map
          (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv =
      (L.discriminantSubgroup P).prod (M.discriminantSubgroup Q) := by
  ext z
  rw [AddSubgroup.mem_prod, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_discriminantSubgroup_orthogonalSumIntermediateCarrier_iff P Q y).mp hy
  · intro hz
    refine ⟨(L.discriminantGroupOrthogonalSumEquiv M).symm z, ?_, by simp⟩
    rw [mem_discriminantSubgroup_orthogonalSumIntermediateCarrier_iff,
      (L.discriminantGroupOrthogonalSumEquiv M).apply_symm_apply]
    exact hz

/-- **Assembling commutes with the inverse-image construction.** The carrier of `L ⊥ M` attached
to the preimage of a product subgroup `H × K ≤ A_L × A_M` is assembled from the carriers attached
to `H` and to `K`. -/
theorem orthogonalSumIntermediateCarrier_intermediateCarrierOfDiscriminantSubgroup
    (H : AddSubgroup L.DiscriminantGroup) (K : AddSubgroup M.DiscriminantGroup) :
    orthogonalSumIntermediateCarrier L M (L.intermediateCarrierOfDiscriminantSubgroup H)
        (M.intermediateCarrierOfDiscriminantSubgroup K) =
      (L.orthogonalSum M).intermediateCarrierOfDiscriminantSubgroup
        ((H.prod K).comap (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv) := by
  have hmap := map_discriminantSubgroup_orthogonalSumIntermediateCarrier
    (L.intermediateCarrierOfDiscriminantSubgroup H) (M.intermediateCarrierOfDiscriminantSubgroup K)
  rw [discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup] at hmap
  refine (L.orthogonalSum M).intermediateCarrierOrderIsoDiscriminantSubgroup.injective ?_
  rw [intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup, ← hmap,
    AddSubgroup.comap_map_eq_self_of_injective
      (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv.injective]

/-- **Integrality of an assembled carrier is componentwise.** -/
@[simp]
theorem isIntegral_orthogonalSumIntermediateCarrier_iff (P : L.IntermediateCarrier)
    (Q : M.IntermediateCarrier) :
    IntermediateCarrier.IsIntegral (orthogonalSumIntermediateCarrier L M P Q) ↔
      IntermediateCarrier.IsIntegral P ∧ IntermediateCarrier.IsIntegral Q := by
  rw [IntermediateCarrier.isIntegral_def, IntermediateCarrier.isIntegral_def,
    IntermediateCarrier.isIntegral_def]
  constructor
  · intro h
    constructor
    · intro x hx x' hx'
      have hxy := h (x, 0) (by simp [hx]) (x', 0) (by simp [hx'])
      rw [orthogonalSum_form, orthogonalSumForm_apply] at hxy
      simpa using hxy
    · intro y hy y' hy'
      have hxy := h (0, y) (by simp [hy]) (0, y') (by simp [hy'])
      rw [orthogonalSum_form, orthogonalSumForm_apply] at hxy
      simpa using hxy
  · rintro ⟨hP, hQ⟩ p hp q hq
    rw [mem_orthogonalSumIntermediateCarrier_iff] at hp hq
    rw [orthogonalSum_form, orthogonalSumForm_apply]
    exact Submodule.add_mem _ (hP p.1 hp.1 q.1 hq.1) (hQ p.2 hp.2 q.2 hq.2)

/-- **Evenness of an assembled carrier is componentwise.** -/
@[simp]
theorem isEven_orthogonalSumIntermediateCarrier_iff (P : L.IntermediateCarrier)
    (Q : M.IntermediateCarrier) :
    IntermediateCarrier.IsEven (orthogonalSumIntermediateCarrier L M P Q) ↔
      IntermediateCarrier.IsEven P ∧ IntermediateCarrier.IsEven Q := by
  have hnorm : ∀ p : V × W,
      (L.orthogonalSum M).norm p = L.norm p.1 + M.norm p.2 := fun p ↦ by
    rw [norm_apply, norm_apply, norm_apply, orthogonalSum_form, orthogonalSumForm_apply]
  rw [IntermediateCarrier.isEven_def, IntermediateCarrier.isEven_def,
    IntermediateCarrier.isEven_def]
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨n, hn⟩ := h (x, 0) (by simp [hx])
      refine ⟨n, ?_⟩
      rw [hnorm] at hn
      simpa using hn
    · intro y hy
      obtain ⟨n, hn⟩ := h (0, y) (by simp [hy])
      refine ⟨n, ?_⟩
      rw [hnorm] at hn
      simpa using hn
  · rintro ⟨hP, hQ⟩ p hp
    rw [mem_orthogonalSumIntermediateCarrier_iff] at hp
    obtain ⟨m, hm⟩ := hP p.1 hp.1
    obtain ⟨n, hn⟩ := hQ p.2 hp.2
    refine ⟨m + n, ?_⟩
    rw [hnorm, hm, hn]
    push_cast
    ring

end OrthogonalSum

end IntegralLattice

end TauCeti
