/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OrthogonalComplement
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Naturality

/-!
# Duality for intermediate carriers of an integral lattice

Let `L` be an integral lattice and let `L ≤ M ≤ Lᵛ` be an intermediate carrier. Its dual
submodule `Mᵛ = L.form.dualSubmodule M` is again intermediate: it is contained in `Lᵛ` because
`L ≤ M`, and it contains `L` because `M ≤ Lᵛ` and the form is symmetric. Passing to the dual is
therefore order-reversing on the interval of intermediate carriers, and is an involution when the
form is nondegenerate. This file identifies it under the correspondence with subgroups of the
discriminant group `A_L = Lᵛ / L`:

```text
Mᵛ / L = (M / L)⊥,   equivalently   (L_H)ᵛ = L_{H⊥}.
```

The proof is a calculation on representatives: a dual vector pairs integrally with every vector
of `M` exactly when its discriminant class kills the class of every such vector.

Three consequences follow. Double duality `(Mᵛ)ᵛ = M` is the double orthogonal complement of a
nondegenerate finite bilinear module. The orders of the two subgroups multiply to the order of
`A_L`. Most importantly, an intermediate carrier is unimodular — it equals its own dual submodule
— exactly when its subgroup of the discriminant group is Lagrangian. Combined with the
correspondence between even overlattices and quadratic-isotropic subgroups, this is the last step
of Nikulin's gluing recipe: gluing an even lattice along a Lagrangian isotropic subgroup produces
an even *unimodular* overlattice.

The construction is natural: it commutes with transport along a lattice isometry, and it is
computed componentwise on an orthogonal direct sum.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier.dual`: the dual of an intermediate carrier.
* `TauCeti.IntegralLattice.IntermediateCarrier.discriminantSubgroup_dual`: the subgroup attached
  to `Mᵛ` is the orthogonal complement of the subgroup attached to `M`.
* `TauCeti.IntegralLattice.dual_intermediateCarrierOfDiscriminantSubgroup`: the
  same statement read as `(L_H)ᵛ = L_{H⊥}`.
* `TauCeti.IntegralLattice.IntermediateCarrier.dual_dual`: double duality.
* `TauCeti.IntegralLattice.IntermediateCarrier.dual_eq_self_iff_isLagrangian`: an
  intermediate carrier is unimodular exactly when its subgroup is Lagrangian.
* `TauCeti.IntegralLattice.dual_intermediateCarrierOfDiscriminantSubgroup_eq_self_iff`: the
  overlattice `L_H` is unimodular exactly when `H = H⊥`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V}

namespace IntermediateCarrier

/-! ## The dual of an intermediate carrier -/

/-- The dual submodule of an intermediate carrier `L ≤ M ≤ Lᵛ`, which is again an intermediate
carrier. -/
def dual (M : L.IntermediateCarrier) : L.IntermediateCarrier :=
  ⟨L.form.dualSubmodule M.1, by
      intro x hx y hy
      rw [L.isSymm.eq]
      exact M.2.2 hy x hx, by
      intro x hx y hy
      exact hx y (M.2.1 hy)⟩

/-- The underlying submodule of the dual carrier is the dual submodule. -/
@[simp]
theorem coe_dual (M : L.IntermediateCarrier) : (dual M).1 = L.form.dualSubmodule M.1 :=
  (rfl)

/-- The dual of the smallest intermediate carrier, the carrier of `L` itself, is the largest one,
the dual carrier. -/
@[simp]
theorem dual_bot : dual (⊥ : L.IntermediateCarrier) = ⊤ := by
  refine Subtype.ext ?_
  rw [coe_dual, Set.Icc.coe_bot, Set.Icc.coe_top]

/-- The dual of the largest intermediate carrier, the dual carrier, is the carrier of `L`. -/
@[simp]
theorem dual_top [L.IsNondegenerate] : dual (⊤ : L.IntermediateCarrier) = ⊥ := by
  refine Subtype.ext ?_
  rw [coe_dual, Set.Icc.coe_top, Set.Icc.coe_bot, L.dualSubmodule_dualCarrier]

/-- Passing to the dual carrier reverses inclusions. -/
theorem dual_le_dual {M N : L.IntermediateCarrier} (h : M ≤ N) : dual N ≤ dual M := by
  intro x hx y hy
  exact hx y (h hy)

/-- Passing to the dual carrier is an adjunction: one carrier lies in the dual of a second
exactly when the second lies in the dual of the first. -/
theorem le_dual_comm {M N : L.IntermediateCarrier} : M ≤ dual N ↔ N ≤ dual M := by
  rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, coe_dual, coe_dual, ← L.form_flip,
    LinearMap.BilinForm.le_flip_dualSubmodule, L.form_flip]

/-- **Integrality is containment in the dual.** An intermediate carrier is integral exactly when
it is contained in its own dual carrier. -/
theorem isIntegral_iff_le_dual (M : L.IntermediateCarrier) : IsIntegral M ↔ M ≤ dual M := by
  rw [isIntegral_def, ← Subtype.coe_le_coe, coe_dual]
  exact ⟨fun h _ hx y hy ↦ h _ hx y hy, fun h x hx y hy ↦ h hx y hy⟩

/-! ## The dual carrier and the orthogonal complement -/

/-- A discriminant class belongs to the subgroup of the dual carrier exactly when it is
orthogonal to the whole subgroup of the original carrier. -/
theorem mem_discriminantSubgroup_dual_iff (M : L.IntermediateCarrier)
    (a : L.DiscriminantGroup) :
    a ∈ L.discriminantSubgroup (dual M) ↔
      ∀ b ∈ L.discriminantSubgroup M, L.discriminantPairing a b = 0 := by
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    rw [L.mk_mem_discriminantSubgroup_iff, coe_dual,
      LinearMap.BilinForm.mem_dualSubmodule]
    constructor
    · intro hx b hb
      induction b using Submodule.Quotient.induction_on with
      | _ y =>
        exact (L.discriminantPairing_mk_eq_zero_iff x y).mpr
          (hx y ((L.mk_mem_discriminantSubgroup_iff M y).mp hb))
    · intro hx y hy
      have hyd : y ∈ L.dualCarrier := M.2.2 hy
      exact (L.discriminantPairing_mk_eq_zero_iff x ⟨y, hyd⟩).mp
        (hx _ ((L.mk_mem_discriminantSubgroup_iff M ⟨y, hyd⟩).mpr hy))

variable [L.IsNondegenerate]

/-- **The dual of an intermediate carrier is the orthogonal complement of its subgroup.** Under
the correspondence between intermediate carriers and subgroups of the discriminant group, taking
the dual submodule corresponds to taking the orthogonal complement in the discriminant bilinear
module. -/
@[simp]
theorem discriminantSubgroup_dual (M : L.IntermediateCarrier) :
    L.discriminantSubgroup (dual M) =
      L.discriminantBilinearModule.orthogonalComplement (L.discriminantSubgroup M) := by
  refine AddSubgroup.ext fun a ↦ (mem_discriminantSubgroup_dual_iff M a).trans ?_
  refine ⟨fun h ↦ (L.discriminantBilinearModule.mem_orthogonalComplement_iff _ a).mpr
      fun b hb ↦ (L.discriminantBilinearModule_pairing a b).trans (h b hb), fun h b hb ↦ ?_⟩
  exact (L.discriminantBilinearModule_pairing a b).symm.trans
    ((L.discriminantBilinearModule.mem_orthogonalComplement_iff _ a).mp h b hb)

/-- **Double duality for intermediate carriers.** -/
@[simp]
theorem dual_dual (M : L.IntermediateCarrier) : dual (dual M) = M := by
  refine Subtype.ext ?_
  rw [coe_dual, coe_dual]
  simpa only [L.form_flip] using
    LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip L.form L.form_nondegenerate M.1

/-- Passing to the dual carrier is injective. -/
theorem dual_injective : Function.Injective (dual (L := L)) := by
  intro M N h
  rw [← dual_dual M, ← dual_dual N, h]

/-- Passing to the dual carrier reflects inclusions as well as reversing them. -/
@[simp]
theorem dual_le_dual_iff {M N : L.IntermediateCarrier} : dual M ≤ dual N ↔ N ≤ M :=
  ⟨fun h ↦ by simpa using dual_le_dual h, dual_le_dual⟩

/-- The orders of the subgroups attached to an intermediate carrier and to its dual multiply to
the order of the discriminant group. -/
theorem card_discriminantSubgroup_mul_card_discriminantSubgroup_dual
    (M : L.IntermediateCarrier) :
    Nat.card (L.discriminantSubgroup M) * Nat.card (L.discriminantSubgroup (dual M)) =
      Nat.card L.DiscriminantGroup := by
  have hcard : Nat.card (L.discriminantSubgroup (dual M)) =
      Nat.card (L.discriminantBilinearModule.orthogonalComplement (L.discriminantSubgroup M)) :=
    congrArg (fun K : AddSubgroup L.DiscriminantGroup ↦ Nat.card K) (discriminantSubgroup_dual M)
  rw [hcard]
  exact FiniteBilinearModule.IsNondegenerate.card_mul_card_orthogonalComplement
    L.discriminantBilinearModule L.isNondegenerate_discriminantBilinearModule _

/-! ## Unimodular intermediate carriers and Lagrangian subgroups -/

/-- **An intermediate carrier is unimodular exactly when its subgroup is Lagrangian.** Here
unimodularity is the equality `Mᵛ = M` of an intermediate carrier with its own dual submodule,
matching `TauCeti.IntegralLattice.IsUnimodular` for the lattice which `M` carries. -/
@[simp]
theorem dual_eq_self_iff_isLagrangian (M : L.IntermediateCarrier) :
    dual M = M ↔ L.discriminantBilinearModule.IsLagrangian (L.discriminantSubgroup M) := by
  constructor
  · intro h
    exact (L.discriminantBilinearModule.isLagrangian_def _).mpr
      ((congrArg L.discriminantSubgroup h).symm.trans (discriminantSubgroup_dual M))
  · intro h
    refine L.intermediateCarrierOrderIsoDiscriminantSubgroup.injective ?_
    rw [L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
      L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply]
    exact (discriminantSubgroup_dual M).trans
      ((L.discriminantBilinearModule.isLagrangian_def _).mp h).symm

end IntermediateCarrier

open IntermediateCarrier

section Subgroups

variable (L) [L.IsNondegenerate]

/-! ## The correspondence read on subgroups -/

/-- **The dual of a glued overlattice is the overlattice glued along the orthogonal
complement**: `(L_H)ᵛ = L_{H⊥}`. -/
@[simp]
theorem dual_intermediateCarrierOfDiscriminantSubgroup
    (H : AddSubgroup L.DiscriminantGroup) :
    dual (L.intermediateCarrierOfDiscriminantSubgroup H) =
      L.intermediateCarrierOfDiscriminantSubgroup
        (L.discriminantBilinearModule.orthogonalComplement H) := by
  apply L.intermediateCarrierOrderIsoDiscriminantSubgroup.injective
  rw [L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply]
  have h1 : L.discriminantSubgroup (dual (L.intermediateCarrierOfDiscriminantSubgroup H)) =
      L.discriminantBilinearModule.orthogonalComplement H :=
    (discriminantSubgroup_dual _).trans
      (congrArg _ (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H))
  have h2 : L.discriminantSubgroup (L.intermediateCarrierOfDiscriminantSubgroup
      (L.discriminantBilinearModule.orthogonalComplement H)) =
      L.discriminantBilinearModule.orthogonalComplement H :=
    L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup _
  exact h1.trans h2.symm

/-- **The overlattice glued along `H` is unimodular exactly when `H` is Lagrangian.** For an even
lattice `L` and a quadratic-isotropic subgroup `H`, the glued overlattice `L_H` is even by
`TauCeti.IntegralLattice.isEven_intermediateCarrierOfDiscriminantSubgroup_iff`, so this is the
criterion for `L_H` to be an even unimodular overlattice of `L`. -/
theorem dual_intermediateCarrierOfDiscriminantSubgroup_eq_self_iff
    (H : AddSubgroup L.DiscriminantGroup) :
    dual (L.intermediateCarrierOfDiscriminantSubgroup H) =
        L.intermediateCarrierOfDiscriminantSubgroup H ↔
      L.discriminantBilinearModule.IsLagrangian H :=
  (dual_eq_self_iff_isLagrangian _).trans
    (Iff.of_eq (congrArg _ (L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup H)))

end Subgroups

/-! ## Naturality -/

namespace Isometry

variable {M : IntegralLattice W}

/-- **Transport along an isometry commutes with duality of intermediate carriers.** -/
@[simp]
theorem intermediateCarrierEquiv_dual (e : Isometry L M) (P : L.IntermediateCarrier) :
    e.intermediateCarrierEquiv (dual P) = dual (e.intermediateCarrierEquiv P) := by
  refine Subtype.ext (Submodule.ext fun y ↦ ?_)
  rw [mem_intermediateCarrierEquiv_iff, coe_dual, LinearMap.BilinForm.mem_dualSubmodule,
    coe_dual, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hy w hw
    rw [mem_intermediateCarrierEquiv_iff] at hw
    have hmap : M.form y w = L.form (e.symm y) (e.symm w) := by
      rw [← e.map_app (e.symm y) (e.symm w), e.apply_symm_apply, e.apply_symm_apply]
    rw [hmap]
    exact hy (e.symm w) hw
  · intro hy x hx
    have hmap : L.form (e.symm y) x = M.form y (e x) := by
      rw [← e.map_app (e.symm y) x, e.apply_symm_apply]
    rw [hmap]
    exact hy (e x) ((e.apply_mem_intermediateCarrierEquiv_iff P x).mpr hx)

end Isometry

/-! ## Orthogonal direct sums -/

/-- **Duality of intermediate carriers is componentwise on an orthogonal direct sum.** -/
@[simp]
theorem dual_orthogonalSumIntermediateCarrier (L : IntegralLattice V) (M : IntegralLattice W)
    (P : L.IntermediateCarrier) (Q : M.IntermediateCarrier) :
    dual (orthogonalSumIntermediateCarrier L M P Q) =
      orthogonalSumIntermediateCarrier L M (dual P) (dual Q) := by
  refine Subtype.ext (Submodule.ext fun p ↦ ?_)
  simp only [coe_dual, LinearMap.BilinForm.mem_dualSubmodule,
    mem_orthogonalSumIntermediateCarrier_iff]
  constructor
  · refine fun hp ↦ ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · have h := hp (x, 0) ⟨hx, zero_mem _⟩
      simpa only [orthogonalSum_form, orthogonalSumForm_apply, map_zero, LinearMap.zero_apply,
        add_zero] using h
    · have h := hp (0, y) ⟨zero_mem _, hy⟩
      simpa only [orthogonalSum_form, orthogonalSumForm_apply, map_zero, LinearMap.zero_apply,
        zero_add] using h
  · rintro ⟨hp₁, hp₂⟩ q hq
    rw [orthogonalSum_form, orthogonalSumForm_apply]
    exact add_mem (hp₁ q.1 hq.1) (hp₂ q.2 hq.2)

end IntegralLattice

end TauCeti
