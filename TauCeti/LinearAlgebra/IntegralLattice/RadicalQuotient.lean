/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
import Mathlib.LinearAlgebra.Projection

/-!
# Quotienting an integral lattice by its radical

The rational bilinear form of a possibly degenerate integral lattice descends to the quotient of
its ambient space by its radical. The image of the integral carrier is again a full integral
lattice, and the descended form is nondegenerate. This lets later discriminant-group constructions,
which require nondegeneracy, be applied after discarding exactly the null directions.

The quotient map preserves the rational and integral forms. Evenness descends, and the quotient
has signature `(n₊, 0, n₋)`: its positive and negative indices agree with those of the original
lattice, while its null index vanishes.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`.

## Main definitions and results

* `TauCeti.IntegralLattice.radicalQuotientForm`: the descended rational bilinear form.
* `TauCeti.IntegralLattice.radicalQuotientForm_mk`: evaluation of the descended form on classes.
* `TauCeti.IntegralLattice.radicalQuotientCarrier`: the image of the integral carrier.
* `TauCeti.IntegralLattice.mem_radicalQuotientCarrier_iff`: representatives of carrier elements.
* `TauCeti.IntegralLattice.radicalQuotient`: the image lattice in the quotient ambient space.
* `TauCeti.IntegralLattice.radicalQuotientMap`: the quotient map on integral carriers.
* `TauCeti.IntegralLattice.radicalQuotientMap_surjective`: the quotient map on carriers
  is surjective.
* `TauCeti.IntegralLattice.radicalQuotientMap_eq_zero_iff`: the map discards exactly the radical.
* `TauCeti.IntegralLattice.form_radicalQuotientMap`: preservation of the rational form.
* `TauCeti.IntegralLattice.integralForm_radicalQuotientMap`: preservation of the integral form.
* `TauCeti.IntegralLattice.radicalQuotient_norm_mk`: preservation of the rational norm.
* `TauCeti.IntegralLattice.integralNorm_radicalQuotientMap`: preservation of the integral norm.
* `TauCeti.IntegralLattice.nondegenerate_radicalQuotientForm`: the descended form is
  nondegenerate.
* `TauCeti.IntegralLattice.radical_radicalQuotient_eq_bot`: the quotient radical is trivial.
* `TauCeti.IntegralLattice.IsEven.radicalQuotient`: evenness descends to the quotient.
* `TauCeti.IntegralLattice.sigPos_radicalQuotient`: preservation of the positive index.
* `TauCeti.IntegralLattice.sigNeg_radicalQuotient`: preservation of the negative index.
* `TauCeti.IntegralLattice.signature_radicalQuotient`: the quotient signature is
  `(n₊, 0, n₋)`.
-/

public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The bilinear form induced on the quotient of the ambient space by the lattice radical. -/
noncomputable def radicalQuotientForm :
    LinearMap.BilinForm ℚ (V ⧸ L.radical) :=
  QuadraticMap.associated (L.form.toQuadraticMap.lift L.radical (by
    rw [L.radical_toQuadraticMap]))

/-- The quotient form evaluated on classes is the original form evaluated on representatives. -/
@[simp]
theorem radicalQuotientForm_mk (x y : V) :
    L.radicalQuotientForm (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = L.form x y := by
  have hsymm : L.form y x = L.form x y := L.isSymm.eq y x
  simp only [radicalQuotientForm, QuadraticMap.associated_apply, ← Submodule.Quotient.mk_add,
    QuadraticMap.lift_mk, LinearMap.BilinMap.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, hsymm]
  rw [invOf_smul_eq_iff, two_smul]
  ring

/-- The form induced on the radical quotient is symmetric. -/
theorem isSymm_radicalQuotientForm : L.radicalQuotientForm.IsSymm := by
  rw [radicalQuotientForm]
  exact ⟨QuadraticMap.associated_isSymm ℚ _⟩

/-- The image of the integral carrier in the quotient by the radical. -/
def radicalQuotientCarrier : Submodule ℤ (V ⧸ L.radical) :=
  L.carrier.map (L.radical.mkQ.restrictScalars ℤ)

/-- A quotient class belongs to the quotient carrier exactly when it has a representative in the
original integral carrier. -/
@[simp]
theorem mem_radicalQuotientCarrier_iff (x : V ⧸ L.radical) :
    x ∈ L.radicalQuotientCarrier ↔
      ∃ y ∈ L.carrier, (Submodule.Quotient.mk y : V ⧸ L.radical) = x := by
  change x ∈ L.radicalQuotientCarrier ↔ ∃ y ∈ L.carrier, L.radical.mkQ y = x
  simp only [radicalQuotientCarrier, Submodule.mem_map, LinearMap.restrictScalars_apply]

/-- The image of a full integral carrier in the radical quotient is again a full lattice. -/
instance isLattice_radicalQuotientCarrier : L.radicalQuotientCarrier.IsLattice ℚ where
  fg := L.isLattice.fg.map _
  span_eq_top := by
    -- Express the carrier set as the image of the original carrier under the rational projection
    have hcoe : (L.radicalQuotientCarrier : Set (V ⧸ L.radical)) =
        L.radical.mkQ '' (L.carrier : Set V) := by
      ext x
      simp only [SetLike.mem_coe, radicalQuotientCarrier, Submodule.mem_map,
        LinearMap.restrictScalars_apply, Set.mem_image]
    rw [hcoe, ← Submodule.map_span, L.isLattice.span_eq_top, Submodule.map_top,
      Submodule.range_mkQ]

/-- The radical quotient of an integral lattice. Its carrier is the image of the original carrier,
and its form is the form induced on the quotient ambient space. -/
noncomputable def radicalQuotient : IntegralLattice (V ⧸ L.radical) :=
  ofSubmodule L.radicalQuotientCarrier L.radicalQuotientForm L.isSymm_radicalQuotientForm
    fun x hx y hy ↦ by
      rw [mem_radicalQuotientCarrier_iff] at hx hy
      obtain ⟨x, hxL, rfl⟩ := hx
      obtain ⟨y, hyL, rfl⟩ := hy
      simpa only [Submodule.mkQ_apply, radicalQuotientForm_mk] using L.le_dual hxL y hyL

@[simp]
theorem radicalQuotient_carrier : L.radicalQuotient.carrier = L.radicalQuotientCarrier := by
  exact ofSubmodule_carrier _ _ _ _

@[simp]
theorem radicalQuotient_form : L.radicalQuotient.form = L.radicalQuotientForm := by
  exact ofSubmodule_form _ _ _ _

/-- The quotient map from the original integral carrier to the radical-quotient carrier. -/
noncomputable def radicalQuotientMap : L →ₗ[ℤ] L.radicalQuotient :=
  L.radical.mkQ.restrictScalars ℤ |>.domRestrict L.carrier |>.codRestrict
    L.radicalQuotient.carrier fun x ↦ by
      rw [radicalQuotient_carrier]
      exact Submodule.mem_map.mpr ⟨x, x.2, rfl⟩

/-- Evaluation rule for the radical quotient map. -/
@[simp]
theorem radicalQuotientMap_apply (x : L) :
    (L.radicalQuotientMap x : V ⧸ L.radical) = Submodule.Quotient.mk (x : V) :=
  by simp [radicalQuotientMap]

/-- The radical quotient map on integral lattices is surjective. -/
theorem radicalQuotientMap_surjective : Function.Surjective L.radicalQuotientMap := by
  rintro ⟨x, hx⟩
  rw [radicalQuotient_carrier, mem_radicalQuotientCarrier_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext (L.radicalQuotientMap_apply ⟨y, hy⟩)⟩

/-- A lattice vector maps to zero exactly when its ambient vector belongs to the radical. -/
@[simp]
theorem radicalQuotientMap_eq_zero_iff (x : L) :
    L.radicalQuotientMap x = 0 ↔ (x : V) ∈ L.radical := by
  rw [Subtype.ext_iff]
  simp only [radicalQuotientMap_apply, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero]

/-- The radical quotient map preserves the rational bilinear form. -/
theorem form_radicalQuotientMap (x y : L) :
    L.radicalQuotient.form (L.radicalQuotientMap x) (L.radicalQuotientMap y) = L.form x y :=
  by simp only [radicalQuotient_form, radicalQuotientMap_apply, radicalQuotientForm_mk]

/-- The radical quotient map preserves the integral bilinear form. -/
@[simp]
theorem integralForm_radicalQuotientMap (x y : L) :
    L.radicalQuotient.integralForm (L.radicalQuotientMap x) (L.radicalQuotientMap y) =
      L.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  simp only [integralForm_cast, form_radicalQuotientMap]

/-- The radical quotient preserves the rational norm on representatives. -/
@[simp]
theorem radicalQuotient_norm_mk (x : V) :
    L.radicalQuotient.norm (Submodule.Quotient.mk x) = L.norm x := by
  simp only [norm_apply, radicalQuotient_form, radicalQuotientForm_mk]

/-- The radical quotient map preserves the integral norm. -/
@[simp]
theorem integralNorm_radicalQuotientMap (x : L) :
    L.radicalQuotient.integralNorm (L.radicalQuotientMap x) = L.integralNorm x := by
  simp only [integralNorm_apply, integralForm_radicalQuotientMap]

/-- The form on the radical quotient is nondegenerate. -/
theorem nondegenerate_radicalQuotientForm : L.radicalQuotientForm.Nondegenerate := by
  let _ := L.finiteDimensional
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [L.mem_radical_iff]
    intro y
    have hxy := DFunLike.congr_fun (LinearMap.mem_ker.mp hx) (Submodule.Quotient.mk y)
    simpa only [radicalQuotientForm_mk, LinearMap.zero_apply] using hxy

/-- The radical of the quotient lattice is trivial. -/
@[simp]
theorem radical_radicalQuotient_eq_bot : L.radicalQuotient.radical = ⊥ := by
  rw [← L.radicalQuotient.radical_toQuadraticMap,
    LinearMap.BilinForm.radical_toQuadraticMap L.radicalQuotient.form
      L.radicalQuotient.isSymm, radicalQuotient_form]
  exact L.nondegenerate_radicalQuotientForm.ker_eq_bot

/-- Evenness passes from an integral lattice to its radical quotient. -/
theorem IsEven.radicalQuotient (hL : L.IsEven) : L.radicalQuotient.IsEven := by
  rw [L.radicalQuotient.isEven_iff_forall_norm]
  rintro ⟨x, hx⟩
  rw [L.radicalQuotient_carrier] at hx
  rw [L.mem_radicalQuotientCarrier_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [Submodule.mkQ_apply, radicalQuotient_norm_mk] using
    hL.exists_norm_eq_two_mul ⟨y, hy⟩

/-- The positive index is unchanged after quotienting by the radical. -/
theorem sigPos_radicalQuotient : L.radicalQuotient.sigPos = L.sigPos := by
  let _ := L.finiteDimensional
  dsimp only [sigPos]
  rw [radicalQuotient_form, radicalQuotientForm,
    QuadraticMap.toQuadraticMap_associated ℚ]
  exact TauCeti.QuadraticForm.sigPos_lift_of_eq_radical L.form.toQuadraticMap L.radical
    L.radical_toQuadraticMap.symm

/-- The negative index is unchanged after quotienting by the radical. -/
theorem sigNeg_radicalQuotient : L.radicalQuotient.sigNeg = L.sigNeg := by
  let _ := L.finiteDimensional
  dsimp only [sigNeg]
  rw [radicalQuotient_form, radicalQuotientForm,
    QuadraticMap.toQuadraticMap_associated ℚ]
  exact TauCeti.QuadraticForm.sigNeg_lift_of_eq_radical L.form.toQuadraticMap L.radical
    L.radical_toQuadraticMap.symm

/-- The radical quotient has the same positive and negative indices as the original lattice and
zero null index. -/
theorem signature_radicalQuotient :
    L.radicalQuotient.signature = (L.sigPos, 0, L.sigNeg) := by
  have hnull : L.radicalQuotient.sigNull = 0 := by
    rw [← L.radicalQuotient.radical_eq_bot_iff_sigNull_eq_zero]
    exact L.radical_radicalQuotient_eq_bot
  simp only [signature, L.sigPos_radicalQuotient, L.sigNeg_radicalQuotient, hnull]

end IntegralLattice

end TauCeti
