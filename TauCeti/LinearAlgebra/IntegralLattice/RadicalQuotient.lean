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

## Main definitions and results

* `TauCeti.IntegralLattice.radicalQuotientForm`: the descended rational bilinear form.
* `TauCeti.IntegralLattice.radicalQuotient`: the image lattice in the quotient ambient space.
* `TauCeti.IntegralLattice.radicalQuotientMap`: the quotient map on integral carriers.
* `TauCeti.IntegralLattice.radicalQuotientMap_surjective`: the quotient map on carriers
  is surjective.
* `TauCeti.IntegralLattice.nondegenerate_radicalQuotientForm`: the descended form is
  nondegenerate.
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
  simp [radicalQuotientForm, QuadraticMap.associated_apply, ← Submodule.Quotient.mk_add,
    LinearMap.BilinMap.toQuadraticMap_apply, hsymm]
  ring

/-- The form induced on the radical quotient is symmetric. -/
theorem isSymm_radicalQuotientForm : L.radicalQuotientForm.IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y => simpa only [radicalQuotientForm_mk] using L.isSymm.eq x y

/-- The image of the integral carrier in the quotient by the radical. -/
def radicalQuotientCarrier : Submodule ℤ (V ⧸ L.radical) :=
  L.carrier.map (L.radical.mkQ.restrictScalars ℤ)

/-- A quotient class belongs to the quotient carrier exactly when it has a representative in the
original integral carrier. -/
theorem mem_radicalQuotientCarrier_iff (x : V ⧸ L.radical) :
    x ∈ L.radicalQuotientCarrier ↔ ∃ y : V, y ∈ L.carrier ∧ L.radical.mkQ y = x := by
  simp only [radicalQuotientCarrier, Submodule.mem_map, LinearMap.restrictScalars_apply]

/-- The image of a full integral carrier in the radical quotient is again a full lattice. -/
instance isLattice_radicalQuotientCarrier : L.radicalQuotientCarrier.IsLattice ℚ where
  fg := L.isLattice.fg.map _
  span_eq_top := by
    -- Express the carrier set as the image of the original carrier under the rational projection
    have hcoe : (L.radicalQuotientCarrier : Set (V ⧸ L.radical)) =
        L.radical.mkQ '' (L.carrier : Set V) := by
      ext x
      simp only [SetLike.mem_coe, mem_radicalQuotientCarrier_iff, Set.mem_image]
    rw [hcoe, ← Submodule.map_span, L.isLattice.span_eq_top, Submodule.map_top,
      Submodule.range_mkQ]

/-- The radical quotient of an integral lattice. Its carrier is the image of the original carrier,
and its form is the form induced on the quotient ambient space. -/
noncomputable def radicalQuotient : IntegralLattice (V ⧸ L.radical) :=
  { carrier := L.radicalQuotientCarrier
    form := L.radicalQuotientForm
    isLattice := inferInstance
    isSymm := L.isSymm_radicalQuotientForm
    le_dual := fun x hx y hy ↦ by
      rw [mem_radicalQuotientCarrier_iff] at hx hy
      obtain ⟨x, hxL, rfl⟩ := hx
      obtain ⟨y, hyL, rfl⟩ := hy
      simpa only [Submodule.mkQ_apply, radicalQuotientForm_mk] using L.le_dual hxL y hyL }

@[simp]
theorem radicalQuotient_carrier : L.radicalQuotient.carrier = L.radicalQuotientCarrier := by
  simp [radicalQuotient]

@[simp]
theorem radicalQuotient_form : L.radicalQuotient.form = L.radicalQuotientForm := by
  simp [radicalQuotient]

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

/-- The radical quotient map preserves the rational bilinear form. -/
theorem radicalQuotient_form_map (x y : L) :
    L.radicalQuotient.form (L.radicalQuotientMap x) (L.radicalQuotientMap y) = L.form x y :=
  by simp only [radicalQuotient_form, radicalQuotientMap_apply, radicalQuotientForm_mk]

/-- The radical quotient map preserves the integral bilinear form. -/
@[simp]
theorem radicalQuotient_integralForm_map (x y : L) :
    L.radicalQuotient.integralForm (L.radicalQuotientMap x) (L.radicalQuotientMap y) =
      L.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  simp only [integralForm_cast, radicalQuotient_form_map]

/-- The form on the radical quotient is nondegenerate. -/
theorem nondegenerate_radicalQuotientForm : L.radicalQuotient.form.Nondegenerate := by
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
    simpa only [radicalQuotient_form, radicalQuotientForm_mk, LinearMap.zero_apply] using hxy

/-- The radical of the quotient lattice is trivial. -/
@[simp]
theorem radicalQuotient_radical_eq_bot : L.radicalQuotient.radical = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxker : x ∈ L.radicalQuotient.form.ker := by
    rw [LinearMap.mem_ker, LinearMap.ext_iff]
    exact (L.radicalQuotient.mem_radical_iff x).mp hx
  rw [L.nondegenerate_radicalQuotientForm.ker_eq_bot] at hxker
  exact hxker

/-- Evenness passes from an integral lattice to its radical quotient. -/
theorem IsEven.radicalQuotient (hL : L.IsEven) : L.radicalQuotient.IsEven := by
  rw [L.radicalQuotient.isEven_iff_forall_norm]
  rintro ⟨x, hx⟩
  rw [L.radicalQuotient_carrier] at hx
  rw [L.mem_radicalQuotientCarrier_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [norm_apply, radicalQuotient_form, Submodule.mkQ_apply,
    radicalQuotientForm_mk] using
    hL.exists_norm_eq_two_mul ⟨y, hy⟩

private noncomputable def quotientComplement : Submodule ℚ V :=
  (Submodule.exists_isCompl L.radical).choose

private theorem radical_isCompl_quotientComplement :
    IsCompl L.radical L.quotientComplement :=
  (Submodule.exists_isCompl L.radical).choose_spec

/-- The radical quotient is isometric to the restriction of the original quadratic form to a
linear complement of the radical. This auxiliary equivalence makes the signature comparison
independent of the choice of complement. -/
private noncomputable def radicalQuotientIsometryEquiv :
    (L.form.toQuadraticMap.restrict L.quotientComplement).IsometryEquiv
      L.radicalQuotient.form.toQuadraticMap where
  toLinearEquiv := (L.radical.quotientEquivOfIsCompl L.quotientComplement
    L.radical_isCompl_quotientComplement).symm
  map_app' x := by
    let e := L.radical.quotientEquivOfIsCompl L.quotientComplement
      L.radical_isCompl_quotientComplement
    have he : e.symm x = Submodule.Quotient.mk (x : V) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (Submodule.quotientEquivOfIsCompl_apply_mk_right
        L.radical_isCompl_quotientComplement x).symm
    -- Fold the linear equivalence expression to rewrite by `he`
    change L.radicalQuotient.form.toQuadraticMap (e.symm x) = _
    rw [he]
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, radicalQuotient_form,
      radicalQuotientForm_mk, QuadraticMap.restrict_apply]

private theorem radical_restrict_quotientComplement :
    (L.form.toQuadraticMap.restrict L.quotientComplement).radical = ⊥ := by
  have hrad : (L.form.toQuadraticMap.restrict L.quotientComplement).radical =
      (L.form.restrict L.quotientComplement).ker :=
    LinearMap.BilinForm.radical_toQuadraticMap (L.form.restrict L.quotientComplement)
      ⟨fun x y ↦ L.isSymm.eq x y⟩
  rw [hrad, Submodule.eq_bot_iff]
  intro x hx
  have hxrad : (x : V) ∈ L.radical := by
    rw [L.mem_radical_iff]
    intro y
    obtain ⟨r, w, rfl, _⟩ :=
      Submodule.existsUnique_add_of_isCompl L.radical_isCompl_quotientComplement y
    rw [map_add, L.isSymm.eq x r, (L.mem_radical_iff r).mp r.2 x, zero_add]
    exact DFunLike.congr_fun (LinearMap.mem_ker.mp hx) w
  have hxbot : (x : V) ∈ L.radical ⊓ L.quotientComplement := ⟨hxrad, x.2⟩
  rw [L.radical_isCompl_quotientComplement.disjoint.eq_bot, Submodule.mem_bot] at hxbot
  exact Subtype.ext hxbot

/-- The positive index is unchanged after quotienting by the radical. -/
theorem sigPos_radicalQuotient : L.radicalQuotient.sigPos = L.sigPos := by
  dsimp only [sigPos]
  have hfd := L.finiteDimensional
  have hquot : _root_.sigPos L.radicalQuotient.form.toQuadraticMap =
      _root_.sigPos (L.form.toQuadraticMap.restrict L.quotientComplement) :=
    (QuadraticMap.Equivalent.sigPos_eq (⟨L.radicalQuotientIsometryEquiv⟩ :
      (L.form.toQuadraticMap.restrict L.quotientComplement).Equivalent
        L.radicalQuotient.form.toQuadraticMap)).symm
  have hpos := TauCeti.QuadraticForm.sigPos_restrict_le
    L.form.toQuadraticMap L.quotientComplement
  have hneg := TauCeti.QuadraticForm.sigNeg_restrict_le
    L.form.toQuadraticMap L.quotientComplement
  have hsum := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.form.toQuadraticMap)
  have hsumW := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.form.toQuadraticMap.restrict L.quotientComplement)
  have hradW := L.radical_restrict_quotientComplement
  rw [L.radical_toQuadraticMap] at hsum
  rw [hradW, finrank_bot, add_zero] at hsumW
  have hdim := Submodule.finrank_add_eq_of_isCompl
    L.radical_isCompl_quotientComplement
  omega

/-- The negative index is unchanged after quotienting by the radical. -/
theorem sigNeg_radicalQuotient : L.radicalQuotient.sigNeg = L.sigNeg := by
  dsimp only [sigNeg]
  have hfd := L.finiteDimensional
  have hquotPos : _root_.sigPos L.radicalQuotient.form.toQuadraticMap =
      _root_.sigPos L.form.toQuadraticMap := by
    have := L.sigPos_radicalQuotient
    dsimp only [sigPos] at this
    exact this
  have hsum := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.form.toQuadraticMap)
  have hsumQ := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.radicalQuotient.form.toQuadraticMap)
  rw [L.radical_toQuadraticMap] at hsum
  rw [L.radicalQuotient.radical_toQuadraticMap,
    L.radicalQuotient_radical_eq_bot, finrank_bot, add_zero] at hsumQ
  have hdim := L.radical.finrank_quotient_add_finrank
  omega

/-- The radical quotient has the same positive and negative indices as the original lattice and
zero null index. -/
theorem signature_radicalQuotient :
    L.radicalQuotient.signature = (L.sigPos, 0, L.sigNeg) := by
  have hnull : L.radicalQuotient.sigNull = 0 := by
    rw [← L.radicalQuotient.radical_eq_bot_iff_sigNull_eq_zero]
    exact L.radicalQuotient_radical_eq_bot
  simp only [signature, L.sigPos_radicalQuotient, L.sigNeg_radicalQuotient, hnull]

end IntegralLattice

end TauCeti
