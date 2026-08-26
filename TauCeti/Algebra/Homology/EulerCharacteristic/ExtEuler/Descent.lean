/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian

/-!
# Additivity and descent of the Ext-Euler characteristic

This file proves that the Ext-Euler characteristic is additive along a short exact sequence in
either variable. The proof cuts the long exact `Ext` sequence off at a common vanishing bound;
the correction term at a truncation is the rank of the next boundary map, and it vanishes at the
chosen bound.

For extension-closed object properties `P` and `Q`, an Euler-admissibility hypothesis on every
pair in `P × Q` then gives a biadditive pairing between the exact Grothendieck groups of the two
full subcategories.

## Main results

* `TauCeti.extEuler_shortExact₂` and `TauCeti.extEuler_shortExact₂'`: additivity in the second
  and first variables.
* `TauCeti.extEulerPairing`: descent to a biadditive pairing on the exact `K₀` groups of two
  extension-closed full subcategories.
* `TauCeti.extEulerPairing_of_of` and `TauCeti.extEulerPairing_unique`: the computation rule and
  universal characterization of the descended pairing.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7, for the long exact
  `Ext` sequences used in the additivity argument.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C]

private theorem finrank_eq_finrank_range_add_finrank_range_of_exact
    {U V W : Type*} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : Function.Exact f g) :
    Module.finrank k V = Module.finrank k f.range + Module.finrank k g.range := by
  have hr := g.finrank_range_add_finrank_ker
  rw [h.linearMap_ker_eq] at hr
  omega

private theorem finrank_sub_finrank_sub_finrank_of_exact
    {A B C D E : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    [AddCommGroup E] [Module k E]
    [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (δ : C →ₗ[k] D) (f' : D →ₗ[k] E)
    (hfg : Function.Exact f g) (hgδ : Function.Exact g δ)
    (hδf : Function.Exact δ f') :
    (Module.finrank k B : ℤ) - Module.finrank k A - Module.finrank k C =
      -(Module.finrank k f.ker : ℤ) - Module.finrank k f'.ker := by
  have hB := finrank_eq_finrank_range_add_finrank_range_of_exact f g hfg
  have hC := finrank_eq_finrank_range_add_finrank_range_of_exact g δ hgδ
  have hA := f.finrank_range_add_finrank_ker
  have hker : Module.finrank k f'.ker = Module.finrank k δ.range :=
    congrArg (fun S : Submodule k D ↦ Module.finrank k S) hδf.linearMap_ker_eq
  omega

private theorem truncatedExtEuler_sub_add_sub_correction {S : ShortComplex C} (hS : S.ShortExact)
    (X : C)
    (h₁ : IsExtFinite.{w} k X S.X₁) (h₂ : IsExtFinite.{w} k X S.X₂)
    (h₃ : IsExtFinite.{w} k X S.X₃) (N : ℕ) :
    truncatedExtEuler.{w} k X S.X₂ N - truncatedExtEuler.{w} k X S.X₁ N -
        truncatedExtEuler.{w} k X S.X₃ N =
      (-1 : ℤ) ^ N * Module.finrank k
        (Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero N)).ker := by
  induction N with
  | zero =>
      let _ := hS.mono_f
      have hinj : Function.Injective
          (Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero 0)) :=
        Ext.postcomp_mk₀_injective_of_mono X S.f
      rw [truncatedExtEuler_zero, truncatedExtEuler_zero, truncatedExtEuler_zero,
        LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
      simp
  | succ N ih =>
      let f := Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero N)
      let g := Ext.postcompOfLinear (Ext.mk₀ S.g) k X (add_zero N)
      let δ : Ext.{w} X S.X₃ N →ₗ[k] Ext.{w} X S.X₁ (N + 1) :=
        Ext.postcompOfLinear hS.extClass k X rfl
      let f' := Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero (N + 1))
      let _ := h₁.finiteDimensional N
      let _ := h₂.finiteDimensional N
      let _ := h₃.finiteDimensional N
      have hfg : Function.Exact f g := exact_postcompOfLinear k hS X N
      have hgδ : Function.Exact g δ := by
        have h := Ext.covariant_sequence_exact₃' X hS N (N + 1) rfl
        rw [ShortComplex.ab_exact_iff_function_exact] at h
        -- Mathlib states this with `AddCommGrpCat.ofHom`; expose the underlying linear maps.
        change Function.Exact g δ at h
        exact h
      have hδf : Function.Exact δ f' := by
        have h := Ext.covariant_sequence_exact₁' X hS N (N + 1) rfl
        rw [ShortComplex.ab_exact_iff_function_exact] at h
        -- Mathlib states this with `AddCommGrpCat.ofHom`; expose the underlying linear maps.
        change Function.Exact δ f' at h
        exact h
      have hd := finrank_sub_finrank_sub_finrank_of_exact f g δ f' hfg hgδ hδf
      rw [truncatedExtEuler_succ, truncatedExtEuler_succ, truncatedExtEuler_succ]
      let d₁ : ℤ := Module.finrank k (Ext.{w} X S.X₁ N)
      let d₂ : ℤ := Module.finrank k (Ext.{w} X S.X₂ N)
      let d₃ : ℤ := Module.finrank k (Ext.{w} X S.X₃ N)
      -- Normalize the successor sums and local map abbreviations for the rank calculation.
      change truncatedExtEuler.{w} k X S.X₂ N + (-1 : ℤ) ^ N * d₂ -
          (truncatedExtEuler.{w} k X S.X₁ N + (-1 : ℤ) ^ N * d₁) -
          (truncatedExtEuler.{w} k X S.X₃ N + (-1 : ℤ) ^ N * d₃) = _
      change _ = (-1 : ℤ) ^ (N + 1) * Module.finrank k f'.ker
      change truncatedExtEuler.{w} k X S.X₂ N - truncatedExtEuler.{w} k X S.X₁ N -
          truncatedExtEuler.{w} k X S.X₃ N =
        (-1 : ℤ) ^ N * Module.finrank k f.ker at ih
      change d₂ - d₁ - d₃ =
        -(Module.finrank k f.ker : ℤ) - Module.finrank k f'.ker at hd
      calc
        _ = (truncatedExtEuler.{w} k X S.X₂ N - truncatedExtEuler.{w} k X S.X₁ N -
              truncatedExtEuler.{w} k X S.X₃ N) +
            (-1 : ℤ) ^ N * (d₂ - d₁ - d₃) := by ring
        _ = (-1 : ℤ) ^ N * Module.finrank k f.ker +
            (-1 : ℤ) ^ N * (d₂ - d₁ - d₃) := by rw [ih]
        _ = (-1 : ℤ) ^ N * Module.finrank k f.ker +
            (-1 : ℤ) ^ N * (-(Module.finrank k f.ker : ℤ) -
              Module.finrank k f'.ker) := by rw [hd]
        _ = (-1 : ℤ) ^ (N + 1) * Module.finrank k f'.ker := by
          rw [pow_succ]
          ring

private theorem truncatedExtEuler_sub_sub_correction' {S : ShortComplex C} (hS : S.ShortExact)
    (Y : C) (h₁ : IsExtFinite.{w} k S.X₁ Y) (h₂ : IsExtFinite.{w} k S.X₂ Y)
    (h₃ : IsExtFinite.{w} k S.X₃ Y) (N : ℕ) :
    truncatedExtEuler.{w} k S.X₂ Y N - truncatedExtEuler.{w} k S.X₃ Y N -
        truncatedExtEuler.{w} k S.X₁ Y N =
      (-1 : ℤ) ^ N * Module.finrank k
        (Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add N)).ker := by
  induction N with
  | zero =>
      let _ := hS.epi_g
      have hinj : Function.Injective
          (Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add 0)) :=
        Ext.precomp_mk₀_injective_of_epi Y S.g
      rw [truncatedExtEuler_zero, truncatedExtEuler_zero, truncatedExtEuler_zero,
        LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
      simp
  | succ N ih =>
      let f := Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add N)
      let g := Ext.precompOfLinear (Ext.mk₀ S.f) k Y (zero_add N)
      let δ : Ext.{w} S.X₁ Y N →ₗ[k] Ext.{w} S.X₃ Y (N + 1) :=
        Ext.precompOfLinear hS.extClass k Y (Nat.one_add N)
      let f' := Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add (N + 1))
      let _ := h₁.finiteDimensional N
      let _ := h₂.finiteDimensional N
      let _ := h₃.finiteDimensional N
      have hfg : Function.Exact f g := exact_precompOfLinear k hS Y N
      have hgδ : Function.Exact g δ := by
        have h := Ext.contravariant_sequence_exact₁' hS Y N (N + 1) (Nat.one_add N)
        rw [ShortComplex.ab_exact_iff_function_exact] at h
        -- Mathlib states this with `AddCommGrpCat.ofHom`; expose the underlying linear maps.
        change Function.Exact g δ at h
        exact h
      have hδf : Function.Exact δ f' := by
        have h := Ext.contravariant_sequence_exact₃' hS Y N (N + 1) (Nat.one_add N)
        rw [ShortComplex.ab_exact_iff_function_exact] at h
        -- Mathlib states this with `AddCommGrpCat.ofHom`; expose the underlying linear maps.
        change Function.Exact δ f' at h
        exact h
      have hd := finrank_sub_finrank_sub_finrank_of_exact f g δ f' hfg hgδ hδf
      rw [truncatedExtEuler_succ, truncatedExtEuler_succ, truncatedExtEuler_succ]
      let d₁ : ℤ := Module.finrank k (Ext.{w} S.X₃ Y N)
      let d₂ : ℤ := Module.finrank k (Ext.{w} S.X₂ Y N)
      let d₃ : ℤ := Module.finrank k (Ext.{w} S.X₁ Y N)
      -- Normalize the successor sums and local map abbreviations for the rank calculation.
      change truncatedExtEuler.{w} k S.X₂ Y N + (-1 : ℤ) ^ N * d₂ -
          (truncatedExtEuler.{w} k S.X₃ Y N + (-1 : ℤ) ^ N * d₁) -
          (truncatedExtEuler.{w} k S.X₁ Y N + (-1 : ℤ) ^ N * d₃) = _
      change _ = (-1 : ℤ) ^ (N + 1) * Module.finrank k f'.ker
      change truncatedExtEuler.{w} k S.X₂ Y N - truncatedExtEuler.{w} k S.X₃ Y N -
          truncatedExtEuler.{w} k S.X₁ Y N =
        (-1 : ℤ) ^ N * Module.finrank k f.ker at ih
      change d₂ - d₁ - d₃ =
        -(Module.finrank k f.ker : ℤ) - Module.finrank k f'.ker at hd
      calc
        _ = (truncatedExtEuler.{w} k S.X₂ Y N - truncatedExtEuler.{w} k S.X₃ Y N -
              truncatedExtEuler.{w} k S.X₁ Y N) +
            (-1 : ℤ) ^ N * (d₂ - d₁ - d₃) := by ring
        _ = (-1 : ℤ) ^ N * Module.finrank k f.ker +
            (-1 : ℤ) ^ N * (d₂ - d₁ - d₃) := by rw [ih]
        _ = (-1 : ℤ) ^ N * Module.finrank k f.ker +
            (-1 : ℤ) ^ N * (-(Module.finrank k f.ker : ℤ) -
              Module.finrank k f'.ker) := by rw [hd]
        _ = (-1 : ℤ) ^ (N + 1) * Module.finrank k f'.ker := by
          rw [pow_succ]
          ring

/-! ### Additivity on short exact sequences -/

/-- The Ext-Euler characteristic is additive on a short exact sequence in its second variable. -/
theorem extEuler_shortExact₂ {S : ShortComplex C} (hS : S.ShortExact) (X : C)
    (h₁ : IsEulerAdmissible.{w} k X S.X₁) (h₂ : IsEulerAdmissible.{w} k X S.X₂)
    (h₃ : IsEulerAdmissible.{w} k X S.X₃) :
    extEuler.{w} k h₂ = extEuler.{w} k h₁ + extEuler.{w} k h₃ := by
  obtain ⟨N₁, hN₁⟩ := h₁.isExtBounded.exists_bound
  obtain ⟨N₂, hN₂⟩ := h₂.isExtBounded.exists_bound
  obtain ⟨N₃, hN₃⟩ := h₃.isExtBounded.exists_bound
  let N := max N₁ (max N₂ N₃)
  have hb₁ : IsExtBoundedBy.{w} X S.X₁ N := hN₁.mono (le_max_left _ _)
  have hb₂ : IsExtBoundedBy.{w} X S.X₂ N :=
    hN₂.mono ((le_max_left _ _).trans (le_max_right _ _))
  have hb₃ : IsExtBoundedBy.{w} X S.X₃ N :=
    hN₃.mono ((le_max_right _ _).trans (le_max_right _ _))
  have h := truncatedExtEuler_sub_add_sub_correction hS X h₁.isExtFinite h₂.isExtFinite
    h₃.isExtFinite N
  let _ := hb₁.subsingleton (le_refl N)
  have hz : Module.finrank k
      (Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero N)).ker = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [extEuler_eq k h₁ hb₁, extEuler_eq k h₂ hb₂, extEuler_eq k h₃ hb₃]
  rw [hz, Int.ofNat_zero, mul_zero] at h
  omega

/-- The Ext-Euler characteristic is additive on a short exact sequence in its first variable. -/
theorem extEuler_shortExact₂' {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (h₁ : IsEulerAdmissible.{w} k S.X₁ Y) (h₂ : IsEulerAdmissible.{w} k S.X₂ Y)
    (h₃ : IsEulerAdmissible.{w} k S.X₃ Y) :
    extEuler.{w} k h₂ = extEuler.{w} k h₁ + extEuler.{w} k h₃ := by
  obtain ⟨N₁, hN₁⟩ := h₁.isExtBounded.exists_bound
  obtain ⟨N₂, hN₂⟩ := h₂.isExtBounded.exists_bound
  obtain ⟨N₃, hN₃⟩ := h₃.isExtBounded.exists_bound
  let N := max N₁ (max N₂ N₃)
  have hb₁ : IsExtBoundedBy.{w} S.X₁ Y N := hN₁.mono (le_max_left _ _)
  have hb₂ : IsExtBoundedBy.{w} S.X₂ Y N :=
    hN₂.mono ((le_max_left _ _).trans (le_max_right _ _))
  have hb₃ : IsExtBoundedBy.{w} S.X₃ Y N :=
    hN₃.mono ((le_max_right _ _).trans (le_max_right _ _))
  have h := truncatedExtEuler_sub_sub_correction' hS Y h₁.isExtFinite h₂.isExtFinite
    h₃.isExtFinite N
  let _ := hb₃.subsingleton (le_refl N)
  have hz : Module.finrank k
      (Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add N)).ker = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [extEuler_eq k h₁ hb₁, extEuler_eq k h₂ hb₂, extEuler_eq k h₃ hb₃]
  rw [hz, Int.ofNat_zero, mul_zero] at h
  omega

/-! ### Descent to exact Grothendieck groups -/

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

private noncomputable def extEulerRightInvariant
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) (X : P.FullSubcategory) :
    ExactK0.AdditiveInvariant ((ExactStructure.abelian C).fullSubcategory Q hQ) ℤ where
  obj Y := extEuler.{w} k (h.isEulerAdmissible X.property Y.property)
  map_iso {Y Y'} e :=
    extEuler_of_iso (h.isEulerAdmissible X.property Y.property)
      (h.isEulerAdmissible X.property Y'.property) (Iso.refl X.obj) (Q.ι.mapIso e)
  map_conflation {S} hS := by
    have hc : (ExactStructure.abelian C).Conflation (S.map Q.ι) :=
      (ExactStructure.fullSubcategory_conflation_iff hQ S).mp hS
    have hS' : (S.map Q.ι).ShortExact := (ExactStructure.abelian_conflation _).mp hc
    exact extEuler_shortExact₂ hS' X.obj
      (h.isEulerAdmissible X.property S.X₁.property)
      (h.isEulerAdmissible X.property S.X₂.property)
      (h.isEulerAdmissible X.property S.X₃.property)

/-- For a fixed object in `P`, the Ext-Euler characteristic descends in the second variable to
the exact `K₀` of the extension-closed full subcategory on `Q`. -/
noncomputable def extEulerRight
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) (X : P.FullSubcategory) :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ ℤ :=
  ExactK0.lift (extEulerRightInvariant hQ h X)

omit [ObjectProperty.EssentiallySmall.{w} P] [P.ContainsZero]
  [P.IsClosedUnderBinaryProducts] in
@[simp]
theorem extEulerRight_of
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) (X : P.FullSubcategory)
    (Y : Q.FullSubcategory) :
    extEulerRight hQ h X (ExactK0.of Y) =
      extEuler.{w} k (h.isEulerAdmissible X.property Y.property) :=
  ExactK0.lift_of _ Y

omit [ObjectProperty.EssentiallySmall.{w} P] [P.ContainsZero]
  [P.IsClosedUnderBinaryProducts] in
private theorem extEulerRight_congr
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) {X X' : P.FullSubcategory} (e : X ≅ X') :
    extEulerRight hQ h X = extEulerRight hQ h X' := by
  refine ExactK0.hom_ext fun Y ↦ ?_
  rw [extEulerRight_of, extEulerRight_of]
  exact extEuler_of_iso (h.isEulerAdmissible X.property Y.property)
    (h.isEulerAdmissible X'.property Y.property) (P.ι.mapIso e) (Iso.refl Y.obj)

omit [ObjectProperty.EssentiallySmall.{w} P] in
private theorem extEulerRight_conflation
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) {S : ShortComplex P.FullSubcategory}
    (hS : ((ExactStructure.abelian C).fullSubcategory P hP).Conflation S) :
    extEulerRight hQ h S.X₂ = extEulerRight hQ h S.X₁ + extEulerRight hQ h S.X₃ := by
  refine ExactK0.hom_ext fun Y ↦ ?_
  simp only [extEulerRight_of, AddMonoidHom.add_apply]
  have hc : (ExactStructure.abelian C).Conflation (S.map P.ι) :=
    (ExactStructure.fullSubcategory_conflation_iff hP S).mp hS
  have hS' : (S.map P.ι).ShortExact := (ExactStructure.abelian_conflation _).mp hc
  exact extEuler_shortExact₂' hS' Y.obj
    (h.isEulerAdmissible S.X₁.property Y.property)
    (h.isEulerAdmissible S.X₂.property Y.property)
    (h.isEulerAdmissible S.X₃.property Y.property)

private noncomputable def extEulerLeftInvariant
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) :
    ExactK0.AdditiveInvariant ((ExactStructure.abelian C).fullSubcategory P hP)
  (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ ℤ) where
  obj := extEulerRight hQ h
  map_iso := fun {_ _} e ↦ extEulerRight_congr (P := P) (Q := Q) hQ h e
  map_conflation := fun {_} hS ↦
    extEulerRight_conflation (P := P) (Q := Q) hP hQ h hS

/-- **The Ext-Euler pairing on Grothendieck groups.** If `P` and `Q` are extension-closed
additive object properties and every pair in `P × Q` is Euler-admissible, the object-level
Ext-Euler characteristic descends to a map additive in both variables on their exact `K₀`
groups. The two groups are kept distinct: the pairing need not be symmetric. -/
noncomputable def extEulerPairing
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →+
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ ℤ :=
  ExactK0.lift (extEulerLeftInvariant hP hQ h)

/-- The descended pairing evaluates on object classes as the original Ext-Euler
characteristic. -/
@[simp]
theorem extEulerPairing_of_of
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) (X : P.FullSubcategory)
    (Y : Q.FullSubcategory) :
    extEulerPairing hP hQ h (ExactK0.of X) (ExactK0.of Y) =
      extEuler.{w} k (h.isEulerAdmissible X.property Y.property) := by
  rw [extEulerPairing, ExactK0.lift_of, extEulerLeftInvariant, extEulerRight_of]

/-- The Ext-Euler pairing is the unique biadditive map with the prescribed values on pairs of
object classes. -/
theorem extEulerPairing_unique
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q)
    (b : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →+
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ ℤ)
    (hb : ∀ (X : P.FullSubcategory) (Y : Q.FullSubcategory),
      b (ExactK0.of X) (ExactK0.of Y) =
        extEuler.{w} k (h.isEulerAdmissible X.property Y.property)) :
    b = extEulerPairing hP hQ h := by
  refine ExactK0.hom_ext fun X ↦ ExactK0.hom_ext fun Y ↦ ?_
  rw [hb, extEulerPairing_of_of]

end TauCeti
