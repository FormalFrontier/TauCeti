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

* `TauCeti.extEuler_shortExact₂` and `TauCeti.extEuler_shortExact₁`: additivity in the second
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

private theorem alternating_finrank_sub_add_sub_correction
    {A B D : ℕ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
    (tA tB tD : ℕ → ℤ)
    (f : ∀ n, A n →ₗ[k] B n) (g : ∀ n, B n →ₗ[k] D n)
    (δ : ∀ n, D n →ₗ[k] A (n + 1))
    (hA : ∀ n, FiniteDimensional k (A n))
    (hB : ∀ n, FiniteDimensional k (B n))
    (hD : ∀ n, FiniteDimensional k (D n))
    (htA0 : tA 0 = 0) (htB0 : tB 0 = 0) (htD0 : tD 0 = 0)
    (htA : ∀ n, tA (n + 1) = tA n + (-1 : ℤ) ^ n * Module.finrank k (A n))
    (htB : ∀ n, tB (n + 1) = tB n + (-1 : ℤ) ^ n * Module.finrank k (B n))
    (htD : ∀ n, tD (n + 1) = tD n + (-1 : ℤ) ^ n * Module.finrank k (D n))
    (hinj : Function.Injective (f 0))
    (hfg : ∀ n, Function.Exact (f n) (g n))
    (hgδ : ∀ n, Function.Exact (g n) (δ n))
    (hδf : ∀ n, Function.Exact (δ n) (f (n + 1))) (N : ℕ) :
    tB N - tA N - tD N =
      (-1 : ℤ) ^ N * Module.finrank k (f N).ker := by
  induction N with
  | zero =>
      rw [htA0, htB0, htD0, LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
      simp
  | succ N ih =>
      let _ := hA N
      let _ := hB N
      let _ := hD N
      have hd := finrank_sub_finrank_sub_finrank_of_exact (f N) (g N) (δ N) (f (N + 1))
        (hfg N) (hgδ N) (hδf N)
      rw [htA, htB, htD]
      calc
        _ = (tB N - tA N - tD N) +
            (-1 : ℤ) ^ N * ((Module.finrank k (B N) : ℤ) -
              Module.finrank k (A N) - Module.finrank k (D N)) := by ring
        _ = (-1 : ℤ) ^ N * Module.finrank k (f N).ker +
            (-1 : ℤ) ^ N * ((Module.finrank k (B N) : ℤ) -
              Module.finrank k (A N) - Module.finrank k (D N)) := by rw [ih]
        _ = (-1 : ℤ) ^ N * Module.finrank k (f N).ker +
            (-1 : ℤ) ^ N * (-(Module.finrank k (f N).ker : ℤ) -
              Module.finrank k (f (N + 1)).ker) := by rw [hd]
        _ = (-1 : ℤ) ^ (N + 1) * Module.finrank k (f (N + 1)).ker := by
          rw [pow_succ]
          ring

private theorem truncatedExtEuler_shortExact_correction₂ {S : ShortComplex C} (hS : S.ShortExact)
    (X : C)
    (h₁ : IsExtFinite.{w} k X S.X₁) (h₂ : IsExtFinite.{w} k X S.X₂)
    (h₃ : IsExtFinite.{w} k X S.X₃) (N : ℕ) :
    truncatedExtEuler.{w} k X S.X₂ N - truncatedExtEuler.{w} k X S.X₁ N -
        truncatedExtEuler.{w} k X S.X₃ N =
      (-1 : ℤ) ^ N * Module.finrank k
        (Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero N)).ker := by
  let _ := hS.mono_f
  apply alternating_finrank_sub_add_sub_correction
    (tA := fun n ↦ truncatedExtEuler.{w} k X S.X₁ n)
    (tB := fun n ↦ truncatedExtEuler.{w} k X S.X₂ n)
    (tD := fun n ↦ truncatedExtEuler.{w} k X S.X₃ n)
    (f := fun n ↦ Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero n))
    (g := fun n ↦ Ext.postcompOfLinear (Ext.mk₀ S.g) k X (add_zero n))
    (δ := fun n ↦ Ext.postcompOfLinear hS.extClass k X rfl)
    (fun n ↦ h₁.finiteDimensional n) (fun n ↦ h₂.finiteDimensional n)
    (fun n ↦ h₃.finiteDimensional n)
    (truncatedExtEuler_zero k X S.X₁) (truncatedExtEuler_zero k X S.X₂)
    (truncatedExtEuler_zero k X S.X₃)
    (fun n ↦ truncatedExtEuler_succ k X S.X₁ n)
    (fun n ↦ truncatedExtEuler_succ k X S.X₂ n)
    (fun n ↦ truncatedExtEuler_succ k X S.X₃ n)
    (Ext.postcomp_mk₀_injective_of_mono X S.f)
    (fun n ↦ exact_postcompOfLinear k hS X n)
  · intro n
    have h := Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  · intro n
    have h := Ext.covariant_sequence_exact₁' X hS n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h

private theorem truncatedExtEuler_shortExact_correction₁ {S : ShortComplex C} (hS : S.ShortExact)
    (Y : C) (h₁ : IsExtFinite.{w} k S.X₁ Y) (h₂ : IsExtFinite.{w} k S.X₂ Y)
    (h₃ : IsExtFinite.{w} k S.X₃ Y) (N : ℕ) :
    truncatedExtEuler.{w} k S.X₂ Y N - truncatedExtEuler.{w} k S.X₃ Y N -
        truncatedExtEuler.{w} k S.X₁ Y N =
      (-1 : ℤ) ^ N * Module.finrank k
        (Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add N)).ker := by
  let _ := hS.epi_g
  apply alternating_finrank_sub_add_sub_correction
    (tA := fun n ↦ truncatedExtEuler.{w} k S.X₃ Y n)
    (tB := fun n ↦ truncatedExtEuler.{w} k S.X₂ Y n)
    (tD := fun n ↦ truncatedExtEuler.{w} k S.X₁ Y n)
    (f := fun n ↦ Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add n))
    (g := fun n ↦ Ext.precompOfLinear (Ext.mk₀ S.f) k Y (zero_add n))
    (δ := fun n ↦ Ext.precompOfLinear hS.extClass k Y (Nat.one_add n))
    (fun n ↦ h₃.finiteDimensional n) (fun n ↦ h₂.finiteDimensional n)
    (fun n ↦ h₁.finiteDimensional n)
    (truncatedExtEuler_zero k S.X₃ Y) (truncatedExtEuler_zero k S.X₂ Y)
    (truncatedExtEuler_zero k S.X₁ Y)
    (fun n ↦ truncatedExtEuler_succ k S.X₃ Y n)
    (fun n ↦ truncatedExtEuler_succ k S.X₂ Y n)
    (fun n ↦ truncatedExtEuler_succ k S.X₁ Y n)
    (Ext.precomp_mk₀_injective_of_epi Y S.g)
    (fun n ↦ exact_precompOfLinear k hS Y n)
  · intro n
    have h := Ext.contravariant_sequence_exact₁' hS Y n (n + 1) (Nat.one_add n)
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  · exact fun n ↦ exact_precompOfLinear₃ k hS Y n (n + 1) (Nat.one_add n)

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
  have h := truncatedExtEuler_shortExact_correction₂ hS X h₁.isExtFinite h₂.isExtFinite
    h₃.isExtFinite N
  let _ := hb₁.subsingleton (le_refl N)
  have hz : Module.finrank k
      (Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero N)).ker = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [extEuler_eq k h₁ hb₁, extEuler_eq k h₂ hb₂, extEuler_eq k h₃ hb₃]
  rw [hz, Int.ofNat_zero, mul_zero] at h
  omega

/-- The Ext-Euler characteristic is additive on a short exact sequence in its first variable. -/
theorem extEuler_shortExact₁ {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
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
  have h := truncatedExtEuler_shortExact_correction₁ hS Y h₁.isExtFinite h₂.isExtFinite
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

private noncomputable def extEulerRightAdditiveInvariant
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) :
    ExactK0.RightAdditiveInvariant P.FullSubcategory
      ((ExactStructure.abelian C).fullSubcategory Q hQ) ℤ where
  obj X Y := extEuler.{w} k (h.isEulerAdmissible X.property Y.property)
  map_iso₁ {X X'} e Y :=
    extEuler_of_iso (h.isEulerAdmissible X.property Y.property)
      (h.isEulerAdmissible X'.property Y.property) (P.ι.mapIso e) (Iso.refl Y.obj)
  map_iso₂ X {Y Y'} e :=
    extEuler_of_iso (h.isEulerAdmissible X.property Y.property)
      (h.isEulerAdmissible X.property Y'.property) (Iso.refl X.obj) (Q.ι.mapIso e)
  map_conflation₂ X {S} hS := by
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
  (extEulerRightAdditiveInvariant hQ h).rightLift X

omit [ObjectProperty.EssentiallySmall.{w} P] [P.ContainsZero]
  [P.IsClosedUnderBinaryProducts] in
@[simp]
theorem extEulerRight_of
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) (X : P.FullSubcategory)
    (Y : Q.FullSubcategory) :
    extEulerRight hQ h X (ExactK0.of Y) =
      extEuler.{w} k (h.isEulerAdmissible X.property Y.property) :=
  ExactK0.RightAdditiveInvariant.rightLift_of _ X Y

private noncomputable def extEulerBiadditiveInvariant
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) :
    ExactK0.BiadditiveInvariant ((ExactStructure.abelian C).fullSubcategory P hP)
      ((ExactStructure.abelian C).fullSubcategory Q hQ) ℤ where
  toRightAdditiveInvariant := extEulerRightAdditiveInvariant hQ h
  map_conflation₁ {S} hS Y := by
    have hc : (ExactStructure.abelian C).Conflation (S.map P.ι) :=
      (ExactStructure.fullSubcategory_conflation_iff hP S).mp hS
    have hS' : (S.map P.ι).ShortExact := (ExactStructure.abelian_conflation _).mp hc
    exact extEuler_shortExact₁ hS' Y.obj
      (h.isEulerAdmissible S.X₁.property Y.property)
      (h.isEulerAdmissible S.X₂.property Y.property)
      (h.isEulerAdmissible S.X₃.property Y.property)

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
  (extEulerBiadditiveInvariant hP hQ h).bilift

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
  exact ExactK0.BiadditiveInvariant.bilift_of_of _ X Y

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
  exact ExactK0.BiadditiveInvariant.bilift_unique _ b hb

end TauCeti
