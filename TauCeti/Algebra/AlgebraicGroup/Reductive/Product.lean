/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-!
# Products of reductive affine groups

The direct product of two reductive affine groups over a field is reductive. After extending
scalars to an algebraic closure, a connected normal smooth unipotent subgroup of the product maps
to such a subgroup of each factor. Reductivity makes both projection images trivial. Since the
two coordinate inclusions generate the tensor-product coordinate algebra, the original subgroup
is trivial as well.

The proof uses scheme-theoretic images rather than only algebraic-closure-valued points. This
retains normality and is valid in every characteristic.

## Main declaration

* `TauCeti.reductiveCommHopfAlgProperty.tensorProduct`: direct products of reductive finite-type
  affine groups are reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 19.b.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace reductiveCommHopfAlgProperty

variable {k : Type u} [Field k]

private theorem ker_projection_eq_augmentation
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : reductiveCommHopfAlgProperty k H)
    {P : FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)}
    (f : FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H ⟶ P)
    (hf : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (I : HopfIdeal (AlgebraicClosure k) P)
    (hI : I.IsNormal)
    (hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient P I).obj)
    (hunipotent : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient P I)) :
    HopfIdeal.ker
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (f ≫ FiniteTypeCommHopfAlgCat.mkQuotient P I)) =
      HopfIdeal.augmentation (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  let g :
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj ⟶
        (FiniteTypeCommHopfAlgCat.quotient P I).obj :=
    f.hom ≫ (FiniteTypeCommHopfAlgCat.mkQuotient P I).hom
  have hker : HopfIdeal.ker g.hom =
      I.comap (FiniteTypeCommHopfAlgCat.toBialgHom f) := by
    ext x
    rw [HopfIdeal.mem_ker, HopfIdeal.mem_comap]
    change (FiniteTypeCommHopfAlgCat.mkQuotient P I).hom.hom
        (FiniteTypeCommHopfAlgCat.toBialgHom f x) = 0 ↔ _
    exact FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff P I _
  have hnormal : (HopfIdeal.ker g.hom).IsNormal := by
    rw [hker]
    exact hI.comap_of_injective _ hf
  have himageConnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.image g) :=
    geometricallyConnectedCommHopfAlgProperty.image g hconnected
  have hsource := (smoothUnipotentCommHopfAlgProperty_iff _ _).mp hunipotent
  have hsmooth : smoothCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient P I).obj :=
    (smoothCommHopfAlgProperty_iff _).mpr hsource.1
  let _ : Algebra.Smooth (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P I) :=
    hsource.1
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient P I) :=
    isReduced_of_smooth_of_field (AlgebraicClosure k) _
  have himageUnipotent : geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.image g) :=
    geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced g
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mpr hsource.2)
  have himageSmooth : smoothCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.image g) := smoothCommHopfAlgProperty.image g hsmooth
  have himageSmoothUnipotent : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
        (HopfIdeal.ker g.hom)) := by
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    exact ⟨(smoothCommHopfAlgProperty_iff _).mp himageSmooth,
      (geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mp himageUnipotent⟩
  have h := hH.eq_augmentation (HopfIdeal.ker g.hom) hnormal himageConnected
    himageSmoothUnipotent
  exact h

/-- **A direct product of reductive finite-type affine groups is reductive.** -/
theorem tensorProduct (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : reductiveCommHopfAlgProperty k H)
    (hK : reductiveCommHopfAlgProperty k K) :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  let Kbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) K
  let P₀ := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.tensorProduct H K)
  let P := FiniteTypeCommHopfAlgCat.tensorProduct Hbar Kbar
  let e : P₀ ≅ P :=
    FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso (AlgebraicClosure k) H K
  have hsmooth : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
    let smoothH : Algebra.Smooth k H := hH.smooth
    let smoothK : Algebra.Smooth k K := hK.smooth
    let smoothOverH : Algebra.Smooth H (H ⊗[k] K) :=
      @Algebra.Smooth.baseChange k _ K H _ _ _ _ smoothK
    exact @Algebra.Smooth.comp k _ H (H ⊗[k] K) _ _ _ _ _ _ smoothH smoothOverH
  have hconnected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.tensorProduct H K).obj :=
    geometricallyConnectedCommHopfAlgProperty.tensorProduct H.obj K.obj
      hH.geometricallyConnected hK.geometricallyConnected
  rw [reductiveCommHopfAlgProperty_iff]
  refine ⟨hsmooth, hconnected, ?_⟩
  intro I hI hsourceConnected hU
  let q := FiniteTypeCommHopfAlgCat.mkQuotient P₀ I
  let fH := FiniteTypeCommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.includeLeft H K)
  let fK := FiniteTypeCommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.includeRight H K)
  have hfH : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom fH) := by
    have heq : fH ≫ e.hom = FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar :=
      FiniteTypeCommHopfAlgCat.baseChangeMap_includeLeft_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K
    have hincl : Function.Injective
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar)) := by
      intro x y hxy
      have hxy' : x ⊗ₜ[AlgebraicClosure k] (1 : Kbar) =
          y ⊗ₜ[AlgebraicClosure k] (1 : Kbar) := by
        rw [FiniteTypeCommHopfAlgCat.includeLeft_apply Hbar Kbar x,
          FiniteTypeCommHopfAlgCat.includeLeft_apply Hbar Kbar y] at hxy
        exact hxy
      have hmap := congrArg
        (Bialgebra.TensorProduct.projectLeft
          (R := AlgebraicClosure k) (H₁ := Hbar) (H₂ := Kbar)) hxy'
      simpa using hmap
    intro x y hxy
    apply hincl
    rw [← heq]
    simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply] using
      congrArg (FiniteTypeCommHopfAlgCat.toBialgHom e.hom) hxy
  have hfK : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom fK) := by
    have heq : fK ≫ e.hom = FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar :=
      FiniteTypeCommHopfAlgCat.baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K
    have hincl : Function.Injective
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar)) := by
      intro x y hxy
      have hxy' : (1 : Hbar) ⊗ₜ[AlgebraicClosure k] x =
          (1 : Hbar) ⊗ₜ[AlgebraicClosure k] y := by
        rw [FiniteTypeCommHopfAlgCat.includeRight_apply Hbar Kbar x,
          FiniteTypeCommHopfAlgCat.includeRight_apply Hbar Kbar y] at hxy
        exact hxy
      have hmap := congrArg
        (Bialgebra.TensorProduct.projectRight
          (R := AlgebraicClosure k) (H₁ := Hbar) (H₂ := Kbar)) hxy'
      simpa using hmap
    intro x y hxy
    apply hincl
    rw [← heq]
    simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply] using
      congrArg (FiniteTypeCommHopfAlgCat.toBialgHom e.hom) hxy
  have hleft : HopfIdeal.ker
      (FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q)) =
        HopfIdeal.augmentation (AlgebraicClosure k) Hbar := by
    exact ker_projection_eq_augmentation hH fH hfH I hI hsourceConnected hU
  have hright : HopfIdeal.ker
      (FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q)) =
        HopfIdeal.augmentation (AlgebraicClosure k) Kbar := by
    exact ker_projection_eq_augmentation hK fK hfK I hI hsourceConnected hU
  have hq' (x : P) :
      FiniteTypeCommHopfAlgCat.toBialgHom (e.inv ≫ q) x =
        algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
          (Coalgebra.counit x) := by
    dsimp only [P] at x ⊢
    refine TensorProduct.induction_on x (by simp) (fun h l ↦ ?_) (fun x y hx hy ↦ ?_)
    · have hleftMap :
        FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q) h =
          algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
            (Coalgebra.counit h) := by
        have hmem : h - algebraMap (AlgebraicClosure k) Hbar (Coalgebra.counit h) ∈
            HopfIdeal.augmentation (AlgebraicClosure k) Hbar := by
          rw [HopfIdeal.mem_augmentation]
          simp
        have hzero : FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q)
            (h - algebraMap (AlgebraicClosure k) Hbar (Coalgebra.counit h)) = 0 := by
          rw [← HopfIdeal.mem_ker, hleft]
          exact hmem
        rw [map_sub] at hzero
        rw [sub_eq_zero] at hzero
        rw [hzero]
        exact (FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q)).toAlgHom.commutes
          (Coalgebra.counit h)
      have hrightMap :
        FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q) l =
          algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
            (Coalgebra.counit l) := by
        have hmem : l - algebraMap (AlgebraicClosure k) Kbar (Coalgebra.counit l) ∈
            HopfIdeal.augmentation (AlgebraicClosure k) Kbar := by
          rw [HopfIdeal.mem_augmentation]
          simp
        have hzero : FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q)
            (l - algebraMap (AlgebraicClosure k) Kbar (Coalgebra.counit l)) = 0 := by
          rw [← HopfIdeal.mem_ker, hright]
          exact hmem
        rw [map_sub] at hzero
        rw [sub_eq_zero] at hzero
        rw [hzero]
        exact (FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q)).toAlgHom.commutes
          (Coalgebra.counit l)
      have hleftComp := congrArg
        (fun φ ↦ FiniteTypeCommHopfAlgCat.toBialgHom φ h)
        (FiniteTypeCommHopfAlgCat.baseChangeMap_includeLeft_comp_baseChangeTensorProductIso_hom
          (AlgebraicClosure k) H K)
      have hrightComp := congrArg
        (fun φ ↦ FiniteTypeCommHopfAlgCat.toBialgHom φ l)
        (FiniteTypeCommHopfAlgCat.baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom
          (AlgebraicClosure k) H K)
      rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
        FiniteTypeCommHopfAlgCat.includeLeft_apply] at hleftComp
      rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
        FiniteTypeCommHopfAlgCat.includeRight_apply] at hrightComp
      have hinvLeft : FiniteTypeCommHopfAlgCat.toBialgHom e.inv
          (h ⊗ₜ[AlgebraicClosure k] (1 : Kbar)) =
          FiniteTypeCommHopfAlgCat.toBialgHom fH h := by
        apply (ConcreteCategory.bijective_of_isIso e.hom).1
        change FiniteTypeCommHopfAlgCat.toBialgHom e.hom
            (FiniteTypeCommHopfAlgCat.toBialgHom e.inv
              (h ⊗ₜ[AlgebraicClosure k] (1 : Kbar))) =
          FiniteTypeCommHopfAlgCat.toBialgHom e.hom
            (FiniteTypeCommHopfAlgCat.toBialgHom fH h)
        rw [hleftComp]
        have hid := congrArg
          (fun φ ↦ FiniteTypeCommHopfAlgCat.toBialgHom φ
            (h ⊗ₜ[AlgebraicClosure k] (1 : Kbar))) e.inv_hom_id
        simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
          FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.coe_id, id_eq] using hid
      have hinvRight : FiniteTypeCommHopfAlgCat.toBialgHom e.inv
          ((1 : Hbar) ⊗ₜ[AlgebraicClosure k] l) =
          FiniteTypeCommHopfAlgCat.toBialgHom fK l := by
        apply (ConcreteCategory.bijective_of_isIso e.hom).1
        change FiniteTypeCommHopfAlgCat.toBialgHom e.hom
            (FiniteTypeCommHopfAlgCat.toBialgHom e.inv
              ((1 : Hbar) ⊗ₜ[AlgebraicClosure k] l)) =
          FiniteTypeCommHopfAlgCat.toBialgHom e.hom
            (FiniteTypeCommHopfAlgCat.toBialgHom fK l)
        rw [hrightComp]
        have hid := congrArg
          (fun φ ↦ FiniteTypeCommHopfAlgCat.toBialgHom φ
            ((1 : Hbar) ⊗ₜ[AlgebraicClosure k] l)) e.inv_hom_id
        simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
          FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.coe_id, id_eq] using hid
      calc
        FiniteTypeCommHopfAlgCat.toBialgHom (e.inv ≫ q)
            (h ⊗ₜ[AlgebraicClosure k] l) =
            FiniteTypeCommHopfAlgCat.toBialgHom (e.inv ≫ q)
              ((h ⊗ₜ[AlgebraicClosure k] (1 : Kbar)) *
                ((1 : Hbar) ⊗ₜ[AlgebraicClosure k] l)) := by simp
        _ = FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q) h *
            FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q) l := by
          simp only [map_mul, FiniteTypeCommHopfAlgCat.toBialgHom_comp,
            BialgHom.comp_apply, hinvLeft, hinvRight]
        _ = _ := by rw [hleftMap, hrightMap, mul_comm]; simp
    · simp only [map_add, hx, hy]
  have hq (x : P₀) :
      FiniteTypeCommHopfAlgCat.toBialgHom q x =
        algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
          (Coalgebra.counit x) := by
    have h := hq' (FiniteTypeCommHopfAlgCat.toBialgHom e.hom x)
    rw [← e.hom_inv_id_assoc q]
    simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
      CoalgHomClass.counit_comp_apply] using h
  apply SetLike.ext
  intro x
  rw [HopfIdeal.mem_augmentation]
  change x ∈ I.toIdeal ↔ _
  rw [← FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff P₀ I]
  rw [hq]
  constructor
  · intro hx
    have h := congrArg
      (Coalgebra.counit (R := AlgebraicClosure k)
        (A := FiniteTypeCommHopfAlgCat.quotient P₀ I)) hx
    simpa using h
  · intro hx
    simp [hx]

end reductiveCommHopfAlgProperty

end

end TauCeti
