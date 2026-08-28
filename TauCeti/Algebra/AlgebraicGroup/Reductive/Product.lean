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
    -- Unfold the categorical composite just enough to expose the underlying quotient map;
    -- `mkQuotient_eq_zero_iff` is stated for this concrete map rather than its wrappers.
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

private theorem injective_of_retraction
    {H L : Type u} [CommRing H] [CommRing L]
    [Bialgebra (AlgebraicClosure k) H] [Bialgebra (AlgebraicClosure k) L]
    (i : H →ₐc[AlgebraicClosure k] L) (r : L →ₐc[AlgebraicClosure k] H)
    (hri : r.comp i = BialgHom.id (AlgebraicClosure k) H) :
    Function.Injective i := by
  intro x y hxy
  have := congrArg r hxy
  simpa only [← BialgHom.comp_apply, hri, BialgHom.id_apply] using this

private theorem injective_of_comp_iso
    {H L M : FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)}
    (f : H ⟶ L) (e : L ≅ M) (g : H ⟶ M) (hfg : f ≫ e.hom = g)
    (hg : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom g)) :
    Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom f) := by
  intro x y hxy
  apply hg
  rw [← hfg]
  simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply] using
    congrArg (FiniteTypeCommHopfAlgCat.toBialgHom e.hom) hxy

private theorem map_eq_counit_of_ker_eq_augmentation
    {H L : FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)}
    (f : H ⟶ L)
    (hf : HopfIdeal.ker (FiniteTypeCommHopfAlgCat.toBialgHom f) =
      HopfIdeal.augmentation (AlgebraicClosure k) H) (x : H) :
    FiniteTypeCommHopfAlgCat.toBialgHom f x =
      algebraMap (AlgebraicClosure k) L (Coalgebra.counit x) := by
  have hmem : x - algebraMap (AlgebraicClosure k) H (Coalgebra.counit x) ∈
      HopfIdeal.augmentation (AlgebraicClosure k) H := by
    rw [HopfIdeal.mem_augmentation]
    simp
  have hzero : FiniteTypeCommHopfAlgCat.toBialgHom f
      (x - algebraMap (AlgebraicClosure k) H (Coalgebra.counit x)) = 0 := by
    rw [← HopfIdeal.mem_ker, hf]
    exact hmem
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero]
  exact (FiniteTypeCommHopfAlgCat.toBialgHom f).toAlgHom.commutes (Coalgebra.counit x)

private theorem restriction_eq_counit
    {H L M : FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)}
    (i : H ⟶ L) (g : L ⟶ M) (f : H ⟶ M) (hcomp : i ≫ g = f)
    (hf : HopfIdeal.ker (FiniteTypeCommHopfAlgCat.toBialgHom f) =
      HopfIdeal.augmentation (AlgebraicClosure k) H) :
    (FiniteTypeCommHopfAlgCat.toBialgHom g).toAlgHom.comp
        (FiniteTypeCommHopfAlgCat.toBialgHom i).toAlgHom =
      (Algebra.ofId (AlgebraicClosure k) M).comp
        (Bialgebra.counitAlgHom (AlgebraicClosure k) H) := by
  apply AlgHom.ext
  intro x
  have h := congrArg (fun φ : H ⟶ M ↦ FiniteTypeCommHopfAlgCat.toBialgHom φ x) hcomp
  rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply] at h
  exact h.trans (map_eq_counit_of_ker_eq_augmentation f hf x)

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
          (FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar)) :=
      injective_of_retraction
        (Bialgebra.TensorProduct.includeLeft
          (R := AlgebraicClosure k) (H₁ := Hbar) (H₂ := Kbar))
        (Bialgebra.TensorProduct.projectLeft
          (R := AlgebraicClosure k) (H₁ := Hbar) (H₂ := Kbar))
        Bialgebra.TensorProduct.projectLeft_comp_includeLeft
    exact injective_of_comp_iso fH e
      (FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar) heq hincl
  have hfK : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom fK) := by
    have heq : fK ≫ e.hom = FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar :=
      FiniteTypeCommHopfAlgCat.baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K
    have hincl : Function.Injective
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar)) :=
      injective_of_retraction
        (Bialgebra.TensorProduct.includeRight
          (R := AlgebraicClosure k) (H₁ := Hbar) (H₂ := Kbar))
        (Bialgebra.TensorProduct.projectRight
          (R := AlgebraicClosure k) (H₁ := Hbar) (H₂ := Kbar))
        Bialgebra.TensorProduct.projectRight_comp_includeRight
    exact injective_of_comp_iso fK e
      (FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar) heq hincl
  have hleft : HopfIdeal.ker
      (FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q)) =
        HopfIdeal.augmentation (AlgebraicClosure k) Hbar := by
    exact ker_projection_eq_augmentation hH fH hfH I hI hsourceConnected hU
  have hright : HopfIdeal.ker
      (FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q)) =
        HopfIdeal.augmentation (AlgebraicClosure k) Kbar := by
    exact ker_projection_eq_augmentation hK fK hfK I hI hsourceConnected hU
  let g : P →ₐ[AlgebraicClosure k] (FiniteTypeCommHopfAlgCat.quotient P₀ I) :=
    (FiniteTypeCommHopfAlgCat.toBialgHom (e.inv ≫ q)).toAlgHom
  let ε : P →ₐ[AlgebraicClosure k] (FiniteTypeCommHopfAlgCat.quotient P₀ I) :=
    (Algebra.ofId (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)).comp
      (Bialgebra.counitAlgHom (AlgebraicClosure k) P)
  have hleftComp : FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar ≫ e.inv ≫ q = fH ≫ q := by
    rw [← FiniteTypeCommHopfAlgCat.baseChangeMap_includeLeft_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K, Category.assoc, e.hom_inv_id_assoc]
  have hrightComp : FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar ≫ e.inv ≫ q = fK ≫ q := by
    rw [← FiniteTypeCommHopfAlgCat.baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K, Category.assoc, e.hom_inv_id_assoc]
  have hleftMap : g.comp Algebra.TensorProduct.includeLeft =
      (Algebra.ofId (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)).comp
        (Bialgebra.counitAlgHom (AlgebraicClosure k) Hbar) := by
    have hi : (FiniteTypeCommHopfAlgCat.toBialgHom
        (FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar)).toAlgHom =
        Algebra.TensorProduct.includeLeft := by
      apply AlgHom.ext
      intro h
      exact FiniteTypeCommHopfAlgCat.includeLeft_apply Hbar Kbar h
    rw [← hi]
    simpa only [g] using
      restriction_eq_counit (FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar)
        (e.inv ≫ q) (fH ≫ q) hleftComp hleft
  have hrightMap : g.comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)).comp
        (Bialgebra.counitAlgHom (AlgebraicClosure k) Kbar) := by
    have hi : (FiniteTypeCommHopfAlgCat.toBialgHom
        (FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar)).toAlgHom =
        Algebra.TensorProduct.includeRight := by
      apply AlgHom.ext
      intro l
      exact FiniteTypeCommHopfAlgCat.includeRight_apply Hbar Kbar l
    rw [← hi]
    simpa only [g] using
      restriction_eq_counit (FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar)
        (e.inv ≫ q) (fK ≫ q) hrightComp hright
  have hg : g = ε := by
    rw [← AffineGroup.Product.productMap_restrict g, hleftMap, hrightMap]
    apply Algebra.TensorProduct.ext'
    intro h l
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
        (Coalgebra.counit h) *
        algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
          (Coalgebra.counit l) =
      algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
        (Coalgebra.counit (h ⊗ₜ[AlgebraicClosure k] l))
    rw [← map_mul]
    congr 1
    have hcounit := DFunLike.congr_fun
      (Bialgebra.TensorProduct.counitAlgHom_def (AlgebraicClosure k)
        (AlgebraicClosure k) Hbar Kbar) (h ⊗ₜ[AlgebraicClosure k] l)
    simpa only [Bialgebra.counitAlgHom_apply, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.rid_tmul,
      smul_eq_mul, mul_comm] using hcounit.symm
  have hq' (x : P) :
      FiniteTypeCommHopfAlgCat.toBialgHom (e.inv ≫ q) x =
        algebraMap (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P₀ I)
          (Coalgebra.counit x) := by
    exact DFunLike.congr_fun hg x
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
