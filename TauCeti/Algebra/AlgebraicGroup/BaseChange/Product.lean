/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Base change of products of affine groups

Scalar extension commutes with tensor products of commutative Hopf algebras. Contravariantly,
this identifies the base change of a direct product of affine groups with the direct product of
their base changes. The comparison is also compatible with the two coordinate inclusions, which
represent the projections from a product to its factors.

## Main declarations

* `TauCeti.CommHopfAlgCat.baseChangeTensorProductBialgEquiv`: the bialgebra equivalence between
  the base change of a tensor product and the tensor product of the base changes.
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso`: the equivalence bundled in the
  finite-type commutative Hopf-algebra category.

The underlying algebra equivalence is
`TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`, which upgrades Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`. This is the product/base-change
identification needed to prove that direct products of reductive affine groups are reductive in
Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
variable (H L : _root_.CommHopfAlgCat.{v} k)

private theorem baseChangeTensorAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K
        ((K ⊗[k] H) ⊗[K] (K ⊗[k] L))).comp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom =
    Bialgebra.counitAlgHom K (K ⊗[k] (H ⊗[k] L)) := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul h l => simp [smul_smul, mul_comm]

private theorem baseChangeTensorAlgEquiv_comul_aux
    (s : K) (x : H ⊗[k] H) (y : L ⊗[k] L) :
    (Algebra.TensorProduct.map
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
        k K k K K K (H ⊗[k] L) (H ⊗[k] L)
        (1 ⊗ₜ[K] s ⊗ₜ[k]
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
            k k k k H H L L (x ⊗ₜ[k] y))) =
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      K K K K (K ⊗[k] H) (K ⊗[k] H) (K ⊗[k] L) (K ⊗[k] L)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          k K k K K K H H (1 ⊗ₜ[K] s ⊗ₜ[k] x) ⊗ₜ[K]
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          k K k K K K L L (1 ⊗ₜ[K] 1 ⊗ₜ[k] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simpa only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) hx₁ hx₂
  | tmul h₁ h₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
        simpa only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add] using
          congrArg₂ (· + ·) hy₁ hy₂
    | tmul l₁ l₂ =>
        simp

private theorem baseChangeTensorAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom).comp
      (Bialgebra.comulAlgHom K (K ⊗[k] (H ⊗[k] L))) =
    (Bialgebra.comulAlgHom K ((K ⊗[k] H) ⊗[K] (K ⊗[k] L))).comp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul h l =>
      simp only [AlgHom.coe_comp, Function.comp_apply]
      have he :
          (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
              (s ⊗ₜ[k] (h ⊗ₜ[k] l)) =
            (s ⊗ₜ[k] h) ⊗ₜ[K] (1 ⊗ₜ[k] l) :=
        Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul k K H L s h l
      rw [he]
      simpa only [Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul,
        CommSemiring.comul_apply] using
        baseChangeTensorAlgEquiv_comul_aux k K H L s
          (Coalgebra.comul (R := k) h) (Coalgebra.comul (R := k) l)

/-- **Base change commutes with tensor products of commutative Hopf algebras.**

The underlying algebra equivalence distributes scalar extension across a tensor product. This
bundling records that it also preserves the counit and comultiplication, so contravariantly it is
the canonical identification `(G × H)_K ≅ G_K × H_K` of affine groups. -/
noncomputable def baseChangeTensorProductBialgEquiv :
    baseChange (K := K) (_root_.CommHopfAlgCat.of k (H ⊗[k] L)) ≃ₐc[K]
      ((K ⊗[k] H) ⊗[K] (K ⊗[k] L)) :=
  BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L)
    (baseChangeTensorAlgEquiv_counit_comp k K H L)
    (baseChangeTensorAlgEquiv_map_comp_comul k K H L)

/-- On a pure tensor, the product/base-change equivalence puts the scalar in the first
base-changed factor. -/
@[simp]
theorem baseChangeTensorProductBialgEquiv_tmul (s : K) (h : H) (l : L) :
    baseChangeTensorProductBialgEquiv k K H L (s ⊗ₜ[k] (h ⊗ₜ[k] l)) =
      (s ⊗ₜ[k] h) ⊗ₜ[K] (1 ⊗ₜ[k] l) :=
  Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul k K H L s h l

/-- The inverse product/base-change equivalence multiplies the two scalar coefficients. -/
@[simp]
theorem baseChangeTensorProductBialgEquiv_symm_tmul
    (s t : K) (h : H) (l : L) :
    (baseChangeTensorProductBialgEquiv k K H L).symm
        ((s ⊗ₜ[k] h) ⊗ₜ[K] (t ⊗ₜ[k] l)) =
      (s * t) ⊗ₜ[k] (h ⊗ₜ[k] l) :=
  Algebra.TensorProduct.baseChangeTensorAlgEquiv_symm_tmul k K H L s t h l

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
variable (H L : FiniteTypeCommHopfAlgCat.{u, v} k)

/-- **Base change commutes with finite-type affine-group products.**

This is `CommHopfAlgCat.baseChangeTensorProductBialgEquiv` bundled as an isomorphism in the
finite-type commutative Hopf-algebra category. -/
noncomputable abbrev baseChangeTensorProductIso :
    baseChange (K := K) (tensorProduct H L) ≅
      tensorProduct (baseChange (K := K) H) (baseChange (K := K) L) :=
  ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    CommHopfAlgCat.baseChangeTensorProductBialgEquiv k K H.obj L.obj

/-- The underlying bialgebra equivalence of the finite-type product/base-change isomorphism is
the canonical tensor-product comparison. -/
@[simp]
theorem toBialgHom_baseChangeTensorProductIso_hom :
    toBialgHom (baseChangeTensorProductIso k K H L).hom =
      CommHopfAlgCat.baseChangeTensorProductBialgEquiv k K H.obj L.obj :=
  rfl

/-- The product/base-change isomorphism carries the base change of the left coordinate inclusion
to the left coordinate inclusion between the base-changed factors. -/
theorem baseChangeMap_includeLeft_comp_baseChangeTensorProductIso_hom :
    baseChangeMap (K := K) (includeLeft H L) ≫
        (baseChangeTensorProductIso k K H L).hom =
      includeLeft (baseChange (K := K) H) (baseChange (K := K) L) := by
  apply hom_ext
  apply _root_.BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro s h
  simp only [ObjectProperty.isoMk_hom, _root_.CommHopfAlgCat.isoMk_hom,
    toBialgHom_comp, toBialgHom_ofHom, ObjectProperty.homMk_hom,
    ConcreteCategory.hom_ofHom, BialgHom.comp_toAlgHom,
    _root_.Bialgebra.TensorProduct.map_toAlgHom, BialgHom.id_toAlgHom,
    Bialgebra.TensorProduct.includeLeft_toAlgHom, AlgHom.coe_comp,
    BialgHom.coe_toAlgHom, BialgHom.coe_coe, Function.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    Algebra.TensorProduct.includeLeft_apply]
  exact (CommHopfAlgCat.baseChangeTensorProductBialgEquiv_tmul
    k K H.obj L.obj s h 1).trans <| by
      exact (congrArg (fun z : K ⊗[k] L ↦ (s ⊗ₜ[k] h) ⊗ₜ[K] z)
        (Algebra.TensorProduct.one_def (R := k) (A := K) (B := L))).symm |>.trans
          (includeLeft_apply (baseChange (K := K) H) (baseChange (K := K) L)
            (s ⊗ₜ[k] h)).symm

/-- The product/base-change isomorphism carries the base change of the right coordinate inclusion
to the right coordinate inclusion between the base-changed factors. -/
theorem baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom :
    baseChangeMap (K := K) (includeRight H L) ≫
        (baseChangeTensorProductIso k K H L).hom =
      includeRight (baseChange (K := K) H) (baseChange (K := K) L) := by
  apply hom_ext
  apply _root_.BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro s l
  simp only [ObjectProperty.isoMk_hom, _root_.CommHopfAlgCat.isoMk_hom,
    toBialgHom_comp, toBialgHom_ofHom, ObjectProperty.homMk_hom,
    ConcreteCategory.hom_ofHom, BialgHom.comp_toAlgHom,
    _root_.Bialgebra.TensorProduct.map_toAlgHom, BialgHom.id_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom, AlgHom.coe_comp,
    BialgHom.coe_toAlgHom, BialgHom.coe_coe, Function.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    Algebra.TensorProduct.includeRight_apply]
  exact (CommHopfAlgCat.baseChangeTensorProductBialgEquiv_tmul
    k K H.obj L.obj s 1 l).trans <| by
      rw [includeRight_apply, Algebra.TensorProduct.one_def]
      have hsH : s ⊗ₜ[k] (1 : H) = s • ((1 : K) ⊗ₜ[k] (1 : H)) :=
        TensorProduct.tmul_eq_smul_one_tmul s (1 : H)
      have hsL : s ⊗ₜ[k] l = s • ((1 : K) ⊗ₜ[k] l) :=
        TensorProduct.tmul_eq_smul_one_tmul s l
      rw [hsH, hsL]
      exact TensorProduct.smul_tmul s ((1 : K) ⊗ₜ[k] (1 : H)) ((1 : K) ⊗ₜ[k] l)

end FiniteTypeCommHopfAlgCat

end TauCeti
