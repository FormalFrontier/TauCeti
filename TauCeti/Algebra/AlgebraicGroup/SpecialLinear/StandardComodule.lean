/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# The standard representation of the special linear group

The standard representation of `SL_n` is obtained by restricting the standard representation of
`GL_n` along the determinant-one closed immersion. In coordinate algebras, this is corestriction
of the standard `O(GL_n)`-comodule along the quotient map

```text
O(GL_n) ⟶ O(SL_n).
```

This representation is faithful in every rank. Over a field it is simple in every positive rank.
For `n ≥ 2`, the special linear group acts transitively on nonzero column vectors, so a nonzero
invariant subspace contains every nonzero vector; rank one follows from one-dimensional submodule
theory.

## Main declarations

* `TauCeti.SpecialLinear.standardComodule`: the standard `O(SL_n)`-comodule on `R^n`.
* `TauCeti.SpecialLinear.isFaithful_standardComodule`: the standard representation is faithful.
* `TauCeti.SpecialLinear.mulVec_mem`: a standard subcomodule is stable under every determinant-one
  matrix.
* `TauCeti.SpecialLinear.instIsSimpleOrderSubcomodule`: over a field, the standard comodule is
  simple in every positive rank.

## References

* J. S. Milne, *Algebraic Groups* (2017), §4.a.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The construction and the invariant-subspace argument extend
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule`; the determinant-correction step
is new here.

Faithfulness and simplicity are the representation-theoretic inputs for proving that `SL_n` is
reductive, one of the worked examples accompanying Layer 6 of the ReductiveGroups roadmap.
-/

public section

open Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.SpecialLinear

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The standard right comodule of the special linear coordinate Hopf algebra, obtained by
corestricting the standard `GL_n`-comodule along the determinant-one quotient map. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R n) (Fin n → R) :=
  let _ := GeneralLinear.standardComodule R n
  Comodule.Corestrict (coordinateMap R n).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard `SL_n` coaction is the standard `GL_n` coaction followed by the quotient map on
the coordinate factor. -/
@[simp]
theorem standardComodule_coact :
    let _ := GeneralLinear.standardComodule R n
    Comodule.corestrictCoact
        (R := R) (C := GeneralLinear.coordinateHopfAlgebra R n)
        (D := coordinateHopfAlgebra R n) (M := Fin n → R)
        (Bialgebra.Quotient.mkBialgHom (R := R)
          (definingHopfIdeal R n).toIdeal).toCoalgHom =
      TensorProduct.map LinearMap.id
          (Bialgebra.Quotient.mkBialgHom (R := R)
            (definingHopfIdeal R n).toIdeal).toLinearMap ∘ₗ
        GeneralLinear.standardCoact R n := by
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, LinearMap.comp_apply,
    GeneralLinear.standardComodule_coact]

/-- The coaction bundled by `standardComodule` is its defining corestriction. This explicit bridge
keeps proofs from depending directly on reducibility of the comodule wrapper. -/
private theorem standardComodule_coact_eq_corestrictCoact :
    (standardComodule R n).coact =
      Comodule.corestrictCoact (coordinateMap R n).hom.toCoalgHom :=
  rfl

/-- **The standard comodule of `SL_n` is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R n) (V := Fin n → R) := by
  exact Comodule.isFaithful_corestrict_of_surjective (coordinateMap R n).hom
    (CommHopfAlgCat.mkQuotient_surjective
      (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n))
    (GeneralLinear.isFaithful_standardComodule R n)

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under the canonical scalar-extension identification `A ⊗[R] R^n ≃ A^n`, a point of
`SL_n` acts on the standard comodule by multiplication with its determinant-one matrix. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin n)).toLinearMap.comp
        (Comodule.endOfPoint (Fin n → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
          (Matrix.SpecialLinearGroup.toGL
            ((pointsMulEquiv (R := R) (A := A) n) g)) :
          (Fin n → A) →ₗ[A] Fin n → A).comp
        (TensorProduct.piScalarRight R A A (Fin n)).toLinearMap := by
  rw [Comodule.endOfPoint_corestrict]
  have hpoint :
      g.ofConv.comp ((coordinateMap R n).hom :
        GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n) =
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
          (CommAlgCat.of R A) g).ofConv := by
    rw [CommHopfAlgCat.quotientPointsHom_apply]
  rw [hpoint]
  let q := CommHopfAlgCat.quotientPointsHom
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
    (CommAlgCat.of R A) g
  have hmatrix : GeneralLinear.pointToGeneralLinear n q =
      Matrix.SpecialLinearGroup.toGL ((pointsMulEquiv (R := R) (A := A) n) g) := by
    rw [← GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_toGL]
  rw [← hmatrix]
  exact GeneralLinear.piScalarRight_comp_endOfPoint R n q

end PointAction

private theorem piScalarRight_comm_eq_rid
    (t : (Fin n → R) ⊗[R] R) :
    TensorProduct.piScalarRightHom R R R (Fin n) (TensorProduct.comm R (Fin n → R) R t) =
      TensorProduct.rid R (Fin n → R) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v r =>
      ext i
      simp [TensorProduct.piScalarRightHom_tmul, mul_comm]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- **A subcomodule of the standard comodule of `SL_n` is stable under every determinant-one
matrix.** -/
theorem mulVec_mem (N : Subcomodule R (coordinateHopfAlgebra R n) (Fin n → R))
    (g : Matrix.SpecialLinearGroup (Fin n) R) {w : Fin n → R} (hw : w ∈ N) :
    (g : Matrix (Fin n) (Fin n) R) *ᵥ w ∈ N := by
  let q := (pointsMulEquiv (R := R) (A := R) n).symm g
  have h :
      TensorProduct.rid R (Fin n → R)
          (LinearMap.lTensor (Fin n → R) q.ofConv.toLinearMap
            ((standardComodule R n).coact w)) ∈ N :=
    N.rid_lTensor_coact_mem q.ofConv.toLinearMap hw
  rw [standardComodule_coact_eq_corestrictCoact R n] at h
  rw [CommHopfAlgCat.hom_mkQuotient] at h
  rw [standardComodule_coact R n, LinearMap.comp_apply] at h
  have hcoordinate :
      (Bialgebra.Quotient.mkBialgHom
          (R := R) (definingHopfIdeal R n).toIdeal).toCoalgHom.toLinearMap =
        (Bialgebra.Quotient.mkBialgHom
          (R := R) (definingHopfIdeal R n).toIdeal).toAlgHom.toLinearMap :=
    (_root_.BialgHom.toAlgHom_toLinearMap
      (Bialgebra.Quotient.mkBialgHom (R := R) (definingHopfIdeal R n).toIdeal)).symm
  rw [hcoordinate] at h
  have h' :
      TensorProduct.piScalarRight R R R (Fin n)
          (Comodule.endOfPoint (Fin n → R) q.ofConv (1 ⊗ₜ[R] w)) ∈ N := by
    simpa [Comodule.endOfPoint_tmul, TensorProduct.piScalarRight_apply,
      piScalarRight_comm_eq_rid, LinearMap.lTensor_def, TensorProduct.map_map] using h
  have haction := DFunLike.congr_fun (piScalarRight_comp_endOfPoint R n q) (1 ⊗ₜ[R] w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply] at haction
  rw [haction] at h'
  rw [MulEquiv.apply_symm_apply] at h'
  simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, smul_eq_mul,
    mul_one] using h'

section Simple

variable (k : Type u) [Field k] (m : ℕ) [NeZero m]

omit [NeZero m] in
/-- For `m ≥ 2`, every nonzero vector of `k^m` is the image of every other one under a
determinant-one matrix. -/
private theorem exists_specialLinearGroup_mulVec {v w : Fin m → k} (hm : 2 ≤ m)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin m) k,
      (g : Matrix (Fin m) (Fin m) k) *ᵥ w = v := by
  -- First extend the equivalence between the two lines to an arbitrary ambient equivalence.
  let e : (k ∙ w) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k (Fin m → k) w hw).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton k (Fin m → k) v hv)
  obtain ⟨φ, hφ⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hφw : φ w = v := by
    have hone := hφ ⟨w, Submodule.mem_span_singleton_self w⟩
    have he : e ⟨w, Submodule.mem_span_singleton_self w⟩ =
        ⟨v, Submodule.mem_span_singleton_self v⟩ := by
      simp only [e, LinearEquiv.trans_apply]
      rw [LinearEquiv.coord_self k (Fin m → k) w hw]
      exact LinearEquiv.toSpanNonzeroSingleton_one k (Fin m → k) v hv
    rw [he] at hone
    exact hone.symm
  -- A second direction modulo `k · v` gives a rank-one correction that fixes `v` and has
  -- determinant inverse to that of `φ`.
  have hspan : k ∙ v ≠ ⊤ := by
    intro htop
    have hfin := congrArg
      (fun S : Submodule k (Fin m → k) ↦ Module.finrank k S) htop
    rw [finrank_span_singleton hv, finrank_top, Module.finrank_pi k] at hfin
    simp only [Fintype.card_fin] at hfin
    omega
  obtain ⟨z, hz⟩ := SetLike.exists_not_mem_of_ne_top (k ∙ v) hspan rfl
  obtain ⟨f, hfz, hfspan⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  have hfv : f v = 0 := by
    have hvmap : f v ∈ (k ∙ v).map f :=
      ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
    rw [hfspan, Submodule.mem_bot] at hvmap
    exact hvmap
  let f' : Module.Dual k (Fin m → k) := (f z)⁻¹ • f
  have hf'z : f' z = 1 := by
    simp [f', hfz]
  have hf'v : f' v = 0 := by
    simp [f', hfv]
  let d := LinearEquiv.det φ
  let z' : Fin m → k := ((↑d⁻¹ : k) - 1) • z
  have hf'z' : f' z' = (↑d⁻¹ : k) - 1 := by
    simp [z', hf'z]
  have hunit : IsUnit (1 + f' z') := by
    rw [hf'z']
    have heq : 1 + ((↑d⁻¹ : k) - 1) = (↑d⁻¹ : k) := by ring
    rw [heq]
    exact Units.isUnit _
  let ψ : (Fin m → k) ≃ₗ[k] (Fin m → k) := LinearEquiv.dilatransvection hunit
  have hψv : ψ v = v := by
    rw [LinearEquiv.dilatransvection.apply]
    simp [hf'v]
  have hψdet : LinearEquiv.det ψ = d⁻¹ := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    rw [LinearEquiv.dilatransvection.coe_toLinearMap, LinearMap.transvection.det, hf'z']
    simp
  let θ := ψ * φ
  have hθdet : LinearEquiv.det θ = 1 := by
    simp [θ, hψdet, d]
  have hθw : θ w = v := by
    simp [θ, hφw, hψv]
  -- Read the corrected equivalence as a determinant-one matrix.
  refine ⟨⟨LinearMap.toMatrix' (θ : (Fin m → k) →ₗ[k] Fin m → k), ?_⟩, ?_⟩
  · rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det, hθdet]
    rfl
  · rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    exact hθw

/-- **The standard comodule of `SL_m` over a field is simple** for `m ≠ 0`: its only
subcomodules are the zero comodule and the whole column space. -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k m) (Fin m → k)) := by
  by_cases hm : m = 1
  · have hfin : Module.finrank k (Fin m → k) = 1 := by
      rw [Module.finrank_pi k, Fintype.card_fin, hm]
    let hsimple : IsSimpleOrder (Submodule k (Fin m → k)) :=
      is_simple_module_of_finrank_eq_one hfin
    refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
    · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
      have hone : (Pi.single (0 : Fin m) (1 : k) : Fin m → k) ∈
          (⊥ : Subcomodule k (coordinateHopfAlgebra k m) (Fin m → k)) :=
        h ▸ Subcomodule.mem_top _
      rw [Subcomodule.mem_bot] at hone
      simpa using congrFun hone (0 : Fin m)
    · intro N
      rcases hsimple.eq_bot_or_eq_top N.toSubmodule with hN | hN
      · left
        exact Subcomodule.ext fun x ↦ by
          have hx : x ∈ N.toSubmodule ↔ x ∈ (⊥ : Submodule k (Fin m → k)) :=
            SetLike.ext_iff.mp hN x
          exact hx
      · right
        exact Subcomodule.ext fun x ↦ by
          have hx : x ∈ N.toSubmodule ↔ x ∈ (⊤ : Submodule k (Fin m → k)) :=
            SetLike.ext_iff.mp hN x
          exact hx
  · have hm2 : 2 ≤ m := by
      have hm0 : m ≠ 0 := NeZero.ne m
      omega
    refine Subcomodule.isSimpleOrder_of_transitive
      (Pi.single (0 : Fin m) (1 : k) : Fin m → k) ?_
      (fun (g : Matrix.SpecialLinearGroup (Fin m) k) w ↦
        (g : Matrix (Fin m) (Fin m) k) *ᵥ w) ?_ ?_
    · intro h
      simpa using congrFun h (0 : Fin m)
    · exact fun hv hw ↦ exists_specialLinearGroup_mulVec k m hm2 hv hw
    · exact fun N g _ hw ↦ mulVec_mem k m N g hw

end Simple

end TauCeti.SpecialLinear
