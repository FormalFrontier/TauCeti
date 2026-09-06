/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup

/-!
# The standard representation of the symplectic group

The standard representation of the symplectic group scheme `Sp₂ₘ` is obtained by corestricting
the standard `O(GL₂ₘ)`-comodule along the quotient coordinate morphism

```text
O(GL₂ₘ) ⟶ O(Sp₂ₘ).
```

The representation is faithful in every rank. Over a field it is simple whenever `m` is
positive. The simplicity proof uses the explicit symplectic root elements: a long-root
transvection extracts a coordinate basis vector from any nonzero vector in an invariant
subspace, the opposite long root supplies its symplectic partner, and difference-root elements
move that pair through all coordinates.

## Main declarations

* `TauCeti.Symplectic.standardComodule`: the standard `O(Sp₂ₘ)`-comodule on `R^(2m)`.
* `TauCeti.Symplectic.isFaithful_standardComodule`: the standard comodule is faithful.
* `TauCeti.Symplectic.mulVec_mem`: a standard subcomodule is stable under every symplectic
  matrix.
* `TauCeti.Symplectic.instIsSimpleOrderSubcomodule`: over a field and in positive rank, the
  standard comodule is simple.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3 and 24.6.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

This supplies the faithful simple representation used to prove the `Sp₂ₘ` worked example
reductive in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The standard right comodule of the symplectic coordinate Hopf algebra, obtained by
corestricting the standard `GL₂ₘ`-comodule along the symplectic quotient map. -/
@[expose, instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R m) (Fin (m + m) → R) :=
  let _ := GeneralLinear.standardComodule R (m + m)
  Comodule.Corestrict (coordinateMap R m).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard symplectic coaction is the standard general-linear coaction followed by the
quotient map on the coordinate factor. -/
@[simp]
theorem standardComodule_coact :
    let _ := GeneralLinear.standardComodule R (m + m)
    Comodule.corestrictCoact
        (R := R) (C := GeneralLinear.coordinateHopfAlgebra R (m + m))
        (D := coordinateHopfAlgebra R m) (M := Fin (m + m) → R)
        (Bialgebra.Quotient.mkBialgHom (R := R)
          (definingHopfIdeal R m).toIdeal).toCoalgHom =
      TensorProduct.map LinearMap.id
          (Bialgebra.Quotient.mkBialgHom (R := R)
            (definingHopfIdeal R m).toIdeal).toLinearMap ∘ₗ
        GeneralLinear.standardCoact R (m + m) := by
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, LinearMap.comp_apply,
    GeneralLinear.standardComodule_coact]

/-- The coaction bundled by `standardComodule` is its defining corestriction. -/
@[simp]
theorem standardComodule_coact_eq_corestrictCoact :
    (standardComodule R m).coact =
      Comodule.corestrictCoact (coordinateMap R m).hom.toCoalgHom :=
  rfl

/-- **The standard comodule of `Sp₂ₘ` is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R m)
      (V := Fin (m + m) → R) := by
  unfold standardComodule
  exact Comodule.isFaithful_corestrict_of_surjective (coordinateMap R m).hom
    (by rw [coordinateMap_def]; exact CommHopfAlgCat.mkQuotient_surjective _ _)
    (GeneralLinear.isFaithful_standardComodule R (m + m))

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under the canonical scalar-extension identification `A ⊗[R] R^(2m) ≃ A^(2m)`, a point
of `Sp₂ₘ` acts on the standard comodule by multiplication with its symplectic matrix. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin (m + m))).toLinearMap.comp
        (Comodule.endOfPoint (Fin (m + m) → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
          ((pointsMulEquiv (R := R) (A := A) m) g : GL (Fin (m + m)) A) :
          (Fin (m + m) → A) →ₗ[A] Fin (m + m) → A).comp
        (TensorProduct.piScalarRight R A A (Fin (m + m))).toLinearMap := by
  rw [Comodule.endOfPoint_corestrict]
  have hpoint :
      g.ofConv.comp ((coordinateMap R m).hom :
        GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R] coordinateHopfAlgebra R m) =
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
          (CommAlgCat.of R A) g).ofConv := by
    rw [coordinateMap_def]
    rw [CommHopfAlgCat.quotientPointsHom_apply]
  rw [hpoint]
  let q := CommHopfAlgCat.quotientPointsHom
    (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
    (CommAlgCat.of R A) g
  have hmatrix : GeneralLinear.pointToGeneralLinear (m + m) q =
      ((pointsMulEquiv (R := R) (A := A) m) g : GLSymplecticFin m A) := by
    rw [← GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_coe]
  rw [← hmatrix]
  exact GeneralLinear.piScalarRight_comp_endOfPoint R (m + m) q

end PointAction

private theorem piScalarRight_comm_eq_rid
    (t : (Fin (m + m) → R) ⊗[R] R) :
    TensorProduct.piScalarRightHom R R R (Fin (m + m))
        (TensorProduct.comm R (Fin (m + m) → R) R t) =
      TensorProduct.rid R (Fin (m + m) → R) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v r =>
      ext i
      simp [TensorProduct.piScalarRightHom_tmul, mul_comm]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- **A subcomodule of the standard symplectic comodule is stable under every symplectic
matrix.** -/
theorem mulVec_mem (N : Subcomodule R (coordinateHopfAlgebra R m) (Fin (m + m) → R))
    (g : GLSymplecticFin m R) {w : Fin (m + m) → R} (hw : w ∈ N) :
    (g.1 : Matrix (Fin (m + m)) (Fin (m + m)) R) *ᵥ w ∈ N := by
  let q := (pointsMulEquiv (R := R) (A := R) m).symm g
  have h :
      TensorProduct.rid R (Fin (m + m) → R)
          (LinearMap.lTensor (Fin (m + m) → R) q.ofConv.toLinearMap
            ((standardComodule R m).coact w)) ∈ N :=
    N.rid_lTensor_coact_mem q.ofConv.toLinearMap hw
  rw [standardComodule_coact_eq_corestrictCoact R m] at h
  rw [coordinateMap_def] at h
  rw [CommHopfAlgCat.hom_mkQuotient] at h
  rw [standardComodule_coact R m, LinearMap.comp_apply] at h
  have hcoordinate :
      (Bialgebra.Quotient.mkBialgHom
          (R := R) (definingHopfIdeal R m).toIdeal).toCoalgHom.toLinearMap =
        (Bialgebra.Quotient.mkBialgHom
          (R := R) (definingHopfIdeal R m).toIdeal).toAlgHom.toLinearMap :=
    (_root_.BialgHom.toAlgHom_toLinearMap
      (Bialgebra.Quotient.mkBialgHom (R := R) (definingHopfIdeal R m).toIdeal)).symm
  rw [hcoordinate] at h
  have h' :
      TensorProduct.piScalarRight R R R (Fin (m + m))
          (Comodule.endOfPoint (Fin (m + m) → R) q.ofConv (1 ⊗ₜ[R] w)) ∈ N := by
    simpa [coordinateMap_def, Comodule.endOfPoint_tmul, TensorProduct.piScalarRight_apply,
      piScalarRight_comm_eq_rid, LinearMap.lTensor_def, TensorProduct.map_map] using h
  have haction := DFunLike.congr_fun (piScalarRight_comp_endOfPoint R m q) (1 ⊗ₜ[R] w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply] at haction
  rw [haction] at h'
  rw [MulEquiv.apply_symm_apply] at h'
  simpa only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    smul_eq_mul, mul_one] using h'

section Simple

variable (k : Type u) [Field k] (m : ℕ)

/-- Acting by an elementary transvection and subtracting the original vector isolates one
coordinate multiple of a standard basis vector. -/
private theorem transvectionUnit_mulVec_sub (i j : Fin (m + m)) (hij : i ≠ j) (c : k)
    (w : Fin (m + m) → k) :
    ((transvectionUnit hij c : GL (Fin (m + m)) k) :
        Matrix (Fin (m + m)) (Fin (m + m)) k) *ᵥ w - w =
      Pi.single i (c * w j) := by
  ext a
  simp [coe_transvectionUnit, Matrix.transvection, Matrix.add_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply]

/-- A transvection extracts a standard basis vector from a nonzero coordinate of an invariant
subspace element. -/
private theorem single_one_mem_of_transvection
    (N : Subcomodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k))
    {w : Fin (m + m) → k} (hw : w ∈ N) (i j : Fin (m + m)) (hij : i ≠ j)
    (g : GLSymplecticFin m k)
    (hg : (g : GL (Fin (m + m)) k) = transvectionUnit hij 1) (hj : w j ≠ 0) :
    Pi.single i 1 ∈ N := by
  have hgw := mulVec_mem k m N g hw
  have hsub :
      ((transvectionUnit hij 1 : GL (Fin (m + m)) k) :
          Matrix (Fin (m + m)) (Fin (m + m)) k) *ᵥ w - w ∈ N := by
    rw [← hg]
    exact N.toSubmodule.sub_mem hgw hw
  rw [transvectionUnit_mulVec_sub k m i j hij 1 w, one_mul] at hsub
  have hscaled := N.toSubmodule.smul_mem (w j)⁻¹ hsub
  have heq : (w j)⁻¹ • Pi.single i (w j) = Pi.single i 1 := by
    ext x
    simp [Pi.single_apply, hj]
  rwa [heq] at hscaled

/-- A long-root element moves a standard basis vector to its symplectic partner. -/
private theorem single_swap_mem_of_longRoot
    (N : Subcomodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k)) (i : Fin m)
    (upper : Bool)
    (hmem : Pi.single (finSumFinEquiv (if upper then Sum.inl i else Sum.inr i)) 1 ∈ N) :
    Pi.single (finSumFinEquiv (if upper then Sum.inr i else Sum.inl i)) 1 ∈ N := by
  cases upper with
  | false =>
      let g := GLSymplecticFin.positiveLongRootTransvectionUnit (R := k) i 1
      have hgw := mulVec_mem k m N g hmem
      have hsub := N.toSubmodule.sub_mem hgw hmem
      rw [GLSymplecticFin.coe_positiveLongRootTransvectionUnit] at hsub
      rw [transvectionUnit_mulVec_sub k m _ _
        (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i) 1 _] at hsub
      simpa [Pi.single_apply] using hsub
  | true =>
      let g := GLSymplecticFin.negativeLongRootTransvectionUnit (R := k) i 1
      have hgw := mulVec_mem k m N g hmem
      have hsub := N.toSubmodule.sub_mem hgw hmem
      rw [GLSymplecticFin.coe_negativeLongRootTransvectionUnit] at hsub
      rw [transvectionUnit_mulVec_sub k m _ _
        (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i) 1 _] at hsub
      simpa [Pi.single_apply] using hsub

/-- A difference-root element moves an upper standard basis vector between indices. -/
private theorem differenceShortRootUnit_mulVec_single_sub (i j : Fin m) (hji : j ≠ i) :
    let g := GLSymplecticFin.differenceShortRootUnit (R := k) hji 1
    (g.1 : Matrix (Fin (m + m)) (Fin (m + m)) k) *ᵥ
          Pi.single (finSumFinEquiv (Sum.inl i)) 1 -
        Pi.single (finSumFinEquiv (Sum.inl i)) 1 =
      Pi.single (finSumFinEquiv (Sum.inl j)) 1 := by
  dsimp only
  have addNat_eq_natAdd (r : Fin m) : r.addNat m = Fin.natAdd m r := by
    apply Fin.ext
    simp
  have hcoli : i.addNat m ≠ Fin.castAdd m i := by
    intro h
    apply GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i
    rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left]
    rw [← addNat_eq_natAdd]
    exact h
  have hcolj : j.addNat m ≠ Fin.castAdd m i := by
    intro h
    apply GLSymplecticFin.finSumFinEquiv_inr_ne_inl j i
    rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left]
    rw [← addNat_eq_natAdd]
    exact h
  rw [GLSymplecticFin.coe_differenceShortRootUnit, Units.val_mul]
  rw [← Matrix.mulVec_mulVec]
  ext x
  simp [coe_transvectionUnit, Matrix.transvection, Matrix.add_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply, Matrix.one_apply, hcoli, hcolj]

/-- Short-root elements move an upper standard basis vector to every upper index. -/
private theorem single_inl_mem_of_shortRoot
    (N : Subcomodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k)) (i : Fin m)
    (hmem : Pi.single (finSumFinEquiv (Sum.inl i)) 1 ∈ N) (j : Fin m) :
    Pi.single (finSumFinEquiv (Sum.inl j)) 1 ∈ N := by
  by_cases hji : j = i
  · subst j
    exact hmem
  · let g := GLSymplecticFin.differenceShortRootUnit (R := k) hji 1
    have hgw := mulVec_mem k m N g hmem
    have hsub := N.toSubmodule.sub_mem hgw hmem
    rw [differenceShortRootUnit_mulVec_single_sub k m i j hji] at hsub
    exact hsub

/-- Every standard basis vector belongs to a nonzero invariant subspace of the standard
symplectic representation. -/
private theorem single_one_mem_of_ne_bot
    (N : Subcomodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k)) (hN : N ≠ ⊥)
    (a : Fin (m + m)) : Pi.single a 1 ∈ N := by
  obtain ⟨w, hw, hw0⟩ := N.ne_bot_iff.mp hN
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hw0
  let b' := finSumFinEquiv.symm b
  have hb_eq : finSumFinEquiv b' = b := Equiv.apply_symm_apply finSumFinEquiv b
  have hseed : Pi.single (finSumFinEquiv b'.swap) 1 ∈ N := by
    rcases b' with i | i
    · apply single_one_mem_of_transvection k m N hw
        (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl i))
        (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i)
        (GLSymplecticFin.negativeLongRootTransvectionUnit i 1)
        (GLSymplecticFin.coe_negativeLongRootTransvectionUnit i 1)
      have : w (finSumFinEquiv (Sum.inl i)) ≠ 0 := by
        rw [hb_eq]
        simpa only [Pi.zero_apply] using hb
      exact this
    · apply single_one_mem_of_transvection k m N hw
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr i))
        (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i)
        (GLSymplecticFin.positiveLongRootTransvectionUnit i 1)
        (GLSymplecticFin.coe_positiveLongRootTransvectionUnit i 1)
      have : w (finSumFinEquiv (Sum.inr i)) ≠ 0 := by
        rw [hb_eq]
        simpa only [Pi.zero_apply] using hb
      exact this
  obtain ⟨i, hupper⟩ :
      ∃ i : Fin m, Pi.single (finSumFinEquiv (Sum.inl i)) 1 ∈ N := by
    rcases hb' : b' with i | i
    · have hlower : Pi.single (finSumFinEquiv (Sum.inr i)) 1 ∈ N := by
        simpa [hb'] using hseed
      exact ⟨i, by simpa using single_swap_mem_of_longRoot k m N i false hlower⟩
    · exact ⟨i, by simpa [hb'] using hseed⟩
  rcases ha' : finSumFinEquiv.symm a with j | j
  · have ha_eq : finSumFinEquiv (Sum.inl j) = a := by
      rw [← ha']
      exact Equiv.apply_symm_apply finSumFinEquiv a
    rw [← ha_eq]
    exact single_inl_mem_of_shortRoot k m N i hupper j
  · have ha_eq : finSumFinEquiv (Sum.inr j) = a := by
      rw [← ha']
      exact Equiv.apply_symm_apply finSumFinEquiv a
    rw [← ha_eq]
    simpa using single_swap_mem_of_longRoot k m N j true
      (single_inl_mem_of_shortRoot k m N i hupper j)

variable [NeZero m]

/-- **The standard comodule of `Sp₂ₘ` over a field is simple** when `m` is positive. -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k)) := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have hone : (Pi.single (0 : Fin (m + m)) (1 : k) : Fin (m + m) → k) ∈
        (⊥ : Subcomodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k)) :=
      h ▸ Subcomodule.mem_top _
    rw [Subcomodule.mem_bot] at hone
    simpa using congrFun hone (0 : Fin (m + m))
  · intro N
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      apply top_unique
      intro v _
      have hv : v = ∑ a, v a • Pi.single a 1 := by
        ext a
        simp [Pi.single_apply]
      rw [hv]
      exact N.toSubmodule.sum_mem fun a _ ↦
        N.toSubmodule.smul_mem (v a) (single_one_mem_of_ne_bot k m N hN a)

end Simple

end TauCeti.Symplectic
