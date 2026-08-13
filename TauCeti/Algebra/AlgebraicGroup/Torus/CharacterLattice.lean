/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# The character lattice of a torus

For a finite-type commutative Hopf algebra `H` over a field `k`, its geometric characters are
the group-like elements of its coordinate algebra after extension to an algebraic closure:

```text
X*(H) = GroupLike k̄ (k̄ ⊗[k] H).
```

This description is intrinsic and makes the absolute-Galois action visible without choosing a
splitting of `H`. An automorphism `σ` of `k̄/k` acts on the scalar factor,
`σ • (a ⊗ h) = σ(a) ⊗ h`. The resulting semilinear ring action preserves the counit
and comultiplication equations defining group-like elements, hence acts on `X*(H)`.

For a torus, the defining splitting over `k̄` identifies this character group, noncanonically,
with a finite-rank free abelian group. Thus its additive form is the character lattice equipped
with the standard absolute-Galois action used in the classification of non-split tori.

## Main declarations

* `TauCeti.CommHopfAlgCat.galoisScalarMap`: the semilinear absolute-Galois action on a
  base-changed coordinate Hopf algebra.
* `TauCeti.CommHopfAlgCat.galoisScalarMap_isGroupLikeElem`: this action preserves group-like
  elements.
* `TauCeti.CommHopfAlgCat.geometricCharacterGroup`: the geometric character group.
* `TauCeti.CommHopfAlgCat.characterLattice`: its additive form.
* `TauCeti.splitTorusCharacterLatticeEquiv`: the intrinsic character lattice of a split
  presentation is its defining free abelian group.
* `TauCeti.exists_characterLattice_addEquiv_of_torus`: the character lattice of any torus is
  finite-rank free.

## References

See J. S. Milne, *Algebraic Groups* (2017), §§12.14--12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open Coalgebra TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{u} k)

/-- Apply an automorphism of `k̄/k` to the scalar factor of `k̄ ⊗[k] H`. -/
noncomputable def galoisScalarMap (σ : Field.absoluteGaloisGroup k) :
    AlgebraicClosure k ⊗[k] H →ₐ[k] AlgebraicClosure k ⊗[k] H :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k H)

/-- The Galois scalar map acts on pure tensors through the first factor. -/
@[simp]
theorem galoisScalarMap_tmul (σ : Field.absoluteGaloisGroup k)
    (a : AlgebraicClosure k) (h : H) :
    galoisScalarMap H σ (a ⊗ₜ[k] h) = σ.toAlgHom a ⊗ₜ[k] h := by
  simp [galoisScalarMap]

/-- The identity Galois automorphism acts trivially on the scalar extension. -/
@[simp]
theorem galoisScalarMap_one (x : AlgebraicClosure k ⊗[k] H) :
    galoisScalarMap H 1 x = x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a h =>
      rw [galoisScalarMap_tmul]
      rfl

/-- Galois scalar maps compose according to multiplication in the absolute Galois group. -/
theorem galoisScalarMap_mul (σ τ : Field.absoluteGaloisGroup k)
    (x : AlgebraicClosure k ⊗[k] H) :
    galoisScalarMap H (σ * τ) x = galoisScalarMap H σ (galoisScalarMap H τ x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a h =>
      rw [galoisScalarMap_tmul, galoisScalarMap_tmul, galoisScalarMap_tmul]
      rfl

/-- The scalar-factor action is semilinear for the corresponding automorphism of `k̄`. -/
theorem galoisScalarMap_smul (σ : Field.absoluteGaloisGroup k)
    (a : AlgebraicClosure k) (x : AlgebraicClosure k ⊗[k] H) :
    galoisScalarMap H σ (a • x) = σ.toAlgHom a • galoisScalarMap H σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

/-- The Galois action on the scalar extension as a semilinear map over `k̄`. -/
noncomputable def galoisScalarSemilinearMap (σ : Field.absoluteGaloisGroup k) :
    AlgebraicClosure k ⊗[k] H →ₛₗ[σ.toRingHom] AlgebraicClosure k ⊗[k] H where
  toFun := galoisScalarMap H σ
  map_add' := map_add (galoisScalarMap H σ)
  map_smul' := galoisScalarMap_smul H σ

/-- The semilinear Galois map agrees pointwise with `galoisScalarMap`. -/
@[simp]
theorem galoisScalarSemilinearMap_apply (σ : Field.absoluteGaloisGroup k)
    (x : AlgebraicClosure k ⊗[k] H) :
    galoisScalarSemilinearMap H σ x = galoisScalarMap H σ x :=
  (rfl)

/-- The counit is equivariant for the semilinear Galois action. -/
theorem counit_galoisScalarMap (σ : Field.absoluteGaloisGroup k)
    (x : AlgebraicClosure k ⊗[k] H) :
    counit (R := AlgebraicClosure k) (galoisScalarMap H σ x) =
      σ.toAlgHom (counit (R := AlgebraicClosure k) x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a h => simp [galoisScalarMap_tmul]

/-- Comultiplication is equivariant for the semilinear Galois action. -/
theorem comul_galoisScalarMap (σ : Field.absoluteGaloisGroup k)
    (x : AlgebraicClosure k ⊗[k] H) :
    comul (galoisScalarMap H σ x) =
      TensorProduct.map (galoisScalarSemilinearMap H σ)
        (galoisScalarSemilinearMap H σ) (comul x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h =>
      rw [galoisScalarMap_tmul, TensorProduct.comul_tmul, TensorProduct.comul_tmul]
      induction comul (R := k) h with
      | zero => simp only [tmul_zero, map_zero]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul h₁ h₂ =>
          have ha : comul (R := AlgebraicClosure k) a = 1 ⊗ₜ[AlgebraicClosure k] a := rfl
          have hσa : comul (R := AlgebraicClosure k) (σ.toAlgHom a) =
              1 ⊗ₜ[AlgebraicClosure k] σ.toAlgHom a := rfl
          rw [ha, hσa]
          simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
            galoisScalarSemilinearMap_apply, galoisScalarMap_tmul, map_one]

/-- Applying an absolute-Galois automorphism to the scalar factor preserves the group-like
equations. -/
theorem galoisScalarMap_isGroupLikeElem (σ : Field.absoluteGaloisGroup k)
    {x : AlgebraicClosure k ⊗[k] H}
    (hx : IsGroupLikeElem (AlgebraicClosure k) x) :
    IsGroupLikeElem (AlgebraicClosure k) (galoisScalarMap H σ x) where
  counit_eq_one := by
    rw [counit_galoisScalarMap, hx.counit_eq_one, map_one]
  comul_eq_tmul_self := by
    rw [comul_galoisScalarMap, hx.comul_eq_tmul_self, TensorProduct.map_tmul]
    rfl

/-- The absolute Galois group acts on a scalar-extended coordinate ring by semilinear ring
automorphisms. -/
noncomputable instance instGaloisScalarMulSemiringAction :
    MulSemiringAction (Field.absoluteGaloisGroup k)
    (AlgebraicClosure k ⊗[k] H) where
  smul σ x := galoisScalarMap H σ x
  one_smul := galoisScalarMap_one H
  mul_smul := galoisScalarMap_mul H
  smul_zero σ := map_zero (galoisScalarMap H σ)
  smul_add σ := map_add (galoisScalarMap H σ)
  smul_one σ := map_one (galoisScalarMap H σ)
  smul_mul σ := map_mul (galoisScalarMap H σ)

/-- The geometric character group of a commutative Hopf algebra: the group-like elements of
its coordinate algebra after extension to an algebraic closure. For a represented affine group,
these are exactly its morphisms over `k̄` to the multiplicative group. -/
abbrev geometricCharacterGroup :=
  GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H)

/-- The absolute Galois action on a geometric character. -/
@[expose] noncomputable def galoisSmul (σ : Field.absoluteGaloisGroup k)
    (x : geometricCharacterGroup H) : geometricCharacterGroup H :=
  ⟨galoisScalarMap H σ x.val,
    galoisScalarMap_isGroupLikeElem H σ x.isGroupLikeElem_val⟩

/-- The underlying coordinate of the Galois action is the scalar-factor action. -/
@[simp]
theorem galoisSmul_val (σ : Field.absoluteGaloisGroup k)
    (x : geometricCharacterGroup H) :
    (galoisSmul H σ x).val = galoisScalarMap H σ x.val :=
  (rfl)

/-- Absolute Galois acts on the geometric character group by group automorphisms. -/
noncomputable instance instGeometricCharacterGroupGaloisAction :
    MulDistribMulAction (Field.absoluteGaloisGroup k)
    (geometricCharacterGroup H) where
  smul := galoisSmul H
  one_smul x := GroupLike.val_injective (galoisScalarMap_one H x.val)
  mul_smul σ τ x := GroupLike.val_injective (galoisScalarMap_mul H σ τ x.val)
  smul_one σ := GroupLike.val_injective (map_one (galoisScalarMap H σ))
  smul_mul σ x y := GroupLike.val_injective (map_mul (galoisScalarMap H σ) x.val y.val)

/-- Galois scalar multiplication on a geometric character is `galoisSmul`. -/
@[simp]
theorem smul_def (σ : Field.absoluteGaloisGroup k) (x : geometricCharacterGroup H) :
    σ • x = galoisSmul H σ x :=
  (rfl)

/-- The character lattice of a commutative Hopf algebra, written additively. It carries the
absolute-Galois action transported from `geometricCharacterGroup`. -/
abbrev characterLattice := Additive (geometricCharacterGroup H)

/-- The absolute Galois action on the additive character lattice. -/
noncomputable instance instCharacterLatticeGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup k) (characterLattice H) where
  smul σ x := Additive.ofMul (σ • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul _ x.toMul)
  mul_smul σ τ x := congrArg Additive.ofMul (mul_smul σ τ x.toMul)
  smul_zero σ := congrArg Additive.ofMul (smul_one σ)
  smul_add σ x y := congrArg Additive.ofMul (smul_mul' σ x.toMul y.toMul)

/-- On the additive character lattice, the Galois action is transported from its action on
group-like elements. -/
@[simp]
theorem smul_ofMul (σ : Field.absoluteGaloisGroup k) (x : geometricCharacterGroup H) :
    σ • Additive.ofMul x = Additive.ofMul (σ • x) :=
  (rfl)

/-- The geometric character group of a torus is finitely generated. -/
theorem geometricCharacterGroup_fg_of_torus
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    Group.FG (geometricCharacterGroup H.obj) := by
  have hspan : DiagonalizableGroup.groupLikeSpannedProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
    apply (multiplicativeTypeCommHopfAlgProperty_iff k H).mp
    exact torusCommHopfAlgProperty.multiplicativeType k H hH
  -- `geometricCharacterGroup H.obj` unfolds through two bundled base-change layers; state the
  -- underlying group-like type so the finite-generation theorem sees its coordinate algebra.
  change Group.FG (_root_.GroupLike (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
  exact TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top
    (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
      inferInstance ((DiagonalizableGroup.groupLikeSpannedProperty_iff
        (AlgebraicClosure k) _).mp hspan)

end CommHopfAlgCat

/-- The intrinsic geometric character group of a split-torus presentation is the free abelian
group used to construct its coordinate algebra. -/
noncomputable def splitTorusGeometricCharacterGroupEquiv
    (k : Type u) [Field k] (n : ℕ) :
    CommHopfAlgCat.geometricCharacterGroup
        (DiagonalizableGroup.coordinateRing k
          (SplitTorus.characterGroup (ULift.{u} (Fin n)))).obj ≃*
      Multiplicative (ULift.{u} (Fin n) →₀ ℤ) :=
  (TauCeti.GroupLike.mapEquiv
    (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k)
      (G := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))).trans
    (MonoidAlgebra.groupLikeEquiv (R := AlgebraicClosure k)
      (H := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))

/-- The additive character lattice of a split-torus presentation is its defining finite-rank
free `ℤ`-module. -/
noncomputable def splitTorusCharacterLatticeEquiv
    (k : Type u) [Field k] (n : ℕ) :
    CommHopfAlgCat.characterLattice
        (DiagonalizableGroup.coordinateRing k
          (SplitTorus.characterGroup (ULift.{u} (Fin n)))).obj ≃+
      (ULift.{u} (Fin n) →₀ ℤ) :=
  (MulEquiv.toAdditive (splitTorusGeometricCharacterGroupEquiv k n)).trans
    (AddEquiv.additiveMultiplicative (ULift.{u} (Fin n) →₀ ℤ))

/-- The character lattice of a torus is a finite-rank free abelian group. The equivalence is
noncanonical: it uses the splitting over the chosen algebraic closure from the torus predicate. -/
theorem exists_characterLattice_addEquiv_of_torus (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : torusCommHopfAlgProperty k H) :
    ∃ n : ℕ, Nonempty
      (CommHopfAlgCat.characterLattice H.obj ≃+ (ULift.{u} (Fin n) →₀ ℤ)) := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  let i' : _root_.CommHopfAlgCat.of (AlgebraicClosure k)
        (MonoidAlgebra (AlgebraicClosure k)
          (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) ≅
      _root_.CommHopfAlgCat.of (AlgebraicClosure k)
        (AlgebraicClosure k ⊗[k] H) :=
    (finiteTypeCommHopfAlgProperty (AlgebraicClosure k)).ι.mapIso i
  let e : CommHopfAlgCat.geometricCharacterGroup H.obj ≃*
      Multiplicative (ULift.{u} (Fin n) →₀ ℤ) :=
    (TauCeti.GroupLike.mapEquiv (_root_.CommHopfAlgCat.ofIso i')).symm.trans
      (MonoidAlgebra.groupLikeEquiv (R := AlgebraicClosure k)
        (H := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
  exact ⟨n, ⟨(MulEquiv.toAdditive e).trans
    (AddEquiv.additiveMultiplicative (ULift.{u} (Fin n) →₀ ℤ))⟩⟩

end TauCeti
