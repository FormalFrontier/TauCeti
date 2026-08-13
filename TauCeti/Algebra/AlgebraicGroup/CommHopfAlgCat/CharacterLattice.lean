/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Galois

/-!
# Geometric character groups and their Galois action

For a commutative Hopf algebra `H` over a field `k`, its geometric characters are the group-like
elements of its coordinate algebra after extension to an algebraic closure:

```text
X*(H) = GroupLike k̄ (k̄ ⊗[k] H).
```

The generic scalar action from `TauCeti.Algebra.Bialgebra.GroupLike.Galois` specializes to the
absolute Galois group and acts by `σ • (a ⊗ h) = σ(a) ⊗ h`. Its actions on the scalar
extension, the group-like elements, and their additive form are available through the instances
`GaloisScalar.instScalarMulSemiringAction`, `GaloisScalar.instGroupLikeDistribMulAction`, and
`GaloisScalar.instAdditiveDistribMulAction`.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroup`: the geometric character group.
* `TauCeti.CommHopfAlgCat.additiveCharacterGroup`: its additive form.
* `TauCeti.CommHopfAlgCat.instGaloisScalarMulSemiringAction`: the absolute-Galois action on the
  scalar extension.
* `TauCeti.CommHopfAlgCat.instGeometricCharacterGroupGaloisAction`: the induced action on
  geometric characters.
* `TauCeti.CommHopfAlgCat.instAdditiveCharacterGroupGaloisAction`: the transported additive
  action.

## References

For the torus character-module viewpoint motivating this construction, see J. S. Milne,
*Algebraic Groups* (2017), §§12.14--12.17. The scalar-action lemmas themselves are generic
bialgebra facts.
-/

public section

open TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{u} k)

/-- The geometric character group of a commutative Hopf algebra: the group-like elements of
its coordinate algebra after extension to an algebraic closure. For a represented affine group,
these are exactly its morphisms over `k̄` to the multiplicative group. -/
abbrev geometricCharacterGroup :=
  GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H)

/-- Specialize the generic scalar-factor map to an absolute-Galois automorphism. -/
noncomputable def galoisScalarMap (σ : Field.absoluteGaloisGroup k) :
    AlgebraicClosure k ⊗[k] H →ₐ[k] AlgebraicClosure k ⊗[k] H :=
  GaloisScalar.map (A := H)
    (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ)

/-- The specialized Galois scalar map acts through the first tensor factor. -/
@[simp]
theorem galoisScalarMap_tmul (σ : Field.absoluteGaloisGroup k)
    (a : AlgebraicClosure k) (x : H) :
    galoisScalarMap H σ (a ⊗ₜ[k] x) = σ.toAlgHom a ⊗ₜ[k] x := by
  exact GaloisScalar.map_tmul
    (A := H) (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) a x

/-- The identity absolute-Galois automorphism acts trivially. -/
@[simp]
theorem galoisScalarMap_one_apply (x : AlgebraicClosure k ⊗[k] H) :
    galoisScalarMap H 1 x = x := by
  have h_one : (1 : Field.absoluteGaloisGroup k).toAlgHom =
      AlgHom.id k (AlgebraicClosure k) := AlgHom.ext fun _ => rfl
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
      rw [galoisScalarMap_tmul]
      exact congrArg (fun b : AlgebraicClosure k => b ⊗ₜ[k] x)
        (DFunLike.congr_fun h_one a)

/-- Specialized Galois scalar maps compose according to multiplication. -/
theorem galoisScalarMap_mul_apply (σ τ : Field.absoluteGaloisGroup k)
    (x : AlgebraicClosure k ⊗[k] H) :
    galoisScalarMap H (σ * τ) x = galoisScalarMap H σ (galoisScalarMap H τ x) := by
  have h_mul : (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom := AlgHom.ext fun _ => rfl
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
      rw [galoisScalarMap_tmul, galoisScalarMap_tmul, galoisScalarMap_tmul]
      exact congrArg (fun b : AlgebraicClosure k => b ⊗ₜ[k] x)
        (DFunLike.congr_fun h_mul a)

/-- The specialized scalar map preserves group-like elements. -/
theorem isGroupLikeElem_galoisScalarMap (σ : Field.absoluteGaloisGroup k)
    {x : AlgebraicClosure k ⊗[k] H} (hx : IsGroupLikeElem (AlgebraicClosure k) x) :
    IsGroupLikeElem (AlgebraicClosure k) (galoisScalarMap H σ x) := by
  exact GaloisScalar.isGroupLikeElem_map
    (A := H) (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) hx

/-- The absolute Galois group acts on a scalar-extended coordinate ring through its scalar
factor. -/
noncomputable instance instGaloisScalarMulSemiringAction :
    MulSemiringAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k ⊗[k] H) where
  smul σ x := galoisScalarMap H σ x
  one_smul := galoisScalarMap_one_apply H
  mul_smul := galoisScalarMap_mul_apply H
  smul_zero σ := map_zero (galoisScalarMap H σ)
  smul_add σ := map_add (galoisScalarMap H σ)
  smul_one σ := map_one (galoisScalarMap H σ)
  smul_mul σ := map_mul (galoisScalarMap H σ)

/-- The absolute Galois group acts multiplicatively on geometric characters. -/
noncomputable instance instGeometricCharacterGroupGaloisAction :
    MulDistribMulAction (Field.absoluteGaloisGroup k) (geometricCharacterGroup H) where
  smul σ x := ⟨galoisScalarMap H σ x.val,
    isGroupLikeElem_galoisScalarMap H σ x.isGroupLikeElem_val⟩
  one_smul x := GroupLike.val_injective (galoisScalarMap_one_apply H x.val)
  mul_smul σ τ x := GroupLike.val_injective (galoisScalarMap_mul_apply H σ τ x.val)
  smul_one σ := GroupLike.val_injective (map_one (galoisScalarMap H σ))
  smul_mul σ x y := GroupLike.val_injective (map_mul (galoisScalarMap H σ) x.val y.val)

/-- The absolute-Galois action on the scalar extension is the generic scalar-factor map. -/
@[simp]
theorem galoisScalar_smul_def (σ : Field.absoluteGaloisGroup k)
    (x : AlgebraicClosure k ⊗[k] H) :
    σ • x = galoisScalarMap H σ x :=
  (rfl)

/-- The absolute-Galois action on a pure tensor acts through the scalar factor. -/
theorem galoisScalar_smul_tmul (σ : Field.absoluteGaloisGroup k)
    (a : AlgebraicClosure k) (x : H) :
    σ • (a ⊗ₜ[k] x) = σ.toAlgHom a ⊗ₜ[k] x := by
  rw [galoisScalar_smul_def, galoisScalarMap_tmul]

/-- The coordinate of the Galois action on a geometric character is the scalar-factor map. -/
@[simp]
theorem val_smul_geometricCharacterGroup (σ : Field.absoluteGaloisGroup k)
    (x : geometricCharacterGroup H) :
    (σ • x).val = galoisScalarMap H σ x.val :=
  (rfl)

/-- The additive form of the geometric character group of a commutative Hopf algebra. For a
torus its underlying additive group is free of finite rank. -/
abbrev additiveCharacterGroup := Additive (geometricCharacterGroup H)

/-- The absolute Galois action on the additive character group. -/
noncomputable instance instAdditiveCharacterGroupGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup k) (additiveCharacterGroup H) where
  smul σ x := Additive.ofMul (σ • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul _ x.toMul)
  mul_smul σ τ x := congrArg Additive.ofMul (mul_smul σ τ x.toMul)
  smul_zero σ := congrArg Additive.ofMul (smul_one σ)
  smul_add σ x y := congrArg Additive.ofMul (smul_mul' σ x.toMul y.toMul)

/-- The additive Galois action is transported from the geometric character group. -/
@[simp]
theorem smul_ofMul_additiveCharacterGroup (σ : Field.absoluteGaloisGroup k)
    (x : geometricCharacterGroup H) :
    σ • Additive.ofMul x = Additive.ofMul (σ • x) :=
  (rfl)

/-- Passing to the underlying geometric character commutes with the Galois action. -/
@[simp]
theorem toMul_smul_additiveCharacterGroup (σ : Field.absoluteGaloisGroup k)
    (x : additiveCharacterGroup H) :
    (σ • x).toMul = σ • x.toMul :=
  (rfl)

end CommHopfAlgCat

end TauCeti
