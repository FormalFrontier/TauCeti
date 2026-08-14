/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut

/-!
# Geometric character groups and their Galois action

For a commutative Hopf algebra `H` over a field `k`, its geometric characters are the group-like
elements of its coordinate algebra after extension to an algebraic closure:

```text
X*(H) = GroupLike k̄ (k̄ ⊗[k] H).
```

The generic scalar action from `TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut` specializes to the
absolute Galois group and acts by `σ • (a ⊗ h) = σ(a) ⊗ h`. Its actions on the scalar
extension, the group-like elements, and their additive form are available through the instances
`ScalarAut.instMulSemiringAction`, `ScalarAut.instGroupLikeDistribMulAction`, and
`ScalarAut.instAdditiveDistribMulAction`; this module supplies the instance bridges needed for
the opaque `Field.absoluteGaloisGroup` definition.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroup`: the geometric character group.
* `TauCeti.CommHopfAlgCat.additiveCharacterGroup`: its additive form.
* `TauCeti.CommHopfAlgCat.instGaloisScalarMulSemiringAction`: an instance bridge for the
  absolute-Galois action on the scalar extension.
* `TauCeti.CommHopfAlgCat.instGeometricCharacterGroupGaloisAction`: an instance bridge for the
  induced action on geometric characters.
* `TauCeti.CommHopfAlgCat.instAdditiveCharacterGroupGaloisAction`: an instance bridge for the
  transported additive action.

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

/-- Bridge the generic scalar action across the opaque `Field.absoluteGaloisGroup` definition. -/
noncomputable abbrev instGaloisScalarMulSemiringAction {A : Type u} [Semiring A] [Algebra k A] :
    MulSemiringAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k ⊗[k] A) := by
  unfold Field.absoluteGaloisGroup
  exact ScalarAut.instMulSemiringAction

attribute [instance] instGaloisScalarMulSemiringAction

/-- Bridge the generic group-like action across the opaque absolute-Galois-group definition. -/
noncomputable abbrev instGeometricCharacterGroupGaloisAction {A : Type u}
    [Semiring A] [Bialgebra k A] :
    MulDistribMulAction (Field.absoluteGaloisGroup k)
      (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) := by
  unfold Field.absoluteGaloisGroup
  exact ScalarAut.instGroupLikeDistribMulAction

attribute [instance] instGeometricCharacterGroupGaloisAction

/-- The additive form of the geometric character group of a commutative Hopf algebra. For a
torus its underlying additive group is free of finite rank. -/
abbrev additiveCharacterGroup := Additive (geometricCharacterGroup H)

/-- Bridge the generic additive action across the opaque absolute-Galois-group definition. -/
noncomputable abbrev instAdditiveCharacterGroupGaloisAction {A : Type u}
    [Semiring A] [Bialgebra k A] :
    DistribMulAction (Field.absoluteGaloisGroup k)
      (Additive (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))) := by
  unfold Field.absoluteGaloisGroup
  exact ScalarAut.instAdditiveDistribMulAction

attribute [instance] instAdditiveCharacterGroupGaloisAction

/-- The absolute-Galois action on a scalar extension is tensor-product congruence. -/
@[simp]
theorem smul_def (H : _root_.CommHopfAlgCat.{u} k)
    (σ : Field.absoluteGaloisGroup k) (x : AlgebraicClosure k ⊗[k] H) :
    σ • x = Algebra.TensorProduct.congr
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) .refl x := by
  rw [show σ • x = ScalarAut.congrHom (A := H)
    (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) x from rfl]
  rw [ScalarAut.congrHom_apply]

/-- The absolute-Galois action on the scalar extension is the scalar-factor action. -/
@[simp]
theorem smul_tmul (σ : Field.absoluteGaloisGroup k) (a : AlgebraicClosure k) (x : H) :
    Algebra.TensorProduct.congr
        (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) .refl (a ⊗ₜ[k] x) =
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) a ⊗ₜ[k] x := by
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

/-- The underlying value of the absolute-Galois action on a geometric character. -/
@[simp]
theorem val_smul (σ : Field.absoluteGaloisGroup k) (x : geometricCharacterGroup H) :
    (σ • x).val = (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) • x.val :=
  by
    unfold Field.absoluteGaloisGroup at σ ⊢
    exact ScalarAut.val_smul σ x

/-- Passing from additive to multiplicative characters commutes with the absolute-Galois action. -/
@[simp]
theorem toMul_smul (σ : Field.absoluteGaloisGroup k) (x : additiveCharacterGroup H) :
    (σ • x).toMul = σ • x.toMul :=
  by
    unfold Field.absoluteGaloisGroup at σ ⊢
    exact ScalarAut.toMul_smul σ x

end CommHopfAlgCat

end TauCeti
