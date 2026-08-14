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
* `TauCeti.CommHopfAlgCat.instMulSemiringActionAlgebraicClosure`: an instance bridge for the
  absolute-Galois action on the algebraic closure.
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

/-- Bridge the tautological action across the opaque `Field.absoluteGaloisGroup` definition. -/
noncomputable abbrev instMulSemiringActionAlgebraicClosure :
    MulSemiringAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k) := by
  unfold Field.absoluteGaloisGroup
  exact AlgEquiv.applyMulSemiringAction

attribute [instance] instMulSemiringActionAlgebraicClosure

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

/-- Evaluation through the absolute-Galois wrapper agrees with the underlying algebra
equivalence. -/
theorem smul_algebraicClosure (sigma : Field.absoluteGaloisGroup k)
    (a : AlgebraicClosure k) :
    sigma • a = (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from sigma) a := by
  unfold Field.absoluteGaloisGroup at sigma ⊢
  exact AlgEquiv.smul_def sigma a

/-- The scalar-extension action crosses the absolute-Galois wrapper on pure tensors. -/
theorem smul_tmul_absoluteGalois {A : Type u} [Semiring A] [Algebra k A]
    (sigma : Field.absoluteGaloisGroup k) (a : AlgebraicClosure k) (x : A) :
    sigma • (a ⊗ₜ[k] x) =
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from sigma) a ⊗ₜ[k] x := by
  unfold Field.absoluteGaloisGroup at sigma ⊢
  exact ScalarAut.smul_tmul sigma a x

/-- The underlying value of the absolute-Galois action on a scalar-extended group-like element. -/
@[simp]
theorem val_smul {A : Type u} [Semiring A] [Bialgebra k A]
    (sigma : Field.absoluteGaloisGroup k)
    (x : _root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :
    (sigma • x).val =
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from sigma) • x.val :=
  by
    -- Mathlib exposes `absoluteGaloisGroup` as an opaque `def`, with no conversion lemma to the
    -- underlying algebra equivalence, so this boundary must unfold the wrapper.
    unfold Field.absoluteGaloisGroup at sigma ⊢
    exact ScalarAut.val_smul sigma x

/-- Passing from additive to multiplicative group-like elements commutes with the
absolute-Galois action. -/
@[simp]
theorem toMul_smul {A : Type u} [Semiring A] [Bialgebra k A]
    (sigma : Field.absoluteGaloisGroup k)
    (x : Additive (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))) :
    (sigma • x).toMul = sigma • x.toMul :=
  by
    unfold Field.absoluteGaloisGroup at sigma ⊢
    exact ScalarAut.toMul_smul sigma x

end CommHopfAlgCat

end TauCeti
