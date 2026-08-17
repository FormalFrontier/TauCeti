/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The cotangent space at the identity

For a commutative bialgebra `A` over `R`, the cotangent space at the identity is
the augmentation ideal modulo its square. Its `R`-linear dual represents
counit-valued derivations, hence the tangent space at the identity.

When this cotangent space is finite projective, the usual tensor--Hom
comparison identifies `B ⊗[R] Lie(G)(R)` with the `B`-valued tangent space.
On pure tensors the comparison sends `b ⊗ d` to the derivation
`a ↦ b * algebraMap R B (d a)`. This is the scalar-extension comparison needed
to turn the coefficient-natural adjoint action into an action on one fixed
finite module (ReductiveGroups roadmap, Layer 2).

## Main declarations

* `TauCeti.Bialgebra.CotangentSpace`: the augmentation ideal modulo its square.
* `TauCeti.Bialgebra.cotangentMap`: the universal first-order displacement from
  the identity.
* `TauCeti.Derivation.cotangentLinearEquiv`: the duality between the cotangent
  space and counit-valued derivations.
* `TauCeti.Derivation.tangentScalarExtensionEquiv`: scalar extension of the
  cotangent dual when the cotangent space is finite projective.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12 and §14.
-/

public section

namespace TauCeti

open _root_.Coalgebra TensorProduct

namespace Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The augmentation ideal of a commutative bialgebra, the kernel of its counit. -/
abbrev AugmentationIdeal :=
  RingHom.ker (_root_.Bialgebra.counitAlgHom R A : A →+* R)

/-- The cotangent space at the identity of the affine monoid represented by `A`:
the augmentation ideal `ker ε` modulo its square. -/
abbrev CotangentSpace := (AugmentationIdeal R A).Cotangent

/-- The linear displacement of an element from the scalar selected by the counit. -/
private noncomputable def counitDisplacement : A →ₗ[R] A where
  toFun a := a - algebraMap R A (counit (R := R) a)
  map_add' a b := by
    simp only [map_add]
    abel
  map_smul' r a := by
    simp [Algebra.smul_def]
    ring

/-- The counit displacement regarded as an element of the augmentation ideal. -/
private noncomputable def augmentationProjection : A →ₗ[R] AugmentationIdeal R A where
  toFun a := ⟨counitDisplacement R A a, by
    simp [AugmentationIdeal, counitDisplacement]⟩
  map_add' a b := Subtype.ext ((counitDisplacement R A).map_add a b)
  map_smul' r a := Subtype.ext ((counitDisplacement R A).map_smul r a)

/-- The first-order displacement from the identity, sending `a` to the class of
`a - ε(a)` in the augmentation ideal modulo its square. -/
noncomputable def cotangentMap : A →ₗ[R] CotangentSpace R A where
  __ := ((AugmentationIdeal R A).toCotangent.restrictScalars R).comp
    (augmentationProjection R A)

/-- The cotangent map is the class of the displacement from the counit. -/
@[simp]
lemma cotangentMap_apply (a : A) :
    cotangentMap R A a =
      (AugmentationIdeal R A).toCotangent
        ⟨a - algebraMap R A (counit (R := R) a), by simp⟩ := by
  simp [cotangentMap, augmentationProjection, counitDisplacement]

/-- The cotangent map vanishes at the identity. -/
lemma cotangentMap_one : cotangentMap R A 1 = 0 := by
  rw [cotangentMap_apply]
  apply ((AugmentationIdeal R A).toCotangent_eq_zero _).mpr
  simp

/-- On the augmentation ideal, the cotangent map is the quotient map. -/
lemma cotangentMap_augmentation (x : AugmentationIdeal R A) :
    cotangentMap R A (x : A) = (AugmentationIdeal R A).toCotangent x := by
  rw [cotangentMap_apply]
  have hx : counit (R := R) (x : A) = 0 := by
    exact x.prop
  apply (AugmentationIdeal R A).toCotangent.congr_arg
  ext
  simp [hx]

/-- The cotangent displacement of a product satisfies the Leibniz rule for the
action through the counit. -/
lemma cotangentMap_mul (a b : A) :
    cotangentMap R A (a * b) =
      counit (R := R) a • cotangentMap R A b +
        counit (R := R) b • cotangentMap R A a := by
  rw [cotangentMap_apply, cotangentMap_apply, cotangentMap_apply]
  apply (AugmentationIdeal R A).toCotangent_eq.mpr
  rw [pow_two]
  let x : AugmentationIdeal R A :=
    ⟨a - algebraMap R A (counit (R := R) a), by simp⟩
  let y : AugmentationIdeal R A :=
    ⟨b - algebraMap R A (counit (R := R) b), by simp⟩
  have hxy : (x : A) * (y : A) ∈
      AugmentationIdeal R A * AugmentationIdeal R A :=
    Ideal.mul_mem_mul x.prop y.prop
  convert hxy using 1
  · dsimp [x, y]
    have hc : counit (R := R) (a * b) = counit a * counit b :=
      map_mul (_root_.Bialgebra.counitAlgHom R A) a b
    rw [hc]
    simp only [Algebra.smul_def, map_mul]
    ring

end Bialgebra

namespace Derivation

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Algebra R B]

private lemma algEquivSelf_smul (a : A)
    (z : Bialgebra.CounitAlgebra R A B) :
    Bialgebra.CounitAlgebra.algEquivSelf R A B (a • z) =
      algebraMap R B (counit a) *
        Bialgebra.CounitAlgebra.algEquivSelf R A B z := by
  rw [Algebra.smul_def, map_mul, Bialgebra.CounitAlgebra.algebraMap_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply]
  congr 1
  exact Bialgebra.CounitAlgebra.algEquivSelf_apply
    (R := R) (A := A) (B := B)
    (algebraMap R B (counit a) : Bialgebra.CounitAlgebra R A B)

/-- Construct a counit-valued derivation from a linear map out of the cotangent space. -/
private noncomputable def ofCotangentLinearMap
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  Derivation.mk'
    ((Bialgebra.CounitAlgebra.algEquivSelf R A B).symm.toLinearMap.comp
      (f.comp (Bialgebra.cotangentMap R A)))
    fun a b => by
      simp only [LinearMap.comp_apply]
      rw [Bialgebra.cotangentMap_mul, map_add, map_smul, map_smul]
      apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
      simp only [AlgEquiv.toLinearMap_apply]
      rw [AlgEquiv.apply_symm_apply, map_add, algEquivSelf_smul,
        algEquivSelf_smul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      simp only [Algebra.smul_def]

private lemma algEquivSelf_ofCotangentLinearMap_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) (a : A) :
    Bialgebra.CounitAlgebra.algEquivSelf R A B (ofCotangentLinearMap f a) =
      f (Bialgebra.cotangentMap R A a) := by
  simp only [ofCotangentLinearMap, Derivation.coe_mk', LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]

/-- Factor a counit-valued derivation through the cotangent space. -/
private noncomputable def toCotangentLinearMap
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    Bialgebra.CotangentSpace R A →ₗ[R] B :=
  Ideal.Cotangent.lift
    ((Bialgebra.CounitAlgebra.algEquivSelf R A B).toLinearMap.comp
      ((d : A →ₗ[R] Bialgebra.CounitAlgebra R A B).comp
        ((Bialgebra.AugmentationIdeal R A).subtype.restrictScalars R)))
    fun x y => by
      simp only [LinearMap.comp_apply]
      have hx : counit (R := R) (x : A) = 0 := by
        exact x.prop
      have hy : counit (R := R) (y : A) = 0 := by
        exact y.prop
      have hxy : d ((x : A) * (y : A)) = 0 := by
        rw [Derivation.leibniz]
        simp only [Bialgebra.CounitAlgebra.algebraMap_apply, hx, hy, map_zero,
          Algebra.smul_def]
        -- Both displayed zeroes are in the exported coefficient synonym.
        change (0 : Bialgebra.CounitAlgebra R A B) * d (y : A) +
          0 * d (x : A) = 0
        rw [zero_mul, zero_mul, zero_add]
      -- Expose the stable coercion from the augmentation ideal once.
      change (Bialgebra.CounitAlgebra.algEquivSelf R A B)
        (d ((x : A) * (y : A))) = 0
      rw [hxy]
      exact map_zero (Bialgebra.CounitAlgebra.algEquivSelf R A B)

private lemma toCotangentLinearMap_toCotangent
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B))
    (x : Bialgebra.AugmentationIdeal R A) :
    toCotangentLinearMap d ((Bialgebra.AugmentationIdeal R A).toCotangent x) =
      Bialgebra.CounitAlgebra.algEquivSelf R A B (d x) := by
  simp only [toCotangentLinearMap, Ideal.Cotangent.lift_toCotangent,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    LinearMap.restrictScalars_apply, Submodule.coe_subtype]
  -- After the named coercion reductions, both sides are the same application of `d`.
  rfl

/-- The linear equivalence between cotangent-space functionals and counit-valued derivations. -/
private noncomputable def cotangentLinearEquivBase :
    (Bialgebra.CotangentSpace R A →ₗ[R] B) ≃ₗ[R]
      Derivation R A (Bialgebra.CounitAlgebra R A B) where
  toFun := ofCotangentLinearMap
  invFun := toCotangentLinearMap
  left_inv f := by
    ext x
    obtain ⟨x, rfl⟩ :=
      (Bialgebra.AugmentationIdeal R A).toCotangent_surjective x
    rw [toCotangentLinearMap_toCotangent,
      algEquivSelf_ofCotangentLinearMap_apply,
      Bialgebra.cotangentMap_augmentation]
  right_inv d := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
    rw [algEquivSelf_ofCotangentLinearMap_apply, Bialgebra.cotangentMap_apply,
      toCotangentLinearMap_toCotangent]
    simp only [map_sub, d.map_algebraMap, sub_zero]
  map_add' f g := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
    simp only [algEquivSelf_ofCotangentLinearMap_apply, LinearMap.add_apply,
      Derivation.add_apply, map_add]
  map_smul' r f := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
    simp only [algEquivSelf_ofCotangentLinearMap_apply, LinearMap.smul_apply,
      RingHom.id_apply, Derivation.smul_apply, map_smul]

private lemma cotangentLinearEquivBase_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) :
    cotangentLinearEquivBase (R := R) (A := A) (B := B) f =
      ofCotangentLinearMap f := rfl

private lemma cotangentLinearEquivBase_map_smul (b : B)
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) :
    cotangentLinearEquivBase (R := R) (A := A) (B := B) (b • f) =
      b • cotangentLinearEquivBase (R := R) (A := A) (B := B) f := by
  ext a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  rw [cotangentLinearEquivBase_apply, cotangentLinearEquivBase_apply,
    algEquivSelf_ofCotangentLinearMap_apply, LinearMap.smul_apply,
    Derivation.smul_apply]
  calc
    b • f (Bialgebra.cotangentMap R A a) =
        b • Bialgebra.CounitAlgebra.algEquivSelf R A B (ofCotangentLinearMap f a) := by
      rw [algEquivSelf_ofCotangentLinearMap_apply]
    _ = Bialgebra.CounitAlgebra.algEquivSelf R A B (b • ofCotangentLinearMap f a) := by
      rw [Bialgebra.CounitAlgebra.algEquivSelf_apply,
        Bialgebra.CounitAlgebra.algEquivSelf_apply]
      rfl

/-- Linear functionals on the cotangent space are naturally equivalent to
counit-valued derivations, i.e. tangent vectors at the identity. The equivalence
is linear over the coefficient ring. -/
noncomputable def cotangentLinearEquiv :
    (Bialgebra.CotangentSpace R A →ₗ[R] B) ≃ₗ[B]
      Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  { (cotangentLinearEquivBase (R := R) (A := A) (B := B)).toEquiv with
    map_add' := (cotangentLinearEquivBase (R := R) (A := A) (B := B)).map_add
    map_smul' := cotangentLinearEquivBase_map_smul }

private lemma cotangentLinearEquiv_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) :
    cotangentLinearEquiv (R := R) (A := A) (B := B) f =
      cotangentLinearEquivBase (R := R) (A := A) (B := B) f := rfl

/-- The cotangent-duality equivalence sends a functional to its value on the
first-order displacement. -/
@[simp]
lemma cotangentLinearEquiv_apply_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) (a : A) :
    cotangentLinearEquiv f a = f (Bialgebra.cotangentMap R A a) := by
  rw [cotangentLinearEquiv_apply, cotangentLinearEquivBase_apply]
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  rw [algEquivSelf_ofCotangentLinearMap_apply]
  exact (Bialgebra.CounitAlgebra.algEquivSelf_apply
    (R := R) (A := A) (B := B)
    (f (Bialgebra.cotangentMap R A a) : Bialgebra.CounitAlgebra R A B)).symm

/-- The inverse cotangent-duality equivalence evaluates a derivation on a
representative in the augmentation ideal. -/
@[simp]
lemma cotangentLinearEquiv_symm_toCotangent
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B))
    (x : Bialgebra.AugmentationIdeal R A) :
    (cotangentLinearEquiv (R := R) (A := A) (B := B)).symm d
        ((Bialgebra.AugmentationIdeal R A).toCotangent x) =
      Bialgebra.CounitAlgebra.algEquivSelf R A B (d x) := by
  exact toCotangentLinearMap_toCotangent d x

/-- Scalar extension of tangent vectors. If the cotangent space is finite
projective, `B` tensored with its dual is naturally the space of `B`-valued
tangent vectors. The dual is identified with `Lie(G)(R)` by
`cotangentLinearEquiv`. -/
private noncomputable def tangentScalarExtensionEquivBase
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)] :
    B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A) ≃ₗ[R]
      Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  TensorProduct.comm R B _ ≪≫ₗ
    dualTensorHomEquiv R (Bialgebra.CotangentSpace R A) B ≪≫ₗ
    cotangentLinearEquivBase (R := R) (A := A) (B := B)

private lemma tangentScalarExtensionEquivBase_apply
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)]
    (x : B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A)) :
    tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) x =
      cotangentLinearEquivBase (R := R) (A := A) (B := B)
        (dualTensorHom R (Bialgebra.CotangentSpace R A) B
          (TensorProduct.comm R B _ x)) := by
  simp [tangentScalarExtensionEquivBase, dualTensorHomEquiv]

private lemma tangentScalarExtensionEquivBase_tmul_apply
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)]
    (b : B) (f : Module.Dual R (Bialgebra.CotangentSpace R A)) (a : A) :
    tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) (b ⊗ₜ[R] f) a =
      b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  rw [tangentScalarExtensionEquivBase_apply, TensorProduct.comm_tmul,
    cotangentLinearEquivBase_apply, algEquivSelf_ofCotangentLinearMap_apply]
  calc
    (dualTensorHom R (Bialgebra.CotangentSpace R A) B (f ⊗ₜ[R] b))
        (Bialgebra.cotangentMap R A a) =
        b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) := by
      simp [dualTensorHom_apply, Algebra.smul_def, mul_comm]
    _ = Bialgebra.CounitAlgebra.algEquivSelf R A B
        (b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) :
          Bialgebra.CounitAlgebra R A B) :=
      (Bialgebra.CounitAlgebra.algEquivSelf_apply
        (R := R) (A := A) (B := B)
        (b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) :
          Bialgebra.CounitAlgebra R A B)).symm

private lemma tangentScalarExtensionEquivBase_map_smul
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)]
    (b : B) (x : B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A)) :
    tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) (b • x) =
      b • tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b' f =>
      ext a
      rw [TensorProduct.smul_tmul', tangentScalarExtensionEquivBase_tmul_apply,
        Derivation.smul_apply, tangentScalarExtensionEquivBase_tmul_apply]
      exact smul_mul_assoc b b' _
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Scalar extension of tangent vectors. If the cotangent space is finite
projective, `B` tensored with its dual is naturally the space of `B`-valued
tangent vectors. The dual is identified with `Lie(G)(R)` by
`cotangentLinearEquiv`. -/
noncomputable def tangentScalarExtensionEquiv
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)] :
    B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A) ≃ₗ[B]
      Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  { (tangentScalarExtensionEquivBase (R := R) (A := A) (B := B)).toEquiv with
    map_add' := (tangentScalarExtensionEquivBase
      (R := R) (A := A) (B := B)).map_add
    map_smul' := tangentScalarExtensionEquivBase_map_smul }

private lemma tangentScalarExtensionEquiv_apply
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)]
    (x : B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A)) :
    tangentScalarExtensionEquiv (R := R) (A := A) (B := B) x =
      tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) x := rfl

/-- On pure tensors, scalar extension evaluates the cotangent functional and
multiplies it by the coefficient. -/
@[simp]
lemma tangentScalarExtensionEquiv_tmul_apply
    [Module.Finite R (Bialgebra.CotangentSpace R A)]
    [Module.Projective R (Bialgebra.CotangentSpace R A)]
    (b : B) (f : Module.Dual R (Bialgebra.CotangentSpace R A)) (a : A) :
    tangentScalarExtensionEquiv (R := R) (A := A) (B := B) (b ⊗ₜ[R] f) a =
      b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) := by
  rw [tangentScalarExtensionEquiv_apply,
    tangentScalarExtensionEquivBase_tmul_apply]

end Derivation

end TauCeti
