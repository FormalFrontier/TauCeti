/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange

/-!
# Base change of additive groups

The vector group attached to a `k`-module `M` is represented by the symmetric bialgebra
`SymmetricAlgebra k M`. This file specializes the generic symmetric-bialgebra base-change
equivalence to the rank-one additive group `𝔾ₐ`, and records the corresponding
functor-of-points calculation: if `A` is a commutative `K`-algebra, then the convolution monoid
of `K`-algebra maps out of `K ⊗[k] SymmetricAlgebra k M` is the additive monoid of `k`-linear
maps `M →ₗ[k] A`.

The coordinate result imported from `TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange`
transports the counit and comultiplication, hence is bialgebra-level. No separate antipode or
Hopf-equivalence packaging is asserted here.

The equivalence first restricts a base-changed point along `m ↦ 1 ⊗ ι(m)` using
`AlgHom.baseChangePointsMulEquiv`, then applies `AdditiveGroup.pointsMulEquiv`. The
characteristic lemmas spell out the generator values, the inverse map on scalar multiples of
generators, and the one-dimensional additive group `𝔾ₐ`.

These specializations align the bialgebra and functor-of-points presentations used by the
additive-group worked example in the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv`: the rank-one specialization for `𝔾ₐ`.
* `TauCeti.AdditiveGroup.coordinateHopfAlgebraBaseChangeIso`: its bundled
  commutative-Hopf-algebra form, when the extension ring's universe contains the base ring's.
* `TauCeti.AdditiveGroup.coordinateHopfAlgebraBaseChangeIso_hom_apply_tmul_ι`,
  `TauCeti.AdditiveGroup.coordinateHopfAlgebraBaseChangeIso_hom_apply_tmul_one` and
  `TauCeti.AdditiveGroup.coordinateHopfAlgebraBaseChangeIso_inv_apply_ι`: its coordinate formulas
  on the additive generator and the scalar copies, in both directions.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι`: its forward coordinate formula.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv_tmul_one`: its formula on scalar copies.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv_symm_ι`: the inverse formula for the additive
  coordinate.
* `TauCeti.AdditiveGroup.baseChangePointsMulEquiv`: base-changed vector-group points are
  `k`-linear maps `M →ₗ[k] A`.
* `TauCeti.AdditiveGroup.toAdd_baseChangePointsMulEquiv_apply`: the equivalence reads a
  point on `1 ⊗ ι(m)`.
* `TauCeti.AdditiveGroup.baseChangePointsMulEquiv_symm_apply_tmul_ι`: the inverse
  equivalence evaluates scalar multiples of base-changed generators.
* `TauCeti.AdditiveGroup.gaBaseChangePointsMulEquiv`: the base-changed `𝔾ₐ` points are the
  additive monoid of `A`.

## References

The coordinate-bialgebra equivalence is
`TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`.
The generic points base-change step is Tau Ceti's `AlgHom.baseChangePointsMulEquiv`; the
vector-group points calculation is Tau Ceti's `AdditiveGroup.pointsMulEquiv`. This specialization
follows the API pattern of `RootsOfUnityGroup.baseChangePointsMulEquiv`,
`SplitTorus.baseChangePointsMulEquiv`, and `DiagonalizableGroup.baseChangePointsMulEquiv`.
The construction follows W. C. Waterhouse, *Introduction to Affine Group Schemes*, §1.
-/

public section

open SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w w'

variable {k : Type u} {K : Type v} {A : Type w} {M : Type w'}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
variable [AddCommMonoid M] [Module k M]

section CoordinateBialgebra

/-- The algebra equivalence on symmetric algebras induced by a linear equivalence. -/
private noncomputable def symmetricAlgebraAlgEquiv {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) : SymmetricAlgebra K P ≃ₐ[K] SymmetricAlgebra K N :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι K N ∘ₗ e.toLinearMap))
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι K P ∘ₗ e.symm.toLinearMap))
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro n
      simp [LinearMap.comp_apply])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro m
      simp [LinearMap.comp_apply])

@[simp]
private theorem symmetricAlgebraAlgEquiv_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (p : P) :
    symmetricAlgebraAlgEquiv (K := K) e (SymmetricAlgebra.ι K P p) =
      SymmetricAlgebra.ι K N (e p) := by
  simp [symmetricAlgebraAlgEquiv, LinearMap.comp_apply]

@[simp]
private theorem symmetricAlgebraAlgEquiv_symm_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (n : N) :
    (symmetricAlgebraAlgEquiv (K := K) e).symm (SymmetricAlgebra.ι K N n) =
      SymmetricAlgebra.ι K P (e.symm n) := by
  simp [symmetricAlgebraAlgEquiv, LinearMap.comp_apply]

/-- The bialgebra equivalence on symmetric algebras induced by a linear equivalence. -/
private noncomputable def symmetricAlgebraBialgEquiv {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N] (e : P ≃ₗ[K] N) :
    SymmetricAlgebra K P ≃ₐc[K] SymmetricAlgebra K N :=
  BialgEquiv.ofAlgEquiv (symmetricAlgebraAlgEquiv (K := K) e)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro m
      have h :
          (Bialgebra.counitAlgHom K (SymmetricAlgebra K N))
              (symmetricAlgebraAlgEquiv (K := K) e (SymmetricAlgebra.ι K P m)) =
            (Bialgebra.counitAlgHom K (SymmetricAlgebra K P))
              (SymmetricAlgebra.ι K P m) := by
        rw [symmetricAlgebraAlgEquiv_ι]
        exact (SymmetricAlgebra.algebraMapInv_ι _).trans
          (SymmetricAlgebra.algebraMapInv_ι _).symm
      exact h)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro m
      simp [symmetricAlgebraAlgEquiv, LinearMap.comp_apply, SymmetricAlgebra.comul_ι])

@[simp]
private theorem symmetricAlgebraBialgEquiv_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (p : P) :
    symmetricAlgebraBialgEquiv (K := K) e (SymmetricAlgebra.ι K P p) =
      SymmetricAlgebra.ι K N (e p) :=
  symmetricAlgebraAlgEquiv_ι (K := K) e p

@[simp]
private theorem symmetricAlgebraBialgEquiv_symm_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (n : N) :
    (symmetricAlgebraBialgEquiv (K := K) e).symm (SymmetricAlgebra.ι K N n) =
      SymmetricAlgebra.ι K P (e.symm n) :=
  symmetricAlgebraAlgEquiv_symm_ι (K := K) e n

section GaCoordinateBialgebra

/-- **Base change of the additive coordinate bialgebra is the additive coordinate bialgebra over
the new base.**

This is the rank-one specialization of `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`,
transported along `K ⊗[k] k ≃ K`. -/
noncomputable def gaScalarTensorBialgEquiv :
    K ⊗[k] SymmetricAlgebra k k ≃ₐc[K] SymmetricAlgebra K K :=
  (TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv
      (k := k) (K := K) (M := k)).trans <|
    symmetricAlgebraBialgEquiv (K := K)
      (Algebra.TensorProduct.rid k K K).toLinearEquiv

/-- The `𝔾ₐ` coordinate equivalence sends `s ⊗ ι(r)` to
`s • ι(algebraMap k K r)`. -/
@[simp]
theorem gaScalarTensorBialgEquiv_tmul_ι (s : K) (r : k) :
    gaScalarTensorBialgEquiv (k := k) (K := K)
        (s ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      s • SymmetricAlgebra.ι K K (algebraMap k K r) := by
  calc
    _ = symmetricAlgebraBialgEquiv (K := K)
        (Algebra.TensorProduct.rid k K K).toLinearEquiv
          (SymmetricAlgebra.ι K (K ⊗[k] k) (s ⊗ₜ[k] r)) := by
      rw [gaScalarTensorBialgEquiv, BialgEquiv.trans_apply]
      exact congrArg
        (symmetricAlgebraBialgEquiv (K := K)
          (Algebra.TensorProduct.rid k K K).toLinearEquiv)
        (TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv_tmul_ι
          (k := k) (K := K) (M := k) s r)
    _ = SymmetricAlgebra.ι K K
        (Algebra.TensorProduct.rid k K K (s ⊗ₜ[k] r)) := by
      exact symmetricAlgebraBialgEquiv_ι (K := K)
        (Algebra.TensorProduct.rid k K K).toLinearEquiv (s ⊗ₜ[k] r)
    _ = _ := by
      rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def,
        mul_comm (algebraMap k K r) s]
      exact map_smul (SymmetricAlgebra.ι K K) s (algebraMap k K r)

/-- The `𝔾ₐ` coordinate equivalence identifies the scalar copy of `K` on both sides. -/
@[simp]
theorem gaScalarTensorBialgEquiv_tmul_one (s : K) :
    gaScalarTensorBialgEquiv (k := k) (K := K) (s ⊗ₜ[k] 1) =
      algebraMap K (SymmetricAlgebra K K) s := by
  calc
    _ = symmetricAlgebraBialgEquiv (K := K)
        (Algebra.TensorProduct.rid k K K).toLinearEquiv
          (algebraMap K (SymmetricAlgebra K (K ⊗[k] k)) s) := by
      rw [gaScalarTensorBialgEquiv, BialgEquiv.trans_apply]
      exact congrArg
        (symmetricAlgebraBialgEquiv (K := K)
          (Algebra.TensorProduct.rid k K K).toLinearEquiv)
        (TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv_tmul_one
          (k := k) (K := K) (M := k) s)
    _ = _ := AlgEquiv.commutes
      (symmetricAlgebraBialgEquiv (K := K)
        (Algebra.TensorProduct.rid k K K).toLinearEquiv :
          SymmetricAlgebra K (K ⊗[k] k) ≃ₐ[K] SymmetricAlgebra K K) s

/-- The inverse `𝔾ₐ` coordinate equivalence sends `ι(s)` to the pure tensor
`s ⊗ ι(1)`. -/
@[simp]
theorem gaScalarTensorBialgEquiv_symm_ι (s : K) :
    (gaScalarTensorBialgEquiv (k := k) (K := K)).symm
        (SymmetricAlgebra.ι K K s) =
      s ⊗ₜ[k] SymmetricAlgebra.ι k k 1 := by
  have h :
      gaScalarTensorBialgEquiv (k := k) (K := K)
          (s ⊗ₜ[k] SymmetricAlgebra.ι k k 1) =
        SymmetricAlgebra.ι K K s := by
    rw [gaScalarTensorBialgEquiv_tmul_ι, map_one, ← map_smul]
    simp
  calc
    _ = (gaScalarTensorBialgEquiv (k := k) (K := K)).symm
        (gaScalarTensorBialgEquiv (k := k) (K := K)
          (s ⊗ₜ[k] SymmetricAlgebra.ι k k 1)) := congrArg _ h.symm
    _ = _ := BialgEquiv.symm_apply_apply _ _

open CategoryTheory in
/-- **Base change of the bundled `𝔾ₐ` coordinate Hopf algebra is the `𝔾ₐ` coordinate Hopf
algebra over the new base.**

This is the categorical form of `gaScalarTensorBialgEquiv`, mirroring
`GeneralLinear.coordinateHopfAlgebraBaseChangeIso`. The extension ring's carrier universe must
contain the base ring's carrier universe; in particular, this covers `ℤ → K` for `K` in any
universe. The underlying bialgebra equivalence has no such restriction. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso
    (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K] :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k) ≅
      coordinateHopfAlgebra K :=
  (CommHopfAlgCat.ofIsoSelf
      (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k))).symm ≪≫
    CommHopfAlgCat.isoMk (gaScalarTensorBialgEquiv (k := k) (K := K)) ≪≫
      CommHopfAlgCat.ofIsoSelf (coordinateHopfAlgebra K)

open CategoryTheory in
/-- The bundled base-change isomorphism has the same action on the additive coordinate generator
as the underlying bialgebra equivalence. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_hom_apply_tmul_ι
    (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K] (s : K) (r : k) :
    (coordinateHopfAlgebraBaseChangeIso k K).hom
        (s ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      s • SymmetricAlgebra.ι K K (algebraMap k K r) := by
  simp only [coordinateHopfAlgebraBaseChangeIso, Iso.trans_hom, comp_apply,
    CommHopfAlgCat.ofIsoSelf_hom, CommHopfAlgCat.isoMk_hom, Iso.symm_hom,
    CommHopfAlgCat.ofIsoSelf_inv]
  exact gaScalarTensorBialgEquiv_tmul_ι (k := k) (K := K) s r

open CategoryTheory in
/-- The bundled base-change isomorphism identifies the scalar copy of `K` on both sides. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_hom_apply_tmul_one
    (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K] (s : K) :
    (coordinateHopfAlgebraBaseChangeIso k K).hom (s ⊗ₜ[k] 1) =
      algebraMap K (SymmetricAlgebra K K) s := by
  simp only [coordinateHopfAlgebraBaseChangeIso, Iso.trans_hom, comp_apply,
    CommHopfAlgCat.ofIsoSelf_hom, CommHopfAlgCat.isoMk_hom, Iso.symm_hom,
    CommHopfAlgCat.ofIsoSelf_inv]
  exact gaScalarTensorBialgEquiv_tmul_one (k := k) (K := K) s

open CategoryTheory in
/-- The inverse bundled base-change isomorphism sends the additive coordinate generator back to
its scalar pure tensor. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_inv_apply_ι
    (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K] (s : K) :
    (coordinateHopfAlgebraBaseChangeIso k K).inv (SymmetricAlgebra.ι K K s) =
      s ⊗ₜ[k] SymmetricAlgebra.ι k k 1 := by
  -- The inverse of the categorical composite reduces to `ofHom` of the symmetric bialgebra
  -- equivalence between two identity morphisms. Its coercion to a function is definitionally the
  -- symmetric equivalence, but `ofHom_apply` is deliberately not a simp lemma.
  change (gaScalarTensorBialgEquiv (k := k) (K := K)).symm
      (SymmetricAlgebra.ι K K s) = _
  exact gaScalarTensorBialgEquiv_symm_ι (k := k) (K := K) s

end GaCoordinateBialgebra

end CoordinateBialgebra

/-- The `A`-points of the base change `K ⊗[k] SymmetricAlgebra k M` of the vector group on
`M` are the additive monoid of `k`-linear maps `M →ₗ[k] A`.

The source is the convolution monoid of `K`-algebra maps out of the base-changed bialgebra;
the target is written multiplicatively as `Multiplicative (M →ₗ[k] A)` to match `≃*`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A) ≃* Multiplicative (M →ₗ[k] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (A := SymmetricAlgebra k M) (R := A)).symm.trans
    (pointsMulEquiv (R := k) (M := M) (A := A))

/-- The base-changed vector-group points equivalence reads a point by evaluating it on the
base-changed generator `1 ⊗ ι(m)`. -/
@[simp]
theorem toAdd_baseChangePointsMulEquiv_apply
    (F : WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A)) (m : M) :
    Multiplicative.toAdd (baseChangePointsMulEquiv F) m =
      F.ofConv (1 ⊗ₜ[k] ι k M m) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, toAdd_pointsMulEquiv_apply,
    AlgHom.baseChangePointsMulEquiv_symm_apply]

/-- The inverse base-changed vector-group points equivalence evaluates scalar multiples of
base-changed generators by scalar multiplication of the corresponding linear-map value. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_ι
    (φ : Multiplicative (M →ₗ[k] A)) (s : K) (m : M) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ).ofConv
        (s ⊗ₜ[k] ι k M m) =
      s • (Multiplicative.toAdd φ m) := by
  simp [baseChangePointsMulEquiv, pointsMulEquiv_symm_apply]

/-- The inverse base-changed vector-group points equivalence takes the generator indexed by
`m` to the value of the chosen linear map at `m`. -/
theorem baseChangePointsMulEquiv_symm_apply_ι
    (φ : Multiplicative (M →ₗ[k] A)) (m : M) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ).ofConv
        (1 ⊗ₜ[k] ι k M m) =
      Multiplicative.toAdd φ m := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_ι]
  simp

section Ga

variable {A : Type w} [CommSemiring A]
variable [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The base-changed one-dimensional additive group `𝔾ₐ` has `A`-points the additive monoid
of the value algebra `A`. -/
noncomputable def gaBaseChangePointsMulEquiv :
    WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A) ≃* Multiplicative A :=
  (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := k)).trans
    (AddEquiv.toMultiplicative (LinearMap.ringLmapEquivSelf k k A).toAddEquiv)

/-- The base-changed `𝔾ₐ` points equivalence reads a point by evaluating it on
`1 ⊗ ι(1)`. -/
@[simp]
theorem toAdd_gaBaseChangePointsMulEquiv
    (F : WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A)) :
    Multiplicative.toAdd (gaBaseChangePointsMulEquiv F) =
      F.ofConv (1 ⊗ₜ[k] ι k k 1) := by
  rw [gaBaseChangePointsMulEquiv]
  simp

/-- The inverse base-changed `𝔾ₐ` points equivalence takes the generator `1 ⊗ ι(1)` to the
chosen value. -/
@[simp]
theorem gaBaseChangePointsMulEquiv_symm_apply_ι (a : Multiplicative A) :
    ((gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm a).ofConv
        (1 ⊗ₜ[k] ι k k 1) =
      Multiplicative.toAdd a := by
  rw [gaBaseChangePointsMulEquiv, MulEquiv.symm_trans_apply,
    baseChangePointsMulEquiv_symm_apply_ι]
  simp

end Ga

end AdditiveGroup

end TauCeti
