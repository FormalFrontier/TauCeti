/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import TauCeti.Algebra.Bialgebra.TensorProduct

/-!
# Comultiplication as a convolution product

Let `C` be an `R`-algebra carrying a comultiplication. This file records that, in the convolution
monoid of linear maps `C →ₗ[R] C ⊗[R] C`, comultiplication is the convolution product of the two
canonical inclusions `c ↦ c ⊗ₜ 1` and `c ↦ 1 ⊗ₜ c` of `C` into its tensor square.

The file also provides the exterior convolution product `LinearMap.mulTensor`: linear maps
out of modules `M` and `N`, valued in an algebra, applied legwise on `M ⊗[R] N` and
multiplied in the codomain. Its normalization rules (zero, addition, scalars) and its
multiplicativity for the convolution product make it the engine for composition-level
convolution calculations: convolution products interleave legwise, and composing with a
multiplication lands in the image of `mulTensor` for maps with a suitable multiplicativity
law. This file proves that for an **algebra map**
(`AlgHom.toConv_toLinearMap_comp_mul'`); the Leibniz-rule counterpart for counit-valued
derivations is in `TauCeti/Algebra/AlgebraicGroup/Tangent/Basic.lean`.

## Main declarations

* `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight`: comultiplication as the
  convolution product of the two tensor inclusions.
* `TauCeti.Bialgebra.comulPoint_eq_include_mul`: the corresponding identity for the
  algebra-hom points of a commutative bialgebra.
* `TauCeti.Bialgebra.toConv_comp_comulAlgHom`: the functorial form of the previous identity,
  after post-composing with an arbitrary algebra map out of the tensor square.
* `TauCeti.LinearMap.mulTensor`: the exterior convolution product, with its
  normalization rules and `TauCeti.LinearMap.mulTensor_convMul`.
* `TauCeti.AlgHom.toConv_toLinearMap_comp_mul'`: an algebra map composed with
  multiplication is its own exterior square.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace Coalgebra

variable {R : Type*} {C : Type*} [CommSemiring R] [Semiring C] [Algebra R C]
  [_root_.CoalgebraStruct R C]

/-- **Comultiplication is the convolution product of the two tensor inclusions.** In the
convolution monoid of maps `C →ₗ[R] C ⊗[R] C`, the product of `includeLeft` and `includeRight`
multiplies the two legs of `Δ c` back together in order, which is `Δ` itself.

Only the comultiplication *data* is used, so this needs `CoalgebraStruct` rather than
`Coalgebra`: no coalgebra law, bialgebra compatibility or antipode axiom enters. -/
theorem comul_eq_convMul_includeLeft_includeRight :
    (toConv (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) : WithConv (C →ₗ[R] C ⊗[R] C)) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap *
        toConv (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap := by
  apply WithConv.ofConv_injective
  have hmul : LinearMap.mul' R (C ⊗[R] C) ∘ₗ
      TensorProduct.map
        (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap
        (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap =
      LinearMap.id := by
    -- Mathlib's `lmul'_comp_map` requires a commutative target algebra, whereas `C ⊗[R] C`
    -- is only a semiring here. `lift_includeLeft_includeRight` computes the same pure tensors,
    -- but identifying this linear composite still requires tensor-product extensionality.
    apply TensorProduct.ext
    ext x y
    simp
  simp only [LinearMap.convMul_def]
  rw [← LinearMap.comp_assoc, hmul]
  simp

end Coalgebra

namespace Bialgebra

variable {R : Type*} [CommSemiring R]

section Semiring

variable {H : Type*} [Semiring H] [_root_.Bialgebra R H]

/-- **Post-composition splits the comultiplication point into its two inclusions.** For any
algebra map `φ` out of the tensor square, the point `φ ∘ Δ` is the convolution product of `φ`
restricted along the two inclusions.

The convolution monoid here is the one on points of `H` with values in the *commutative* algebra
`A`, so `H` itself need only be a semiring: the tensor square `H ⊗[R] H` is used solely as the
source of `φ`, never as a convolution target. That is why this is proved from the linear-map
identity `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight` rather than from
`TauCeti.Bialgebra.comulPoint_eq_include_mul`, which needs `H ⊗[R] H` to be commutative. -/
theorem toConv_comp_comulAlgHom {A : Type*} [CommSemiring A] [Algebra R A]
    (phi : H ⊗[R] H →ₐ[R] A) :
    toConv (phi.comp (Bialgebra.comulAlgHom R H)) =
      toConv (phi.comp (Bialgebra.TensorProduct.includeLeft
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom) *
      toConv (phi.comp (Bialgebra.TensorProduct.includeRight
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom) := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]
  have hcomul :
      (Bialgebra.comulAlgHom R H).toLinearMap =
        (toConv (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := H)).toLinearMap *
          toConv (Algebra.TensorProduct.includeRight
            (R := R) (A := H) (B := H)).toLinearMap).ofConv := by
    rw [← Coalgebra.comul_eq_convMul_includeLeft_includeRight (R := R) (C := H)]
    simp
  simp only [AlgHom.comp_toLinearMap, Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom, hcomul]
  exact congrArg WithConv.toConv (LinearMap.algHom_comp_convMul_distrib phi _ _)

end Semiring

variable {H : Type*} [CommSemiring H] [_root_.Bialgebra R H]

/-- The comultiplication point of a commutative bialgebra is the convolution product of the
two canonical tensor-factor points. This is the algebra-hom form of
`Coalgebra.comul_eq_convMul_includeLeft_includeRight`. -/
theorem comulPoint_eq_include_mul :
    toConv (Bialgebra.comulAlgHom R H) =
      toConv (Bialgebra.TensorProduct.includeLeft
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
      toConv (Bialgebra.TensorProduct.includeRight
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]
  simpa only [Bialgebra.toLinearMap_comulAlgHom,
    Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom] using
      (Coalgebra.comul_eq_convMul_includeLeft_includeRight (R := R) (C := H))

end Bialgebra


section ExteriorProduct

open WithConv TensorProduct

variable {R M N S : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Semiring S] [Algebra R S]

namespace LinearMap



/-- The exterior convolution product on `M ⊗[R] N`: apply one factor on each tensor
leg and multiply the results in the coefficients. It underlies the Leibniz-rule
manipulations for counit-valued derivations: composing with the multiplication of the
bialgebra lands in this product's image (there at `N = M`). -/
def mulTensor (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    WithConv (M ⊗[R] N →ₗ[R] S) :=
  toConv (LinearMap.mul' R S ∘ₗ map s.ofConv t.ofConv)

/-- The exterior product evaluates a pure tensor legwise and multiplies the results
in the coefficients. -/
@[simp]
lemma mulTensor_apply_tmul
    (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) (x : M) (y : N) :
    (mulTensor s t).ofConv (x ⊗ₜ[R] y) = s.ofConv x * t.ofConv y := by
  simp [mulTensor]


/-- The exterior product vanishes when the left factor is zero. -/
@[simp]
lemma mulTensor_zero_left (t : WithConv (N →ₗ[R] S)) :
    mulTensor (0 : WithConv (M →ₗ[R] S)) t = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product vanishes when the right factor is zero. -/
@[simp]
lemma mulTensor_zero_right (s : WithConv (M →ₗ[R] S)) :
    mulTensor s (0 : WithConv (N →ₗ[R] S)) = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product is additive in the left factor. -/
@[simp]
lemma mulTensor_add_left (s₁ s₂ : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (s₁ + s₂) t = mulTensor s₁ t + mulTensor s₂ t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [add_mul]

/-- The exterior product is additive in the right factor. -/
@[simp]
lemma mulTensor_add_right (s : WithConv (M →ₗ[R] S)) (t₁ t₂ : WithConv (N →ₗ[R] S)) :
    mulTensor s (t₁ + t₂) = mulTensor s t₁ + mulTensor s t₂ := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [mul_add]

/-- Scalars pull out of the left factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_left (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (r • s) t = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- Scalars pull out of the right factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_right (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor s (r • t) = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

end LinearMap

namespace AlgHom

variable {A : Type*} [Semiring A] [Algebra R A]

open TauCeti.LinearMap in
/-- An algebra-map point composed with multiplication is its own exterior square:
the multiplicativity of the point, in convolution form. -/
@[simp]
lemma toConv_toLinearMap_comp_mul' (g : A →ₐ[R] S) :
    toConv (g.toLinearMap ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv g.toLinearMap) (toConv g.toLinearMap) := by
  -- Not a re-derivation: this is Mathlib's `AlgHom.comp_mul'` transported into the file's
  -- own `mulTensor` vocabulary, which is what consumers rewrite with.
  exact congrArg toConv (AlgHom.comp_mul' g)

end AlgHom

end ExteriorProduct

section ExteriorConvolution

open WithConv TensorProduct

variable {R C D S : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
  [AddCommMonoid D] [Module R D] [CoalgebraStruct R D]
  [CommSemiring S] [Algebra R S]

namespace LinearMap

/-- The exterior product is multiplicative for convolution: products interleave
legwise. Only the comultiplication *data* on each leg is used — no multiplication on the
sources and no bialgebra compatibility — so the two legs may be distinct coalgebras. -/
@[simp]
lemma mulTensor_convMul
    (s u : WithConv (C →ₗ[R] S)) (t v : WithConv (D →ₗ[R] S)) :
    mulTensor s t * mulTensor u v = mulTensor (s * u) (t * v) := by
  have h := LinearMap.algHom_comp_convMul_distrib
    (Algebra.TensorProduct.lmul' R (S := S))
    (toConv (map s.ofConv t.ofConv)) (toConv (map u.ofConv v.ofConv))
  rw [map_convMul_map] at h
  -- The commutative multiplication algebra map and the plain multiplication linear map
  -- agree; restate `h` in the linear form used by `mulTensor`.
  rw [Algebra.TensorProduct.lmul'_toLinearMap] at h
  calc mulTensor s t * mulTensor u v
      = toConv (LinearMap.mul' R S ∘ₗ map (s * u).ofConv (t * v).ofConv) := by
        rw [mulTensor, mulTensor, ← toConv_ofConv (toConv _ * toConv _), ← h]
    _ = mulTensor (s * u) (t * v) := rfl

end LinearMap

end ExteriorConvolution

end TauCeti
