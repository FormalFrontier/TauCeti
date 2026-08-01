/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The monoid algebra of a product is the tensor product of monoid algebras

For two monoids `G` and `H`, the canonical map `single (g, h) 1 ↦ single g 1 ⊗ₜ
single h 1` is an isomorphism of `R`-bialgebras `R[G × H] ≃ₐc[R] R[G] ⊗[R] R[H]`.

The bialgebra isomorphism is promoted from the standard algebra maps: the lift of the group-like
monoid hom `(g, h) ↦ single g 1 ⊗ₜ single h 1` one way, and the tensor-product universal map of
the two inclusions `R[G] → R[G × H]`, `R[H] → R[G × H]` (themselves
`MonoidAlgebra.mapDomainAlgHom` of `MonoidHom.inl`/`MonoidHom.inr`) the other way. The public
API keeps only the bialgebra equivalence and its generator formulas.

This is generic monoid-algebra API used by the diagonalizable-group product calculation.

## Main definitions

* `TauCeti.MonoidAlgebra.prodTensorBialgEquiv`: the bialgebra isomorphism
  `R[G × H] ≃ₐc[R] R[G] ⊗[R] R[H]`.

## References

The tensor-product bialgebra structure and `Algebra.TensorProduct.lift` are from Mathlib's
`Mathlib.RingTheory.Bialgebra.TensorProduct` and `Mathlib.RingTheory.TensorProduct.Maps`; the
monoid-algebra bialgebra structure and `MonoidAlgebra.mapDomainAlgHom` are from
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra` and `Mathlib.Algebra.MonoidAlgebra.Basic`.
-/

public section

open TensorProduct MonoidAlgebra

namespace TauCeti

universe u v w

namespace MonoidAlgebra

variable (R : Type u) [CommSemiring R]
variable {G : Type v} {H : Type w} [Monoid G] [Monoid H]

/-- The group-like monoid homomorphism `(g, h) ↦ single g 1 ⊗ₜ single h 1` from `G × H` into the
multiplicative monoid of `R[G] ⊗[R] R[H]`. -/
private noncomputable def prodGroupLike :
    G × H →* MonoidAlgebra R G ⊗[R] MonoidAlgebra R H where
  toFun p := single p.1 (1 : R) ⊗ₜ[R] single p.2 1
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, ← MonoidAlgebra.one_def,
      Algebra.TensorProduct.one_def]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Algebra.TensorProduct.tmul_mul_tmul,
      single_mul_single, mul_one]

@[simp]
private theorem prodGroupLike_apply (g : G) (h : H) :
    prodGroupLike R (g, h) = single g (1 : R) ⊗ₜ[R] single h 1 := rfl

/-- The forward algebra map `R[G × H] →ₐ[R] R[G] ⊗[R] R[H]`, sending `single (g, h) 1` to
`single g 1 ⊗ₜ single h 1`. -/
private noncomputable def prodTensorAlgHom :
    MonoidAlgebra R (G × H) →ₐ[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  lift R (MonoidAlgebra R G ⊗[R] MonoidAlgebra R H) (G × H) (prodGroupLike R)

@[simp]
private theorem prodTensorAlgHom_single (g : G) (h : H) :
    prodTensorAlgHom R (single (g, h) (1 : R)) = single g 1 ⊗ₜ[R] single h 1 := by
  simp only [prodTensorAlgHom, lift_single, one_smul, prodGroupLike_apply]

/-- The images of the two inclusions `R[G] → R[G × H]` and `R[H] → R[G × H]` commute. -/
private theorem commute_mapDomainAlgHom_inl_inr (x : MonoidAlgebra R G) (y : MonoidAlgebra R H) :
    Commute (mapDomainAlgHom R R (MonoidHom.inl G H) x)
      (mapDomainAlgHom R R (MonoidHom.inr G H) y) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      simp only [of_apply, mapDomainAlgHom_apply, mapDomain_single, MonoidHom.inl_apply,
        MonoidHom.inr_apply, commute_iff_eq, single_mul_single, Prod.mk_mul_mk, mul_one, one_mul]
    | add y₁ y₂ hy₁ hy₂ => rw [map_add]; exact hy₁.add_right hy₂
    | smul r y hy => rw [map_smul]; exact hy.smul_right r
  | add x₁ x₂ hx₁ hx₂ => rw [map_add]; exact hx₁.add_left hx₂
  | smul r x hx => rw [map_smul]; exact hx.smul_left r

/-- The inverse algebra map `R[G] ⊗[R] R[H] →ₐ[R] R[G × H]`, the tensor-product universal map of
the two inclusions `R[G] → R[G × H]` and `R[H] → R[G × H]`. -/
private noncomputable def tensorProdAlgHom :
    MonoidAlgebra R G ⊗[R] MonoidAlgebra R H →ₐ[R] MonoidAlgebra R (G × H) :=
  Algebra.TensorProduct.lift
    (mapDomainAlgHom R R (MonoidHom.inl G H) :
      MonoidAlgebra R G →ₐ[R] MonoidAlgebra R (G × H))
    (mapDomainAlgHom R R (MonoidHom.inr G H) :
      MonoidAlgebra R H →ₐ[R] MonoidAlgebra R (G × H))
    (commute_mapDomainAlgHom_inl_inr R)

@[simp]
private theorem tensorProdAlgHom_tmul_single (g : G) (h : H) :
    tensorProdAlgHom R (single g (1 : R) ⊗ₜ[R] single h 1) = single (g, h) 1 := by
  simp only [tensorProdAlgHom, Algebra.TensorProduct.lift_tmul, mapDomainAlgHom_apply,
    mapDomain_single, single_mul_single, MonoidHom.inl_apply, MonoidHom.inr_apply,
    Prod.mk_mul_mk, mul_one, one_mul]

private noncomputable def prodTensorAlgEquiv :
    MonoidAlgebra R (G × H) ≃ₐ[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  AlgEquiv.ofAlgHom (prodTensorAlgHom R) (tensorProdAlgHom R)
    (by
      apply Algebra.TensorProduct.ext
      · apply MonoidAlgebra.algHom_ext
        · intro g
          simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply]
          rw [one_def, tensorProdAlgHom_tmul_single, prodTensorAlgHom_single]
        · ext
      · apply MonoidAlgebra.algHom_ext
        · intro h
          simp only [AlgHom.coe_restrictScalars', AlgHom.comp_apply, AlgHom.id_apply,
            Algebra.TensorProduct.includeRight_apply]
          rw [one_def, tensorProdAlgHom_tmul_single, prodTensorAlgHom_single]
        · ext)
    (by
      apply MonoidAlgebra.algHom_ext
      · rintro ⟨g, h⟩
        rw [AlgHom.comp_apply, prodTensorAlgHom_single, tensorProdAlgHom_tmul_single,
          AlgHom.id_apply]
      · ext)

@[simp]
private theorem prodTensorAlgEquiv_single (g : G) (h : H) :
    prodTensorAlgEquiv R (single (g, h) (1 : R)) = single g 1 ⊗ₜ[R] single h 1 :=
  prodTensorAlgHom_single R g h

@[simp]
private theorem prodTensorAlgEquiv_symm_tmul_single (g : G) (h : H) :
    (prodTensorAlgEquiv R).symm (single g (1 : R) ⊗ₜ[R] single h 1) = single (g, h) 1 := by
  rw [← prodTensorAlgEquiv_single R g h, AlgEquiv.symm_apply_apply]

/-- **The monoid algebra of a product is the tensor product of monoid algebras**, as a bialgebra
isomorphism. -/
noncomputable def prodTensorBialgEquiv :
    MonoidAlgebra R (G × H) ≃ₐc[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  BialgEquiv.ofAlgEquiv (prodTensorAlgEquiv R)
    (by
      apply MonoidAlgebra.algHom_ext
      · rintro ⟨g, h⟩
        simp
      · ext)
    (by
      apply MonoidAlgebra.algHom_ext
      · rintro ⟨g, h⟩
        simp
      · ext)

/-- The forward product bialgebra equivalence sends the generator indexed by `(g, h)` to the
pure tensor of the two factor generators. -/
@[simp]
theorem prodTensorBialgEquiv_single (g : G) (h : H) :
    prodTensorBialgEquiv R (single (g, h) (1 : R)) = single g 1 ⊗ₜ[R] single h 1 :=
  prodTensorAlgEquiv_single R g h

/-- The inverse product bialgebra equivalence sends a pure tensor of factor generators to the
generator indexed by their product pair. -/
@[simp]
theorem prodTensorBialgEquiv_symm_tmul_single (g : G) (h : H) :
    (prodTensorBialgEquiv R).symm (single g (1 : R) ⊗ₜ[R] single h 1) = single (g, h) 1 := by
  rw [← prodTensorBialgEquiv_single R g h, BialgEquiv.symm_apply_apply]

end MonoidAlgebra

end TauCeti
