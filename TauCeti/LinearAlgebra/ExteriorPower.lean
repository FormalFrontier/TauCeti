/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace

/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module, and computes the trace of an induced
endomorphism from a basis of eigenvectors.

It then builds the surjection `exteriorPower.fromTensorPower : ⨂[R]^n M →ₗ[R] ⋀[R]^n M` that is
left inverse, up to the factor `n!`, to Mathlib's antisymmetrization
`exteriorPower.toTensorPower`: composing the antisymmetrization with it is `n! • id` on the exterior
power, while composing the two the other way round is the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. Consequently the antisymmetrization is injective once `n!` is a
unit in the base ring, and its image is the image of that operator. That is the statement a Young
symmetrizer of a one-column shape consumes.

It then describes the exterior power in the top degree, that is, in the degree equal to the rank of
the module. There an exterior product of `n` vectors is the determinant of those vectors against a
fixed basis, times the exterior product of that basis; so the top exterior power is free of rank
one, spanned by the exterior product of a basis, and an endomorphism acts on it by its determinant.

## Main definitions

* `exteriorPower.fromTensorPower` is the canonical surjection of the tensor power onto the
  exterior power.
* `exteriorPower.topEquiv` identifies the top exterior power of a module with the scalars, using a
  basis indexed by `Fin n`.

## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.
* `exteriorPower.trace_map_of_apply_basis` computes the trace on `⋀[R]^d M` from the
  eigenvalues of an endomorphism on a finite basis.
* `exteriorPower.ιMulti_eq_basis_det_smul` expands a top-degree exterior product of vectors in
  terms of the exterior product of a basis.
* `exteriorPower.map_top_eq_det_smul` says an endomorphism acts on the top exterior power as
  multiplication by its determinant, and `exteriorPower.trace_map_top` computes the resulting
  trace.
* `exteriorPower.fromTensorPower_comp_toTensorPower`: antisymmetrizing and projecting back is
  multiplication by `n!`, whence `exteriorPower.toTensorPower_injective`.
* `exteriorPower.range_toTensorPower`: the image of the antisymmetrization is the image of the
  antisymmetrization operator on the tensor power.
* `exteriorPower.toTensorPower_comp_map` and `exteriorPower.map_comp_fromTensorPower`: the
  antisymmetrization and the canonical surjection are natural in the module.

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison, and the
determinant of a family of vectors against a basis from `Mathlib.LinearAlgebra.Determinant`.
-/

public section

open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Trace

variable [CommRing R]
variable {I : Type*} [Fintype I]
variable [AddCommGroup M] [Module R M]

/-- If an endomorphism is diagonal in a finite basis, then its trace on the `d`th exterior
power is the `d`th elementary symmetric sum of its eigenvalues. -/
theorem trace_map_of_apply_basis (b : Module.Basis I R M) (f : M →ₗ[R] M)
    (a : I → R) (d : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (⋀[R]^d M) (map d f) =
      ∑ s : Set.powersetCard I d, ∏ i ∈ (s : Finset I), a i := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let B := b.exteriorPower d
  rw [LinearMap.trace_eq_matrix_trace R B, Matrix.trace]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [B, basis_apply]
  rw [map_apply_ιMulti_family, basis_repr_apply]
  have hmap :
      ιMulti_family R d (f ∘ b) s =
        (∏ j : Fin d, a (Set.powersetCard.ofFinEmbEquiv.symm s j)) •
          ιMulti_family R d b s := by
    rw [ιMulti_family, ιMulti_family]
    have hfun :
        (f ∘ b) ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
          fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j) •
            b (Set.powersetCard.ofFinEmbEquiv.symm s j) := by
      funext j
      simp only [Function.comp_apply, hf]
    have hbfun :
        b ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
          fun j => b (Set.powersetCard.ofFinEmbEquiv.symm s j) := rfl
    rw [hfun]
    rw [hbfun]
    simpa only [Function.comp_apply] using
      (ιMulti R d).map_smul_univ
        (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j))
        (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm s j))
  rw [hmap, map_smul, ιMultiDual_apply_diag, smul_eq_mul, mul_one]
  rw [← Finset.prod_coe_sort s.1 a]
  apply Fintype.prod_equiv (s.1.orderIsoOfFin s.2).toEquiv
  intro j
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact congrArg a (Finset.coe_orderIsoOfFin_apply s.1 s.2 j)

end Trace

section Vanishing

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Module.subsingleton R _
    · rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
      exact h
  exact Subsingleton.elim x 0

end Vanishing

/-! ### The exterior power as a quotient of the tensor power -/

section FromTensorPower

variable [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)

variable (R M) in
/-- **The canonical surjection of the tensor power onto the exterior power**, sending a pure
tensor to the corresponding exterior product.

Mathlib's `exteriorPower.toTensorPower` runs the other way, by antisymmetrization; antisymmetrizing
and then projecting back is `n!` on the exterior power, while projecting and then antisymmetrizing
is the antisymmetrization operator `∑_σ sgn(σ) σ` on the tensor power. -/
noncomputable def fromTensorPower : (⨂[R]^n M) →ₗ[R] ⋀[R]^n M :=
  PiTensorProduct.lift (ιMulti R n).toMultilinearMap

@[simp]
theorem fromTensorPower_tprod (m : Fin n → M) :
    fromTensorPower R M n (PiTensorProduct.tprod R m) = ιMulti R n m :=
  PiTensorProduct.lift.tprod m

theorem fromTensorPower_surjective : Function.Surjective (fromTensorPower R M n) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod R v, fromTensorPower_tprod n v⟩

/-- Antisymmetrizing an exterior product and projecting it back multiplies by `n!`: each of the
`n!` signed reorderings returns the same exterior product. -/
@[simp]
theorem fromTensorPower_comp_toTensorPower :
    (fromTensorPower R M n) ∘ₗ (toTensorPower R M n) =
      n.factorial • LinearMap.id (R := R) (M := ⋀[R]^n M) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) * ((Equiv.Perm.sign σ : ℤ)) = 1 := fun σ => by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have h : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) • ιMulti R n (fun i => v (σ i)) = ιMulti R n v := fun σ => by
    rw [← Function.comp_def v σ, (ιMulti R n).map_perm, Units.smul_def, smul_smul, hsq, one_smul]
  rw [LinearMap.coe_comp, Function.comp_apply, toTensorPower_apply_ιMulti, map_sum]
  simp only [Units.smul_def, map_zsmul, fromTensorPower_tprod, h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- The antisymmetrization is injective as soon as `n!` is a unit in the base ring, for instance
over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit (n.factorial : R)) :
    Function.Injective (toTensorPower R M n) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the canonical surjection by `u⁻¹` makes it a left inverse of the antisymmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • fromTensorPower R M n) ?_
  rw [LinearMap.smul_comp, fromTensorPower_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, ← hu, u.inv_mul, one_smul]

/-- Projecting a tensor to the exterior power and antisymmetrizing it back is the
antisymmetrization operator `∑_σ sgn(σ) σ` of the tensor power. -/
theorem toTensorPower_comp_fromTensorPower :
    (toTensorPower R M n) ∘ₗ (fromTensorPower R M n) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, Function.comp_apply, fromTensorPower_tprod,
    toTensorPower_apply_ιMulti, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
  simp [Units.smul_def, Equiv.Perm.inv_def]

/-- The antisymmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R N n) ∘ₗ (map n f) =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (toTensorPower R M n) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  simp [Units.smul_def, Function.comp_def]

/-- The canonical surjection is natural in the module. -/
theorem map_comp_fromTensorPower {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (map n f) ∘ₗ (fromTensorPower R M n) =
      (fromTensorPower R N n) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [Function.comp_def]

/-- The image of the antisymmetrization is the image of the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R M n) =
      LinearMap.range (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap) := by
  rw [← toTensorPower_comp_fromTensorPower, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (fromTensorPower_surjective n), Submodule.map_top]

end FromTensorPower

section Top

variable [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- In the top degree, an exterior product of `n` vectors is the determinant of that family
against a basis, times the exterior product of the basis. -/
theorem ιMulti_eq_basis_det_smul (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    ιMulti R n v = b.det v • ιMulti R n ⇑b := by
  -- Compare both sides coordinatewise in the basis of `⋀[R]^n M` induced by `b`: each coordinate
  -- is an `R`-valued alternating form, hence a multiple of `b.det`.
  refine (b.exteriorPower n).ext_elem fun s ↦ ?_
  -- The `s`th coordinate of `ιMulti R n v` is an alternating form in `v`.
  set φ : M [⋀^Fin n]→ₗ[R] R := (ιMultiDual R n b s).compAlternatingMap (ιMulti R n) with hφ
  have hφ_apply (w : Fin n → M) :
      φ w = (b.exteriorPower n).repr (ιMulti R n w) s := by
    rw [hφ, basis_repr_apply, LinearMap.compAlternatingMap_apply]
  have hdet : φ = φ ⇑b • b.det := φ.eq_smul_basis_det b
  calc (b.exteriorPower n).repr (ιMulti R n v) s
      = φ v := (hφ_apply v).symm
    _ = φ ⇑b * b.det v := by rw [hdet]; simp [Module.Basis.det_self]
    _ = b.det v * (b.exteriorPower n).repr (ιMulti R n ⇑b) s := by
        rw [← hφ_apply ⇑b, mul_comm]
    _ = (b.exteriorPower n).repr (b.det v • ιMulti R n ⇑b) s := by simp

/-- **An endomorphism acts on the top exterior power as multiplication by its determinant.** -/
theorem map_top_eq_det_smul (b : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) :
    map n f = LinearMap.det f • LinearMap.id := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  rw [map_apply_ιMulti, ιMulti_eq_basis_det_smul b (f ∘ v), ιMulti_eq_basis_det_smul b v,
    Module.Basis.det_comp, mul_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]

/-- The basis-free form of `exteriorPower.map_top_eq_det_smul`: on the exterior power in the degree
equal to the rank, an endomorphism of a finite free module acts by its determinant. -/
@[simp]
theorem map_finrank_eq_det_smul [Nontrivial R] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    map (Module.finrank R M) f = LinearMap.det f • LinearMap.id :=
  map_top_eq_det_smul (Module.finBasis R M) f

/-- The top exterior power of a module with a basis indexed by `Fin n` is free of rank one: it is
identified with the scalars by sending an exterior product of vectors to their determinant against
the basis. -/
noncomputable def topEquiv (b : Module.Basis (Fin n) R M) : ⋀[R]^n M ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R (⋀[R]^n M) (ιMulti R n ⇑b))
    (by
      ext
      simp [Module.Basis.det_self])
    (by
      refine LinearMap.ext_on (ιMulti_span R n M) ?_
      rintro _ ⟨v, rfl⟩
      simp [ιMulti_eq_basis_det_smul b v, Module.Basis.det_self])

@[simp]
lemma topEquiv_apply_ιMulti (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    topEquiv b (ιMulti R n v) = b.det v := by
  simp [topEquiv]

@[simp]
lemma topEquiv_symm_apply (b : Module.Basis (Fin n) R M) (r : R) :
    (topEquiv b).symm r = r • ιMulti R n ⇑b := by
  simp [topEquiv]

/-- The trace of the induced endomorphism of the top exterior power is the determinant. -/
theorem trace_map_top [Nontrivial R] (b : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) :
    LinearMap.trace R (⋀[R]^n M) (map n f) = LinearMap.det f := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  -- The top exterior power is one-dimensional, the diagonal case `Nat.choose n n = 1`.
  rw [map_top_eq_det_smul b f, map_smul, LinearMap.trace_id, finrank_eq,
    Module.finrank_eq_card_basis b, Fintype.card_fin, Nat.choose_self]
  simp

end Top

end exteriorPower
