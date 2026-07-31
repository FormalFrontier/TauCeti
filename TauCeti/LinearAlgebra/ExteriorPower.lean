/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace

/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module, and computes the trace of an induced
endomorphism from a basis of eigenvectors.

It then describes the exterior power in the top degree, that is, in the degree equal to the rank of
the module. There an exterior product of `n` vectors is the determinant of those vectors against a
fixed basis, times the exterior product of that basis; so the top exterior power is free of rank
one, spanned by the exterior product of a basis, and an endomorphism acts on it by its determinant.

## Main definitions

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

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison, and the
determinant of a family of vectors against a basis from `Mathlib.LinearAlgebra.Determinant`.
-/

public section

open scoped BigOperators

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
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
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
  LinearEquiv.ofLinear (alternatingMapLinearEquiv b.det)
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
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  -- The top exterior power is one-dimensional, the diagonal case `Nat.choose n n = 1`.
  rw [map_top_eq_det_smul b f, map_smul, LinearMap.trace_id, finrank_eq,
    Module.finrank_eq_card_basis b, Fintype.card_fin, Nat.choose_self]
  simp

end Top

end exteriorPower
