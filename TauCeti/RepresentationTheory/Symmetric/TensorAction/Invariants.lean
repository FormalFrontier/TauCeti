/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.LinearAlgebra.Multilinear.Polarization
public import TauCeti.LinearAlgebra.SymmetricPower.Basic
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-!
# The symmetric tensors are spanned by the pure powers

The symmetric group of `ι` acts on the tensor power `⨂[R] (_ : ι), M` by permuting the factors.
This file identifies the invariants of that action, once `(#ι)!` is invertible in `R`: they are
exactly the span of the **pure powers** `⨂ₜ i, x`, the tensors with the same vector in every slot.

The engine is the polarization identity
`PiTensorProduct.sum_neg_one_pow_card_smul_tprod_sum_compl`, which writes the full symmetrization
of a pure tensor as an alternating sum of pure powers and needs no invertibility. Dividing by
`(#ι)!` then turns the symmetrization into a projection onto the invariants: an invariant tensor is
the average of its own orbit, so it lies in the span of the pure powers.

This is the spanning half of the double centralizer in Schur-Weyl duality. There `ι` is finite and
`V` is a finite free module, so that the canonical map `(End V)^{⊗ι} → End (V^{⊗ι})` is an
isomorphism; the results below need neither hypothesis on `M`. Under that identification the
endomorphisms commuting with the factor permutations are the invariants of the permutation action
on `(End V)^{⊗ι}`, and this file says they are spanned by the pure powers `f^{⊗ι}` — the diagonal
operators through which the general linear group acts.

## Main results

* `PiTensorProduct.invariants_reindexRepresentation`: the invariants of the permutation action on
  the tensor power are the span of the pure powers, when `(#ι)!` is invertible.
* `PiTensorProduct.range_sum_reindexRepresentation`: the symmetrization operator has that same
  span as its range.
* `SymmetricPower.range_toTensorPower_eq_span`: consequently the symmetric power sits inside the
  tensor power as the span of the pure powers.
* `TauCeti.invariants_permTensorAction` and `TauCeti.range_permTensorActionAlgHom_sum_single`: the
  statement specialized to the `S_d`-action on `(Rⁿ)^{⊗d}`, the setting of Schur-Weyl duality, in
  its invariant-subspace and its group-algebra-image forms.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, “The double centralizer (image-level)”: the centralizer of the symmetric-group image in
  `End((ℂᵈ)^{⊗n})` is the image of `ℂ[GLₔ]`, whose spanning half is the identification proved here.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6, and Appendix B.1 for
  the polarization argument.
-/

public section

open scoped Nat TensorProduct

universe u v w

namespace PiTensorProduct

section

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- A pure power `⨂ₜ i, x` is fixed by every permutation of the tensor factors. -/
theorem tprod_const_mem_invariants (x : M) :
    (⨂ₜ[R] (_ : ι), x) ∈ (reindexRepresentation R M ι).invariants := by
  intro σ
  rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod]

end

section

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- Symmetrizing any tensor lands in the span of the pure powers. -/
theorem sum_reindexRepresentation_mem_span (y : ⨂[R] _ : ι, M) :
    ∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ y ∈
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  classical
  have hy : y ∈ (⊤ : Submodule R (⨂[R] _ : ι, M)) := Submodule.mem_top
  rw [← span_tprod_eq_top] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have hperm : ∀ σ : Equiv.Perm ι, reindexRepresentation R M ι σ (tprod R m) =
        ⨂ₜ[R] i, m (σ⁻¹ i) := by
      intro σ
      rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod]
      rfl
    have hinv : (∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ⁻¹ i)) =
        ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) :=
      Equiv.sum_comp (Equiv.inv (Equiv.Perm ι)) fun σ => ⨂ₜ[R] i, m (σ i)
    rw [Finset.sum_congr rfl fun σ _ => hperm σ, hinv,
      ← sum_neg_one_pow_card_smul_tprod_sum_compl]
    exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, rfl⟩)
  | zero => simp
  | add z z' hz hz' ihz ihz' => simpa [Finset.sum_add_distrib] using Submodule.add_mem _ ihz ihz'
  | smul r z hz ihz => simpa [← Finset.smul_sum] using Submodule.smul_mem _ r ihz

/-- **The symmetrization operator has the symmetric tensors as its range.** The range of `∑_σ σ` is
the span of the pure powers; the operator scales an invariant tensor by `(#ι)!`, so it is the
projection onto that span only up to that factor. -/
theorem range_sum_reindexRepresentation (h : IsUnit ((Fintype.card ι)! : R)) :
    LinearMap.range (∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ) =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  let := h.invertible
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro _ ⟨y, rfl⟩
    simpa [LinearMap.sum_apply] using sum_reindexRepresentation_mem_span y
  · rintro _ ⟨x, rfl⟩
    have hfix : ∀ σ : Equiv.Perm ι,
        reindexRepresentation R M ι σ (⨂ₜ[R] (_ : ι), x) = ⨂ₜ[R] (_ : ι), x := fun σ => by simp
    refine ⟨⅟((Fintype.card ι)! : R) • (⨂ₜ[R] (_ : ι), x), ?_⟩
    rw [map_smul, LinearMap.sum_apply, Finset.sum_congr rfl fun σ _ => hfix σ,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul R, smul_smul,
      invOf_mul_self, one_smul]

end

section

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/-- **The symmetric tensors are the span of the pure powers.** When `(#ι)!` is invertible in `R`,
the invariants of the permutation action on `⨂[R] (_ : ι), M` are spanned by the pure powers
`⨂ₜ i, x`. -/
@[simp]
theorem invariants_reindexRepresentation (h : IsUnit ((Fintype.card ι)! : R)) :
    (reindexRepresentation R M ι).invariants =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  classical
  let := h.invertible
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.mpr ?_)
  · have horbit : ∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ y =
        ((Fintype.card ι)! : R) • y := by
      rw [Finset.sum_congr rfl fun σ _ => hy σ, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, ← Nat.cast_smul_eq_nsmul R]
    have := Submodule.smul_mem _ (⅟((Fintype.card ι)! : R))
      (horbit ▸ sum_reindexRepresentation_mem_span y)
    rwa [smul_smul, invOf_mul_self, one_smul] at this
  · rintro _ ⟨x, rfl⟩
    exact tprod_const_mem_invariants x

end

end PiTensorProduct

namespace SymmetricPower

variable {R : Type u} {M : Type v} {ι : Type u}
variable [CommRing R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- **The symmetric power sits inside the tensor power as the span of the pure powers.** The
symmetrization `SymmetricPower.toTensorPower` has as its image the span of the tensors `⨂ₜ i, x`.

Together with `SymmetricPower.toTensorPower_injective` this presents `Sym[R] ι M` concretely: it
is the subspace of `⨂[R] (_ : ι), M` generated by the pure powers. The index type is confined to
the universe of `R` because `SymmetricPower` is. -/
theorem range_toTensorPower_eq_span (h : IsUnit ((Fintype.card ι)! : R)) :
    LinearMap.range (toTensorPower R ι M) =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  have hsum : (∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap) =
      ∑ σ : Equiv.Perm ι, PiTensorProduct.reindexRepresentation R M ι σ :=
    Finset.sum_congr rfl fun σ _ => (PiTensorProduct.reindexRepresentation_apply R M ι σ).symm
  rw [range_toTensorPower, hsum]
  exact PiTensorProduct.range_sum_reindexRepresentation h

end SymmetricPower

namespace TauCeti

variable {R : Type u} {n d : ℕ} [CommRing R]

/-- **The symmetric tensors in `(Rⁿ)^{⊗d}`.** The invariants of the `S_d`-action permuting the
tensor factors are spanned by the pure powers `⨂ₜ i, x`; this is the spanning half of the
Schur-Weyl double centralizer, read on the tensor power itself. -/
@[simp]
theorem invariants_permTensorAction (h : IsUnit (d ! : R)) :
    (permTensorAction R n d).invariants =
      Submodule.span R (Set.range fun x : Fin n → R => ⨂ₜ[R] (_ : Fin d), x) := by
  rw [permTensorAction_def]
  exact PiTensorProduct.invariants_reindexRepresentation (by rwa [Fintype.card_fin])

/-- **The symmetrizer of `R[S_d]` cuts out the same subspace.** The image of the group-algebra
element `∑_σ σ` acting on `(Rⁿ)^{⊗d}` is the span of the pure powers, hence the invariants: it is
the projection onto them, up to the factor `d!`. This is the Young symmetrizer of a one-row shape,
read at the level of the image subalgebra of `R[S_d]` in which Schur-Weyl duality is stated. -/
theorem range_permTensorActionAlgHom_sum_single (h : IsUnit (d ! : R)) :
    LinearMap.range (permTensorActionAlgHom R n d
        (∑ σ : Equiv.Perm (Fin d), MonoidAlgebra.single σ (1 : R))) =
      Submodule.span R (Set.range fun x : Fin n → R => ⨂ₜ[R] (_ : Fin d), x) := by
  have hsum : permTensorActionAlgHom R n d
        (∑ σ : Equiv.Perm (Fin d), MonoidAlgebra.single σ (1 : R)) =
      ∑ σ : Equiv.Perm (Fin d),
        PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d) σ := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_single, one_smul,
      permTensorAction_def]
  rw [hsum]
  exact PiTensorProduct.range_sum_reindexRepresentation (by rwa [Fintype.card_fin])

end TauCeti
