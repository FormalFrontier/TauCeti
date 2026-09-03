/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Hom
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Invariants

/-!
# The commutant of the permutation action on a tensor power

The symmetric group of `ι` acts on `⨂[R] (_ : ι), M` by permuting the tensor factors, and every
**diagonal** endomorphism `f^{⊗ι} = PiTensorProduct.map (fun _ ↦ f)` commutes with that action
(`PiTensorProduct.commute_reindexRepresentation_map`). This file proves the converse when `M` is
finite free and `(#ι)!` is invertible in `R`: an endomorphism of the tensor power commuting with
all the factor permutations is an `R`-linear combination of diagonal ones.

That is one half of the double centralizer of Schur-Weyl duality, at the level of image
subalgebras: the commutant of the image of `R[S_ι]` in `End (M^{⊗ι})` is the span of the diagonal
operators, through which the general linear group acts.

The proof runs the computation on the other side of the comparison isomorphism
`PiTensorProduct.piTensorHomEquiv`, which identifies `End (M^{⊗ι})` with `(End M)^{⊗ι}`. Under that
identification conjugation by a factor permutation on `End (M^{⊗ι})` becomes the permutation action
on `(End M)^{⊗ι}`, so a commuting endomorphism is an invariant tensor; and the invariants of a
permutation action are the span of the pure powers
(`PiTensorProduct.invariants_reindexRepresentation`), which are exactly the diagonal operators.
Both hypotheses are used once: freeness and finiteness make the comparison map an isomorphism, and
the invertibility of `(#ι)!` is what averaging over the symmetric group needs.

## Main results

* `PiTensorProduct.piTensorHomEquiv_reindexRepresentation_mul`: the comparison isomorphism
  intertwines the permutation action on `(End M)^{⊗ι}` with conjugation by the factor permutations
  on `End (M^{⊗ι})`.
* `PiTensorProduct.mem_span_range_map_const_iff_forall_commute`: **the commutant of the permutation
  action is the span of the diagonal operators.**
* `TauCeti.mem_span_range_map_const_iff_forall_commute_permTensorAction`: the same statement in the
  Schur-Weyl setting `M = Rⁿ`, `ι = Fin d`, where the invertibility hypothesis reads `d !`.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, "The double centralizer (image-level)", whose first half asks for exactly the commutant
  of the symmetric-group image inside `End (V^{⊗n})`. The other half, that the commutant of the
  diagonal operators is the symmetric-group image, is not proved here.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6 and Appendix B.1.
-/

public section

open scoped Nat TensorProduct

namespace PiTensorProduct

universe u v w

section Semiring

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Permuting the factors is invertible: the operators of the permutation representation compose to
the identity along inverse permutations. -/
private theorem reindexRepresentation_mul_inv (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ * reindexRepresentation R M ι σ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

variable [Finite ι] [Module.Free R M] [Module.Finite R M]

/-- **The comparison isomorphism carries a permuted pure tensor to the conjugated map.** This is
the pure-tensor case of `PiTensorProduct.piTensorHomEquiv_reindexRepresentation_mul`, and is
Mathlib's compatibility of `PiTensorProduct.map` with `PiTensorProduct.reindex`. -/
theorem piTensorHomEquiv_reindexRepresentation_tprod_mul (σ : Equiv.Perm ι)
    (f : ι → (M →ₗ[R] M)) :
    piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)
          (reindexRepresentation R (M →ₗ[R] M) ι σ (tprod R f)) *
        reindexRepresentation R M ι σ =
      reindexRepresentation R M ι σ *
        piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M) (tprod R f) := by
  rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod,
    piTensorHomEquiv_tprod, piTensorHomEquiv_tprod, reindexRepresentation_apply,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  exact map_comp_reindex_eq f σ

/-- **The comparison isomorphism intertwines the two actions.** Permuting the factors of a tensor
of endomorphisms is conjugating the corresponding endomorphism of the tensor power by the
permutation of the factors. -/
theorem piTensorHomEquiv_reindexRepresentation_mul (σ : Equiv.Perm ι)
    (x : ⨂[R] _ : ι, M →ₗ[R] M) :
    piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)
          (reindexRepresentation R (M →ₗ[R] M) ι σ x) *
        reindexRepresentation R M ι σ =
      reindexRepresentation R M ι σ *
        piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul, smul_mul_assoc, mul_smul_comm,
      piTensorHomEquiv_reindexRepresentation_tprod_mul]
  | add x y hx hy =>
    rw [map_add, LinearEquiv.map_add, LinearEquiv.map_add, add_mul, mul_add, hx, hy]

end Semiring

section Ring

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  [Module.Free R M] [Module.Finite R M]

/-- **The commutant of the permutation action on a tensor power is the span of the diagonal
operators.** For a finite free module `M` and `(#ι)!` invertible in `R`, an endomorphism of
`⨂[R] (_ : ι), M` commutes with every permutation of the tensor factors exactly when it is an
`R`-linear combination of the operators `f^{⊗ι}` applying one endomorphism `f` in every factor.

One direction is `PiTensorProduct.commute_reindexRepresentation_map`; the substance is the other,
which says that the diagonal operators already exhaust the commutant. -/
theorem mem_span_range_map_const_iff_forall_commute (h : IsUnit ((Fintype.card ι)! : R))
    (T : (⨂[R] _ : ι, M) →ₗ[R] ⨂[R] _ : ι, M) :
    T ∈ Submodule.span R (Set.range fun f : M →ₗ[R] M => map fun _ : ι => f) ↔
      ∀ σ : Equiv.Perm ι, Commute T (reindexRepresentation R M ι σ) := by
  -- The diagonal operators are the images of the pure powers of endomorphisms.
  have hdiag : (fun f : M →ₗ[R] M => map fun _ : ι => f) =
      ⇑(piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).toLinearMap ∘
        fun f : M →ₗ[R] M => ⨂ₜ[R] (_ : ι), f := by
    funext f
    simp
  -- So their span is the image of the invariants under the comparison map.
  have hspan : Submodule.span R (Set.range fun f : M →ₗ[R] M => map fun _ : ι => f) =
      Submodule.map (piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).toLinearMap
        (reindexRepresentation R (M →ₗ[R] M) ι).invariants := by
    rw [invariants_reindexRepresentation h, Submodule.map_span, ← Set.range_comp, hdiag]
  rw [hspan, Submodule.mem_map_equiv, Representation.mem_invariants]
  refine forall_congr' fun σ => ?_
  -- Being fixed by `σ` is, after comparison, commuting with the permutation of the factors.
  have hkey := piTensorHomEquiv_reindexRepresentation_mul σ
    ((piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).symm T)
  rw [LinearEquiv.apply_symm_apply] at hkey
  refine ⟨fun hfix => ?_, fun hcomm => ?_⟩
  · rw [Commute, SemiconjBy, ← hkey, hfix, LinearEquiv.apply_symm_apply]
  · refine (piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    have hcancel := congrArg (· * reindexRepresentation R M ι σ⁻¹) (hkey.trans hcomm.symm)
    simp only [mul_assoc, reindexRepresentation_mul_inv, mul_one] at hcancel
    exact hcancel

end Ring

end PiTensorProduct

namespace TauCeti

open PiTensorProduct

variable {R : Type*} {n d : ℕ} [CommRing R]

/-- **The commutant of the symmetric group on `(Rⁿ)^{⊗d}`**, the Schur-Weyl reading of
`PiTensorProduct.mem_span_range_map_const_iff_forall_commute`: when `d !` is invertible in `R`, the
endomorphisms of `(Rⁿ)^{⊗d}` commuting with the permutations of the tensor factors are exactly the
`R`-linear combinations of the diagonal operators `f^{⊗d}`, through which the general linear group
acts. -/
theorem mem_span_range_map_const_iff_forall_commute_permTensorAction (h : IsUnit (d ! : R))
    (T : (⨂[R] _ : Fin d, Fin n → R) →ₗ[R] ⨂[R] _ : Fin d, Fin n → R) :
    T ∈ Submodule.span R
        (Set.range fun f : (Fin n → R) →ₗ[R] (Fin n → R) => map fun _ : Fin d => f) ↔
      ∀ σ : Equiv.Perm (Fin d), Commute T (permTensorAction R n d σ) := by
  rw [permTensorAction_def]
  exact mem_span_range_map_const_iff_forall_commute (by rwa [Fintype.card_fin]) T

end TauCeti
