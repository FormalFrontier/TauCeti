/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.LinearAlgebra.SymmetricPower.Basic
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-!
# The symmetric tensors are spanned by the pure powers

The symmetric group of `ι` acts on the tensor power `⨂[R] (_ : ι), M` by permuting the factors.
This file identifies the invariants of that action, once `(#ι)!` is invertible in `R`: they are
exactly the span of the **pure powers** `⨂ₜ i, x`, the tensors with the same vector in every slot.

The engine is the classical polarization identity, proved here for an arbitrary multilinear map
`f` of `ι` arguments and stated as an inclusion-exclusion over the subsets of `ι`:
`∑_{S ⊆ ι} (-1)^{#S} f (∑_{i ∉ S} m i, …, ∑_{i ∉ S} m i) = ∑_{σ} f (m (σ ·))`.
Expanding each argument by multilinearity turns the left side into a sum over all functions
`g : ι → ι`, weighted by `∑_{S ⊆ (range g)ᶜ} (-1)^{#S}`, which vanishes unless `g` is onto; the
surviving terms are the permutations. Since the identity holds for every multilinear map, no
invertibility is needed for it, and the diagonal values `f (x, …, x)` alone already reach every
full symmetrization.

Dividing by `(#ι)!` then turns the symmetrization into a projection onto the invariants: an
invariant tensor is the average of its own orbit, so it lies in the span of the pure powers.

This is the spanning half of the double centralizer in Schur-Weyl duality. Under the
identification `End (V^{⊗ι}) ≃ (End V)^{⊗ι}`, the endomorphisms commuting with the factor
permutations are the invariants of the permutation action on `(End V)^{⊗ι}`, and this file says
they are spanned by the pure powers `f^{⊗ι}` — the diagonal operators through which the general
linear group acts.

## Main results

* `MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl`: the polarization identity for a
  multilinear map.
* `PiTensorProduct.sum_neg_one_pow_card_smul_tprod_sum_compl`: its tensor-power instance, writing
  the full symmetrization of a pure tensor as an alternating sum of pure powers.
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

open scoped Finset Nat TensorProduct

universe u v w z

namespace TauCeti

variable {R : Type u} {ι : Type w} [CommRing R] [DecidableEq ι]

/-- The functions into a fixed finset, as a filter on all functions. -/
private theorem piFinset_const [Fintype ι] (T : Finset ι) :
    (Fintype.piFinset fun _ : ι => T) =
      {g ∈ (Finset.univ : Finset (ι → ι)) | Finset.image g Finset.univ ⊆ T} := by
  ext g
  simp [Fintype.mem_piFinset, Finset.image_subset_iff]

/-- The subsets whose complement contains a fixed finset are the subsets of its complement. -/
private theorem filter_subset_compl [Fintype ι] (A : Finset ι) :
    {S ∈ (Finset.univ : Finset (Finset ι)) | A ⊆ Sᶜ} = Aᶜ.powerset := by
  ext S
  simp [Finset.mem_powerset, Finset.subset_compl_comm]

/-- The alternating sum over the subsets of a finset, in an arbitrary commutative ring. -/
private theorem sum_powerset_neg_one_pow_card (A : Finset ι) :
    ∑ S ∈ A.powerset, (-1 : R) ^ #S = if A = ∅ then 1 else 0 := by
  have := congrArg (Int.cast (R := R)) (Finset.sum_powerset_neg_one_pow_card (x := A))
  rw [Int.cast_sum] at this
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, apply_ite (Int.cast (R := R)),
    Int.cast_zero] using this

end TauCeti

namespace MultilinearMap

variable {R : Type u} {M : Type v} {N : Type z} {ι : Type w}
variable [CommRing R] [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
variable [Fintype ι] [DecidableEq ι]

/-- **Polarization.** For a multilinear map of `ι` arguments, the alternating sum over the subsets
`S ⊆ ι` of its value on the constant family `∑_{i ∉ S} m i` is the full symmetrization of its value
on `m`. Only the diagonal values of `f` appear on the left, so they already determine every
symmetrization; over a ring in which `(#ι)!` is invertible they therefore determine `f` on all
symmetric arguments. -/
theorem sum_neg_one_pow_card_smul_apply_sum_compl
    (f : MultilinearMap R (fun _ : ι => M) N) (m : ι → M) :
    ∑ S : Finset ι, (-1 : R) ^ #S • f (fun _ => ∑ i ∈ Sᶜ, m i) =
      ∑ σ : Equiv.Perm ι, f fun i => m (σ i) := by
  classical
  have expand : ∀ S : Finset ι, (-1 : R) ^ #S • f (fun _ => ∑ i ∈ Sᶜ, m i) =
      ∑ g : ι → ι, if Finset.image g Finset.univ ⊆ Sᶜ then
        (-1 : R) ^ #S • f fun i => m (g i) else 0 := by
    intro S
    rw [f.map_sum_finset (fun (_ i : ι) => m i) fun _ => Sᶜ, Finset.smul_sum,
      TauCeti.piFinset_const, Finset.sum_filter]
  have collapse : ∀ g : ι → ι, (∑ S : Finset ι, if Finset.image g Finset.univ ⊆ Sᶜ then
      (-1 : R) ^ #S • f fun i => m (g i) else 0) =
      (if Function.Bijective g then (1 : R) else 0) • f fun i => m (g i) := by
    intro g
    have hiff : (Finset.image g Finset.univ)ᶜ = ∅ ↔ Function.Bijective g := by
      rw [Finset.compl_eq_empty_iff]
      refine Iff.trans ?_ (Finite.surjective_iff_bijective (f := g))
      simp [Finset.eq_univ_iff_forall, Finset.mem_image, Function.Surjective]
    rw [← Finset.sum_filter, TauCeti.filter_subset_compl, ← Finset.sum_smul,
      TauCeti.sum_powerset_neg_one_pow_card]
    exact congrArg (fun r : R => r • f fun i => m (g i)) (if_congr hiff rfl rfl)
  have unweight : ∀ g : ι → ι, (if Function.Bijective g then (1 : R) else 0) •
      f (fun i => m (g i)) = if Function.Bijective g then f (fun i => m (g i)) else 0 := by
    intro g
    split <;> simp
  rw [Finset.sum_congr rfl fun S _ => expand S, Finset.sum_comm,
    Finset.sum_congr rfl fun g _ => (collapse g).trans (unweight g), ← Finset.sum_filter]
  refine (Finset.sum_bij (fun (σ : Equiv.Perm ι) _ => (σ : ι → ι))
    (fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩)
    (fun σ _ τ _ h => Equiv.coe_fn_injective h) (fun g hg => ?_) fun σ _ => rfl).symm
  exact ⟨Equiv.ofBijective g (Finset.mem_filter.mp hg).2, Finset.mem_univ _, rfl⟩

end MultilinearMap

namespace PiTensorProduct

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- A pure power `⨂ₜ i, x` is fixed by every permutation of the tensor factors. -/
theorem tprod_const_mem_invariants (x : M) :
    (⨂ₜ[R] (_ : ι), x) ∈ (reindexRepresentation R M ι).invariants := by
  intro σ
  rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod]

variable [Fintype ι] [DecidableEq ι]

/-- **Polarization for tensor powers.** The full symmetrization of a pure tensor is an alternating
sum of pure powers `⨂ₜ i, x`. -/
theorem sum_neg_one_pow_card_smul_tprod_sum_compl (m : ι → M) :
    ∑ S : Finset ι, (-1 : R) ^ #S • (⨂ₜ[R] (_ : ι), ∑ i ∈ Sᶜ, m i) =
      ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) :=
  MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl (tprod R) m

/-- Symmetrizing any tensor lands in the span of the pure powers: on a pure tensor this is
polarization, and both sides are linear. -/
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

variable [Invertible ((Fintype.card ι)! : R)]

omit [DecidableEq ι] in
/-- **The symmetric tensors are the span of the pure powers.** When `(#ι)!` is invertible in `R`,
the invariants of the permutation action on `⨂[R] (_ : ι), M` are spanned by the pure powers
`⨂ₜ i, x`. -/
theorem invariants_reindexRepresentation :
    (reindexRepresentation R M ι).invariants =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  classical
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

/-- **The symmetrization operator projects onto the symmetric tensors.** Its range is again the
span of the pure powers. -/
theorem range_sum_reindexRepresentation :
    LinearMap.range (∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ) =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro _ ⟨y, rfl⟩
    simpa [LinearMap.sum_apply] using sum_reindexRepresentation_mem_span y
  · rintro _ ⟨x, rfl⟩
    refine ⟨⅟((Fintype.card ι)! : R) • (⨂ₜ[R] (_ : ι), x), ?_⟩
    rw [map_smul, LinearMap.sum_apply,
      Finset.sum_congr rfl fun σ _ => tprod_const_mem_invariants (R := R) (ι := ι) x σ,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul R, smul_smul,
      invOf_mul_self, one_smul]

end PiTensorProduct

namespace SymmetricPower

variable {R : Type u} {M : Type v} {ι : Type u}
variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable [Invertible ((Fintype.card ι)! : R)]

/-- **The symmetric power sits inside the tensor power as the span of the pure powers.** The
symmetrization `SymmetricPower.toTensorPower` has as its image the span of the tensors `⨂ₜ i, x`.

Together with `SymmetricPower.toTensorPower_injective` this presents `Sym[R] ι M` concretely: it
is the subspace of `⨂[R] (_ : ι), M` generated by the pure powers. The index type is confined to
the universe of `R` because `SymmetricPower` is. -/
theorem range_toTensorPower_eq_span :
    LinearMap.range (toTensorPower R ι M) =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  have hsum : (∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap) =
      ∑ σ : Equiv.Perm ι, PiTensorProduct.reindexRepresentation R M ι σ :=
    Finset.sum_congr rfl fun σ _ => (PiTensorProduct.reindexRepresentation_apply R M ι σ).symm
  rw [range_toTensorPower, hsum]
  exact PiTensorProduct.range_sum_reindexRepresentation

end SymmetricPower

namespace TauCeti

variable {R : Type u} {n d : ℕ} [CommRing R] [Invertible (d ! : R)]

/-- **The symmetric tensors in `(Rⁿ)^{⊗d}`.** The invariants of the `S_d`-action permuting the
tensor factors are spanned by the pure powers `⨂ₜ i, x`; this is the spanning half of the
Schur-Weyl double centralizer, read on the tensor power itself. -/
theorem invariants_permTensorAction :
    (permTensorAction R n d).invariants =
      Submodule.span R (Set.range fun x : Fin n → R => ⨂ₜ[R] (_ : Fin d), x) := by
  have : Invertible ((Fintype.card (Fin d))! : R) := by
    rw [Fintype.card_fin]; infer_instance
  rw [permTensorAction_def]
  exact PiTensorProduct.invariants_reindexRepresentation

/-- **The symmetrizer of `R[S_d]` cuts out the same subspace.** The image of the group-algebra
element `∑_σ σ` acting on `(Rⁿ)^{⊗d}` is the span of the pure powers, hence the invariants: it is
the projection onto them, up to the factor `d!`. This is the Young symmetrizer of a one-row shape,
read at the level of the image subalgebra of `R[S_d]` in which Schur-Weyl duality is stated. -/
theorem range_permTensorActionAlgHom_sum_single :
    LinearMap.range (permTensorActionAlgHom R n d
        (∑ σ : Equiv.Perm (Fin d), MonoidAlgebra.single σ (1 : R))) =
      Submodule.span R (Set.range fun x : Fin n → R => ⨂ₜ[R] (_ : Fin d), x) := by
  have : Invertible ((Fintype.card (Fin d))! : R) := by
    rw [Fintype.card_fin]; infer_instance
  have hsum : permTensorActionAlgHom R n d
        (∑ σ : Equiv.Perm (Fin d), MonoidAlgebra.single σ (1 : R)) =
      ∑ σ : Equiv.Perm (Fin d),
        PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d) σ := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_single, one_smul,
      permTensorAction_def]
  rw [hsum]
  exact PiTensorProduct.range_sum_reindexRepresentation

end TauCeti
