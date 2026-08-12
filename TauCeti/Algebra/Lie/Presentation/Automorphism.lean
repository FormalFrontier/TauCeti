/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre

/-!
# Automorphisms of a Serre presentation

Two families of automorphisms of `Matrix.ToLieAlgebra R CM` are visible in Serre's presentation
itself, and both are constructed here from the universal property in
`TauCeti/Algebra/Lie/Presentation/Serre.lean`.

The first family comes from the *symmetries of the matrix*: a permutation `σ` of the index set with
`CM.submatrix σ σ = CM` reindexes the generators, and `TauCeti.serreDiagramAut` is the resulting
automorphism `Hᵢ ↦ H_{σ i}`, `Eᵢ ↦ E_{σ i}`, `Fᵢ ↦ F_{σ i}`. When `CM` is the Cartan matrix of a
Dynkin diagram these are the *diagram* (or *graph*) automorphisms; the permutations themselves are
already pinned in `TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean`, whose entrywise
invariance lemmas supply the hypothesis `CM.submatrix σ σ = CM` through `Matrix.ext`.

The second is the *Chevalley involution* `TauCeti.serreChevalleyInvolution`, which exchanges the
raising and lowering generators with a sign: `Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ`. It exists because
Serre's relations are invariant under that exchange, and it is an involution because the exchange
is. The two families commute (`TauCeti.serreChevalleyInvolution_trans_serreDiagramAut`).

Both are instances of one observation, isolated here as stability properties of the predicate
`TauCeti.IsSerreSystem`: a Serre system in *any* Lie algebra stays a Serre system after reindexing
along a symmetry of the matrix (`TauCeti.IsSerreSystem.perm`) or after the signed exchange
(`TauCeti.IsSerreSystem.negSwap`). Stated at that generality they also give the *naturality* of the
two automorphisms — `TauCeti.serreLift_comp_serreDiagramAut` and
`TauCeti.serreLift_comp_serreChevalleyInvolution` — which say that any realisation of the
presentation transports them, and are how a downstream identification of the presented algebra with
a concrete split semisimple Lie algebra will carry them across.

Nothing here assumes that `CM` is a Cartan matrix, matching
`TauCeti/Algebra/Lie/Presentation/Serre.lean`: the constructions are statements about the relators.

## Main definitions

* `TauCeti.serreDiagramAut`: the automorphism of `Matrix.ToLieAlgebra R CM` induced by a permutation
  of the index set preserving `CM`.
* `TauCeti.serreChevalleyInvolution`: the Chevalley involution of `Matrix.ToLieAlgebra R CM`.

## Main results

* `TauCeti.IsSerreSystem.perm` and `TauCeti.IsSerreSystem.negSwap`: the two stability properties of
  Serre systems the automorphisms are built from.
* `TauCeti.serreDiagramAut_serreH` and its companions, `TauCeti.serreChevalleyInvolution_serreH` and
  its companions: the values on the generators, together with the uniqueness statements
  `TauCeti.eq_serreDiagramAut` and `TauCeti.eq_serreChevalleyInvolution`.
* `TauCeti.serreDiagramAut_refl`, `TauCeti.serreDiagramAut_trans` and
  `TauCeti.serreDiagramAut_symm`: the diagram automorphisms follow the group law of the
  permutations.
* `TauCeti.serreChevalleyInvolution_involutive`: the Chevalley involution squares to the identity.
* `TauCeti.serreChevalleyInvolution_trans_serreDiagramAut`: it commutes with every diagram
  automorphism.
* `TauCeti.serreLift_comp_serreDiagramAut` and
  `TauCeti.serreLift_comp_serreChevalleyInvolution`: naturality against an arbitrary Serre system.

## Implementation notes

The hypothesis that `σ` preserves `CM` is carried as the equation `CM.submatrix σ σ = CM` rather
than as a new predicate: it is the Mathlib spelling, its entrywise form `CM (σ i) (σ j) = CM i j`
holds by `rfl`, and the group law of such permutations is `Matrix.submatrix_submatrix`. Where a
composite automorphism needs the corresponding hypothesis for `σ.symm` or `σ.trans τ`, the lemmas
below take it as an argument instead of building it, so that a caller may supply whichever proof it
has; proof irrelevance makes the choice immaterial.

## Roadmap

The diagram automorphisms are a prerequisite for the pinned Chevalley--Demazure group schemes,
Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`: a pinning is what makes "the" graph
automorphism well defined, and the isomorphism theorem for pinned groups is what turns a diagram
automorphism into a named group automorphism. The Chevalley involution is the other automorphism
Layer 9's Chevalley basis needs, since it is what relates the structure constants `N (α, β)` and
`N (-α, -β)` and so fixes their signs. Consumed in turn by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose twisted groups of Lie type are built from graph
automorphisms of the ambient pinned group.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*][bourbaki1968]
* [J.E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  sections 14.2 and 25.2
* [R.W. Carter, *Simple Groups of Lie Type*][carter1972], section 4.1
-/

public section

namespace TauCeti

open LieAlgebra

variable {B : Type*} [DecidableEq B] (R : Type*) [CommRing R] (CM : Matrix B B ℤ)
variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-! ## Stability of Serre systems -/

section SerreSystem

variable {R CM} {H E F : B → L} {σ : Equiv.Perm B}

omit [DecidableEq B] in
/-- Negating an element of a Lie algebra does not change which vectors its iterated adjoint action
annihilates, because `ad` is linear and `-1` is a unit of the base ring. -/
private theorem ad_neg_pow_apply {x y : L} {n : ℕ} (h : (ad R L x ^ n) y = 0) :
    (ad R L (-x) ^ n) y = 0 := by
  have hneg : ad R L (-x) = (-1 : R) • ad R L x := by rw [map_neg, neg_smul, one_smul]
  rw [hneg, smul_pow, LinearMap.smul_apply, h, smul_zero]

omit [DecidableEq B] in
/-- Reindexing a Serre system along a permutation `σ` of the index set that preserves the matrix
gives a Serre system for the same matrix. -/
theorem IsSerreSystem.perm (h : IsSerreSystem R CM H E F) (hσ : CM.submatrix σ σ = CM) :
    IsSerreSystem R CM (H ∘ σ) (E ∘ σ) (F ∘ σ) := by
  have hCM : ∀ i j, CM (σ i) (σ j) = CM i j := fun i j => congrFun₂ hσ i j
  exact
    { lie_H_H := fun i j => h.lie_H_H (σ i) (σ j)
      lie_E_F_self := fun i => h.lie_E_F_self (σ i)
      lie_E_F_of_ne := fun i j hij => h.lie_E_F_of_ne (σ i) (σ j) (fun hc => hij (σ.injective hc))
      lie_H_E := fun i j => by
        simpa only [Function.comp_apply, hCM] using h.lie_H_E (σ i) (σ j)
      lie_H_F := fun i j => by
        simpa only [Function.comp_apply, hCM] using h.lie_H_F (σ i) (σ j)
      ad_pow_lie_E_E := fun i j => by
        simpa only [Function.comp_apply, hCM] using h.ad_pow_lie_E_E (σ i) (σ j)
      ad_pow_lie_F_F := fun i j => by
        simpa only [Function.comp_apply, hCM] using h.ad_pow_lie_F_F (σ i) (σ j) }

omit [DecidableEq B] in
/-- Negating the Cartan family of a Serre system and exchanging its raising and lowering families,
again with a sign, gives a Serre system for the same matrix. This is the symmetry of Serre's
relations behind the Chevalley involution. -/
theorem IsSerreSystem.negSwap (h : IsSerreSystem R CM H E F) :
    IsSerreSystem R CM (fun i => -H i) (fun i => -F i) (fun i => -E i) where
  lie_H_H i j := by simp [h.lie_H_H i j]
  lie_E_F_self i := by
    rw [neg_lie, lie_neg, neg_neg, ← lie_skew, h.lie_E_F_self i]
  lie_E_F_of_ne i j hij := by
    rw [neg_lie, lie_neg, neg_neg, ← lie_skew, h.lie_E_F_of_ne j i (Ne.symm hij), neg_zero]
  lie_H_E i j := by rw [neg_lie, lie_neg, neg_neg, h.lie_H_F i j, smul_neg]
  lie_H_F i j := by rw [neg_lie, lie_neg, neg_neg, h.lie_H_E i j, smul_neg, neg_neg]
  ad_pow_lie_E_E i j := by
    rw [neg_lie, lie_neg, neg_neg]
    exact ad_neg_pow_apply (h.ad_pow_lie_F_F i j)
  ad_pow_lie_F_F i j := by
    rw [neg_lie, lie_neg, neg_neg]
    exact ad_neg_pow_apply (h.ad_pow_lie_E_E i j)

end SerreSystem

/-! ## The diagram automorphisms

A permutation of the index set preserving the matrix acts on the presented algebra by permuting the
generators. -/

section Diagram

variable {σ τ : Equiv.Perm B}

omit [DecidableEq B] in
/-- If `σ` preserves a square matrix then so does `σ.symm`. -/
private theorem submatrix_perm_symm {α : Type*} {M : Matrix B B α}
    (hσ : M.submatrix σ σ = M) : M.submatrix σ.symm σ.symm = M :=
  calc M.submatrix ⇑σ.symm ⇑σ.symm
      = (M.submatrix ⇑σ ⇑σ).submatrix ⇑σ.symm ⇑σ.symm := by rw [hσ]
    _ = M := by rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

/-- The homomorphism of `Matrix.ToLieAlgebra R CM` permuting the generators along `σ`. It is
packaged as the automorphism `TauCeti.serreDiagramAut` below; only that is public. -/
private noncomputable def serreDiagramHom (hσ : CM.submatrix σ σ = CM) :
    Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM :=
  serreLift ((isSerreSystem_serre R CM).perm hσ)

/-- Permuting along `σ` and then along `σ.symm` is the identity of the presented algebra. -/
private theorem serreDiagramHom_comp (hσ : CM.submatrix σ σ = CM)
    (hσ' : CM.submatrix σ.symm σ.symm = CM) :
    (serreDiagramHom R CM hσ').comp (serreDiagramHom R CM hσ) = LieHom.id :=
  serre_hom_ext (fun i => by simp [serreDiagramHom]) (fun i => by simp [serreDiagramHom])
    fun i => by simp [serreDiagramHom]

/-- The automorphism of `Matrix.ToLieAlgebra R CM` induced by a permutation `σ` of the index set
preserving `CM`: it sends the generator of index `i` to the generator of index `σ i`, in each of
the three families. For a Cartan matrix this is a diagram automorphism. -/
noncomputable def serreDiagramAut (hσ : CM.submatrix σ σ = CM) :
    Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ Matrix.ToLieAlgebra R CM where
  toLieHom := serreDiagramHom R CM hσ
  invFun := serreDiagramHom R CM (submatrix_perm_symm hσ)
  left_inv x := by
    simpa using congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x)
      (serreDiagramHom_comp R CM hσ (submatrix_perm_symm hσ))
  right_inv x := by
    simpa using congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x)
      (serreDiagramHom_comp R CM (submatrix_perm_symm hσ) hσ)

@[simp]
theorem serreDiagramAut_serreH (hσ : CM.submatrix σ σ = CM) (i : B) :
    serreDiagramAut R CM hσ (serreH R CM i) = serreH R CM (σ i) :=
  serreLift_serreH _ i

@[simp]
theorem serreDiagramAut_serreE (hσ : CM.submatrix σ σ = CM) (i : B) :
    serreDiagramAut R CM hσ (serreE R CM i) = serreE R CM (σ i) :=
  serreLift_serreE _ i

@[simp]
theorem serreDiagramAut_serreF (hσ : CM.submatrix σ σ = CM) (i : B) :
    serreDiagramAut R CM hσ (serreF R CM i) = serreF R CM (σ i) :=
  serreLift_serreF _ i

/-- `TauCeti.serreDiagramAut` is the unique homomorphism permuting the generators along `σ`. -/
theorem eq_serreDiagramAut {hσ : CM.submatrix σ σ = CM}
    {g : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM}
    (hH : ∀ i, g (serreH R CM i) = serreH R CM (σ i))
    (hE : ∀ i, g (serreE R CM i) = serreE R CM (σ i))
    (hF : ∀ i, g (serreF R CM i) = serreF R CM (σ i)) :
    g = (serreDiagramAut R CM hσ : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) :=
  eq_serreLift hH hE hF

/-- The identity permutation induces the identity automorphism. -/
@[simp]
theorem serreDiagramAut_refl (hσ : CM.submatrix (Equiv.refl B) (Equiv.refl B) = CM) :
    serreDiagramAut R CM hσ = LieEquiv.refl := by
  refine LieEquiv.ext fun x => ?_
  have h : (serreDiagramAut R CM hσ).toLieHom =
      (LieEquiv.refl : Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ Matrix.ToLieAlgebra R CM).toLieHom :=
    serre_hom_ext (fun i => by simp) (fun i => by simp) fun i => by simp
  exact congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x) h

/-- Diagram automorphisms compose along the composition of permutations. -/
theorem serreDiagramAut_trans (hσ : CM.submatrix σ σ = CM) (hτ : CM.submatrix τ τ = CM)
    (hστ : CM.submatrix (σ.trans τ) (σ.trans τ) = CM) :
    (serreDiagramAut R CM hσ).trans (serreDiagramAut R CM hτ) = serreDiagramAut R CM hστ := by
  refine LieEquiv.ext fun x => ?_
  have h : ((serreDiagramAut R CM hσ).trans (serreDiagramAut R CM hτ)).toLieHom =
      (serreDiagramAut R CM hστ).toLieHom :=
    serre_hom_ext (fun i => by simp) (fun i => by simp) fun i => by simp
  exact congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x) h

/-- The inverse of a diagram automorphism is the diagram automorphism of the inverse
permutation. -/
theorem serreDiagramAut_symm (hσ : CM.submatrix σ σ = CM)
    (hσ' : CM.submatrix σ.symm σ.symm = CM) :
    (serreDiagramAut R CM hσ).symm = serreDiagramAut R CM hσ' :=
  LieEquiv.ext fun _ => rfl

/-- Naturality: any Serre system realising the presentation transports the diagram automorphism to
the reindexed system. -/
theorem serreLift_comp_serreDiagramAut {H E F : B → L} (h : IsSerreSystem R CM H E F)
    (hσ : CM.submatrix σ σ = CM) :
    (serreLift h).comp
        (serreDiagramAut R CM hσ : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) =
      serreLift (h.perm hσ) :=
  serre_hom_ext (fun i => by simp) (fun i => by simp) fun i => by simp

end Diagram

/-! ## The Chevalley involution -/

section Chevalley

/-- The homomorphism of `Matrix.ToLieAlgebra R CM` exchanging the raising and lowering generators
with a sign. It is packaged as the involution `TauCeti.serreChevalleyInvolution` below; only that
is public. -/
private noncomputable def serreChevalleyHom :
    Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM :=
  serreLift (isSerreSystem_serre R CM).negSwap

private theorem serreChevalleyHom_comp :
    (serreChevalleyHom R CM).comp (serreChevalleyHom R CM) = LieHom.id :=
  serre_hom_ext (fun i => by simp [serreChevalleyHom]) (fun i => by simp [serreChevalleyHom])
    fun i => by simp [serreChevalleyHom]

/-- The *Chevalley involution* of `Matrix.ToLieAlgebra R CM`: the automorphism `Hᵢ ↦ -Hᵢ`,
`Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ` exchanging the raising and lowering generators with a sign. -/
noncomputable def serreChevalleyInvolution :
    Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ Matrix.ToLieAlgebra R CM where
  toLieHom := serreChevalleyHom R CM
  invFun := serreChevalleyHom R CM
  left_inv x := by
    simpa using congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x)
      (serreChevalleyHom_comp R CM)
  right_inv x := by
    simpa using congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x)
      (serreChevalleyHom_comp R CM)

@[simp]
theorem serreChevalleyInvolution_serreH (i : B) :
    serreChevalleyInvolution R CM (serreH R CM i) = -serreH R CM i :=
  serreLift_serreH _ i

@[simp]
theorem serreChevalleyInvolution_serreE (i : B) :
    serreChevalleyInvolution R CM (serreE R CM i) = -serreF R CM i :=
  serreLift_serreE _ i

@[simp]
theorem serreChevalleyInvolution_serreF (i : B) :
    serreChevalleyInvolution R CM (serreF R CM i) = -serreE R CM i :=
  serreLift_serreF _ i

/-- `TauCeti.serreChevalleyInvolution` is the unique homomorphism exchanging the raising and
lowering generators with a sign. -/
theorem eq_serreChevalleyInvolution
    {g : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM}
    (hH : ∀ i, g (serreH R CM i) = -serreH R CM i)
    (hE : ∀ i, g (serreE R CM i) = -serreF R CM i)
    (hF : ∀ i, g (serreF R CM i) = -serreE R CM i) :
    g = (serreChevalleyInvolution R CM :
      Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) :=
  eq_serreLift hH hE hF

/-- The Chevalley involution is an involution. -/
theorem serreChevalleyInvolution_involutive :
    Function.Involutive (serreChevalleyInvolution R CM) := fun x =>
  (serreChevalleyInvolution R CM).left_inv x

@[simp]
theorem serreChevalleyInvolution_symm :
    (serreChevalleyInvolution R CM).symm = serreChevalleyInvolution R CM :=
  LieEquiv.ext fun _ => rfl

@[simp]
theorem serreChevalleyInvolution_trans_self :
    (serreChevalleyInvolution R CM).trans (serreChevalleyInvolution R CM) = LieEquiv.refl :=
  LieEquiv.ext (serreChevalleyInvolution_involutive R CM)

/-- The Chevalley involution commutes with every diagram automorphism: both send the generator of
index `i` to the signed generator of index `σ i` of the opposite family. -/
theorem serreChevalleyInvolution_trans_serreDiagramAut {σ : Equiv.Perm B}
    (hσ : CM.submatrix σ σ = CM) :
    (serreChevalleyInvolution R CM).trans (serreDiagramAut R CM hσ) =
      (serreDiagramAut R CM hσ).trans (serreChevalleyInvolution R CM) := by
  refine LieEquiv.ext fun x => ?_
  have h : ((serreChevalleyInvolution R CM).trans (serreDiagramAut R CM hσ)).toLieHom =
      ((serreDiagramAut R CM hσ).trans (serreChevalleyInvolution R CM)).toLieHom :=
    serre_hom_ext (fun i => by simp) (fun i => by simp) fun i => by simp
  exact congrArg (fun f : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM => f x) h

/-- Naturality: any Serre system realising the presentation transports the Chevalley involution to
the signed exchange of that system. -/
theorem serreLift_comp_serreChevalleyInvolution {H E F : B → L} (h : IsSerreSystem R CM H E F) :
    (serreLift h).comp
        (serreChevalleyInvolution R CM :
          Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) =
      serreLift h.negSwap :=
  serre_hom_ext (fun i => by simp) (fun i => by simp) fun i => by simp

end Chevalley

end TauCeti
