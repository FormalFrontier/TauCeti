/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The presented algebra and its universal property occur throughout.
public import TauCeti.Algebra.Lie.Presentation.Serre
-- `TauCeti.submatrix_perm_trans` and `TauCeti.submatrix_perm_symm` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.Submatrix

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
is. The two families commute (`TauCeti.serreChevalleyInvolution_comm_serreDiagramAut`).

Both are instances of one observation, recorded with the predicate itself in
`TauCeti/Algebra/Lie/Presentation/Serre.lean` as stability properties of `TauCeti.IsSerreSystem`: a
Serre system in *any* Lie algebra stays a Serre system after reindexing along an injective map of
index sets (`TauCeti.IsSerreSystem.submatrix`, of which reindexing along a symmetry of the matrix is
the special case `TauCeti.IsSerreSystem.perm`) or after the signed exchange
(`TauCeti.IsSerreSystem.neg_swap`). Stated at that generality they also give the
*naturality* of the two automorphisms — `TauCeti.serreLift_comp_serreDiagramAut` and
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

* `TauCeti.serreDiagramAut_serreH` and its companions, `TauCeti.serreChevalleyInvolution_serreH` and
  its companions: the values on the generators, together with the uniqueness statements
  `TauCeti.eq_serreDiagramAut` and `TauCeti.eq_serreChevalleyInvolution`.
* `TauCeti.serreDiagramAut_refl`, `TauCeti.serreDiagramAut_trans` and
  `TauCeti.serreDiagramAut_symm`: the diagram automorphisms follow the group law of the
  permutations, which for the hypothesis itself is `TauCeti.submatrix_perm_refl`,
  `TauCeti.submatrix_perm_trans` and `TauCeti.submatrix_perm_symm`.
* `TauCeti.serreDiagramAut_iterate_eq_id`: a power relation on the indexing permutation induces
  the same iterate relation on its diagram automorphism.
* `TauCeti.serreChevalleyInvolution_involutive`: the Chevalley involution squares to the identity.
* `TauCeti.serreChevalleyInvolution_comm_serreDiagramAut`: it commutes with every diagram
  automorphism.
* `TauCeti.serreLift_comp_serreDiagramAut` and
  `TauCeti.serreLift_comp_serreChevalleyInvolution`: naturality against an arbitrary Serre system.
* `TauCeti.comp_serreLift_eq_serreLift_comp_serreChevalleyInvolution`: a concrete signed
  involution intertwines the universal lift with the Serre Chevalley involution.

## Implementation notes

The hypothesis that `σ` preserves `CM` is carried as the equation `CM.submatrix σ σ = CM` rather
than as a new predicate: it is the Mathlib spelling, its entrywise form `CM (σ i) (σ j) = CM i j`
holds by `rfl`, and the group law of such permutations is `Matrix.submatrix_submatrix`. That group
law is `TauCeti.submatrix_perm_refl`, `TauCeti.submatrix_perm_trans` and
`TauCeti.submatrix_perm_symm` of `TauCeti/LinearAlgebra/Matrix/Submatrix.lean`, so a composite
automorphism builds the hypothesis it needs for `Equiv.refl B`, `σ.trans τ` or `σ.symm` rather than
demanding it from the caller; proof irrelevance makes a caller's own proof interchangeable with the
one built here.

Equalities of the automorphisms themselves are proved with `TauCeti.serre_equiv_ext`, the
equivalence-level extensionality principle of the presentation, so that no proof here has to
descend to the underlying homomorphisms by hand.

## Roadmap

Both automorphisms are prerequisites for the pinned Chevalley--Demazure group schemes, Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, which asks for the split reductive group scheme over
`ℤ` to be built "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping algebra". The
Serre presentation of `TauCeti/Algebra/Lie/Presentation/Serre.lean` is the explicit carrier of the
Lie algebra that construction starts from, and the two automorphisms are the two symmetries of it
that construction uses.

The Chevalley involution is the immediate one: the classical normalisation of a Chevalley basis
picks the root vectors `x α` and `x (-α)` compatibly by transporting them along an automorphism
acting as `h ↦ -h` on the Cartan subalgebra and exchanging the raising and lowering root vectors
with a sign, and that choice is what forces the structure constants of opposite pairs of roots to
match up as `N (-α, -β) = -N (α, β)` (Humphreys §25.2, Carter §4.1). Integrality of the structure
constants is a separate matter, coming from the root-string argument once the basis is normalised
this way; the involution is what makes the two halves of the basis consistent, not what clears
denominators.
`TauCeti.serreChevalleyInvolution` is that automorphism on the presented algebra, and
`TauCeti.serreLift_comp_serreChevalleyInvolution` is what will carry it to any concrete split
semisimple Lie algebra identified with the presentation.

The diagram automorphisms are the second: a pinning is what makes "the" graph automorphism well
defined, and on the Chevalley--Demazure side the graph automorphism of the group scheme is obtained
by descending the one that permutes the divided powers of the generators in the Kostant `ℤ`-form,
which is `TauCeti.serreDiagramAut` on the underlying Lie algebra. Consumed in turn by milestone L0
of `TauCetiRoadmap/CFSGStatement/README.md`, whose twisted groups of Lie type are the fixed points
of a Steinberg endomorphism built from a graph automorphism of the ambient pinned group.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*][bourbaki1968]
* [J.E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  sections 14.2 and 25.2
* [R.W. Carter, *Simple Groups of Lie Type*][carter1972], section 4.1
-/

public section

namespace TauCeti

variable {B : Type*} [DecidableEq B] (R : Type*) [CommRing R] (CM : Matrix B B ℤ)
variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-! ## The diagram automorphisms

A permutation of the index set preserving the matrix acts on the presented algebra by permuting the
generators. -/

section Diagram

variable {σ τ : Equiv.Perm B}

/-- The homomorphism of `Matrix.ToLieAlgebra R CM` permuting the generators along `σ`. It is
packaged as the automorphism `TauCeti.serreDiagramAut` below; only that is public. -/
private noncomputable def serreDiagramHom (hσ : CM.submatrix σ σ = CM) :
    Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM :=
  serreLift ((isSerreSystem_serre R CM).perm hσ)

/-- Permuting along `σ` and then along a `τ` inverting it is the identity of the presented
algebra. -/
private theorem serreDiagramHom_comp (hσ : CM.submatrix σ σ = CM) (hτ : CM.submatrix τ τ = CM)
    (hστ : ∀ i, τ (σ i) = i) :
    (serreDiagramHom R CM hτ).comp (serreDiagramHom R CM hσ) = LieHom.id :=
  serre_hom_ext (fun i => by simp [serreDiagramHom, hστ])
    (fun i => by simp [serreDiagramHom, hστ]) fun i => by simp [serreDiagramHom, hστ]

/-- The automorphism of `Matrix.ToLieAlgebra R CM` induced by a permutation `σ` of the index set
preserving `CM`: it sends the generator of index `i` to the generator of index `σ i`, in each of
the three families. For a Cartan matrix this is a diagram automorphism. -/
noncomputable def serreDiagramAut (hσ : CM.submatrix σ σ = CM) :
    Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ Matrix.ToLieAlgebra R CM where
  toLieHom := serreDiagramHom R CM hσ
  invFun := serreDiagramHom R CM (submatrix_perm_symm hσ)
  left_inv x := by
    simpa using DFunLike.congr_fun
      (serreDiagramHom_comp R CM hσ (submatrix_perm_symm hσ) σ.symm_apply_apply) x
  right_inv x := by
    simpa using DFunLike.congr_fun
      (serreDiagramHom_comp R CM (submatrix_perm_symm hσ) hσ σ.apply_symm_apply) x

-- The three generator values below are `TauCeti.serreLift_serreH` and its companions: the
-- `toLieHom` field of `TauCeti.serreDiagramAut` is the `TauCeti.serreLift` of the reindexed
-- system, so the two sides agree once the `LieEquiv` coercion is unfolded.

/-- The diagram automorphism of `σ` sends `Hᵢ` to `H_{σ i}`. -/
@[simp]
theorem serreDiagramAut_serreH (hσ : CM.submatrix σ σ = CM) (i : B) :
    serreDiagramAut R CM hσ (serreH R CM i) = serreH R CM (σ i) :=
  serreLift_serreH _ i

/-- The diagram automorphism of `σ` sends `Eᵢ` to `E_{σ i}`. -/
@[simp]
theorem serreDiagramAut_serreE (hσ : CM.submatrix σ σ = CM) (i : B) :
    serreDiagramAut R CM hσ (serreE R CM i) = serreE R CM (σ i) :=
  serreLift_serreE _ i

/-- The diagram automorphism of `σ` sends `Fᵢ` to `F_{σ i}`. -/
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
theorem serreDiagramAut_refl :
    serreDiagramAut R CM (submatrix_perm_refl CM) = LieEquiv.refl :=
  serre_equiv_ext (fun i => by simp) (fun i => by simp) fun i => by simp

/-- Diagram automorphisms compose along the composition of permutations. -/
@[simp]
theorem serreDiagramAut_trans (hσ : CM.submatrix σ σ = CM) (hτ : CM.submatrix τ τ = CM) :
    (serreDiagramAut R CM hσ).trans (serreDiagramAut R CM hτ) =
      serreDiagramAut R CM (submatrix_perm_trans hσ hτ) :=
  serre_equiv_ext (fun i => by simp) (fun i => by simp) fun i => by simp

/-- The inverse of a diagram automorphism is the diagram automorphism of the inverse
permutation. -/
@[simp]
theorem serreDiagramAut_symm (hσ : CM.submatrix σ σ = CM) :
    (serreDiagramAut R CM hσ).symm = serreDiagramAut R CM (submatrix_perm_symm hσ) :=
  serre_equiv_ext (fun i => (LieEquiv.symm_apply_eq _).2 (by simp))
    (fun i => (LieEquiv.symm_apply_eq _).2 (by simp))
    fun i => (LieEquiv.symm_apply_eq _).2 (by simp)

-- Unlike `Equiv.Perm`, endomorphism `LieEquiv`s do not carry a group instance. This private
-- iterate keeps every intermediate map bundled, so the Serre-generator extensionality theorem can
-- be used below. Its value is the ordinary function iterate by `lieEquivIterate_apply`.
private noncomputable def lieEquivIterate
    {L : Type*} [LieRing L] [LieAlgebra R L] (e : L ≃ₗ⁅R⁆ L) : ℕ → L ≃ₗ⁅R⁆ L
  | 0 => LieEquiv.refl
  | n + 1 => e.trans (lieEquivIterate e n)

private theorem lieEquivIterate_apply
    {L : Type*} [LieRing L] [LieAlgebra R L] (e : L ≃ₗ⁅R⁆ L) (n : ℕ) (x : L) :
    lieEquivIterate R e n x = e^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (e x)

private theorem lieEquivIterate_apply_of_apply
    {I L : Type*} [LieRing L] [LieAlgebra R L] (e : L ≃ₗ⁅R⁆ L) (τ : Equiv.Perm I)
    (g : I → L) (h : ∀ i, e (g i) = g (τ i)) (n : ℕ) (i : I) :
    lieEquivIterate R e n (g i) = g ((τ ^ n) i) := by
  induction n generalizing i with
  | zero => simp [lieEquivIterate]
  | succ n ih =>
      rw [lieEquivIterate, LieEquiv.trans_apply, h, ih, pow_succ,
        Equiv.Perm.mul_apply]

/-- A diagram automorphism has order dividing the order of its indexing permutation. If
`σ ^ n = 1`, then applying the corresponding Serre automorphism `n` times is the identity.

This is stated using `Function.iterate` because endomorphism `LieEquiv`s do not carry a group
instance. -/
theorem serreDiagramAut_iterate_eq_id (hσ : CM.submatrix σ σ = CM) {n : ℕ}
    (hn : σ ^ n = 1) : (serreDiagramAut R CM hσ : _ → _)^[n] = id := by
  have hiter : lieEquivIterate R (serreDiagramAut R CM hσ) n = LieEquiv.refl :=
    serre_equiv_ext
      (fun i => calc
        _ = serreH R CM ((σ ^ n) i) := lieEquivIterate_apply_of_apply R _ σ
          (serreH R CM) (serreDiagramAut_serreH R CM hσ) n i
        _ = _ := by rw [hn, Equiv.Perm.one_apply]; rfl)
      (fun i => calc
        _ = serreE R CM ((σ ^ n) i) := lieEquivIterate_apply_of_apply R _ σ
          (serreE R CM) (serreDiagramAut_serreE R CM hσ) n i
        _ = _ := by rw [hn, Equiv.Perm.one_apply]; rfl)
      fun i => calc
        _ = serreF R CM ((σ ^ n) i) := lieEquivIterate_apply_of_apply R _ σ
          (serreF R CM) (serreDiagramAut_serreF R CM hσ) n i
        _ = _ := by rw [hn, Equiv.Perm.one_apply]; rfl
  funext x
  rw [← lieEquivIterate_apply, hiter]
  rfl

/-- Naturality: any Serre system realising the presentation transports the diagram automorphism to
the reindexed system. -/
@[simp]
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
  serreLift (isSerreSystem_serre R CM).neg_swap

/-- The signed exchange of the generators is its own inverse. -/
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
  left_inv x := by simpa using DFunLike.congr_fun (serreChevalleyHom_comp R CM) x
  right_inv x := by simpa using DFunLike.congr_fun (serreChevalleyHom_comp R CM) x

-- As for the diagram automorphisms, the three generator values below are
-- `TauCeti.serreLift_serreH` and its companions: the `toLieHom` field of
-- `TauCeti.serreChevalleyInvolution` is the `TauCeti.serreLift` of the exchanged system.

/-- The Chevalley involution sends `Hᵢ` to `-Hᵢ`. -/
@[simp]
theorem serreChevalleyInvolution_serreH (i : B) :
    serreChevalleyInvolution R CM (serreH R CM i) = -serreH R CM i :=
  serreLift_serreH _ i

/-- The Chevalley involution sends `Eᵢ` to `-Fᵢ`. -/
@[simp]
theorem serreChevalleyInvolution_serreE (i : B) :
    serreChevalleyInvolution R CM (serreE R CM i) = -serreF R CM i :=
  serreLift_serreE _ i

/-- The Chevalley involution sends `Fᵢ` to `-Eᵢ`. -/
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

/-- Applying the Chevalley involution twice returns the original element. -/
@[simp]
theorem serreChevalleyInvolution_serreChevalleyInvolution (x : Matrix.ToLieAlgebra R CM) :
    serreChevalleyInvolution R CM (serreChevalleyInvolution R CM x) = x := by
  have h : (serreChevalleyInvolution R CM).trans (serreChevalleyInvolution R CM) =
      (LieEquiv.refl : Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) :=
    serre_equiv_ext (fun i => by simp) (fun i => by simp) fun i => by simp
  simpa using DFunLike.congr_fun h x

/-- The Chevalley involution is an involution. -/
theorem serreChevalleyInvolution_involutive :
    Function.Involutive (serreChevalleyInvolution R CM) :=
  serreChevalleyInvolution_serreChevalleyInvolution R CM

/-- The Chevalley involution is its own inverse. -/
@[simp]
theorem serreChevalleyInvolution_symm :
    (serreChevalleyInvolution R CM).symm = serreChevalleyInvolution R CM :=
  serre_equiv_ext (fun i => (LieEquiv.symm_apply_eq _).2 (by simp))
    (fun i => (LieEquiv.symm_apply_eq _).2 (by simp))
    fun i => (LieEquiv.symm_apply_eq _).2 (by simp)

/-- The Chevalley involution commutes with every diagram automorphism: both composites send `Hᵢ` to
`-H_{σ i}`, `Eᵢ` to `-F_{σ i}` and `Fᵢ` to `-E_{σ i}`. -/
theorem serreChevalleyInvolution_comm_serreDiagramAut {σ : Equiv.Perm B}
    (hσ : CM.submatrix σ σ = CM) :
    (serreChevalleyInvolution R CM).trans (serreDiagramAut R CM hσ) =
      (serreDiagramAut R CM hσ).trans (serreChevalleyInvolution R CM) :=
  serre_equiv_ext (fun i => by simp) (fun i => by simp) fun i => by simp

/-- Naturality: any Serre system realising the presentation transports the Chevalley involution to
the signed exchange of that system. -/
@[simp]
theorem serreLift_comp_serreChevalleyInvolution {H E F : B → L} (h : IsSerreSystem R CM H E F) :
    (serreLift h).comp
        (serreChevalleyInvolution R CM :
          Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) =
      serreLift h.neg_swap :=
  serre_hom_ext (fun i => by simp) (fun i => by simp) fun i => by simp

/-- A homomorphism acting by signed exchange on a Serre system intertwines its universal lift with
the Chevalley involution of the presentation. -/
theorem comp_serreLift_eq_serreLift_comp_serreChevalleyInvolution {H E F : B → L}
    (h : IsSerreSystem R CM H E F) (θ : L →ₗ⁅R⁆ L)
    (hH : ∀ i, θ (H i) = -H i) (hE : ∀ i, θ (E i) = -F i)
    (hF : ∀ i, θ (F i) = -E i) :
    θ.comp (serreLift h) =
      (serreLift h).comp
        (serreChevalleyInvolution R CM :
          Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) := by
  rw [serreLift_comp_serreChevalleyInvolution]
  exact eq_serreLift (fun i => by simp [hH]) (fun i => by simp [hE]) fun i => by simp [hF]

end Chevalley

end TauCeti
