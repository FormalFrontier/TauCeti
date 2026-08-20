/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
public import TauCeti.LinearAlgebra.RootSystem.EquivInvariance

/-!
# Symmetries of Geck's construction

Geck's construction attaches to a root pairing `P` with base `b` an explicit Lie subalgebra of the
matrices indexed by `b.support ⊕ ι`, spanned by the brackets of the numbered matrices
`RootPairing.GeckConstruction.h i`, `RootPairing.GeckConstruction.e i` and
`RootPairing.GeckConstruction.f i`. Every entry of those matrices is a Cartan integer, a root-string
coefficient, or the truth value of an additive relation between roots: *no sign is chosen*, unlike
the construction of a Lie algebra directly on `H ⊕ K^Φ`, whose structure constants need a choice of
extraspecial pairs.

This file is about the consequence of that. An equivalence `g` of root pairings whose index
bijection restricts to an equivalence `τ` of their bases identifies the corresponding index types,
and reindexing a matrix along that equivalence carries each of the three numbered families to the
other, moving the number along:

```text
h i ↦ h (τ i),   e i ↦ e (τ i),   f i ↦ f (τ i).
```

So reindexing restricts to an equivalence of the two Geck Lie algebras, and for an automorphism it
gives `TauCeti.geckLieAut`. On the defining modules it is a permutation of coordinates,
`TauCeti.geckModuleEquiv`. Such a coordinate permutation preserves the standard coordinate lattice
and is intended as input to a later Chevalley--Demazure descent; unlike an automorphism moving root
vectors by signs, it needs no further renormalisation first.

Nothing here uses `RootPairing.Base.equivOfCartanMatrixEq` or any other rigidity statement. The
equivalence `g` is data supplied by the caller, and the hypothesis `hτ` says only that its index
bijection restricts to `τ`. In the automorphism case, a caller holding only a permutation `τ` of the
nodes that preserves the Cartan matrix gets such a `g` from Mathlib's
`RootPairing.Base.equivOfCartanMatrixEq`, and `hτ` is
then `TauCeti.equivOfCartanMatrixEq_indexEquiv_apply` read in the other direction.

## Main definitions

* `TauCeti.geckIndexEquiv`: the equivalence of matrix index types induced by a base-preserving
  equivalence of root pairings.
* `TauCeti.geckModuleEquiv`: the resulting coordinate permutation of the defining module.
* `TauCeti.geckLieEquiv`: the resulting equivalence of Geck's Lie algebras.
* `TauCeti.geckLieAut`: its specialization to an automorphism of one Geck Lie algebra.

## Main results

* `TauCeti.reindex_geckIndexEquiv_h`, `TauCeti.reindex_geckIndexEquiv_e` and
  `TauCeti.reindex_geckIndexEquiv_f`: conjugation carries the numbered matrix at `i` to the one at
  `τ i`.
* `TauCeti.map_lieAlgebra_geckIndexEquiv`: reindexing carries one Geck Lie algebra onto the other.
* `TauCeti.geckModuleEquiv_mulVec_h`, `TauCeti.geckModuleEquiv_mulVec_e` and
  `TauCeti.geckModuleEquiv_mulVec_f`: the coordinate permutation intertwines the action of the
  numbered matrix at `i` with the action of the one at `τ i`.

## Roadmap

This advances Layer 9, "pinned Chevalley--Demazure group schemes over `ℤ`", of
`TauCetiRoadmap/ReductiveGroups/README.md`, whose "Pinnings" bullet asks for the graph automorphism
attached to a pinning as named data. Its consumer is milestone L1, "ordinary and graph-twisted
Steinberg maps", of `TauCetiRoadmap/CFSGStatement/README.md`, through
`TauCeti.GraphTwistedIndex.graphAut`: the pair of a permutation of the numbered raising generators
and a linear automorphism of the representation intertwining them is exactly the input of
`TauCeti.UniversalEnvelopingAlgebra.kostantElementaryNumberedSymmetryAut`, and
`TauCeti.geckModuleEquiv` together with `TauCeti.geckModuleEquiv_mulVec_e` supplies it for Geck's
representation.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
-/

public section

namespace TauCeti

open Function Set Matrix RootPairing

-- The Lie ring structure on matrices is the one Geck's construction is stated against; Mathlib
-- makes it a local instance rather than a global one.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
  [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
  [P.IsCrystallographic] [P₂.IsCrystallographic] {b : P.Base} {b₂ : P₂.Base}
  (g : P.Equiv P₂) (τ : b.support ≃ b₂.support)

/-- The equivalence of the index types of Geck's matrices attached to an equivalence `g` of root
pairings whose index bijection restricts to `τ` on the bases.

The `b.support` summand indexes the Cartan coordinates and the `ι` summand indexes the root
coordinates, so the permutation is `τ` on the first and `g.indexEquiv` on the second. -/
def geckIndexEquiv : (b.support ⊕ ι) ≃ (b₂.support ⊕ ι₂) :=
  Equiv.sumCongr τ g.indexEquiv

omit [Finite ι] [Finite ι₂] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  [P₂.IsCrystallographic] in
@[simp]
theorem geckIndexEquiv_inl (i : b.support) :
    geckIndexEquiv g τ (Sum.inl i) = Sum.inl (τ i) := by
  simp [geckIndexEquiv]

omit [Finite ι] [Finite ι₂] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  [P₂.IsCrystallographic] in
@[simp]
theorem geckIndexEquiv_inr (i : ι) :
    geckIndexEquiv g τ (Sum.inr i) = Sum.inr (g.indexEquiv i) := by
  simp [geckIndexEquiv]

/-! ## The coordinate permutation of the defining module -/

/-- The coordinate equivalence of the defining modules of Geck's construction induced by a
base-preserving equivalence of root pairings. -/
def geckModuleEquiv : ((b.support ⊕ ι) → R) ≃ₗ[R] ((b₂.support ⊕ ι₂) → R) :=
  LinearEquiv.funCongrLeft R R (geckIndexEquiv g τ).symm

omit [Finite ι] [Finite ι₂] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  [P₂.IsCrystallographic] in
@[simp]
theorem geckModuleEquiv_apply (v : (b.support ⊕ ι) → R) (x : b₂.support ⊕ ι₂) :
    geckModuleEquiv g τ v x = v ((geckIndexEquiv g τ).symm x) := by
  simp [geckModuleEquiv, LinearEquiv.funCongrLeft, LinearMap.funLeft]

section

variable [DecidableEq ι] [Fintype ι] [DecidableEq ι₂] [Fintype ι₂]

omit [Finite ι] [Finite ι₂] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  [P₂.IsCrystallographic] in
/-- The coordinate permutation intertwines the action of a matrix with the action of its
conjugate. -/
theorem geckModuleEquiv_mulVec (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)
    (v : (b.support ⊕ ι) → R) :
    geckModuleEquiv g τ (A *ᵥ v) =
      reindexAlgEquiv R R (geckIndexEquiv g τ) A *ᵥ geckModuleEquiv g τ v := by
  rw [coe_reindexAlgEquiv, reindex_apply,
    submatrix_mulVec_equiv A (geckModuleEquiv g τ v) (geckIndexEquiv g τ).symm
      (geckIndexEquiv g τ).symm]
  ext x
  simp [Function.comp_def]

end

section Numbered

variable (hτ : ∀ i : b.support, (τ i : ι₂) = g.indexEquiv i)
include hτ

/-! ## Conjugating the numbered matrices -/

omit [Finite ι] [Finite ι₂] [IsDomain R] in
/-- Pulling back `RootPairing.GeckConstruction.h (τ i)` along the index equivalence gives the
matrix numbered by `i`, entrywise. Unlike `TauCeti.reindex_geckIndexEquiv_h` this needs neither a
`Fintype` nor a `DecidableEq` instance on the root index type. -/
theorem submatrix_geckIndexEquiv_h (i : b.support) :
    (GeckConstruction.h (b := b₂) (τ i)).submatrix
        (geckIndexEquiv g τ) (geckIndexEquiv g τ) =
      GeckConstruction.h (b := b) (R := R) i := by
  classical
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [submatrix_apply, geckIndexEquiv_inl, geckIndexEquiv_inr, GeckConstruction.h_def,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, diagonal_apply, Equiv.apply_eq_iff_eq, hτ, pairingIn_indexEquiv]

/-- Pulling back `RootPairing.GeckConstruction.e (τ i)` along the index equivalence gives the
matrix numbered by `i`, entrywise. Unlike `TauCeti.reindex_geckIndexEquiv_e` this needs neither a
`Fintype` nor a `DecidableEq` instance on the root index type. -/
theorem submatrix_geckIndexEquiv_e (i : b.support) :
    (GeckConstruction.e (b := b₂) (τ i)).submatrix
        (geckIndexEquiv g τ) (geckIndexEquiv g τ) =
      GeckConstruction.e (b := b) (R := R) i := by
  classical
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [submatrix_apply, geckIndexEquiv_inl, geckIndexEquiv_inr, GeckConstruction.e,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply, hτ, ← indexEquiv_neg g, indexNeg_neg, Equiv.apply_eq_iff_eq,
      Base.cartanMatrixIn_def, pairingIn_indexEquiv, root_indexEquiv_add_iff,
      chainBotCoeff_indexEquiv]

/-- Pulling back `RootPairing.GeckConstruction.f (τ i)` along the index equivalence gives the
matrix numbered by `i`, entrywise. Unlike `TauCeti.reindex_geckIndexEquiv_f` this needs neither a
`Fintype` nor a `DecidableEq` instance on the root index type. -/
theorem submatrix_geckIndexEquiv_f (i : b.support) :
    (GeckConstruction.f (b := b₂) (τ i)).submatrix
        (geckIndexEquiv g τ) (geckIndexEquiv g τ) =
      GeckConstruction.f (b := b) (R := R) i := by
  classical
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [submatrix_apply, geckIndexEquiv_inl, geckIndexEquiv_inr, GeckConstruction.f,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply, hτ, ← indexEquiv_neg g, indexNeg_neg, Equiv.apply_eq_iff_eq,
      Base.cartanMatrixIn_def, pairingIn_indexEquiv, root_indexEquiv_sub_iff,
      chainTopCoeff_indexEquiv]

section

variable [DecidableEq ι] [Fintype ι] [DecidableEq ι₂] [Fintype ι₂]

omit [Finite ι] [Finite ι₂] [IsDomain R] in
/-- Conjugation by the index permutation carries the Cartan matrix numbered by `i` to the one
numbered by `τ i`. -/
@[simp]
theorem reindex_geckIndexEquiv_h (i : b.support) :
    reindexAlgEquiv R R (geckIndexEquiv g τ) (GeckConstruction.h (b := b) (R := R) i) =
      GeckConstruction.h (b := b₂) (τ i) := by
  rw [coe_reindexAlgEquiv, ← submatrix_geckIndexEquiv_h g τ hτ i, reindex_apply,
    submatrix_submatrix]
  simp

/-- Conjugation by the index permutation carries the raising matrix numbered by `i` to the one
numbered by `τ i`. -/
@[simp]
theorem reindex_geckIndexEquiv_e (i : b.support) :
    reindexAlgEquiv R R (geckIndexEquiv g τ) (GeckConstruction.e (b := b) (R := R) i) =
      GeckConstruction.e (b := b₂) (τ i) := by
  rw [coe_reindexAlgEquiv, ← submatrix_geckIndexEquiv_e g τ hτ i, reindex_apply,
    submatrix_submatrix]
  simp

/-- Conjugation by the index permutation carries the lowering matrix numbered by `i` to the one
numbered by `τ i`. -/
@[simp]
theorem reindex_geckIndexEquiv_f (i : b.support) :
    reindexAlgEquiv R R (geckIndexEquiv g τ) (GeckConstruction.f (b := b) (R := R) i) =
      GeckConstruction.f (b := b₂) (τ i) := by
  rw [coe_reindexAlgEquiv, ← submatrix_geckIndexEquiv_f g τ hτ i, reindex_apply,
    submatrix_submatrix]
  simp

/-! ## The equivalence of Geck's Lie algebras -/

/-- **Geck's Lie algebra is invariant under base-preserving equivalence of root pairings.**
Reindexing carries the Lie subalgebra spanned by the source numbered matrices onto the target one,
because it carries each of the three numbered families onto its target counterpart. -/
theorem map_lieAlgebra_geckIndexEquiv :
    (GeckConstruction.lieAlgebra b).map
        ((reindexAlgEquiv R R (geckIndexEquiv g τ)).toLieEquiv.toLieHom) =
      GeckConstruction.lieAlgebra b₂ := by
  have key : ∀ (m : b.support → Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)
      (m₂ : b₂.support → Matrix (b₂.support ⊕ ι₂) (b₂.support ⊕ ι₂) R),
      (∀ i, reindexAlgEquiv R R (geckIndexEquiv g τ) (m i) = m₂ (τ i)) →
      ⇑(reindexAlgEquiv R R (geckIndexEquiv g τ)).toLieEquiv.toLieHom '' range m = range m₂ := by
    intro m m₂ hm
    have hcomp : ⇑(reindexAlgEquiv R R (geckIndexEquiv g τ)).toLieEquiv.toLieHom ∘ m =
        m₂ ∘ τ := funext hm
    rw [← range_comp, hcomp, τ.surjective.range_comp]
  rw [GeckConstruction.lieAlgebra, LieSubalgebra.map_lieSpan]
  congr 1
  rw [image_union, image_union, key _ _ (reindex_geckIndexEquiv_h g τ hτ),
    key _ _ (reindex_geckIndexEquiv_e g τ hτ), key _ _ (reindex_geckIndexEquiv_f g τ hτ)]

/-- The equivalence of Geck's Lie algebras induced by a base-preserving equivalence of root
pairings: the restriction of matrix reindexing. -/
noncomputable def geckLieEquiv :
    GeckConstruction.lieAlgebra b ≃ₗ⁅R⁆ GeckConstruction.lieAlgebra b₂ :=
  LieEquiv.ofSubalgebras _ _ (reindexAlgEquiv R R (geckIndexEquiv g τ)).toLieEquiv
    (map_lieAlgebra_geckIndexEquiv g τ hτ)

@[simp]
theorem geckLieEquiv_apply (x : GeckConstruction.lieAlgebra b) :
    (geckLieEquiv g τ hτ x : Matrix (b₂.support ⊕ ι₂) (b₂.support ⊕ ι₂) R) =
      reindexAlgEquiv R R (geckIndexEquiv g τ) x :=
  LieEquiv.ofSubalgebras_apply _ _ _ _ x

end

section

variable [Fintype ι] [Fintype ι₂]

omit [Finite ι] [Finite ι₂] [IsDomain R] in
/-- The coordinate permutation carries the action of the Cartan matrix numbered by `i` to the
action of the one numbered by `τ i`. -/
@[simp]
theorem geckModuleEquiv_mulVec_h (i : b.support) (v : (b.support ⊕ ι) → R) :
    geckModuleEquiv g τ (GeckConstruction.h (b := b) (R := R) i *ᵥ v) =
      GeckConstruction.h (b := b₂) (τ i) *ᵥ geckModuleEquiv g τ v := by
  classical
  rw [geckModuleEquiv_mulVec, reindex_geckIndexEquiv_h g τ hτ]

/-- The coordinate permutation carries the action of the raising matrix numbered by `i` to the
action of the one numbered by `τ i`. This is the intertwining relation that a numbered symmetry of
the Kostant data is built from. -/
@[simp]
theorem geckModuleEquiv_mulVec_e (i : b.support) (v : (b.support ⊕ ι) → R) :
    geckModuleEquiv g τ (GeckConstruction.e (b := b) (R := R) i *ᵥ v) =
      GeckConstruction.e (b := b₂) (τ i) *ᵥ geckModuleEquiv g τ v := by
  classical
  rw [geckModuleEquiv_mulVec, reindex_geckIndexEquiv_e g τ hτ]

/-- The coordinate permutation carries the action of the lowering matrix numbered by `i` to the
action of the one numbered by `τ i`. -/
@[simp]
theorem geckModuleEquiv_mulVec_f (i : b.support) (v : (b.support ⊕ ι) → R) :
    geckModuleEquiv g τ (GeckConstruction.f (b := b) (R := R) i *ᵥ v) =
      GeckConstruction.f (b := b₂) (τ i) *ᵥ geckModuleEquiv g τ v := by
  classical
  rw [geckModuleEquiv_mulVec, reindex_geckIndexEquiv_f g τ hτ]

end

end Numbered

section Automorphism

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}
  (g : P.Equiv P) (τ : b.support ≃ b.support)
  (hτ : ∀ i : b.support, (τ i : ι) = g.indexEquiv i)
  [DecidableEq ι] [Fintype ι]

/-- The automorphism of Geck's Lie algebra induced by a base-preserving automorphism of the root
pairing. -/
noncomputable def geckLieAut :
    GeckConstruction.lieAlgebra b ≃ₗ⁅R⁆ GeckConstruction.lieAlgebra b :=
  geckLieEquiv g τ hτ

@[simp]
theorem geckLieAut_apply (x : GeckConstruction.lieAlgebra b) :
    (geckLieAut g τ hτ x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) =
      reindexAlgEquiv R R (geckIndexEquiv g τ) x :=
  geckLieEquiv_apply g τ hτ x

end Automorphism

end TauCeti
