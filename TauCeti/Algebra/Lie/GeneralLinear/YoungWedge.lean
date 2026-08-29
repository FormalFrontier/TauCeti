/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.ExteriorPower
public import TauCeti.Combinatorics.Young.Cells

import Mathlib.LinearAlgebra.ExteriorPower.Basis

public section

/-!
# Highest weight vectors of `gl ι` from Young diagrams

Every weakly decreasing tuple of natural numbers is the weight of a highest weight vector in a
`gl ι`-module finite over the base ring. The module is a single exterior power, and the vector is
a wedge of standard basis vectors indexed by the cells of a Young diagram.

## The construction

Let `κ` index a second, auxiliary coordinate, so that `ι × κ → R` is the standard module of
`gl (ι × κ)` and `gl ι` acts on it through the block-diagonal map `TauCeti.glBlockDiagonal`, which
sends `A` to `Matrix.blockDiagonal fun _ : κ => A`. Concretely the matrix unit `Eₛₜ` of `gl ι` goes
to the sum `∑ c, E₍ₛ,c₎₍ₜ,c₎` of the matrix units of `gl (ι × κ)` that move a cell from row `t` to
row `s` and leave its column alone (`TauCeti.glBlockDiagonal_single`).

For a finite set of cells `D ⊆ ι × κ` the wedge `exteriorPower.basisWedge R D` of the standard
basis vectors `e_p`, `p ∈ D`, is then a weight vector for the diagonal: summing
`exteriorPower.lie_single_self_basisWedge` over the columns, `Eₛₛ` scales the wedge by the number
of cells of `D` in row `s`. And if `D` is row lower closed — containing with every cell the cells
directly above it, which is exactly the shape of a Young diagram — then every raising operator
`Eₛₜ` with `s < t` annihilates the wedge by `exteriorPower.lie_single_basisWedge_of_ne`, since
moving a cell from row `t` up to row `s` lands on a cell already present.

The weight read off this way is the row-length function of `D`. Taking `κ = Fin m` and `D` the
Young diagram `TauCeti.CellDiagram.ofRowLens a m` of a weakly decreasing `a : ι → ℕ`, the row
lengths are the `a i` themselves, which realizes `a` as a highest weight.

## Main definitions

* `TauCeti.glBlockDiagonal`: the block-diagonal map from `gl ι` to `gl (ι × κ)`, together with the
  `gl ι`-module structure it induces on the exterior powers of `ι × κ → R`.
* `TauCeti.prodLexLinearOrder`: the lexicographic order on `ι × κ`, which fixes the order in which
  the basis vectors of a set of cells are wedged together.

## Main results

* `TauCeti.isGlHighestWeightVector_basisWedge`: **the wedge of a row lower closed set of cells is a
  highest weight vector**, of weight the row lengths of the set.
* `TauCeti.isGlHighestWeightVector_basisWedge_ofRowLens` and
  `TauCeti.exists_isGlHighestWeightVector_natCast`: **every weakly decreasing tuple of natural
  numbers is a highest weight** of a `gl ι`-module finite over `R`.

## Roadmap context

Layer 9 of the
[highest weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
asks for the finite-dimensional irreducible `gl n`-module of each dominant weight.
`TauCeti.exists_isGlHighestWeightVector_natCast` supplies highest weight vectors for the dominant
weights with natural number entries, the existence input to that classification;
`TauCeti.nonempty_lieModuleEquiv_of_isGlHighestWeightVector` and
`TauCeti.finrank_le_of_isGlHighestWeightVector` are the uniqueness half, already proved.

## Implementation notes

`TauCeti.glBlockDiagonal` is the constant family map followed by `Matrix.blockDiagonalRingHom`,
but it is packaged directly as a `LieHom` rather than through `AlgHom.toLieHom`, since only the
multiplicativity lemma `Matrix.blockDiagonal_mul` is needed and no unit or `algebraMap` bookkeeping.
It is not injective when `κ` is empty, so it is a map rather than an embedding.

A single-column diagram gives back the fundamental weights: for `κ` a singleton, the row lower
closed set of the first `d` rows is the wedge `exteriorPower.firstBasisWedge`, transported along
`ι × κ ≃ ι`. The two are not literally the same declaration because the ambient index types differ,
and it is the second coordinate — absent there — that lets a row be repeated, which is what a
general weakly decreasing tuple needs.

The cells of a diagram are wedged together in the order `exteriorPower.basisWedge` reads off the
linear order on `ι × κ`; the lexicographic one is used, as a local instance, purely to fix that
order. Nothing below depends on the choice: a different order permutes the factors and changes the
wedge by a sign, which affects neither being nonzero nor being a highest weight vector.

## References

* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §5.5 and §9.1,
  where the modules of the classical groups are realized inside exterior powers of `Kⁿ ⊗ Kᵐ`.
* W. Fulton, J. Harris, *Representation Theory: A First Course*, GTM 129, §15.5.
-/

namespace TauCeti

open Matrix Module exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The block-diagonal map from `gl ι` to `gl (ι × κ)` -/

section BlockDiagonal

variable (R : Type*) [CommRing R]
variable (ι : Type*) [DecidableEq ι] [Fintype ι]
variable (κ : Type*) [DecidableEq κ] [Fintype κ]

/-- The **block-diagonal map** from `gl ι` to `gl (ι × κ)`, sending a matrix `A` to the block
diagonal matrix with `κ` copies of `A` down the diagonal. On the standard module `ι × κ → R` this
is the action of `gl ι` on the first coordinate alone. -/
def glBlockDiagonal : Matrix ι ι R →ₗ⁅R⁆ Matrix (ι × κ) (ι × κ) R where
  toFun A := blockDiagonal fun _ : κ => A
  map_add' A B := by rw [← blockDiagonal_add]; rfl
  map_smul' c A := by rw [RingHom.id_apply, ← blockDiagonal_smul]; rfl
  map_lie' {A B} := by
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
      ← blockDiagonal_mul, ← blockDiagonal_mul, ← blockDiagonal_sub]
    rfl

@[simp]
theorem glBlockDiagonal_apply (A : Matrix ι ι R) :
    glBlockDiagonal R ι κ A = blockDiagonal fun _ : κ => A :=
  (rfl)

variable {R ι κ}

/-- The block-diagonal map takes a matrix unit of `gl ι` to the sum, over the auxiliary coordinate,
of the matrix units of `gl (ι × κ)` that move a cell from row `t` to row `s` and leave its column
alone. -/
theorem glBlockDiagonal_single (s t : ι) :
    glBlockDiagonal R ι κ (single s t 1) = ∑ c : κ, single (s, c) (t, c) (1 : R) := by
  ext p q
  rw [glBlockDiagonal_apply, blockDiagonal_apply, Matrix.sum_apply]
  by_cases hpq : p.2 = q.2
  · rw [ite_eq_left hpq, Finset.sum_eq_single p.2]
    · simp [single_apply, Prod.ext_iff, hpq, eq_comm]
    · intro c _ hc
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨hp, -⟩
      exact hc (congrArg Prod.snd hp)
    · exact fun hc => absurd (Finset.mem_univ p.2) hc
  · rw [ite_eq_right hpq]
    refine (Finset.sum_eq_zero fun c _ => Matrix.single_apply_of_ne _ _ _ _ _ ?_).symm
    rintro ⟨hp, hq⟩
    have hcp : c = p.2 := congrArg Prod.snd hp
    have hcq : c = q.2 := congrArg Prod.snd hq
    exact hpq (hcp.symm.trans hcq)

/-! ### The `gl ι`-module structure on exterior powers of `ι × κ → R` -/

variable (R ι κ) in
/-- The bracket of `gl ι` on an exterior power of `ι × κ → R`, pulled back along the block-diagonal
map from the standard `gl (ι × κ)`-action. -/
noncomputable scoped instance glBlockDiagonalLieRingModule (N : ℕ) :
    LieRingModule (Matrix ι ι R) (⋀[R]^N (ι × κ → R)) :=
  LieRingModule.compLieHom _ (glBlockDiagonal R ι κ)

variable (R ι κ) in
/-- The compatibility of that bracket with the `R`-module structures, making an exterior power of
`ι × κ → R` a `gl ι`-module over `R`. -/
noncomputable scoped instance glBlockDiagonalLieModule (N : ℕ) :
    LieModule R (Matrix ι ι R) (⋀[R]^N (ι × κ → R)) :=
  LieModule.compLieHom _ (glBlockDiagonal R ι κ)

/-- The `gl ι`-action on an exterior power of `ι × κ → R` is the `gl (ι × κ)`-action of the
block-diagonal image. -/
theorem gl_lie_blockDiagonal_def {N : ℕ} (A : Matrix ι ι R) (x : ⋀[R]^N (ι × κ → R)) :
    ⁅A, x⁆ = ⁅glBlockDiagonal R ι κ A, x⁆ :=
  LieRingModule.compLieHom_apply _ _ _ _

/-- A matrix unit of `gl ι` acts on an exterior power of `ι × κ → R` as the sum, over the auxiliary
coordinate, of the matrix units of `gl (ι × κ)` it is built from. -/
theorem gl_lie_single {N : ℕ} (s t : ι) (x : ⋀[R]^N (ι × κ → R)) :
    ⁅(single s t 1 : Matrix ι ι R), x⁆
      = ∑ c : κ, ⁅(single (s, c) (t, c) 1 : Matrix (ι × κ) (ι × κ) R), x⁆ := by
  rw [gl_lie_blockDiagonal_def, glBlockDiagonal_single, sum_lie]

end BlockDiagonal

/-! ### Ordering the cells -/

/-- The lexicographic order on `ι × κ`, transported from `ι ×ₗ κ`. It is used only to fix the order
in which the basis vectors indexed by a finite set of cells are wedged together. -/
@[instance_reducible]
def prodLexLinearOrder {ι κ : Type*} [LinearOrder ι] [LinearOrder κ] : LinearOrder (ι × κ) :=
  LinearOrder.lift' (⇑(toLex : (ι × κ) ≃ ι ×ₗ κ)) (Equiv.injective _)

/-! ### Row lower closed sets of cells give highest weight vectors -/

section Wedge

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [Fintype κ] [LinearOrder κ]

attribute [local instance] prodLexLinearOrder

open CellDiagram

/-- The diagonal matrix unit `Eᵢᵢ` scales the wedge of a set of cells by the number of cells the
set has in row `i`. -/
@[simp]
theorem gl_lie_single_self_basisWedge {N : ℕ} (D : Finset (ι × κ)) (h : D.card = N) (i : ι) :
    ⁅(single i i 1 : Matrix ι ι R), basisWedge R D h⁆ = (rowLen D i : R) • basisWedge R D h := by
  rw [gl_lie_single]
  simp only [lie_single_self_basisWedge, ← Finset.sum_smul, Finset.sum_boole]
  rw [rowLen_eq_card_filter_mem]

/-- The raising matrix units annihilate the wedge of a row lower closed set of cells: moving a cell
up lands on a cell that is already there, so every summand has a repeated factor. -/
theorem gl_lie_single_basisWedge_of_lt {N : ℕ} {D : Finset (ι × κ)} (h : D.card = N)
    (hD : IsRowLowerClosed D) {s t : ι} (hst : s < t) :
    ⁅(single s t 1 : Matrix ι ι R), basisWedge R D h⁆ = 0 := by
  rw [gl_lie_single]
  refine Finset.sum_eq_zero fun c _ => ?_
  refine lie_single_basisWedge_of_ne D h (fun hc => hst.ne (congrArg Prod.fst hc)) fun hmem => ?_
  exact isRowLowerClosed_iff.1 hD _ hmem s hst

/-- **The wedge of a row lower closed set of cells is a highest weight vector** for `gl ι`, of
weight the row lengths of the set. -/
theorem isGlHighestWeightVector_basisWedge [Nontrivial R] {N : ℕ} {D : Finset (ι × κ)}
    (h : D.card = N) (hD : IsRowLowerClosed D) :
    IsGlHighestWeightVector (fun i => (rowLen D i : R)) (basisWedge R D h) :=
  isGlHighestWeightVector_iff.mpr ⟨basisWedge_ne_zero D h,
    fun i => gl_lie_single_self_basisWedge D h i,
    fun _ _ hst => gl_lie_single_basisWedge_of_lt h hD hst⟩

end Wedge

/-! ### Young diagrams -/

section YoungDiagram

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

attribute [local instance] prodLexLinearOrder

open CellDiagram

/-- **The wedge of a Young diagram is a highest weight vector of the weight the diagram
prescribes.** Its exterior degree is the size `∑ i, a i` of the diagram. -/
theorem isGlHighestWeightVector_basisWedge_ofRowLens [Nontrivial R] {a : ι → ℕ} (ha : Antitone a)
    {m : ℕ} (hm : ∀ i, a i ≤ m) :
    IsGlHighestWeightVector (fun i => (a i : R))
      (basisWedge R (ofRowLens a m) (card_ofRowLens hm)) := by
  have hweight : (fun i => ((rowLen (ofRowLens a m) i : ℕ) : R)) = fun i => ((a i : ℕ) : R) :=
    funext fun i => by rw [rowLen_ofRowLens hm]
  rw [← hweight]
  exact isGlHighestWeightVector_basisWedge _ (isRowLowerClosed_ofRowLens ha m)

/-- **Every weakly decreasing tuple of natural numbers is a highest weight** of `gl ι`: it is the
weight of a highest weight vector in the exterior power `⋀^|a| (ι × Fin |a| → R)` of the standard
module of `gl (ι × Fin |a|)`, where `|a| = ∑ i, a i`, a module finite over `R` by
`exteriorPower.instFinite`. The auxiliary width is taken to be `|a|` itself, which is wide enough
to hold every row. -/
theorem exists_isGlHighestWeightVector_natCast [Nontrivial R] {a : ι → ℕ} (ha : Antitone a) :
    ∃ v : ⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R),
      IsGlHighestWeightVector (fun i => (a i : R)) v :=
  ⟨_, isGlHighestWeightVector_basisWedge_ofRowLens ha fun i =>
    Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩

end YoungDiagram

end TauCeti
