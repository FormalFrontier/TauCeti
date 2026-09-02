/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.BlockDiagonal
public import TauCeti.Combinatorics.Young.Cells

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
of cells of `D` in row `s`. And if `D` is a row lower set — containing with every cell the cells
directly above it, which is the closure in the row direction that the raising operators need —
then every raising operator `Eₛₜ` with `s < t` annihilates the wedge by
`exteriorPower.lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem`, since moving a cell from row
`t` up to row `s` lands on a cell already present.

The weight read off this way is the row-length function of `D`. Taking `κ = Fin m` and `D` the
Young diagram `TauCeti.CellDiagram.ofRowLens a m` of a weakly decreasing `a : ι → ℕ`, and taking
`m` with `∀ i, a i ≤ m`, the row lengths are the `a i` themselves, which realizes `a` as a highest
weight.

## Main results

* `TauCeti.isGlHighestWeightVector_basisWedge`: **the wedge of a row lower set of cells is a
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
promoted to an `AlgHom`, and then viewed as a `LieHom`. It need not be injective when `κ` is empty,
so it is a map rather than an embedding.

A single-column diagram gives back the fundamental weights: for `κ` a singleton, the row lower
set of the first `d` rows is the wedge `exteriorPower.firstBasisWedge`, transported along
`ι × κ ≃ ι`. The two are not literally the same declaration because the ambient index types differ,
and it is the second coordinate — absent there — that lets a row be repeated, which is what a
general weakly decreasing tuple needs.

The cells of a diagram are wedged together in the order `exteriorPower.basisWedge` reads off the
linear order on `ι × κ`, and that order is a parameter of the results below: nothing depends on the
choice, since a different order permutes the factors and changes the wedge by a sign, which affects
neither being nonzero nor being a highest weight vector. Only
`TauCeti.exists_isGlHighestWeightVector_natCast`, which has to produce a witness, picks one, and it
picks the lexicographic order, supplied as a local instance.

## References

* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §5.5 and §9.1,
  where the modules of the classical groups are realized inside exterior powers of `Kⁿ ⊗ Kᵐ`.
* W. Fulton, J. Harris, *Representation Theory: A First Course*, GTM 129, §15.5.
-/

namespace TauCeti

open Matrix Module exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Row lower sets of cells give highest weight vectors -/

section Wedge

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ] [LinearOrder (ι × κ)]

open CellDiagram

/-- The diagonal matrix unit `Eᵢᵢ` scales the wedge of a set of cells by the number of cells the
set has in row `i`. -/
@[simp]
theorem gl_lie_single_self_basisWedge {N : ℕ} (D : Finset (ι × κ)) (h : D.card = N) (i : ι) :
    ⁅(single i i 1 : Matrix ι ι R), basisWedge R D h⁆ = (rowLen D i : R) • basisWedge R D h := by
  rw [gl_lie_single]
  simp only [lie_single_self_basisWedge, ← Finset.sum_smul, Finset.sum_boole]
  rw [rowLen_eq_card_filter_mem]

/-- The raising matrix units annihilate the wedge of a row lower set of cells: moving a cell
up lands on a cell that is already there, so every summand has a repeated factor. -/
theorem gl_lie_single_basisWedge_eq_zero_of_isRowLowerSet_of_lt {N : ℕ}
    {D : Finset (ι × κ)} (h : D.card = N) (hD : IsRowLowerSet D) {s t : ι} (hst : s < t) :
    ⁅(single s t 1 : Matrix ι ι R), basisWedge R D h⁆ = 0 := by
  rw [gl_lie_single]
  refine Finset.sum_eq_zero fun c _ => ?_
  refine lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem D h
    (fun hc => hst.ne (congrArg Prod.fst hc)) fun hmem => ?_
  exact isRowLowerSet_iff.1 hD _ hmem s hst

/-- **The wedge of a row lower set of cells is a highest weight vector** for `gl ι`, of
weight the row lengths of the set. -/
theorem isGlHighestWeightVector_basisWedge [Nontrivial R] {N : ℕ} {D : Finset (ι × κ)}
    (h : D.card = N) (hD : IsRowLowerSet D) :
    IsGlHighestWeightVector (fun i => (rowLen D i : R)) (basisWedge R D h) :=
  isGlHighestWeightVector_iff.mpr ⟨basisWedge_ne_zero D h,
    fun i => gl_lie_single_self_basisWedge D h i,
    fun _ _ hst => gl_lie_single_basisWedge_eq_zero_of_isRowLowerSet_of_lt h hD hst⟩

end Wedge

/-! ### Young diagrams -/

section YoungDiagram

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

open CellDiagram

/-- **The wedge of a Young diagram is a highest weight vector of the weight the diagram
prescribes.** Its exterior degree is the size `∑ i, a i` of the diagram. -/
theorem isGlHighestWeightVector_basisWedge_ofRowLens [Nontrivial R] {a : ι → ℕ} (ha : Antitone a)
    {m : ℕ} [LinearOrder (ι × Fin m)] (hm : ∀ i, a i ≤ m) :
    IsGlHighestWeightVector (fun i => (a i : R))
      (basisWedge R (ofRowLens a m) (card_ofRowLens_of_le hm)) := by
  have hweight : (fun i => ((rowLen (ofRowLens a m) i : ℕ) : R)) = fun i => ((a i : ℕ) : R) :=
    funext fun i => by rw [rowLen_ofRowLens_of_le hm]
  rw [← hweight]
  exact isGlHighestWeightVector_basisWedge _ (isRowLowerSet_ofRowLens ha m)

/-- The lexicographic order on the cells, used only to fix the order of the wedge factors in the
existential witness below. -/
local instance cellFinLinearOrder {m : ℕ} : LinearOrder (ι × Fin m) :=
  LinearOrder.lift' (⇑(toLex : (ι × Fin m) ≃ ι ×ₗ Fin m)) (Equiv.injective _)

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
