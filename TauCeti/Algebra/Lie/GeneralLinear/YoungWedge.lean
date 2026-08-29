/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.ExteriorPower

import Mathlib.LinearAlgebra.ExteriorPower.Basis

public section

/-!
# Highest weight vectors of `gl ι` from Young diagrams

Every weakly decreasing tuple of natural numbers is the weight of a highest weight vector in a
finite-dimensional `gl ι`-module. The module is a single exterior power, and the vector is a wedge
of standard basis vectors indexed by the cells of a Young diagram.

## The construction

Let `κ` index a second, auxiliary coordinate, so that `ι × κ → R` is the standard module of
`gl (ι × κ)` and `gl ι` acts on it through the block-diagonal embedding `TauCeti.glBlockDiagonal`,
which sends `A` to `Matrix.blockDiagonal fun _ : κ => A`. Concretely the matrix unit `Eₛₜ` sends
the standard basis vector `e₍ₚ,ᵣ₎` to `e₍ₛ,ᵣ₎` when `t = p`, and to `0` otherwise: it moves a cell
from row `t` to row `s` and leaves its column alone.

For a finite set of cells `D ⊆ ι × κ` the wedge `TauCeti.glDiagramWedge R D` of the basis vectors
`e_p`, `p ∈ D`, is then a weight vector for the diagonal: `Eₛₛ` fixes each of its factors lying in
row `s` and kills the others, so it scales the wedge by the number of cells of `D` in row `s`. And
if `D` is **row closed** — with every cell it contains the cells directly above it, which is
exactly the shape of a Young diagram — the wedge is annihilated by every raising operator `Eₛₜ`
with `s < t`: moving a cell from row `t` up to row `s` lands on a cell already present, so every
summand of the Leibniz expansion is a wedge with a repeated factor.

The weight read off this way is the row-count function of `D`. Taking `κ = Fin m` and `D` the Young
diagram `{(i, c) | c < a i}` of a weakly decreasing `a : ι → ℕ`, the row counts are the `a i`
themselves, which realizes `a` as a highest weight.

## Main definitions

* `TauCeti.glBlockDiagonal`: the block-diagonal embedding of `gl ι` in `gl (ι × κ)`, together
  with the `gl ι`-module structure it induces on the exterior powers of `ι × κ → R`.
* `TauCeti.glDiagramWedge`: the wedge of the standard basis vectors indexed by a finite set of
  cells, and `TauCeti.rowCard`, the number of cells in a row.
* `TauCeti.IsRowClosed`: the Young-diagram shape condition on a finite set of cells.
* `TauCeti.youngCells`: the Young diagram of a tuple of row lengths, as a finite set of cells.

## Main results

* `TauCeti.isGlHighestWeightVector_glDiagramWedge`: **the wedge of a row-closed set of cells is a
  highest weight vector**, of weight the row counts of the set.
* `TauCeti.isGlHighestWeightVector_glDiagramWedge_youngCells` and
  `TauCeti.exists_isGlHighestWeightVector_natCast`: **every weakly decreasing tuple of natural
  numbers is a highest weight** of a finite-dimensional `gl ι`-module.

## Roadmap context

Layer 9 of the
[highest weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
asks for the finite-dimensional irreducible `gl n`-module of each dominant weight.
`TauCeti.exists_isGlHighestWeightVector_natCast` supplies highest weight vectors for the dominant
weights with natural number entries, the existence input to that classification;
`TauCeti.nonempty_lieModuleEquiv_of_isGlHighestWeightVector` and
`TauCeti.finrank_le_of_isGlHighestWeightVector` are the uniqueness half, already proved.

## Implementation notes

Mathlib's `YoungDiagram` is a set of cells in `ℕ × ℕ` closed downwards in *both* directions, and
its rows are indexed by `ℕ`. The rows here are indexed by the abstract `gl` index type `ι`, and
only closure in the row direction is needed — that is precisely what makes the raising operators
act by zero — so the diagrams below are plain finite sets of cells with
`TauCeti.IsRowClosed` imposed where it is used.

`TauCeti.glBlockDiagonal` is the constant family map followed by `Matrix.blockDiagonalRingHom`,
but it is packaged directly as a `LieHom` rather than through `AlgHom.toLieHom`, since only the
multiplicativity lemma `Matrix.blockDiagonal_mul` is needed and no unit or `algebraMap` bookkeeping.

A single-column diagram gives back the fundamental weights: for `κ` a singleton, the row-closed set
of the first `d` rows is the wedge `exteriorPower.firstBasisWedge`, transported along
`ι × κ ≃ ι`. The two are not literally the same declaration because the ambient index types differ,
and it is the second coordinate — absent there — that lets a row be repeated, which is what a
general weakly decreasing tuple needs.

The cells of a diagram are wedged together in the order they receive from `Finset.orderEmbOfFin`,
which needs a linear order on `ι × κ`; the lexicographic one is used, as a local instance, purely
to fix that order, and `TauCeti.cellEmb` forgets it again. Nothing below depends on the choice: a
different order permutes the factors and changes the wedge by a sign, which affects neither being
nonzero nor being a highest weight vector.

## References

* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §5.5 and §9.1,
  where the modules of the classical groups are realized inside exterior powers of `Kⁿ ⊗ Kᵐ`.
* W. Fulton, J. Harris, *Representation Theory: A First Course*, GTM 129, §15.5.
-/

namespace TauCeti

open Matrix Module exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The block-diagonal embedding of `gl ι` in `gl (ι × κ)` -/

section BlockDiagonal

variable (R : Type*) [CommRing R]
variable (ι : Type*) [DecidableEq ι] [Fintype ι]
variable (κ : Type*) [DecidableEq κ] [Fintype κ]

/-- The **block-diagonal embedding** of `gl ι` in `gl (ι × κ)`, sending a matrix `A` to the block
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

/-- A matrix unit of `gl ι`, acting through the block-diagonal embedding, moves a cell of the
standard basis of `ι × κ → R` from row `p.1` to row `s`. -/
theorem glBlockDiagonal_single_mulVec_of_eq (s t : ι) {p : ι × κ} (h : t = p.1) :
    glBlockDiagonal R ι κ (single s t 1) *ᵥ (Pi.single p 1 : ι × κ → R)
      = Pi.single (s, p.2) 1 := by
  subst h
  ext q
  simp only [glBlockDiagonal_apply, mulVec_single_one, Matrix.col_apply, blockDiagonal_apply,
    single_apply, Pi.single_apply, Prod.ext_iff]
  by_cases hq : q.2 = p.2
  · by_cases hs : q.1 = s
    · simp [hq, hs]
    · simp [hq, hs, Ne.symm hs]
  · simp [hq]

/-- A matrix unit of `gl ι`, acting through the block-diagonal embedding, kills the cells of the
standard basis of `ι × κ → R` lying outside its source row. -/
theorem glBlockDiagonal_single_mulVec_of_ne (s t : ι) {p : ι × κ} (h : t ≠ p.1) :
    glBlockDiagonal R ι κ (single s t 1) *ᵥ (Pi.single p 1 : ι × κ → R) = 0 := by
  ext q
  simp only [glBlockDiagonal_apply, mulVec_single_one, Matrix.col_apply, blockDiagonal_apply,
    single_apply, Pi.zero_apply]
  by_cases hq : q.2 = p.2 <;> simp [hq, h]

/-! ### The `gl ι`-module structure on exterior powers of `ι × κ → R` -/

variable (R ι κ) in
/-- The `gl ι`-module structure on an exterior power of `ι × κ → R`, pulled back along the
block-diagonal embedding from the standard `gl (ι × κ)`-action. -/
noncomputable scoped instance glBlockDiagonalLieRingModule (N : ℕ) :
    LieRingModule (Matrix ι ι R) (⋀[R]^N (ι × κ → R)) :=
  LieRingModule.compLieHom _ (glBlockDiagonal R ι κ)

variable (R ι κ) in
/-- The `gl ι`-module structure on an exterior power of `ι × κ → R`, pulled back along the
block-diagonal embedding from the standard `gl (ι × κ)`-action. -/
noncomputable scoped instance glBlockDiagonalLieModule (N : ℕ) :
    LieModule R (Matrix ι ι R) (⋀[R]^N (ι × κ → R)) :=
  LieModule.compLieHom _ (glBlockDiagonal R ι κ)

/-- The `gl ι`-action on an exterior power of `ι × κ → R` is the `gl (ι × κ)`-action of the
block-diagonal image. -/
theorem gl_lie_blockDiagonal_def {N : ℕ} (A : Matrix ι ι R) (x : ⋀[R]^N (ι × κ → R)) :
    ⁅A, x⁆ = ⁅glBlockDiagonal R ι κ A, x⁆ :=
  LieRingModule.compLieHom_apply _ _ _ _

/-- A matrix of `gl ι` acts on a decomposable wedge in `⋀^N (ι × κ → R)` by acting on one factor at
a time. -/
theorem gl_lie_ιMulti {N : ℕ} (A : Matrix ι ι R) (v : Fin N → (ι × κ → R)) :
    ⁅A, ιMulti R N v⁆ =
      ∑ k : Fin N, ιMulti R N (Function.update v k (glBlockDiagonal R ι κ A *ᵥ v k)) := by
  rw [gl_lie_blockDiagonal_def, gl_lie_def, glLieMap_apply_ιMulti]

end BlockDiagonal

/-! ### Enumerating a finite set of cells -/

section Cells

variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- The lexicographic order on cells. It is used only to enumerate a finite set of cells in a fixed
order when wedging their basis vectors together. -/
@[instance_reducible]
def cellLinearOrder : LinearOrder (ι × κ) :=
  LinearOrder.lift' (⇑(toLex : (ι × κ) ≃ ι ×ₗ κ)) (Equiv.injective _)

attribute [local instance] cellLinearOrder

/-- The enumeration of a finite set of cells in lexicographic order, in which their basis vectors
are wedged together by `TauCeti.glDiagramWedge`. -/
noncomputable def cellEmb (D : Finset (ι × κ)) : Fin D.card ↪ (ι × κ) :=
  (D.orderEmbOfFin rfl).toEmbedding

private theorem cellEmb_apply (D : Finset (ι × κ)) (k : Fin D.card) :
    cellEmb D k = D.orderEmbOfFin rfl k :=
  (rfl)

@[simp]
theorem cellEmb_mem (D : Finset (ι × κ)) (k : Fin D.card) : cellEmb D k ∈ D := by
  rw [cellEmb_apply]
  exact D.orderEmbOfFin_mem rfl k

/-- Every cell of `D` is enumerated by `TauCeti.cellEmb`. -/
theorem exists_cellEmb_eq {D : Finset (ι × κ)} {p : ι × κ} (hp : p ∈ D) :
    ∃ k, cellEmb D k = p := by
  have hrange : p ∈ Set.range (D.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_coe.2 hp
  obtain ⟨k, hk⟩ := hrange
  exact ⟨k, (cellEmb_apply D k).trans hk⟩

end Cells

/-! ### The wedge of a set of cells -/

section Wedge

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [Fintype κ] [LinearOrder κ]

attribute [local instance] cellLinearOrder

variable (R) in
/-- The wedge of the standard basis vectors indexed by a finite set `D` of cells, an element of the
`D.card`-th exterior power of `ι × κ → R`. -/
noncomputable def glDiagramWedge (D : Finset (ι × κ)) : ⋀[R]^D.card (ι × κ → R) :=
  ιMulti R D.card fun k => Pi.single (cellEmb D k) 1

omit [Fintype ι] [Fintype κ] in
/-- The wedge of a set of cells, unfolded. -/
@[simp]
theorem glDiagramWedge_eq_ιMulti (D : Finset (ι × κ)) :
    glDiagramWedge R D = ιMulti R D.card fun k => Pi.single (cellEmb D k) 1 := by
  rw [glDiagramWedge]

omit [Fintype ι] [Fintype κ] in
/-- The wedge of a set of cells is the member of the standard basis of the exterior power that the
set indexes. -/
theorem glDiagramWedge_eq_ιMulti_family [Finite ι] [Finite κ] (D : Finset (ι × κ)) :
    glDiagramWedge R D
      = ιMulti_family (I := ι × κ) R D.card (Pi.basisFun R (ι × κ)) ⟨D, rfl⟩ := by
  rw [glDiagramWedge_eq_ιMulti, ιMulti_family]
  refine congrArg (ιMulti R D.card) (funext fun k => ?_)
  simp [Pi.basisFun_apply, cellEmb, Set.powersetCard.ofFinEmbEquiv_symm_apply]

omit [Fintype ι] [Fintype κ] in
/-- The wedge of a set of cells is nonzero. -/
theorem glDiagramWedge_ne_zero [Nontrivial R] [Finite ι] [Finite κ] (D : Finset (ι × κ)) :
    glDiagramWedge R D ≠ 0 := by
  have h := (ιMulti_family_linearIndependent_ofBasis (I := ι × κ) R D.card
    (Pi.basisFun R (ι × κ))).ne_zero (⟨D, rfl⟩ : ↥(Set.powersetCard (ι × κ) D.card))
  rwa [glDiagramWedge_eq_ιMulti_family]

/-! ### Row-closed sets of cells give highest weight vectors -/

/-- The number of cells of `D` in row `i`. It is the `i`-th entry of the weight of
`TauCeti.glDiagramWedge R D`. -/
def rowCard (D : Finset (ι × κ)) (i : ι) : ℕ :=
  (D.filter fun p => p.1 = i).card

omit [Fintype ι] [Fintype κ] in
private theorem card_filter_cellEmb_eq (D : Finset (ι × κ)) (i : ι) :
    (Finset.univ.filter fun k => (cellEmb D k).1 = i).card = rowCard D i := by
  rw [rowCard, ← Finset.card_image_of_injective _ (cellEmb D).injective]
  refine congrArg Finset.card (Finset.ext fun p => ?_)
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨cellEmb_mem D k, hk⟩
  · rintro ⟨hp, hpi⟩
    obtain ⟨k, rfl⟩ := exists_cellEmb_eq hp
    exact ⟨k, hpi, rfl⟩

/-- The diagonal matrix unit `Eᵢᵢ` scales the wedge of a set of cells by the number of cells the
set has in row `i`. -/
theorem lie_single_self_glDiagramWedge (D : Finset (ι × κ)) (i : ι) :
    ⁅(single i i 1 : Matrix ι ι R), glDiagramWedge R D⁆ =
      (rowCard D i : R) • glDiagramWedge R D := by
  classical
  rw [glDiagramWedge_eq_ιMulti, gl_lie_ιMulti,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ fun k => (cellEmb D k).1 = i]
  have hmem : ∀ k ∈ Finset.univ.filter fun k => (cellEmb D k).1 = i,
      ιMulti R D.card (Function.update (fun k => (Pi.single (cellEmb D k) 1 : ι × κ → R)) k
          (glBlockDiagonal R ι κ (single i i 1) *ᵥ Pi.single (cellEmb D k) 1))
        = ιMulti R D.card fun k => (Pi.single (cellEmb D k) 1 : ι × κ → R) := by
    intro k hk
    have hki : (cellEmb D k).1 = i := (Finset.mem_filter.1 hk).2
    have hcell : ((i, (cellEmb D k).2) : ι × κ) = cellEmb D k := by rw [← hki]
    rw [glBlockDiagonal_single_mulVec_of_eq i i hki.symm, hcell, Function.update_eq_self]
  have hnotMem : ∀ k ∈ Finset.univ.filter fun k => ¬(cellEmb D k).1 = i,
      ιMulti R D.card (Function.update (fun k => (Pi.single (cellEmb D k) 1 : ι × κ → R)) k
          (glBlockDiagonal R ι κ (single i i 1) *ᵥ Pi.single (cellEmb D k) 1)) = 0 := by
    intro k hk
    rw [glBlockDiagonal_single_mulVec_of_ne i i fun h => (Finset.mem_filter.1 hk).2 h.symm]
    exact (ιMulti R D.card).map_update_zero _ _
  rw [Finset.sum_congr rfl hmem, Finset.sum_congr rfl hnotMem, Finset.sum_const_zero, add_zero,
    Finset.sum_const, card_filter_cellEmb_eq, ← Nat.cast_smul_eq_nsmul R]

/-- A set of cells is **row closed** when with every cell it contains all the cells directly above
it: if `(j, c)` is a cell and `i < j`, then `(i, c)` is a cell. This is the shape condition on a
Young diagram, and it is what makes the raising operators annihilate
`TauCeti.glDiagramWedge R D`. -/
def IsRowClosed (D : Finset (ι × κ)) : Prop :=
  ∀ p ∈ D, ∀ i : ι, i < p.1 → (i, p.2) ∈ D

/-- The raising matrix units annihilate the wedge of a row-closed set of cells: moving a cell up
lands on a cell that is already there, so every summand has a repeated factor. -/
theorem lie_single_glDiagramWedge_of_lt {D : Finset (ι × κ)} (hD : IsRowClosed D) {s t : ι}
    (hst : s < t) : ⁅(single s t 1 : Matrix ι ι R), glDiagramWedge R D⁆ = 0 := by
  classical
  rw [glDiagramWedge_eq_ιMulti, gl_lie_ιMulti]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases htk : t = (cellEmb D k).1
  · obtain ⟨l, hl⟩ := exists_cellEmb_eq (hD _ (cellEmb_mem D k) s (htk ▸ hst))
    have hlk : l ≠ k := by
      rintro rfl
      exact hst.ne' (htk.trans (congrArg Prod.fst hl))
    rw [glBlockDiagonal_single_mulVec_of_eq s t htk]
    refine (ιMulti R D.card).map_eq_zero_of_eq
      (Function.update (fun k => (Pi.single (cellEmb D k) (1 : R) : ι × κ → R)) k
        (Pi.single (s, (cellEmb D k).2) 1)) (i := l) (j := k) ?_ hlk
    rw [Function.update_of_ne hlk, Function.update_self, hl]
  · rw [glBlockDiagonal_single_mulVec_of_ne s t htk]
    exact (ιMulti R D.card).map_update_zero _ _

/-- **The wedge of a row-closed set of cells is a highest weight vector** for `gl ι`, of weight the
row counts of the set. -/
theorem isGlHighestWeightVector_glDiagramWedge [Nontrivial R] {D : Finset (ι × κ)}
    (hD : IsRowClosed D) :
    IsGlHighestWeightVector (fun i => (rowCard D i : R)) (glDiagramWedge R D) :=
  isGlHighestWeightVector_iff.mpr ⟨glDiagramWedge_ne_zero D,
    fun i => lie_single_self_glDiagramWedge D i,
    fun _ _ hst => lie_single_glDiagramWedge_of_lt hD hst⟩

end Wedge

/-! ### Young diagrams -/

section YoungDiagram

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

attribute [local instance] cellLinearOrder

/-- The **Young diagram** of a tuple `a : ι → ℕ` of row lengths, as the set of cells `(i, c)` whose
column index `c` is smaller than the `i`-th row length. -/
def youngCells (a : ι → ℕ) (m : ℕ) : Finset (ι × Fin m) :=
  Finset.univ.filter fun p => (p.2 : ℕ) < a p.1

omit [LinearOrder ι] in
@[simp]
theorem mem_youngCells_iff {a : ι → ℕ} {m : ℕ} {p : ι × Fin m} :
    p ∈ youngCells a m ↔ (p.2 : ℕ) < a p.1 := by
  simp [youngCells]

/-- A Young diagram is row closed exactly because its row lengths are weakly decreasing. -/
theorem isRowClosed_youngCells {a : ι → ℕ} (ha : Antitone a) (m : ℕ) :
    IsRowClosed (youngCells a m) := by
  intro p hp i hi
  have hlt : (p.2 : ℕ) < a p.1 := mem_youngCells_iff.1 hp
  exact mem_youngCells_iff.2 (lt_of_lt_of_le hlt (ha hi.le))

/-- The rows of the Young diagram of `a` have the lengths `a` prescribes, as soon as the diagram is
wide enough to hold them. -/
theorem rowCard_youngCells {a : ι → ℕ} {m : ℕ} (hm : ∀ i, a i ≤ m) (i : ι) :
    rowCard (youngCells a m) i = a i := by
  classical
  have himage : (youngCells a m).filter (fun p => p.1 = i)
      = Finset.univ.image fun c : Fin (a i) => ((i, Fin.castLE (hm i) c) : ι × Fin m) := by
    refine Finset.ext fun p => ?_
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, mem_youngCells_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨hlt, rfl⟩
      exact ⟨⟨p.2, hlt⟩, by simp⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c.isLt, rfl⟩
  rw [rowCard, himage, Finset.card_image_of_injective _ fun c d h =>
      Fin.castLE_injective (hm i) (congrArg Prod.snd h),
    Finset.card_univ, Fintype.card_fin]

/-- The Young diagram of `a` has one cell for each unit of each row length. -/
theorem card_youngCells {a : ι → ℕ} {m : ℕ} (hm : ∀ i, a i ≤ m) :
    (youngCells a m).card = ∑ i, a i := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ι × Fin m => p.1) (t := Finset.univ)
    fun _ _ => Finset.mem_univ _]
  exact Finset.sum_congr rfl fun i _ => rowCard_youngCells hm i

/-- **The wedge of a Young diagram is a highest weight vector of the weight the diagram
prescribes.** -/
theorem isGlHighestWeightVector_glDiagramWedge_youngCells [Nontrivial R] {a : ι → ℕ}
    (ha : Antitone a) {m : ℕ} (hm : ∀ i, a i ≤ m) :
    IsGlHighestWeightVector (fun i => (a i : R)) (glDiagramWedge R (youngCells a m)) := by
  have hweight : (fun i => ((rowCard (youngCells a m) i : ℕ) : R)) = fun i => ((a i : ℕ) : R) :=
    funext fun i => by rw [rowCard_youngCells hm]
  rw [← hweight]
  exact isGlHighestWeightVector_glDiagramWedge (isRowClosed_youngCells ha m)

/-- **Every weakly decreasing tuple of natural numbers is a highest weight** of `gl ι`: it is the
weight of a highest weight vector in the exterior power `⋀^|a| (ι × Fin m → R)` of the standard
module of `gl (ι × Fin m)`, which is a finite `R`-module by `exteriorPower.instFinite`. Its
exterior degree is the size `∑ i, a i` of the Young diagram, by `TauCeti.card_youngCells`. -/
theorem exists_isGlHighestWeightVector_natCast [Nontrivial R] {a : ι → ℕ} (ha : Antitone a)
    {m : ℕ} (hm : ∀ i, a i ≤ m) :
    ∃ v : ⋀[R]^((youngCells a m).card) (ι × Fin m → R),
      IsGlHighestWeightVector (fun i => (a i : R)) v :=
  ⟨_, isGlHighestWeightVector_glDiagramWedge_youngCells ha hm⟩

end YoungDiagram

end TauCeti
