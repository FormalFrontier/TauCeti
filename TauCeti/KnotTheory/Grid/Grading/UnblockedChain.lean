/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Finsupp.Weight
public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The bigrading of the unblocked grid complex `GC⁻`

`Unblocked.lean` builds the unblocked grid complex `GC⁻`, the free module on grid states over
`R[V₀, …, V_{n-1}]`, and records how one rectangle counted by its differential moves the two
gradings of a grid state. This file fixes the bigrading those two records were made for and proves
that the unblocked differential is homogeneous for it.

The convention is the standard one: a variable `V_c` sits in `O`-Maslov degree `-2` and Alexander
degree `-1`, so the basis element `V^e · x` has bidegree

`(M_O(x) - 2 |e|, A(x) - |e|)`

for `|e|` the total degree of the exponent vector `e`. This is
`OddComponentGridDiagram.monomialBidegree`; the Alexander grading is an integer exactly for a
diagram with an odd number of link components, which is why the bigraded statements are made for
`OddComponentGridDiagram`, matching `Grading/Chain.lean`. The underlying grading changes are stated
first for an arbitrary grid diagram, in the integer gradings `GridDiagram.maslovOℤ` and
`GridDiagram.alexanderTwoℤ`, where no hypothesis on the component count is needed; they live here
rather than beside their rational counterparts in `Unblocked.lean` because the integer gradings are
not among that file's dependencies.

With that convention the two records of `Unblocked.lean` say exactly that **the unblocked grid
differential has bidegree `(-1, 0)`**: it drops the `O`-Maslov grading by one and preserves the
Alexander grading. That is the convention the roadmap asks to be fixed once and for all before any
grid homology is stated, and it is what makes `GC⁻` a bigraded complex rather than merely a module
carrying a differential.

The homogeneous piece `OddComponentGridDiagram.bigradedChainMinusPiece` is a submodule over the
coefficient ring `R` only, not over `R[V₀, …, V_{n-1}]`: the variables move the bidegree. It
consists of the chains all of whose monomials have the given bidegree, and these pieces make `GC⁻`
an internal direct sum (`OddComponentGridDiagram.isInternal_bigradedChainMinusPiece`). This is not
the decomposition of `Grading/Chain.lean`, which regroups the basis of grid states of the blocked
chain module `GridChain R n` by bidegree over an arbitrary coefficient ring: over the polynomial
ring a basis element is a monomial *times* a grid state, and its bidegree depends on both, so what
is graded here is `GC⁻` itself and the pieces are submodules of it.

## Main definitions

* `TauCeti.OddComponentGridDiagram.monomialBidegree`: the bidegree of the basis element `V^e · x`
  of `GC⁻`.
* `TauCeti.OddComponentGridDiagram.bigradedChainMinusPiece`: the homogeneous piece of `GC⁻` in one
  bidegree.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_sub_two_mul_card_OColumns` and
  `TauCeti.GridDiagram.alexanderTwoℤ_sub_two_mul_card_OColumns`: the integer forms of the two
  grading changes across a rectangle counted by `∂⁻`.
* `TauCeti.OddComponentGridDiagram.monomialBidegree_add_of_mem_unblockedRectangles`: multiplying by
  the weight of a counted rectangle and moving to its target lowers the bidegree by `(1, 0)`.
* `TauCeti.OddComponentGridDiagram.unblockedDifferential_mem_bigradedChainMinusPiece`: the
  unblocked grid differential has bidegree `(-1, 0)`.
* `TauCeti.OddComponentGridDiagram.monomial_smul_mem_bigradedChainMinusPiece` and
  `TauCeti.OddComponentGridDiagram.X_smul_mem_bigradedChainMinusPiece`: the variable `V_c` has
  bidegree `(-2, -1)`, and a monomial `V^d` has bidegree `-|d|` times `(2, 1)`.
* `TauCeti.OddComponentGridDiagram.isInternal_bigradedChainMinusPiece`: `GC⁻` is the internal
  direct sum of its homogeneous pieces.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", whose unblocked complex `GC⁻` this bigrades, and its standing convention "Mind the
bigrading bookkeeping", which asks to "fix once whether differentials drop Maslov by 1 and preserve
Alexander (unblocked)". The conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Chapter 4.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) {x y : GridState n}

/-! ### The integer grading changes across a counted rectangle -/

/-- The integer form of the `O`-Maslov grading change across an empty rectangle: charging the
weight `V^{O(r)}` with `-2` per variable, a rectangle counted by `∂⁻` lowers the integer `O`-Maslov
grading by exactly one. -/
theorem maslovOℤ_sub_two_mul_card_OColumns {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    G.maslovOℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) = G.maslovOℤ x - 1 := by
  have h := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hr
  rw [G.maslovO_eq_intCast, G.maslovO_eq_intCast] at h
  exact_mod_cast h

/-- The integer form of the Alexander grading change across a rectangle carrying no `X`-marking:
charging the weight `V^{O(r)}` with `-1` per variable, a rectangle counted by `∂⁻` preserves the
Alexander grading, here in its doubled integer form. -/
theorem alexanderTwoℤ_sub_two_mul_card_OColumns {r : GridRectangleBetween x y}
    (hr : Disjoint r.toGridRectangle.coveredSquares G.XSet) :
    G.alexanderTwoℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) = G.alexanderTwoℤ x := by
  have h := G.alexander_sub_card_OColumns_eq_alexander hr
  have hy := G.two_mul_alexander_eq_intCast y
  have hx := G.two_mul_alexander_eq_intCast x
  have hq : (G.alexanderTwoℤ y : ℚ) - 2 * ((G.OColumns r.toGridRectangle).card : ℚ) =
      (G.alexanderTwoℤ x : ℚ) := by
    rw [← hy, ← hx]
    linarith
  exact_mod_cast hq

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) {x y : GridState n}

/-- The integer Alexander grading is unchanged across a rectangle counted by `∂⁻`, once its weight
`V^{O(r)}` is charged `-1` per variable. -/
theorem alexanderℤ_sub_card_OColumns {r : GridRectangleBetween x y}
    (hr : Disjoint r.toGridRectangle.coveredSquares G.1.XSet) :
    G.alexanderℤ y - ((G.1.OColumns r.toGridRectangle).card : ℤ) = G.alexanderℤ x := by
  have h := G.1.alexanderTwoℤ_sub_two_mul_card_OColumns hr
  rw [← G.two_mul_alexanderℤ, ← G.two_mul_alexanderℤ] at h
  omega

/-! ### The bidegree of a monomial generator -/

/-- The bidegree of the basis element `V^e · x` of the unblocked grid chain module `GC⁻`.

Each variable `V_c` sits in `O`-Maslov degree `-2` and Alexander degree `-1`, so the exponent
vector `e` shifts the bidegree of the grid state `x` by `-|e|` times `(2, 1)`, for `|e|` the total
degree of `e`. -/
noncomputable def monomialBidegree (x : GridState n) (e : Fin n →₀ ℕ) : ℤ × ℤ :=
  G.bidegree x - (2 * (e.degree : ℤ), (e.degree : ℤ))

/-- The `O`-Maslov component of the bidegree of `V^e · x`. -/
@[simp]
theorem monomialBidegree_fst (x : GridState n) (e : Fin n →₀ ℕ) :
    (G.monomialBidegree x e).1 = G.1.maslovOℤ x - 2 * (e.degree : ℤ) := by
  rw [monomialBidegree, Prod.fst_sub, bidegree_fst]

/-- The Alexander component of the bidegree of `V^e · x`. -/
@[simp]
theorem monomialBidegree_snd (x : GridState n) (e : Fin n →₀ ℕ) :
    (G.monomialBidegree x e).2 = G.alexanderℤ x - (e.degree : ℤ) := by
  rw [monomialBidegree, Prod.snd_sub, bidegree_snd]

/-- A grid-state generator carries the bidegree of its state. -/
@[simp]
theorem monomialBidegree_zero (x : GridState n) : G.monomialBidegree x 0 = G.bidegree x := by
  rw [monomialBidegree]
  simp

/-- Multiplying the basis element `V^e · x` by the weight of a rectangle counted by `∂⁻` and
passing to the rectangle's target lowers the bidegree by `(1, 0)`. This is the whole content of the
statement that `∂⁻` has bidegree `(-1, 0)`. -/
theorem monomialBidegree_add_of_mem_unblockedRectangles
    {r : GridRectangleBetween x y} (hr : r ∈ G.1.unblockedRectangles x y) (e : Fin n →₀ ℕ) :
    G.monomialBidegree y (e + ∑ c ∈ G.1.OColumns r.toGridRectangle, Finsupp.single c 1) =
      G.monomialBidegree x e - (1, 0) := by
  have hM := G.1.maslovOℤ_sub_two_mul_card_OColumns (G.1.isEmpty_of_mem_unblockedRectangles hr)
  have hA := G.alexanderℤ_sub_card_OColumns (G.1.disjoint_XSet_of_mem_unblockedRectangles hr)
  have hsum : ((e + ∑ c ∈ G.1.OColumns r.toGridRectangle,
      Finsupp.single (M := ℕ) c 1).degree : ℤ) =
      (e.degree : ℤ) + ((G.1.OColumns r.toGridRectangle).card : ℤ) := by
    rw [map_add, map_sum]
    simp
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, monomialBidegree_fst]
    rw [hsum]
    omega
  · simp only [Prod.snd_sub, monomialBidegree_snd]
    rw [hsum]
    omega

/-! ### The homogeneous pieces of `GC⁻` -/

/-- The chains of `GC⁻` all of whose monomials have bidegree in a prescribed set of bidegrees.
Only the singleton and complement-of-singleton cases are used: a homogeneous piece is the first,
and comparing it against the second is what makes the pieces independent. -/
private def bigradedChainMinusSupported (R : Type*) [CommSemiring R] (S : Set (ℤ × ℤ)) :
    Submodule R (GridChainMinus R n) where
  carrier := {c | ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialBidegree x e ∈ S}
  add_mem' {a b} ha hb x e he := by
    classical
    rw [Finsupp.add_apply] at he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact ha x e h
    · exact hb x e h
  zero_mem' x e he := by simp at he
  smul_mem' a b hb x e he := by
    rw [Finsupp.smul_apply] at he
    exact hb x e (MvPolynomial.support_smul he)

private theorem bigradedChainMinusSupported_mono {R : Type*} [CommSemiring R] {S T : Set (ℤ × ℤ)}
    (h : S ⊆ T) : G.bigradedChainMinusSupported R S ≤ G.bigradedChainMinusSupported R T :=
  fun _ hc x e he => h (hc x e he)

/-- The homogeneous piece of the unblocked grid chain module `GC⁻` in bidegree `g`: the chains all
of whose monomials `V^e · x` have bidegree `g`.

The variables move the bidegree, so this is a submodule over the coefficient ring `R` only, not
over `R[V₀, …, V_{n-1}]`. -/
def bigradedChainMinusPiece (R : Type*) [CommSemiring R] (g : ℤ × ℤ) :
    Submodule R (GridChainMinus R n) :=
  G.bigradedChainMinusSupported R {g}

/-- A chain of `GC⁻` is homogeneous of bidegree `g` exactly when every monomial occurring in it
has bidegree `g`. -/
@[simp]
theorem mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] {g : ℤ × ℤ}
    {c : GridChainMinus R n} :
    c ∈ G.bigradedChainMinusPiece R g ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialBidegree x e = g :=
  Iff.rfl

/-- A monomial multiple of a single grid-state generator is homogeneous of its own bidegree. -/
theorem single_monomial_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R]
    (x : GridState n) (e : Fin n →₀ ℕ) (a : R) :
    (Finsupp.single x (monomial e a) : GridChainMinus R n) ∈
      G.bigradedChainMinusPiece R (G.monomialBidegree x e) := by
  rw [mem_bigradedChainMinusPiece]
  intro z f hf
  rcases eq_or_ne z x with rfl | hzx
  · rw [Finsupp.single_eq_same] at hf
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hf)]
  · rw [Finsupp.single_eq_of_ne hzx] at hf
    simp at hf

/-- A grid-state generator of `GC⁻` is homogeneous of the bidegree of its state. -/
theorem single_one_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R] (x : GridState n) :
    (Finsupp.single x 1 : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R (G.bidegree x) := by
  have h := G.single_monomial_mem_bigradedChainMinusPiece R x 0 (1 : R)
  have hone : (monomial (0 : Fin n →₀ ℕ) (1 : R) : MvPolynomial (Fin n) R) = 1 := by
    simp
  rwa [monomialBidegree_zero, hone] at h

/-- **The unblocked grid differential has bidegree `(-1, 0)`**: it drops the `O`-Maslov grading by
one and preserves the Alexander grading. -/
theorem unblockedDifferential_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R]
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.unblockedDifferential R c ∈ G.bigradedChainMinusPiece R (g - (1, 0)) := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro z f hf
  rw [GridDiagram.unblockedDifferential_apply_apply, Finsupp.sum] at hf
  obtain ⟨w, -, hfw⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hf)
  obtain ⟨e, he, d, hd, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hfw)
  obtain ⟨r, hr, rfl⟩ :=
    G.1.exists_mem_unblockedRectangles_of_mem_support_unblockedCoefficient R hd
  rw [G.monomialBidegree_add_of_mem_unblockedRectangles hr e, hc w e he]

/-- The unblocked grid differential maps each homogeneous piece of `GC⁻` into the piece one lower
in the `O`-Maslov grading. -/
theorem map_unblockedDifferential_bigradedChainMinusPiece_le (R : Type*) [CommSemiring R]
    (g : ℤ × ℤ) :
    Submodule.map ((G.1.unblockedDifferential R).restrictScalars R)
        (G.bigradedChainMinusPiece R g) ≤
      G.bigradedChainMinusPiece R (g - (1, 0)) := by
  rintro _ ⟨c, hc, rfl⟩
  exact G.unblockedDifferential_mem_bigradedChainMinusPiece hc

/-- **A monomial of the polynomial ring has bidegree `-|d|` times `(2, 1)`**: multiplying a
homogeneous chain of `GC⁻` by `V^d` lowers its `O`-Maslov grading by `2 |d|` and its Alexander
grading by `|d|`. -/
theorem monomial_smul_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R]
    (d : Fin n →₀ ℕ) (a : R) {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    (monomial d a : MvPolynomial (Fin n) R) • c ∈
      G.bigradedChainMinusPiece R (g - (2 * (d.degree : ℤ), (d.degree : ℤ))) := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro z f hf
  rw [Finsupp.smul_apply, smul_eq_mul] at hf
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hf)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)]
  have hdeg : ((d + e).degree : ℤ) = (d.degree : ℤ) + (e.degree : ℤ) := by
    rw [map_add]
    push_cast
    ring
  have hfst := congrArg Prod.fst (hc z e he)
  have hsnd := congrArg Prod.snd (hc z e he)
  rw [monomialBidegree_fst] at hfst
  rw [monomialBidegree_snd] at hsnd
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, monomialBidegree_fst]
    rw [hdeg]
    omega
  · simp only [Prod.snd_sub, monomialBidegree_snd]
    rw [hdeg]
    omega

/-- **The variable `V_c` has bidegree `(-2, -1)`**: multiplying a homogeneous chain of `GC⁻` by a
polynomial variable lowers its `O`-Maslov grading by two and its Alexander grading by one. -/
theorem X_smul_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] (i : Fin n) {g : ℤ × ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    (X i : MvPolynomial (Fin n) R) • c ∈ G.bigradedChainMinusPiece R (g - (2, 1)) := by
  have h := G.monomial_smul_mem_bigradedChainMinusPiece (Finsupp.single i 1) (1 : R) hc
  rwa [Finsupp.degree_single, Nat.cast_one, mul_one, ← X] at h

/-! ### `GC⁻` is the direct sum of its homogeneous pieces -/

/-- The homogeneous pieces of `GC⁻` span it: every chain is a finite sum of monomial multiples of
grid-state generators. -/
theorem iSup_bigradedChainMinusPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ g : ℤ × ℤ, G.bigradedChainMinusPiece R g = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add x p c _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    have hp : (Finsupp.single x p : GridChainMinus R n) =
        ∑ e ∈ p.support, Finsupp.single x (monomial e (coeff e p)) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      exact map_sum (Finsupp.singleAddHom x) _ _
    rw [hp]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.mem_iSup_of_mem (G.monomialBidegree x e)
        (G.single_monomial_mem_bigradedChainMinusPiece R x e _)

/-- The homogeneous pieces of `GC⁻` are independent: every monomial of a chain has exactly one
bidegree. -/
theorem iSupIndep_bigradedChainMinusPiece (R : Type*) [CommSemiring R] :
    iSupIndep (G.bigradedChainMinusPiece R) := by
  intro g
  rw [Submodule.disjoint_def]
  intro c hc hc'
  rw [mem_bigradedChainMinusPiece] at hc
  have hcompl : c ∈ G.bigradedChainMinusSupported R {g}ᶜ :=
    iSup₂_le (fun _ hg => G.bigradedChainMinusSupported_mono
      (Set.singleton_subset_iff.mpr hg)) hc'
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun e he => hcompl z e he (hc z e he)

/-- **The unblocked grid chain module is bigraded**: `GC⁻` is the internal direct sum of its
homogeneous pieces.

The coefficient ring is a `CommRing` here, and not merely a `CommSemiring` as elsewhere in the
file, because independence plus spanning gives an internal direct sum only over a ring
(`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`). The grid coefficient rings of
interest, `ZMod 2` first among them, are rings. -/
theorem isInternal_bigradedChainMinusPiece (R : Type*) [CommRing R] :
    DirectSum.IsInternal (G.bigradedChainMinusPiece R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (G.iSupIndep_bigradedChainMinusPiece R) (G.iSup_bigradedChainMinusPiece_eq_top R)

end OddComponentGridDiagram

end TauCeti
