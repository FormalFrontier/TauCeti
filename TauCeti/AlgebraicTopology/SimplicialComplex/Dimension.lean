/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# The dimension of an abstract simplicial complex

The dimension of a simplicial complex is the supremum of the dimensions of its faces, where a
face with `k + 1` vertices has dimension `k`. This file defines that dimension for
`PreAbstractSimplicialComplex` (Mathlib's downward-closed collection of nonempty finite faces,
no singleton requirement) and for `AbstractSimplicialComplex`.

Following the convention Mathlib uses for `Order.krullDim`, the dimension takes values in
`WithBot ℕ∞`: the empty complex `⊥` has dimension `⊥` (the "`-1`" of the void complex), a complex
whose faces have unbounded cardinality has dimension `⊤`, and a finite-dimensional nonempty complex
has an honest natural-number dimension. This is the primitive the layer-11 combinatorial-manifold
recursion is indexed against: a combinatorial `n`-sphere or `n`-ball is an `n`-dimensional complex,
and the boundary of the standard `(n + 1)`-simplex — computed here to have dimension `n` — is the
base model of that recursion.

The definitions follow Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
This supplements the basic API (faces, the star and link of a simplex) that the geometric-topology
roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 11) asks for on top of Mathlib's
`AbstractSimplicialComplex`.

## Main definitions

* `PreAbstractSimplicialComplex.dimension`: the dimension of a precomplex.
* `AbstractSimplicialComplex.dimension`: the dimension of an abstract complex.

## Main results

* `PreAbstractSimplicialComplex.le_dimension`: every face's dimension bounds the complex's.
* `PreAbstractSimplicialComplex.dimension_le_iff`: the dimension is bounded exactly when
  every face's dimension is.
* `PreAbstractSimplicialComplex.dimension_mono`: dimension is monotone in the complex.
* `PreAbstractSimplicialComplex.dimension_eq_bot_iff`: only the void complex has dimension
  `⊥`.
* `PreAbstractSimplicialComplex.dimension_eq_top_iff` /
  `dimension_lt_top_iff`: infinite dimension means that face cardinalities are unbounded, while
  finite dimension means that they have a uniform natural-number bound.
* `PreAbstractSimplicialComplex.dimension_le_card_sub_one`: a finite set containing every
  face gives an explicit dimension bound.
* `PreAbstractSimplicialComplex.dimension_top_eq_top_of_infinite`: the full complex on an
  infinite vertex type has infinite dimension.
* `PreAbstractSimplicialComplex.dimension_simplex` /
  `PreAbstractSimplicialComplex.dimension_simplexBoundary`: the dimensions of the standard
  simplex on `V` (namely `V.card - 1`) and of its boundary (namely `V.card - 2`).
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-- The **dimension** of a pre-abstract simplicial complex: the supremum, over its faces `σ`, of
the face dimension `σ.card - 1`. It takes values in `WithBot ℕ∞`, so the void complex has dimension
`⊥` and an unbounded complex has dimension `⊤`. -/
noncomputable def dimension (K : PreAbstractSimplicialComplex ι) : WithBot ℕ∞ :=
  ⨆ σ ∈ K, ((σ.card - 1 : ℕ) : WithBot ℕ∞)

variable {K L : PreAbstractSimplicialComplex ι} {σ : Finset ι}

/-- The dimension of any face bounds the dimension of the complex. -/
theorem le_dimension (hσ : σ ∈ K) : ((σ.card - 1 : ℕ) : WithBot ℕ∞) ≤ dimension K :=
  le_iSup₂ (f := fun σ (_ : σ ∈ K) => ((σ.card - 1 : ℕ) : WithBot ℕ∞)) σ hσ

/-- The dimension of a complex is bounded by `n` exactly when every face's dimension is. -/
theorem dimension_le_iff {n : WithBot ℕ∞} :
    dimension K ≤ n ↔ ∀ σ ∈ K, ((σ.card - 1 : ℕ) : WithBot ℕ∞) ≤ n := by
  simp only [dimension, iSup_le_iff]

/-- Dimension is monotone in the complex. -/
theorem dimension_mono (h : K ≤ L) : dimension K ≤ dimension L :=
  dimension_le_iff.mpr fun _ hσ => le_dimension (h hσ)

/-- The void complex has dimension `⊥`. -/
@[simp]
theorem dimension_bot : dimension (⊥ : PreAbstractSimplicialComplex ι) = ⊥ := by
  rw [eq_bot_iff, dimension_le_iff]
  exact fun _ hσ => hσ.elim

/-- Only the void complex has dimension `⊥`: any face contributes a nonnegative dimension. -/
@[simp]
theorem dimension_eq_bot_iff : dimension K = ⊥ ↔ K = ⊥ := by
  refine ⟨fun h => eq_bot_iff.mpr fun σ hσ => ?_, fun h => h ▸ dimension_bot⟩
  have hle := le_dimension hσ
  rw [h] at hle
  exact absurd (le_bot_iff.mp hle) (WithBot.natCast_ne_bot _)

/-- A complex has infinite dimension exactly when its face cardinalities are unbounded. -/
@[simp]
theorem dimension_eq_top_iff :
    dimension K = ⊤ ↔ ∀ n : ℕ, ∃ σ ∈ K, n ≤ σ.card := by
  constructor
  · intro h n
    rw [dimension] at h
    obtain ⟨σ, hσ⟩ := (iSup_eq_top.mp h) (n : WithBot ℕ∞)
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))
    obtain ⟨hσK, hnσ⟩ := lt_iSup_iff.mp hσ
    refine ⟨σ, hσK, ?_⟩
    have : n < σ.card - 1 := by exact_mod_cast hnσ
    omega
  · intro h
    rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    obtain ⟨σ, hσK, hcard⟩ := h (n + 1)
    apply le_trans (b := ((σ.card - 1 : ℕ) : WithBot ℕ∞))
    · exact_mod_cast (by omega : n ≤ σ.card - 1)
    · exact le_dimension hσK

/-- A complex has dimension below `⊤` exactly when its face cardinalities have a uniform natural
number bound. -/
@[simp]
theorem dimension_lt_top_iff :
    dimension K < ⊤ ↔ ∃ n : ℕ, ∀ σ ∈ K, σ.card ≤ n := by
  rw [lt_top_iff_ne_top, Ne, dimension_eq_top_iff]
  constructor
  · intro h
    push Not at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, fun σ hσ => Nat.le_of_lt (hn σ hσ)⟩
  · rintro ⟨n, hn⟩ h
    obtain ⟨σ, hσK, hcard⟩ := h (n + 1)
    exact (Nat.not_succ_le_self n) (hcard.trans (hn σ hσK))

/-- If every face of a complex is contained in a finite set `V`, then its dimension is at most
`V.card - 1`. -/
theorem dimension_le_card_sub_one {V : Finset ι} (hV : ∀ σ ∈ K, σ ⊆ V) :
    dimension K ≤ ((V.card - 1 : ℕ) : WithBot ℕ∞) := by
  rw [dimension_le_iff]
  intro σ hσ
  exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_card (hV σ hσ)) 1

/-- A complex carried by a finite set of vertices has dimension below `⊤`. -/
theorem dimension_lt_top_of_finite_vertices {V : Finset ι} (hV : ∀ σ ∈ K, σ ⊆ V) :
    dimension K < ⊤ :=
  (dimension_le_card_sub_one hV).trans_lt
    (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top (V.card - 1)))

/-- A complex on a finite vertex type has dimension below `⊤`. -/
theorem dimension_lt_top_of_finite [Finite ι] : dimension K < ⊤ := by
  let _ := Fintype.ofFinite ι
  exact dimension_lt_top_of_finite_vertices (V := Finset.univ) fun _ _ => Finset.subset_univ _

/-- The full complex on an infinite vertex type has infinite dimension. -/
@[simp]
theorem dimension_top_eq_top_of_infinite [Infinite ι] :
    dimension (⊤ : PreAbstractSimplicialComplex ι) = ⊤ := by
  rw [dimension_eq_top_iff]
  intro n
  obtain ⟨σ, hcard⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  refine ⟨σ, Finset.card_pos.mp (by omega), ?_⟩
  omega

/-- The dimension of the standard simplex on a nonempty vertex set `V` is `V.card - 1`. -/
@[simp]
theorem dimension_simplex {V : Finset ι} (hV : V.Nonempty) :
    dimension (simplex V) = ((V.card - 1 : ℕ) : WithBot ℕ∞) := by
  refine le_antisymm (dimension_le_iff.mpr fun σ hσ => ?_) (le_dimension (self_mem_simplex.mpr hV))
  exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_card (mem_simplex.mp hσ).2) 1

/-- The dimension of the boundary of the standard simplex on a vertex set `V` with at least two
vertices is `V.card - 2`. -/
@[simp]
theorem dimension_simplexBoundary {V : Finset ι} (hV : 1 < V.card) :
    dimension (simplexBoundary V) = ((V.card - 2 : ℕ) : WithBot ℕ∞) := by
  refine le_antisymm (dimension_le_iff.mpr fun σ hσ => ?_) ?_
  · have h := Finset.card_lt_card (mem_simplexBoundary.mp hσ).2
    exact_mod_cast (by omega : σ.card - 1 ≤ V.card - 2)
  · obtain ⟨W, hWV, hWcard⟩ := le_card_iff_exists_subset_card.mp (Nat.sub_le V.card 1)
    have hWmem : W ∈ simplexBoundary V := by
      rw [mem_simplexBoundary]
      refine ⟨Finset.card_pos.mp (by rw [hWcard]; omega), ?_⟩
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨hWV, fun h => by rw [h] at hWcard; omega⟩
    have hle := le_dimension hWmem
    rwa [hWcard, Nat.sub_sub] at hle

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- The **dimension** of an abstract simplicial complex, defined through its underlying
precomplex. -/
noncomputable def dimension (K : AbstractSimplicialComplex ι) : WithBot ℕ∞ :=
  PreAbstractSimplicialComplex.dimension K.toPreAbstractSimplicialComplex

/-- The dimension of an abstract complex agrees with the dimension of its underlying precomplex. -/
@[simp]
theorem dimension_toPreAbstractSimplicialComplex (K : AbstractSimplicialComplex ι) :
    PreAbstractSimplicialComplex.dimension K.toPreAbstractSimplicialComplex = dimension K :=
  (rfl)

variable {K L : AbstractSimplicialComplex ι} {σ : Finset ι}

/-- The dimension of any face bounds the dimension of the complex. -/
theorem le_dimension (hσ : σ ∈ K) : ((σ.card - 1 : ℕ) : WithBot ℕ∞) ≤ dimension K :=
  PreAbstractSimplicialComplex.le_dimension (mem_toPreAbstractSimplicialComplex.mpr hσ)

/-- The dimension of an abstract complex is bounded by `n` exactly when every face's dimension is.
-/
theorem dimension_le_iff {n : WithBot ℕ∞} :
    dimension K ≤ n ↔ ∀ σ ∈ K, ((σ.card - 1 : ℕ) : WithBot ℕ∞) ≤ n :=
  by
    simp only [← mem_toPreAbstractSimplicialComplex]
    exact PreAbstractSimplicialComplex.dimension_le_iff

/-- Dimension is monotone in the abstract complex. -/
theorem dimension_mono (h : K ≤ L) : dimension K ≤ dimension L :=
  PreAbstractSimplicialComplex.dimension_mono
    ((_root_.AbstractSimplicialComplex.toPreAbstractSimplicialComplex_le_iff
      (K := K) (L := L)).mpr h)

/-- An abstract simplicial complex has infinite dimension exactly when its face cardinalities are
unbounded. -/
@[simp]
theorem dimension_eq_top_iff :
    dimension K = ⊤ ↔ ∀ n : ℕ, ∃ σ ∈ K, n ≤ σ.card := by
  rw [← dimension_toPreAbstractSimplicialComplex,
    PreAbstractSimplicialComplex.dimension_eq_top_iff]
  constructor
  · intro h n
    obtain ⟨σ, hσ, hn⟩ := h n
    exact ⟨σ, mem_toPreAbstractSimplicialComplex.mp hσ, hn⟩
  · intro h n
    obtain ⟨σ, hσ, hn⟩ := h n
    exact ⟨σ, mem_toPreAbstractSimplicialComplex.mpr hσ, hn⟩

/-- An abstract simplicial complex has dimension below `⊤` exactly when its face cardinalities have
a uniform natural-number bound. -/
@[simp]
theorem dimension_lt_top_iff :
    dimension K < ⊤ ↔ ∃ n : ℕ, ∀ σ ∈ K, σ.card ≤ n := by
  rw [← dimension_toPreAbstractSimplicialComplex,
    PreAbstractSimplicialComplex.dimension_lt_top_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun σ hσ => hn σ (mem_toPreAbstractSimplicialComplex.mpr hσ)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun σ hσ => hn σ (mem_toPreAbstractSimplicialComplex.mp hσ)⟩

/-- If every face of an abstract simplicial complex is contained in a finite set `V`, then its
dimension is at most `V.card - 1`. -/
theorem dimension_le_card_sub_one {V : Finset ι} (hV : ∀ σ ∈ K, σ ⊆ V) :
    dimension K ≤ ((V.card - 1 : ℕ) : WithBot ℕ∞) := by
  rw [← dimension_toPreAbstractSimplicialComplex]
  apply PreAbstractSimplicialComplex.dimension_le_card_sub_one
  intro σ hσ
  exact hV σ (mem_toPreAbstractSimplicialComplex.mp hσ)

/-- An abstract simplicial complex carried by a finite set of vertices has dimension below `⊤`. -/
theorem dimension_lt_top_of_finite_vertices {V : Finset ι} (hV : ∀ σ ∈ K, σ ⊆ V) :
    dimension K < ⊤ := by
  rw [← dimension_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.dimension_lt_top_of_finite_vertices (V := V)
    fun σ hσ => hV σ (mem_toPreAbstractSimplicialComplex.mp hσ)

/-- An abstract simplicial complex on a finite vertex type has dimension below `⊤`. -/
theorem dimension_lt_top_of_finite [Finite ι] : dimension K < ⊤ := by
  rw [← dimension_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.dimension_lt_top_of_finite

/-- The full abstract simplicial complex on an infinite vertex type has infinite dimension. -/
@[simp]
theorem dimension_top_eq_top_of_infinite [Infinite ι] :
    dimension (⊤ : AbstractSimplicialComplex ι) = ⊤ := by
  rw [← dimension_toPreAbstractSimplicialComplex,
    _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.dimension_top_eq_top_of_infinite

end AbstractSimplicialComplex
