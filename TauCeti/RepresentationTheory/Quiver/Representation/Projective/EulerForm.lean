/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import TauCeti.RepresentationTheory.Quiver.LastArrow
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic

/-!
# The Euler form against the dimension vector of a vertex projective

The Euler form of a finite quiver is the numerical shadow of the homological pairing: for
finite-dimensional representations of an acyclic quiver, `⟨dim M, dim N⟩` is
`dim Hom(M, N) - dim Ext¹(M, N)`. On the projective `Pᵢ` that identity needs no `Ext`, because
`Ext¹(Pᵢ, -)` vanishes and `Hom(Pᵢ, N)` is `Nᵢ`. This file proves the resulting closed formula,

`⟨dim Pᵢ, e⟩ = eᵢ` for every `e : Q → ℤ`,

which holds over any finite quiver with finitely many paths — no acyclicity, no algebraically
closed field, no finite-dimensionality of the representations involved.

## Main results

* `TauCeti.eulerForm_card_path_left`: the combinatorial core, `⟨(#(i → -)), e⟩ = eᵢ`, a restatement
  of the last-arrow recursion `TauCeti.card_path_eq_ite_add_sum` for path counts.
* `TauCeti.eulerForm_dimVector_indecProjRep`: `⟨dim Pᵢ, e⟩ = eᵢ`.
* `TauCeti.eulerForm_dimVector_indecProjRep_eq_finrank_hom`: the homological reading,
  `⟨dim Pᵢ, dim N⟩ = dim Hom(Pᵢ, N)`.
* `TauCeti.eulerForm_dimVector_indecProjRep_indecProjRep`: the Cartan pairing of two projectives
  counts the paths `j → i`.
* `TauCeti.titsForm_dimVector_indecProjRep_of_isAcyclic`: over an acyclic quiver `dim Pᵢ` has Tits
  norm `1`, so it is a root of the Tits form.

## Implementation notes

The hypothesis carried throughout is `∀ a b, Finite (Quiver.Path a b)`, the finiteness that makes
`TauCeti.dimVector (indecProjRep k Q i)` an honest path count rather than the `0` that
`Module.finrank` returns on an infinite-dimensional space. For a finite quiver it follows from
acyclicity, by `TauCeti.finite_paths_of_isAcyclic`; the loop quiver, where it fails, is exactly the
boundary case the roadmap records.

Dimension vectors take values in `ℕ` while the Euler form is defined on `Q → ℤ`, so every statement
below feeds the Euler form the pointwise cast `fun v ↦ (dimVector M v : ℤ)`.

The dual statements, for the injective `Iᵢ` on the right-hand side of the Euler form, need the
decomposition of a path by its *first* arrow, which
`TauCeti.RepresentationTheory.Quiver.LastArrow` does not provide; they are left for later.

## References

This implements the projective case of the homological interpretation of the Euler form, Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman, *An
Introduction to Quiver Representations*, Ch. 1, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable (Q : Type v) [Quiver.{w} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [∀ a b : Q, Finite (Quiver.Path a b)]

/-- **The Euler form against a path-count vector is evaluation.** Pairing the vector counting the
paths out of `i` against any `e : Q → ℤ` returns `eᵢ`: at each vertex `b` the path count `#(i → b)`
cancels the arrow-weighted sum `∑ₐ #(a ⟶ b) · #(i → a)` up to the trivial path, by the last-arrow
recursion `TauCeti.card_path_eq_ite_add_sum`. -/
theorem eulerForm_card_path_left (i : Q) (e : Q → ℤ) :
    eulerForm Q (fun v ↦ (Nat.card (Quiver.Path i v) : ℤ)) e = e i := by
  classical
  have key : ∀ b : Q,
      (Nat.card (Quiver.Path i b) : ℤ)
          - ∑ a : Q, (Fintype.card (a ⟶ b) : ℤ) * (Nat.card (Quiver.Path i a) : ℤ)
        = if i = b then 1 else 0 := by
    intro b
    have h := congrArg (fun n : ℕ ↦ (n : ℤ)) (card_path_eq_ite_add_sum (V := Q) i b)
    push_cast [Nat.card_eq_fintype_card] at h
    rw [h, Finset.sum_congr rfl fun a _ ↦
      mul_comm ((Fintype.card (a ⟶ b) : ℤ)) ((Nat.card (Quiver.Path i a) : ℤ))]
    ring
  have hswap : ∑ a : Q, ∑ b : Q,
        (Fintype.card (a ⟶ b) : ℤ) * ((Nat.card (Quiver.Path i a) : ℤ) * e b)
      = ∑ b : Q,
          (∑ a : Q, (Fintype.card (a ⟶ b) : ℤ) * (Nat.card (Quiver.Path i a) : ℤ)) * e b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [eulerForm_eq_sum_card, hswap, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun b _ ↦ by rw [← sub_mul, key b]]
  simp

variable (k : Type u) [Field k]

/-- **The Euler form against the dimension vector of `Pᵢ` is evaluation at `i`.** This is the
homological identity `⟨dim M, dim N⟩ = dim Hom(M, N) - dim Ext¹(M, N)` in the one case where it
needs no `Ext`: the projective `Pᵢ` represents evaluation at `i`. -/
theorem eulerForm_dimVector_indecProjRep (i : Q) (e : Q → ℤ) :
    eulerForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ)) e = e i := by
  have hcount : (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ))
      = fun v ↦ (Nat.card (Quiver.Path i v) : ℤ) := by
    funext v
    rw [dimVector_indecProjRep]
  rw [hcount, eulerForm_card_path_left]

/-- **The homological reading of the Euler form at a projective.** For every representation `N`,
`⟨dim Pᵢ, dim N⟩` is the dimension of `Hom(Pᵢ, N)`; the `Ext¹` term of the general identity is
absent because `Pᵢ` is projective. -/
theorem eulerForm_dimVector_indecProjRep_eq_finrank_hom (i : Q) (N : QuiverRep k Q) :
    eulerForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ))
        (fun v ↦ (dimVector N v : ℤ))
      = (Module.finrank k (indecProjRep k Q i ⟶ N) : ℤ) := by
  rw [eulerForm_dimVector_indecProjRep, finrank_hom_indecProjRep]

/-- **The Cartan pairing of two vertex projectives.** `⟨dim Pᵢ, dim Pⱼ⟩` counts the paths `j → i`,
which is `dim Hom(Pᵢ, Pⱼ)`: the Euler form reproduces the path-counting Cartan matrix of a path
algebra. -/
theorem eulerForm_dimVector_indecProjRep_indecProjRep (i j : Q) :
    eulerForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ))
        (fun v ↦ (dimVector (indecProjRep k Q j) v : ℤ))
      = (Nat.card (Quiver.Path j i) : ℤ) := by
  rw [eulerForm_dimVector_indecProjRep, dimVector_indecProjRep]

/-- **The Euler pairing of a projective against a vertex simple.** `⟨dim Pᵢ, αⱼ⟩ = δᵢⱼ`, the
dimension of `Hom(Pᵢ, Sⱼ)`: the projectives and the simples are dual bases for the Euler form. -/
theorem eulerForm_dimVector_indecProjRep_single [DecidableEq Q] (i j : Q) :
    eulerForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ)) (Pi.single j 1)
      = if i = j then 1 else 0 := by
  rw [eulerForm_dimVector_indecProjRep, Pi.single_apply]

/-- The Tits norm of the dimension vector of `Pᵢ` counts the closed paths at `i`. -/
theorem titsForm_dimVector_indecProjRep (i : Q) :
    titsForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ))
      = (Nat.card (Quiver.Path i i) : ℤ) := by
  rw [titsForm_def, eulerForm_dimVector_indecProjRep, dimVector_indecProjRep]

/-- **Over an acyclic quiver the dimension vector of `Pᵢ` is a root of the Tits form**: its Tits
norm is `1`, the trivial path being the only closed path at `i`. -/
theorem titsForm_dimVector_indecProjRep_of_isAcyclic (h : Quiver.IsAcyclic Q) (i : Q) :
    titsForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ)) = 1 := by
  letI : Subsingleton (Quiver.Path i i) := h.subsingleton_path_self i
  letI : Unique (Quiver.Path i i) := uniqueOfSubsingleton Quiver.Path.nil
  rw [titsForm_dimVector_indecProjRep, Nat.card_unique, Nat.cast_one]

end TauCeti
