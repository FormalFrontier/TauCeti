/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Representation.Injective.Basic

/-!
# The Euler form against the dimension vector of a vertex injective

The Euler form of a finite quiver is the numerical shadow of the homological pairing: for
finite-dimensional representations of an acyclic quiver, `⟨dim M, dim N⟩` is
`dim Hom(M, N) - dim Ext¹(M, N)`. On the injective `Iᵢ` in the *right-hand* argument that identity
needs no `Ext`, because `Ext¹(-, Iᵢ)` vanishes and `Hom(M, Iᵢ)` is the dual of `Mᵢ`. This file
proves the resulting closed formula,

`⟨d, dim Iᵢ⟩ = dᵢ` for every `d : Q → ℤ`,

which holds over any finite quiver with finitely many paths into `i` — no acyclicity, no
algebraically closed field, no finite-dimensionality of the representations involved.

It is the mirror image of `TauCeti.RepresentationTheory.Quiver.Representation.Projective.EulerForm`,
which computes the Euler form against `dim Pᵢ` in the *left-hand* argument. The Euler form is not
symmetric, so neither file's results follow from the other's; what makes them mirror images is that
the path-count vector of `Iᵢ` is the transpose of that of `Pᵢ`
(`TauCeti.dimVector_indecInjRep_eq_dimVector_indecProjRep`).

## Main results

* `TauCeti.eulerForm_dimVector_indecInjRep`: `⟨d, dim Iᵢ⟩ = dᵢ`.
* `TauCeti.eulerForm_dimVector_indecInjRep_eq_finrank_hom`: the homological reading,
  `⟨dim M, dim Iᵢ⟩ = dim Hom(M, Iᵢ)`.
* `TauCeti.eulerForm_dimVector_indecInjRep_indecInjRep`: the Cartan pairing of two injectives
  counts the paths `j → i`, the same count as for two projectives.
* `TauCeti.eulerForm_dimVector_indecProjRep_indecInjRep`: the mixed pairing `⟨dim Pᵢ, dim Iⱼ⟩`
  counts the paths `i → j`.

## Implementation notes

The combinatorial core is `TauCeti.eulerForm_card_path_right`, in
`TauCeti.RepresentationTheory.Quiver.EulerForm`, which pairs the Euler form against a path-count
vector on the right; the results below just rewrite `dim Iᵢ` into that path count.

The hypothesis carried throughout is `∀ a, Finite (Quiver.Path a i)`, for the vertex `i` at hand:
the finiteness that makes `TauCeti.dimVector (indecInjRep k Q i)` an honest path count rather than
the `0` that `Module.finrank` returns on an infinite-dimensional space. For a finite quiver it
follows from acyclicity, by `TauCeti.finite_paths_of_isAcyclic`; the loop quiver, where it fails, is
exactly the boundary case the roadmap records. It is the transpose of the hypothesis
`∀ a, Finite (Quiver.Path i a)` carried by the projective file, and neither implies the other.

Dimension vectors take values in `ℕ` while the Euler form is defined on `Q → ℤ`, so every statement
below feeds the Euler form the pointwise cast `fun v ↦ (dimVector M v : ℤ)`.

## References

This implements the injective case of the homological interpretation of the Euler form, Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman, *An
Introduction to Quiver Representations*, Ch. 1, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable (Q : Type v) [Quiver.{w} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  (k : Type u) [Field k]

/-- **The Euler form against the dimension vector of `Iᵢ` is evaluation at `i`.** This is the
homological identity `⟨dim M, dim N⟩ = dim Hom(M, N) - dim Ext¹(M, N)` in the second case where it
needs no `Ext`: the injective `Iᵢ` corepresents the dual of evaluation at `i`. -/
theorem eulerForm_dimVector_indecInjRep (i : Q) [∀ a : Q, Finite (Quiver.Path a i)] (d : Q → ℤ) :
    eulerForm Q d (fun v ↦ (dimVector (indecInjRep k Q i) v : ℤ)) = d i := by
  have hcount : (fun v ↦ (dimVector (indecInjRep k Q i) v : ℤ))
      = fun v ↦ (Nat.card (Quiver.Path v i) : ℤ) := by
    funext v
    rw [dimVector_indecInjRep]
  rw [hcount, eulerForm_card_path_right]

/-- **The homological reading of the Euler form at an injective.** For every representation `M`,
`⟨dim M, dim Iᵢ⟩` is the dimension of `Hom(M, Iᵢ)`; the `Ext¹` term of the general identity is
absent because `Iᵢ` is injective. -/
theorem eulerForm_dimVector_indecInjRep_eq_finrank_hom (i : Q)
    [∀ a : Q, Finite (Quiver.Path a i)] (M : QuiverRep k Q) :
    eulerForm Q (fun v ↦ (dimVector M v : ℤ))
        (fun v ↦ (dimVector (indecInjRep k Q i) v : ℤ))
      = (Module.finrank k (M ⟶ indecInjRep k Q i) : ℤ) := by
  rw [eulerForm_dimVector_indecInjRep, finrank_hom_indecInjRep]

/-- **The Cartan pairing of two vertex injectives.** `⟨dim Iᵢ, dim Iⱼ⟩` counts the paths `j → i`,
which is `dim Hom(Iᵢ, Iⱼ)`: the injectives reproduce the same path-counting Cartan matrix as the
projectives. -/
theorem eulerForm_dimVector_indecInjRep_indecInjRep (i j : Q)
    [∀ a : Q, Finite (Quiver.Path a j)] :
    eulerForm Q (fun v ↦ (dimVector (indecInjRep k Q i) v : ℤ))
        (fun v ↦ (dimVector (indecInjRep k Q j) v : ℤ))
      = (Nat.card (Quiver.Path j i) : ℤ) := by
  rw [eulerForm_dimVector_indecInjRep, dimVector_indecInjRep]

/-- **The mixed pairing of a projective against an injective.** `⟨dim Pᵢ, dim Iⱼ⟩` counts the paths
`i → j`; reading it instead as `dim Hom(Pᵢ, Iⱼ)` is
`TauCeti.eulerForm_dimVector_indecInjRep_eq_finrank_hom` at `M := Pᵢ`. Both
`TauCeti.eulerForm_dimVector_indecProjRep` and `TauCeti.eulerForm_dimVector_indecInjRep` apply
here, and they agree. -/
theorem eulerForm_dimVector_indecProjRep_indecInjRep (i j : Q)
    [∀ a : Q, Finite (Quiver.Path a j)] :
    eulerForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ))
        (fun v ↦ (dimVector (indecInjRep k Q j) v : ℤ))
      = (Nat.card (Quiver.Path i j) : ℤ) := by
  rw [eulerForm_dimVector_indecInjRep, dimVector_indecProjRep]

/-- **The Euler pairing of a vertex simple against an injective.** `⟨αⱼ, dim Iᵢ⟩ = δᵢⱼ`, the
dimension of `Hom(Sⱼ, Iᵢ)`: the injectives and the simples are dual bases for the Euler form, as
the projectives and the simples are on the other side. -/
theorem eulerForm_single_dimVector_indecInjRep [DecidableEq Q] (i : Q)
    [∀ a : Q, Finite (Quiver.Path a i)] (j : Q) :
    eulerForm Q (Pi.single j 1) (fun v ↦ (dimVector (indecInjRep k Q i) v : ℤ))
      = if i = j then 1 else 0 := by
  rw [eulerForm_dimVector_indecInjRep, Pi.single_apply]

/-- The Tits norm of the dimension vector of `Iᵢ` counts the closed paths at `i`, the same count as
for `Pᵢ`. -/
theorem titsForm_dimVector_indecInjRep (i : Q) [∀ a : Q, Finite (Quiver.Path a i)] :
    titsForm Q (fun v ↦ (dimVector (indecInjRep k Q i) v : ℤ))
      = (Nat.card (Quiver.Path i i) : ℤ) := by
  rw [titsForm_def, eulerForm_dimVector_indecInjRep, dimVector_indecInjRep]

end TauCeti
