/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Wedderburn
public import TauCeti.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The irreducible representations carried by the Wedderburn blocks

A Wedderburn presentation `e : k[G] ≃ₐ[k] Π i, Matₙᵢ(k)` of a finite group algebra is a numerical
statement until each block is turned into a representation. This file does that: composing `e` with
the projection onto the `i`-th factor and with `Matrix.toLinAlgEquiv'` presents the column space
`Fin (d i) → k` as a `k[G]`-module, hence as a representation of `G`.

Two facts make the resulting family the family of irreducibles. Each `blockRepresentation e i` is
irreducible by `TauCeti.Representation.isIrreducible_of_asAlgebraHom_surjective`, its algebra map
onto `End k (Fin (d i) → k)` being surjective. And the blocks are pairwise inequivalent, because
the idempotent `e.symm (Pi.single i 1)` acts as the identity on the `i`-th block and as zero on
every other one.

Together with `TauCeti.exists_algEquiv_pi_matrix_conjClasses` this produces, over an algebraically
closed field whose characteristic does not divide `|G|`, a family of pairwise inequivalent
irreducible representations of `G` indexed by the conjugacy classes of `G`.

## Main definitions

* `TauCeti.blockAlgHom`: the algebra map from `k[G]` onto the endomorphisms of the `i`-th column
  space cut out by a Wedderburn presentation.
* `TauCeti.blockRepresentation`: the representation of `G` on that column space.

## Main statements

* `TauCeti.isIrreducible_blockRepresentation`: **every block of a Wedderburn presentation carries an
  irreducible representation**.
* `TauCeti.isEmpty_equiv_blockRepresentation`: **distinct blocks carry inequivalent
  representations**.
* `TauCeti.exists_irreducible_family_conjClasses`: **there are as many pairwise inequivalent
  irreducible representations of `G` as `G` has conjugacy classes**, in the form of a family indexed
  by `ConjClasses G`, whose dimensions have squares summing to `|G|`.

## References

This supplies one half of the block ⇆ irreducible-representation matching that Layer 2.5 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
asks for, in the concrete form needed by Layer 3's completeness statement. See J.-P. Serre, *Linear
Representations of Finite Groups*, Section 6.4, or I. M. Isaacs, *Character Theory of Finite
Groups*, Chapter 1.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u v w

section Block

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G] {ι : Type w} {d : ι → ℕ}
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)

/-- The algebra map from the group algebra onto the endomorphisms of the `i`-th column space of a
Wedderburn presentation: project `e` onto the `i`-th matrix block and let a matrix act on column
vectors. -/
noncomputable def blockAlgHom (i : ι) : k[G] →ₐ[k] Module.End k (Fin (d i) → k) :=
  (Matrix.toLinAlgEquiv' (n := Fin (d i)) (R := k)).toAlgHom.comp
    ((Pi.evalAlgHom k (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i).comp e.toAlgHom)

@[simp]
theorem blockAlgHom_apply (i : ι) (x : k[G]) :
    blockAlgHom e i x = Matrix.toLinAlgEquiv' (e x i) := by
  simp [blockAlgHom]

/-- Each block of a Wedderburn presentation exhausts the endomorphisms of its column space: `e` is
bijective, the projection onto a factor is surjective, and matrices are all the endomorphisms of a
coordinate space. -/
theorem blockAlgHom_surjective (i : ι) : Function.Surjective (blockAlgHom e i) := by
  classical
  intro T
  refine ⟨e.symm (Pi.single i (Matrix.toLinAlgEquiv'.symm T)), ?_⟩
  simp

/-- **The representation of `G` on the `i`-th block of a Wedderburn presentation of `k[G]`**: the
group acts on the column space `Fin (d i) → k` through the `i`-th matrix factor. -/
noncomputable def blockRepresentation (i : ι) : Representation k G (Fin (d i) → k) :=
  (blockAlgHom e i).toMonoidHom.comp (MonoidAlgebra.of k G)

@[simp]
theorem blockRepresentation_apply (i : ι) (g : G) :
    blockRepresentation e i g = Matrix.toLinAlgEquiv' (e (MonoidAlgebra.of k G g) i) := by
  simp [blockRepresentation]

/-- The algebra map of `TauCeti.blockRepresentation` is the block projection it was built from. -/
@[simp]
theorem asAlgebraHom_blockRepresentation (i : ι) :
    (blockRepresentation e i).asAlgebraHom = blockAlgHom e i := by
  refine AlgHom.ext fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [Representation.asAlgebraHom_of]; simp [blockRepresentation]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul r x hx => rw [map_smul, map_smul, hx]

end Block

section Irreducible

variable {k : Type u} {G : Type v} [Field k] [Monoid G] {ι : Type w} {d : ι → ℕ}
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)

/-- **Every Wedderburn block carries an irreducible representation.** -/
theorem isIrreducible_blockRepresentation (i : ι) [NeZero (d i)] :
    (blockRepresentation e i).IsIrreducible := by
  have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  have : Nontrivial (Fin (d i) → k) := inferInstance
  exact Representation.isIrreducible_of_asAlgebraHom_surjective _
    (by simpa using blockAlgHom_surjective e i)

end Irreducible

section Inequivalent

variable {k : Type u} {G : Type v} [CommSemiring k] [Nontrivial k] [Monoid G] {ι : Type w}
  {d : ι → ℕ}
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)

/-- **Distinct Wedderburn blocks carry inequivalent representations.** The idempotent that `e`
matches with `Pi.single i 1` acts as the identity on the `i`-th block and as zero on the `j`-th. -/
theorem isEmpty_equiv_blockRepresentation {i j : ι} [NeZero (d i)] (hij : i ≠ j) :
    IsEmpty ((blockRepresentation e i).Equiv (blockRepresentation e j)) := by
  classical
  have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  have : Nontrivial (Fin (d i) → k) := inferInstance
  refine ⟨fun φ => ?_⟩
  set u : k[G] := e.symm (Pi.single i 1) with hu
  have hcomm : ∀ x : k[G], ∀ v : Fin (d i) → k,
      φ ((blockRepresentation e i).asAlgebraHom x v) =
        (blockRepresentation e j).asAlgebraHom x (φ v) := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
        intro v
        simpa using Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v
    | add x y hx hy =>
        intro v
        simp only [map_add, LinearMap.add_apply, map_add, hx v, hy v]
    | smul r x hx =>
        intro v
        simp only [map_smul, LinearMap.smul_apply, map_smul, hx v]
  have hi : (blockRepresentation e i).asAlgebraHom u = 1 := by
    simp [hu]
  have hj : (blockRepresentation e j).asAlgebraHom u = 0 := by
    simp [hu, Pi.single_eq_of_ne (Ne.symm hij)]
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin (d i) → k)
  refine hv (φ.toLinearEquiv.injective ?_)
  have hv0 := hcomm u v
  rw [hi, hj] at hv0
  simpa using hv0

end Inequivalent

section Existence

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
  [IsAlgClosed k]

/-- **There are as many pairwise inequivalent irreducible representations of `G` as `G` has
conjugacy classes.** Maschke and Artin--Wedderburn present `k[G]` with its blocks indexed by
`ConjClasses G`, and the blocks carry pairwise inequivalent irreducible representations, of
dimensions whose squares add up to `|G|`, that being the dimension of `k[G]`.

The bound in the other direction, that no family of pairwise inequivalent irreducibles is larger,
is `TauCeti.ClassFunction.card_le_card_conjClasses`. -/
theorem exists_irreducible_family_conjClasses :
    ∃ (d : ConjClasses G → ℕ) (ρ : ∀ C, Representation k G (Fin (d C) → k)),
      (∀ C, (ρ C).IsIrreducible) ∧ (Pairwise fun C D => IsEmpty ((ρ C).Equiv (ρ D))) ∧
        ∑ᶠ C, d C ^ 2 = Nat.card G := by
  obtain ⟨d, hd, hsum, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_conjClasses k G
  have := hd
  exact ⟨d, blockRepresentation e, fun C => isIrreducible_blockRepresentation e C,
    fun _ _ h => isEmpty_equiv_blockRepresentation e h, hsum⟩

end Existence

end TauCeti
