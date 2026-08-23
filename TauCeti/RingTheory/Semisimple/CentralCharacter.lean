/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Schur

/-!
# The central character of a simple module

A central element `z` of a `k`-algebra `A` acts on an `A`-module `M` by an `A`-linear map, because
`z` commutes with every scalar; this is the algebra homomorphism `TauCeti.centerToEnd`. When `M` is
a finite-dimensional simple module over an algebraically closed field `k`, Schur's lemma collapses
the endomorphism algebra to `k` itself, so the action of the centre is by honest scalars. The
resulting `k`-algebra homomorphism `Z(A) → k` is the **central character** of `M`.

For `A = k[G]` this is the character-theoretic `ωᵪ`. Its value on the class sum of a conjugacy
class `C` with representative `g` is the entry `χ(g)` of the character table weighted by the class
size and normalized by the degree: `ωᵪ(K_C) = |C| · χ(g) / χ(1)`, when `χ(1) ≠ 0` in `k`.

## Main definitions

* `TauCeti.centerToEnd`: a central element of `A` acts on an `A`-module by an `A`-linear
  endomorphism, as a homomorphism of `k`-algebras `Z(A) →ₐ[k] End_A M`. No simplicity or
  finiteness hypothesis is needed.
* `TauCeti.centralCharacter`: the central character `Z(A) →ₐ[k] k` of a finite-dimensional simple
  module over an algebraically closed field.

## Main statements

* `TauCeti.smul_eq_centralCharacter_smul`: the defining property, that a central element acts as
  multiplication by its central character.
* `TauCeti.centralCharacter_eq_of_smul_eq`: the central character is the *only* scalar with that
  property, in the form asking for the equality at every vector.
* `TauCeti.centralCharacter_eq_of_ne_zero_of_smul_eq`: the sharper form, computing the central
  character from the action on a single nonzero vector.

## References

This implements the "central characters" item of Layer 4 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
in the generality of a simple module over an arbitrary algebra. See I. M. Isaacs, *Character
Theory of Finite Groups*, Chapter 3, or C. W. Curtis and I. Reiner, *Representation Theory of
Finite Groups and Associative Algebras*, §33.
-/

public section

namespace TauCeti

universe u v w

/-! ### The action of the centre -/

section CenterToEnd

variable (k : Type u) [CommSemiring k] (A : Type v) [Semiring A] [Algebra k A]
variable (M : Type w) [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- A central element of `A` acts on an `A`-module `M` by an `A`-linear endomorphism, and doing so
is a homomorphism of `k`-algebras from the centre of `A` to `End_A M`.

Centrality is exactly what makes the action `A`-linear rather than merely additive; Mathlib's
`Module.End.smulLeft` packages the individual endomorphism. -/
def centerToEnd : Subalgebra.center k A →ₐ[k] Module.End A M where
  toFun z := Module.End.smulLeft (M := M) (z : A)
    (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp z.2))
  map_one' := by ext m; simp
  map_mul' z w := by ext m; simp [smul_smul, Subalgebra.mem_center_iff.mp w.2 (z : A)]
  map_zero' := by ext m; simp
  map_add' z w := by ext m; simp [add_smul]
  commutes' r := by ext m; simp [algebraMap_smul]

/-- The endomorphism attached to a central element is multiplication by it. -/
@[simp]
theorem centerToEnd_apply (z : Subalgebra.center k A) (m : M) :
    centerToEnd k A M z m = (z : A) • m :=
  (rfl)

end CenterToEnd

/-! ### The central character of a simple module -/

section CentralCharacter

variable (k : Type u) [Field k] [IsAlgClosed k] (A : Type v) [Ring A] [Algebra k A]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable [IsSimpleModule A M] [FiniteDimensional k M]

/-- The **central character** of a finite-dimensional simple module `M` over a `k`-algebra `A`,
for `k` algebraically closed: the homomorphism of `k`-algebras recording the scalar by which each
central element of `A` acts on `M`.

The scalar exists because the action of a central element is `A`-linear (`TauCeti.centerToEnd`)
and every `A`-linear endomorphism of `M` is a scalar (Schur's lemma,
`TauCeti.endAlgEquivSelfOfIsSimpleModule`). -/
noncomputable def centralCharacter : Subalgebra.center k A →ₐ[k] k :=
  (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := M)).toAlgHom.comp (centerToEnd k A M)

/-- The defining property of the central character: a central element acts on the module as
multiplication by the scalar the central character assigns to it.

This is the simp normal form: the opaque action of the centre is replaced by the action of a
scalar, which is the whole point of the construction. -/
@[simp]
theorem smul_eq_centralCharacter_smul (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centralCharacter k A M z • m :=
  (endAlgEquivSelfOfIsSimpleModule_smul (k := k) (centerToEnd k A M z) m).symm

variable {k A M}

/-- The central character is determined by the action of a central element on a single nonzero
vector: no other scalar can reproduce it there. -/
theorem centralCharacter_eq_of_ne_zero_of_smul_eq {z : Subalgebra.center k A} {c : k} {m : M}
    (hm : m ≠ 0) (h : (z : A) • m = c • m) : centralCharacter k A M z = c := by
  have hsub : (centralCharacter k A M z - c) • m = 0 := by
    rw [sub_smul, ← smul_eq_centralCharacter_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hm)

/-- The central character is the unique scalar by which a central element acts.

A simple module is nonzero, which is what rules out the degenerate case where every scalar would
qualify. -/
theorem centralCharacter_eq_of_smul_eq {z : Subalgebra.center k A} {c : k}
    (h : ∀ m : M, (z : A) • m = c • m) : centralCharacter k A M z = c := by
  have : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact centralCharacter_eq_of_ne_zero_of_smul_eq hm (h m)

end CentralCharacter

end TauCeti
