/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Semisimple.CentralCharacter
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Eigenrow
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Integral
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The central character of an irreducible representation

The centre of `k[G]` acts on an irreducible representation by scalars: a central element acts by an
intertwiner, and Schur's lemma over an algebraically closed field leaves only scalars. Recording
those scalars is the **central character** `ωᵪ : Z(k[G]) →ₐ[k] k` of the representation, the
general construction `TauCeti.centralCharacter` read on `ρ.asModule`.

Its values on the class sums are the character-theoretic content: taking traces in
`ρ(K_C) = ωᵪ(K_C) · id` turns the defining scalar identity into `ωᵪ(K_C) · χ(1) = |C| · χ(g)` for
any `g` in the class `C`. That identity is stated here without division, so that it holds over
every algebraically closed field; dividing by the degree `χ(1)` needs it to be invertible, which it
is in characteristic zero.

Because the class sums are integral over `ℤ` and an algebra homomorphism preserves integrality,
every value `ωᵪ(K_C)` is an algebraic integer. This is the input to the divisibility `χ(1) ∣ |G|`
and to the Dixon-Schneider algorithm, where the row `C ↦ ωᵪ(K_C)` is a common left eigenrow of the
class-multiplication matrices.

## Main definitions

* `TauCeti.Representation.centralCharacter`: the central character of an irreducible
  representation, a `k`-algebra homomorphism out of the centre of the group algebra.

## Main statements

* `TauCeti.Representation.asAlgebraHom_apply_of_mem_center`: a central element of the group algebra
  acts on the representation as the scalar its central character records.
* `TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one`: the class-sum
  identity `ωᵪ(K_C) · χ(1) = |C| · χ(g)`, in its division-free form, with
  `TauCeti.Representation.centralCharacter_classSumCenter` the quotient form for an invertible
  degree.
* `TauCeti.Representation.isIntegral_centralCharacter_classSumCenter`: the values of the central
  character on the class sums are algebraic integers.
* `TauCeti.Representation.isClassEigenrow_classSumRow_centralCharacter`: those values form a common
  left eigenrow of the class-multiplication matrices, which is what the Dixon-Schneider
  characterization consumes.
* `TauCeti.Representation.centralCharacter_trivial_classSumCenter`: the worked case of the trivial
  representation, where the value on a class sum is the size of the class.

## Implementation notes

These declarations live in `TauCeti.Representation`, not in the root `Representation` namespace, so
dot notation on a representation does not reach them: they are applied as `centralCharacter ρ`.

## References

This implements the "central characters, integrally" item of Layer 4 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
See I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 3, or J.-P. Serre, *Linear
Representations of Finite Groups*, Section 6.5.
-/

public section

open Module (finrank)
open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-! ### The action of a class sum -/

section ClassSum

variable [Fintype G] [DecidableEq G]

/-- A class sum acts on a representation by the sum of the actions of the elements of the class. -/
theorem asAlgebraHom_classSum (C : ConjClasses G) :
    ρ.asAlgebraHom (classSum k C) = ∑ x : C.carrier, ρ (x : G) := by
  rw [classSum_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun x _ => ρ.asAlgebraHom_of x

/-- The character is constant on a conjugacy class, so the trace of the action of a class sum is
the size of the class times the character value there. -/
theorem trace_asAlgebraHom_classSum {C : ConjClasses G} {g : G} (hg : ConjClasses.mk g = C) :
    LinearMap.trace k V (ρ.asAlgebraHom (classSum k C)) = Nat.card C.carrier * ρ.character g := by
  rw [asAlgebraHom_classSum, map_sum]
  have hconst : ∀ x : C.carrier, LinearMap.trace k V (ρ (x : G)) = ρ.character g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp (hg.trans (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm))
    exact ρ.char_conj g c
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

end ClassSum

/-! ### The central character -/

variable [IsAlgClosed k] [FiniteDimensional k V] [ρ.IsIrreducible]

/-- The **central character** of an irreducible representation: the algebra homomorphism recording
the scalar by which each central element of the group algebra acts.

An irreducible representation is a simple `k[G]`-module, so this is `TauCeti.centralCharacter` for
the algebra `k[G]`; the roadmap writes it `ωᵪ`. -/
noncomputable def centralCharacter : Subalgebra.center k k[G] →ₐ[k] k :=
  TauCeti.centralCharacter k k[G] ρ.asModule

/-- A central element of the group algebra acts on the representation as multiplication by the
value of the central character. -/
theorem asAlgebraHom_apply_of_mem_center (z : Subalgebra.center k k[G]) (v : V) :
    ρ.asAlgebraHom (z : k[G]) v = centralCharacter ρ z • v := by
  have h : (z : k[G]) • ρ.asModuleEquiv.symm v =
      centralCharacter ρ z • ρ.asModuleEquiv.symm v :=
    (TauCeti.centralCharacter_smul k k[G] ρ.asModule z _).symm
  have h' := congrArg ρ.asModuleEquiv h
  rwa [_root_.Representation.asModuleEquiv_map_smul, map_smul,
    LinearEquiv.apply_symm_apply] at h'

/-- A central element of the group algebra acts on an irreducible representation by a scalar
endomorphism. -/
theorem asAlgebraHom_of_mem_center (z : Subalgebra.center k k[G]) :
    ρ.asAlgebraHom (z : k[G]) = centralCharacter ρ z • LinearMap.id :=
  LinearMap.ext fun v => asAlgebraHom_apply_of_mem_center ρ z v

/-- The trace of the action of a central element is its central character times the degree. -/
theorem trace_asAlgebraHom_of_mem_center (z : Subalgebra.center k k[G]) :
    LinearMap.trace k V (ρ.asAlgebraHom (z : k[G])) = centralCharacter ρ z * finrank k V := by
  rw [asAlgebraHom_of_mem_center, map_smul, LinearMap.trace_id, smul_eq_mul]

section Finite

variable [Fintype G] [DecidableEq G]

/-- **The central character on a class sum.** In division-free form: the value of the central
character on the class sum of `C`, times the degree `χ(1)`, is the size of `C` times the character
value on `C`.

This is the identity `ωᵪ(K_C) = |C| · χ(g) / χ(1)` of the roadmap, stated so that no invertibility
of the degree is needed; see `TauCeti.Representation.centralCharacter_classSumCenter` for the
quotient form. -/
theorem centralCharacter_classSumCenter_mul_character_one {C : ConjClasses G} {g : G}
    (hg : ConjClasses.mk g = C) :
    centralCharacter ρ (classSumCenter C) * ρ.character 1 =
      Nat.card C.carrier * ρ.character g := by
  rw [ρ.char_one, ← trace_asAlgebraHom_of_mem_center ρ (classSumCenter C), classSumCenter_coe,
    trace_asAlgebraHom_classSum ρ hg]

/-- The central character on a class sum, in quotient form, when the degree of the representation
is nonzero in `k`; it is nonzero whenever `k` has characteristic zero. -/
theorem centralCharacter_classSumCenter {C : ConjClasses G} {g : G} (hg : ConjClasses.mk g = C)
    (hχ : ρ.character 1 ≠ 0) :
    centralCharacter ρ (classSumCenter C) = Nat.card C.carrier * ρ.character g / ρ.character 1 :=
  eq_div_of_mul_eq hχ (centralCharacter_classSumCenter_mul_character_one ρ hg)

/-- **The values of a central character on the class sums are algebraic integers.**

The class sums are integral over `ℤ` in the centre of `k[G]`, and an algebra homomorphism carries
integral elements to integral elements. -/
theorem isIntegral_centralCharacter_classSumCenter (C : ConjClasses G) :
    IsIntegral ℤ (centralCharacter ρ (classSumCenter C)) :=
  (isIntegral_classSumCenter k C).map ((centralCharacter ρ).restrictScalars ℤ)

/-- The values of a central character on the class sums form a common left eigenrow of the
class-multiplication matrices: this is the row that the Dixon-Schneider characterization of the
character table computes with. It is the specialization of
`TauCeti.isClassEigenrow_classSumRow` to the central character. -/
theorem isClassEigenrow_classSumRow_centralCharacter :
    IsClassEigenrow (classSumRow (centralCharacter ρ)) :=
  isClassEigenrow_classSumRow _

end Finite

/-! ### The trivial representation -/

section Trivial

variable (k G) [Fintype G] [DecidableEq G]

/-- The central character of the trivial representation on the base field sends the class sum of
`C` to the size of `C`: every group element acts by the identity there, so a class sum acts by the
number of its terms.

This pins the normalization of `TauCeti.Representation.centralCharacter`, and is the case `χ = 1`
of `TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one`. -/
theorem centralCharacter_trivial_classSumCenter (C : ConjClasses G) :
    centralCharacter (_root_.Representation.trivial k G k) (classSumCenter C) =
      Nat.card C.carrier := by
  have h := asAlgebraHom_apply_of_mem_center (_root_.Representation.trivial k G k)
    (classSumCenter C) (1 : k)
  rw [classSumCenter_coe, asAlgebraHom_classSum, LinearMap.sum_apply] at h
  simp only [_root_.Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card, ← h]

end Trivial

end Representation

end TauCeti
