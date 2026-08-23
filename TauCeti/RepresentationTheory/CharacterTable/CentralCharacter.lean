/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.CentralCharacter
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Integral
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Representation

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
class-multiplication matrices; that eigenrow property holds of any algebra homomorphism out of the
centre, and is `TauCeti.isClassEigenrow_classSumRow` applied to a central character.

## Main definitions

* `TauCeti.Representation.centralCharacter`: the central character of an irreducible
  representation, a `k`-algebra homomorphism out of the centre of the group algebra.

## Main statements

* `TauCeti.Representation.asAlgebraHom_center_apply`: a central element of the group algebra
  acts on the representation as the scalar its central character records, and
  `TauCeti.Representation.centralCharacter_eq_of_ne_zero_of_asAlgebraHom_apply_eq`: that scalar is
  the only one doing so at a single nonzero vector.
* `TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one`: the class-sum
  identity `ωᵪ(K_C) · χ(1) = |C| · χ(g)`, in its division-free form, with
  `TauCeti.Representation.centralCharacter_classSumCenter` the quotient form for an invertible
  degree.
* `TauCeti.Representation.centralCharacter_eq_of_equiv`: equivalent irreducible representations
  have the same central character.
* `TauCeti.Representation.isIntegral_centralCharacter_classSumCenter`: the values of the central
  character on the class sums are algebraic integers.
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

/-! ### The central character -/

variable [IsAlgClosed k] [FiniteDimensional k V] [ρ.IsIrreducible]

/-- The **central character** of an irreducible representation: the algebra homomorphism recording
the scalar by which each central element of the group algebra acts.

An irreducible representation is a simple `k[G]`-module, so this is `TauCeti.centralCharacter` for
the algebra `k[G]`; the roadmap writes it `ωᵪ`. -/
noncomputable def centralCharacter : Subalgebra.center k k[G] →ₐ[k] k :=
  TauCeti.centralCharacter k k[G] ρ.asModule

/-- A central element of the group algebra acts on the representation as multiplication by the
value of the central character.

Not itself `@[simp]`: simp reaches this normal form from the map-level
`TauCeti.Representation.asAlgebraHom_center` below. -/
theorem asAlgebraHom_center_apply (z : Subalgebra.center k k[G]) (v : V) :
    ρ.asAlgebraHom (z : k[G]) v = centralCharacter ρ z • v := by
  have h : (z : k[G]) • ρ.asModuleEquiv.symm v =
      centralCharacter ρ z • ρ.asModuleEquiv.symm v :=
    TauCeti.smul_eq_centralCharacter_smul k k[G] ρ.asModule z _
  have h' := congrArg ρ.asModuleEquiv h
  rwa [_root_.Representation.asModuleEquiv_map_smul, map_smul,
    LinearEquiv.apply_symm_apply] at h'

/-- A central element of the group algebra acts on an irreducible representation by a scalar
endomorphism.

This is the simp normal form for the action of the centre: the opaque action is replaced by a
scalar, applied or not. -/
@[simp]
theorem asAlgebraHom_center (z : Subalgebra.center k k[G]) :
    ρ.asAlgebraHom (z : k[G]) = centralCharacter ρ z • LinearMap.id :=
  LinearMap.ext fun v => asAlgebraHom_center_apply ρ z v

/-- The central character is determined by the action of a central element on a single nonzero
vector: no other scalar can reproduce it there.

This is `TauCeti.centralCharacter_eq_of_ne_zero_of_smul_eq` read through
`Representation.asModuleEquiv`. -/
theorem centralCharacter_eq_of_ne_zero_of_asAlgebraHom_apply_eq {z : Subalgebra.center k k[G]}
    {c : k} {v : V} (hv : v ≠ 0) (h : ρ.asAlgebraHom (z : k[G]) v = c • v) :
    centralCharacter ρ z = c := by
  have hv' : ρ.asModuleEquiv.symm v ≠ 0 := fun h0 =>
    hv (by simpa using congrArg ρ.asModuleEquiv h0)
  refine TauCeti.centralCharacter_eq_of_ne_zero_of_smul_eq hv' (ρ.asModuleEquiv.injective ?_)
  rw [_root_.Representation.asModuleEquiv_map_smul, map_smul, LinearEquiv.apply_symm_apply, h]

/-- The trace of the action of a central element is its central character times the degree. -/
theorem trace_asAlgebraHom_center (z : Subalgebra.center k k[G]) :
    LinearMap.trace k V (ρ.asAlgebraHom (z : k[G])) = centralCharacter ρ z * finrank k V := by
  rw [asAlgebraHom_center, map_smul, LinearMap.trace_id, smul_eq_mul]

/-- **Equivalent irreducible representations have the same central character.** An equivalence
commutes with the action of the group algebra, so it carries the scalar action of the centre on one
to the scalar action on the other; a nonzero vector then forces the two scalars to agree. -/
theorem centralCharacter_eq_of_equiv {W : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (σ : _root_.Representation k G W) [σ.IsIrreducible] (φ : ρ.Equiv σ) :
    centralCharacter σ = centralCharacter ρ := by
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] _
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hφv : φ.toIntertwiningMap v ≠ 0 := fun h0 =>
    hv (φ.toLinearEquiv.injective (by simpa using h0))
  refine AlgHom.ext fun z => ?_
  have h : φ.toIntertwiningMap (ρ.asAlgebraHom (z : k[G]) v) =
      σ.asAlgebraHom (z : k[G]) (φ.toIntertwiningMap v) :=
    (_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
      φ.toIntertwiningMap).map_smul' (z : k[G]) v
  refine centralCharacter_eq_of_ne_zero_of_asAlgebraHom_apply_eq σ hφv ?_
  rw [← h, asAlgebraHom_center_apply, map_smul]

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
  rw [ρ.char_one, ← trace_asAlgebraHom_center ρ (classSumCenter C), classSumCenter_coe,
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

end Finite

/-! ### The trivial representation -/

section Trivial

variable (k G) [Fintype G] [DecidableEq G]

/-- The central character of the trivial representation on the base field sends the class sum of
`C` to the size of `C`: every group element acts by the identity there, so a class sum acts by the
number of its terms.

This pins the normalization of `TauCeti.Representation.centralCharacter`. It is derived from
`TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one` as the case `χ = 1`,
where both the degree and the character value on the class are `1`.

This is the simp normal form of the value: the central character of the trivial representation on a
class sum is evaluated to the size of the class. -/
@[simp]
theorem centralCharacter_trivial_classSumCenter (C : ConjClasses G) :
    centralCharacter (_root_.Representation.trivial k G k) (classSumCenter C) =
      Nat.card C.carrier := by
  have hchar : ∀ x : G, (_root_.Representation.trivial k G k).character x = 1 := fun x => by
    have : (_root_.Representation.trivial k G k) x = LinearMap.id :=
      LinearMap.ext fun v => by simp
    simp [_root_.Representation.character, this]
  obtain ⟨g, hg⟩ := C.exists_rep
  simpa [hchar] using
    centralCharacter_classSumCenter_mul_character_one (_root_.Representation.trivial k G k) hg

end Trivial

end Representation

end TauCeti
