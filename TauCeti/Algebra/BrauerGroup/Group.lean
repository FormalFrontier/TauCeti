/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.BrauerGroup.Trivial` is imported publicly: `TauCeti.IsBrauerTrivial` occurs in
-- the statements below, and its theorems `TauCeti.isBrauerTrivial_tensorOp` (which becomes the
-- inverse law) and `TauCeti.isBrauerTrivial_of_isSplittingField` are what the group law and its
-- corollaries run on. It re-exports `TauCeti.Algebra.BrauerGroup.Basic`, hence `CSA`,
-- `IsBrauerEquivalent`, `BrauerGroup`, the constructors `TauCeti.CSA.of`, `TauCeti.CSA.base`,
-- `TauCeti.CSA.matrix` and `TauCeti.CSA.tensorProduct` with the four Brauer equivalences of the
-- tensor product, `TauCeti.Algebra.IsSplittingField`, and `TauCeti.Algebra.CentralSimple.Opposite`,
-- hence the central simple structure on `Aᵐᵒᵖ` and, arriving with it, Mathlib's opposite-algebra
-- and opposite-matrix isomorphisms `AlgEquiv.op` and `AlgEquiv.mopMatrix`; that is why none of
-- those is imported again here.
public import TauCeti.Algebra.BrauerGroup.Trivial
-- `Mathlib.GroupTheory.OrderOfElement` is imported publicly: `orderOf` occurs in the statements of
-- the order results closing the file, so importers of this module get it with them.
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The Brauer group of a field is a commutative group

Two finite-dimensional central simple `K`-algebras are **Brauer equivalent** when they become
isomorphic after passing to matrix algebras over them (Mathlib's `IsBrauerEquivalent`), and
`BrauerGroup K` is the quotient of `CSA K` by that relation. Mathlib defines that quotient and
records making it a group as a TODO; `TauCeti/Algebra/BrauerGroup/Basic.lean` supplies the
constructors, the two moves that leave a Brauer class unchanged, and the behaviour of `⊗[K]` under
them, and `TauCeti/Algebra/BrauerGroup/Trivial.lean` supplies the class that will be the identity.
This file assembles those pieces into the group.

The multiplication is induced by the tensor product: it is well defined on classes because
`TauCeti.isBrauerEquivalent_tensorProduct_congr` says `⊗[K]` respects Brauer equivalence, and
associative, commutative and unital because
`TauCeti.isBrauerEquivalent_tensorProduct_assoc`, `TauCeti.isBrauerEquivalent_tensorProduct_comm`
and `TauCeti.isBrauerEquivalent_tensorProduct_base` say so already at the level of algebras -- in
each case up to an actual isomorphism, which is a Brauer equivalence. The one law that is not
inherited from an isomorphism of algebras is the existence of inverses: the inverse of the class of
`A` is the class of the opposite algebra `Aᵐᵒᵖ`, and the reason `A ⊗[K] Aᵐᵒᵖ` is trivial is the
Azumaya isomorphism `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] M_{finrank K A}(K)` behind
`TauCeti.isBrauerTrivial_tensorOp`. The new ingredient this file has to supply for that is that
`Aᵐᵒᵖ` is a move on classes at all, `TauCeti.isBrauerEquivalent_op_congr`.

## The universe

The group structure is stated for `BrauerGroup.{u, u} K`, the classes of central simple algebras
living in the same universe as `K`. This is not incidental: the identity of the group is the class
of `K` itself, so the identity is available exactly when the algebras are allowed to live in the
universe of `K`. The universe-polymorphic statements about `BrauerGroup.{u, v} K` that do not
mention the identity -- for instance the two `Subsingleton` results of
`TauCeti/Algebra/BrauerGroup/Trivial.lean` -- are unaffected, and `TauCeti.BrauerGroup.mk` itself is
stated in the universe-polymorphic form.

## Main definitions and results

* `TauCeti.CSA.op`: the opposite of a central simple algebra, again a central simple algebra.
* `TauCeti.isBrauerEquivalent_op_congr`: passing to the opposite algebra respects Brauer
  equivalence, so it descends to the classes.
* `TauCeti.BrauerGroup.mk`: the Brauer class of a central simple algebra, with
  `TauCeti.BrauerGroup.inductionOn` its elimination principle.
* `TauCeti.BrauerGroup.instCommGroup`: **the Brauer group of a field is a commutative group**, with
  multiplication induced by `⊗[K]`, identity the class of `K`, and the class of `Aᵐᵒᵖ` inverse to
  the class of `A`.
* `TauCeti.BrauerGroup.mk_eq_one_iff`: a class is the identity exactly when its algebras are
  Brauer trivial; with `TauCeti.BrauerGroup.mk_eq_one_of_isSplittingField` and
  `TauCeti.BrauerGroup.mk_end` as the two standard sources of identity classes.
* `TauCeti.BrauerGroup.orderOf_mk_dvd_two`: an algebra Brauer equivalent to its own opposite has a
  class of order dividing `2`, with `TauCeti.BrauerGroup.orderOf_mk_eq_two` the sharp form for a
  class that is not the identity. The real quaternions are the worked example in
  `TauCeti/Algebra/BrauerGroup/Quaternion.lean`.

## What is not proved here

The converse of `TauCeti.BrauerGroup.mk_eq_one_of_isSplittingField` -- that an algebra whose class
is the identity is split by `K` -- needs the uniqueness of the Wedderburn data, which sits above
this file in the import order; it is `TauCeti.BrauerGroup.mk_eq_one_iff_isSplittingField`, in
`TauCeti/Algebra/BrauerGroup/Splitting.lean`. It is also what supplies, in an example such as
`ℍ[ℝ]`, the nonidentity hypothesis that `TauCeti.BrauerGroup.orderOf_mk_eq_two` needs to sharpen
the divisibility `orderOf (mk (CSA.of ℝ ℍ[ℝ])) ∣ 2` to the equality `= 2`. The functoriality of
`BrauerGroup` under base change is not taken here either, but it is on record one file up:
`TauCeti.BrauerGroup.baseChange` in `TauCeti/Algebra/BrauerGroup/BaseChange.lean`, whose kernel is
described there as the classes that become Brauer trivial over the extension
(`TauCeti.BrauerGroup.mk_mem_ker_baseChange_iff`). Identifying that kernel with the classes *split*
by the extension is the converse above again, one field up, and is not proved anywhere yet.

## References

This is the second bullet of Layer 6 ("The Brauer group as a group") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
pinned there as `brauerCommGroup`, together with the Brauer-group half of its Hamilton-quaternion
worked example. It also settles the first TODO of Mathlib's `Mathlib/Algebra/BrauerGroup/Defs.lean`.
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.4, and
R. S. Pierce, *Associative Algebras*, Springer GTM 88 (1982), Chapter 12.
-/

public section

universe u v

namespace TauCeti

variable {K : Type u} [Field K]

/-! ### The opposite algebra as a move on Brauer classes -/

/-- The opposite of a finite-dimensional central simple `K`-algebra, again a finite-dimensional
central simple `K`-algebra: centrality and simplicity are both stable under `ᵐᵒᵖ` (instances in
Mathlib's `Algebra/Central/Basic.lean` and `RingTheory/SimpleRing/Basic.lean`), and so is the
dimension.

This is the constructor for the inverse of the group law on `BrauerGroup K`
(`TauCeti.BrauerGroup.mk_op`); the reason it *is* an inverse is
`TauCeti.isBrauerTrivial_tensorOp`. -/
abbrev CSA.op (A : CSA.{u, v} K) : CSA.{u, v} K := CSA.of K (A : Type v)ᵐᵒᵖ

/-- **Passing to the opposite algebra respects Brauer equivalence**, so it descends to a map of
Brauer classes.

The witness is the one of the hypothesis, in the same two sizes: transposition identifies
`Mₙ(Aᵐᵒᵖ)` with `Mₙ(A)ᵐᵒᵖ` (Mathlib's `AlgEquiv.mopMatrix`), and an isomorphism
`Mₙ(A) ≃ₐ[K] Mₘ(B)` opposes to `Mₙ(A)ᵐᵒᵖ ≃ₐ[K] Mₘ(B)ᵐᵒᵖ`. -/
theorem isBrauerEquivalent_op_congr {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (CSA.op A) (CSA.op B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨AlgEquiv.mopMatrix.trans ((AlgEquiv.op e).trans AlgEquiv.mopMatrix.symm)⟩⟩

namespace BrauerGroup

/-! ### Brauer classes -/

/-- The **Brauer class** of a finite-dimensional central simple `K`-algebra.

Mathlib's `BrauerGroup K` is the quotient of `CSA K` by `Brauer.CSA_Setoid K`, which is a `def` and
not an instance, so the quotient notation `⟦A⟧` is unavailable; this is the name for the projection
that the lemmas below are stated in terms of. -/
abbrev mk (A : CSA.{u, v} K) : BrauerGroup.{u, v} K := Quotient.mk (Brauer.CSA_Setoid K) A

/-- To prove a property of every Brauer class, it suffices to prove it for the class of every
finite-dimensional central simple algebra. -/
@[elab_as_elim]
protected theorem inductionOn {motive : BrauerGroup.{u, v} K → Prop} (x : BrauerGroup.{u, v} K)
    (h : ∀ A : CSA.{u, v} K, motive (mk A)) : motive x :=
  Quotient.inductionOn x h

/-- **Two algebras have the same Brauer class exactly when they are Brauer equivalent.** -/
@[simp]
theorem mk_eq_mk_iff {A B : CSA.{u, v} K} : mk A = mk B ↔ IsBrauerEquivalent A B :=
  ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

/-- Isomorphic algebras have the same Brauer class. -/
theorem mk_eq_mk_of_algEquiv {A B : CSA.{u, v} K} (e : A ≃ₐ[K] B) : mk A = mk B :=
  mk_eq_mk_iff.2 (IsBrauerEquivalent.of_algEquiv K e)

/-- **Passing to matrices does not change the Brauer class.** -/
@[simp]
theorem mk_matrix (A : CSA.{u, v} K) (n : ℕ) [NeZero n] : mk (CSA.matrix A n) = mk A :=
  mk_eq_mk_iff.2 (isBrauerEquivalent_matrix K A n)

/-! ### The group structure -/

/-- **The Brauer group of a field is a commutative group.**

Multiplication is induced by the tensor product over `K`, which respects Brauer equivalence
(`TauCeti.isBrauerEquivalent_tensorProduct_congr`); the identity is the class of `K` itself; and the
inverse of the class of `A` is the class of `Aᵐᵒᵖ`, which respects Brauer equivalence by
`TauCeti.isBrauerEquivalent_op_congr` and is an inverse by `TauCeti.isBrauerTrivial_tensorOp`.
Associativity, commutativity and the unit law hold already for the algebras, up to isomorphism.

The universe is pinned at `BrauerGroup.{u, u} K` because the identity is the class of `K`, which
lives in `Type u`; see the module docstring. -/
instance instCommGroup : CommGroup (BrauerGroup.{u, u} K) where
  mul x y := Quotient.liftOn₂ x y (fun A B ↦ mk (CSA.tensorProduct A B))
    fun _ _ _ _ h₁ h₂ ↦ Quotient.sound (isBrauerEquivalent_tensorProduct_congr K h₁ h₂)
  one := mk (CSA.base K)
  inv x := Quotient.liftOn x (fun A ↦ mk (CSA.op A))
    fun _ _ h ↦ Quotient.sound (isBrauerEquivalent_op_congr h)
  mul_assoc x y z := Quotient.inductionOn₃ x y z fun A B C ↦
    Quotient.sound (isBrauerEquivalent_tensorProduct_assoc K A B C)
  mul_comm x y := Quotient.inductionOn₂ x y fun A B ↦
    Quotient.sound (isBrauerEquivalent_tensorProduct_comm K A B)
  one_mul x := Quotient.inductionOn x fun A ↦ Quotient.sound <|
    (isBrauerEquivalent_tensorProduct_comm K (CSA.base K) A).trans
      (isBrauerEquivalent_tensorProduct_base K A)
  mul_one x := Quotient.inductionOn x fun A ↦
    Quotient.sound (isBrauerEquivalent_tensorProduct_base K A)
  inv_mul_cancel x := Quotient.inductionOn x fun A ↦ Quotient.sound <|
    (isBrauerEquivalent_tensorProduct_comm K (CSA.op A) A).trans (isBrauerTrivial_tensorOp K A)

/-- **The class of a tensor product is the product of the classes**: the defining property of the
multiplication of `BrauerGroup K`. -/
@[simp]
theorem mk_tensorProduct (A B : CSA.{u, u} K) : mk (CSA.tensorProduct A B) = mk A * mk B :=
  rfl

/-- **The class of `K` is the identity** of `BrauerGroup K`. -/
@[simp]
theorem mk_base : mk (CSA.base K) = 1 :=
  rfl

/-- **The class of the opposite algebra is the inverse class**: the defining property of the
inversion of `BrauerGroup K`. -/
@[simp]
theorem mk_op (A : CSA.{u, u} K) : mk (CSA.op A) = (mk A)⁻¹ :=
  rfl

/-! ### Identity classes -/

/-- **A class is the identity exactly when its algebras are Brauer trivial.**

This is the definition of `TauCeti.IsBrauerTrivial` read in the group: it is the statement that the
identity class is the class of the split algebras, and every recognition of an identity class below
goes through it. -/
@[simp]
theorem mk_eq_one_iff {A : CSA.{u, u} K} : mk A = 1 ↔ IsBrauerTrivial A := by
  rw [← mk_base]
  exact mk_eq_mk_iff

/-- **An algebra split by its own base field has identity Brauer class.**

The converse is not available here: it needs the uniqueness of the division algebra in a Brauer
class. See the module docstring. -/
theorem mk_eq_one_of_isSplittingField {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (h : Algebra.IsSplittingField K A K) :
    mk (CSA.of K A) = 1 :=
  mk_eq_one_iff.2 (isBrauerTrivial_of_isSplittingField K h)

/-- **The endomorphism algebra of a nonzero finite-dimensional vector space has identity Brauer
class.** Every full matrix algebra over `K` is such an `End_K V` up to isomorphism, and this is the
form in which the identity class gets used downstream: `A ⊗[K] Aᵐᵒᵖ` is an `End_K A`. -/
theorem mk_end (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V] :
    mk (CSA.of K (Module.End K V)) = 1 :=
  mk_eq_one_iff.2 (isBrauerTrivial_end K V)

/-! ### Classes of order two -/

/-- **An algebra Brauer equivalent to its own opposite has a self-inverse Brauer class.** -/
theorem inv_mk_eq_mk_of_isBrauerEquivalent_op {A : CSA.{u, u} K}
    (h : IsBrauerEquivalent A (CSA.op A)) : (mk A)⁻¹ = mk A :=
  (mk_op A).symm.trans (mk_eq_mk_iff.2 h.symm)

/-- **An algebra isomorphic to its own opposite has a self-inverse Brauer class.**

This is the Brauer-group reading of an isomorphism `A ≃ₐ[K] Aᵐᵒᵖ`: since the class of `Aᵐᵒᵖ` is the
inverse class, such an isomorphism says the class of `A` is its own inverse, equivalently that
`A ⊗[K] A` is Brauer trivial. -/
theorem inv_mk_eq_mk_of_algEquiv_op {A : CSA.{u, u} K} (e : (A : Type u) ≃ₐ[K] (A : Type u)ᵐᵒᵖ) :
    (mk A)⁻¹ = mk A :=
  inv_mk_eq_mk_of_isBrauerEquivalent_op (IsBrauerEquivalent.of_algEquiv K e)

/-- **An algebra Brauer equivalent to its own opposite has a class of order dividing `2`.**

The order is exactly `2` unless the class is the identity, that is, unless `A` is Brauer trivial
(`TauCeti.BrauerGroup.orderOf_mk_eq_two`); ruling that out is a separate matter, discussed in the
module docstring. -/
theorem orderOf_mk_dvd_two {A : CSA.{u, u} K} (h : IsBrauerEquivalent A (CSA.op A)) :
    orderOf (mk A) ∣ 2 :=
  orderOf_dvd_of_pow_eq_one <| by
    rw [sq]
    exact inv_eq_iff_mul_eq_one.1 (inv_mk_eq_mk_of_isBrauerEquivalent_op h)

/-- **An algebra isomorphic to its own opposite has a class of order dividing `2`.** -/
theorem orderOf_mk_dvd_two_of_algEquiv_op {A : CSA.{u, u} K}
    (e : (A : Type u) ≃ₐ[K] (A : Type u)ᵐᵒᵖ) : orderOf (mk A) ∣ 2 :=
  orderOf_mk_dvd_two (IsBrauerEquivalent.of_algEquiv K e)

/-- **A self-opposite Brauer class other than the identity has order exactly `2`.** This is the
sharp form of `TauCeti.BrauerGroup.orderOf_mk_dvd_two`. -/
theorem orderOf_mk_eq_two {A : CSA.{u, u} K} (h : IsBrauerEquivalent A (CSA.op A))
    (h1 : mk A ≠ 1) : orderOf (mk A) = 2 :=
  orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.1 (orderOf_mk_dvd_two h)) h1

/-- **An algebra isomorphic to its own opposite, but not split, has a class of order exactly
`2`.** -/
theorem orderOf_mk_eq_two_of_algEquiv_op {A : CSA.{u, u} K}
    (e : (A : Type u) ≃ₐ[K] (A : Type u)ᵐᵒᵖ) (h1 : mk A ≠ 1) : orderOf (mk A) = 2 :=
  orderOf_mk_eq_two (IsBrauerEquivalent.of_algEquiv K e) h1

end BrauerGroup

/-! ### Worked examples -/

section Examples

/-- A full matrix algebra over `K` has identity Brauer class: it is `Mₙ` of the class of `K`. -/
example (n : ℕ) [NeZero n] : BrauerGroup.mk (CSA.of K (Matrix (Fin n) (Fin n) K)) = 1 :=
  BrauerGroup.mk_eq_one_iff.2 (isBrauerTrivial_matrix K n)

/-- The Brauer class of `Aᵐᵒᵖ` is inverse to the class of `A`, which is the content of the Azumaya
isomorphism `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] M_{finrank K A}(K)` once the group structure is in place. -/
example (A : CSA.{u, u} K) : BrauerGroup.mk A * BrauerGroup.mk (CSA.op A) = 1 := by
  simp

end Examples

end TauCeti
