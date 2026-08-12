/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.BrauerGroup.Basic` is imported publicly: the bundling `TauCeti.CSA.of` and the
-- base field `TauCeti.CSA.base` occur in the statements below, and the two moves that leave a
-- Brauer class unchanged, `TauCeti.IsBrauerEquivalent.of_algEquiv` and
-- `TauCeti.isBrauerEquivalent_matrix`, are what the triviality proofs run on. It re-exports
-- `Mathlib.Algebra.BrauerGroup.Defs` (hence `CSA`, `IsBrauerEquivalent` and `BrauerGroup`), the two
-- halves of the central simple structure on a full matrix algebra, which is what bundles `Mₙ(K)`
-- as a term of `CSA K`, and `Mathlib.Data.Matrix.Composition`, hence the matrix identity
-- `Mₚ(Mᵩ(R)) ≃ₐ Mₚ˟ᵩ(R)` used in a proof below; that is why none of those is imported again here.
public import TauCeti.Algebra.BrauerGroup.Basic
-- `TauCeti.Algebra.CentralSimple.End` is imported publicly: its simplicity instance
-- `TauCeti.IsSimpleRing.moduleEnd_of_field`, together with the centrality instance it re-exports
-- from `Mathlib.Algebra.Central.End`, is what bundles `End_K V` as a term of `CSA K` in the
-- statements below.
public import TauCeti.Algebra.CentralSimple.End
-- `TauCeti.Algebra.CentralSimple.Opposite` is imported publicly: `A ⊗[K] Aᵐᵒᵖ` occurs in a
-- statement below, and this module supplies the central simple structure making it a `CSA`, as
-- well as the isomorphism `TauCeti.Algebra.tensorOpAlgEquivMatrix` that splits it.
-- It also re-exports `TauCeti.LinearAlgebra.Matrix.ToLin`, and with it
-- `TauCeti.Algebra.endAlgEquivMatrix`.
public import TauCeti.Algebra.CentralSimple.Opposite
-- `TauCeti.Algebra.IsSplittingField` occurs in the statements below.
public import TauCeti.Algebra.CentralSimple.Splitting
-- Non-public: the prime field of the worked example is used only inside a proof, so downstream
-- importers do not pay for it.
import Mathlib.Algebra.Field.ZMod

/-!
# Brauer triviality

Two finite-dimensional central simple `K`-algebras are **Brauer equivalent** when they become
isomorphic after passing to matrix algebras over them (Mathlib's `IsBrauerEquivalent`), and
`BrauerGroup K` is the quotient of `CSA K` by that relation. Mathlib stops there: the quotient
carries no group structure yet, and `TauCeti/Algebra/BrauerGroup/Basic.lean` supplies the
constructors and the two moves that leave a Brauer class unchanged. This file builds the part of
the theory the identity element of that group will rest on -- which algebras are **Brauer
trivial**, that is, equivalent to `K` itself -- and reads off the first two computations of a
Brauer group.

The engine is a single observation. An algebra **split by `K`**, in the sense of
`TauCeti.Algebra.IsSplittingField`, is a matrix algebra `Mₚ(K)`, and any two matrix algebras over
`K` become isomorphic after one more round of matrices: `Mᵩ(Mₚ(K))` and `Mₚ(Mᵩ(K))` are both the
matrix algebra over `K` indexed by a product of `Fin p` and `Fin q`, in the two orders, and
transposing the two factors matches them up. So the algebras split by `K` form a *single* Brauer
class, and each of the three named Brauer-trivial algebras is trivial because it is already known
to be a matrix algebra over `K`: a full matrix algebra `Mₙ(K)` by definition, the endomorphism
algebra `End_K V` of a nonzero finite-dimensional vector space by a choice of basis
(`TauCeti.Algebra.endAlgEquivMatrix`), and `A ⊗[K] Aᵐᵒᵖ` for a finite-dimensional central simple
`A` by the Azumaya isomorphism (`TauCeti.Algebra.tensorOpAlgEquivMatrix`).

The last of these is why the Brauer group will have inverses: it says the class of `Aᵐᵒᵖ` is
inverse to the class of `A`, once the multiplication induced by `⊗[K]` is known to descend to
classes.

## Main definitions

* `TauCeti.IsBrauerTrivial`: Brauer equivalence to the base field.

## Main results

* `TauCeti.isBrauerEquivalent_of_isSplittingField`: **two algebras split by `K` are Brauer
  equivalent**, with `TauCeti.isBrauerTrivial_of_isSplittingField` the form having the base field
  on one side.
* `TauCeti.isBrauerTrivial_matrix`, `TauCeti.isBrauerTrivial_end` and
  `TauCeti.isBrauerTrivial_tensorOp`: the three Brauer-trivial algebras named above.
* `TauCeti.subsingleton_brauerGroup_of_isAlgClosed` and
  `TauCeti.subsingleton_brauerGroup_of_finite`: **the Brauer group of an algebraically closed
  field, and of a finite field, is trivial.**

## Implementation notes

`TauCeti.IsBrauerTrivial` compares an algebra with `TauCeti.CSA.base K`, so it is stated for a
`CSA.{u, u} K`, an algebra in the universe of its own base field. That is not a restriction on the
mathematics -- a finite-dimensional `K`-algebra has a model in `Type u` -- but Mathlib's
`IsBrauerEquivalent` relates two algebras in one universe, and `K` lives in `Type u`. The
statements that do not mention `K` itself as an algebra, including the two Brauer-group
computations, stay at the full generality of `BrauerGroup.{u, v}`.

The two splitting facts `TauCeti.Algebra.isSplittingField_end` and
`TauCeti.Algebra.isSplittingField_tensorOp` are proved here rather than with the rest of the
splitting API, because they consume the simplicity of an endomorphism algebra and the Azumaya
isomorphism, which sit above `TauCeti/Algebra/CentralSimple/Splitting.lean` in the import order.

The converse of `TauCeti.isBrauerTrivial_of_isSplittingField` -- that a Brauer-trivial algebra is
split -- is **not** proved here, and is not a formal consequence of these lemmas: it needs the
uniqueness of the Wedderburn data, which sits above this file in the import order. It is
`TauCeti.Algebra.isSplittingField_self_of_isBrauerTrivial`, in
`TauCeti/Algebra/BrauerGroup/Splitting.lean`. Nothing below uses it, and in particular the two
Brauer-group computations go through the splitting side only.

## References

This implements the Brauer-triviality prerequisites of the first bullet of Layer 6 ("the API that
the identity and inverse rest on: finite-dimensional `Module.End K V` is Brauer-equivalent to `K`;
`Matrix n n K` is Brauer-trivial") together with the "Finite base fields" bullet ("`BrauerGroup` of
a finite field is trivial") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.4, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12.
-/

public section

namespace TauCeti

open scoped TensorProduct

universe u v

variable (K : Type u) [Field K]

/-- A finite-dimensional central simple `K`-algebra is **Brauer trivial** when it is Brauer
equivalent to the base field, that is, when its Brauer class is the one that will be the identity
of `BrauerGroup K`.

Every algebra split by `K` is Brauer trivial (`TauCeti.isBrauerTrivial_of_isSplittingField`); the
converse needs the uniqueness of the Wedderburn data and is
`TauCeti.Algebra.isSplittingField_self_of_isBrauerTrivial`, proved in
`TauCeti/Algebra/BrauerGroup/Splitting.lean`. -/
abbrev IsBrauerTrivial {K : Type u} [Field K] (A : CSA.{u, u} K) : Prop :=
  IsBrauerEquivalent A (CSA.base K)

/-! ### The algebras split by the base field form one Brauer class -/

/-- The size of a matrix presentation of a nontrivial algebra is nonzero, because a `0 × 0` matrix
algebra is the zero ring. -/
theorem ne_zero_of_algEquiv_matrix {A : Type v} [Ring A] [Algebra K A] [Nontrivial A] {p : ℕ}
    (e : A ≃ₐ[K] Matrix (Fin p) (Fin p) K) : p ≠ 0 := by
  rintro rfl
  exact not_subsingleton A e.toEquiv.subsingleton

/-- **Two central simple algebras split by their own base field are Brauer equivalent.**

Writing `A ≃ₐ Mₚ(K)` and `B ≃ₐ Mᵩ(K)`, both `Mᵩ(A)` and `Mₚ(B)` are the matrix algebra over `K`
indexed by a product of `Fin p` and `Fin q`, in the two orders, and transposing the two factors
matches them up. -/
theorem isBrauerEquivalent_of_isSplittingField {A B : CSA.{u, v} K}
    (hA : Algebra.IsSplittingField K A K) (hB : Algebra.IsSplittingField K B K) :
    IsBrauerEquivalent A B := by
  obtain ⟨p, ⟨eA⟩⟩ := (Algebra.isSplittingField_self_iff K A).1 hA
  obtain ⟨q, ⟨eB⟩⟩ := (Algebra.isSplittingField_self_iff K B).1 hB
  refine ⟨q, p, ne_zero_of_algEquiv_matrix K eB, ne_zero_of_algEquiv_matrix K eA, ⟨?_⟩⟩
  exact eA.mapMatrix.trans <| (Matrix.compAlgEquiv (Fin q) (Fin p) K K).trans <|
    (Matrix.reindexAlgEquiv K K (Equiv.prodComm (Fin q) (Fin p))).trans <|
      (Matrix.compAlgEquiv (Fin p) (Fin q) K K).symm.trans eB.symm.mapMatrix

/-! ### The Brauer-trivial algebras -/

/-- **A full matrix algebra over `K` is Brauer trivial.** It is `Mₙ` of the base field, so this is
the matrix move `TauCeti.isBrauerEquivalent_matrix` applied to the class of `K` itself. -/
theorem isBrauerTrivial_matrix (n : ℕ) [NeZero n] :
    IsBrauerTrivial (CSA.of K (Matrix (Fin n) (Fin n) K)) :=
  isBrauerEquivalent_matrix K (CSA.base K) n

/-- **An algebra split by its own base field is Brauer trivial**: it is isomorphic to a full matrix
algebra over `K`, so the two class-preserving moves compose to a Brauer equivalence with `K`.

Over an algebra in the universe of `K` this is the statement wanted downstream; the version for two
algebras in an arbitrary universe, which cannot pass through `TauCeti.CSA.base K` because `K` lives
in `Type u`, is `TauCeti.isBrauerEquivalent_of_isSplittingField`. -/
theorem isBrauerTrivial_of_isSplittingField {A : Type u} [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (hA : Algebra.IsSplittingField K A K) : IsBrauerTrivial (CSA.of K A) := by
  obtain ⟨p, ⟨e⟩⟩ := (Algebra.isSplittingField_self_iff K A).1 hA
  have : NeZero p := ⟨ne_zero_of_algEquiv_matrix K e⟩
  exact (IsBrauerEquivalent.of_algEquiv K (A := CSA.of K A)
    (B := CSA.of K (Matrix (Fin p) (Fin p) K)) e).trans (isBrauerTrivial_matrix K p)

section End

variable (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **`End_K V` is split by `K`**: a choice of basis of `V` presents it as the matrix algebra of
size `Module.finrank K V`. -/
theorem Algebra.isSplittingField_end : Algebra.IsSplittingField K (Module.End K V) K :=
  (Algebra.isSplittingField_self_iff K _).2 ⟨_, ⟨Algebra.endAlgEquivMatrix K V rfl⟩⟩

variable [Nontrivial V]

/-- **The endomorphism algebra of a nonzero finite-dimensional vector space is Brauer trivial.**

This is the form in which triviality gets used downstream: the identity Brauer class is not only
the class of the abstract matrix algebras but the class of every `End_K V`, and `End_K A` is what
`A ⊗[K] Aᵐᵒᵖ` is isomorphic to. -/
theorem isBrauerTrivial_end : IsBrauerTrivial (CSA.of K (Module.End K V)) :=
  isBrauerTrivial_of_isSplittingField K (Algebra.isSplittingField_end K V)

end End

section Opposite

variable (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **`A ⊗[K] Aᵐᵒᵖ` is split by `K`**: it is the matrix algebra of size `Module.finrank K A`, by
the Azumaya isomorphism `TauCeti.Algebra.tensorOpAlgEquivMatrix`. -/
theorem Algebra.isSplittingField_tensorOp : Algebra.IsSplittingField K (A ⊗[K] Aᵐᵒᵖ) K := by
  have := IsSimpleRing.isAzumaya K A
  exact (Algebra.isSplittingField_self_iff K _).2
    ⟨_, ⟨Algebra.tensorOpAlgEquivMatrix K A rfl⟩⟩

/-- **`A ⊗[K] Aᵐᵒᵖ` is Brauer trivial.**

This is what will make the class of `Aᵐᵒᵖ` inverse to the class of `A`: once the tensor product is
known to descend to a multiplication of Brauer classes, this says the product of those two classes
is the identity. -/
theorem isBrauerTrivial_tensorOp : IsBrauerTrivial (CSA.of K (A ⊗[K] Aᵐᵒᵖ)) :=
  isBrauerTrivial_of_isSplittingField K (Algebra.isSplittingField_tensorOp K A)

end Opposite

/-! ### Fields with trivial Brauer group -/

/-- **The Brauer group of an algebraically closed field is trivial.** Every finite-dimensional
central simple algebra over an algebraically closed field is a matrix algebra over it
(`TauCeti.Algebra.isSplittingField_of_isAlgClosed`, with the extension taken to be the base field
itself), so there is only one Brauer class. -/
theorem subsingleton_brauerGroup_of_isAlgClosed [IsAlgClosed K] :
    Subsingleton (BrauerGroup.{u, v} K) :=
  ⟨fun x y ↦ Quotient.inductionOn₂ x y fun A B ↦ Quotient.sound <|
    isBrauerEquivalent_of_isSplittingField K (Algebra.isSplittingField_of_isAlgClosed K A K)
      (Algebra.isSplittingField_of_isAlgClosed K B K)⟩

/-- **The Brauer group of a finite field is trivial.** A finite division ring is a field (little
Wedderburn), so the Wedderburn presentation of a central simple algebra over a finite field is
already a matrix algebra over that field (`TauCeti.Algebra.isSplittingField_self_of_finite`); again
there is only one Brauer class. -/
theorem subsingleton_brauerGroup_of_finite [Finite K] : Subsingleton (BrauerGroup.{u, v} K) :=
  ⟨fun x y ↦ Quotient.inductionOn₂ x y fun A B ↦ Quotient.sound <|
    isBrauerEquivalent_of_isSplittingField K (Algebra.isSplittingField_self_of_finite K A)
      (Algebra.isSplittingField_self_of_finite K B)⟩

/-! ### Worked example -/

section Examples

/-- The Brauer group of a prime field is trivial: over `ZMod p` there is no central division
algebra other than `ZMod p` itself. -/
example (p : ℕ) [Fact p.Prime] : Subsingleton (BrauerGroup (ZMod p)) :=
  subsingleton_brauerGroup_of_finite (ZMod p)

end Examples

end TauCeti
