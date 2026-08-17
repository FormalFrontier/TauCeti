/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.LinearAlgebra.RootSystem.DynkinType` is imported publicly: `TauCeti.HasCartanType`
-- occurs in the statement below, and `TauCeti.HasCartanType.exists_supportEquiv_cartanMatrix_eq`
-- supplies the relabelling the proof feeds to Mathlib's `RootPairing.Base.equivOfCartanMatrixEq`.
-- It re-exports `Mathlib.LinearAlgebra.RootSystem.CartanMatrix`, hence that theorem.
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# Root systems of the same Dynkin type are isomorphic

The Cartan-Killing classification has two halves. One is combinatorial: the Cartan matrix of a base
of an irreducible reduced crystallographic finite root system is, after relabelling the nodes, one
of the standard matrices `TauCeti.DynkinType.cartanMatrix`. The other is the rigidity statement
that the type is a complete invariant, and this file supplies it: two root systems carrying bases
of the same Dynkin type are isomorphic as root pairings.

Nothing here re-proves rigidity. Mathlib's `RootPairing.Base.equivOfCartanMatrixEq` already builds
an isomorphism from a relabelling matching the two Cartan matrices, and
`TauCeti.HasCartanType.exists_supportEquiv_cartanMatrix_eq` is what supplies such a relabelling: two
bases of type `t` are each labelled by the nodes of `t`, and composing the two labellings identifies
their supports compatibly with the Cartan matrices.

## Main results

* `TauCeti.nonempty_equiv_of_hasCartanType`: **two root systems carrying bases of the same Cartan
  type are isomorphic.**

## References

This file proves `nonempty_equiv_of_hasCartanType`, the final isomorphism step of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signature in
`TauCetiRoadmap/RepresentationTheory/RootSystems/Suggested.lean`. See Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4-6*, chapter VI, §4, and Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §11.1, for the isomorphism theorem in the classical language.
-/

namespace TauCeti

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
  [CharZero R] [IsDomain R] [Finite ι] [Finite ι₂]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  [P₂.IsRootSystem] [P₂.IsCrystallographic] [P₂.IsReduced]

/-- **Two root systems carrying bases of the same Cartan type are isomorphic.** This is the
rigidity half of the Cartan-Killing classification: the Dynkin type is not merely an invariant of a
finite reduced crystallographic root system, it is a complete one.

Only the existence of an isomorphism is asserted. The isomorphism produced depends on the two
labellings of the supports by the nodes of `t`, which `TauCeti.HasCartanType` quantifies
existentially, so there is no canonical choice to name; a caller that needs one destructures the two
`HasCartanType` witnesses and applies `RootPairing.Base.equivOfCartanMatrixEq` itself. -/
theorem nonempty_equiv_of_hasCartanType (b : P.Base) (b₂ : P₂.Base) (t : DynkinType)
    (h : HasCartanType P b t) (h₂ : HasCartanType P₂ b₂ t) :
    Nonempty (P.Equiv P₂) :=
  let ⟨e, he⟩ := h.exists_supportEquiv_cartanMatrix_eq h₂
  ⟨_root_.RootPairing.Base.equivOfCartanMatrixEq b b₂ e he⟩

end TauCeti
