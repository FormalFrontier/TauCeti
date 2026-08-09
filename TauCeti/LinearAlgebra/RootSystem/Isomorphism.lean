/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.LinearAlgebra.RootSystem.Duality` is imported publicly: `TauCeti.HasCartanType` occurs
-- in every statement below, and the corollaries about the dual root system run on
-- `TauCeti.HasCartanType.flip`, `TauCeti.hasCartanType_dual_iff_of_rank_le_two` and
-- `TauCeti.DynkinType.dual_eq_self_of_isSimplyLaced`. It re-exports
-- `TauCeti.LinearAlgebra.RootSystem.DynkinType`, hence the enumeration and
-- `TauCeti.hasCartanType_iff`, and through it `Mathlib.LinearAlgebra.RootSystem.CartanMatrix`,
-- hence `RootPairing.Base.equivOfCartanMatrixEq`, which is the theorem every proof here consumes.
public import TauCeti.LinearAlgebra.RootSystem.Duality

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
`TauCeti.HasCartanType.exists_supportEquiv` is what supplies such a relabelling: two bases of type
`t` are each labelled by the nodes of `t`, and composing the two labellings identifies their
supports compatibly with the Cartan matrices. The rest of the file is what that isomorphism buys.

The first consequence is that the root index sets match, so the *number of roots* is an invariant
of the Cartan type, not of the presentation. The others concern duality. Passing to the dual root
system `RootPairing.flip` dualizes the Dynkin type (`TauCeti.hasCartanType_flip_iff`), so a root
system whose type is fixed by duality is isomorphic to its own dual — which covers the simply-laced
types `A`, `D`, `E` and also `F₄` and `G₂` — and a root system of type `Bₙ` is isomorphic to the
dual of one of type `Cₙ`. At rank at most two duality is invisible
(`TauCeti.hasCartanType_dual_iff_of_rank_le_two`), and there every root system is isomorphic to its
dual; the worked instance is `B 2 = C 2`, the low-rank coincidence that
`TauCeti.DynkinType.Valid` resolves by dropping the name `C 2`.

The duality statements carry torsion-freeness of the weight and coweight spaces, which is exactly
the hypothesis of Mathlib's `RootPairing.instFlipIsReduced`: reducedness of `P` transfers to
`P.flip` only there, and `RootPairing.Base.equivOfCartanMatrixEq` needs the target root system to
be reduced. Neither hypothesis is needed for the main theorem, which never flips, and both are
automatic over a field.

## Main results

* `TauCeti.HasCartanType.exists_supportEquiv`: two bases of the same Cartan type are related by a
  relabelling of their supports that matches their Cartan matrices.
* `TauCeti.nonempty_equiv_of_hasCartanType`: **two root systems carrying bases of the same Cartan
  type are isomorphic.**
* `TauCeti.nonempty_indexEquiv_of_hasCartanType` and `TauCeti.natCard_eq_of_hasCartanType`: their
  root index sets are in bijection, so the number of roots depends only on the Cartan type.
* `TauCeti.nonempty_equiv_flip_of_dual_eq_self`, with the specializations
  `TauCeti.nonempty_equiv_flip_of_isSimplyLaced` and `TauCeti.nonempty_equiv_flip_of_rank_le_two`:
  a root system of self-dual Cartan type is isomorphic to its dual.
* `TauCeti.nonempty_equiv_flip_of_hasCartanType_B_C`: a root system of type `Bₙ` is isomorphic to
  the dual of one of type `Cₙ`, and `TauCeti.nonempty_equiv_of_hasCartanType_B_two_C_two`: at rank
  two the flip is not needed, `B 2` and `C 2` being the same root system.

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

section Relabelling

variable [P.IsCrystallographic] [P₂.IsCrystallographic]

/-- **Two bases of the same Cartan type are related by a relabelling matching their Cartan
matrices.** Each of the two bases comes with a labelling of its support by the nodes of `t`, and
composing one with the inverse of the other identifies the supports; the two Cartan matrices then
agree because each agrees with the standard matrix of `t`.

This is the hypothesis of Mathlib's `RootPairing.Base.equivOfCartanMatrixEq`, and is stated
separately because it needs neither finiteness nor reducedness: it is pure bookkeeping about the
labellings, with the root-system content left to that theorem. -/
theorem HasCartanType.exists_supportEquiv {b : P.Base} {b₂ : P₂.Base} {t : DynkinType}
    (h : HasCartanType P b t) (h₂ : HasCartanType P₂ b₂ t) :
    ∃ e : b.support ≃ b₂.support, ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  obtain ⟨e₂, he₂⟩ := (hasCartanType_iff b₂ t).mp h₂
  exact ⟨e.trans e₂.symm, fun i j ↦ by
    simp only [Equiv.trans_apply, he₂, he, Equiv.apply_symm_apply]⟩

end Relabelling

section Isomorphism

variable [CharZero R] [IsDomain R] [Finite ι] [Finite ι₂]
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
  let ⟨e, he⟩ := h.exists_supportEquiv h₂
  ⟨_root_.RootPairing.Base.equivOfCartanMatrixEq b b₂ e he⟩

/-- **The root index sets of two root systems of the same Cartan type are in bijection.** An
isomorphism of root pairings carries a bijection of root indices (`RootPairing.Hom.indexEquiv`), so
this is read off `TauCeti.nonempty_equiv_of_hasCartanType`. -/
theorem nonempty_indexEquiv_of_hasCartanType (b : P.Base) (b₂ : P₂.Base) (t : DynkinType)
    (h : HasCartanType P b t) (h₂ : HasCartanType P₂ b₂ t) :
    Nonempty (ι ≃ ι₂) :=
  (nonempty_equiv_of_hasCartanType b b₂ t h h₂).elim fun e ↦ ⟨e.toHom.indexEquiv⟩

/-- **The number of roots depends only on the Cartan type.** Together with
`TauCeti.HasCartanType.card_support`, which does the same for the number of simple roots, this says
that the coarse numerical invariants of a root system are already determined by its diagram. -/
theorem natCard_eq_of_hasCartanType (b : P.Base) (b₂ : P₂.Base) (t : DynkinType)
    (h : HasCartanType P b t) (h₂ : HasCartanType P₂ b₂ t) :
    Nat.card ι = Nat.card ι₂ :=
  (nonempty_indexEquiv_of_hasCartanType b b₂ t h h₂).elim Nat.card_congr

/-- **Types `B 2` and `C 2` describe the same root system.** This is the low-rank coincidence that
`TauCeti.DynkinType.Valid` resolves by keeping only the name `B 2`, here as an isomorphism rather
than as the equality of matching predicates `TauCeti.hasCartanType_C_two_iff_B_two`. Unlike the
statements below it needs no `RootPairing.flip`, precisely because at rank two the two names match
the very same bases. -/
theorem nonempty_equiv_of_hasCartanType_B_two_C_two (b : P.Base) (b₂ : P₂.Base)
    (h : HasCartanType P b (.B 2)) (h₂ : HasCartanType P₂ b₂ (.C 2)) :
    Nonempty (P.Equiv P₂) :=
  nonempty_equiv_of_hasCartanType b b₂ (.B 2) h (hasCartanType_C_two_iff_B_two.mp h₂)

end Isomorphism

section Dual

variable [CharZero R] [IsDomain R] [Finite ι]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  [Module.IsTorsionFree R M] [Module.IsTorsionFree R N]

/-- **A root system whose Cartan type is fixed by duality is isomorphic to its dual.** Flipping
carries a base of type `t` to a base of type `t.dual` (`TauCeti.HasCartanType.flip`), so when
`t.dual = t` the two root systems `P` and `P.flip` carry bases of a common type. -/
theorem nonempty_equiv_flip_of_dual_eq_self (b : P.Base) {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.dual = t) :
    Nonempty (P.Equiv P.flip) :=
  nonempty_equiv_of_hasCartanType b b.flip t h (by rw [← ht]; exact h.flip)

/-- **A simply-laced root system is isomorphic to its dual.** The simply-laced types `A`, `D` and
`E` have no arrow for duality to reverse; `F₄` and `G₂` are self-dual too, and for them
`TauCeti.nonempty_equiv_flip_of_dual_eq_self` applies directly. -/
theorem nonempty_equiv_flip_of_isSimplyLaced (b : P.Base) {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.IsSimplyLaced) :
    Nonempty (P.Equiv P.flip) :=
  nonempty_equiv_flip_of_dual_eq_self b h (DynkinType.dual_eq_self_of_isSimplyLaced ht)

/-- **A root system of rank at most two is isomorphic to its dual.** Here the type itself may move
under duality — `B 2` becomes `C 2` — but at rank at most two the dual type matches the same bases
(`TauCeti.hasCartanType_dual_iff_of_rank_le_two`), so `P` and `P.flip` still share the type
`t.dual`. -/
theorem nonempty_equiv_flip_of_rank_le_two (b : P.Base) {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.rank ≤ 2) :
    Nonempty (P.Equiv P.flip) :=
  nonempty_equiv_of_hasCartanType b b.flip t.dual
    ((hasCartanType_dual_iff_of_rank_le_two ht).mpr h) h.flip

end Dual

/-- **A root system of type `Bₙ` is isomorphic to the dual of one of type `Cₙ`.** The oriented
matching of `TauCeti.HasCartanType` keeps the two types apart, and this says what does relate them:
not an isomorphism, but an isomorphism after flipping. At rank two the flip is unnecessary, by
`TauCeti.nonempty_equiv_of_hasCartanType_B_two_C_two`. -/
theorem nonempty_equiv_flip_of_hasCartanType_B_C [CharZero R] [IsDomain R] [Finite ι] [Finite ι₂]
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    [P₂.IsRootSystem] [P₂.IsCrystallographic] [P₂.IsReduced]
    [Module.IsTorsionFree R M₂] [Module.IsTorsionFree R N₂]
    (b : P.Base) (b₂ : P₂.Base) {n : ℕ}
    (h : HasCartanType P b (.B n)) (h₂ : HasCartanType P₂ b₂ (.C n)) :
    Nonempty (P.Equiv P₂.flip) :=
  nonempty_equiv_of_hasCartanType b b₂.flip (.B n) h (hasCartanType_flip_B_iff.mpr h₂)

end TauCeti
