/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Skeletal
public import TauCeti.RepresentationTheory.Induction.Conjugate

/-!
# The inertia group of a representation of a normal subgroup

Let `N` be a normal subgroup of `G`.  Conjugation makes `G` act on `FDRep k N`
(`TauCeti.conjNormalFDRepMulAction`), and the *inertia group* of `A : FDRep k N` is the stabilizer
of the isomorphism class of `A`,

`inertia A = {g : G | {}^g A ≅ A}`.

This is not `MulAction.stabilizer G A`, which asks for `{}^g A = A` on the nose; the two are
compared in `TauCeti.stabilizer_le_inertia`.  Instead, isomorphism classes of objects of a
category are Mathlib's `CategoryTheory.Skeleton`, and conjugation descends to them because it is a
*functor*, via `CategoryTheory.Functor.mapSkeleton`; that descent is the `MulAction` instance
`TauCeti.conjNormalFDRepSkeletonMulAction`, and `inertia A` is literally
`MulAction.stabilizer G (toSkeleton A)`.  Everything else — that the inertia group is a subgroup,
that it only depends on the isomorphism class, and that conjugating the representation conjugates
it — is then Mathlib's generic stabilizer API.

The conjugation file `TauCeti.RepresentationTheory.Induction.Conjugate` deliberately stops at the
action of `G` on `FDRep k N` itself and leaves the induced action on isomorphism classes to a later
file; this is that file.

The inertia group contains `N` (`TauCeti.le_inertia`), because conjugating by an element `n` of `N`
itself is an inner twist: `A.ρ n` intertwines `{}^n A` with `A`
(`TauCeti.conjNormalFDRepSelfIso`).  Together with the normality of `N` inside `inertia A`, which
Mathlib's `Subgroup.normal_subgroupOf` instance supplies for any subgroup of `G`, this is what makes
the quotient `inertia A / N` — where the Clifford-theory obstruction lives — available.

Nothing here needs `A` to be irreducible: the inertia group is defined for every
finite-dimensional representation of `N`, and irreducibility only enters later, when Clifford's
theorem identifies the constituents of a restriction with a single `G`-orbit.

## Main definitions

* `TauCeti.conjNormalFDRepSkeletonSMul`, `TauCeti.conjNormalFDRepSkeletonMulAction`: conjugation
  acting on isomorphism classes of finite-dimensional representations of `N`.
* `TauCeti.inertia`: the inertia group of a representation of a normal subgroup.

## Main statements

* `TauCeti.mem_inertia_iff`: membership in the inertia group is the existence of an isomorphism
  `{}^g A ≅ A`.
* `TauCeti.le_inertia`: the inertia group contains `N`.
* `TauCeti.inertia_congr`: isomorphic representations have the same inertia group, so the inertia
  group is an invariant of the isomorphism class.
* `TauCeti.inertia_conjNormalFDRep`: conjugating the representation conjugates its inertia group.
* `TauCeti.char_conj_eq_of_mem_inertia`: the character of `A` is invariant under conjugation
  by an element of the inertia group.

## References

This file builds the inertia group of Layer 5 (Clifford theory over a normal subgroup) of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks for
"the **inertia (stabilizer) group** `inertia V ≤ G` of an irreducible `V : FDRep k N` is
`{g : G | {}^g V ≅ V}`, a subgroup containing `N`", and pins `inertia`, `mem_inertia_iff` and
`le_inertia` in the accompanying `Suggested.lean`.
-/

public section

open CategoryTheory
open scoped Pointwise

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [hN : N.Normal]

section Ring

variable [Ring k]

/-- Conjugation acts on the isomorphism classes of finite-dimensional representations of `N`: the
descent of the conjugation functor to the skeleton is Mathlib's
`CategoryTheory.Functor.mapSkeleton`. -/
noncomputable instance conjNormalFDRepSkeletonSMul : SMul G (Skeleton (FDRep k N)) where
  smul g := (conjNormalFDRepFunctor g).mapSkeleton.obj

/-- The action on isomorphism classes is induced by the action on representations. -/
@[simp]
theorem smul_toSkeleton (g : G) (A : FDRep k N) :
    g • toSkeleton A = toSkeleton (conjNormalFDRep g A) :=
  (conjNormalFDRepFunctor g).mapSkeleton_obj_toSkeleton A

/-- Conjugation on isomorphism classes is an action, because conjugation is one
(`conjNormalFDRep_one`, `conjNormalFDRep_mul`); every class is `toSkeleton` of a representative, so
`smul_toSkeleton` reduces both laws to their counterparts on representations.

This is the action whose stabilizers are the inertia groups. -/
noncomputable instance conjNormalFDRepSkeletonMulAction : MulAction G (Skeleton (FDRep k N)) where
  one_smul X := by
    obtain ⟨A, rfl⟩ : ∃ A, toSkeleton A = X := ⟨_, toSkeleton_fromSkeleton_obj X⟩
    rw [smul_toSkeleton, conjNormalFDRep_one]
  mul_smul s t X := by
    obtain ⟨A, rfl⟩ : ∃ A, toSkeleton A = X := ⟨_, toSkeleton_fromSkeleton_obj X⟩
    rw [smul_toSkeleton, smul_toSkeleton, smul_toSkeleton, conjNormalFDRep_mul]

/-- The **inertia group** of `A : FDRep k N`, for `N` a normal subgroup of `G`: the elements of
`G` whose conjugate representation `{}^g A` is isomorphic to `A`, i.e. the stabilizer of the
isomorphism class of `A` under `conjNormalFDRepSkeletonMulAction`.

See `TauCeti.mem_inertia_iff` for the description as `{g | {}^g A ≅ A}`, and
`TauCeti.stabilizer_le_inertia` for the comparison with the stabilizer of `A` itself. -/
noncomputable def inertia (A : FDRep k N) : Subgroup G :=
  MulAction.stabilizer G (toSkeleton A)

/-- An element lies in the inertia group exactly when it conjugates the representation to an
isomorphic one. -/
@[simp]
theorem mem_inertia_iff {A : FDRep k N} {g : G} :
    g ∈ inertia A ↔ Nonempty (conjNormalFDRep g A ≅ A) := by
  rw [inertia, MulAction.mem_stabilizer_iff, smul_toSkeleton, toSkeleton_eq_toSkeleton_iff]

/-- The inertia group of `A` contains the elements fixing `A` on the nose. -/
theorem stabilizer_le_inertia (A : FDRep k N) :
    MulAction.stabilizer G A ≤ inertia A :=
  fun _ hg => mem_inertia_iff.2 ⟨eqToIso hg⟩

/-- **The inertia group contains the normal subgroup**: conjugating by an element of `N` is an
inner twist, so it fixes the isomorphism class. -/
theorem le_inertia (A : FDRep k N) : N ≤ inertia A :=
  fun n hn => mem_inertia_iff.2 ⟨conjNormalFDRepSelfIso A ⟨n, hn⟩⟩

/-- Isomorphic representations have the same inertia group: the inertia group depends only on the
isomorphism class of `A`, which — once `A` is irreducible — is a point of `Irr(N)`. -/
theorem inertia_congr {A B : FDRep k N} (e : A ≅ B) : inertia A = inertia B :=
  congrArg (MulAction.stabilizer G) (congr_toSkeleton_of_iso e)

/-- **Conjugating the representation conjugates the inertia group**: `I({}^g A) = g I(A) g⁻¹`.

Equivalently the inertia groups along a `G`-orbit in `Irr(N)` are all conjugate, so they share an
index; that index is the number of constituents in Clifford's theorem. -/
theorem inertia_conjNormalFDRep (g : G) (A : FDRep k N) :
    inertia (conjNormalFDRep g A) = MulAut.conj g • inertia A := by
  rw [inertia, ← smul_toSkeleton, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.pointwise_smul_def]
  rfl

end Ring

section Field

variable [Field k]

/-- The character of `A` is invariant under conjugation by an element of its inertia group:
`χ(g⁻¹xg) = χ(x)` for `g ∈ inertia A` and `x : N`.

This is the character shadow of `mem_inertia_iff`, and the form in which Clifford's theorem uses
the inertia group. -/
theorem char_conj_eq_of_mem_inertia {A : FDRep k N} {g : G} (hg : g ∈ inertia A) (x : N) :
    A.character ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ = A.character x := by
  obtain ⟨e⟩ := mem_inertia_iff.1 hg
  rw [← char_conjNormalFDRep_mk, FDRep.char_iso e]

end Field

end TauCeti
