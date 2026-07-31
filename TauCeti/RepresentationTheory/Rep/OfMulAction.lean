/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Permutation representations on the cosets of a subgroup

For a group `G` and a subgroup `H`, the permutation representation `k[G ⧸ H]` interpolates
between the two extremes `H = ⊤` and `H = ⊥`.  This file identifies those extremes: the cosets
of the whole group carry the trivial representation, and the cosets of the trivial subgroup
carry the left regular representation.

Both identifications go through `ofMulActionIsoCongr`, which turns a `G`-equivariant equivalence
of `G`-sets into an isomorphism of the permutation representations they carry.

## Main definitions

* `TauCeti.ofMulActionIsoCongr`: an equivariant equivalence of `G`-sets induces an isomorphism
  of permutation representations.
* `TauCeti.quotientIsoCongr`: equal subgroups give isomorphic permutation representations.
* `TauCeti.quotientTopIsoTrivial`: `k[G ⧸ ⊤] ≅ k` with the trivial action.
* `TauCeti.quotientBotIsoLeftRegular`: `k[G ⧸ ⊥] ≅ k[G]` with the left regular action.

## Main statements

* `TauCeti.quotientBot_smul_eq_self_iff`: a group element fixes a coset of the trivial subgroup
  only when it is the identity.  This is what makes the character of the left regular
  representation vanish away from the identity.
-/

public section

namespace TauCeti

universe u v

section Congr

variable (k : Type u) [Ring k] {G : Type v} [Monoid G] {X Y : Type u} [MulAction G X]
  [MulAction G Y]

/-- A `G`-equivariant equivalence of `G`-sets induces an equivalence of the permutation
representations on their free modules. -/
noncomputable def ofMulActionEquivCongr (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    (Representation.ofMulAction k G X).Equiv (Representation.ofMulAction k G Y) :=
  .mk (MonoidAlgebra.mapDomainLinearEquiv k k e) fun _ => by ext; simp [he]

/-- A `G`-equivariant equivalence of `G`-sets induces an isomorphism of the permutation
representations they carry. -/
noncomputable def ofMulActionIsoCongr (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Rep.ofMulAction k G X ≅ Rep.ofMulAction k G Y :=
  Rep.mkIso (ofMulActionEquivCongr k e he)

@[simp]
theorem ofMulActionIsoCongr_hom_hom_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x : X) (r : k) :
    (ofMulActionIsoCongr k e he).hom.hom (MonoidAlgebra.single x r) =
      MonoidAlgebra.single (e x) r := by
  simp [ofMulActionIsoCongr, ofMulActionEquivCongr]

end Congr

section Quotient

variable (k : Type u) [Ring k] {G : Type u} [Group G]

/-- Equal subgroups have the same cosets, so they carry isomorphic permutation
representations. -/
noncomputable def quotientIsoCongr {H K : Subgroup G} (h : H = K) :
    Rep.ofMulAction k G (G ⧸ H) ≅ Rep.ofMulAction k G (G ⧸ K) := by
  subst h
  exact CategoryTheory.Iso.refl _

/-- The permutation representation of `G` on the cosets of the whole group is the trivial
representation: there is only one coset. -/
noncomputable def quotientTopIsoTrivial :
    Rep.ofMulAction k G (G ⧸ (⊤ : Subgroup G)) ≅ Rep.trivial k G k :=
  haveI := QuotientGroup.subsingleton_quotient_top (G := G)
  Rep.ofMulActionSubsingletonIsoTrivial k G (G ⧸ (⊤ : Subgroup G))

@[simp]
theorem quotientTopIsoTrivial_hom_hom_single (q : G ⧸ (⊤ : Subgroup G)) (r : k) :
    (quotientTopIsoTrivial k).hom.hom (MonoidAlgebra.single q r) = r := by
  haveI := QuotientGroup.subsingleton_quotient_top (G := G)
  simp [quotientTopIsoTrivial, Representation.ofMulActionSubsingletonEquivTrivial,
    MonoidAlgebra.uniqueLinearEquiv, Subsingleton.elim q 1]

/-- Left translation on the cosets of the trivial subgroup is left translation in the group. -/
theorem quotientBot_smul (g x : G) :
    QuotientGroup.quotientBot (g • (x : G ⧸ (⊥ : Subgroup G))) =
      g * QuotientGroup.quotientBot (x : G ⧸ (⊥ : Subgroup G)) :=
  rfl

/-- Identifying the cosets of the trivial subgroup with the group is equivariant for left
translation. -/
theorem quotientBot_equivariant (g : G) (q : G ⧸ (⊥ : Subgroup G)) :
    QuotientGroup.quotientBot.toEquiv (g • q) =
      g • QuotientGroup.quotientBot.toEquiv q := by
  induction q using QuotientGroup.induction_on with
  | H x => exact quotientBot_smul g x

/-- The permutation representation of `G` on the cosets of the trivial subgroup is the left
regular representation. -/
noncomputable def quotientBotIsoLeftRegular :
    Rep.ofMulAction k G (G ⧸ (⊥ : Subgroup G)) ≅ Rep.leftRegular k G :=
  ofMulActionIsoCongr k QuotientGroup.quotientBot.toEquiv quotientBot_equivariant

@[simp]
theorem quotientBotIsoLeftRegular_hom_hom_single (x : G) (r : k) :
    (quotientBotIsoLeftRegular k).hom.hom
        (MonoidAlgebra.single (x : G ⧸ (⊥ : Subgroup G)) r) =
      MonoidAlgebra.single x r :=
  ofMulActionIsoCongr_hom_hom_single k QuotientGroup.quotientBot.toEquiv
    quotientBot_equivariant _ r

/-- A group element fixes a coset of the trivial subgroup exactly when it is the identity. -/
theorem quotientBot_smul_eq_self_iff (g : G) (q : G ⧸ (⊥ : Subgroup G)) :
    g • q = q ↔ g = 1 := by
  constructor
  · intro h
    have := congrArg QuotientGroup.quotientBot h
    induction q using QuotientGroup.induction_on with
    | H x => simpa [quotientBot_smul] using this
  · rintro rfl
    exact one_smul _ _

end Quotient

end TauCeti
