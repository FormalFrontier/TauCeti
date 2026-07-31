/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.GroupTheory.QuotientGroup.Basic

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

Each isomorphism comes with the lemmas reading it, and its inverse, on the basis of `k[G ⧸ H]`
indexed by the cosets.
-/

public section

namespace TauCeti

universe u v w w'

open CategoryTheory

section Congr

variable {G : Type v} [Monoid G]

section Semiring

variable (k : Type u) [Semiring k] {X : Type w} {Y : Type w'} [MulAction G X] [MulAction G Y]

/-- A `G`-equivariant equivalence of `G`-sets induces an equivalence of the permutation
representations on their free modules. -/
noncomputable def ofMulActionEquivCongr (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    (Representation.ofMulAction k G X).Equiv (Representation.ofMulAction k G Y) :=
  .mk (MonoidAlgebra.mapDomainLinearEquiv k k e) fun _ => by ext; simp [he]

@[simp]
theorem ofMulActionEquivCongr_apply_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (x : X) (r : k) :
    ofMulActionEquivCongr k e he (MonoidAlgebra.single x r) = MonoidAlgebra.single (e x) r := by
  simp [ofMulActionEquivCongr]

@[simp]
theorem ofMulActionEquivCongr_symm_apply_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (y : Y) (r : k) :
    (ofMulActionEquivCongr k e he).symm (MonoidAlgebra.single y r) =
      MonoidAlgebra.single (e.symm y) r := by
  simp [ofMulActionEquivCongr]

end Semiring

-- Objects of `Rep k G` carry an `AddCommGroup`, so `Rep.ofMulAction k G X` needs `k[X]` to be
-- one; Mathlib declares `Rep.ofMulAction` in its `ring` section for exactly this reason, and
-- everything below is stated in terms of it.  An isomorphism in `Rep k G` also compares two
-- objects of the same category, so here `X` and `Y` share a universe.
variable (k : Type u) [Ring k] {X Y : Type w} [MulAction G X] [MulAction G Y]

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

@[simp]
theorem ofMulActionIsoCongr_inv_hom_single (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (y : Y) (r : k) :
    (ofMulActionIsoCongr k e he).inv.hom (MonoidAlgebra.single y r) =
      MonoidAlgebra.single (e.symm y) r := by
  simp [ofMulActionIsoCongr, ofMulActionEquivCongr]

end Congr

section Quotient

variable (k : Type u) [Ring k] {G : Type v} [Group G]

/-- Equal subgroups have the same cosets, so they carry isomorphic permutation
representations. -/
noncomputable def quotientIsoCongr {H K : Subgroup G} (h : H = K) :
    Rep.ofMulAction k G (G ⧸ H) ≅ Rep.ofMulAction k G (G ⧸ K) :=
  ofMulActionIsoCongr k (Subgroup.quotientEquivOfEq h) fun _ q => by
    induction q using QuotientGroup.induction_on with
    | H x => rfl

@[simp]
theorem quotientIsoCongr_hom_hom_single {H K : Subgroup G} (h : H = K) (q : G ⧸ H) (r : k) :
    (quotientIsoCongr k h).hom.hom (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (Subgroup.quotientEquivOfEq h q) r :=
  ofMulActionIsoCongr_hom_hom_single k _ _ q r

@[simp]
theorem quotientIsoCongr_inv_hom_single {H K : Subgroup G} (h : H = K) (q : G ⧸ K) (r : k) :
    (quotientIsoCongr k h).inv.hom (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (Subgroup.quotientEquivOfEq h.symm q) r :=
  ofMulActionIsoCongr_inv_hom_single k _ _ q r

/-- The basis element indexed by the coset of a representative, in the forward direction. -/
@[simp]
theorem quotientIsoCongr_hom_hom_single_mk {H K : Subgroup G} (h : H = K) (x : G) (r : k) :
    (quotientIsoCongr k h).hom.hom (MonoidAlgebra.single (x : G ⧸ H) r) =
      MonoidAlgebra.single (x : G ⧸ K) r :=
  quotientIsoCongr_hom_hom_single k h _ r

/-- The basis element indexed by the coset of a representative, in the inverse direction. -/
@[simp]
theorem quotientIsoCongr_inv_hom_single_mk {H K : Subgroup G} (h : H = K) (x : G) (r : k) :
    (quotientIsoCongr k h).inv.hom (MonoidAlgebra.single (x : G ⧸ K) r) =
      MonoidAlgebra.single (x : G ⧸ H) r :=
  quotientIsoCongr_inv_hom_single k h _ r

/-- The permutation representation of `G` on the cosets of the trivial subgroup is the left
regular representation. -/
noncomputable def quotientBotIsoLeftRegular :
    Rep.ofMulAction k G (G ⧸ (⊥ : Subgroup G)) ≅ Rep.leftRegular k G :=
  ofMulActionIsoCongr k QuotientGroup.quotientBot.toEquiv quotientBot_equivariant

@[simp]
theorem quotientBotIsoLeftRegular_hom_hom_single (q : G ⧸ (⊥ : Subgroup G)) (r : k) :
    (quotientBotIsoLeftRegular k).hom.hom (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (QuotientGroup.quotientBot q) r :=
  ofMulActionIsoCongr_hom_hom_single k QuotientGroup.quotientBot.toEquiv
    quotientBot_equivariant q r

/-- The basis element indexed by the coset of a representative is sent to that
representative. -/
@[simp]
theorem quotientBotIsoLeftRegular_hom_hom_single_mk (x : G) (r : k) :
    (quotientBotIsoLeftRegular k).hom.hom
        (MonoidAlgebra.single (x : G ⧸ (⊥ : Subgroup G)) r) =
      MonoidAlgebra.single x r :=
  quotientBotIsoLeftRegular_hom_hom_single k _ r

@[simp]
theorem quotientBotIsoLeftRegular_inv_hom_single (x : G) (r : k) :
    (quotientBotIsoLeftRegular k).inv.hom (MonoidAlgebra.single x r) =
      MonoidAlgebra.single (x : G ⧸ (⊥ : Subgroup G)) r :=
  ofMulActionIsoCongr_inv_hom_single k QuotientGroup.quotientBot.toEquiv
    quotientBot_equivariant _ r

end Quotient

section QuotientTop

-- Mathlib's `Rep.ofMulActionSubsingletonIsoTrivial` compares `Rep.ofMulAction k G H` with
-- `Rep.trivial k G k`, so it needs the `G`-set `H` to live in the universe of `k`; for
-- `H = G ⧸ ⊤` that forces `G` into the universe of `k` as well.
variable (k : Type u) [Ring k] {G : Type u} [Group G]

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
  rw [quotientTopIsoTrivial, Rep.mkIso_hom_hom_apply,
    Representation.ofMulActionSubsingletonEquivTrivial_apply, Subsingleton.elim q 1]
  simp

@[simp]
theorem quotientTopIsoTrivial_inv_hom_apply (r : k) :
    (quotientTopIsoTrivial k).inv.hom r =
      MonoidAlgebra.single ((1 : G) : G ⧸ (⊤ : Subgroup G)) r := by
  haveI := QuotientGroup.subsingleton_quotient_top (G := G)
  rw [quotientTopIsoTrivial, Rep.mkIso_inv_hom_apply, ← Representation.Equiv.coe_toLinearMap,
    Representation.ofMulActionSubsingletonEquivTrivial_symm_apply, QuotientGroup.mk_one]

end QuotientTop

end TauCeti
