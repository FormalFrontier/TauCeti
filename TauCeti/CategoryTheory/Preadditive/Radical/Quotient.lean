/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
-- Finite-dimensionality of the quotient, for the local finiteness of the Auslander-Reiten quiver.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- The dimension bound on the quotient, for the local finiteness of that quiver.
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The space of irreducible morphisms of a linear category

Between two objects `X` and `Y` of a `k`-linear category with local endomorphism rings, the
morphisms lying in the radical but not in its square are exactly the irreducible ones
(`TauCeti.isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq`).  The
quotient `rad(X, Y) / rad²(X, Y)` is therefore the `k`-module whose nonzero classes are the
irreducible morphisms `X ⟶ Y`, and it is the object an arrow of the Auslander-Reiten quiver is a
basis vector of: the number of arrows `X → Y` of that quiver is its dimension.  This file builds
that quotient, `TauCeti.irreducibleMorphismSpace k X Y`, on top of the two submodules supplied by
`TauCeti.CategoryTheory.Preadditive.Radical.Basic`.

The three things the Auslander-Reiten quiver needs of it are here.  First, the **detection**
statement: a class is nonzero exactly when the morphism representing it is irreducible, so the
space is nontrivial exactly when an irreducible morphism `X ⟶ Y` exists — that is what makes "there
is an arrow `X → Y`" mean "there is an irreducible morphism `X ⟶ Y`".  Second, **isomorphism
invariance**: conjugating by isomorphisms `X ≅ X'` and `Y ≅ Y'` induces a `k`-linear equivalence
`Irr(X, Y) ≃ₗ[k] Irr(X', Y')`, functorially, which is what lets the arrows be indexed by
*isomorphism classes* of indecomposables.  Third, **finite-dimensionality** over a division ring
whenever the ambient morphism space is finite-dimensional, which is what makes the quiver locally
finite.

The detection statement is the only one that constrains the objects: it needs the two endomorphism
rings to be local (the indecomposables of a Krull-Schmidt category) and the category to have binary
biproducts, exactly as its input in `Radical.Basic` does.  The construction of the quotient, its
linear structure and its invariance under isomorphism need none of that, so they are stated for an
arbitrary `k`-linear category over a ring `k`.

What is *not* built here is the bimodule structure of `Irr(X, Y)` over the residue division rings
`End X / rad(End X)` and `End Y / rad(End Y)`, which is what refines the dimension count over a base
field that is not algebraically closed; over an algebraically closed field those residue rings are
`k` itself and the `k`-module structure below is the whole story.

## Main definitions

* `TauCeti.jacobsonRadicalSqSubmoduleIn`: the square of the radical, viewed as a submodule of the
  radical rather than of the whole morphism space; the submodule that is quotiented out.
* `TauCeti.irreducibleMorphismSpace k X Y`: the space `rad(X, Y) / rad²(X, Y)` of irreducible
  morphisms, a `k`-module.
* `TauCeti.irreducibleMorphismMk`: the class of a radical morphism, as a `k`-linear map.
* `TauCeti.irreducibleMorphismSpaceCongr`: the `k`-linear equivalence induced by a pair of
  isomorphisms of the source and the target.

## Main results

* `TauCeti.irreducibleMorphismMk_eq_zero_iff`: a class vanishes exactly when its representative
  lies in the square of the radical, and `TauCeti.irreducibleMorphismMk_eq_iff` the corresponding
  criterion for two classes to agree.
* `TauCeti.irreducibleMorphismMk_ne_zero_iff`: **the detection statement** — between objects with
  local endomorphism rings a class is nonzero exactly when its representative is an irreducible
  morphism.
* `TauCeti.nontrivial_irreducibleMorphismSpace_iff` and
  `TauCeti.subsingleton_irreducibleMorphismSpace_iff`: the space is nontrivial exactly when an
  irreducible morphism exists, and vanishes exactly when none does.
* `TauCeti.jacobsonRadicalSubmodule_map_homCongr` and
  `TauCeti.jacobsonRadicalSqSubmodule_map_homCongr`: conjugation by isomorphisms carries the
  radical onto the radical and its square onto its square.
* `TauCeti.irreducibleMorphismSpaceCongr_refl`, `TauCeti.irreducibleMorphismSpaceCongr_trans` and
  `TauCeti.irreducibleMorphismSpaceCongr_symm`: the invariance is functorial in the two
  isomorphisms.
* `TauCeti.exists_isIrreducibleMorphism_irreducibleMorphismMk_eq`: every nonzero class is
  represented by an irreducible morphism.
* `TauCeti.finrank_irreducibleMorphismSpace_le`: over a division ring the space is no larger than
  the morphism space it is carved out of, and
  `TauCeti.finrank_irreducibleMorphismSpace_pos_iff` that its dimension — the number of arrows
  `X → Y` of the Auslander-Reiten quiver — is positive exactly when an irreducible morphism
  `X ⟶ Y` exists.

## Implementation notes

The quotient is formed inside the *submodule* `rad(X, Y)`, so its elements are classes of elements
of the subtype `↥(jacobsonRadicalSubmodule k X Y)`; every statement below is therefore phrased with
the underlying morphism `(f : X ⟶ Y)` of such an element, so that a caller never has to see the
subtype's own submodule `TauCeti.jacobsonRadicalSqSubmoduleIn`.  The alternative, quotienting the
whole morphism space by `rad²`, is a different module — it has the non-radical morphisms in it as
well — and is not what an arrow of the Auslander-Reiten quiver counts.

`TauCeti.irreducibleMorphismSpace` is a plain `def` rather than an abbreviation, with its additive
and `k`-module structures transported by `inferInstanceAs`, so that the quotient is not unfolded by
`simp` in goals that mention it.  Consequently the API below is stated for
`TauCeti.irreducibleMorphismMk`, which is `Submodule.mkQ` at that type, and no statement mentions
`Submodule.Quotient.mk` directly.  It and the submodule it divides by carry `@[expose]`, without
which a downstream module could not see that the two transported instances are the quotient's own
and so could not use Mathlib's quotient API on it at all; `TauCeti.irreducibleMorphismMk` does not,
its `Submodule.mkQ` implementation being reached only through the lemmas below.

Conjugation by a pair of isomorphisms is Mathlib's `CategoryTheory.Linear.homCongr`, so that the
two `map` lemmas are statements about a `k`-linear equivalence of morphism spaces that is already
available, and the induced equivalence of quotients is `Submodule.Quotient.equiv` applied to them.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.7 and
  VII.1, where `rad / rad²` is introduced as the space the arrows of the Auslander-Reiten quiver are
  counted by.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1 and VII.1.
* [Quiver-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md),
  Layer 6: "the **radical** of the module category ... and its square; the irreducible maps are
  `rad / rad²`", and sublayer 6F, the Auslander-Reiten quiver, "whose arrows are a basis of the
  irreducible morphisms `rad(M, N) / rad²(M, N)`".
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### The quotient `rad / rad²` -/

section Defs

variable (k : Type*) [Ring k] [Linear k C] (X Y : C)

/-- **The square of the radical, as a submodule of the radical.**  `TauCeti.jacobsonRadicalSq` is a
subgroup of the whole morphism space `X ⟶ Y`; this is its preimage in the submodule
`TauCeti.jacobsonRadicalSubmodule`, which is what the quotient `rad(X, Y) / rad²(X, Y)` divides by.
The two describe the same morphisms, by `TauCeti.mem_jacobsonRadicalSqSubmoduleIn`. -/
@[expose]
def jacobsonRadicalSqSubmoduleIn : Submodule k (jacobsonRadicalSubmodule k X Y) :=
  (jacobsonRadicalSqSubmodule k X Y).comap (jacobsonRadicalSubmodule k X Y).subtype

/-- **The space of irreducible morphisms** `X ⟶ Y`, the quotient `rad(X, Y) / rad²(X, Y)`.

Between objects with local endomorphism rings its nonzero classes are exactly the irreducible
morphisms (`TauCeti.irreducibleMorphismMk_ne_zero_iff`), and its dimension over the base is the
number of arrows `X → Y` of the Auslander-Reiten quiver. -/
@[expose]
def irreducibleMorphismSpace : Type v :=
  jacobsonRadicalSubmodule k X Y ⧸ jacobsonRadicalSqSubmoduleIn k X Y

instance : AddCommGroup (irreducibleMorphismSpace k X Y) :=
  inferInstanceAs (AddCommGroup
    (jacobsonRadicalSubmodule k X Y ⧸ jacobsonRadicalSqSubmoduleIn k X Y))

instance : Module k (irreducibleMorphismSpace k X Y) :=
  inferInstanceAs (Module k
    (jacobsonRadicalSubmodule k X Y ⧸ jacobsonRadicalSqSubmoduleIn k X Y))

/-- **The class of a radical morphism** in the space of irreducible morphisms, as a `k`-linear
map. -/
def irreducibleMorphismMk :
    jacobsonRadicalSubmodule k X Y →ₗ[k] irreducibleMorphismSpace k X Y :=
  (jacobsonRadicalSqSubmoduleIn k X Y).mkQ

variable {k X Y}

/-- Membership in `TauCeti.jacobsonRadicalSqSubmoduleIn` is membership of the underlying morphism
in the square of the radical. -/
@[simp]
theorem mem_jacobsonRadicalSqSubmoduleIn {f : jacobsonRadicalSubmodule k X Y} :
    f ∈ jacobsonRadicalSqSubmoduleIn k X Y ↔ (f : X ⟶ Y) ∈ jacobsonRadicalSq X Y :=
  mem_jacobsonRadicalSqSubmodule

/-- Every element of the space of irreducible morphisms is the class of a radical morphism. -/
theorem irreducibleMorphismMk_surjective :
    Function.Surjective (irreducibleMorphismMk k X Y) :=
  Submodule.mkQ_surjective _

/-- **A class vanishes exactly when its representative lies in the square of the radical.** -/
@[simp]
theorem irreducibleMorphismMk_eq_zero_iff {f : jacobsonRadicalSubmodule k X Y} :
    irreducibleMorphismMk k X Y f = 0 ↔ (f : X ⟶ Y) ∈ jacobsonRadicalSq X Y :=
  (Submodule.Quotient.mk_eq_zero (jacobsonRadicalSqSubmoduleIn k X Y)).trans
    mem_jacobsonRadicalSqSubmoduleIn

/-- **Two radical morphisms have the same class exactly when they differ by an element of the
square of the radical.** -/
theorem irreducibleMorphismMk_eq_iff {f g : jacobsonRadicalSubmodule k X Y} :
    irreducibleMorphismMk k X Y f = irreducibleMorphismMk k X Y g ↔
      (f : X ⟶ Y) - (g : X ⟶ Y) ∈ jacobsonRadicalSq X Y := by
  rw [← sub_eq_zero, ← map_sub, irreducibleMorphismMk_eq_zero_iff, Submodule.coe_sub]

end Defs

/-! ### Detection of irreducible morphisms -/

section Local

variable {k : Type*} [Ring k] [Linear k C] [Limits.HasBinaryBiproducts C]
variable {X Y : C} [IsLocalRing (End X)] [IsLocalRing (End Y)]

/-- **The nonzero classes are the irreducible morphisms.**  Between objects with local endomorphism
rings a radical morphism is irreducible exactly when it is not a composite of two radical morphisms
(`TauCeti.isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq`), which is
exactly the nonvanishing of its class.  This is the sense in which
`TauCeti.irreducibleMorphismSpace` is the space of irreducible morphisms. -/
theorem irreducibleMorphismMk_ne_zero_iff {f : jacobsonRadicalSubmodule k X Y} :
    irreducibleMorphismMk k X Y f ≠ 0 ↔ IsIrreducibleMorphism (f : X ⟶ Y) := by
  rw [ne_eq, irreducibleMorphismMk_eq_zero_iff,
    isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq]
  exact (and_iff_right (mem_jacobsonRadicalSubmodule.1 f.2)).symm

/-- **The space of irreducible morphisms is nontrivial exactly when an irreducible morphism
exists.**  This is what makes "there is an arrow `X → Y` in the Auslander-Reiten quiver" and "there
is an irreducible morphism `X ⟶ Y`" the same statement. -/
theorem nontrivial_irreducibleMorphismSpace_iff :
    Nontrivial (irreducibleMorphismSpace k X Y) ↔ ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  constructor
  · intro _
    obtain ⟨x, hx⟩ := exists_ne (0 : irreducibleMorphismSpace k X Y)
    obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
    exact ⟨(f : X ⟶ Y), irreducibleMorphismMk_ne_zero_iff.1 hx⟩
  · rintro ⟨f, hf⟩
    refine nontrivial_of_ne (irreducibleMorphismMk k X Y
      ⟨f, mem_jacobsonRadicalSubmodule.2 hf.mem_jacobsonRadical⟩) 0 ?_
    exact irreducibleMorphismMk_ne_zero_iff.2 hf

/-- **Every nonzero class is represented by an irreducible morphism.**  Together with
`TauCeti.irreducibleMorphismMk_surjective` this says that the irreducible morphisms `X ⟶ Y`
exhaust the nonzero elements of `TauCeti.irreducibleMorphismSpace k X Y`. -/
theorem exists_isIrreducibleMorphism_irreducibleMorphismMk_eq
    {x : irreducibleMorphismSpace k X Y} (hx : x ≠ 0) :
    ∃ f : jacobsonRadicalSubmodule k X Y,
      IsIrreducibleMorphism (f : X ⟶ Y) ∧ irreducibleMorphismMk k X Y f = x := by
  obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
  exact ⟨f, irreducibleMorphismMk_ne_zero_iff.1 hx, rfl⟩

/-- **The space of irreducible morphisms vanishes exactly when there is no irreducible
morphism**, the contrapositive form of `TauCeti.nontrivial_irreducibleMorphismSpace_iff`. -/
theorem subsingleton_irreducibleMorphismSpace_iff :
    Subsingleton (irreducibleMorphismSpace k X Y) ↔ ∀ f : X ⟶ Y, ¬ IsIrreducibleMorphism f := by
  rw [← not_nontrivial_iff_subsingleton, nontrivial_irreducibleMorphismSpace_iff]
  exact not_exists

end Local

/-! ### Invariance under isomorphism -/

section Congr

variable (k : Type*) [Ring k] [Linear k C] {X X' Y Y' : C}

/-- **Conjugation by isomorphisms carries the radical onto the radical.**  Both containments are
the radical being a two-sided ideal of the category: `e.inv ≫ f ≫ e'.hom` is radical whenever `f`
is, and the reverse containment is the same statement for the inverse conjugation
`e.hom ≫ g ≫ e'.inv`. -/
theorem jacobsonRadicalSubmodule_map_homCongr (e : X ≅ X') (e' : Y ≅ Y') :
    (jacobsonRadicalSubmodule k X Y).map (Linear.homCongr k e e').toLinearMap =
      jacobsonRadicalSubmodule k X' Y' := by
  refine le_antisymm ?_ fun g hg => ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Linear.homCongr_apply,
      mem_jacobsonRadicalSubmodule] at hf ⊢
    exact comp_mem_jacobsonRadical_right (comp_mem_jacobsonRadical_left e.inv hf) e'.hom
  · refine ⟨(Linear.homCongr k e e').symm g, ?_, by simp⟩
    rw [SetLike.mem_coe, Linear.homCongr_symm_apply, mem_jacobsonRadicalSubmodule]
    exact comp_mem_jacobsonRadical_left e.hom
      (comp_mem_jacobsonRadical_right (mem_jacobsonRadicalSubmodule.1 hg) e'.inv)

/-- **Conjugation by isomorphisms carries the square of the radical onto the square of the
radical**, the square being a two-sided ideal of the category just as the radical is. -/
theorem jacobsonRadicalSqSubmodule_map_homCongr (e : X ≅ X') (e' : Y ≅ Y') :
    (jacobsonRadicalSqSubmodule k X Y).map (Linear.homCongr k e e').toLinearMap =
      jacobsonRadicalSqSubmodule k X' Y' := by
  refine le_antisymm ?_ fun g hg => ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Linear.homCongr_apply,
      mem_jacobsonRadicalSqSubmodule] at hf ⊢
    exact comp_mem_jacobsonRadicalSq_right (comp_mem_jacobsonRadicalSq_left e.inv hf) e'.hom
  · refine ⟨(Linear.homCongr k e e').symm g, ?_, by simp⟩
    rw [SetLike.mem_coe, Linear.homCongr_symm_apply, mem_jacobsonRadicalSqSubmodule]
    exact comp_mem_jacobsonRadicalSq_left e.hom
      (comp_mem_jacobsonRadicalSq_right (mem_jacobsonRadicalSqSubmodule.1 hg) e'.inv)

/-- **Conjugation by isomorphisms, as an equivalence of radicals.** -/
noncomputable def jacobsonRadicalSubmoduleCongr (e : X ≅ X') (e' : Y ≅ Y') :
    jacobsonRadicalSubmodule k X Y ≃ₗ[k] jacobsonRadicalSubmodule k X' Y' :=
  (Linear.homCongr k e e').submoduleMap (jacobsonRadicalSubmodule k X Y) ≪≫ₗ
    LinearEquiv.ofEq _ _ (jacobsonRadicalSubmodule_map_homCongr k e e')

@[simp]
theorem coe_jacobsonRadicalSubmoduleCongr (e : X ≅ X') (e' : Y ≅ Y')
    (f : jacobsonRadicalSubmodule k X Y) :
    (jacobsonRadicalSubmoduleCongr k e e' f : X' ⟶ Y') = (e.inv ≫ (f : X ⟶ Y)) ≫ e'.hom :=
  (rfl)

@[simp]
theorem coe_jacobsonRadicalSubmoduleCongr_symm (e : X ≅ X') (e' : Y ≅ Y')
    (g : jacobsonRadicalSubmodule k X' Y') :
    ((jacobsonRadicalSubmoduleCongr k e e').symm g : X ⟶ Y) =
      e.hom ≫ (g : X' ⟶ Y') ≫ e'.inv := by
  have h := coe_jacobsonRadicalSubmoduleCongr k e e'
    ((jacobsonRadicalSubmoduleCongr k e e').symm g)
  rw [LinearEquiv.apply_symm_apply] at h
  conv_rhs => rw [h]
  simp

/-- **The space of irreducible morphisms depends only on the isomorphism classes of its two
objects**: a pair of isomorphisms `X ≅ X'` and `Y ≅ Y'` induces a `k`-linear equivalence
`Irr(X, Y) ≃ₗ[k] Irr(X', Y')`.  This is what lets the arrows of the Auslander-Reiten quiver be
indexed by isomorphism classes of indecomposables rather than by objects. -/
noncomputable def irreducibleMorphismSpaceCongr (e : X ≅ X') (e' : Y ≅ Y') :
    irreducibleMorphismSpace k X Y ≃ₗ[k] irreducibleMorphismSpace k X' Y' :=
  Submodule.Quotient.equiv _ _ (jacobsonRadicalSubmoduleCongr k e e') <| by
    refine le_antisymm ?_ fun g hg => ?_
    · rw [Submodule.map_le_iff_le_comap]
      intro f hf
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe, mem_jacobsonRadicalSqSubmoduleIn,
        coe_jacobsonRadicalSubmoduleCongr] at hf ⊢
      exact comp_mem_jacobsonRadicalSq_right (comp_mem_jacobsonRadicalSq_left e.inv hf) e'.hom
    · refine ⟨(jacobsonRadicalSubmoduleCongr k e e').symm g, ?_, by simp⟩
      simp only [SetLike.mem_coe, mem_jacobsonRadicalSqSubmoduleIn,
        coe_jacobsonRadicalSubmoduleCongr_symm] at hg ⊢
      exact comp_mem_jacobsonRadicalSq_left e.hom (comp_mem_jacobsonRadicalSq_right hg e'.inv)

@[simp]
theorem irreducibleMorphismSpaceCongr_mk (e : X ≅ X') (e' : Y ≅ Y')
    (f : jacobsonRadicalSubmodule k X Y) :
    irreducibleMorphismSpaceCongr k e e' (irreducibleMorphismMk k X Y f) =
      irreducibleMorphismMk k X' Y' (jacobsonRadicalSubmoduleCongr k e e' f) :=
  (rfl)

/-- Conjugating by the identity isomorphisms does nothing. -/
@[simp]
theorem irreducibleMorphismSpaceCongr_refl (X Y : C) :
    irreducibleMorphismSpaceCongr k (Iso.refl X) (Iso.refl Y) =
      LinearEquiv.refl k (irreducibleMorphismSpace k X Y) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
  rw [irreducibleMorphismSpaceCongr_mk, LinearEquiv.refl_apply]
  exact congrArg _ (Subtype.ext (by simp))

/-- Conjugating by a composite of isomorphisms is conjugating twice. -/
theorem irreducibleMorphismSpaceCongr_trans {X'' Y'' : C} (e : X ≅ X') (e' : Y ≅ Y')
    (d : X' ≅ X'') (d' : Y' ≅ Y'') :
    (irreducibleMorphismSpaceCongr k e e').trans (irreducibleMorphismSpaceCongr k d d') =
      irreducibleMorphismSpaceCongr k (e ≪≫ d) (e' ≪≫ d') := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
  rw [LinearEquiv.trans_apply, irreducibleMorphismSpaceCongr_mk,
    irreducibleMorphismSpaceCongr_mk, irreducibleMorphismSpaceCongr_mk]
  exact congrArg _ (Subtype.ext (by simp))

/-- The inverse of conjugating by a pair of isomorphisms is conjugating by the inverse pair. -/
@[simp]
theorem irreducibleMorphismSpaceCongr_symm (e : X ≅ X') (e' : Y ≅ Y') :
    (irreducibleMorphismSpaceCongr k e e').symm =
      irreducibleMorphismSpaceCongr k e.symm e'.symm := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
  apply (irreducibleMorphismSpaceCongr k e e').injective
  rw [LinearEquiv.apply_symm_apply, irreducibleMorphismSpaceCongr_mk,
    irreducibleMorphismSpaceCongr_mk]
  exact congrArg _ (Subtype.ext (by simp))

end Congr

/-! ### Finite-dimensionality -/

section Finite

variable (k : Type*) [DivisionRing k] [Linear k C] (X Y : C)

instance [FiniteDimensional k (X ⟶ Y)] :
    FiniteDimensional k (irreducibleMorphismSpace k X Y) :=
  inferInstanceAs (FiniteDimensional k
    (jacobsonRadicalSubmodule k X Y ⧸ jacobsonRadicalSqSubmoduleIn k X Y))

/-- **The space of irreducible morphisms is no larger than the morphism space it is carved out
of.**  This is the bound that makes the Auslander-Reiten quiver of a category with
finite-dimensional morphism spaces locally finite.  Finite-dimensionality of `X ⟶ Y` is a genuine
hypothesis and not merely a convenience: without it the right-hand side is `0` by the convention
for `Module.finrank`, while the quotient can perfectly well be finite-dimensional and nonzero. -/
theorem finrank_irreducibleMorphismSpace_le [FiniteDimensional k (X ⟶ Y)] :
    Module.finrank k (irreducibleMorphismSpace k X Y) ≤ Module.finrank k (X ⟶ Y) :=
  (Submodule.finrank_quotient_le _).trans (Submodule.finrank_le _)

/-- **The number of arrows `X → Y` of the Auslander-Reiten quiver is positive exactly when there is
an irreducible morphism `X ⟶ Y`**: the dimension count of
`TauCeti.nontrivial_irreducibleMorphismSpace_iff`. -/
theorem finrank_irreducibleMorphismSpace_pos_iff [FiniteDimensional k (X ⟶ Y)]
    [Limits.HasBinaryBiproducts C] [IsLocalRing (End X)] [IsLocalRing (End Y)] :
    0 < Module.finrank k (irreducibleMorphismSpace k X Y) ↔
      ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  rw [Module.finrank_pos_iff_of_free, nontrivial_irreducibleMorphismSpace_iff]

end Finite

end TauCeti
