/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
-- Finite-dimensionality of the quotient, for the local finiteness of the Auslander-Reiten quiver.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Non-public: Mathlib's quotient operations occur only inside the declarations below, the API
-- here standing in for them, and the dimension bound only inside proofs.
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The space of irreducible morphisms of a linear category

Between two objects `X` and `Y` of a `k`-linear category with binary biproducts and local
endomorphism rings, the morphisms lying in the radical but not in its square are exactly the
irreducible ones
(`TauCeti.isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq`).  Under
those hypotheses the quotient `rad(X, Y) / rad²(X, Y)` is therefore the `k`-module whose nonzero
classes are the irreducible morphisms `X ⟶ Y`, and it is the space the arrows `X → Y` of the
Auslander-Reiten quiver are read off from.  This file builds that quotient,
`TauCeti.irreducibleMorphismSpace k X Y`, on top of the two submodules supplied by
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
biproducts, exactly as its input in `Radical.Basic` does.  The construction of the quotient and its
linear structure need none of that, so they are stated for an arbitrary `k`-linear category over a
ring `k`.

What is *not* built here is the bimodule structure of `Irr(X, Y)` over the residue division rings
`End X / rad(End X)` and `End Y / rad(End Y)`.  It is the dimensions over *those* rings, not the
`k`-dimension computed below, that count the arrows `X → Y` of the Auslander-Reiten quiver; the two
counts do agree whenever both residue division rings are `k` itself, as happens for instance over an
algebraically closed `k` when the two endomorphism algebras are finite-dimensional over it, but that
is only a sufficient condition — they also agree, vacuously, whenever `Irr(X, Y)` vanishes.  So no
statement below claims to compute an arrow multiplicity: what is proved is the `k`-dimension, its
bound by `finrank k (X ⟶ Y)`, and its positivity exactly when an irreducible morphism exists.

## Main definitions

* `TauCeti.irreducibleMorphismSpace k X Y`: the space `rad(X, Y) / rad²(X, Y)` of irreducible
  morphisms, a `k`-module.
* `TauCeti.irreducibleMorphismMk`: the class of a radical morphism, as a `k`-linear map.
* `TauCeti.irreducibleMorphismLift`: the universal property, a `k`-linear map out of the space
  from one on radical morphisms that kills the square of the radical, unique with its values by
  `TauCeti.irreducibleMorphismSpace_linearMap_ext`.
* `TauCeti.irreducibleMorphismSpaceCongr`: the `k`-linear equivalence induced by a pair of
  isomorphisms of the source and the target.

## Main results

* `TauCeti.irreducibleMorphismMk_eq_zero_iff`: a class vanishes exactly when its representative
  lies in the square of the radical, and `TauCeti.irreducibleMorphismMk_eq_iff` the corresponding
  criterion for two classes to agree.
* `TauCeti.irreducibleMorphismSpace_linearMap_ext`: the uniqueness half of the universal
  property — a `k`-linear map out of the space is determined by its values on classes of radical
  morphisms.
* `TauCeti.irreducibleMorphismMk_ne_zero_iff`: **the detection statement** — between objects with
  local endomorphism rings a class is nonzero exactly when its representative is an irreducible
  morphism.
* `TauCeti.nontrivial_irreducibleMorphismSpace_iff` and
  `TauCeti.subsingleton_irreducibleMorphismSpace_iff`: the space is nontrivial exactly when an
  irreducible morphism exists, and vanishes exactly when none does.
* `TauCeti.irreducibleMorphismSpaceCongr_refl`, `TauCeti.irreducibleMorphismSpaceCongr_trans` and
  `TauCeti.irreducibleMorphismSpaceCongr_symm`: the invariance is functorial in the two
  isomorphisms.
* `TauCeti.exists_isIrreducibleMorphism_irreducibleMorphismMk_eq`: every nonzero class is
  represented by an irreducible morphism.
* `TauCeti.finrank_irreducibleMorphismSpace_le`: over a division ring the space is no larger than
  the morphism space it is carved out of, and
  `TauCeti.finrank_irreducibleMorphismSpace_pos_iff` that its dimension is positive exactly when
  an irreducible morphism `X ⟶ Y` exists.

## Implementation notes

The quotient is formed inside the *submodule* `rad(X, Y)`, so its elements are classes of elements
of the subtype `↥(jacobsonRadicalSubmodule k X Y)`; every statement below is therefore phrased with
the underlying morphism `(f : X ⟶ Y)` of such an element, so that a caller never has to see the
subtype's own submodule, which is private.  The alternative, quotienting the whole morphism space by
`rad²`, is a different module — it has the non-radical morphisms in it as well — and is not what an
arrow of the Auslander-Reiten quiver counts.

`TauCeti.irreducibleMorphismSpace` is a plain `def` rather than an abbreviation, with its additive
and `k`-module structures transported by `inferInstanceAs`, so that the quotient is not unfolded by
`simp` in goals that mention it.  Its body is not exposed, and the submodule it divides by is
private, so that no caller depends on the subtype-quotient representation: the API below stands in
for Mathlib's quotient operations, with `TauCeti.irreducibleMorphismMk` for
`Submodule.Quotient.mk`, `TauCeti.irreducibleMorphismMk_surjective` for quotient induction,
`TauCeti.irreducibleMorphismLift` for `Submodule.liftQ` and
`TauCeti.irreducibleMorphismSpace_linearMap_ext` for `Submodule.linearMap_qext`.

Conjugation by a pair of isomorphisms needs no quotient theory, so the equivalence of radicals it
induces, `TauCeti.jacobsonRadicalSubmoduleCongr`, lives with the radical itself in
`TauCeti.CategoryTheory.Preadditive.Radical.Basic`; the induced equivalence of quotients built here
is Mathlib's `Submodule.Quotient.equiv` applied to it.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.7 and
  VII.1, where `rad / rad²` is introduced as the space the arrows of the Auslander-Reiten quiver are
  counted by.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1 and VII.1.
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
The two describe the same morphisms, by `mem_jacobsonRadicalSqSubmoduleIn`.  It is private: the
constructor, eliminator and equality API below is stated in terms of the underlying morphism, so no
consumer needs the subtype-quotient representation. -/
private def jacobsonRadicalSqSubmoduleIn : Submodule k (jacobsonRadicalSubmodule k X Y) :=
  (jacobsonRadicalSqSubmodule k X Y).submoduleOf (jacobsonRadicalSubmodule k X Y)

/-- **The space of irreducible morphisms** `X ⟶ Y`, the quotient `rad(X, Y) / rad²(X, Y)`.

In a category with binary biproducts, between objects with local endomorphism rings, its nonzero
classes are exactly the irreducible morphisms (`TauCeti.irreducibleMorphismMk_ne_zero_iff`); it is
the space the arrows `X → Y` of the Auslander-Reiten quiver are read off from. -/
def irreducibleMorphismSpace : Type v :=
  jacobsonRadicalSubmodule k X Y ⧸ jacobsonRadicalSqSubmoduleIn k X Y

-- Instances are exposed, so they may not name the private `jacobsonRadicalSqSubmoduleIn`; they
-- transport the quotient's structures along its definition spelled out.
instance : AddCommGroup (irreducibleMorphismSpace k X Y) :=
  inferInstanceAs (AddCommGroup (jacobsonRadicalSubmodule k X Y ⧸
    (jacobsonRadicalSqSubmodule k X Y).submoduleOf (jacobsonRadicalSubmodule k X Y)))

instance : Module k (irreducibleMorphismSpace k X Y) :=
  inferInstanceAs (Module k (jacobsonRadicalSubmodule k X Y ⧸
    (jacobsonRadicalSqSubmodule k X Y).submoduleOf (jacobsonRadicalSubmodule k X Y)))

/-- **The class of a radical morphism** in the space of irreducible morphisms, as a `k`-linear
map. -/
def irreducibleMorphismMk :
    jacobsonRadicalSubmodule k X Y →ₗ[k] irreducibleMorphismSpace k X Y :=
  (jacobsonRadicalSqSubmoduleIn k X Y).mkQ

variable {k X Y}

/-- Membership in `jacobsonRadicalSqSubmoduleIn` is membership of the underlying morphism in the
square of the radical. -/
@[simp]
private theorem mem_jacobsonRadicalSqSubmoduleIn {f : jacobsonRadicalSubmodule k X Y} :
    f ∈ jacobsonRadicalSqSubmoduleIn k X Y ↔ (f : X ⟶ Y) ∈ jacobsonRadicalSq X Y :=
  mem_jacobsonRadicalSqSubmodule

/-- Every element of the space of irreducible morphisms is the class of a radical morphism.  This
is the induction principle for the space: `obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x`
replaces an element by the class of a radical morphism. -/
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
@[simp]
theorem irreducibleMorphismMk_eq_iff {f g : jacobsonRadicalSubmodule k X Y} :
    irreducibleMorphismMk k X Y f = irreducibleMorphismMk k X Y g ↔
      (f : X ⟶ Y) - (g : X ⟶ Y) ∈ jacobsonRadicalSq X Y := by
  rw [← sub_eq_zero, ← map_sub, irreducibleMorphismMk_eq_zero_iff, Submodule.coe_sub]

/-- **The universal property of the space of irreducible morphisms**: a `k`-linear map on radical
morphisms that vanishes on the square of the radical descends to the quotient.  Together
with `TauCeti.irreducibleMorphismLift_irreducibleMorphismMk` and
`TauCeti.irreducibleMorphismMk_surjective` this is how a map out of
`TauCeti.irreducibleMorphismSpace` is built and computed with. -/
def irreducibleMorphismLift {M : Type*} [AddCommGroup M] [Module k M]
    (g : jacobsonRadicalSubmodule k X Y →ₗ[k] M)
    (hg : ∀ f : jacobsonRadicalSubmodule k X Y, (f : X ⟶ Y) ∈ jacobsonRadicalSq X Y → g f = 0) :
    irreducibleMorphismSpace k X Y →ₗ[k] M :=
  (jacobsonRadicalSqSubmoduleIn k X Y).liftQ g fun f hf =>
    hg f (mem_jacobsonRadicalSqSubmoduleIn.1 hf)

/-- The map descending a `k`-linear map along `TauCeti.irreducibleMorphismMk` is the map itself. -/
@[simp]
theorem irreducibleMorphismLift_irreducibleMorphismMk {M : Type*} [AddCommGroup M] [Module k M]
    (g : jacobsonRadicalSubmodule k X Y →ₗ[k] M)
    (hg : ∀ f : jacobsonRadicalSubmodule k X Y, (f : X ⟶ Y) ∈ jacobsonRadicalSq X Y → g f = 0)
    (f : jacobsonRadicalSubmodule k X Y) :
    irreducibleMorphismLift g hg (irreducibleMorphismMk k X Y f) = g f :=
  LinearMap.congr_fun ((jacobsonRadicalSqSubmoduleIn k X Y).liftQ_mkQ g
    fun x hx => hg x (mem_jacobsonRadicalSqSubmoduleIn.1 hx)) f

/-- **A `k`-linear map out of the space of irreducible morphisms is determined by its values on
classes of radical morphisms.**  This is the uniqueness half of the universal property, so that
`TauCeti.irreducibleMorphismLift` is the *only* map with the values
`TauCeti.irreducibleMorphismLift_irreducibleMorphismMk` gives it. -/
@[ext high]
theorem irreducibleMorphismSpace_linearMap_ext {M : Type*} [AddCommGroup M] [Module k M]
    ⦃g₁ g₂ : irreducibleMorphismSpace k X Y →ₗ[k] M⦄
    (h : ∀ f : jacobsonRadicalSubmodule k X Y,
      g₁ (irreducibleMorphismMk k X Y f) = g₂ (irreducibleMorphismMk k X Y f)) :
    g₁ = g₂ :=
  LinearMap.ext fun x => by
    obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
    exact h f

end Defs

/-! ### Detection of irreducible morphisms -/

section Local

variable {k : Type*} [Ring k] [Linear k C] [Limits.HasBinaryBiproducts C]
variable {X Y : C} [IsLocalRing (End X)] [IsLocalRing (End Y)]

/-- **The nonzero classes are the irreducible morphisms.**  In a category with binary biproducts,
between objects with local endomorphism rings, a radical morphism is irreducible exactly when it is
not a composite of two radical morphisms
(`TauCeti.isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq`), which is
exactly the nonvanishing of its class.  This is the sense in which
`TauCeti.irreducibleMorphismSpace` is the space of irreducible morphisms. -/
theorem irreducibleMorphismMk_ne_zero_iff {f : jacobsonRadicalSubmodule k X Y} :
    irreducibleMorphismMk k X Y f ≠ 0 ↔ IsIrreducibleMorphism (f : X ⟶ Y) := by
  rw [ne_eq, irreducibleMorphismMk_eq_zero_iff,
    isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq]
  exact (and_iff_right (mem_jacobsonRadicalSubmodule.1 f.2)).symm

/-- **The space of irreducible morphisms is nontrivial exactly when an irreducible morphism
exists**, in a category with binary biproducts and between objects with local endomorphism rings.
This is what makes "there is an arrow `X → Y` in the Auslander-Reiten quiver" and "there
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

/-- **Every nonzero class is represented by an irreducible morphism**, in a category with binary
biproducts and between objects with local endomorphism rings.  Together with
`TauCeti.irreducibleMorphismMk_surjective` this says that the irreducible morphisms `X ⟶ Y`
exhaust the nonzero elements of `TauCeti.irreducibleMorphismSpace k X Y`. -/
theorem exists_isIrreducibleMorphism_irreducibleMorphismMk_eq
    {x : irreducibleMorphismSpace k X Y} (hx : x ≠ 0) :
    ∃ f : jacobsonRadicalSubmodule k X Y,
      IsIrreducibleMorphism (f : X ⟶ Y) ∧ irreducibleMorphismMk k X Y f = x := by
  obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective x
  exact ⟨f, irreducibleMorphismMk_ne_zero_iff.1 hx, rfl⟩

/-- **The space of irreducible morphisms vanishes exactly when there is no irreducible morphism**,
under the same hypotheses of binary biproducts and local endomorphism rings: the contrapositive
form of `TauCeti.nontrivial_irreducibleMorphismSpace_iff`. -/
theorem subsingleton_irreducibleMorphismSpace_iff :
    Subsingleton (irreducibleMorphismSpace k X Y) ↔ ∀ f : X ⟶ Y, ¬ IsIrreducibleMorphism f := by
  rw [← not_nontrivial_iff_subsingleton, nontrivial_irreducibleMorphismSpace_iff]
  exact not_exists

end Local

/-! ### Invariance of the quotient under isomorphism -/

section Congr

variable (k : Type*) [Ring k] [Linear k C] {X X' Y Y' : C}

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
        coe_jacobsonRadicalSubmoduleCongr_apply] at hf ⊢
      exact comp_mem_jacobsonRadicalSq_right (comp_mem_jacobsonRadicalSq_left e.inv hf) e'.hom
    · refine ⟨(jacobsonRadicalSubmoduleCongr k e e').symm g, ?_, by simp⟩
      simp only [SetLike.mem_coe, mem_jacobsonRadicalSqSubmoduleIn,
        coe_jacobsonRadicalSubmoduleCongr_symm_apply] at hg ⊢
      exact comp_mem_jacobsonRadicalSq_left e.hom (comp_mem_jacobsonRadicalSq_right hg e'.inv)

/-- **Conjugation of the quotient is computed on representatives**: the image of the class of a
radical morphism `f` is the class of its conjugate
`TauCeti.jacobsonRadicalSubmoduleCongr k e e' f`. -/
@[simp]
theorem irreducibleMorphismSpaceCongr_mk (e : X ≅ X') (e' : Y ≅ Y')
    (f : jacobsonRadicalSubmodule k X Y) :
    irreducibleMorphismSpaceCongr k e e' (irreducibleMorphismMk k X Y f) =
      irreducibleMorphismMk k X' Y' (jacobsonRadicalSubmoduleCongr k e e' f) :=
  (Submodule.Quotient.equiv_apply _ _ (jacobsonRadicalSubmoduleCongr k e e') _ _).trans
    (Submodule.mapQ_apply _ _ _ f)

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
@[simp]
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
  inferInstanceAs (FiniteDimensional k (jacobsonRadicalSubmodule k X Y ⧸
    (jacobsonRadicalSqSubmodule k X Y).submoduleOf (jacobsonRadicalSubmodule k X Y)))

/-- **The space of irreducible morphisms is no larger than the morphism space it is carved out
of.**  This is the bound that makes the Auslander-Reiten quiver of a category with
finite-dimensional morphism spaces locally finite.  Finite-dimensionality of `X ⟶ Y` is a genuine
hypothesis and not merely a convenience: without it the right-hand side is `0` by the convention
for `Module.finrank`, while the quotient can perfectly well be finite-dimensional and nonzero. -/
theorem finrank_irreducibleMorphismSpace_le [FiniteDimensional k (X ⟶ Y)] :
    Module.finrank k (irreducibleMorphismSpace k X Y) ≤ Module.finrank k (X ⟶ Y) :=
  (Submodule.finrank_quotient_le _).trans (Submodule.finrank_le _)

/-- **The dimension of the space of irreducible morphisms is positive exactly when there is an
irreducible morphism `X ⟶ Y`**, in a category with binary biproducts and between objects with local
endomorphism rings: the dimension count of `TauCeti.nontrivial_irreducibleMorphismSpace_iff`.  Only
the quotient itself has to be finite-dimensional here, which the instance above supplies whenever
`X ⟶ Y` is. -/
theorem finrank_irreducibleMorphismSpace_pos_iff
    [FiniteDimensional k (irreducibleMorphismSpace k X Y)]
    [Limits.HasBinaryBiproducts C] [IsLocalRing (End X)] [IsLocalRing (End Y)] :
    0 < Module.finrank k (irreducibleMorphismSpace k X Y) ↔
      ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  rw [Module.finrank_pos_iff_of_free, nontrivial_irreducibleMorphismSpace_iff]

end Finite

end TauCeti
