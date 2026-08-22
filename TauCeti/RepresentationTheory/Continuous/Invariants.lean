/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# The invariants of a normal subgroup as a representation of the quotient

For a continuous representation `π` of a group `G` on `V` and a normal subgroup `S ≤ G`, the
invariants of the restricted representation `π|_S` form a `G`-stable submodule of `V`, and the
action of `G` on it factors through `G ⧸ S`. This file builds that `G ⧸ S`-representation, both in
the unbundled language and in the category `TopRep`, together with the inclusion of the invariants
back into the ambient object.

These are the continuous counterparts of Mathlib's `Representation.toInvariants`,
`Representation.quotientToInvariants`, `Representation.quotientToInvariants_lift` and
`Rep.quotientToInvariantsFunctor`. They are the coefficient half of inflation: the compatible pair
inducing `Hⁿ(G ⧸ S, Xˢ) ⟶ Hⁿ(G, X)` on continuous cohomology consists of the quotient
homomorphism `G → G ⧸ S` together with the inclusion `Xˢ ↪ X`.

## Main definitions

* `ContRepresentation.toInvariants`: the representation of `G` on the invariants of `π|_S`.
* `ContRepresentation.quotientToInvariants`: the representation of `G ⧸ S` on the
  invariants of `π|_S`.
* `TopRep.quotientToInvariants`: the same construction in the category `TopRep`.
* `TopRep.quotientToInvariantsι`: the inclusion of the invariants into the ambient object,
  as a morphism of `G`-objects.
* `TopRep.quotientToInvariantsFunctor`: the functor `X ↦ Xˢ`.

## Main results

* `ContRepresentation.apply_mem_invariants_restrict`: the invariants of `π|_S` are a
  `G`-stable submodule when `S` is normal.
* `ContRepresentation.invariants_restrict_bot`,
  `ContRepresentation.invariants_restrict_top`: the two degenerate subgroups.
* `TopRep.quotientToInvariantsMap_comp_quotientToInvariantsι`: naturality of the inclusion of the
  invariants.
* `TopRep.isIso_invariantsResMap_quotientToInvariantsι`: taking quotient invariants and then
  invariants under the quotient recovers the original invariants.

These declarations live in the root `ContRepresentation` and `TopRep` namespaces, rather than
under `TauCeti`, so that dot notation on the Mathlib types they extend elaborates.
-/

public section

open CategoryTheory TauCeti.ContRepresentation

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]
  (π : ContRepresentation R G V) (S : Subgroup G) [S.Normal]

omit [S.Normal] in
variable {π S} in
-- Not `@[simp]`: `simp` already normalizes the left-hand side to the right-hand side through
-- `mem_invariants`, `restrict_apply_apply` and `Subtype.forall`, so the attribute would make this
-- a `simpNF` violation. This is the `rw`-usable form of that normalization.
/-- Membership in the invariants of `π|_S`, in terms of elements of `G` lying in `S`. -/
theorem mem_invariants_restrict {v : V} :
    v ∈ (π.restrict S.subtype).invariants ↔ ∀ s ∈ S, π s v = v :=
  ⟨fun hv s hs ↦ hv ⟨s, hs⟩, fun hv s ↦ hv (s : G) s.2⟩

omit [S.Normal] in
/-- The trivial subgroup fixes everything. -/
@[simp]
theorem invariants_restrict_bot : (π.restrict (⊥ : Subgroup G).subtype).invariants = ⊤ := by
  ext v
  simp

omit [S.Normal] in
/-- The invariants of the whole group are the invariants of `π`. -/
@[simp]
theorem invariants_restrict_top : (π.restrict (⊤ : Subgroup G).subtype).invariants = π.invariants :=
  SetLike.ext fun _ ↦ by simp [mem_invariants]

/-- For a normal subgroup `S`, the invariants of `π|_S` are a `G`-stable submodule: this is the
statement that makes `toInvariants` below a representation of `G` and not merely of `S`. -/
theorem apply_mem_invariants_restrict (g : G) (v : V)
    (hv : v ∈ (π.restrict S.subtype).invariants) :
    π g v ∈ (π.restrict S.subtype).invariants := by
  rw [mem_invariants_restrict] at hv ⊢
  intro s hs
  have hv' : π (g⁻¹ * s * g) v = v := hv _ ((‹S.Normal›).conj_mem' s hs g)
  have hg : s * g = g * (g⁻¹ * s * g) := by group
  rw [← mul_apply_eq_comp, ← map_mul, hg, map_mul, mul_apply_eq_comp, hv']

/-- The representation of `G` on the invariants of `π|_S`, for a normal subgroup `S ≤ G`; the
continuous counterpart of `Representation.toInvariants`. -/
abbrev toInvariants : ContRepresentation R G (π.restrict S.subtype).invariants :=
  subrepresentation π _ (apply_mem_invariants_restrict π S)

-- Not `@[simp]`: `toInvariants` is reducible, so `simp` already reaches this statement through
-- `coe_subrepresentation_apply`.
/-- The action on the invariants of `π|_S` is the ambient action, read on the underlying vectors. -/
theorem coe_toInvariants_apply (g : G) (v : (π.restrict S.subtype).invariants) :
    ((toInvariants π S g v : (π.restrict S.subtype).invariants) : V) = π g (v : V) :=
  coe_subrepresentation_apply g v

/-- `S` acts trivially on the invariants of `π|_S`, which is what lets the `G`-action descend to
`G ⧸ S`. -/
theorem toInvariants_apply_of_mem {s : G} (hs : s ∈ S) : toInvariants π S s = 1 := by
  ext v
  simpa using v.2 ⟨s, hs⟩

/-- The representation of `G ⧸ S` on the invariants of `π|_S`, for a normal subgroup `S ≤ G`; the
continuous counterpart of `Representation.quotientToInvariants`. -/
def quotientToInvariants :
    ContRepresentation R (G ⧸ S) (π.restrict S.subtype).invariants :=
  .ofMonoidHom (QuotientGroup.lift S (toInvariants π S).toMonoidHom
    fun _ hs ↦ toInvariants_apply_of_mem π S hs)

@[simp]
theorem quotientToInvariants_mk (g : G) :
    quotientToInvariants π S (g : G ⧸ S) = toInvariants π S g :=
  (rfl)

-- Not `@[simp]`: `simp` already reaches this statement through `quotientToInvariants_mk` and
-- `coe_subrepresentation_apply`.
/-- The `G ⧸ S`-action on the invariants of `π|_S`, read on the underlying vectors. -/
theorem coe_quotientToInvariants_mk_apply (g : G) (v : (π.restrict S.subtype).invariants) :
    ((quotientToInvariants π S (g : G ⧸ S) v : (π.restrict S.subtype).invariants) : V) =
      π g (v : V) := by
  rw [quotientToInvariants_mk, coe_toInvariants_apply]

end ContRepresentation

namespace TopRep

open ContRepresentation

variable {R : Type*} [Ring R] [TopologicalSpace R] {G : Type*} [Group G]
  (X : TopRep R G) (S : Subgroup G) [S.Normal]

/-- The `G ⧸ S`-object on the `S`-invariants of a topological representation, for a normal
subgroup `S ≤ G`. This is the coefficient half of inflation. -/
abbrev quotientToInvariants : TopRep R (G ⧸ S) :=
  of (ContRepresentation.quotientToInvariants X.ρ S)

-- Exposed: the `rfl`-proof of `quotientToInvariantsι_apply` below reads off the underlying map.
/-- The inclusion `Xˢ ↪ X` of the `S`-invariants into the ambient object, as a morphism of
`G`-objects, where `Xˢ` is a `G`-object by restriction along `G → G ⧸ S`. Together with the
quotient homomorphism it is the compatible pair defining inflation; it is the continuous
counterpart of `Representation.quotientToInvariants_lift`. -/
@[expose] def quotientToInvariantsι :
    res (QuotientGroup.mk' S : G →* G ⧸ S) (quotientToInvariants X S) ⟶ X :=
  ofHom
    { toContinuousLinearMap := (X.ρ.restrict S.subtype).invariants.subtypeL
      isIntertwining' _ := by ext v; simp [ContRepresentation.restrict_apply_apply] }

@[simp]
theorem quotientToInvariantsι_apply (v : (X.ρ.restrict S.subtype).invariants) :
    quotientToInvariantsι X S v = (v : X) :=
  (rfl)

-- Exposed: the `rfl`-proof of `coe_quotientToInvariantsMap_apply` below reads off the underlying
-- map, and `quotientToInvariantsMap_id` and `_comp` are proved by `ext`.
/-- A morphism `f : X ⟶ Y` of topological `G`-representations restricts to the `S`-invariants. -/
@[expose] def quotientToInvariantsMap {X Y : TopRep R G} (f : X ⟶ Y) (S : Subgroup G) [S.Normal] :
    quotientToInvariants X S ⟶ quotientToInvariants Y S :=
  ofHom
    { toContinuousLinearMap := (f.hom.restrict S.subtype).mapInvariants
      isIntertwining' g := QuotientGroup.induction_on g fun g ↦ by
        ext v
        simpa [ContIntertwiningMap.mapInvariants_apply] using f.hom.isIntertwining g (v : X) }

@[simp]
theorem coe_quotientToInvariantsMap_apply {X Y : TopRep R G} (f : X ⟶ Y)
    (v : (X.ρ.restrict S.subtype).invariants) :
    ((quotientToInvariantsMap f S v : (Y.ρ.restrict S.subtype).invariants) : Y) = f.hom (v : X) :=
  (rfl)

@[simp]
theorem quotientToInvariantsMap_id : quotientToInvariantsMap (𝟙 X) S = 𝟙 _ := by
  ext v
  rfl

@[simp]
theorem quotientToInvariantsMap_comp {X Y Z : TopRep R G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    quotientToInvariantsMap (f ≫ g) S =
      quotientToInvariantsMap f S ≫ quotientToInvariantsMap g S := by
  ext v
  rfl

/-- The inclusion of the invariants is natural: restricting `f : X ⟶ Y` to the `S`-invariants and
then including into `Y` is including into `X` and then applying `f`. This is the square that makes
the compatible pair defining inflation natural in the coefficients. -/
@[reassoc, simp]
theorem quotientToInvariantsMap_comp_quotientToInvariantsι {X Y : TopRep R G} (f : X ⟶ Y) :
    (resFunctor (QuotientGroup.mk' S : G →* G ⧸ S)).map (quotientToInvariantsMap f S) ≫
        quotientToInvariantsι Y S = quotientToInvariantsι X S ≫ f := by
  ext v
  rfl

/-- A `G`-invariant vector is `S`-invariant, and the element of `X^S` it becomes is invariant under
the induced `G ⧸ S`-action. -/
private noncomputable def invariantsToQuotientToInvariants :
    invariants X ⟶ invariants (quotientToInvariants X S) :=
  TopModuleCat.ofHom
    ((X.ρ.invariants.subtypeL.codRestrict (X.ρ.restrict S.subtype).invariants
        fun v ↦ invariants_le_invariants_restrict X.ρ S.subtype v.2).codRestrict
      (ContRepresentation.quotientToInvariants X.ρ S).invariants fun v g ↦ by
        induction g using QuotientGroup.induction_on with
        | H g =>
          refine Subtype.ext ?_
          rw [coe_quotientToInvariants_mk_apply]
          exact v.2 g)

-- The two nested `codRestrict`s above change only the proofs of membership in the nested invariant
-- submodules, not the underlying vector.
private theorem coe_invariantsToQuotientToInvariants_apply (v : X.ρ.invariants) :
    (((invariantsToQuotientToInvariants X S) v :
      (X.ρ.restrict S.subtype).invariants) : X.V) = (v : X.V) := by
  rfl

-- Likewise, `invariantsResMap` applied to the inclusion of `S`-invariants retains the vector and
-- only repackages its invariance proof.
private theorem coe_invariantsResMap_quotientToInvariantsι_apply
    (v : (ContRepresentation.quotientToInvariants X.ρ S).invariants) :
    ((invariantsResMap (QuotientGroup.mk' S : G →* G ⧸ S)
        (quotientToInvariantsι X S) v : X.ρ.invariants) : X.V) =
      ((v : (X.ρ.restrict S.subtype).invariants) : X.V) := by
  rfl

/-- **`(X^S)^{G/S}` is canonically isomorphic to `X^G`.** The map induced on invariants by the
inclusion `X^S ⟶ X` is an isomorphism, with inverse preserving the underlying vector. -/
theorem isIso_invariantsResMap_quotientToInvariantsι :
    IsIso (invariantsResMap (QuotientGroup.mk' S : G →* G ⧸ S)
      (quotientToInvariantsι X S)) :=
  ⟨invariantsToQuotientToInvariants X S,
    by
      ext v
      exact (coe_invariantsResMap_quotientToInvariantsι_apply X S v).trans
        (coe_invariantsToQuotientToInvariants_apply X S
          (invariantsResMap (QuotientGroup.mk' S : G →* G ⧸ S)
            (quotientToInvariantsι X S) v)),
    by
      ext v
      exact (coe_invariantsToQuotientToInvariants_apply X S v).trans
        (coe_invariantsResMap_quotientToInvariantsι_apply X S
          ((invariantsToQuotientToInvariants X S) v))⟩

-- Exposed: the generated `@[simps]` field lemmas are `rfl`-proofs about this body.
variable (R G) in
/-- The functor sending a topological `G`-representation `X` to the `G ⧸ S`-representation on
`Xˢ`; the continuous counterpart of `Rep.quotientToInvariantsFunctor`. -/
@[expose, simps]
noncomputable def quotientToInvariantsFunctor (S : Subgroup G) [S.Normal] :
    TopRep R G ⥤ TopRep R (G ⧸ S) where
  obj X := quotientToInvariants X S
  map f := quotientToInvariantsMap f S
  map_id _ := quotientToInvariantsMap_id _ _
  map_comp _ _ := quotientToInvariantsMap_comp _ _ _

end TopRep
