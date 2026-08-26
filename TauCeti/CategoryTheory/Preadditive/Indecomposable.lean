/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Recognizing indecomposable objects from their endomorphisms

Mathlib defines `CategoryTheory.Indecomposable X` as the conjunction "`X` is not a zero object,
and in every decomposition `X ≅ Y ⊞ Z` one of `Y`, `Z` is zero", and proves exactly one criterion
for it: a simple object is indecomposable (`CategoryTheory.indecomposable_of_simple`). That
criterion is too strong for the objects that carry the theory of a finite-dimensional algebra: an
indecomposable projective module is almost never simple. The criterion that does apply is the one
this file supplies — an object all of whose idempotent endomorphisms are trivial is
indecomposable — together with the two forms in which it is used in practice. An object whose
endomorphisms are recorded faithfully in a *local* ring, by a map preserving zero, the identity and
squares, is indecomposable; this is the criterion behind the Krull–Schmidt theorem, and the one
the quiver Jordan blocks need, their endomorphism algebra `k[X]/(Xⁿ⁺¹)` being local but not a
field. And over a field, an object whose endomorphism space is one-dimensional (a *brick*) is
indecomposable.

The converse holds as soon as idempotents split, that is, over an idempotent-complete category
(`CategoryTheory.IsIdempotentComplete`, which every abelian category is): splitting `e` and `𝟙 - e`
produces two retracts of `X` whose idempotents add up to the identity, and any such pair realizes
`X` as their biproduct. So over such a category an object is indecomposable exactly when it is
nonzero and carries no idempotent endomorphism other than `0` and the identity, which is the form
in which indecomposability is *used*: it turns a decomposition of a vertex space into a
decomposition of the whole object.

## Main results

* `TauCeti.indecomposable_of_idempotent_eq_zero_or_id`: a nonzero object whose only idempotent
  endomorphisms are `0` and the identity is indecomposable.
* `TauCeti.indecomposable_of_injective_of_isLocalRing`: **an object whose endomorphisms are
  recorded faithfully in a local ring, by a map preserving zero, the identity and squares, is
  indecomposable.**
* `TauCeti.indecomposable_of_finrank_end_eq_one`: in a `k`-linear category over a field,
  **a brick is indecomposable**.
* `TauCeti.isoBiprodOfRetracts`: two retracts of `X` whose idempotents sum to the identity exhibit
  `X` as their biproduct.
* `TauCeti.idempotent_eq_zero_or_id_of_indecomposable`: the converse of the first criterion, over
  an idempotent-complete category, packaged with it as
  `TauCeti.indecomposable_iff_idempotent_eq_zero_or_id`.
* `TauCeti.isIso_of_isIso_comp`: an invertible composite `f ≫ g` through an object with only
  trivial idempotent endomorphisms has `f` invertible.

## Implementation notes

The idempotent hypothesis is phrased with composition, `e ≫ e = e`, rather than through the ring
`CategoryTheory.End X`, whose multiplication is composition in the opposite order; for an
idempotent the two agree, but the hypothesis is easier to discharge as stated.

`indecomposable_of_injective_of_isLocalRing` records the endomorphisms in an unbundled map `φ`,
asked to be injective, to send `0` to `0` and `𝟙 X` to `1`, and to carry squares to squares,
`φ (e ≫ e) = φ e * φ e`. Those are exactly the equations the proof consumes: an idempotent has an
idempotent record, a local ring pins that record to `0` or `1`, the two normalization equations
say which endomorphisms those values are the records of, and injectivity carries the dichotomy
back to the idempotent. Multiplicativity is asked on squares alone because that is where the proof
meets `φ`, and because it is the hypothesis that costs a use site least: asking instead that `φ`
turn every `≫` into a product would raise a question this one does not, the multiplication of
`End X` being composition in the opposite order. On a square the two orders agree, so no use site
has to choose between them. Bundling `φ` as a ring homomorphism would settle the order the other
way and demand additivity besides, which no use site has reason to prove. The ring is not asked to
be commutative because the endomorphism ring of an indecomposable object, the intended source of
`φ`, is not.

Two neighbours state the same idea in narrower settings and do not reach the objects that need it
here. `TauCeti.indecomposable_iff_isLocalRing_end` asks `CategoryTheory.End` itself to be local but
is confined to `ModuleCat A` and to modules of finite length;
`TauCeti.isIndecomposableModule_of_isLocalRing_end` is the statement for bare modules. A quiver
representation is a functor `Paths Q ⥤ ModuleCat k`, not an object of `ModuleCat A`, and asking for
`IsLocalRing (X ⟶ X)` would make every use site exhibit its endomorphisms as a ring first —
recording them instead in a ring already known to be local is what makes the criterion cheap to
apply.

`indecomposable_of_idempotent_eq_zero_or_id` extracts, from an isomorphism `X ≅ Y ⊞ Z`, the
idempotent `biprod.fst ≫ biprod.inl` transported to `X`. It is `0` exactly when `Y` is zero and the
identity exactly when `Z` is zero, so the hypothesis splits the decomposition; the proof reads off
`𝟙 Y` and `𝟙 Z` from it using only the biproduct equations `biprod.inl_fst`, `biprod.inr_snd` and
`biprod.inr_fst`.

That every endomorphism of a brick is a scalar is Mathlib's `finrank_eq_one_iff_of_nonzero'`
applied to the identity, which spans the endomorphism space because it is nonzero.

The brick criterion is stated for a field. The argument itself only inverts one scalar, so it
would run over a division ring, but `CategoryTheory.Linear` takes a commutative base and
`Module.finrank` is the invariant used by the consumers, so no generality is lost in practice.

`isoBiprodOfRetracts` asks only for the two retractions and the identity `r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X`;
the orthogonality relations `i₁ ≫ r₂ = 0` and `i₂ ≫ r₁ = 0` that make the comparison map an
isomorphism are consequences, extracted by cancelling the split monomorphisms `i₁` and `i₂`. Stating
it this way keeps it usable from any source of complementary idempotents, not only from
`CategoryTheory.IsIdempotentComplete.idempotents_split`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **An object with no nontrivial idempotent endomorphism is indecomposable.** A decomposition
`X ≅ Y ⊞ Z` produces the idempotent `biprod.fst ≫ biprod.inl` on `X`; it is `0` only if `Y` is
zero, and the identity only if `Z` is zero. -/
theorem indecomposable_of_idempotent_eq_zero_or_id [HasBinaryBiproducts C] {X : C} (hX : ¬ IsZero X)
    (h : ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X) : Indecomposable X := by
  refine ⟨hX, fun Y Z i ↦ ?_⟩
  have hidem : (i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv) ≫
      (i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv) = i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv := by
    simp
  rcases h _ hidem with h0 | h1
  · refine Or.inl ((IsZero.iff_id_eq_zero Y).mpr ?_)
    -- Conjugating back and framing with `biprod.inl`, `biprod.fst` turns the idempotent into `𝟙 Y`.
    have := congrArg (fun f : X ⟶ X ↦ biprod.inl ≫ i.inv ≫ f ≫ i.hom ≫ biprod.fst) h0
    simpa using this
  · refine Or.inr ((IsZero.iff_id_eq_zero Z).mpr ?_)
    -- Framing instead with `biprod.inr`, `biprod.snd` kills the idempotent and leaves `𝟙 Z`.
    have := congrArg (fun f : X ⟶ X ↦ biprod.inr ≫ i.inv ≫ f ≫ i.hom ≫ biprod.snd) h1
    simpa using this.symm

/-- **An object whose endomorphisms are recorded faithfully in a local ring is indecomposable.**
The record `φ` is asked to be injective and to preserve zero, the identity and squares. An
idempotent endomorphism then has an idempotent record, and a local ring carries no idempotent
other than `0` and `1` (`TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`), so the
record — and with it the endomorphism, the record being faithful — is `0` or the identity. This is
the criterion behind the Krull–Schmidt theorem: an object whose endomorphism ring is local is
indecomposable. -/
theorem indecomposable_of_injective_of_isLocalRing [HasBinaryBiproducts C] {X : C} (hX : ¬ IsZero X)
    {R : Type*} [Ring R] [IsLocalRing R] (φ : (X ⟶ X) → R) (hφ : Function.Injective φ)
    (hzero : φ 0 = 0) (hid : φ (𝟙 X) = 1) (hsq : ∀ e : X ⟶ X, φ (e ≫ e) = φ e * φ e) :
    Indecomposable X := by
  refine indecomposable_of_idempotent_eq_zero_or_id hX fun e he ↦ ?_
  have hidem : IsIdempotentElem (φ e) := (hsq e).symm.trans (congrArg φ he)
  rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · exact Or.inl (hφ (h0.trans hzero.symm))
  · exact Or.inr (hφ (h1.trans hid.symm))

/-- **Two retracts whose idempotents sum to the identity split an object as a biproduct.** Its
comparison map and inverse are read off by `TauCeti.isoBiprodOfRetracts_hom` and
`TauCeti.isoBiprodOfRetracts_inv`. -/
noncomputable def isoBiprodOfRetracts [HasBinaryBiproducts C] {X Y Z : C} (i₁ : Y ⟶ X) (r₁ : X ⟶ Y)
    (i₂ : Z ⟶ X) (r₂ : X ⟶ Z) (h₁ : i₁ ≫ r₁ = 𝟙 Y) (h₂ : i₂ ≫ r₂ = 𝟙 Z)
    (h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X) : X ≅ Y ⊞ Z := by
  -- `i₁` and `i₂` are split monomorphisms, so orthogonality can be checked after composing with
  -- them, where the hypothesis `h` and the two retraction identities settle it.
  haveI : IsSplitMono i₁ := ⟨⟨r₁, h₁⟩⟩
  haveI : IsSplitMono i₂ := ⟨⟨r₂, h₂⟩⟩
  have horth₁ : i₁ ≫ r₂ = 0 := by
    have key : i₁ ≫ (r₁ ≫ i₁ + r₂ ≫ i₂) = i₁ := by rw [h, Category.comp_id]
    rw [Preadditive.comp_add, ← Category.assoc, h₁, Category.id_comp] at key
    rw [← cancel_mono i₂, Category.assoc]
    simpa using key
  have horth₂ : i₂ ≫ r₁ = 0 := by
    have key : i₂ ≫ (r₁ ≫ i₁ + r₂ ≫ i₂) = i₂ := by rw [h, Category.comp_id]
    rw [Preadditive.comp_add, ← Category.assoc (f := i₂) (g := r₂), h₂, Category.id_comp] at key
    rw [← cancel_mono i₁, Category.assoc]
    simpa using key
  exact
    { hom := biprod.lift r₁ r₂
      inv := biprod.desc i₁ i₂
      hom_inv_id := by rw [biprod.lift_desc, h]
      inv_hom_id := by
        refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
          simp [h₁, h₂, horth₁, horth₂] }

/-- The comparison map of `TauCeti.isoBiprodOfRetracts` is the pair of the two retractions. -/
@[simp]
theorem isoBiprodOfRetracts_hom [HasBinaryBiproducts C] {X Y Z : C} {i₁ : Y ⟶ X} {r₁ : X ⟶ Y}
    {i₂ : Z ⟶ X} {r₂ : X ⟶ Z} {h₁ : i₁ ≫ r₁ = 𝟙 Y} {h₂ : i₂ ≫ r₂ = 𝟙 Z}
    {h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X} :
    (isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ h).hom = biprod.lift r₁ r₂ :=
  -- The parentheses are load-bearing: `isoBiprodOfRetracts` does not expose its body, and the
  -- bare-`rfl` elaborator refuses to unfold a sealed definition, even in the defining module.
  (rfl)

/-- The inverse of `TauCeti.isoBiprodOfRetracts` is the pair of the two sections. -/
@[simp]
theorem isoBiprodOfRetracts_inv [HasBinaryBiproducts C] {X Y Z : C} {i₁ : Y ⟶ X} {r₁ : X ⟶ Y}
    {i₂ : Z ⟶ X} {r₂ : X ⟶ Z} {h₁ : i₁ ≫ r₁ = 𝟙 Y} {h₂ : i₂ ≫ r₂ = 𝟙 Z}
    {h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X} :
    (isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ h).inv = biprod.desc i₁ i₂ :=
  (rfl)

/-- **An indecomposable object has no nontrivial idempotent endomorphism**, as soon as idempotents
split. This is the converse of `TauCeti.indecomposable_of_idempotent_eq_zero_or_id`. -/
theorem idempotent_eq_zero_or_id_of_indecomposable [HasBinaryBiproducts C] [IsIdempotentComplete C]
    {X : C} (hX : Indecomposable X) {e : X ⟶ X} (he : e ≫ e = e) : e = 0 ∨ e = 𝟙 X := by
  obtain ⟨Y, i₁, r₁, h₁, hr₁⟩ := IsIdempotentComplete.idempotents_split X e he
  obtain ⟨Z, i₂, r₂, h₂, hr₂⟩ := IsIdempotentComplete.idempotents_split X (𝟙 X - e) (by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, he])
  have hsum : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X := by rw [hr₁, hr₂]; abel
  rcases hX.2 Y Z (isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ hsum) with hY | hZ
  · exact Or.inl (by rw [← hr₁, hY.eq_of_tgt r₁ 0, Limits.zero_comp])
  · refine Or.inr (sub_eq_zero.mp ?_).symm
    rw [← hr₂, hZ.eq_of_tgt r₂ 0, Limits.zero_comp]

/-- **Indecomposability is the triviality of the idempotent endomorphisms**, over a category in
which idempotents split. -/
theorem indecomposable_iff_idempotent_eq_zero_or_id [HasBinaryBiproducts C]
    [IsIdempotentComplete C] {X : C} :
    Indecomposable X ↔ ¬ IsZero X ∧ ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X :=
  ⟨fun hX ↦ ⟨hX.1, fun _ he ↦ idempotent_eq_zero_or_id_of_indecomposable hX he⟩,
    fun hX ↦ indecomposable_of_idempotent_eq_zero_or_id hX.1 hX.2⟩

omit [Preadditive C] in
/-- **A composite that is invertible has an invertible first factor**, when the object it passes
through has only the trivial idempotent endomorphisms and the identity of the source is nonzero:
the composite produces the idempotent `(g ≫ inv (f ≫ g)) ≫ f` of `Y`, which is then `0` or `𝟙 Y`,
and `0` is excluded by `𝟙 X ≠ 0`.

The hypotheses are the two consequences of indecomposability that the argument uses, in the form
`TauCeti.idempotent_eq_zero_or_id_of_indecomposable` supplies the second one; neither is stated as
indecomposability itself, which would need biproducts and splitting idempotents. Only the zero
morphisms are used, not the additivity of the hom-groups, so the statement is made at
`CategoryTheory.Limits.HasZeroMorphisms` rather than in the preadditive setting of the rest of
this file. -/
theorem isIso_of_isIso_comp [HasZeroMorphisms C] {X Y : C} (hX : 𝟙 X ≠ 0)
    (hY : ∀ e : Y ⟶ Y, e ≫ e = e → e = 0 ∨ e = 𝟙 Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (h : IsIso (f ≫ g)) : IsIso f := by
  have := h
  have hfp : f ≫ (g ≫ inv (f ≫ g)) = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]
  have hidem : ((g ≫ inv (f ≫ g)) ≫ f) ≫ (g ≫ inv (f ≫ g)) ≫ f = (g ≫ inv (f ≫ g)) ≫ f := by
    rw [Category.assoc, ← Category.assoc f, hfp, Category.id_comp]
  rcases hY _ hidem with h0 | h1
  · exfalso
    have hf0 : f = 0 := by
      have hz : f ≫ (g ≫ inv (f ≫ g)) ≫ f = 0 := by rw [h0, comp_zero]
      rwa [← Category.assoc, hfp, Category.id_comp] at hz
    have hzero : f ≫ (g ≫ inv (f ≫ g)) = 0 := by
      simpa using congrArg (fun t : X ⟶ Y ↦ t ≫ (g ≫ inv (f ≫ g))) hf0
    exact hX (hfp.symm.trans hzero)
  · exact ⟨⟨g ≫ inv (f ≫ g), hfp, h1⟩⟩

variable {k : Type*} [Field k] [Linear k C]

/-- An object whose endomorphism space is one-dimensional has a nonzero identity, hence is not a
zero object. -/
theorem id_ne_zero_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    𝟙 X ≠ 0 := by
  have : Nontrivial (X ⟶ X) := Module.nontrivial_of_finrank_pos (R := k) (by rw [h]; exact one_pos)
  obtain ⟨f, g, hfg⟩ := exists_pair_ne (X ⟶ X)
  intro hid
  exact hfg (by rw [← Category.comp_id f, ← Category.comp_id g, hid, comp_zero, comp_zero])

/-- An object whose endomorphism space is one-dimensional is not a zero object. -/
theorem not_isZero_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    ¬ IsZero X := fun hX ↦
  id_ne_zero_of_finrank_end_eq_one h ((IsZero.iff_id_eq_zero X).mp hX)

/-- **A brick is indecomposable.** If the endomorphism space of `X` is one-dimensional over the
base field then the identity spans it, so every endomorphism is a scalar, the only idempotents are
`0` and the identity and `TauCeti.indecomposable_of_idempotent_eq_zero_or_id` applies. -/
theorem indecomposable_of_finrank_end_eq_one [HasBinaryBiproducts C] {X : C}
    (h : Module.finrank k (X ⟶ X) = 1) :
    Indecomposable X := by
  refine indecomposable_of_idempotent_eq_zero_or_id (not_isZero_of_finrank_end_eq_one h)
    fun e he ↦ ?_
  obtain ⟨c, rfl⟩ :=
    (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_ne_zero_of_finrank_end_eq_one h)).mp h e
  rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul] at he
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl (zero_smul k (𝟙 X))
  · refine Or.inr ?_
    -- Scaling the idempotent equation `(c * c) • 𝟙 X = c • 𝟙 X` by `c⁻¹` gives `c • 𝟙 X = 𝟙 X`.
    have := congrArg (fun f : X ⟶ X ↦ c⁻¹ • f) he
    simpa [smul_smul, ← mul_assoc, inv_mul_cancel₀ hc] using this

end TauCeti
