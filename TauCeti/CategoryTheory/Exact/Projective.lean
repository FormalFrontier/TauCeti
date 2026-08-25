/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Resolution

/-!
# Relative projectives in an exact category, and the horseshoe lemma

Let `E` be a Quillen exact structure on an additive category `C`. An object `Q` is
*`E`-projective* when every morphism out of `Q` lifts along every deflation of `E`. This is the
relative notion Bühler uses: it depends on the exact structure, not just on the category. For
the split exact structure every object is projective, and for the canonical exact structure of
an abelian category it is Mathlib's `CategoryTheory.Projective`.

Two theorems make relative projectives usable for resolutions, and both are proved by the same
method — pull a conflation back along a deflation, then split the resulting conflation because
its third term is projective — although each builds its own pullback square. **Schanuel's
lemma** says that two conflations `K ↪ Q ↠ X` and `K' ↪ Q' ↠ X` with projective middle terms
have stably isomorphic kernels, `K ⊞ Q' ≅ K' ⊞ Q`.

The main theorem is the **horseshoe lemma**. Given a conflation `X ↪ Y ↠ Z` and first steps
`K_X ↪ Q_X ↠ X` and `K_Z ↪ Q_Z ↠ Z` of resolutions of the two outer terms, with `Q_Z`
projective, there is a conflation

```text
K ↪ Q_X ⊞ Q_Z ↠ Y
```

whose middle term is the direct sum of the two resolving terms and whose kernel `K` is itself an
extension `K_X ↪ K ↠ K_Z` of the two syzygies, compatibly with the two given conflations.
Iterating it resolves the middle term of a conflation from resolutions of the outer terms, and
that is the form in which the last result of this file states it: for an object property `P`
consisting of projectives, containing a zero object and closed under binary biproducts, admitting
a finite `P`-resolution is closed under extensions, with no increase in length.

That closure property is what makes the objects of finite projective dimension an
extension-closed subcategory, so that
`TauCeti.ExactStructure.fullSubcategory` equips them with an induced exact structure — the
setting in which the resolution theorem compares their Grothendieck group with the one generated
by the projectives themselves.

## Main definitions

* `TauCeti.ExactStructure.isProjective`: the object property of being projective relative to an
  exact structure, together with the lift `TauCeti.ExactStructure.isProjective.factorThru` of a
  morphism along a deflation.
* `TauCeti.ExactStructure.splittingOfProjective`: the splitting of a conflation whose third term
  is projective.

## Main results

* `TauCeti.ExactStructure.split_isProjective` and
  `TauCeti.ExactStructure.abelian_isProjective_iff`: the two calibrating computations. Every
  object is projective for the split exact structure, and for the canonical exact structure of
  an abelian category the notion is Mathlib's `CategoryTheory.Projective`.
* `TauCeti.ExactStructure.nonempty_iso_biprod_of_projective`: **Schanuel's lemma**, that two
  conflations over the same object with projective middle terms have stably isomorphic kernels.
* `TauCeti.ExactStructure.exists_conflation_biprod_of_conflation_of_projective`: **the horseshoe
  lemma**.
* `TauCeti.ExactStructure.exists_finiteResolution_length_le_of_conflation`: the middle term of a
  conflation admits a finite `P`-resolution of length at most the common bound on the lengths of
  resolutions of the two outer terms, when `P` consists of projectives, contains a zero object
  and is closed under binary biproducts.
* `TauCeti.ExactStructure.isExtensionClosed_admitsFiniteResolution`: under those same hypotheses
  on `P`, admitting a finite `P`-resolution is closed under extensions.
* `TauCeti.ExactStructure.isExtensionClosed_of_le_isProjective` and
  `TauCeti.ExactStructure.fullSubcategory_eq_split`: a property consisting of projectives is
  itself extension closed, and the exact structure it inherits is the split one.

## Implementation notes

The horseshoe is proved without ever choosing a lift of `Q_Z` into `Y` by hand. Pulling the
conflation `X ↪ Y ↠ Z` back along the deflation `Q_Z ↠ Z` gives a conflation `X ↪ W ↠ Q_Z`,
which splits because `Q_Z` is projective, while pulling the conflation `K_Z ↪ Q_Z ↠ Z` back
along `Y ↠ Z` exhibits the *same* object `W` as an extension of `Y` by `K_Z`. Composing the
resulting deflation `W ↠ Y` with the direct sum `Q_X ⊞ Q_Z ↠ X ⊞ Q_Z ≅ W` and applying the dual
Noether package `TauCeti.ExactStructure.exists_conflation_comp'` produces the conflation and
identifies its kernel in one step.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>. Sections 11–12 develop projective objects and resolutions
  in a Quillen exact category, of which Schanuel's lemma and the horseshoe lemma proved here are
  the two basic constructions.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  where finite resolutions and the resolution theorem consume this closure property.
* `Mathlib/CategoryTheory/Preadditive/Projective/Basic.lean`, whose `factorThru`,
  `factorThru_comp` and isomorphism, zero-object and biproduct closure API for absolute
  projectivity is the layout adapted here to the relative setting, and
  `Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean`, whose
  `CategoryTheory.ShortComplex.ShortExact.splittingOfProjective` is the balanced-category
  ancestor of `TauCeti.ExactStructure.splittingOfProjective`.
* [The Tau Ceti Grothendieck groups, Cartan maps, and Euler forms roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/GrothendieckEulerForms/README.md),
  Layer 3, whose projective-resolution calculus requires the horseshoe lemma and whose subsequent
  finite-resolution applications require the resulting extension-closed object property.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

/-- The objects that are **projective relative to the exact structure `E`**: those `Q` for which
every morphism out of `Q` factors through every deflation of `E`.

This depends on `E` and not only on `C`. For the split exact structure every object is
projective, by `TauCeti.ExactStructure.split_isProjective`; for the canonical exact structure of
an abelian category the notion is Mathlib's `CategoryTheory.Projective`, by
`TauCeti.ExactStructure.abelian_isProjective_iff`. -/
def isProjective (E : ExactStructure C) : ObjectProperty C := fun Q =>
  ∀ ⦃X Y : C⦄ {p : X ⟶ Y}, E.IsDeflation p → ∀ f : Q ⟶ Y, ∃ g : Q ⟶ X, g ≫ p = f

/-- The defining lifting property, as the characterisation of
`TauCeti.ExactStructure.isProjective` available to code that cannot unfold its body. -/
theorem isProjective_iff {Q : C} :
    E.isProjective Q ↔
      ∀ ⦃X Y : C⦄ {p : X ⟶ Y}, E.IsDeflation p → ∀ f : Q ⟶ Y, ∃ g : Q ⟶ X, g ≫ p = f :=
  Iff.rfl

namespace isProjective

/-- The chosen lift of `f : Q ⟶ Y` along a deflation `p : X ⟶ Y`, for `Q` projective. -/
noncomputable def factorThru {Q : C} (hQ : E.isProjective Q) {X Y : C} {p : X ⟶ Y}
    (hp : E.IsDeflation p) (f : Q ⟶ Y) : Q ⟶ X :=
  (hQ hp f).choose

@[reassoc (attr := simp)]
theorem factorThru_comp {Q : C} (hQ : E.isProjective Q) {X Y : C} {p : X ⟶ Y}
    (hp : E.IsDeflation p) (f : Q ⟶ Y) : hQ.factorThru hp f ≫ p = f :=
  (hQ hp f).choose_spec

end isProjective

/-- Projectivity is invariant under isomorphism: transport the lift along the isomorphism. -/
instance : (E.isProjective).IsClosedUnderIsomorphisms where
  of_iso e hQ _ _ _ hp f := ⟨e.inv ≫ hQ.factorThru hp (e.hom ≫ f), by simp⟩

/-- A zero object is projective: every morphism out of it is zero. -/
instance : (E.isProjective).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by
    intro _ _ _ _ f
    exact ⟨0, (isZero_zero C).eq_of_src _ f⟩⟩

/-- A binary direct sum of projectives is projective: lift the two components separately. -/
theorem isProjective_biprod {Q₁ Q₂ : C} (h₁ : E.isProjective Q₁) (h₂ : E.isProjective Q₂) :
    E.isProjective (Q₁ ⊞ Q₂) := by
  intro X Y p hp f
  refine ⟨biprod.desc (h₁.factorThru hp (biprod.inl ≫ f)) (h₂.factorThru hp (biprod.inr ≫ f)),
    ?_⟩
  apply biprod.hom_ext' <;> simp

/-- The projectives are closed under binary products: in a preadditive category those are
biproducts. -/
instance : (E.isProjective).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod (E.isProjective)
    fun _ _ h₁ h₂ => isProjective_biprod h₁ h₂

/-- **A conflation with projective third term splits.** The section of its deflation is the lift
of the identity of that term.

This is the exact-structure analogue of Mathlib's
`CategoryTheory.ShortComplex.ShortExact.splittingOfProjective`, with the balancedness hypothesis
on the ambient category replaced by the kernel–cokernel pair carried by a conflation. -/
noncomputable def splittingOfProjective (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₃ : E.isProjective S.X₃) : S.Splitting :=
  (E.isKernelCokernelPair S hS).splittingOfSection
    (h₃.factorThru (E.isDeflation_g hS) (𝟙 S.X₃)) (by simp)

@[simp] theorem splittingOfProjective_s (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₃ : E.isProjective S.X₃) :
    (E.splittingOfProjective hS h₃).s = h₃.factorThru (E.isDeflation_g hS) (𝟙 S.X₃) :=
  (E.isKernelCokernelPair S hS).splittingOfSection_s _ _

@[simp] theorem splittingOfProjective_r (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₃ : E.isProjective S.X₃) :
    (E.splittingOfProjective hS h₃).r = (E.isKernelCokernelPair S hS).lift
      (𝟙 S.X₂ - S.g ≫ h₃.factorThru (E.isDeflation_g hS) (𝟙 S.X₃)) (by simp) :=
  (E.isKernelCokernelPair S hS).splittingOfSection_r _ _

/-- **Every object is projective for the split exact structure.** Its deflations are split
epimorphisms, along which every morphism visibly lifts. -/
@[simp]
theorem split_isProjective (X : C) : (ExactStructure.split C).isProjective X := by
  intro Y Z p hp f
  have := isSplitEpi_of_split_isDeflation hp
  exact ⟨f ≫ section_ p, by simp⟩

/-- **For the canonical exact structure of an abelian category, relative projectivity is
Mathlib's `CategoryTheory.Projective`.** The deflations there are exactly the epimorphisms. -/
@[simp]
theorem abelian_isProjective_iff {A : Type u} [Category.{v} A] [Abelian A] (X : A) :
    (ExactStructure.abelian A).isProjective X ↔ Projective X := by
  constructor
  · exact fun h => ⟨fun f e he => h ((abelian_isDeflation_iff e).mpr he) f⟩
  · intro h Y Z p hp f
    have : Epi p := (abelian_isDeflation_iff p).mp hp
    exact h.factors f p

/-- **Schanuel's lemma.** Two conflations `K ↪ Q ↠ X` and `K' ↪ Q' ↠ X` with projective middle
terms have stably isomorphic kernels: `K ⊞ Q' ≅ K' ⊞ Q`.

Both isomorphisms come from the pullback `Q ×_X Q'`, which base change exhibits at once as an
extension of `Q'` by `K` and as an extension of `Q` by `K'`; projectivity splits both. -/
theorem nonempty_iso_biprod_of_projective {X K Q : C} {m : K ⟶ Q} {a : Q ⟶ X} {hm : m ≫ a = 0}
    (hc : E.Conflation (ShortComplex.mk m a hm)) (hQ : E.isProjective Q)
    {K' Q' : C} {m' : K' ⟶ Q'} {a' : Q' ⟶ X} {hm' : m' ≫ a' = 0}
    (hc' : E.Conflation (ShortComplex.mk m' a' hm')) (hQ' : E.isProjective Q') :
    Nonempty ((K ⊞ Q' : C) ≅ (K' ⊞ Q : C)) := by
  have : HasPullback a a' := E.hasPullbacks_deflations.hasPullback a' (E.isDeflation_g hc)
  have sq : IsPullback (pullback.fst a a') (pullback.snd a a') a a' :=
    IsPullback.of_hasPullback _ _
  -- the pullback as an extension of `Q'` by `K`, and as an extension of `Q` by `K'`
  have h₁ := E.conflation_baseChange hc sq
  rw [baseChange_def] at h₁
  have h₂ := E.conflation_baseChange hc' sq.flip
  rw [baseChange_def] at h₂
  exact ⟨(E.splittingOfProjective h₁ hQ').isoBinaryBiproduct.symm.trans
    (E.splittingOfProjective h₂ hQ).isoBinaryBiproduct⟩

section Horseshoe

/-- **The horseshoe lemma.** Let `S : X ↪ Y ↠ Z` be a conflation and let
`K_X ↪ Q_X ↠ X` and `K_Z ↪ Q_Z ↠ Z` be conflations resolving its two outer terms, with `Q_Z`
projective. Then `Y` is the third term of a conflation whose middle term is `Q_X ⊞ Q_Z` and
whose first term is an extension of `K_Z` by `K_X`.

The two conflations form a horseshoe over the given one: the new deflation `a` restricts on the
first summand to `Q_X ↠ X ↪ Y` and covers `Q_Z ↠ Z` on the second, while the new inflation `u`
restricts on `K_X` to `K_X ↪ Q_X ↪ Q_X ⊞ Q_Z` and covers `K_Z ↪ Q_Z` on the second summand.

Iterating this is what lifts resolutions of `X` and of `Z` to a resolution of `Y`; see
`TauCeti.ExactStructure.exists_finiteResolution_length_le_of_conflation`. -/
theorem exists_conflation_biprod_of_conflation_of_projective {S : ShortComplex C}
    (hS : E.Conflation S) {KX QX : C} {mX : KX ⟶ QX} {aX : QX ⟶ S.X₁} {hmX : mX ≫ aX = 0}
    (hcX : E.Conflation (ShortComplex.mk mX aX hmX))
    {KZ QZ : C} {mZ : KZ ⟶ QZ} {aZ : QZ ⟶ S.X₃} {hmZ : mZ ≫ aZ = 0}
    (hcZ : E.Conflation (ShortComplex.mk mZ aZ hmZ)) (hQZ : E.isProjective QZ) :
    ∃ (K : C) (u : K ⟶ QX ⊞ QZ) (a : QX ⊞ QZ ⟶ S.X₂) (hu : u ≫ a = 0) (v : KX ⟶ K)
      (w : K ⟶ KZ) (hv : v ≫ w = 0),
      E.Conflation (ShortComplex.mk u a hu) ∧ E.Conflation (ShortComplex.mk v w hv) ∧
        biprod.inl ≫ a = aX ≫ S.f ∧ a ≫ S.g = biprod.snd ≫ aZ ∧
        v ≫ u = mX ≫ biprod.inl ∧ u ≫ biprod.snd = w ≫ mZ := by
  have hdZ : E.IsDeflation aZ := E.isDeflation_g hcZ
  have : HasPullback aZ S.g := E.hasPullbacks_deflations.hasPullback S.g hdZ
  have sq : IsPullback (pullback.fst aZ S.g) (pullback.snd aZ S.g) aZ S.g :=
    IsPullback.of_hasPullback _ _
  -- Pulling `S` back along `aZ` exhibits the pullback as an extension of `QZ` by `S.X₁` …
  have hspl := E.conflation_baseChange hS sq.flip
  rw [baseChange_def] at hspl
  -- … and pulling the resolving conflation of `Z` back along `S.g` exhibits the same pullback as
  -- an extension of `S.X₂` by `KZ`.
  have hker := E.conflation_baseChange hcZ sq
  rw [baseChange_def] at hker
  -- Projectivity of `QZ` splits the first of these two conflations, and under that splitting the
  -- deflation of the pullback onto `QZ` is the second projection.
  have sp : (ShortComplex.mk (baseChangeι S sq.flip) (pullback.fst aZ S.g)
      (baseChangeι_snd S sq.flip)).Splitting := E.splittingOfProjective hspl hQZ
  have hinv : sp.isoBinaryBiproduct.inv ≫ pullback.fst aZ S.g = biprod.snd := by
    apply biprod.hom_ext' <;> simp [sp.s_g]
  -- the direct sum of the resolving conflation of `X` with the trivial conflation on `QZ`
  have hbipzero : biprod.map mX (0 : (0 : C) ⟶ QZ) ≫ biprod.map aX (𝟙 QZ) = 0 := by
    apply biprod.hom_ext' <;> simp [reassoc_of% hmX]
  have hbip : E.Conflation (ShortComplex.mk (biprod.map mX (0 : (0 : C) ⟶ QZ))
      (biprod.map aX (𝟙 QZ)) hbipzero) :=
    E.conflation_biprod hcX (E.conflation_zero_id QZ)
  have hzero : biprod.map mX (0 : (0 : C) ⟶ QZ) ≫
      (biprod.map aX (𝟙 QZ) ≫ sp.isoBinaryBiproduct.inv) = 0 := by
    rw [← Category.assoc, hbipzero, zero_comp]
  have hc₁ : E.Conflation (ShortComplex.mk (biprod.map mX (0 : (0 : C) ⟶ QZ))
      (biprod.map aX (𝟙 QZ) ≫ sp.isoBinaryBiproduct.inv) hzero) := by
    refine E.conflation_of_iso ?_ hbip
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) sp.isoBinaryBiproduct.symm
      (by simp) (by simp)
  obtain ⟨K, c, α, β, hcz, hβα, hK₁, hK₂, hcq, hβc⟩ := E.exists_conflation_comp' hker hc₁
  refine ⟨K, c, _, hcz, (isoBiprodZero (isZero_zero C)).hom ≫ β, α,
    by rw [Category.assoc, hβα, comp_zero], hK₁, ?_, by simp, ?_, ?_, ?_⟩
  · -- the syzygy conflation, after discarding the zero summand of its first term
    refine E.conflation_of_iso ?_ hK₂
    exact ShortComplex.isoMk (isoBiprodZero (isZero_zero C)).symm (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.symm_hom, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]) (by simp)
  · -- the new deflation covers `aZ` on the second summand
    simp only [Category.assoc]
    rw [← sq.w, ← Category.assoc sp.isoBinaryBiproduct.inv, hinv]
    simp
  · -- the new inflation restricts to `mX` on `KX`
    rw [Category.assoc, hβc]
    apply biprod.hom_ext <;> simp
  · -- and covers `mZ` on the second summand
    have h := hcq =≫ pullback.fst aZ S.g
    simp only [Category.assoc] at h
    rw [hinv] at h
    simpa using h

end Horseshoe

section Resolutions

variable {P : ObjectProperty C}

/-- **A property consisting of projectives is extension closed**, as soon as it is replete and
closed under binary biproducts: a conflation whose third term is projective splits, so its middle
term is the biproduct of the two outer ones.

Together with `TauCeti.ExactStructure.fullSubcategory` this equips the objects satisfying `P`
with an induced exact structure — necessarily the split one, by
`TauCeti.ExactStructure.fullSubcategory_eq_split`. -/
theorem isExtensionClosed_of_le_isProjective [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderBinaryProducts] (hP : P ≤ E.isProjective) : E.IsExtensionClosed P where
  prop_X₂ hS h₁ h₃ :=
    P.prop_of_iso (E.splittingOfProjective hS (hP _ h₃)).isoBinaryBiproduct.symm
      (P.prop_biprod_of_isClosedUnderBinaryProducts h₁ h₃)

/-- A property containing a zero object and closed under binary products is automatically
replete, by `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero`; so the
results below need no separate repleteness hypothesis, even though the resolution API they call
does. -/
local instance [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

/-- **The exact structure induced on a subcategory of projectives is the split one.** -/
theorem fullSubcategory_eq_split (hP : P ≤ E.isProjective) :
    E.fullSubcategory P (E.isExtensionClosed_of_le_isProjective hP) =
      ExactStructure.split P.FullSubcategory := by
  apply ExactStructure.ext
  intro S
  refine ⟨fun hS => ?_, fun hS => ExactStructure.conflation_of_split_conflation _ hS⟩
  rw [fullSubcategory_conflation_iff] at hS
  have hs := E.splittingOfProjective hS (hP _ S.X₃.property)
  exact (ExactStructure.split_conflation S).mpr ⟨{
    r := ObjectProperty.homMk hs.r
    s := ObjectProperty.homMk hs.s
    f_r := ObjectProperty.hom_ext _ hs.f_r
    s_g := ObjectProperty.hom_ext _ hs.s_g
    id := ObjectProperty.hom_ext _ hs.id }⟩

/-- **Finite resolutions by projectives lift along a conflation.** If `P` consists of
`E`-projectives, contains a zero object and is closed under binary biproducts, and both outer
terms of a conflation admit a finite `P`-resolution of length at most `n`, then so does its
middle term.

This is the horseshoe lemma, iterated: at each stage the two resolving terms are added, and the
new syzygy is an extension of the two old ones. -/
theorem exists_finiteResolution_length_le_of_conflation (hP : P ≤ E.isProjective) (n : ℕ)
    {S : ShortComplex C} (hS : E.Conflation S)
    (h₁ : ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n)
    (h₃ : ∃ t : E.FiniteResolution P S.X₃, t.length ≤ n) :
    ∃ u : E.FiniteResolution P S.X₂, u.length ≤ n := by
  induction n generalizing S with
  | zero =>
      obtain ⟨r, hr⟩ := h₁
      obtain ⟨t, ht⟩ := h₃
      have hX₁ : P S.X₁ := by simpa using r.prop_syzygy hr
      have hX₃ : P S.X₃ := by simpa using t.prop_syzygy ht
      refine ⟨.base ((E.isExtensionClosed_of_le_isProjective hP).prop_X₂ hS hX₁ hX₃), by simp⟩
  | succ n ih =>
      obtain ⟨KX, QX, mX, aX, hmX, hQX, hcX, hKX⟩ :=
        E.exists_conflation_of_exists_finiteResolution_length_le_succ h₁
      obtain ⟨KZ, QZ, mZ, aZ, hmZ, hQZ, hcZ, hKZ⟩ :=
        E.exists_conflation_of_exists_finiteResolution_length_le_succ h₃
      obtain ⟨K, u, a, hu, v, w, hv, hKu, hKv, -, -, -, -⟩ :=
        E.exists_conflation_biprod_of_conflation_of_projective hS hcX hcZ (hP _ hQZ)
      obtain ⟨s, hs⟩ := ih (S := ShortComplex.mk v w hv) hKv hKX hKZ
      have hQ : P (QX ⊞ QZ) :=
        P.prop_biprod_of_isClosedUnderBinaryProducts hQX hQZ
      exact ⟨.step hQ u a hu hKu s,
        by rw [FiniteResolution.length_step]; exact Nat.succ_le_succ hs⟩

/-- **The objects of finite `P`-dimension are extension closed**, for an object property `P`
consisting of `E`-projectives which contains a zero object and is closed under binary
biproducts. The middle term of a conflation is covered by
`TauCeti.ExactStructure.IsExtensionClosed.prop_X₂`.

Together with `TauCeti.ExactStructure.fullSubcategory` this equips them with an induced exact
structure, in which the resolution theorem compares their Grothendieck group with the one
generated by the objects satisfying `P`. -/
theorem isExtensionClosed_admitsFiniteResolution (hP : P ≤ E.isProjective) :
    E.IsExtensionClosed (E.admitsFiniteResolution P) := by
  refine ⟨fun {S} hS h₁ h₃ => ?_⟩
  rw [admitsFiniteResolution_iff] at h₁ h₃ ⊢
  obtain ⟨r⟩ := h₁
  obtain ⟨t⟩ := h₃
  obtain ⟨u, -⟩ := exists_finiteResolution_length_le_of_conflation hP
    (max r.length t.length) hS ⟨r, le_max_left _ _⟩ ⟨t, le_max_right _ _⟩
  exact ⟨u⟩

end Resolutions

end ExactStructure

end TauCeti
