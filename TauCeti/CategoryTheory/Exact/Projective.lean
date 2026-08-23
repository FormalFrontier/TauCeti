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

Two theorems make relative projectives usable for resolutions, and both come from the same
pullback square. **Schanuel's lemma** says that two conflations `K ↪ Q ↠ X` and `K' ↪ Q' ↠ X`
with projective middle terms have stably isomorphic kernels, `K ⊞ Q' ≅ K' ⊞ Q`.

The main theorem is the **horseshoe lemma**. Given a conflation `X ↪ Y ↠ Z` and first steps
`K_X ↪ Q_X ↠ X` and `K_Z ↪ Q_Z ↠ Z` of resolutions of the two outer terms, with `Q_Z`
projective, there is a conflation

```text
K ↪ Q_X ⊞ Q_Z ↠ Y
```

whose middle term is the direct sum of the two resolving terms and whose kernel `K` is itself an
extension `K_X ↪ K ↠ K_Z` of the two syzygies. Iterating it resolves the middle term of a
conflation from resolutions of the outer terms, and that is the form in which the last result of
this file states it: for an object property `P` consisting of projectives, admitting a finite
`P`-resolution is closed under extensions, with no increase in length.

That closure property is what makes the objects of finite projective dimension an
extension-closed subcategory, so that
`TauCeti.ExactStructure.fullSubcategory` equips them with an induced exact structure — the
setting in which the resolution theorem compares their Grothendieck group with the one generated
by the projectives themselves.

## Main definitions

* `TauCeti.ExactStructure.projectives`: the object property of being projective relative to an
  exact structure, together with the lift `TauCeti.ExactStructure.projectives.factorThru` of a
  morphism along a deflation.
* `TauCeti.ExactStructure.splittingOfProjective`: the splitting of a conflation whose third term
  is projective.

## Main results

* `TauCeti.ExactStructure.projectives_split` and
  `TauCeti.ExactStructure.abelian_projectives_iff`: the two calibrating computations. Every
  object is projective for the split exact structure, and for the canonical exact structure of
  an abelian category the notion is Mathlib's `CategoryTheory.Projective`.
* `TauCeti.ExactStructure.nonempty_iso_biprod_of_projective`: **Schanuel's lemma**, that two
  conflations over the same object with projective middle terms have stably isomorphic kernels.
* `TauCeti.ExactStructure.exists_conflations_biprod_of_conflations`: **the horseshoe lemma**.
* `TauCeti.ExactStructure.exists_finiteResolution_length_le_of_conflation`: the middle term of a
  conflation admits a finite `P`-resolution of length at most the common bound on the lengths of
  resolutions of the two outer terms, when `P` consists of projectives.
* `TauCeti.ExactStructure.isExtensionClosed_admitsFiniteResolution`: admitting a finite
  `P`-resolution is closed under extensions.

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
projective, by `TauCeti.ExactStructure.projectives_split`; for the canonical exact structure of
an abelian category the notion is Mathlib's `CategoryTheory.Projective`, by
`TauCeti.ExactStructure.abelian_projectives_iff`. -/
def projectives (E : ExactStructure C) : ObjectProperty C := fun Q =>
  ∀ ⦃X Y : C⦄ {p : X ⟶ Y}, E.IsDeflation p → ∀ f : Q ⟶ Y, ∃ g : Q ⟶ X, g ≫ p = f

namespace projectives

/-- The chosen lift of `f : Q ⟶ Y` along a deflation `p : X ⟶ Y`, for `Q` projective. -/
noncomputable def factorThru {Q : C} (hQ : E.projectives Q) {X Y : C} {p : X ⟶ Y}
    (hp : E.IsDeflation p) (f : Q ⟶ Y) : Q ⟶ X :=
  (hQ hp f).choose

@[reassoc (attr := simp)]
theorem factorThru_comp {Q : C} (hQ : E.projectives Q) {X Y : C} {p : X ⟶ Y}
    (hp : E.IsDeflation p) (f : Q ⟶ Y) : hQ.factorThru hp f ≫ p = f :=
  (hQ hp f).choose_spec

end projectives

/-- Projectivity is invariant under isomorphism: transport the lift along the isomorphism. -/
instance : (E.projectives).IsClosedUnderIsomorphisms where
  of_iso e hQ _ _ _ hp f := ⟨e.inv ≫ hQ.factorThru hp (e.hom ≫ f), by simp⟩

/-- A zero object is projective: every morphism out of it is zero. -/
instance : (E.projectives).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by
    intro _ _ _ _ f
    exact ⟨0, (isZero_zero C).eq_of_src _ f⟩⟩

/-- A binary direct sum of projectives is projective: lift the two components separately. -/
theorem projectives_biprod {Q₁ Q₂ : C} (h₁ : E.projectives Q₁) (h₂ : E.projectives Q₂) :
    E.projectives (Q₁ ⊞ Q₂) := by
  intro X Y p hp f
  refine ⟨biprod.desc (h₁.factorThru hp (biprod.inl ≫ f)) (h₂.factorThru hp (biprod.inr ≫ f)),
    ?_⟩
  apply biprod.hom_ext' <;> simp

/-- The projectives are closed under binary products: in a preadditive category those are
biproducts. -/
instance : (E.projectives).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (E.projectives).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      (projectives_biprod (p.prop_diag_obj ⟨.left⟩) (p.prop_diag_obj ⟨.right⟩))

/-- **A conflation with projective third term splits.** The section of its deflation is the lift
of the identity of that term. -/
noncomputable def splittingOfProjective (E : ExactStructure C) {S : ShortComplex C}
    (hS : E.Conflation S) (h₃ : E.projectives S.X₃) : S.Splitting :=
  (E.isKernelCokernelPair S hS).splittingOfSection
    (h₃.factorThru (E.isDeflation_g hS) (𝟙 S.X₃)) (by simp)

/-- **Every object is projective for the split exact structure.** Its deflations are the
biproduct projections, along which every morphism visibly lifts. -/
@[simp]
theorem projectives_split (X : C) : (ExactStructure.split C).projectives X := by
  intro Y Z p hp f
  obtain ⟨W, e, he⟩ := (ExactStructure.split_isDeflation_iff p).mp hp
  exact ⟨f ≫ biprod.inr ≫ e.inv, by rw [Category.assoc, Category.assoc, he]; simp⟩

/-- **For the canonical exact structure of an abelian category, relative projectivity is
Mathlib's `CategoryTheory.Projective`.** The deflations there are exactly the epimorphisms. -/
@[simp]
theorem abelian_projectives_iff {A : Type u} [Category.{v} A] [Abelian A] (X : A) :
    (ExactStructure.abelian A).projectives X ↔ Projective X := by
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
    (hc : E.Conflation (ShortComplex.mk m a hm)) (hQ : E.projectives Q)
    {K' Q' : C} {m' : K' ⟶ Q'} {a' : Q' ⟶ X} {hm' : m' ≫ a' = 0}
    (hc' : E.Conflation (ShortComplex.mk m' a' hm')) (hQ' : E.projectives Q') :
    Nonempty ((K ⊞ Q' : C) ≅ (K' ⊞ Q : C)) := by
  have : HasPullback a a' := E.hasPullbacks_deflations.hasPullback a' (E.isDeflation_g hc)
  have sq : IsPullback (pullback.fst a a') (pullback.snd a a') a a' :=
    IsPullback.of_hasPullback _ _
  have h₁ : E.Conflation (ShortComplex.mk (baseChangeι (ShortComplex.mk m a hm) sq)
      (pullback.snd a a') (baseChangeι_snd (ShortComplex.mk m a hm) sq)) := by
    have h := E.conflation_baseChange hc sq
    rwa [baseChange_def] at h
  have h₂ : E.Conflation (ShortComplex.mk (baseChangeι (ShortComplex.mk m' a' hm') sq.flip)
      (pullback.fst a a') (baseChangeι_snd (ShortComplex.mk m' a' hm') sq.flip)) := by
    have h := E.conflation_baseChange hc' sq.flip
    rwa [baseChange_def] at h
  exact ⟨(E.splittingOfProjective h₁ hQ').isoBinaryBiproduct.symm.trans
    (E.splittingOfProjective h₂ hQ).isoBinaryBiproduct⟩

section Horseshoe

/-- **The horseshoe lemma.** Let `S : X ↪ Y ↠ Z` be a conflation and let
`K_X ↪ Q_X ↠ X` and `K_Z ↪ Q_Z ↠ Z` be conflations resolving its two outer terms, with `Q_Z`
projective. Then `Y` is the third term of a conflation whose middle term is `Q_X ⊞ Q_Z` and
whose first term is an extension of `K_Z` by `K_X`; moreover the new deflation restricts on the
first summand to `Q_X ↠ X ↪ Y`.

Iterating this is what lifts resolutions of `X` and of `Z` to a resolution of `Y`; see
`TauCeti.ExactStructure.exists_finiteResolution_length_le_of_conflation`. -/
theorem exists_conflations_biprod_of_conflations {S : ShortComplex C} (hS : E.Conflation S)
    {KX QX : C} {mX : KX ⟶ QX} {aX : QX ⟶ S.X₁} {hmX : mX ≫ aX = 0}
    (hcX : E.Conflation (ShortComplex.mk mX aX hmX))
    {KZ QZ : C} {mZ : KZ ⟶ QZ} {aZ : QZ ⟶ S.X₃} {hmZ : mZ ≫ aZ = 0}
    (hcZ : E.Conflation (ShortComplex.mk mZ aZ hmZ)) (hQZ : E.projectives QZ) :
    ∃ (K : C) (u : K ⟶ QX ⊞ QZ) (a : QX ⊞ QZ ⟶ S.X₂) (hu : u ≫ a = 0) (v : KX ⟶ K)
      (w : K ⟶ KZ) (hv : v ≫ w = 0),
      E.Conflation (ShortComplex.mk u a hu) ∧ E.Conflation (ShortComplex.mk v w hv) ∧
        biprod.inl ≫ a = aX ≫ S.f := by
  have hdZ : E.IsDeflation aZ := E.isDeflation_g hcZ
  have : HasPullback aZ S.g := E.hasPullbacks_deflations.hasPullback S.g hdZ
  have sq : IsPullback (pullback.fst aZ S.g) (pullback.snd aZ S.g) aZ S.g :=
    IsPullback.of_hasPullback _ _
  -- Pulling `S` back along `aZ` exhibits the pullback as an extension of `QZ` by `S.X₁` …
  have hspl : E.Conflation (ShortComplex.mk (baseChangeι S sq.flip) (pullback.fst aZ S.g)
      (baseChangeι_snd S sq.flip)) := by
    have h := E.conflation_baseChange hS sq.flip
    rwa [baseChange_def] at h
  -- … and pulling the resolving conflation of `Z` back along `S.g` exhibits the same pullback as
  -- an extension of `S.X₂` by `KZ`.
  have hker : E.Conflation (ShortComplex.mk (baseChangeι (ShortComplex.mk mZ aZ hmZ) sq)
      (pullback.snd aZ S.g) (baseChangeι_snd (ShortComplex.mk mZ aZ hmZ) sq)) := by
    have h := E.conflation_baseChange hcZ sq
    rwa [baseChange_def] at h
  -- Projectivity of `QZ` splits the first of these two conflations.
  have sp : (ShortComplex.mk (baseChangeι S sq.flip) (pullback.fst aZ S.g)
      (baseChangeι_snd S sq.flip)).Splitting := E.splittingOfProjective hspl hQZ
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
  obtain ⟨K, c, α, β, hcz, hβα, hK₁, hK₂, -, -⟩ := E.exists_conflation_comp' hker hc₁
  refine ⟨K, c, _, hcz, (isoBiprodZero (isZero_zero C)).hom ≫ β, α,
    by rw [Category.assoc, hβα, comp_zero], hK₁, ?_, by simp⟩
  refine E.conflation_of_iso ?_ hK₂
  exact ShortComplex.isoMk (isoBiprodZero (isZero_zero C)).symm (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.symm_hom, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]) (by simp)

end Horseshoe

section Resolutions

variable {P : ObjectProperty C}

/-- The first step of a finite `P`-resolution of length at most `n + 1`: a conflation
`K ↪ Q ↠ X` with `P Q`, whose subobject `K` still admits a finite `P`-resolution of length at
most `n`. A resolution of length zero contributes the trivial conflation `0 ↪ X ↠ X`. -/
theorem exists_conflation_of_exists_length_le_succ [P.IsClosedUnderIsomorphisms]
    [P.ContainsZero] {X : C} {n : ℕ} (h : ∃ r : E.FiniteResolution P X, r.length ≤ n + 1) :
    ∃ (K Q : C) (m : K ⟶ Q) (a : Q ⟶ X) (hm : m ≫ a = 0), P Q ∧
      E.Conflation (ShortComplex.mk m a hm) ∧ ∃ s : E.FiniteResolution P K, s.length ≤ n := by
  obtain ⟨r, hr⟩ := h
  cases r with
  | base hX =>
      exact ⟨0, X, 0, 𝟙 X, by simp, hX, E.conflation_zero_id X, .base P.prop_zero, by simp⟩
  | step hQ i p zero hp r =>
      exact ⟨_, _, i, p, zero, hQ, hp, r, by simpa using hr⟩

local instance [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨Z, hZ, hZP⟩ := P.exists_prop_of_containsZero
    let B : BinaryFan Z X := BinaryFan.mk (hZ.from_ Y) e.inv
    have hB : IsLimit B := BinaryFan.IsLimit.mk B (fun _ g => g ≫ e.hom)
      (fun _ _ => hZ.eq_of_tgt _ _)
      (fun _ _ => by simp [B])
      (fun _ _ _ _ hg => by simpa [B] using congrArg (fun k => k ≫ e.hom) hg)
    exact P.prop_of_isLimit_binaryFan hB hZP hX

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

/-- **Finite resolutions by projectives lift along a conflation.** If `P` consists of
`E`-projectives and both outer terms of a conflation admit a finite `P`-resolution of length at
most `n`, then so does its middle term.

This is the horseshoe lemma, iterated: at each stage the two resolving terms are added, and the
new syzygy is an extension of the two old ones. -/
theorem exists_finiteResolution_length_le_of_conflation (hP : P ≤ E.projectives) (n : ℕ)
    {S : ShortComplex C} (hS : E.Conflation S)
    (h₁ : ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n)
    (h₃ : ∃ t : E.FiniteResolution P S.X₃, t.length ≤ n) :
    ∃ u : E.FiniteResolution P S.X₂, u.length ≤ n := by
  induction n generalizing S with
  | zero =>
      obtain ⟨r, hr⟩ := h₁
      obtain ⟨t, ht⟩ := h₃
      have hX₁ : P S.X₁ := by
        cases r with
        | base hX => exact hX
        | step _ _ _ _ _ _ => simp at hr
      have hX₃ : P S.X₃ := by
        cases t with
        | base hZ => exact hZ
        | step _ _ _ _ _ _ => simp at ht
      refine ⟨.base (P.prop_of_iso (E.splittingOfProjective hS (hP _ hX₃)).isoBinaryBiproduct.symm
        (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hX₁ hX₃)), by simp⟩
  | succ n ih =>
      obtain ⟨KX, QX, mX, aX, hmX, hQX, hcX, hKX⟩ :=
        exists_conflation_of_exists_length_le_succ h₁
      obtain ⟨KZ, QZ, mZ, aZ, hmZ, hQZ, hcZ, hKZ⟩ :=
        exists_conflation_of_exists_length_le_succ h₃
      obtain ⟨K, u, a, hu, v, w, hv, hKu, hKv, -⟩ :=
        E.exists_conflations_biprod_of_conflations hS hcX hcZ (hP _ hQZ)
      obtain ⟨s, hs⟩ := ih (S := ShortComplex.mk v w hv) hKv hKX hKZ
      have hQ : P (QX ⊞ QZ) :=
        P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hQX hQZ
      exact ⟨.step hQ u a hu hKu s,
        by rw [FiniteResolution.length_step]; exact Nat.succ_le_succ hs⟩

/-- The middle term of a conflation admits a finite `P`-resolution as soon as its two outer terms
do, provided `P` consists of `E`-projectives. -/
theorem admitsFiniteResolution_X₂_of_conflation (hP : P ≤ E.projectives) {S : ShortComplex C}
    (hS : E.Conflation S) (h₁ : E.admitsFiniteResolution P S.X₁)
    (h₃ : E.admitsFiniteResolution P S.X₃) : E.admitsFiniteResolution P S.X₂ := by
  rw [admitsFiniteResolution_iff] at h₁ h₃ ⊢
  obtain ⟨r⟩ := h₁
  obtain ⟨t⟩ := h₃
  obtain ⟨u, -⟩ := exists_finiteResolution_length_le_of_conflation hP
    (max r.length t.length) hS ⟨r, le_max_left _ _⟩ ⟨t, le_max_right _ _⟩
  exact ⟨u⟩

/-- **The objects of finite `P`-dimension are extension closed**, for an object property `P`
consisting of `E`-projectives.

Together with `TauCeti.ExactStructure.fullSubcategory` this equips them with an induced exact
structure, in which the resolution theorem compares their Grothendieck group with the one
generated by the objects satisfying `P`. -/
theorem isExtensionClosed_admitsFiniteResolution (hP : P ≤ E.projectives) :
    E.IsExtensionClosed (E.admitsFiniteResolution P) :=
  ⟨fun hS h₁ h₃ => admitsFiniteResolution_X₂_of_conflation hP hS h₁ h₃⟩

end Resolutions

end ExactStructure

end TauCeti
