/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExactStructure

/-!
# Conflations along admissible base change, and the Noether conflation

Quillen's axiom E2 produces a pushout of an inflation along an arbitrary morphism and asserts
only that the resulting morphism is again an inflation. This file identifies the *cokernel* of
that inflation: cobase change of a conflation `X ⟶ Y ⟶ Z` along `u : X ⟶ X'` produces a
conflation `X' ⟶ Q ⟶ Z` with the *same* third term. Dually, base change of a conflation along
`u : Z' ⟶ Z` produces a conflation `X ⟶ Q ⟶ Z'` with the same first term.

The second half of the file uses this to describe the conflations attached to a composite of two
inflations. If `X ⟶ Y ⟶ Z` and `Y ⟶ W ⟶ V` are conflations, then the pushout `Q` of the
inflation `Y ⟶ W` along the deflation `Y ⟶ Z` is at once the third term of a conflation
`X ⟶ W ⟶ Q` and the second term of a conflation `Z ⟶ Q ⟶ V`. This is the exact-category form of
Noether's second isomorphism theorem, `Q ≅ W/X` with `(W/X)/(Y/X) ≅ W/Y`, and it is what makes
extension-closed subcategories inherit axiom E1.

## Main definitions

* `TauCeti.cobaseChange`: the conflation `X' ⟶ Q ⟶ Z` obtained from `S : X ⟶ Y ⟶ Z` and a
  pushout square along `u : X ⟶ X'`.
* `TauCeti.baseChange`: the conflation `X ⟶ Q ⟶ Z'` obtained from `S : X ⟶ Y ⟶ Z` and a pullback
  square along `u : Z' ⟶ Z`.

## Main results

* `TauCeti.ExactStructure.conflation_cobaseChange` and
  `TauCeti.ExactStructure.conflation_baseChange`: base and cobase change of a conflation along an
  arbitrary morphism is a conflation; the inflation or deflation in the original conflation is
  the admissible morphism being pushed out or pulled back.
* `TauCeti.ExactStructure.conflation_comp_of_isPushout` and
  `TauCeti.ExactStructure.conflation_comp_of_isPullback`: the cokernel of a composite of
  inflations, and the kernel of a composite of deflations, computed as a pushout resp. pullback.
* `TauCeti.ExactStructure.exists_conflation_comp`: the Noether package for a composite of two
  inflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>. Proposition 2.12 identifies the cokernel along a cobase
  change and Lemma 3.5 is the Noether isomorphism proved here.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section CobaseChange

variable (S : ShortComplex C) {X' Q : C} {u : S.X₁ ⟶ X'} {v : S.X₂ ⟶ Q} {w : X' ⟶ Q}

/-- The morphism `Q ⟶ S.X₃` out of a cobase change of `S.f` along `u`, induced by `S.g` on the
one summand and by `0` on the other. -/
noncomputable def cobaseChangeπ (sq : IsPushout S.f u v w) : Q ⟶ S.X₃ :=
  sq.desc S.g 0 (by simp [S.zero])

@[reassoc (attr := simp)]
theorem inl_cobaseChangeπ (sq : IsPushout S.f u v w) : v ≫ cobaseChangeπ S sq = S.g :=
  sq.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_cobaseChangeπ (sq : IsPushout S.f u v w) : w ≫ cobaseChangeπ S sq = 0 :=
  sq.inr_desc _ _ _

/-- The cobase change of a short complex `S` along `u : S.X₁ ⟶ X'`: the short complex
`X' ⟶ Q ⟶ S.X₃` attached to a pushout square of `S.f` along `u`. -/
noncomputable def cobaseChange (sq : IsPushout S.f u v w) : ShortComplex C :=
  ShortComplex.mk w (cobaseChangeπ S sq) (by simp)

/-- The defining equation for `cobaseChange`. -/
theorem cobaseChange_def (sq : IsPushout S.f u v w) :
    cobaseChange S sq = ShortComplex.mk w (cobaseChangeπ S sq) (by simp) := (rfl)

@[simp] theorem cobaseChange_X₁ (sq : IsPushout S.f u v w) : (cobaseChange S sq).X₁ = X' := (rfl)
@[simp] theorem cobaseChange_X₂ (sq : IsPushout S.f u v w) : (cobaseChange S sq).X₂ = Q := (rfl)
@[simp] theorem cobaseChange_X₃ (sq : IsPushout S.f u v w) : (cobaseChange S sq).X₃ = S.X₃ := (rfl)
@[simp] theorem cobaseChange_f (sq : IsPushout S.f u v w) : HEq (cobaseChange S sq).f w :=
  (HEq.rfl)

@[simp] theorem cobaseChange_g (sq : IsPushout S.f u v w) :
    HEq (cobaseChange S sq).g (cobaseChangeπ S sq) := (HEq.rfl)

end CobaseChange

section BaseChange

variable (S : ShortComplex C) {Z' Q : C} {u : Z' ⟶ S.X₃} {v : Q ⟶ S.X₂} {w : Q ⟶ Z'}

/-- The morphism `S.X₁ ⟶ Q` into a base change of `S.g` along `u`, induced by `S.f` on the one
factor and by `0` on the other. -/
noncomputable def baseChangeι (sq : IsPullback v w S.g u) : S.X₁ ⟶ Q :=
  sq.lift S.f 0 (by simp [S.zero])

@[reassoc (attr := simp)]
theorem baseChangeι_fst (sq : IsPullback v w S.g u) : baseChangeι S sq ≫ v = S.f :=
  sq.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeι_snd (sq : IsPullback v w S.g u) : baseChangeι S sq ≫ w = 0 :=
  sq.lift_snd _ _ _

/-- The base change of a short complex `S` along `u : Z' ⟶ S.X₃`: the short complex
`S.X₁ ⟶ Q ⟶ Z'` attached to a pullback square of `S.g` along `u`. -/
noncomputable def baseChange (sq : IsPullback v w S.g u) : ShortComplex C :=
  ShortComplex.mk (baseChangeι S sq) w (by simp)

/-- The defining equation for `baseChange`. -/
theorem baseChange_def (sq : IsPullback v w S.g u) :
    baseChange S sq = ShortComplex.mk (baseChangeι S sq) w (by simp) := (rfl)

@[simp] theorem baseChange_X₁ (sq : IsPullback v w S.g u) : (baseChange S sq).X₁ = S.X₁ := (rfl)
@[simp] theorem baseChange_X₂ (sq : IsPullback v w S.g u) : (baseChange S sq).X₂ = Q := (rfl)
@[simp] theorem baseChange_X₃ (sq : IsPullback v w S.g u) : (baseChange S sq).X₃ = Z' := (rfl)
@[simp] theorem baseChange_g (sq : IsPullback v w S.g u) : HEq (baseChange S sq).g w :=
  (HEq.rfl)

@[simp] theorem baseChange_f (sq : IsPullback v w S.g u) :
    HEq (baseChange S sq).f (baseChangeι S sq) := (HEq.rfl)

end BaseChange

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C] (E : ExactStructure C)

/-- **Cobase change of a conflation is a conflation with the same cokernel.** The pushout of a
conflation `X ⟶ Y ⟶ Z` along a morphism `u : X ⟶ X'` is a conflation `X' ⟶ Q ⟶ Z`.

Axiom E2 alone gives only that `X' ⟶ Q` is an inflation; the content here is that its cokernel
may be taken to be the original `Z`. -/
theorem conflation_cobaseChange {S : ShortComplex C} (hS : E.Conflation S) {X' Q : C}
    {u : S.X₁ ⟶ X'} {v : S.X₂ ⟶ Q} {w : X' ⟶ Q} (sq : IsPushout S.f u v w) :
    E.Conflation (cobaseChange S sq) := by
  have hpair : IsKernelCokernelPair S := E.isKernelCokernelPair S hS
  have hw : E.IsInflation w :=
    E.isStableUnderCobaseChange_inflations.of_isPushout sq.flip (E.isInflation_f hS)
  have hepi : Epi (cobaseChangeπ S sq) := by
    have := hpair.epi_g
    have h : Epi (v ≫ cobaseChangeπ S sq) := by rw [inl_cobaseChangeπ]; assumption
    exact epi_of_epi v (cobaseChangeπ S sq)
  have key : ∀ (A : C) (k : Q ⟶ A), w ≫ k = 0 →
      ∃ l : S.X₃ ⟶ A, cobaseChangeπ S sq ≫ l = k := fun A k hk => by
    refine ⟨hpair.desc (v ≫ k) ?_, ?_⟩
    · rw [← Category.assoc, sq.w, Category.assoc, hk, comp_zero]
    · refine sq.hom_ext ?_ ?_
      · rw [← Category.assoc, inl_cobaseChangeπ, hpair.g_desc]
      · rw [← Category.assoc, inr_cobaseChangeπ, zero_comp, hk]
  refine E.conflation_of_isColimit_of_isInflation ?_ hw
  letI : Epi (cobaseChange S sq).g := hepi
  exact CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk =>
    ⟨(key A k hk).choose, (key A k hk).choose_spec⟩

/-- **Base change of a conflation is a conflation with the same kernel.** The pullback of a
conflation `X ⟶ Y ⟶ Z` along a morphism `u : Z' ⟶ Z` is a conflation `X ⟶ Q ⟶ Z'`. -/
theorem conflation_baseChange {S : ShortComplex C} (hS : E.Conflation S) {Z' Q : C}
    {u : Z' ⟶ S.X₃} {v : Q ⟶ S.X₂} {w : Q ⟶ Z'} (sq : IsPullback v w S.g u) :
    E.Conflation (baseChange S sq) := by
  have hpair : IsKernelCokernelPair S := E.isKernelCokernelPair S hS
  have hw : E.IsDeflation w :=
    E.isStableUnderBaseChange_deflations.of_isPullback sq (E.isDeflation_g hS)
  have hmono : Mono (baseChangeι S sq) := by
    have := hpair.mono_f
    have h : Mono (baseChangeι S sq ≫ v) := by rw [baseChangeι_fst]; assumption
    exact mono_of_mono (baseChangeι S sq) v
  have key : ∀ (A : C) (k : A ⟶ Q), k ≫ w = 0 →
      ∃ l : A ⟶ S.X₁, l ≫ baseChangeι S sq = k := fun A k hk => by
    refine ⟨hpair.lift (k ≫ v) ?_, ?_⟩
    · rw [Category.assoc, sq.w, ← Category.assoc, hk, zero_comp]
    · refine sq.hom_ext ?_ ?_
      · rw [Category.assoc, baseChangeι_fst, hpair.lift_f]
      · rw [Category.assoc, baseChangeι_snd, comp_zero, hk]
  refine E.conflation_of_isLimit_of_isDeflation ?_ hw
  letI : Mono (baseChange S sq).f := hmono
  exact KernelFork.IsLimit.ofι' _ _ fun {A} k hk =>
    ⟨(key A k hk).choose, (key A k hk).choose_spec⟩

/-- **The cokernel of a composite of inflations.** If `X ⟶ Y ⟶ Z` and `Y ⟶ W ⟶ V` are
conflations, then the pushout `Q` of the inflation `Y ⟶ W` along the deflation `Y ⟶ Z` is a
cokernel of the composite inflation `X ⟶ W`. -/
theorem conflation_comp_of_isPushout {X Y Z W V Q : C} {i : X ⟶ Y} {p : Y ⟶ Z} {hip : i ≫ p = 0}
    (h₁ : E.Conflation (ShortComplex.mk i p hip)) {j : Y ⟶ W} {v : W ⟶ V} {hjv : j ≫ v = 0}
    (h₂ : E.Conflation (ShortComplex.mk j v hjv)) {c : W ⟶ Q} {α : Z ⟶ Q}
    (sq : IsPushout j p c α) :
    E.Conflation (ShortComplex.mk (i ≫ j) c
      (by rw [Category.assoc, sq.w, ← Category.assoc, hip, zero_comp])) := by
  have hpair₁ : IsKernelCokernelPair (ShortComplex.mk i p hip) := E.isKernelCokernelPair _ h₁
  have hp : Epi p := hpair₁.epi_g
  have hij : E.IsInflation (i ≫ j) :=
    E.isInflation_comp i j (E.isInflation_f h₁) (E.isInflation_f h₂)
  have hc : Epi c := ⟨fun {T} k l hkl => sq.hom_ext hkl <| (cancel_epi p).1 <| by
    simp only [← reassoc_of% sq.w, hkl]⟩
  have key : ∀ (T : C) (t : W ⟶ T), (i ≫ j) ≫ t = 0 → ∃ s : Q ⟶ T, c ≫ s = t := fun T t ht => by
    have hu : i ≫ j ≫ t = 0 := by rw [← Category.assoc]; exact ht
    exact ⟨sq.desc t (hpair₁.desc (j ≫ t) hu) (hpair₁.g_desc (j ≫ t) hu).symm, by simp⟩
  refine E.conflation_of_isColimit_of_isInflation ?_ hij
  exact CokernelCofork.IsColimit.ofπ' _ _ fun {T} t ht =>
    ⟨(key T t ht).choose, (key T t ht).choose_spec⟩

/-- **The kernel of a composite of deflations.** If `X ⟶ Y ⟶ Z` and `V ⟶ W ⟶ Y` are conflations,
then the pullback `Q` of the deflation `W ⟶ Y` along the inflation `X ⟶ Y` is a kernel of the
composite deflation `W ⟶ Z`. -/
theorem conflation_comp_of_isPullback {X Y Z W V Q : C} {i : X ⟶ Y} {p : Y ⟶ Z} {hip : i ≫ p = 0}
    (h₁ : E.Conflation (ShortComplex.mk i p hip)) {v : V ⟶ W} {q : W ⟶ Y} {hvq : v ≫ q = 0}
    (h₂ : E.Conflation (ShortComplex.mk v q hvq)) {c : Q ⟶ W} {α : Q ⟶ X}
    (sq : IsPullback c α q i) :
    E.Conflation (ShortComplex.mk c (q ≫ p)
      (by rw [← Category.assoc, sq.w, Category.assoc, hip, comp_zero])) := by
  have hpair₁ : IsKernelCokernelPair (ShortComplex.mk i p hip) := E.isKernelCokernelPair _ h₁
  have hi : Mono i := hpair₁.mono_f
  have hqp : E.IsDeflation (q ≫ p) :=
    E.isDeflation_comp q p (E.isDeflation_g h₂) (E.isDeflation_g h₁)
  have hc : Mono c := ⟨fun {T} k l hkl => sq.hom_ext hkl <| (cancel_mono i).1 <| by
    simp only [Category.assoc, ← sq.w, reassoc_of% hkl]⟩
  have key : ∀ (T : C) (t : T ⟶ W), t ≫ q ≫ p = 0 → ∃ l : T ⟶ Q, l ≫ c = t := fun T t ht => by
    have hu : (t ≫ q) ≫ p = 0 := by rw [Category.assoc]; exact ht
    exact ⟨sq.lift t (hpair₁.lift (t ≫ q) hu) (hpair₁.lift_f (t ≫ q) hu).symm, by simp⟩
  refine E.conflation_of_isLimit_of_isDeflation ?_ hqp
  exact KernelFork.IsLimit.ofι' _ _ fun {T} t ht =>
    ⟨(key T t ht).choose, (key T t ht).choose_spec⟩

/-- **The Noether isomorphism for exact categories.** Given conflations `X ⟶ Y ⟶ Z` and
`Y ⟶ W ⟶ V`, there is an object `Q` — the pushout of `Y ⟶ W` along `Y ⟶ Z` — which is at once
the cokernel of the composite inflation `X ⟶ W` and an extension of `V` by `Z`.

In the classical notation `Q ≅ W/X`, and the second conflation is
`Y/X ⟶ W/X ⟶ W/Y`. This is Bühler's Lemma 3.5, and it is exactly what an extension-closed
subcategory needs in order to inherit axiom E1. -/
theorem exists_conflation_comp {X Y Z W V : C} {i : X ⟶ Y} {p : Y ⟶ Z} {hip : i ≫ p = 0}
    (h₁ : E.Conflation (ShortComplex.mk i p hip)) {j : Y ⟶ W} {v : W ⟶ V} {hjv : j ≫ v = 0}
    (h₂ : E.Conflation (ShortComplex.mk j v hjv)) :
    ∃ (Q : C) (c : W ⟶ Q) (α : Z ⟶ Q) (β : Q ⟶ V) (hc : (i ≫ j) ≫ c = 0) (hβ : α ≫ β = 0),
      E.Conflation (ShortComplex.mk (i ≫ j) c hc) ∧ E.Conflation (ShortComplex.mk α β hβ) ∧
        j ≫ c = p ≫ α ∧ c ≫ β = v := by
  have : HasPushout j p := E.hasPushouts_inflations.hasPushout p (E.isInflation_f h₂)
  have sq : IsPushout j p (pushout.inl j p) (pushout.inr j p) := IsPushout.of_hasPushout j p
  exact ⟨pushout j p, pushout.inl j p, pushout.inr j p,
    cobaseChangeπ (ShortComplex.mk j v hjv) sq,
    by rw [Category.assoc, sq.w, ← Category.assoc, hip, zero_comp],
    inr_cobaseChangeπ (ShortComplex.mk j v hjv) sq,
    E.conflation_comp_of_isPushout h₁ h₂ sq, E.conflation_cobaseChange h₂ sq, sq.w,
    inl_cobaseChangeπ (ShortComplex.mk j v hjv) sq⟩

/-- **The dual Noether isomorphism.** Given conflations `X ⟶ Y ⟶ Z` and `V ⟶ W ⟶ Y`, the
pullback `Q` of `W ⟶ Y` along `X ⟶ Y` is at once the kernel of the composite deflation
`W ⟶ Z` and an extension of `X` by `V`. -/
theorem exists_conflation_comp' {X Y Z W V : C} {i : X ⟶ Y} {p : Y ⟶ Z} {hip : i ≫ p = 0}
    (h₁ : E.Conflation (ShortComplex.mk i p hip)) {v : V ⟶ W} {q : W ⟶ Y} {hvq : v ≫ q = 0}
    (h₂ : E.Conflation (ShortComplex.mk v q hvq)) :
    ∃ (Q : C) (c : Q ⟶ W) (α : Q ⟶ X) (β : V ⟶ Q) (hc : c ≫ q ≫ p = 0) (hβ : β ≫ α = 0),
      E.Conflation (ShortComplex.mk c (q ≫ p) hc) ∧ E.Conflation (ShortComplex.mk β α hβ) ∧
        c ≫ q = α ≫ i ∧ β ≫ c = v := by
  have : HasPullback q i := E.hasPullbacks_deflations.hasPullback i (E.isDeflation_g h₂)
  have sq : IsPullback (pullback.fst q i) (pullback.snd q i) q i := IsPullback.of_hasPullback q i
  exact ⟨pullback q i, pullback.fst q i, pullback.snd q i,
    baseChangeι (ShortComplex.mk v q hvq) sq,
    by rw [← Category.assoc, sq.w, Category.assoc, hip, comp_zero],
    baseChangeι_snd (ShortComplex.mk v q hvq) sq,
    E.conflation_comp_of_isPullback h₁ h₂ sq, E.conflation_baseChange h₂ sq, sq.w,
    baseChangeι_fst (ShortComplex.mk v q hvq) sq⟩

end ExactStructure

end TauCeti
