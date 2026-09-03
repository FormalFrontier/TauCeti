/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator

/-!
# Alternating elements of the group algebra of a weight space

An element `f` of the integral group algebra `ℤ[M]` of the weight space of a root pairing is
**alternating** for the dot action when its coefficients transform by the sign character,

`[e^{w ⬝ x}] f = sgn(w) · [e^x] f`.

Both universal elements of the Weyl character formula are alternating: the Weyl denominator
`Δ = ∏_{α>0}(1 - e^{-α})` (`TauCeti.coeff_weylDenominator_dotAction`) and the Weyl numerator
`N(λ) = ∑_{w} sgn(w) e^{w ⬝ λ}` of any weight. This file proves that the numerators exhaust them:
an alternating element is the sign-symmetrization of its coefficients on a fundamental domain, so
that `ℤ[M]`'s alternating elements are freely spanned by the numerators. That is the step by which
the Weyl character formula is concluded: the product `ch L(λ) · Δ` is alternating, being a product
of a Weyl-invariant and an alternating element, and the formula is then the identification of which
combination of numerators it is.

The Weyl denominator identity `Δ = N(0)`
(`TauCeti.weylDenominator_eq_weylNumerator_zero`) is that identification carried out for `Δ`
itself, and is the case `λ = 0` of the character formula.

## The fundamental domain

The dot action `w ⬝ x = w(x + ρ) - ρ` has its walls at `⟨x, αᵢ^∨⟩ = -1`, so its open chamber is
`TauCeti.openDotDominantChamber`, the weights whose `ρ`-shift is strictly dominant, which for a
general coefficient ring may be strictly larger than the closed dominant chamber. Two facts about it
drive everything here. The dot action is **free** on it, so a numerator `N(μ)` with `μ` in the
chamber has coefficient `1` at `μ` and `0` at every other point of the chamber. And every weight is
carried into the closed shifted chamber by some Weyl-group element, whose boundary is a union of
walls, where an alternating element vanishes because an odd element fixes the point. Together these
say an alternating element is determined by its restriction to the open dot chamber
(`TauCeti.IsDotAlternating.eq_of_coeff_openDotDominantChamber_eq`), which is the mechanism behind
every result below.

## Main definitions

* `TauCeti.IsDotAlternating`: the coefficients of `f` transform by the sign character under the dot
  action. `TauCeti.isDotAlternating_iff` is the preferred way to introduce it and
  `TauCeti.IsDotAlternating.coeff_dotAction` the preferred way to eliminate it, so that the
  definition itself need not be unfolded.
* `TauCeti.dotAlternatingSubmodule`: the alternating elements as a `ℤ`-submodule of `ℤ[M]`.
* `TauCeti.weylNumeratorBasis`: its basis of Weyl numerators, indexed by the open dot chamber, whose
  coordinates are read off by `TauCeti.weylNumeratorBasis_repr_apply`.

## Main results

* `TauCeti.isDotAlternating_weylNumerator` and `TauCeti.isDotAlternating_weylDenominator`: the Weyl
  numerator of any weight, and the Weyl denominator, are alternating.
* `TauCeti.IsDotAlternating.eq_of_coeff_openDotDominantChamber_eq`: an alternating element is
  determined by its coefficients on the open chamber of the dot action.
* `TauCeti.IsDotAlternating.eq_sum_weylNumerator`: **an alternating element is the sum of the Weyl
  numerators of the points of the open dot chamber in its support, weighted by its coefficients
  there**, and `TauCeti.eq_zero_of_sum_smul_weylNumerator_eq_zero`: those weights are unique.
  Together they are the spanning and independence halves of `TauCeti.weylNumeratorBasis`.
* `TauCeti.IsDotAlternating.eq_weylNumerator`: **an alternating element whose only nonvanishing
  coefficient on the open dot chamber is a `1` at `λ` is `N(λ)`**, the form in which the Weyl
  character formula consumes all of this.

## References

This is the "concluding by Weyl alternation" step of the Weyl character formula route fixed by
Layer 6 ("the Weyl character, dimension, and Kostant formulas") of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. As with `TauCeti.weylNumerator`
and `TauCeti.weylDenominator`, nothing here needs a Lie algebra, so it is stated for an abstract
root pairing and the Lie-algebra statement is a specialization rather than a rebuild.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.2.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII, §7.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

section Alternating

variable [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]

/-- An element of the integral group algebra of the weight space is **alternating** for the dot
action when its coefficients transform by the sign character of the Weyl group,
`[e^{w ⬝ x}] f = sgn(w) · [e^x] f`.

The dot action `w ⬝ x = w(x + ρ) - ρ` is used rather than the linear one because that is the
normalization in which the Weyl denominator `∏_{α>0}(1 - e^{-α})` is alternating: the linear action
sends it to `sgn(w) e^{w(ρ) - ρ}` times itself. -/
def IsDotAlternating (f : AddMonoidAlgebra ℤ M) : Prop :=
  ∀ (w : P.weylGroup) (x : M),
    f.coeff (dotAction P b w x) = ((weylSign P b w : ℤ)) * f.coeff x

/-- The defining condition of `TauCeti.IsDotAlternating`, as an `Iff`: this is the preferred way to
introduce the predicate, and `TauCeti.IsDotAlternating.coeff_dotAction` the preferred way to
eliminate it, so that callers need not unfold the definition.

Not a `simp` lemma: unfolding the predicate would dissolve `IsDotAlternating` out of the goals its
own API is stated about. -/
lemma isDotAlternating_iff (f : AddMonoidAlgebra ℤ M) :
    IsDotAlternating P b f ↔ ∀ (w : P.weylGroup) (x : M),
      f.coeff (dotAction P b w x) = ((weylSign P b w : ℤ)) * f.coeff x := Iff.rfl

/-- The zero element is alternating. -/
theorem isDotAlternating_zero : IsDotAlternating P b (0 : AddMonoidAlgebra ℤ M) := by
  intro w x
  simp

/-- **The Weyl denominator is alternating.** This is
`TauCeti.coeff_weylDenominator_dotAction`, packaged as the predicate. -/
theorem isDotAlternating_weylDenominator : IsDotAlternating P b (weylDenominator P b) :=
  coeff_weylDenominator_dotAction P b

/-- **The Weyl numerator of any weight is alternating.** Reindexing the defining sum by `v ↦ w⁻¹v`
matches the term at `w ⬝ x` with the term at `x`, at the cost of the sign of `w`. -/
theorem isDotAlternating_weylNumerator [Fintype P.weylGroup] (lam : M) :
    IsDotAlternating P b (weylNumerator P b lam) :=
  coeff_weylNumerator_dotAction P b lam

variable {P b} {f g : AddMonoidAlgebra ℤ M}

namespace IsDotAlternating

/-- The defining identity of an alternating element, as an elimination rule. -/
theorem coeff_dotAction (hf : IsDotAlternating P b f) (w : P.weylGroup) (x : M) :
    f.coeff (dotAction P b w x) = ((weylSign P b w : ℤ)) * f.coeff x := hf w x

/-- A sum of alternating elements is alternating. -/
theorem add (hf : IsDotAlternating P b f) (hg : IsDotAlternating P b g) :
    IsDotAlternating P b (f + g) := by
  intro w x
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf w x, hg w x]
  ring

/-- The negative of an alternating element is alternating. -/
theorem neg (hf : IsDotAlternating P b f) : IsDotAlternating P b (-f) := by
  intro w x
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hf w x]
  ring

/-- A difference of alternating elements is alternating. -/
theorem sub (hf : IsDotAlternating P b f) (hg : IsDotAlternating P b g) :
    IsDotAlternating P b (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- An integer multiple of an alternating element is alternating. -/
theorem zsmul (hf : IsDotAlternating P b f) (c : ℤ) : IsDotAlternating P b (c • f) := by
  intro w x
  simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, hf w x]
  ring

/-- **A coefficient of an alternating element at a weight fixed by an odd Weyl-group element
vanishes**: the alternating identity turns such a fixed point into `c = -c`. -/
theorem coeff_eq_zero_of_dotAction_eq_self (hf : IsDotAlternating P b f) {w : P.weylGroup} {x : M}
    (hw : weylSign P b w = -1) (hx : dotAction P b w x = x) : f.coeff x = 0 := by
  have h := hf w x
  rw [hx, hw] at h
  norm_num at h
  omega

/-- **A coefficient of an alternating element on a wall of the dot action vanishes.** The wall of
the simple reflection `sᵢ` is the affine hyperplane `⟨x, αᵢ^∨⟩ = -1`, and a simple reflection is
odd. -/
theorem coeff_eq_zero_of_coroot'_eq_neg_one (hf : IsDotAlternating P b f) {i : ι}
    (hi : i ∈ b.support) {x : M} (hx : P.coroot' i x = -1) : f.coeff x = 0 :=
  hf.coeff_eq_zero_of_dotAction_eq_self (weylSign_ofIdx P b i)
    ((dotAction_ofIdx_eq_self_iff P b hi x).mpr hx)

end IsDotAlternating

/-- A finite sum of alternating elements is alternating. -/
theorem isDotAlternating_sum {α : Type*} {s : Finset α} {g : α → AddMonoidAlgebra ℤ M}
    (hg : ∀ a ∈ s, IsDotAlternating P b (g a)) : IsDotAlternating P b (∑ a ∈ s, g a) :=
  Finset.sum_induction g (IsDotAlternating P b) (fun _ _ ha hb ↦ ha.add hb)
    (isDotAlternating_zero P b) hg

variable (P b) in
/-- **The alternating elements of the integral group algebra `ℤ[M]`, as a `ℤ`-submodule.** The
closure properties are `TauCeti.isDotAlternating_zero`, `TauCeti.IsDotAlternating.add` and
`TauCeti.IsDotAlternating.zsmul`; `TauCeti.weylNumeratorBasis` is its basis of Weyl numerators. -/
def dotAlternatingSubmodule : Submodule ℤ (AddMonoidAlgebra ℤ M) where
  carrier := {f | IsDotAlternating P b f}
  zero_mem' := isDotAlternating_zero P b
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.zsmul c

/-- Membership in `TauCeti.dotAlternatingSubmodule` is being alternating. -/
@[simp]
lemma mem_dotAlternatingSubmodule :
    f ∈ dotAlternatingSubmodule P b ↔ IsDotAlternating P b f := Iff.rfl

end Alternating

/-! ### The open chamber of the dot action as a fundamental domain

Everything below reads an alternating element off its coefficients on
`TauCeti.openDotDominantChamber`. The linearly ordered hypotheses already supply `IsDomain R`
through `IsStrictOrderedRing.isDomain`, so it is not repeated.
-/

section Dominant

variable [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]
  [LinearOrder R] [IsStrictOrderedRing R]

section Numerator

variable [P.flip.IsReduced] [Fintype P.weylGroup]

/-- **The numerator of a weight of the open dot chamber vanishes at every other weight of that
chamber**: the chamber meets each dot orbit at most once. -/
@[simp]
theorem coeff_weylNumerator_eq_zero_of_mem_openDotDominantChamber {lam nu : M}
    (hlam : lam ∈ openDotDominantChamber P b) (hnu : nu ∈ openDotDominantChamber P b)
    (hne : lam ≠ nu) : (weylNumerator P b lam).coeff nu = 0 :=
  coeff_weylNumerator_eq_zero P b fun _ hw ↦
    hne (eq_of_dotAction_eq_of_mem_openDotDominantChamber P b hlam hnu hw).symm

end Numerator

variable {P b} {f g : AddMonoidAlgebra ℤ M}

section Determination

variable [P.IsRootSystem]

/-- **An alternating element vanishing on the open chamber of the dot action vanishes
identically.**

Every weight is carried by some Weyl-group element to one whose `ρ`-shift is dominant. If that
shift is strictly dominant the hypothesis applies; otherwise the weight lies on a wall, where an
alternating element vanishes. Either way the coefficient there vanishes, and it differs from the
original coefficient by a sign. -/
theorem IsDotAlternating.coeff_eq_zero_of_forall_mem_openDotDominantChamber
    (hf : IsDotAlternating P b f) (h : ∀ y ∈ openDotDominantChamber P b, f.coeff y = 0) (x : M) :
    f.coeff x = 0 := by
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber P b (x + weylVector P b)
  have hyd : dotAction P b w x + weylVector P b ∈ dominantChamber P b := by
    rw [dotAction_add_weylVector]
    exact hw
  have hzero : f.coeff (dotAction P b w x) = 0 := by
    by_cases hopen : dotAction P b w x ∈ openDotDominantChamber P b
    · exact h _ hopen
    · rw [mem_openDotDominantChamber, mem_openDominantChamber] at hopen
      push Not at hopen
      obtain ⟨i, hi, hle⟩ := hopen
      refine hf.coeff_eq_zero_of_coroot'_eq_neg_one hi ?_
      have hwall := le_antisymm hle ((mem_dominantChamber P b _).mp hyd i hi)
      rw [coroot'_add_weylVector P b hi] at hwall
      linarith
  have hcoeff := hf w x
  rw [hzero] at hcoeff
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left
    (by exact_mod_cast Units.ne_zero (weylSign P b w))

/-- **An alternating element is determined by its coefficients on the open chamber of the dot
action.** -/
theorem IsDotAlternating.eq_of_coeff_openDotDominantChamber_eq (hf : IsDotAlternating P b f)
    (hg : IsDotAlternating P b g)
    (h : ∀ x ∈ openDotDominantChamber P b, f.coeff x = g.coeff x) : f = g := by
  rw [← sub_eq_zero, ← AddMonoidAlgebra.coeff_eq_zero]
  refine Finsupp.ext fun x ↦ ?_
  simpa using (hf.sub hg).coeff_eq_zero_of_forall_mem_openDotDominantChamber
    (fun y hy ↦ by simp [AddMonoidAlgebra.coeff_sub, h y hy]) x

end Determination

section Basis

variable [P.flip.IsReduced] [P.IsRootSystem] [Fintype P.weylGroup]

open scoped Classical in
/-- **An alternating element is the combination of the Weyl numerators of the weights of the open
dot chamber in its support**, taken with its own coefficients there as multipliers.

This is the spanning half of `TauCeti.weylNumeratorBasis`; with
`TauCeti.eq_zero_of_sum_smul_weylNumerator_eq_zero`, which says those coefficients are uniquely
determined, it exhibits the numerators `N(μ)` for `μ` in the open dot chamber as a basis of the
alternating elements of `ℤ[M]`. -/
theorem IsDotAlternating.eq_sum_weylNumerator (hf : IsDotAlternating P b f) :
    f = ∑ mu ∈ f.coeff.support.filter (· ∈ openDotDominantChamber P b),
      f.coeff mu • weylNumerator P b mu := by
  refine hf.eq_of_coeff_openDotDominantChamber_eq
    (isDotAlternating_sum fun mu _ ↦ (isDotAlternating_weylNumerator P b mu).zsmul _)
    fun nu hnu ↦ ?_
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  by_cases hmem : nu ∈ f.coeff.support.filter (· ∈ openDotDominantChamber P b)
  · rw [Finset.sum_eq_single_of_mem nu hmem fun mu hmu hne ↦ by
      rw [coeff_weylNumerator_eq_zero_of_mem_openDotDominantChamber P b
        (Finset.mem_filter.mp hmu).2 hnu hne, mul_zero],
      coeff_weylNumerator_self_of_mem_openDotDominantChamber P b hnu, mul_one]
  · have hzero : f.coeff nu = 0 := by
      by_contra hne
      exact hmem (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hnu⟩)
    rw [hzero]
    refine (Finset.sum_eq_zero fun mu hmu ↦ ?_).symm
    rw [coeff_weylNumerator_eq_zero_of_mem_openDotDominantChamber P b
      (Finset.mem_filter.mp hmu).2 hnu fun hc ↦ hmem (hc ▸ hmu), mul_zero]

omit [P.IsRootSystem] in
/-- **The Weyl numerators of the weights of the open dot chamber are linearly independent over
`ℤ`**: a vanishing combination has vanishing multipliers, since the coefficient of the combination
at `ν` is exactly the multiplier of `N(ν)`. -/
theorem eq_zero_of_sum_smul_weylNumerator_eq_zero {s : Finset M} {c : M → ℤ}
    (hs : ∀ mu ∈ s, mu ∈ openDotDominantChamber P b)
    (h : ∑ mu ∈ s, c mu • weylNumerator P b mu = 0) {nu : M} (hnu : nu ∈ s) : c nu = 0 := by
  have h' := congrArg (fun u : AddMonoidAlgebra ℤ M ↦ u.coeff nu) h
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h'
  rwa [Finset.sum_eq_single_of_mem nu hnu fun mu hmu hne ↦ by
      rw [coeff_weylNumerator_eq_zero_of_mem_openDotDominantChamber P b (hs mu hmu) (hs nu hnu)
        hne, mul_zero],
    coeff_weylNumerator_self_of_mem_openDotDominantChamber P b (hs nu hnu), mul_one] at h'

variable (P b) in
/-- **The Weyl numerators of the weights of the open dot chamber, as a basis of the alternating
elements of `ℤ[M]`.**

The two halves are `TauCeti.IsDotAlternating.eq_sum_weylNumerator`, which spans, and
`TauCeti.eq_zero_of_sum_smul_weylNumerator_eq_zero`, which is the independence; those are what
`Module.Basis.mk` consumes here, and `TauCeti.weylNumeratorBasis_repr_apply` reads the resulting
coordinates back as the coefficients of the element on the chamber. -/
noncomputable def weylNumeratorBasis :
    Module.Basis (openDotDominantChamber P b) ℤ (dotAlternatingSubmodule P b) :=
  Module.Basis.mk (v := fun mu ↦ ⟨weylNumerator P b mu, isDotAlternating_weylNumerator P b mu⟩)
    (by
      classical
      refine linearIndependent_iff'.mpr fun s g hg mu hmu ↦ ?_
      -- extend the multipliers, indexed by the chamber, to a function on all of `M`
      obtain ⟨c, hcval⟩ : ∃ c : M → ℤ, ∀ nu : openDotDominantChamber P b, c nu = g nu :=
        ⟨fun x ↦ if h : x ∈ openDotDominantChamber P b then g ⟨x, h⟩ else 0, fun nu ↦ by simp⟩
      have hsum : ∑ nu ∈ s.image ((↑) : openDotDominantChamber P b → M),
          c nu • weylNumerator P b nu = 0 := by
        rw [Finset.sum_image fun x _ y _ h ↦ Subtype.ext h]
        simpa [hcval] using congrArg Subtype.val hg
      have := eq_zero_of_sum_smul_weylNumerator_eq_zero
        (fun nu hnu ↦ by obtain ⟨nu, -, rfl⟩ := Finset.mem_image.mp hnu; exact nu.2) hsum
        (Finset.mem_image_of_mem _ hmu)
      rwa [hcval] at this)
    (by
      classical
      rintro ⟨f, hf⟩ -
      have key : (⟨f, hf⟩ : dotAlternatingSubmodule P b) =
          ∑ mu ∈ (f.coeff.support.filter (· ∈ openDotDominantChamber P b)).attach,
            f.coeff (mu : M) •
              (⟨weylNumerator P b mu, isDotAlternating_weylNumerator P b mu⟩ :
                dotAlternatingSubmodule P b) := by
        refine Subtype.ext ?_
        rw [AddSubmonoidClass.coe_finsetSum]
        simp only [SetLike.val_smul]
        rw [Finset.sum_attach _ fun mu ↦ f.coeff mu • weylNumerator P b mu]
        exact hf.eq_sum_weylNumerator
      rw [key]
      exact Submodule.sum_mem _ fun mu _ ↦ Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨(mu : M), (Finset.mem_filter.mp mu.2).2⟩, rfl⟩))

variable (P b) in
/-- The basis vector of `TauCeti.weylNumeratorBasis` at a weight of the open dot chamber is the
Weyl numerator of that weight. -/
@[simp]
lemma coe_weylNumeratorBasis (mu : openDotDominantChamber P b) :
    (weylNumeratorBasis P b mu : AddMonoidAlgebra ℤ M) = weylNumerator P b mu :=
  congrArg Subtype.val (Module.Basis.mk_apply _ _ mu)

variable (P b) in
/-- **The coordinates of an alternating element in the basis of Weyl numerators are its
coefficients on the open dot chamber.** -/
@[simp]
lemma weylNumeratorBasis_repr_apply (f : dotAlternatingSubmodule P b)
    (mu : openDotDominantChamber P b) :
    (weylNumeratorBasis P b).repr f mu = (f : AddMonoidAlgebra ℤ M).coeff mu := by
  classical
  refine (weylNumeratorBasis P b).repr_apply_eq
    (fun f mu ↦ (f : AddMonoidAlgebra ℤ M).coeff mu) (fun _ _ ↦ funext fun _ ↦ by simp)
    (fun _ _ ↦ funext fun _ ↦ by
      simp only [SetLike.val_smul, AddMonoidAlgebra.coeff_smul_apply, Pi.smul_apply])
    (fun mu ↦ funext fun nu ↦ ?_) f mu
  rcases eq_or_ne nu mu with rfl | hne
  · simp [coeff_weylNumerator_self_of_mem_openDotDominantChamber P b nu.2]
  · rw [Finsupp.single_eq_of_ne hne]
    simpa using coeff_weylNumerator_eq_zero_of_mem_openDotDominantChamber P b mu.2 nu.2
      fun h ↦ hne (Subtype.ext h).symm

/-- **An alternating element whose only nonvanishing coefficient on the open dot chamber is a `1`
at `λ` is the Weyl numerator of `λ`.**

This is the form in which the Weyl denominator identity
(`TauCeti.weylDenominator_eq_weylNumerator_zero`) is proved, and the form the Weyl character
formula is meant to be concluded in: for an alternating element the hypotheses are two coefficient
computations on the open dot chamber, and nothing else about it is needed. -/
theorem IsDotAlternating.eq_weylNumerator (hf : IsDotAlternating P b f) {lam : M}
    (hlam : lam ∈ openDotDominantChamber P b) (hcoeff : f.coeff lam = 1)
    (hsupp : ∀ x ∈ openDotDominantChamber P b, f.coeff x ≠ 0 → x = lam) :
    f = weylNumerator P b lam := by
  refine hf.eq_of_coeff_openDotDominantChamber_eq (isDotAlternating_weylNumerator P b lam)
    fun nu hnu ↦ ?_
  by_cases hne : nu = lam
  · subst hne
    rw [hcoeff, coeff_weylNumerator_self_of_mem_openDotDominantChamber P b hlam]
  · rw [coeff_weylNumerator_eq_zero_of_mem_openDotDominantChamber P b hlam hnu (Ne.symm hne)]
    by_contra hc
    exact hne (hsupp nu hnu hc)

end Basis

end Dominant

end TauCeti
