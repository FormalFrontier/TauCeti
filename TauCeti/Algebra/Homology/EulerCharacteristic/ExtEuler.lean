/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import TauCeti.LinearAlgebra.Exact

/-!
# Euler-admissible pairs and the Ext-Euler characteristic

Let `C` be a `k`-linear abelian category with `Ext` groups. The **Ext-Euler characteristic** of a
pair of objects is the alternating sum

```text
χ(X, Y) = ∑ n, (-1)ⁿ dim_k Extⁿ(X, Y).
```

This is a number only under two genuinely separate finiteness hypotheses: every `Extⁿ(X, Y)` must
be a finite-dimensional `k`-vector space, and `Extⁿ(X, Y)` must vanish for all large `n`. Neither
implies the other — over the dual numbers `k[ε]/(ε²)` the simple module `S` has
`Extⁿ(S, S) ≅ k` for every `n`, so the first holds and the second fails, while an
infinite-dimensional vector space is `Ext`-bounded but not `Ext`-finite against itself — and
a definition that totalizes the sum would return a junk value in exactly the first
situation. This file therefore keeps
the two conditions apart, as `IsExtFinite` and `IsExtBounded`, packages them as
`IsEulerAdmissible`, and defines the Euler characteristic only from a witness of both.

The value is defined by truncating the sum to the degrees below an explicit bound
(`truncatedExtEuler`); the whole content of `extEuler_eq` is that every bound beyond which the
`Ext` groups vanish gives the same answer.

## Main definitions

* `TauCeti.IsExtFinite`: every `Extⁿ(X, Y)` is a finite-dimensional `k`-vector space.
* `TauCeti.IsExtBoundedBy` and `TauCeti.IsExtBounded`: `Extⁿ(X, Y)` vanishes for `n` at least a
  given bound, resp. for all large `n`.
* `TauCeti.IsEulerAdmissible`: the conjunction of the two, the hypothesis under which the
  Ext-Euler characteristic of the pair `(X, Y)` exists.
* `TauCeti.IsExtBoundedOn` and `TauCeti.IsEulerAdmissibleOn`: respectively, uniform boundedness
  and pointwise Euler-admissibility for a pair of object properties; the latter is the hypothesis
  Layer 5's descent to Grothendieck groups will consume.
* `TauCeti.truncatedExtEuler` and `TauCeti.extEuler`: the truncated alternating sum, and the
  Ext-Euler characteristic of an Euler-admissible pair.
* `TauCeti.extLinearEquivOfIso`: the `k`-linear isomorphism `Extⁿ(X, Y) ≃ Extⁿ(X', Y')` induced
  by isomorphisms `X ≅ X'` and `Y ≅ Y'`.

## Main results

* `TauCeti.extEuler_eq`: the Ext-Euler characteristic is the alternating sum truncated at *any*
  bound beyond which the `Ext` groups vanish.
* `TauCeti.IsEulerAdmissible.of_iso` and `TauCeti.extEuler_of_iso`: isomorphism invariance of the
  hypothesis and of the value.
* `TauCeti.IsEulerAdmissible.of_shortExact₂` and
  `TauCeti.IsEulerAdmissible.of_shortExact₂'`: Euler-admissibility is closed under extensions in
  either variable, and `TauCeti.IsEulerAdmissible.biprod`,
  `TauCeti.IsEulerAdmissible.biprod'` under finite direct sums.
* `TauCeti.IsExtFinite.finiteDimensional_hom`: Hom-finiteness is the degree-zero consequence of
  `Ext`-finiteness, and is kept as a separate predicate.
* `TauCeti.extEuler_projective`: **projective evaluation**, `χ(P, Y) = dim_k Hom(P, Y)`.

The remaining Layer 5 targets — the long exact sequences cut off by the vanishing bound, the
resulting additivity of `χ` in both variables, and the descent of `χ` to a biadditive pairing on
Grothendieck groups — are not proved here; this file supplies the finiteness interface they are
stated over.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7 and Chapter 4, for `Ext`,
  its long exact sequences, and projective dimension.
* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras, Volume 1*, LMS Student Texts 65, Cambridge University Press (2006),
  Chapter III, Section 3, Proposition 3.13, for the Euler form of an algebra of finite global
  dimension.
* [The Tau Ceti Grothendieck groups, Cartan maps, and Euler forms roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/GrothendieckEulerForms/README.md),
  Layer 5, whose "Ext-finite pairs" bullet and the first half of its "Ext-Euler value" bullet are
  the targets proved here.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] (k : Type t) [Field k] [Linear k C]
  [HasExt.{w} C]

/-! ### The two finiteness conditions -/

/-- Every `Extⁿ(X, Y)` is a finite-dimensional `k`-vector space. This is one of the two
independent halves of `TauCeti.IsEulerAdmissible`; on its own it does not make the alternating
sum of the dimensions a finite sum. -/
structure IsExtFinite (X Y : C) : Prop where
  /-- Each `Ext` group of the pair is finite-dimensional. -/
  finiteDimensional (n : ℕ) : FiniteDimensional k (Ext.{w} X Y n)

/-- `Extⁿ(X, Y)` vanishes in every degree `n ≥ N`. -/
structure IsExtBoundedBy (X Y : C) (N : ℕ) : Prop where
  /-- The `Ext` groups of the pair vanish from degree `N` on. -/
  subsingleton ⦃n : ℕ⦄ (hn : N ≤ n) : Subsingleton (Ext.{w} X Y n)

/-- `Extⁿ(X, Y)` vanishes for all large `n`. This is the other half of
`TauCeti.IsEulerAdmissible`, and the one that makes the Ext-Euler characteristic a finite sum. -/
structure IsExtBounded (X Y : C) : Prop where
  /-- Some degree bounds the `Ext`-support of the pair. -/
  exists_bound : ∃ N, IsExtBoundedBy.{w} X Y N

/-- A pair `(X, Y)` is **Euler-admissible** when all of its `Ext` groups are finite-dimensional
and all but finitely many of them vanish. This is exactly the hypothesis under which the
alternating sum `∑ n, (-1)ⁿ dim_k Extⁿ(X, Y)` is a well-defined integer. -/
structure IsEulerAdmissible (X Y : C) : Prop where
  /-- All `Ext` groups of the pair are finite-dimensional. -/
  isExtFinite : IsExtFinite.{w} k X Y
  /-- All but finitely many `Ext` groups of the pair vanish. -/
  isExtBounded : IsExtBounded.{w} X Y

/-! ### Elementary consequences and monotonicity -/

variable {k}

namespace IsExtBoundedBy

/-- A vanishing bound may always be raised. -/
theorem mono {X Y : C} {N M : ℕ} (h : IsExtBoundedBy.{w} X Y N) (hNM : N ≤ M) :
    IsExtBoundedBy.{w} X Y M :=
  ⟨fun _ hn ↦ h.subsingleton (hNM.trans hn)⟩

/-- An explicit vanishing bound witnesses eventual `Ext`-vanishing. -/
theorem isExtBounded {X Y : C} {N : ℕ} (h : IsExtBoundedBy.{w} X Y N) : IsExtBounded.{w} X Y :=
  ⟨N, h⟩

end IsExtBoundedBy

/-- Hom-finiteness is the degree-zero part of `Ext`-finiteness, and is kept as a separate, weaker
predicate: it says nothing about the higher `Ext` groups. -/
theorem IsExtFinite.finiteDimensional_hom {X Y : C} (h : IsExtFinite.{w} k X Y) :
    FiniteDimensional k (X ⟶ Y) :=
  haveI := h.finiteDimensional 0
  Module.Finite.equiv (Ext.linearEquiv₀ (R := k) (X := X) (Y := Y))

variable (k)

/-! ### Versions for a pair of object properties -/

/-- A **uniform** `Ext`-vanishing bound for a pair of object properties: `Extⁿ(X, Y) = 0` in every
degree `n ≥ N`, for all `X` satisfying `P` and all `Y` satisfying `Q`. For a category of modules
over a `k`-algebra of finite global dimension this is the bound supplied by that dimension, and it
is a strictly stronger hypothesis than pointwise `Ext`-boundedness. -/
structure IsExtBoundedOn (P Q : ObjectProperty C) (N : ℕ) : Prop where
  /-- The bound `N` works for every pair of objects drawn from `P` and `Q`. -/
  isExtBoundedBy ⦃X Y : C⦄ (hX : P X) (hY : Q Y) : IsExtBoundedBy.{w} X Y N

/-- Every pair of objects drawn from `P` and `Q` is Euler-admissible, with a bound that may depend
on the pair. This is the hypothesis under which the Ext-Euler characteristic descends to a pairing
between the Grothendieck groups of the two subcategories. A shared bound is the separate, stronger
predicate `TauCeti.IsExtBoundedOn`. -/
structure IsEulerAdmissibleOn (P Q : ObjectProperty C) : Prop where
  /-- Each pair of objects drawn from `P` and `Q` is Euler-admissible. -/
  isEulerAdmissible ⦃X Y : C⦄ (hX : P X) (hY : Q Y) : IsEulerAdmissible.{w} k X Y

variable {k}

/-- A uniform bound is in particular a pointwise one. -/
theorem IsExtBoundedOn.isExtBounded {P Q : ObjectProperty C} {N : ℕ}
    (h : IsExtBoundedOn.{w} P Q N) {X Y : C} (hX : P X) (hY : Q Y) : IsExtBounded.{w} X Y :=
  (h.isExtBoundedBy hX hY).isExtBounded

/-- Euler-admissibility on a pair of object properties passes to smaller properties, in
particular to full subcategories of the ones considered. -/
theorem IsEulerAdmissibleOn.mono {P P' Q Q' : ObjectProperty C}
    (h : IsEulerAdmissibleOn.{w} k P Q) (hP : P' ≤ P) (hQ : Q' ≤ Q) :
    IsEulerAdmissibleOn.{w} k P' Q' :=
  ⟨fun _ _ hX hY ↦ h.isEulerAdmissible (hP _ hX) (hQ _ hY)⟩

/-- A uniform bound and pointwise `Ext`-finiteness give Euler-admissibility on the pair. -/
theorem IsExtBoundedOn.isEulerAdmissibleOn {P Q : ObjectProperty C} {N : ℕ}
    (h : IsExtBoundedOn.{w} P Q N)
    (hfin : ∀ ⦃X Y : C⦄, P X → Q Y → IsExtFinite.{w} k X Y) :
    IsEulerAdmissibleOn.{w} k P Q :=
  ⟨fun _ _ hX hY ↦ ⟨hfin hX hY, h.isExtBounded hX hY⟩⟩

/-! ### The Ext-Euler characteristic -/

variable (k)

/-- The alternating sum `∑_{n < N} (-1)ⁿ dim_k Extⁿ(X, Y)` of the `Ext` dimensions of the pair
`(X, Y)` in the cohomological degrees below `N`. Truncating at an explicit bound is what keeps
`TauCeti.extEuler` finite; its Euler-admissibility witness additionally ensures that every
dimension in the sum is genuine. -/
noncomputable def truncatedExtEuler (X Y : C) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, (-1) ^ n * (Module.finrank k (Ext.{w} X Y n) : ℤ)

/-- The empty truncation of the alternating sum is zero. -/
@[simp]
theorem truncatedExtEuler_zero (X Y : C) : truncatedExtEuler.{w} k X Y 0 = 0 :=
  Finset.sum_empty

/-- Raising the truncation bound by one adds the signed dimension of the next `Ext` group. -/
theorem truncatedExtEuler_succ (X Y : C) (N : ℕ) :
    truncatedExtEuler.{w} k X Y (N + 1) =
      truncatedExtEuler.{w} k X Y N + (-1) ^ N * (Module.finrank k (Ext.{w} X Y N) : ℤ) :=
  Finset.sum_range_succ _ N

/-- Raising the truncation bound past a degree from which the `Ext` groups vanish does not change
the alternating sum. -/
theorem truncatedExtEuler_eq_of_le {X Y : C} {N M : ℕ} (h : IsExtBoundedBy.{w} X Y N)
    (hNM : N ≤ M) : truncatedExtEuler.{w} k X Y M = truncatedExtEuler.{w} k X Y N := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 hNM) fun n _ hn ↦ ?_).symm
  have := h.subsingleton (by simpa using hn)
  simp [Module.finrank_zero_of_subsingleton]

/-- **The Ext-Euler characteristic** `χ(X, Y) = ∑ n, (-1)ⁿ dim_k Extⁿ(X, Y)` of an
Euler-admissible pair. The choice of vanishing bound made here is removed at once by
`TauCeti.extEuler_eq`, so no result depends on it. -/
noncomputable def extEuler {X Y : C} (h : IsEulerAdmissible.{w} k X Y) : ℤ :=
  truncatedExtEuler.{w} k X Y h.isExtBounded.exists_bound.choose

/-- **Every** degree from which the `Ext` groups of the pair vanish computes its Ext-Euler
characteristic. -/
theorem extEuler_eq {X Y : C} (h : IsEulerAdmissible.{w} k X Y) {N : ℕ}
    (hN : IsExtBoundedBy.{w} X Y N) : extEuler.{w} k h = truncatedExtEuler.{w} k X Y N := by
  have key : extEuler.{w} k h =
      truncatedExtEuler.{w} k X Y h.isExtBounded.exists_bound.choose := rfl
  exact key.trans
    ((truncatedExtEuler_eq_of_le k h.isExtBounded.exists_bound.choose_spec
        (le_max_left _ N)).symm.trans
      (truncatedExtEuler_eq_of_le k hN (le_max_right _ N)))

/-- The Ext-Euler characteristic of a pair with no `Ext` at all is zero. -/
theorem extEuler_eq_zero_of_isExtBoundedBy_zero {X Y : C} (h : IsEulerAdmissible.{w} k X Y)
    (h₀ : IsExtBoundedBy.{w} X Y 0) : extEuler.{w} k h = 0 := by
  rw [extEuler_eq k h h₀, truncatedExtEuler_zero]

/-! ### Isomorphism invariance -/

variable {X X' Y Y' : C}

/-- Isomorphisms `e : X ≅ X'` and `f : Y ≅ Y'` induce an isomorphism
`Extⁿ(X, Y) ≃ Extⁿ(X', Y')`, by composing with `e.inv` on the left and with `f.hom` on the right.
This is the action of an isomorphism through `CategoryTheory.Abelian.extFunctor`, spelled out so
that `TauCeti.extLinearEquivOfIso` can refine it to a `k`-linear equivalence. -/
noncomputable def extAddEquivOfIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w} X' Y' n where
  toFun x := (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun y := (Ext.mk₀ e.hom).comp (y.comp (Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

/-- `TauCeti.extAddEquivOfIso` composes with `e.inv` and `f.hom`. -/
theorem extAddEquivOfIso_apply (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extAddEquivOfIso e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-- The `k`-linear refinement of `TauCeti.extAddEquivOfIso`: in a `k`-linear abelian category,
isomorphisms `X ≅ X'` and `Y ≅ Y'` identify `Extⁿ(X, Y)` and `Extⁿ(X', Y')` as `k`-vector
spaces. -/
noncomputable def extLinearEquivOfIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Ext.{w} X Y n ≃ₗ[k] Ext.{w} X' Y' n where
  __ := extAddEquivOfIso e f n
  map_smul' r x := by simp [extAddEquivOfIso_apply]

/-- `TauCeti.extLinearEquivOfIso` composes with `e.inv` and `f.hom`. -/
theorem extLinearEquivOfIso_apply (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extLinearEquivOfIso k e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

variable {k}

/-- `Ext`-finiteness only depends on the isomorphism classes of the two objects. -/
theorem IsExtFinite.of_iso (h : IsExtFinite.{w} k X Y) (e : X ≅ X') (f : Y ≅ Y') :
    IsExtFinite.{w} k X' Y' :=
  ⟨fun n ↦ haveI := h.finiteDimensional n
    Module.Finite.equiv (extLinearEquivOfIso k e f n)⟩

/-- A vanishing bound transports along isomorphisms of the two objects. -/
theorem IsExtBoundedBy.of_iso {N : ℕ} (h : IsExtBoundedBy.{w} X Y N) (e : X ≅ X') (f : Y ≅ Y') :
    IsExtBoundedBy.{w} X' Y' N :=
  ⟨fun n hn ↦ haveI := h.subsingleton hn
    (extAddEquivOfIso e f n).symm.toEquiv.subsingleton⟩

/-- Eventual `Ext`-vanishing only depends on the isomorphism classes of the two objects. -/
theorem IsExtBounded.of_iso (h : IsExtBounded.{w} X Y) (e : X ≅ X') (f : Y ≅ Y') :
    IsExtBounded.{w} X' Y' :=
  ⟨h.exists_bound.choose, h.exists_bound.choose_spec.of_iso e f⟩

/-- Euler-admissibility only depends on the isomorphism classes of the two objects. -/
theorem IsEulerAdmissible.of_iso (h : IsEulerAdmissible.{w} k X Y) (e : X ≅ X') (f : Y ≅ Y') :
    IsEulerAdmissible.{w} k X' Y' :=
  ⟨h.isExtFinite.of_iso e f, h.isExtBounded.of_iso e f⟩

/-- The Ext-Euler characteristic only depends on the isomorphism classes of the two objects. -/
theorem extEuler_of_iso (h : IsEulerAdmissible.{w} k X Y)
    (h' : IsEulerAdmissible.{w} k X' Y') (e : X ≅ X') (f : Y ≅ Y') :
    extEuler.{w} k h = extEuler.{w} k h' := by
  obtain ⟨N, hN⟩ := h.isExtBounded.exists_bound
  rw [extEuler_eq k h hN, extEuler_eq k h' (hN.of_iso e f)]
  exact Finset.sum_congr rfl fun n _ ↦ by
    rw [(extLinearEquivOfIso k e f n).finrank_eq]

/-! ### Closure under extensions and finite direct sums -/

variable {S : ShortComplex C}

/-- Exactness of `Extⁿ(X, S.X₁) → Extⁿ(X, S.X₂) → Extⁿ(X, S.X₃)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` packaged as a
`Function.Exact` statement about the postcomposition maps. -/
theorem exact_postcomp (hS : S.ShortExact) (X : C) (n : ℕ) :
    Function.Exact (Ext.postcomp (Ext.mk₀ S.f) X (add_zero n))
      (Ext.postcomp (Ext.mk₀ S.g) X (add_zero n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.covariant_sequence_exact₂ X hS x₂ hx, by
    rintro ⟨x₁, rfl⟩
    simp [S.zero]⟩

/-- Exactness of `Extⁿ(S.X₃, Y) → Extⁿ(S.X₂, Y) → Extⁿ(S.X₁, Y)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` packaged as
a `Function.Exact` statement about the precomposition maps. -/
theorem exact_precomp (hS : S.ShortExact) (Y : C) (n : ℕ) :
    Function.Exact (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n))
      (Ext.precomp (Ext.mk₀ S.f) Y (zero_add n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.contravariant_sequence_exact₂ hS Y x₂ hx, by
    rintro ⟨x₃, rfl⟩
    simp [S.zero]⟩

/-- The linear postcomposition map agrees pointwise with `Ext.postcomp`. -/
theorem postcompOfLinear_apply (R : Type t) [CommRing R] [Linear R C]
    {Y Z : C} {n a b : ℕ} (beta : Ext.{w} Y Z n) (X : C)
    (h : a + n = b) (x : Ext.{w} X Y a) :
    Ext.postcompOfLinear beta R X h x = Ext.postcomp beta X h x :=
  rfl

/-- The linear precomposition map agrees pointwise with `Ext.precomp`. -/
theorem precompOfLinear_apply (R : Type t) [CommRing R] [Linear R C]
    {X Y : C} {n a b : ℕ} (alpha : Ext.{w} X Y n) (Z : C)
    (h : n + a = b) (x : Ext.{w} Y Z a) :
    Ext.precompOfLinear alpha R Z h x = Ext.precomp alpha Z h x :=
  rfl

variable (k)

/-- The `k`-linear form of `TauCeti.exact_postcomp`. -/
theorem exact_postcompOfLinear (hS : S.ShortExact) (X : C) (n : ℕ) :
    Function.Exact (Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero n))
      (Ext.postcompOfLinear (Ext.mk₀ S.g) k X (add_zero n)) := by
  rw [show ⇑(Ext.postcompOfLinear (Ext.mk₀ S.f) k X (add_zero n)) =
      Ext.postcomp (Ext.mk₀ S.f) X (add_zero n) from
    funext fun x ↦ postcompOfLinear_apply k _ _ _ x]
  rw [show ⇑(Ext.postcompOfLinear (Ext.mk₀ S.g) k X (add_zero n)) =
      Ext.postcomp (Ext.mk₀ S.g) X (add_zero n) from
    funext fun x ↦ postcompOfLinear_apply k _ _ _ x]
  exact exact_postcomp hS X n

/-- The `k`-linear form of `TauCeti.exact_precomp`. -/
theorem exact_precompOfLinear (hS : S.ShortExact) (Y : C) (n : ℕ) :
    Function.Exact (Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add n))
      (Ext.precompOfLinear (Ext.mk₀ S.f) k Y (zero_add n)) := by
  rw [show ⇑(Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add n)) =
      Ext.precomp (Ext.mk₀ S.g) Y (zero_add n) from
    funext fun x ↦ precompOfLinear_apply k _ _ _ x]
  rw [show ⇑(Ext.precompOfLinear (Ext.mk₀ S.f) k Y (zero_add n)) =
      Ext.precomp (Ext.mk₀ S.f) Y (zero_add n) from
    funext fun x ↦ precompOfLinear_apply k _ _ _ x]
  exact exact_precomp hS Y n

variable {k}

/-- **Extension closure in the second variable** for `Ext`-finiteness. -/
theorem IsExtFinite.of_shortExact₂ (hS : S.ShortExact) {X : C} (h₁ : IsExtFinite.{w} k X S.X₁)
    (h₃ : IsExtFinite.{w} k X S.X₃) : IsExtFinite.{w} k X S.X₂ :=
  ⟨fun n ↦ haveI := h₁.finiteDimensional n
    haveI := h₃.finiteDimensional n
    finiteDimensional_of_exact (exact_postcompOfLinear k hS X n)⟩

/-- **Extension closure in the first variable** for `Ext`-finiteness. -/
theorem IsExtFinite.of_shortExact₂' (hS : S.ShortExact) {Y : C} (h₁ : IsExtFinite.{w} k S.X₁ Y)
    (h₃ : IsExtFinite.{w} k S.X₃ Y) : IsExtFinite.{w} k S.X₂ Y :=
  ⟨fun n ↦ haveI := h₁.finiteDimensional n
    haveI := h₃.finiteDimensional n
    finiteDimensional_of_exact (exact_precompOfLinear k hS Y n)⟩

/-- **Extension closure in the second variable** for eventual `Ext`-vanishing: the middle term of
a short exact sequence inherits the larger of the two outer bounds. -/
theorem IsExtBoundedBy.of_shortExact₂ (hS : S.ShortExact) {X : C} {N₁ N₃ : ℕ}
    (h₁ : IsExtBoundedBy.{w} X S.X₁ N₁) (h₃ : IsExtBoundedBy.{w} X S.X₃ N₃) :
    IsExtBoundedBy.{w} X S.X₂ (max N₁ N₃) :=
  ⟨fun n hn ↦ haveI := h₁.subsingleton ((le_max_left N₁ N₃).trans hn)
    haveI := h₃.subsingleton ((le_max_right N₁ N₃).trans hn)
    subsingleton_of_exact (exact_postcomp hS X n) (map_zero _)⟩

/-- **Extension closure in the first variable** for eventual `Ext`-vanishing. -/
theorem IsExtBoundedBy.of_shortExact₂' (hS : S.ShortExact) {Y : C} {N₁ N₃ : ℕ}
    (h₁ : IsExtBoundedBy.{w} S.X₁ Y N₁) (h₃ : IsExtBoundedBy.{w} S.X₃ Y N₃) :
    IsExtBoundedBy.{w} S.X₂ Y (max N₁ N₃) :=
  ⟨fun n hn ↦ haveI := h₁.subsingleton ((le_max_left N₁ N₃).trans hn)
    haveI := h₃.subsingleton ((le_max_right N₁ N₃).trans hn)
    subsingleton_of_exact (exact_precomp hS Y n) (map_zero _)⟩

/-- **Euler-admissibility is closed under extensions in the second variable.** -/
theorem IsEulerAdmissible.of_shortExact₂ (hS : S.ShortExact) {X : C}
    (h₁ : IsEulerAdmissible.{w} k X S.X₁) (h₃ : IsEulerAdmissible.{w} k X S.X₃) :
    IsEulerAdmissible.{w} k X S.X₂ := by
  obtain ⟨N₁, hN₁⟩ := h₁.isExtBounded.exists_bound
  obtain ⟨N₃, hN₃⟩ := h₃.isExtBounded.exists_bound
  exact ⟨h₁.isExtFinite.of_shortExact₂ hS h₃.isExtFinite,
    (hN₁.of_shortExact₂ hS hN₃).isExtBounded⟩

/-- **Euler-admissibility is closed under extensions in the first variable.** -/
theorem IsEulerAdmissible.of_shortExact₂' (hS : S.ShortExact) {Y : C}
    (h₁ : IsEulerAdmissible.{w} k S.X₁ Y) (h₃ : IsEulerAdmissible.{w} k S.X₃ Y) :
    IsEulerAdmissible.{w} k S.X₂ Y := by
  obtain ⟨N₁, hN₁⟩ := h₁.isExtBounded.exists_bound
  obtain ⟨N₃, hN₃⟩ := h₃.isExtBounded.exists_bound
  exact ⟨h₁.isExtFinite.of_shortExact₂' hS h₃.isExtFinite,
    (hN₁.of_shortExact₂' hS hN₃).isExtBounded⟩

/-- Euler-admissibility is closed under binary direct sums in the second variable, because
`Y₁ ⟶ Y₁ ⊞ Y₂ ⟶ Y₂` is short exact. -/
theorem IsEulerAdmissible.biprod {X Y₁ Y₂ : C} (h₁ : IsEulerAdmissible.{w} k X Y₁)
    (h₂ : IsEulerAdmissible.{w} k X Y₂) : IsEulerAdmissible.{w} k X (Y₁ ⊞ Y₂) :=
  IsEulerAdmissible.of_shortExact₂ (ShortComplex.Splitting.ofHasBinaryBiproduct Y₁ Y₂).shortExact
    h₁ h₂

/-- Euler-admissibility is closed under binary direct sums in the first variable. -/
theorem IsEulerAdmissible.biprod' {X₁ X₂ Y : C} (h₁ : IsEulerAdmissible.{w} k X₁ Y)
    (h₂ : IsEulerAdmissible.{w} k X₂ Y) : IsEulerAdmissible.{w} k (X₁ ⊞ X₂) Y :=
  IsEulerAdmissible.of_shortExact₂' (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact
    h₁ h₂

/-! ### Projective evaluation -/

/-- All `Ext` groups of positive degree out of a projective object vanish, so a pair with
projective first entry is `Ext`-bounded by `1`. -/
theorem isExtBoundedBy_one_of_projective (P Y : C) [Projective P] : IsExtBoundedBy.{w} P Y 1 :=
  ⟨fun n hn ↦ by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa [Nat.add_comm] using Ext.subsingleton_of_projective.{w} P Y m⟩

/-- If every object satisfying `P` is projective, then `1` is a uniform `Ext`-vanishing bound for
`P` against an arbitrary `Q`. This is the degenerate case of a uniform global-dimension bound, and
the one Layer 4's Cartan comparison uses on the subcategory of projectives. -/
theorem isExtBoundedOn_one_of_projective {P : ObjectProperty C} (hP : ∀ X, P X → Projective X)
    (Q : ObjectProperty C) : IsExtBoundedOn.{w} P Q 1 :=
  ⟨fun X Y hX _ ↦ haveI := hP X hX
    isExtBoundedBy_one_of_projective X Y⟩

variable (k)

/-- A Hom-finite pair with projective first entry is `Ext`-finite: apart from the degree-zero
group, which is the Hom space, all of its `Ext` groups vanish. -/
theorem isExtFinite_of_projective (P Y : C) [Projective P] [FiniteDimensional k (P ⟶ Y)] :
    IsExtFinite.{w} k P Y := by
  refine ⟨fun n ↦ ?_⟩
  match n with
  | 0 => exact Module.Finite.equiv (Ext.linearEquiv₀ (R := k) (X := P) (Y := Y)).symm
  | (m + 1) =>
    have := Ext.subsingleton_of_projective.{w} P Y m
    infer_instance

/-- A Hom-finite pair with projective first entry is Euler-admissible. -/
theorem isEulerAdmissible_of_projective (P Y : C) [Projective P] [FiniteDimensional k (P ⟶ Y)] :
    IsEulerAdmissible.{w} k P Y :=
  ⟨isExtFinite_of_projective k P Y, (isExtBoundedBy_one_of_projective P Y).isExtBounded⟩

/-- **Projective evaluation**: the Ext-Euler characteristic of a pair with projective first entry
is the dimension of its Hom space, `χ(P, Y) = dim_k Hom(P, Y)`. -/
theorem extEuler_projective {P Y : C} [Projective P]
    (h : IsEulerAdmissible.{w} k P Y) :
    extEuler.{w} k h = Module.finrank k (P ⟶ Y) := by
  rw [extEuler_eq k h (isExtBoundedBy_one_of_projective P Y), truncatedExtEuler_succ,
    truncatedExtEuler_zero, (Ext.linearEquiv₀ (R := k) (X := P) (Y := Y)).finrank_eq]
  simp

/-- Hom-finite projectives are Euler-admissible against every object: this is the concrete source
of Euler-admissibility on the projective side, and it is what makes
`TauCeti.IsEulerAdmissibleOn` a nonempty hypothesis. -/
theorem isEulerAdmissibleOn_of_projective {P Q : ObjectProperty C} (hP : ∀ X, P X → Projective X)
    (hHom : ∀ ⦃X Y : C⦄, P X → Q Y → FiniteDimensional k (X ⟶ Y)) :
    IsEulerAdmissibleOn.{w} k P Q :=
  ⟨fun X Y hX hY ↦ haveI := hP X hX
    haveI := hHom hX hY
    isEulerAdmissible_of_projective k X Y⟩

end TauCeti
