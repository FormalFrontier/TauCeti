/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# The Ext-Euler characteristic from a finite projective resolution

Let `C` be a `k`-linear abelian category. A finite projective resolution

```text
0 ⟶ Pₙ ⟶ ⋯ ⟶ P₁ ⟶ P₀ ⟶ X ⟶ 0
```

computes the Ext-Euler characteristic against `Y` as the alternating Hom dimension

```text
χ(X, Y) = ∑ i, (-1)ⁱ dimₖ Hom(Pᵢ, Y).
```

The only finiteness hypothesis needed on the resolution is that every resolving object has a
finite-dimensional Hom space into `Y`. Projectivity makes its higher `Ext` groups vanish. The
long exact Ext sequence then proves, from the far end of the resolution towards `X`, both that
`(X, Y)` is Euler-admissible and that the displayed formula holds.

The auxiliary `of_shortExact₃'` lemmas below are the first-variable two-out-of-three statements
needed by that induction: for a short exact sequence `X₁ ⟶ X₂ ⟶ X₃`, finiteness and
eventual vanishing for `(X₁, Y)` and `(X₂, Y)` imply the corresponding property for `(X₃, Y)`.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.homEuler`: the alternating Hom dimension of the terms
  of a finite resolution.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.isEulerAdmissible`: a Hom-finite finite projective
  resolution makes the resolved pair Euler-admissible.
* `TauCeti.ExactStructure.FiniteResolution.extEuler_eq_homEuler`: every admissibility witness gives
  the Ext-Euler characteristic as the alternating Hom dimension of the resolution.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7, for the long
  exact Ext sequence and computation of Ext by projective resolutions.
* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras, Volume 1*, Chapter III, Proposition 3.13, for the resulting Euler-form
  formula over a finite-dimensional algebra.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C]

/-! ### Two-out-of-three towards the quotient term -/

variable {S : ShortComplex C} {Y : C}

/-- In the first-variable long exact Ext sequence, Ext-finiteness of the subobject and middle
object implies Ext-finiteness of the quotient. -/
theorem IsExtFinite.of_shortExact₃' (hS : S.ShortExact)
    (h₁ : IsExtFinite.{w} k S.X₁ Y) (h₂ : IsExtFinite.{w} k S.X₂ Y) :
    IsExtFinite.{w} k S.X₃ Y := by
  refine ⟨fun n ↦ ?_⟩
  match n with
  | 0 =>
      let _ := hS.epi_g
      let _ := h₂.finiteDimensional 0
      exact FiniteDimensional.of_injective
        (Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add 0))
        (Ext.precomp_mk₀_injective_of_epi Y S.g)
  | n + 1 =>
      let _ := h₁.finiteDimensional n
      let _ := h₂.finiteDimensional (n + 1)
      have h := Ext.contravariant_sequence_exact₃' hS Y n (n + 1) (Nat.one_add n)
      rw [ShortComplex.ab_exact_iff_function_exact] at h
      -- Mathlib states this through `AddCommGrpCat`; expose the underlying functions so the
      -- same exactness proof applies to the linear refinements.
      change Function.Exact (Ext.precomp hS.extClass Y (Nat.one_add n))
        (Ext.precomp (Ext.mk₀ S.g) Y (zero_add (n + 1))) at h
      exact finiteDimensional_of_exact
        (f := Ext.precompOfLinear hS.extClass k Y (Nat.one_add n))
        (g := Ext.precompOfLinear (Ext.mk₀ S.g) k Y (zero_add (n + 1)))
        h

/-- In the first-variable long exact Ext sequence, bounds for the subobject and middle object
give a bound for the quotient. A bound `N₁` for the subobject is shifted by one degree. -/
theorem IsExtBoundedBy.of_shortExact₃' (hS : S.ShortExact) {N₁ N₂ : ℕ}
    (h₁ : IsExtBoundedBy.{w} S.X₁ Y N₁) (h₂ : IsExtBoundedBy.{w} S.X₂ Y N₂) :
    IsExtBoundedBy.{w} S.X₃ Y (max (N₁ + 1) N₂) := by
  refine ⟨fun {n} hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let _ := h₁.subsingleton (by omega : N₁ ≤ m)
  let _ := h₂.subsingleton (by omega : N₂ ≤ m + 1)
  have h := Ext.contravariant_sequence_exact₃' hS Y m (m + 1) (Nat.one_add m)
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  -- As above, remove only the concrete-category wrapper from Mathlib's exactness statement.
  change Function.Exact (Ext.precomp hS.extClass Y (Nat.one_add m))
    (Ext.precomp (Ext.mk₀ S.g) Y (zero_add (m + 1))) at h
  exact subsingleton_of_exact
    (f := Ext.precomp hS.extClass Y (Nat.one_add m))
    (g := Ext.precomp (Ext.mk₀ S.g) Y (zero_add (m + 1))) h (map_zero _)

/-- Euler-admissibility for the subobject and middle object of a short exact sequence implies
Euler-admissibility for its quotient, in the first variable. -/
theorem IsEulerAdmissible.of_shortExact₃' (hS : S.ShortExact)
    (h₁ : IsEulerAdmissible.{w} k S.X₁ Y) (h₂ : IsEulerAdmissible.{w} k S.X₂ Y) :
    IsEulerAdmissible.{w} k S.X₃ Y := by
  obtain ⟨N₁, hN₁⟩ := h₁.isExtBounded.exists_bound
  obtain ⟨N₂, hN₂⟩ := h₂.isExtBounded.exists_bound
  exact ⟨h₁.isExtFinite.of_shortExact₃' hS h₂.isExtFinite,
    (hN₁.of_shortExact₃' hS hN₂).isExtBounded⟩

/-! ### Alternating Hom dimension of a finite resolution -/

namespace ExactStructure.FiniteResolution

variable {P : ObjectProperty C} {X Y : C}

/-- The alternating Hom dimension of a finite resolution against `Y`:
`dim Hom(P₀,Y) - dim Hom(P₁,Y) + ⋯ + (-1)ⁿ dim Hom(Pₙ,Y)`.

As with `TauCeti.truncatedExtEuler`, this definition is total: `Module.finrank` has its usual
zero fallback when a Hom space is not finite-dimensional. The theorems below assume Hom-finiteness,
so every summand there is an actual dimension. -/
noncomputable def homEuler (k : Type t) [Field k] [Linear k C] (Y : C) :
    ∀ {X : C}, (ExactStructure.abelian C).FiniteResolution P X → ℤ
  | X, .base _ => Module.finrank k (X ⟶ Y)
  | _, .step (Q := Q) _ _ _ _ _ r => Module.finrank k (Q ⟶ Y) - r.homEuler k Y

omit [HasExt.{w} C] in
/-- A length-zero resolution has Hom-Euler characteristic equal to its Hom dimension. -/
@[simp]
theorem homEuler_base (hX : P X) :
    (base (E := ExactStructure.abelian C) hX).homEuler k Y = Module.finrank k (X ⟶ Y) :=
  (rfl)

omit [HasExt.{w} C] in
/-- Prepending a resolving term subtracts the Hom-Euler characteristic of the remaining
resolution from the Hom dimension of that term. -/
@[simp]
theorem homEuler_step {K Q : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : (ExactStructure.abelian C).Conflation (ShortComplex.mk i p zero))
    (r : (ExactStructure.abelian C).FiniteResolution P K) :
    (step hQ i p zero hp r).homEuler k Y = Module.finrank k (Q ⟶ Y) - r.homEuler k Y :=
  (rfl)

/-- A finite resolution by projectives whose Hom spaces into `Y` are finite-dimensional makes
the resolved pair `(X,Y)` Euler-admissible. -/
theorem isEulerAdmissible
    (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → FiniteDimensional k (Z ⟶ Y)) :
    IsEulerAdmissible.{w} k X Y := by
  induction r with
  | @base X hX =>
      let _ : Projective X := (ExactStructure.abelian_isProjective_iff X).mp (hproj X hX)
      let _ := hHom X hX
      exact isEulerAdmissible_of_projective k X Y
  | @step K Q X hQ i p zero hp r ih =>
      let _ : Projective Q := (ExactStructure.abelian_isProjective_iff Q).mp (hproj Q hQ)
      let _ := hHom Q hQ
      exact ih.of_shortExact₃' ((ExactStructure.abelian_conflation _).mp hp)
        (isEulerAdmissible_of_projective k Q Y)

/-- **Finite-projective-resolution formula for the Ext-Euler characteristic.** The value of
`χ(X,Y)` is the alternating sum of the dimensions of `Hom(Pᵢ,Y)` along any finite `P`-resolution
of `X`, provided the `P`-objects are projective and those Hom spaces are finite-dimensional. -/
theorem extEuler_eq_homEuler
    (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → FiniteDimensional k (Z ⟶ Y))
    (h : IsEulerAdmissible.{w} k X Y) :
    extEuler.{w} k h = r.homEuler k Y := by
  induction r with
  | @base X hX =>
      let _ : Projective X := (ExactStructure.abelian_isProjective_iff X).mp (hproj X hX)
      exact extEuler_projective k h
  | @step K Q X hQ i p zero hp r ih =>
      let _ : Projective Q := (ExactStructure.abelian_isProjective_iff Q).mp (hproj Q hQ)
      let _ := hHom Q hQ
      have hK := r.isEulerAdmissible hproj hHom
      have hQ' := isEulerAdmissible_of_projective k Q Y
      have hadd := extEuler_shortExact₁ ((ExactStructure.abelian_conflation _).mp hp) Y hK hQ' h
      have hQeval := extEuler_projective k hQ'
      rw [homEuler_step, ← ih hK]
      omega

/-- The alternating Hom dimension is independent of the chosen finite projective resolution. -/
theorem homEuler_eq_homEuler
    (r s : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → FiniteDimensional k (Z ⟶ Y)) :
    r.homEuler k Y = s.homEuler k Y := by
  have h := r.isEulerAdmissible hproj hHom
  rw [← r.extEuler_eq_homEuler hproj hHom h, ← s.extEuler_eq_homEuler hproj hHom h]

end ExactStructure.FiniteResolution

end TauCeti
