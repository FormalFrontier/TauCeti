/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
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

The hypotheses are conditions on the object property `P` along which the resolution is taken:
every object satisfying `P` is projective and has a finite-dimensional Hom space into `Y`.
Projectivity makes the higher `Ext` groups of the resolving terms vanish, and bounds the
projective dimension of `X` by the length of the resolution. The long exact Ext sequence then
proves, from the far end of the resolution towards `X`, both that `(X, Y)` is Euler-admissible
and that the displayed formula holds.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.homEuler`: the alternating Hom dimension of the terms
  of a finite resolution.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.hasProjectiveDimensionLT`: a finite resolution by
  projectives bounds the projective dimension of the resolved object by its length.
* `TauCeti.ExactStructure.FiniteResolution.isExtBoundedBy` and
  `TauCeti.ExactStructure.FiniteResolution.isExtFinite`: the two halves of Euler-admissibility,
  with the explicit vanishing bound `r.length + 1`; they are packaged as
  `TauCeti.ExactStructure.FiniteResolution.isEulerAdmissible`.
* `TauCeti.ExactStructure.FiniteResolution.extEuler_eq_homEuler`: every admissibility witness gives
  the Ext-Euler characteristic as the alternating Hom dimension of the resolution.
* `TauCeti.ExactStructure.FiniteResolution.homEuler_eq_homEuler`: any two finite resolutions of
  `X`, along object properties consisting of projectives with finite-dimensional Hom spaces into
  `Y`, have the same alternating Hom dimension.

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

namespace ExactStructure.FiniteResolution

/-! ### Alternating Hom dimension of a finite resolution -/

variable {E : ExactStructure C} {P : ObjectProperty C} {X Y : C}

/-- The alternating Hom dimension of a finite resolution against `Y`:
`dim Hom(P₀,Y) - dim Hom(P₁,Y) + ⋯ + (-1)ⁿ dim Hom(Pₙ,Y)`.

As with `TauCeti.truncatedExtEuler`, this definition is total: `Module.finrank` has its usual
zero fallback when a Hom space is not finite-dimensional. The theorems below assume Hom-finiteness,
so every summand there is an actual dimension. -/
noncomputable def homEuler (k : Type t) [Field k] [Linear k C] (Y : C) {X : C}
    (r : E.FiniteResolution P X) : ℤ :=
  r.foldAlternating fun Z _ ↦ (Module.finrank k (Z ⟶ Y) : ℤ)

omit [HasExt.{w} C] in
/-- A length-zero resolution has Hom-Euler characteristic equal to its Hom dimension. -/
@[simp]
theorem homEuler_base (hX : P X) :
    (base (E := E) hX).homEuler k Y = Module.finrank k (X ⟶ Y) :=
  foldAlternating_base _ hX

omit [HasExt.{w} C] in
/-- Prepending a resolving term subtracts the Hom-Euler characteristic of the remaining
resolution from the Hom dimension of that term. -/
@[simp]
theorem homEuler_step {K Q : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : E.Conflation (ShortComplex.mk i p zero)) (r : E.FiniteResolution P K) :
    (step hQ i p zero hp r).homEuler k Y = Module.finrank k (Q ⟶ Y) - r.homEuler k Y :=
  foldAlternating_step _ hQ i p zero hp r

/-! ### Euler-admissibility along a projective resolution -/

omit [HasExt.{w} C] in
/-- A finite resolution by projectives bounds the projective dimension of the resolved object by
its length: the resolving terms have projective dimension `< 1`, and each conflation of the chain
raises the bound by one through
`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`. -/
theorem hasProjectiveDimensionLT (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective) :
    HasProjectiveDimensionLT X (r.length + 1) := by
  induction r with
  | @base X hX =>
      have : Projective X := (ExactStructure.abelian_isProjective_iff X).mp (hproj X hX)
      exact hasProjectiveDimensionLT_of_ge X 1 _ (by omega)
  | @step K Q X hQ i p zero hp r ih =>
      have : Projective Q := (ExactStructure.abelian_isProjective_iff Q).mp (hproj Q hQ)
      have hQ' : HasProjectiveDimensionLT Q (r.length + 1 + 1) :=
        hasProjectiveDimensionLT_of_ge Q 1 _ (by omega)
      rw [length_step]
      exact ((ExactStructure.abelian_conflation _).mp hp).hasProjectiveDimensionLT_X₃
        (r.length + 1) ih hQ'

/-- The `Ext` groups out of an object with a finite projective resolution vanish from degree
`r.length + 1` on. Only projectivity of the `P`-objects is used; no Hom-finiteness is needed. -/
theorem isExtBoundedBy (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective) :
    IsExtBoundedBy.{w} X Y (r.length + 1) :=
  have := r.hasProjectiveDimensionLT hproj
  ⟨fun _ hn ↦ HasProjectiveDimensionLT.subsingleton X (r.length + 1) _ hn Y⟩

/-- The `Ext` groups out of an object with a finite resolution whose `P`-objects are projective
and have finite-dimensional Hom spaces into `Y` are finite-dimensional. -/
theorem isExtFinite (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → FiniteDimensional k (Z ⟶ Y)) :
    IsExtFinite.{w} k X Y := by
  induction r with
  | @base X hX =>
      have : Projective X := (ExactStructure.abelian_isProjective_iff X).mp (hproj X hX)
      have := hHom X hX
      exact isExtFinite_of_projective k X Y
  | @step K Q X hQ i p zero hp r ih =>
      have : Projective Q := (ExactStructure.abelian_isProjective_iff Q).mp (hproj Q hQ)
      have := hHom Q hQ
      exact ih.of_shortExact₃' ((ExactStructure.abelian_conflation _).mp hp)
        (isExtFinite_of_projective k Q Y)

/-- A finite resolution along an object property whose objects are projective and have
finite-dimensional Hom spaces into `Y` makes the resolved pair `(X,Y)` Euler-admissible. -/
theorem isEulerAdmissible (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → FiniteDimensional k (Z ⟶ Y)) :
    IsEulerAdmissible.{w} k X Y :=
  ⟨r.isExtFinite hproj hHom, (r.isExtBoundedBy (Y := Y) hproj).isExtBounded⟩

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
      have : Projective X := (ExactStructure.abelian_isProjective_iff X).mp (hproj X hX)
      rw [homEuler_base]
      exact extEuler_projective k h
  | @step K Q X hQ i p zero hp r ih =>
      have : Projective Q := (ExactStructure.abelian_isProjective_iff Q).mp (hproj Q hQ)
      have := hHom Q hQ
      have hK := r.isEulerAdmissible hproj hHom
      have hQ' := isEulerAdmissible_of_projective k Q Y
      have hadd := extEuler_shortExact₁ ((ExactStructure.abelian_conflation _).mp hp) Y hK hQ' h
      have hQeval := extEuler_projective k hQ'
      rw [homEuler_step, ← ih hK]
      omega

/-- The alternating Hom dimension is the same along any two finite resolutions of `X` taken along
object properties whose objects are projective and have finite-dimensional Hom spaces into `Y`. -/
theorem homEuler_eq_homEuler {P' : ObjectProperty C}
    (r : (ExactStructure.abelian C).FiniteResolution P X)
    (s : (ExactStructure.abelian C).FiniteResolution P' X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → FiniteDimensional k (Z ⟶ Y))
    (hproj' : P' ≤ (ExactStructure.abelian C).isProjective)
    (hHom' : ∀ Z, P' Z → FiniteDimensional k (Z ⟶ Y)) :
    r.homEuler k Y = s.homEuler k Y := by
  have h := r.isEulerAdmissible hproj hHom
  rw [← r.extEuler_eq_homEuler hproj hHom h, ← s.extEuler_eq_homEuler hproj' hHom' h]

end ExactStructure.FiniteResolution

end TauCeti
