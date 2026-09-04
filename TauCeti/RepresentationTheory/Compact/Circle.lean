/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Group.TypeTags
public import TauCeti.RepresentationTheory.Compact.Character.Basic
public import TauCeti.RepresentationTheory.LinearCharacter
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The circle group: Fourier monomials are its irreducible characters

The circle `AddCircle T` is a compact abelian group, so every irreducible representation of it is
one-dimensional and its own character. This file builds those representations from Mathlib's
Fourier monomials and checks that the general compact-group theory, specialized to the circle,
returns Mathlib's Fourier analysis on the nose.

Concretely, `fourierRep T n` is the continuous representation of the circle on `ℂ` in which the
group element `x` acts by multiplication by `fourier n x`. It is one-dimensional, hence
irreducible, and unitary because `fourier n x` has modulus one; its character is `fourier n` again.
Under those identifications:

* the `L²` inner product of two of these characters, computed for the normalized Haar measure of
  `TauCeti/RepresentationTheory/Compact/Haar.lean`, is Mathlib's `AddCircle.orthonormal_fourier`;
* the general first orthogonality relation `character_orthonormal_self` and the general second
  orthogonality relation `character_orthonormal_distinct` return the diagonal and off-diagonal
  halves of that same statement.

The last two are recorded as anonymous `example`s: they are consistency checks on the general
theory's normalization, not new API, and naming them would duplicate
`TauCeti.inner_characterLp_fourierRep`.

## Main definitions

* `TauCeti.fourierChar`: the `n`-th Fourier monomial as a linear character
  `Multiplicative (AddCircle T) →* ℂˣ` of the circle group.
* `TauCeti.fourierRep`: the `n`-th Fourier monomial as a one-dimensional continuous representation
  of the circle group.

## Main statements

* `TauCeti.haarProb_eq_haarAddCircle`: the normalized Haar measure of the circle group is Mathlib's
  `AddCircle.haarAddCircle`.
* `TauCeti.isUnitary_fourierRep`, `TauCeti.isIrreducible_fourierRep`: each `fourierRep T n` is a
  unitary irreducible representation.
* `TauCeti.character_fourierRep`: the character of `fourierRep T n` is `fourier n`.
* `TauCeti.contIntertwiningMap_fourierRep_eq_zero_of_ne`: for `m ≠ n` there is no nonzero
  continuous intertwiner `fourierRep T n → fourierRep T m`, so the Fourier representations are
  pairwise inequivalent.
* `TauCeti.orthonormal_characterLp_fourierRep`: **the character-orthonormality half of the
  acceptance criterion.** The characters of the `fourierRep T n` are an orthonormal family in `L²`
  of the circle group for normalized Haar measure; this is `AddCircle.orthonormal_fourier` read
  through the general compact-group packaging.

## Implementation notes

`fourierRep T n` acts by the scalar `fourierChar T n`, so its underlying representation is
`Representation.ofLinearCharacter (fourierChar T n)`
(`TauCeti.toRepresentation_fourierRep`); irreducibility and the character are then the
corresponding facts about a linear character, not fresh one-dimensional computations.

`ContRepresentation` is stated for a multiplicative monoid, while `AddCircle T` is additive, so the
group here is `Multiplicative (AddCircle T)`. The measure-theoretic instances that makes that type
usable as a compact group with Haar measure are in
`TauCeti/MeasureTheory/Group/TypeTags.lean`; they are definitional, so
`haarProb_eq_haarAddCircle` is just the uniqueness of a Haar probability measure applied on the
multiplicative side. Because `Multiplicative (AddCircle T)` and `AddCircle T` are the same type
with the same topology and σ-algebra, an integral over one is literally an integral over the other,
which is what lets `inner_characterLp_fourierRep` end in Mathlib's orthonormality statement.

What is *not* done here is the full Peter-Weyl half of the roadmap's circle acceptance criterion —
identifying `peterWeylBasis` with `AddCircle.fourierBasis` under the indexing equivalence
`Σ π, Fin 1 × Fin 1 ≃ ℤ`. That needs the exhaustion of the irreducibles of the circle, which is not
proved here: the statements below say that the `fourierRep T n` are pairwise inequivalent
irreducibles with orthonormal characters, not that there are no others.

This is the circle bullet of the `## Worked examples (acceptance criteria)` section of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose Layer 6 character theory is in
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean`. The mathematical development follows
Daniel Bump, *Lie Groups*, second edition, Chapter 2.

## Tags

circle group, Fourier series, character, Peter-Weyl
-/

public section

open MeasureTheory AddCircle
open scoped ComplexConjugate InnerProductSpace

namespace TauCeti

variable (T : ℝ)

/-- **The `n`-th Fourier monomial as a linear character of the circle group.** It is Mathlib's
`AddCircle.toCircle_addChar` precomposed with multiplication by `n`, read as a multiplicative
character valued in `ℂˣ`; `TauCeti.coe_fourierChar` identifies its value with `fourier n`. -/
noncomputable def fourierChar (n : ℤ) : Multiplicative (AddCircle T) →* ℂˣ :=
  Circle.toUnits.comp (toCircle_addChar.compAddMonoidHom (zsmulAddGroupHom n)).toMonoidHom

@[simp]
theorem coe_fourierChar (n : ℤ) (x : Multiplicative (AddCircle T)) :
    (fourierChar T n x : ℂ) = fourier n (Multiplicative.toAdd x) := (rfl)

/-- **The `n`-th Fourier character of the circle group**, as a one-dimensional continuous
representation on `ℂ`: the group element `x` acts by multiplication by `fourier n x`. -/
noncomputable def fourierRep (n : ℤ) : ContRepresentation ℂ (Multiplicative (AddCircle T)) ℂ :=
  .ofMonoidHom
    { toFun := fun x => (fourierChar T n x : ℂ) • (1 : ℂ →L[ℂ] ℂ)
      map_one' := ContinuousLinearMap.ext fun z => by simp
      map_mul' := fun x y => ContinuousLinearMap.ext fun z => by
        simp [mul_assoc] }

@[simp]
theorem fourierRep_apply (n : ℤ) (x : Multiplicative (AddCircle T)) (z : ℂ) :
    fourierRep T n x z = fourier n (Multiplicative.toAdd x) * z := (rfl)

/-- **The Fourier representation is the one-dimensional representation of its linear character.**
Everything about it that only depends on the scalar action -- irreducibility, the character -- is
read off from `Representation.ofLinearCharacter` through this identification. -/
theorem toRepresentation_fourierRep (n : ℤ) :
    (fourierRep T n).toRepresentation = Representation.ofLinearCharacter (fourierChar T n) :=
  MonoidHom.ext fun x => LinearMap.ext fun z => by
    rw [Representation.ofLinearCharacter_apply, coe_fourierChar]
    exact fourierRep_apply T n x z

/-- The Fourier representation is continuous: its action operator depends on the group element
through the continuous map `fourier n`. -/
theorem continuous_fourierRep (n : ℤ) : Continuous (fourierRep T n) :=
  Continuous.congr (f := fun x : Multiplicative (AddCircle T) =>
      (fourier n (Multiplicative.toAdd x) : ℂ) • (1 : ℂ →L[ℂ] ℂ))
    (((fourier n).continuous.comp continuous_id).smul continuous_const)
    fun _ => ContinuousLinearMap.ext fun _ => by simp

/-- The Fourier representation is unitary: multiplication by a number of modulus one is an
isometry of `ℂ`. -/
theorem isUnitary_fourierRep (n : ℤ) : ContRepresentation.IsUnitary (fourierRep T n) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro x z
  rw [fourierRep_apply, norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-- The Fourier representation is irreducible, being the one-dimensional representation of a
linear character. -/
theorem isIrreducible_fourierRep (n : ℤ) :
    Representation.IsIrreducible (fourierRep T n).toRepresentation := by
  rw [toRepresentation_fourierRep]
  infer_instance

/-- **The character of the `n`-th Fourier representation is `fourier n`.** A one-dimensional
representation is its own character; this is `Representation.char_ofLinearCharacter` read through
`TauCeti.toRepresentation_fourierRep`.

The equation is stated between continuous maps rather than pointwise because that is the spelling
`simp` can normalize with: `TauCeti.ContRepresentation.character_apply` is itself `@[simp]`, so a
pointwise `character (fourierRep T n) _ x = _` is not in simp-normal form and `simpNF` rejects the
tag on it, whereas the unapplied left-hand side is a subterm of the pointwise one and rewrites it
too. This is how `TauCeti.SU2.character_symPowerModel` is stated for the same reason. -/
@[simp]
theorem character_fourierRep (n : ℤ) :
    ContRepresentation.character (fourierRep T n) (continuous_fourierRep T n) = fourier n :=
  ContinuousMap.ext fun x => by
    have h : ContRepresentation.character (fourierRep T n) (continuous_fourierRep T n) x =
        (fourierRep T n).toRepresentation.character x :=
      congrFun (ContRepresentation.coe_character _ _) x
    rw [h, toRepresentation_fourierRep, Representation.char_ofLinearCharacter]
    -- `Multiplicative (AddCircle T)` is `AddCircle T`, so `fourier n (Multiplicative.toAdd x)`
    -- and `fourier n x` are the same term.
    exact coe_fourierChar T n x

/-- **The Fourier representations are pairwise inequivalent.** For `m ≠ n` every continuous
intertwiner `fourierRep T n → fourierRep T m` vanishes: such a map is multiplication by its value
`c` at `1`, and intertwining forces `fourier n x * c = fourier m x * c` for every `x`, so `c = 0`
by `TauCeti.fourier_injective`.

This is the hypothesis of the general second orthogonality relation
`TauCeti.ContRepresentation.character_orthonormal_distinct`. -/
theorem contIntertwiningMap_fourierRep_eq_zero_of_ne (hT : T ≠ 0) {m n : ℤ} (h : m ≠ n)
    (f : ContIntertwiningMap (fourierRep T n) (fourierRep T m)) :
    f.toContinuousLinearMap = 0 := by
  have hlin : ∀ c : ℂ, f.toContinuousLinearMap c = c * f.toContinuousLinearMap 1 := fun c => by
    simpa using f.toContinuousLinearMap.map_smul c (1 : ℂ)
  have hone : f.toContinuousLinearMap (1 : ℂ) = 0 := by
    by_contra hne
    refine (fun hc => h (fourier_injective (T := T) hT hc)) ?_
    ext x
    have hx := congrArg (fun g : ℂ →L[ℂ] ℂ => g 1)
      (f.isIntertwining' (Multiplicative.ofAdd x))
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, fourierRep_apply,
      mul_one] at hx
    refine (mul_right_cancel₀ hne ?_).symm
    calc fourier n x * f.toContinuousLinearMap 1
        = f.toContinuousLinearMap (fourier n x) := (hlin _).symm
      _ = fourier m x * f.toContinuousLinearMap 1 := hx
  refine ContinuousLinearMap.ext fun z => ?_
  simp [hlin z, hone]

variable [hT : Fact (0 < T)]

/-- **Normalized Haar measure on the circle group is Mathlib's `AddCircle.haarAddCircle`.** Both
are Haar probability measures on a compact group, and there is only one such. -/
theorem haarProb_eq_haarAddCircle :
    haarProb (Multiplicative (AddCircle T)) = haarAddCircle :=
  (eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure
    (G := Multiplicative (AddCircle T)) haarAddCircle).symm

/-- **The `L²` inner product of two Fourier characters is Mathlib's Fourier orthonormality.** Both
sides are the Haar integral of `fourier n · conj (fourier m)`; the left is that integral written
for the general compact-group packaging of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean`, the right is
`AddCircle.orthonormal_fourier`. -/
theorem inner_characterLp_fourierRep (m n : ℤ) :
    ⟪ContRepresentation.characterLp (fourierRep T m) (continuous_fourierRep T m),
      ContRepresentation.characterLp (fourierRep T n) (continuous_fourierRep T n)⟫_ℂ =
      if m = n then 1 else 0 := by
  have key : ∫ x : AddCircle T, fourier n x * conj (fourier m x) ∂haarAddCircle =
      if m = n then 1 else 0 := by
    rw [← ContinuousMap.inner_toLp haarAddCircle (fourier m) (fourier n)]
    exact orthonormal_iff_ite.mp orthonormal_fourier m n
  rw [ContRepresentation.characterLp_def, ContRepresentation.characterLp_def,
    ContinuousMap.inner_toLp, haarProb_eq_haarAddCircle]
  simp only [character_fourierRep]
  exact key

/-- **The character-orthonormality half of the acceptance criterion.** The characters of the
Fourier representations are an orthonormal family in `L²` of the circle group for normalized Haar
measure: the general compact-group character theory, specialized to the circle, is Mathlib's
`AddCircle.orthonormal_fourier`. The remaining half, the identification of `peterWeylBasis` with
`AddCircle.fourierBasis`, is not proved here. -/
theorem orthonormal_characterLp_fourierRep :
    Orthonormal ℂ fun n : ℤ =>
      ContRepresentation.characterLp (fourierRep T n) (continuous_fourierRep T n) :=
  orthonormal_iff_ite.mpr fun m n => inner_characterLp_fourierRep T m n

-- The general first orthogonality relation returns the diagonal half of `orthonormal_fourier`.
example (n : ℤ) :
    ‖ContRepresentation.characterLp (fourierRep T n) (continuous_fourierRep T n)‖ = 1 :=
  ContRepresentation.norm_characterLp_eq_one _ _ (isUnitary_fourierRep T n)
    (isIrreducible_fourierRep T n)

-- The general second orthogonality relation returns the off-diagonal half.
example {m n : ℤ} (h : m ≠ n) :
    ⟪ContRepresentation.characterLp (fourierRep T m) (continuous_fourierRep T m),
      ContRepresentation.characterLp (fourierRep T n) (continuous_fourierRep T n)⟫_ℂ = 0 :=
  ContRepresentation.character_orthonormal_distinct _ _ _ _ (isUnitary_fourierRep T m)
    (contIntertwiningMap_fourierRep_eq_zero_of_ne T hT.out.ne' h)

end TauCeti
