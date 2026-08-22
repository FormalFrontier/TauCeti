/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution
public import TauCeti.CategoryTheory.GrothendieckGroup.Exact

/-!
# The Euler class of a finite resolution

For a finite `P`-resolution of an object `X` of an exact category, the *Euler class* is the
alternating sum

```text
[Q₀] - [Q₁] + ⋯ + (-1)ⁿ⁻¹ [Qₙ₋₁] + (-1)ⁿ [Kₙ]
```

of the classes of its resolving terms and its last syzygy in exact `K₀`. The conflation relation
telescopes the alternating sum, so the Euler class of a resolution of `X` is `[X]`. This is the
computation that makes the Euler class independent of the chosen resolution -- of its length, of
zero padding, and of every other choice -- and it is the first half of Weibel's resolution
theorem: it exhibits `[X]` as an integral combination of classes of objects satisfying `P`, so
those classes generate exact `K₀` as soon as every object admits a finite `P`-resolution.

The second half, that the comparison map from the exact `K₀` of the full subcategory on `P` is
also injective, needs the resolving hypotheses on `P` and Weibel's common-refinement argument,
and is not proved here.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.eulerClass`: the alternating class of a finite
  resolution in exact `K₀`.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.eulerClass_eq_of`: the Euler class of a resolution of
  `X` is the class of `X`; `TauCeti.ExactStructure.FiniteResolution.eulerClass_eq_eulerClass` is
  the resulting independence of the resolution.
* `TauCeti.ExactK0.mem_propClasses_iff`: membership in the generator set `propClasses E P` is
  being the class of an object satisfying `P`.
* `TauCeti.ExactK0.closure_propClasses_eq_top`: if every object admits a finite `P`-resolution,
  the classes of the objects satisfying `P` generate exact `K₀`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Theorem 7.6 and Lemma 7.6.1, the resolution theorem and the telescoping computation of the
  Euler class used here.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C] {E : ExactStructure C} {P : ObjectProperty C}

namespace ExactStructure.FiniteResolution

/-- The Euler class of a finite `P`-resolution: the alternating sum of the classes of its
resolving terms, ending with the class of its last syzygy. -/
noncomputable def eulerClass :
    ∀ {X : C}, E.FiniteResolution P X → ExactK0 E
  | X, .base _ => ExactK0.of X
  | _, .step (Q := Q) _ _ _ _ _ r => ExactK0.of Q - r.eulerClass

@[simp] theorem eulerClass_base {X : C} (hX : P X) :
    (base (E := E) hX).eulerClass = ExactK0.of X := (rfl)

@[simp] theorem eulerClass_step {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : E.FiniteResolution P K) :
    (step hQ i p zero hp r).eulerClass = ExactK0.of Q - r.eulerClass := (rfl)

/-- **The Euler class of a resolution of `X` is the class of `X`.** The conflation relation
telescopes the alternating sum. -/
theorem eulerClass_eq_of {X : C} (r : E.FiniteResolution P X) :
    r.eulerClass = ExactK0.of X := by
  induction r with
  | base hX => rfl
  | step hQ i p zero hp r ih =>
      rw [eulerClass_step, ih, ExactK0.of_eq_add_of_conflation zero hp]
      abel

/-- The Euler class does not depend on the resolution: any two finite `P`-resolutions of the same
object have the same Euler class, whatever their lengths. -/
theorem eulerClass_eq_eulerClass {X : C} (r s : E.FiniteResolution P X) :
    r.eulerClass = s.eulerClass := by
  rw [eulerClass_eq_of, eulerClass_eq_of]

@[simp] theorem eulerClass_ofIso [P.IsClosedUnderIsomorphisms] {X Y : C} (e : X ≅ Y)
    (r : E.FiniteResolution P X) : (ofIso e r).eulerClass = r.eulerClass := by
  rw [eulerClass_eq_of, eulerClass_eq_of, ExactK0.of_congr e]

@[simp] theorem eulerClass_zeroPad [P.IsClosedUnderIsomorphisms] [P.ContainsZero] {X : C}
    (r : E.FiniteResolution P X) : r.zeroPad.eulerClass = r.eulerClass := by
  rw [eulerClass_eq_of, eulerClass_eq_of]

@[simp] theorem eulerClass_pad [P.IsClosedUnderIsomorphisms] [P.ContainsZero] {X : C}
    (r : E.FiniteResolution P X) (n : ℕ) : (r.pad n).eulerClass = r.eulerClass := by
  rw [eulerClass_eq_of, eulerClass_eq_of]

@[simp] theorem eulerClass_biprod [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]
    {X Y : C} (r : E.FiniteResolution P X) (s : E.FiniteResolution P Y) :
    (r.biprod s).eulerClass = r.eulerClass + s.eulerClass := by
  rw [eulerClass_eq_of, eulerClass_eq_of, eulerClass_eq_of, ExactK0.of_biprod]

end ExactStructure.FiniteResolution

namespace ExactK0

variable (E P) in
/-- The classes of the objects satisfying `P`, as a subset of exact `K₀`. -/
def propClasses : Set (ExactK0 E) := (ExactK0.of (E := E)) '' {X : C | P X}

/-- Membership in the generator set `propClasses E P`: an element of exact `K₀` lies in it
exactly when it is the class of an object satisfying `P`. -/
@[simp] theorem mem_propClasses_iff {x : ExactK0 E} :
    x ∈ propClasses E P ↔ ∃ Q : C, P Q ∧ (ExactK0.of Q : ExactK0 E) = x := by
  simp [propClasses]

/-- The class of an object satisfying `P` is one of the generators `propClasses E P`. -/
theorem of_mem_propClasses {Q : C} (hQ : P Q) : (ExactK0.of Q : ExactK0 E) ∈ propClasses E P :=
  ⟨Q, hQ, rfl⟩

/-- The class of an object admitting a finite `P`-resolution is an integral combination of
classes of objects satisfying `P`. -/
theorem of_mem_closure_propClasses {X : C} (hX : E.admitsFiniteResolution P X) :
    (ExactK0.of X : ExactK0 E) ∈ AddSubgroup.closure (propClasses E P) := by
  refine E.admitsFiniteResolution_induction (P := P)
    (motive := fun X => (ExactK0.of X : ExactK0 E) ∈ AddSubgroup.closure (propClasses E P))
    (fun Q hQ => AddSubgroup.subset_closure (of_mem_propClasses hQ)) ?_ hX
  intro K Q X hQ i p zero hp hK
  rw [of_eq_sub_of_conflation (S := ShortComplex.mk i p zero) hp] at hK
  have hQ' : (ExactK0.of Q : ExactK0 E) ∈ AddSubgroup.closure (propClasses E P) :=
    AddSubgroup.subset_closure (of_mem_propClasses hQ)
  simpa using AddSubgroup.sub_mem _ hQ' hK

variable (E P) in
/-- **The generating half of the resolution theorem.** If every object of `C` admits a finite
`P`-resolution, then the classes of the objects satisfying `P` generate exact `K₀`. -/
theorem closure_propClasses_eq_top (h : ∀ X : C, E.admitsFiniteResolution P X) :
    AddSubgroup.closure (propClasses E P) = ⊤ := by
  rw [eq_top_iff, ← ExactK0.closure_range_of, AddSubgroup.closure_le]
  rintro _ ⟨X, rfl⟩
  exact of_mem_closure_propClasses (h X)

end ExactK0

end TauCeti
