/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Split
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite resolutions in an exact category

Let `E` be an exact structure on an additive category `C` and let `P` be a property of objects
of `C`. A *finite `P`-resolution* of an object `X` is a finite chain of `E`-conflations

```text
K₁ ↪ Q₀ ↠ X,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁
```

whose resolving terms `Q₀, …, Qₙ₋₁` and whose last syzygy `Kₙ` all satisfy `P`. Equivalently, it
is a bounded exact augmented complex `0 → Kₙ → Qₙ₋₁ → ⋯ → Q₀ → X → 0` built from conflations.
`TauCeti.ExactStructure.FiniteResolution` records exactly that chain, as data, by recursion on
its length.

This file is the reusable resolution vocabulary in which the resolution theorem is stated. It
develops the operations a later Euler-class argument needs -- length, syzygies and truncation,
transport along an isomorphism, zero padding, and direct sums -- for an arbitrary object
property, before any projectivity hypothesis is available.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution E P X`: a finite `P`-resolution of `X`, as data.
* `TauCeti.ExactStructure.FiniteResolution.length`: the number of conflations in the chain.
* `TauCeti.ExactStructure.FiniteResolution.syzygy` and
  `TauCeti.ExactStructure.FiniteResolution.truncate`: the `n`-th syzygy of a resolution, and the
  resolution of it obtained by discarding the first `n` conflations.
* `TauCeti.ExactStructure.FiniteResolution.ofIso`: transport along an isomorphism of the resolved
  object.
* `TauCeti.ExactStructure.FiniteResolution.zeroPad` and
  `TauCeti.ExactStructure.FiniteResolution.pad`: lengthen a resolution by adjoining trivial
  conflations `0 ↪ Kₙ ↠ Kₙ` at its far end.
* `TauCeti.ExactStructure.FiniteResolution.biprod`: the componentwise direct sum of two
  resolutions.
* `TauCeti.ExactStructure.admitsFiniteResolution`: the object property of admitting some finite
  `P`-resolution, the object-property presentation of the above data.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.syzygy_truncate` and
  `TauCeti.ExactStructure.FiniteResolution.syzygy_eq_syzygy_length_of_length_le`: truncating
  shifts the syzygies, and they stabilise at the last one past the length.
* `TauCeti.ExactStructure.FiniteResolution.prop_syzygy_length`: the last syzygy of a resolution
  satisfies `P`; more generally `TauCeti.ExactStructure.FiniteResolution.prop_syzygy` covers
  every index beyond the length.
* `TauCeti.ExactStructure.FiniteResolution.length_biprod`: a direct sum of resolutions has the
  larger of the two lengths, the shorter chain being padded against the longer one.
* `TauCeti.ExactStructure.admitsFiniteResolution_induction`: the object property of admitting a
  finite `P`-resolution is the smallest one containing `P` and closed under passing from the
  subobject of a conflation with resolving middle term to its quotient.

## Implementation notes

The recursion is on the *deep* end of the chain: `TauCeti.ExactStructure.FiniteResolution.base`
is a resolution of length zero of an object already satisfying `P`, and
`TauCeti.ExactStructure.FiniteResolution.step` prepends one conflation `K ↪ Q ↠ X` to a
resolution of `K`. This is the presentation in which zero padding is the operation that rewrites
the `base` leaf, and it is the one the roadmap's `AdmitsFiniteResolutionAlong` uses. The
conflations are stored by their two maps rather than as a `CategoryTheory.ShortComplex`, so that
the resolved object is a genuine index of the family and `FiniteResolution E P X` never needs an
equality of objects to be matched on.

Every operation is sealed behind its `@[simp]` equations, with one exception:
`TauCeti.ExactStructure.FiniteResolution.syzygy` is the type index of
`TauCeti.ExactStructure.FiniteResolution.truncate`, so the statements of the `truncate` equations
only typecheck when its body is exposed.

The closure hypotheses on `P` are Mathlib's object-property type classes, and are assumed only
where they are used: repleteness for `ofIso`, `CategoryTheory.ObjectProperty.ContainsZero` for
padding, and closure under binary products for direct sums, the last of these reaching
biproducts through `CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan` applied to
`CategoryTheory.Limits.BinaryBiproduct.isLimit`. The resolving-subcategory package,
which bundles these with extension closure and closure under kernels of deflations, is
downstream.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  where finite resolutions by a resolving subcategory and the resolution theorem are developed.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Sections
  11--12, for resolutions in a Quillen exact category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- A finite `P`-resolution of an object `X` of an exact category: a finite chain of conflations

```text
K₁ ↪ Q₀ ↠ X,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁
```

whose resolving terms `Qᵢ` satisfy `P`, ending at a syzygy `Kₙ` which satisfies `P` as well.
The recursion is on the deep end: `base` is the empty chain, available when `X` already
satisfies `P`, and `step` prepends one conflation to a resolution of its subobject. -/
inductive FiniteResolution (E : ExactStructure C) (P : ObjectProperty C) : C → Type (max u v)
  /-- An object satisfying `P` is its own resolution, of length zero. -/
  | base {X : C} (hX : P X) : FiniteResolution E P X
  /-- Prepend a conflation `K ↪ Q ↠ X` with resolving term `Q` to a resolution of `K`. -/
  | step {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
      (hp : E.Conflation (ShortComplex.mk i p zero)) (r : FiniteResolution E P K) :
      FiniteResolution E P X

namespace FiniteResolution

variable {E} {P : ObjectProperty C}

/-- The length of a resolution: the number of conflations in its chain. -/
def length : ∀ {X : C}, FiniteResolution E P X → ℕ
  | _, .base _ => 0
  | _, .step _ _ _ _ _ r => r.length + 1

@[simp] theorem length_base {X : C} (hX : P X) : (base (E := E) hX).length = 0 := (rfl)

@[simp] theorem length_step {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : E.Conflation (ShortComplex.mk i p zero)) (r : FiniteResolution E P K) :
    (step hQ i p zero hp r).length = r.length + 1 := (rfl)

/-- The `n`-th syzygy of a resolution of `X`: the object resolved by what is left after
discarding the first `n` conflations. It is `X` itself for `n = 0`, and it stabilises at the
last syzygy once `n` reaches the length. -/
@[expose] def syzygy : ∀ {X : C}, FiniteResolution E P X → ℕ → C
  | X, .base _, _ => X
  | X, .step _ _ _ _ _ _, 0 => X
  | _, .step _ _ _ _ _ r, n + 1 => r.syzygy n

@[simp] theorem syzygy_base {X : C} (hX : P X) (n : ℕ) :
    (base (E := E) hX).syzygy n = X := rfl

@[simp] theorem syzygy_zero {X : C} (r : FiniteResolution E P X) : r.syzygy 0 = X := by
  cases r <;> rfl

@[simp] theorem syzygy_step_succ {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) (n : ℕ) :
    (step hQ i p zero hp r).syzygy (n + 1) = r.syzygy n := rfl

/-- The truncation of a resolution below degree `n`: the chain that remains after discarding the
first `n` conflations, a resolution of the `n`-th syzygy. -/
def truncate : ∀ {X : C} (r : FiniteResolution E P X) (n : ℕ),
    FiniteResolution E P (r.syzygy n)
  | _, .base hX, _ => .base hX
  | _, .step hQ i p zero hp r, 0 => .step hQ i p zero hp r
  | _, .step _ _ _ _ _ r, n + 1 => r.truncate n

@[simp] theorem truncate_base {X : C} (hX : P X) (n : ℕ) :
    (base (E := E) hX).truncate n = base hX := by
  cases n <;> rfl

@[simp] theorem truncate_step_zero {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) :
    (step hQ i p zero hp r).truncate 0 = step hQ i p zero hp r := (rfl)

@[simp] theorem truncate_step_succ {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) (n : ℕ) :
    (step hQ i p zero hp r).truncate (n + 1) = r.truncate n := (rfl)

/-- The syzygies of a truncation are the syzygies of the original chain, shifted. -/
@[simp] theorem syzygy_truncate {X : C} (r : FiniteResolution E P X) (n m : ℕ) :
    (r.truncate n).syzygy m = r.syzygy (n + m) := by
  induction r generalizing n with
  | base hX => simp
  | step hQ i p zero hp r ih =>
      cases n with
      | zero =>
          simp only [truncate_step_zero, Nat.zero_add]
          -- the two sides now differ only in the type index `(step … r).syzygy 0`, which is `X`
          rfl
      | succ n => simpa [Nat.succ_add] using ih n

@[simp] theorem length_truncate {X : C} (r : FiniteResolution E P X) (n : ℕ) :
    (r.truncate n).length = r.length - n := by
  induction r generalizing n with
  | base hX => cases n <;> simp
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => rfl
      | succ n => simpa using ih n

/-- Once the index reaches the length, the syzygies stabilise at the last one. -/
theorem syzygy_eq_syzygy_length_of_length_le {X : C} (r : FiniteResolution E P X) {n : ℕ}
    (hn : r.length ≤ n) : r.syzygy n = r.syzygy r.length := by
  induction r generalizing n with
  | base hX => simp
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => simp at hn
      | succ n => simpa using ih (by simpa using hn)

/-- Every syzygy of index at least the length satisfies `P`: the chain has run out. -/
theorem prop_syzygy {X : C} (r : FiniteResolution E P X) {n : ℕ} (hn : r.length ≤ n) :
    P (r.syzygy n) := by
  induction r generalizing n with
  | base hX => exact hX
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => simp at hn
      | succ n => exact ih (by simpa using hn)

/-- The last syzygy of a resolution satisfies `P`. -/
theorem prop_syzygy_length {X : C} (r : FiniteResolution E P X) : P (r.syzygy r.length) :=
  r.prop_syzygy le_rfl

section Iso

variable [P.IsClosedUnderIsomorphisms]

/-- Transport a resolution along an isomorphism of the resolved object. -/
def ofIso : ∀ {X Y : C}, (X ≅ Y) → FiniteResolution E P X → FiniteResolution E P Y
  | _, _, e, .base hX => .base (P.prop_of_iso e hX)
  | _, _, e, .step hQ i p zero hp r =>
      .step hQ i (p ≫ e.hom) (by rw [← Category.assoc, zero, zero_comp])
        (E.conflation_of_iso (S := ShortComplex.mk i p zero)
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp)) hp) r

@[simp] theorem ofIso_base {X Y : C} (e : X ≅ Y) (hX : P X) :
    ofIso (E := E) e (base hX) = base (P.prop_of_iso e hX) := by
  simp [ofIso]

@[simp] theorem ofIso_step {K Q X Y : C} (e : X ≅ Y) (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) :
    ofIso e (step hQ i p zero hp r) =
      step hQ i (p ≫ e.hom) (by rw [← Category.assoc, zero, zero_comp])
        (E.conflation_of_iso (S := ShortComplex.mk i p zero)
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp)) hp) r := by
  simp [ofIso]

@[simp] theorem length_ofIso {X Y : C} (e : X ≅ Y) (r : FiniteResolution E P X) :
    (ofIso e r).length = r.length := by
  cases r <;> simp [ofIso]

end Iso

section Pad

variable [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

/-- Lengthen a resolution by one, adjoining the trivial conflation `0 ↪ Kₙ ↠ Kₙ` at its last
syzygy. -/
noncomputable def zeroPad :
    ∀ {X : C}, FiniteResolution E P X → FiniteResolution E P X
  | X, .base hX =>
      .step hX (0 : (0 : C) ⟶ X) (𝟙 X) (by simp) (E.conflation_zero_id X) (.base P.prop_zero)
  | _, .step hQ i p zero hp r => .step hQ i p zero hp r.zeroPad

@[simp] theorem zeroPad_base {X : C} (hX : P X) :
    (base (E := E) hX).zeroPad =
      step hX (0 : (0 : C) ⟶ X) (𝟙 X) (by simp) (E.conflation_zero_id X)
        (base P.prop_zero) := by
  simp [zeroPad]

@[simp] theorem zeroPad_step {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : E.Conflation (ShortComplex.mk i p zero)) (r : FiniteResolution E P K) :
    (step hQ i p zero hp r).zeroPad = step hQ i p zero hp r.zeroPad := by
  simp [zeroPad]

@[simp] theorem length_zeroPad {X : C} (r : FiniteResolution E P X) :
    r.zeroPad.length = r.length + 1 := by
  induction r with
  | base hX => simp [zeroPad]
  | step hQ i p zero hp r ih => simpa [zeroPad] using ih

/-- Zero padding does not change the syzygies in the original resolution. -/
@[simp] theorem syzygy_zeroPad_of_le_length {X : C} (r : FiniteResolution E P X) {n : ℕ}
    (hn : n ≤ r.length) : r.zeroPad.syzygy n = r.syzygy n := by
  induction r generalizing n with
  | base hX => simp_all
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => simp
      | succ n => simpa using ih (by simpa using hn)

/-- After the original resolution ends, every syzygy of its zero padding is the zero object. -/
@[simp] theorem syzygy_zeroPad_of_length_lt {X : C} (r : FiniteResolution E P X) {n : ℕ}
    (hn : r.length < n) : r.zeroPad.syzygy n = (0 : C) := by
  induction r generalizing n with
  | base hX =>
      cases n with
      | zero => simp at hn
      | succ n => simp
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => simp at hn
      | succ n => simpa using ih (by simpa using hn)

/-- Lengthen a resolution by `n`, adjoining `n` trivial conflations at its last syzygy. -/
noncomputable def pad {X : C} (r : FiniteResolution E P X) :
    ℕ → FiniteResolution E P X
  | 0 => r
  | n + 1 => (r.pad n).zeroPad

@[simp] theorem pad_zero {X : C} (r : FiniteResolution E P X) : r.pad 0 = r := by
  simp [pad]

@[simp] theorem pad_succ {X : C} (r : FiniteResolution E P X) (n : ℕ) :
    r.pad (n + 1) = (r.pad n).zeroPad := by
  simp [pad]

@[simp] theorem length_pad {X : C} (r : FiniteResolution E P X) (n : ℕ) :
    (r.pad n).length = r.length + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pad, ih, Nat.add_assoc]

/-- Iterated padding does not change the syzygies in the original resolution. -/
@[simp] theorem syzygy_pad_of_le_length {X : C} (r : FiniteResolution E P X) (m : ℕ) {n : ℕ}
    (hn : n ≤ r.length) : (r.pad m).syzygy n = r.syzygy n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pad_succ, syzygy_zeroPad_of_le_length]
      · exact ih
      · simpa using hn.trans (Nat.le_add_right r.length m)

/-- After the original resolution ends, every syzygy of a positive padding is the zero object. -/
theorem syzygy_pad_succ_of_length_lt {X : C} (r : FiniteResolution E P X) (m : ℕ)
    {n : ℕ} (hn : r.length < n) : (r.pad (m + 1)).syzygy n = (0 : C) := by
  induction m with
  | zero => simpa using syzygy_zeroPad_of_length_lt r hn
  | succ m ih =>
      rw [pad_succ]
      by_cases h : n ≤ (r.pad (m + 1)).length
      · rw [syzygy_zeroPad_of_le_length _ h]
        exact ih
      · exact syzygy_zeroPad_of_length_lt _ (Nat.lt_of_not_ge h)

end Pad

section Biprod

variable [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]

/-- The componentwise direct sum of two finite `P`-resolutions. Where one chain has run out, it
is padded against the other by the trivial conflation on its last syzygy. -/
noncomputable def biprod :
    ∀ {X Y : C}, FiniteResolution E P X → FiniteResolution E P Y →
      FiniteResolution E P (X ⊞ Y)
  | _, _, .base hX, .base hY =>
      .base (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hX hY)
  | X, _, .base hX, .step hQ i p zero hp s =>
      .step (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hX hQ)
        (Limits.biprod.map (0 : (0 : C) ⟶ X) i) (Limits.biprod.map (𝟙 X) p)
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero])
        (E.conflation_biprod (E.conflation_zero_id X) hp)
        (s.ofIso (isoZeroBiprod (isZero_zero C)))
  | _, Y, .step hQ i p zero hp r, .base hY =>
      .step (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hQ hY)
        (Limits.biprod.map i (0 : (0 : C) ⟶ Y)) (Limits.biprod.map p (𝟙 Y))
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero])
        (E.conflation_biprod hp (E.conflation_zero_id Y))
        (r.ofIso (isoBiprodZero (isZero_zero C)))
  | _, _, .step hQ i p zero hp r, .step hQ' i' p' zero' hp' s =>
      .step (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hQ hQ')
        (Limits.biprod.map i i') (Limits.biprod.map p p')
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero, reassoc_of% zero'])
        (E.conflation_biprod hp hp') (r.biprod s)

@[simp] theorem biprod_base_base {X Y : C} (hX : P X) (hY : P Y) :
    (base (E := E) hX).biprod (base hY) =
      base (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hX hY) := by
  simp [biprod]

@[simp] theorem biprod_base_step {X K Q Y : C} (hX : P X) (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ Y)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (s : FiniteResolution E P K) :
    (base (E := E) hX).biprod (step hQ i p zero hp s) =
      step (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hX hQ)
        (Limits.biprod.map (0 : (0 : C) ⟶ X) i) (Limits.biprod.map (𝟙 X) p)
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero])
        (E.conflation_biprod (E.conflation_zero_id X) hp)
        (s.ofIso (isoZeroBiprod (isZero_zero C))) := by
  simp [biprod]

@[simp] theorem biprod_step_base {K Q X Y : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) (hY : P Y) :
    (step hQ i p zero hp r).biprod (base hY) =
      step (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hQ hY)
        (Limits.biprod.map i (0 : (0 : C) ⟶ Y)) (Limits.biprod.map p (𝟙 Y))
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero])
        (E.conflation_biprod hp (E.conflation_zero_id Y))
        (r.ofIso (isoBiprodZero (isZero_zero C))) := by
  simp [biprod]

@[simp] theorem biprod_step_step {K Q X K' Q' Y : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) (hQ' : P Q') (i' : K' ⟶ Q') (p' : Q' ⟶ Y)
    (zero' : i' ≫ p' = 0) (hp' : E.Conflation (ShortComplex.mk i' p' zero'))
    (s : FiniteResolution E P K') :
    (step hQ i p zero hp r).biprod (step hQ' i' p' zero' hp' s) =
      step (P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) hQ hQ')
        (Limits.biprod.map i i') (Limits.biprod.map p p')
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero, reassoc_of% zero'])
        (E.conflation_biprod hp hp') (r.biprod s) := by
  simp [biprod]

@[simp] theorem length_biprod {X Y : C} (r : FiniteResolution E P X)
    (s : FiniteResolution E P Y) : (r.biprod s).length = max r.length s.length := by
  induction r generalizing Y with
  | base hX => cases s <;> simp [biprod, length]
  | step hQ i p zero hp r ih => cases s <;> simp [biprod, length, ih]

end Biprod

end FiniteResolution

variable (P : ObjectProperty C)

/-- The object property of admitting some finite `P`-resolution: the object-property
presentation of `TauCeti.ExactStructure.FiniteResolution`. -/
def admitsFiniteResolution : ObjectProperty C := fun X => Nonempty (FiniteResolution E P X)

@[simp] theorem admitsFiniteResolution_iff {X : C} :
    E.admitsFiniteResolution P X ↔ Nonempty (FiniteResolution E P X) := Iff.rfl

/-- An object satisfying `P` admits a finite `P`-resolution, namely the empty chain. -/
theorem le_admitsFiniteResolution : P ≤ E.admitsFiniteResolution P :=
  fun _ hX => ⟨.base hX⟩

/-- Admitting a finite `P`-resolution passes from the subobject of a conflation with resolving
middle term to its quotient. -/
theorem admitsFiniteResolution_of_conflation {K Q X : C} (hQ : P Q) {i : K ⟶ Q} {p : Q ⟶ X}
    {zero : i ≫ p = 0} (hp : E.Conflation (ShortComplex.mk i p zero))
    (hK : E.admitsFiniteResolution P K) : E.admitsFiniteResolution P X :=
  ⟨.step hQ i p zero hp hK.some⟩

/-- **The object-property presentation.** Admitting a finite `P`-resolution is the smallest
object property containing `P` and closed under passing from the subobject of a conflation with
resolving middle term to its quotient. -/
theorem admitsFiniteResolution_induction {motive : ObjectProperty C} (hP : P ≤ motive)
    (hstep : ∀ {K Q X : C}, P Q → ∀ {i : K ⟶ Q} {p : Q ⟶ X} {zero : i ≫ p = 0},
      E.Conflation (ShortComplex.mk i p zero) → motive K → motive X)
    {X : C} (hX : E.admitsFiniteResolution P X) : motive X := by
  obtain ⟨r⟩ := hX
  induction r with
  | base hX => exact hP _ hX
  | step hQ i p zero hp _ ih => exact hstep hQ hp ih

instance [P.IsClosedUnderIsomorphisms] :
    (E.admitsFiniteResolution P).IsClosedUnderIsomorphisms where
  of_iso e hX := ⟨.ofIso e hX.some⟩

instance [P.IsClosedUnderIsomorphisms] [P.ContainsZero] :
    (E.admitsFiniteResolution P).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, ⟨.base P.prop_zero⟩⟩

/-- Admitting a finite `P`-resolution is closed under binary direct sums. -/
theorem admitsFiniteResolution_biprod [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderBinaryProducts] {X Y : C} (hX : E.admitsFiniteResolution P X)
    (hY : E.admitsFiniteResolution P Y) : E.admitsFiniteResolution P (X ⊞ Y) :=
  ⟨hX.some.biprod hY.some⟩

instance [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts] :
    (E.admitsFiniteResolution P).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (E.admitsFiniteResolution P).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      (E.admitsFiniteResolution_biprod P (p.prop_diag_obj ⟨.left⟩) (p.prop_diag_obj ⟨.right⟩))

end ExactStructure

end TauCeti
