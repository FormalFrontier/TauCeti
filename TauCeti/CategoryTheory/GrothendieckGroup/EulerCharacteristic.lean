/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Data.Int.Interval
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian

/-!
# The Euler characteristic of a bounded complex in abelian `K₀`

For a cochain complex `K` over an essentially small abelian category `A`, the alternating sum

```text
∑ n ∈ s, (-1)ⁿ [Kⁿ]
```

of the classes of the terms of `K` over a finite set `s` of degrees is an element of
`TauCeti.AbelianK0 A`. This file proves the **Euler–Poincaré theorem**: as soon as `K` is bounded
and `s` contains every degree where `K` lives, this alternating sum equals the alternating sum of
the classes of the cohomology objects of `K`.

The finiteness is carried by data, not inferred: the summation range is an explicit `Finset ℤ`,
and boundedness is Mathlib's `CochainComplex.IsStrictlyGE`/`CochainComplex.IsStrictlyLE`. Nothing
here is a `finsum`, so an unbounded complex produces no value at all rather than a junk one; the
comparison with the totalized `HomologicalComplex.eulerChar` of Mathlib is left to the
finite-dimensionality layer that gives it a `ℤ`-valued additive invariant.

## Main definitions

* `TauCeti.AbelianK0.eulerChar`: the alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` of the terms of a
  cochain complex over a finite set of degrees.
* `TauCeti.AbelianK0.homologyEulerChar`: the same alternating class formed from the cohomology
  objects.

## Main results

* `TauCeti.AbelianK0.of_kernel_add_of_kernel`: for a short complex `S` in an abelian category,
  `[ker S.g] + [ker S.f] = [S.homology] + [S.X₁]`. This is the single relation from which the
  telescoping argument runs.
* `TauCeti.AbelianK0.eulerChar_eq_homologyEulerChar`: **Euler–Poincaré**. A bounded complex has the
  same Euler characteristic computed from its terms and from its cohomology.
* `TauCeti.AbelianK0.AdditiveInvariant.sum_negOnePow_obj_X`: the same statement for an arbitrary
  invariant additive on short exact sequences, obtained from the universal property of abelian
  `K₀`.
* `TauCeti.AbelianK0.eulerChar_eq_of_quasiIso`: the Euler characteristic of a bounded complex
  depends only on its image in the derived category.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.3 and 1.6, for the
  cycles/boundaries bookkeeping behind the Euler–Poincaré formula.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Proposition 6.6, for the `K₀`-valued form of the alternating sum used here.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [EssentiallySmall.{w} A]

private theorem isZero_kernel_of_isZero {B : Type u} [Category.{v} B] [Abelian B] {X Y : B}
    (f : X ⟶ Y) (hX : IsZero X) : IsZero (kernel f) :=
  IsZero.of_iso hX (kernelIsoOfEq (hX.eq_of_src f 0) ≪≫ kernelZeroIsoSource)

namespace AbelianK0

/-- **The homology relation in abelian `K₀`.** For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` in an
abelian category, `[ker S.g] + [ker S.f] = [S.homology] + [S.X₁]`.

Both sides count the boundaries `im S.f` once: the kernel of `S.g` is an extension of the homology
by them, and `X₁` is an extension of them by the kernel of `S.f`. -/
theorem of_kernel_add_of_kernel (S : ShortComplex A) :
    (of (kernel S.g) : AbelianK0 A) + of (kernel S.f) = of S.homology + of S.X₁ := by
  have h1 := of_eq_of_image_add_of_cokernel (C := A) (kernel.lift S.g S.f S.zero)
  have h2 : (of (cokernel (kernel.lift S.g S.f S.zero)) : AbelianK0 A) = of S.homology :=
    of_congr S.homologyIsoCokernelLift.symm
  have h3 := of_eq_of_kernel_add_of_coimage (C := A) (kernel.lift S.g S.f S.zero)
  have h4 : (of (Abelian.coimage (kernel.lift S.g S.f S.zero)) : AbelianK0 A)
      = of (Abelian.image (kernel.lift S.g S.f S.zero)) :=
    of_congr (Abelian.coimageIsoImage _)
  have h5 : (of (kernel (kernel.lift S.g S.f S.zero)) : AbelianK0 A) = of (kernel S.f) :=
    of_congr ((kernelCompMono _ (kernel.ι S.g)).symm ≪≫ kernelIsoOfEq (kernel.lift_ι _ _ _))
  rw [h1, h2, h3, h4, h5]
  abel

section CochainComplex

variable (K : CochainComplex A ℤ)

/-- **The degreewise homology relation for a cochain complex.** For consecutive degrees
`i + 1 = j` and `j + 1 = k`, the classes of the two cocycle objects around degree `j` differ from
the class of the cohomology at `j` by the class of the term in degree `i`. -/
theorem of_kernel_d_add_of_kernel_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (of (kernel (K.d j k)) : AbelianK0 A) + of (kernel (K.d i j))
      = of (K.homology j) + of (K.X i) := by
  have h := of_kernel_add_of_kernel (K.sc' i j k)
  rwa [of_congr (K.homologyIsoSc' i j k ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk)).symm] at h

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` of the terms of a cochain complex over a finite
set `s` of degrees. The set of degrees is data: no value is attached to a complex whose support
is infinite. -/
noncomputable def eulerChar (s : Finset ℤ) : AbelianK0 A :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.X n)

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Hⁿ K]` of the cohomology of a cochain complex over a
finite set `s` of degrees. -/
noncomputable def homologyEulerChar (s : Finset ℤ) : AbelianK0 A :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.homology n)

@[simp] theorem eulerChar_empty : eulerChar K ∅ = 0 := Finset.sum_empty

@[simp] theorem homologyEulerChar_empty : homologyEulerChar K ∅ = 0 := Finset.sum_empty

theorem eulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    eulerChar K (insert n s) = ((n.negOnePow : ℤ)) • of (K.X n) + eulerChar K s :=
  Finset.sum_insert hn

theorem homologyEulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    homologyEulerChar K (insert n s)
      = ((n.negOnePow : ℤ)) • of (K.homology n) + homologyEulerChar K s :=
  Finset.sum_insert hn

/-- In the lowest degree where a bounded-below complex lives, the cocycles are the cohomology,
because there are no coboundaries. -/
theorem of_kernel_d_eq_of_homology (a : ℤ) [K.IsStrictlyGE a] :
    (of (kernel (K.d a (a + 1))) : AbelianK0 A) = of (K.homology a) := by
  have h := of_kernel_d_add_of_kernel_d K (a - 1) a (a + 1) (by omega) rfl
  have hX : IsZero (K.X (a - 1)) := K.isZero_of_isStrictlyGE a (a - 1) (by omega)
  rw [of_eq_zero_of_isZero (isZero_kernel_of_isZero _ hX), of_eq_zero_of_isZero hX] at h
  simpa using h

/-- The running form of the Euler–Poincaré computation: over the degrees `a` to `b` of a complex
that is strictly bounded below by `a`, the two alternating sums differ by the single correction
term supplied by the cocycles in degree `b + 1`. -/
private theorem eulerChar_Icc_aux (a : ℤ) [K.IsStrictlyGE a] (b : ℤ) (hb : a ≤ b) :
    eulerChar K (Finset.Icc a b) = homologyEulerChar K (Finset.Icc a b)
      + (((b + 1).negOnePow : ℤ)) •
        (of (K.homology (b + 1)) - of (kernel (K.d (b + 1) (b + 1 + 1)))) := by
  induction b, hb using Int.leInduction with
  | base =>
      have key := of_kernel_d_add_of_kernel_d K a (a + 1) (a + 1 + 1) rfl rfl
      rw [of_kernel_d_eq_of_homology K a] at key
      have hX : (of (K.X a) : AbelianK0 A)
          = of (kernel (K.d (a + 1) (a + 1 + 1))) + of (K.homology a)
            - of (K.homology (a + 1)) := by
        rw [key]; abel
      have he : (((a + 1).negOnePow : ℤ)) = -((a.negOnePow : ℤ)) := by
        rw [Int.negOnePow_succ]; simp
      simp only [eulerChar, homologyEulerChar, Finset.Icc_self, Finset.sum_singleton, hX, he]
      simp only [smul_add, smul_sub, neg_smul]
      abel
  | succ b hb ih =>
      have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (b + 1) ∉ Finset.Icc a b := by simp
      have key := of_kernel_d_add_of_kernel_d K (b + 1) (b + 1 + 1) (b + 1 + 1 + 1) rfl rfl
      have hX : (of (K.X (b + 1)) : AbelianK0 A)
          = of (kernel (K.d (b + 1 + 1) (b + 1 + 1 + 1))) + of (kernel (K.d (b + 1) (b + 1 + 1)))
            - of (K.homology (b + 1 + 1)) := by
        rw [key]; abel
      have he : (((b + 1 + 1).negOnePow : ℤ)) = -(((b + 1).negOnePow : ℤ)) := by
        rw [Int.negOnePow_succ]; simp
      rw [hins, eulerChar_insert K hnot, homologyEulerChar_insert K hnot, ih, hX, he]
      simp only [smul_add, smul_sub, neg_smul]
      abel

section Bounded

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

omit [EssentiallySmall.{w} A] in
private theorem isZero_X_of_notMem_Icc {n : ℤ} (hn : n ∉ Finset.Icc a b) : IsZero (K.X n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isStrictlyGE a n h
  · exact K.isZero_of_isStrictlyLE b n (by omega)

omit [EssentiallySmall.{w} A] in
private theorem isZero_homology_of_notMem_Icc {n : ℤ} (hn : n ∉ Finset.Icc a b) :
    IsZero (K.homology n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isGE a n h
  · exact K.isZero_of_isLE b n (by omega)

/-- Enlarging the range of degrees beyond the support of a bounded complex does not change its
Euler characteristic. -/
theorem eulerChar_eq_eulerChar_Icc {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar K s = eulerChar K (Finset.Icc a b) :=
  (Finset.sum_subset hs fun x _ hx => by
    rw [of_eq_zero_of_isZero (isZero_X_of_notMem_Icc K a b hx), smul_zero]).symm

/-- Enlarging the range of degrees beyond the support of a bounded complex does not change the
alternating class of its cohomology. -/
theorem homologyEulerChar_eq_homologyEulerChar_Icc {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    homologyEulerChar K s = homologyEulerChar K (Finset.Icc a b) :=
  (Finset.sum_subset hs fun x _ hx => by
    rw [of_eq_zero_of_isZero (isZero_homology_of_notMem_Icc K a b hx), smul_zero]).symm

/-- The Euler characteristic of a bounded complex does not depend on the finite range of degrees
over which it is summed, as long as that range contains the support. -/
theorem eulerChar_eq_eulerChar {s t : Finset ℤ} (hs : Finset.Icc a b ⊆ s)
    (ht : Finset.Icc a b ⊆ t) : eulerChar K s = eulerChar K t := by
  rw [eulerChar_eq_eulerChar_Icc K a b hs, eulerChar_eq_eulerChar_Icc K a b ht]

/-- The alternating class of the cohomology of a bounded complex does not depend on the finite
range of degrees over which it is summed. -/
theorem homologyEulerChar_eq_homologyEulerChar {s t : Finset ℤ} (hs : Finset.Icc a b ⊆ s)
    (ht : Finset.Icc a b ⊆ t) : homologyEulerChar K s = homologyEulerChar K t := by
  rw [homologyEulerChar_eq_homologyEulerChar_Icc K a b hs,
    homologyEulerChar_eq_homologyEulerChar_Icc K a b ht]

/-- **The Euler–Poincaré theorem in abelian `K₀`.** For a cochain complex that is strictly
supported in degrees `a` to `b`, and any finite range of degrees containing `[a, b]`, the
alternating sum of the classes of the terms equals the alternating sum of the classes of the
cohomology objects. -/
theorem eulerChar_eq_homologyEulerChar {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar K s = homologyEulerChar K s := by
  rw [eulerChar_eq_eulerChar_Icc K a b hs, homologyEulerChar_eq_homologyEulerChar_Icc K a b hs]
  rcases le_or_gt a b with hab | hab
  · rw [eulerChar_Icc_aux K a b hab,
      of_eq_zero_of_isZero (K.isZero_of_isLE b (b + 1) (by omega)),
      of_eq_zero_of_isZero
        (isZero_kernel_of_isZero _ (K.isZero_of_isStrictlyLE b (b + 1) (by omega)))]
    simp
  · rw [Finset.Icc_eq_empty (by omega), eulerChar_empty, homologyEulerChar_empty]

/-- **Euler–Poincaré for an arbitrary additive invariant.** Every invariant additive on short exact
sequences computes the same alternating sum from the terms of a bounded complex as from its
cohomology; this is the `K₀` statement pushed forward along the universal property. -/
theorem AdditiveInvariant.sum_negOnePow_obj_X {G : Type*} [AddCommGroup G]
    (v : AdditiveInvariant A G) {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n)
      = ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.homology n) := by
  have h := congrArg (lift v) (eulerChar_eq_homologyEulerChar K a b hs)
  simpa [eulerChar, homologyEulerChar, map_sum, map_zsmul] using h

/-- A bounded exact complex has vanishing Euler characteristic. -/
theorem eulerChar_eq_zero_of_exactAt (hK : ∀ n : ℤ, K.ExactAt n) {s : Finset ℤ}
    (hs : Finset.Icc a b ⊆ s) : eulerChar K s = 0 := by
  rw [eulerChar_eq_homologyEulerChar K a b hs]
  exact Finset.sum_eq_zero fun n _ => by
    rw [of_eq_zero_of_isZero (hK n).isZero_homology, smul_zero]

end Bounded

section QuasiIso

variable {K} {L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]

include f in
/-- A quasi-isomorphism preserves the alternating class of the cohomology, in any range of
degrees. -/
theorem homologyEulerChar_eq_of_quasiIso (s : Finset ℤ) :
    homologyEulerChar K s = homologyEulerChar L s :=
  Finset.sum_congr rfl fun n _ => by
    have : IsIso (HomologicalComplex.homologyMap f n) :=
      (quasiIsoAt_iff_isIso_homologyMap f n).mp inferInstance
    rw [of_congr (asIso (HomologicalComplex.homologyMap f n))]

include f in
/-- **The Euler characteristic is a quasi-isomorphism invariant.** Two bounded complexes joined by
a quasi-isomorphism have the same alternating class of terms; this is what makes the Euler
characteristic a function of the image of the complex in the derived category. -/
theorem eulerChar_eq_of_quasiIso (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [L.IsStrictlyGE a] [L.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar K s = eulerChar L s := by
  rw [eulerChar_eq_homologyEulerChar K a b hs, homologyEulerChar_eq_of_quasiIso f s,
    ← eulerChar_eq_homologyEulerChar L a b hs]

end QuasiIso

end CochainComplex

end AbelianK0

end TauCeti
