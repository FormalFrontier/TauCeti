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

For a cochain complex `K` over an abelian category `A` and an invariant `v` additive on short
exact sequences, the alternating sum

```text
∑ n ∈ s, (-1)ⁿ v(Kⁿ)
```

over a finite set `s` of degrees is the **Euler characteristic** of `K` relative to `v`. This file
proves the **Euler–Poincaré theorem**: as soon as `K` is bounded and `s` contains every degree
where `K` lives, this alternating sum equals the alternating sum formed from the cohomology
objects of `K`. The argument is carried out for an arbitrary additive invariant, so it needs no
smallness hypothesis on `A`; specializing it to the tautological invariant `X ↦ [X]` gives the
statement in `TauCeti.AbelianK0 A`, which is the form the rest of the theory consumes.

The finiteness is carried by data, not inferred: the summation range is an explicit `Finset ℤ`,
and boundedness is Mathlib's `CochainComplex.IsStrictlyGE`/`CochainComplex.IsStrictlyLE`. Nothing
here is a `finsum`, so every value is a truncation to an explicitly given finite range of degrees;
what boundedness buys is that all large enough ranges give the same answer, so a complex with
infinite support is assigned no canonical, range-independent Euler characteristic rather than a
junk one. The comparison with the totalized `HomologicalComplex.eulerChar` of Mathlib is left to
the finite-dimensionality layer that gives it a `ℤ`-valued additive invariant.

## Main definitions

* `TauCeti.AbelianK0.eulerChar`: the alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` of the terms of a
  cochain complex over a finite set of degrees.
* `TauCeti.AbelianK0.homologyEulerChar`: the same alternating class formed from the cohomology
  objects.

## Main results

* `TauCeti.AbelianK0.AdditiveInvariant.obj_kernel_add_obj_kernel`: for a short complex `S` in an
  abelian category, `v(ker S.g) + v(ker S.f) = v(S.homology) + v(S.X₁)`. This is the single
  relation from which the telescoping argument runs.
* `TauCeti.AbelianK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology`:
  **Euler–Poincaré**. A bounded complex has the same Euler characteristic computed from its terms
  and from its cohomology, for every invariant additive on short exact sequences.
* `TauCeti.AbelianK0.of_kernel_add_of_kernel` and
  `TauCeti.AbelianK0.eulerChar_eq_homologyEulerChar`: the two statements above in abelian `K₀`.
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

variable {A : Type u} [Category.{v} A] [Abelian A]

private theorem isZero_kernel_of_isZero {X Y : A} (f : X ⟶ Y) (hX : IsZero X) :
    IsZero (kernel f) :=
  IsZero.of_iso hX (kernelIsoOfEq (hX.eq_of_src f 0) ≪≫ kernelZeroIsoSource)

private theorem isZero_X_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {n : ℤ} (hn : n ∉ Finset.Icc a b) : IsZero (K.X n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isStrictlyGE a n h
  · exact K.isZero_of_isStrictlyLE b n (by omega)

private theorem isZero_homology_of_notMem_Icc (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {n : ℤ} (hn : n ∉ Finset.Icc a b) : IsZero (K.homology n) := by
  rw [Finset.mem_Icc] at hn
  rcases lt_or_ge n a with h | h
  · exact K.isZero_of_isGE a n h
  · exact K.isZero_of_isLE b n (by omega)

namespace AbelianK0

namespace AdditiveInvariant

variable {G : Type*} [AddCommGroup G] (v : AdditiveInvariant A G)

private theorem obj_eq_zero_of_isZero {X : A} (hX : IsZero X) : v.obj X = 0 := by
  have h : (ShortComplex.mk (𝟙 X) (𝟙 X) (hX.eq_of_src _ _)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hX
      mono_f := inferInstance
      epi_g := inferInstance }
  exact left_eq_add.mp (v.map_shortExact h)

private theorem obj_eq_obj_kernel_add {Y Z : A} (p : Y ⟶ Z) [Epi p] :
    v.obj Y = v.obj (kernel p) + v.obj Z :=
  v.map_shortExact ((ExactStructure.abelian_conflation _).mp
    (ExactStructure.abelian_conflation_of_epi p))

private theorem obj_eq_add_obj_cokernel {X Y : A} (i : X ⟶ Y) [Mono i] :
    v.obj Y = v.obj X + v.obj (cokernel i) :=
  v.map_shortExact ((ExactStructure.abelian_conflation _).mp
    (ExactStructure.abelian_conflation_of_mono i))

/-- **The homology relation for an additive invariant.** For a short complex
`S = (X₁ ⟶ X₂ ⟶ X₃)` in an abelian category and an invariant `v` additive on short exact
sequences, `v(ker S.g) + v(ker S.f) = v(S.homology) + v(S.X₁)`.

Both sides count the boundaries `im S.f` once: the kernel of `S.g` is an extension of the homology
by them, and `X₁` is an extension of them by the kernel of `S.f`. -/
theorem obj_kernel_add_obj_kernel (S : ShortComplex A) :
    v.obj (kernel S.g) + v.obj (kernel S.f) = v.obj S.homology + v.obj S.X₁ := by
  have h1 : v.obj (kernel S.g)
      = v.obj (Abelian.image (kernel.lift S.g S.f S.zero))
        + v.obj (cokernel (kernel.lift S.g S.f S.zero)) :=
    obj_eq_obj_kernel_add v (cokernel.π (kernel.lift S.g S.f S.zero))
  have h2 : v.obj (cokernel (kernel.lift S.g S.f S.zero)) = v.obj S.homology :=
    v.map_iso S.homologyIsoCokernelLift.symm
  have h3 : v.obj S.X₁ = v.obj (kernel (kernel.lift S.g S.f S.zero))
      + v.obj (Abelian.coimage (kernel.lift S.g S.f S.zero)) :=
    obj_eq_add_obj_cokernel v (kernel.ι (kernel.lift S.g S.f S.zero))
  have h4 : v.obj (Abelian.coimage (kernel.lift S.g S.f S.zero))
      = v.obj (Abelian.image (kernel.lift S.g S.f S.zero)) :=
    v.map_iso (Abelian.coimageIsoImage _)
  have h5 : v.obj (kernel (kernel.lift S.g S.f S.zero)) = v.obj (kernel S.f) :=
    v.map_iso ((kernelCompMono _ (kernel.ι S.g)).symm ≪≫ kernelIsoOfEq (kernel.lift_ι _ _ _))
  rw [h1, h2, h3, h4, h5]
  abel

section CochainComplex

variable (K : CochainComplex A ℤ)

/-- **The degreewise homology relation for a cochain complex.** For consecutive degrees
`i + 1 = j` and `j + 1 = k`, the values of an additive invariant on the two cocycle objects around
degree `j` differ from its value on the cohomology at `j` by its value on the term in degree
`i`. -/
theorem obj_kernel_d_add_obj_kernel_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    v.obj (kernel (K.d j k)) + v.obj (kernel (K.d i j))
      = v.obj (K.homology j) + v.obj (K.X i) := by
  have h := obj_kernel_add_obj_kernel v (K.sc' i j k)
  rwa [v.map_iso (K.homologyIsoSc' i j k ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk)).symm] at h

/-- In the lowest degree where a bounded-below complex lives, the cocycles are the cohomology,
because there are no coboundaries. -/
theorem obj_kernel_d_eq_obj_homology (a : ℤ) [K.IsStrictlyGE a] :
    v.obj (kernel (K.d a (a + 1))) = v.obj (K.homology a) := by
  have h := obj_kernel_d_add_obj_kernel_d v K (a - 1) a (a + 1) (by omega) rfl
  have hX : IsZero (K.X (a - 1)) := K.isZero_of_isStrictlyGE a (a - 1) (by omega)
  rw [obj_eq_zero_of_isZero v (isZero_kernel_of_isZero _ hX), obj_eq_zero_of_isZero v hX] at h
  simpa using h

/-- The running form of the Euler–Poincaré computation: over the degrees `a` to `b` of a complex
that is strictly bounded below by `a`, the two alternating sums differ by the single correction
term supplied by the cocycles in degree `b + 1`. -/
private theorem sum_negOnePow_obj_Icc_aux (a : ℤ) [K.IsStrictlyGE a] (b : ℤ) (hb : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • v.obj (K.X n)
      = ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • v.obj (K.homology n)
        + (((b + 1).negOnePow : ℤ)) •
          (v.obj (K.homology (b + 1)) - v.obj (kernel (K.d (b + 1) (b + 1 + 1)))) := by
  induction b, hb using Int.leInduction with
  | base =>
      have key := obj_kernel_d_add_obj_kernel_d v K a (a + 1) (a + 1 + 1) rfl rfl
      rw [obj_kernel_d_eq_obj_homology v K a] at key
      have hX : v.obj (K.X a)
          = v.obj (kernel (K.d (a + 1) (a + 1 + 1))) + v.obj (K.homology a)
            - v.obj (K.homology (a + 1)) := by
        rw [key]; abel
      have he : (((a + 1).negOnePow : ℤ)) = -((a.negOnePow : ℤ)) := by
        rw [Int.negOnePow_succ]; simp
      simp only [Finset.Icc_self, Finset.sum_singleton, hX, he]
      simp only [smul_add, smul_sub, neg_smul]
      abel
  | succ b hb ih =>
      have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (b + 1) ∉ Finset.Icc a b := by simp
      have key := obj_kernel_d_add_obj_kernel_d v K (b + 1) (b + 1 + 1) (b + 1 + 1 + 1) rfl rfl
      have hX : v.obj (K.X (b + 1))
          = v.obj (kernel (K.d (b + 1 + 1) (b + 1 + 1 + 1)))
            + v.obj (kernel (K.d (b + 1) (b + 1 + 1))) - v.obj (K.homology (b + 1 + 1)) := by
        rw [key]; abel
      have he : (((b + 1 + 1).negOnePow : ℤ)) = -(((b + 1).negOnePow : ℤ)) := by
        rw [Int.negOnePow_succ]; simp
      rw [hins, Finset.sum_insert hnot, Finset.sum_insert hnot, ih, hX, he]
      simp only [smul_add, smul_sub, neg_smul]
      abel

/-- **The Euler–Poincaré theorem for an additive invariant.** For a cochain complex that is
strictly supported in degrees `a` to `b`, any finite range of degrees containing `[a, b]`, and any
invariant additive on short exact sequences, the alternating sum of the values on the terms equals
the alternating sum of the values on the cohomology objects. -/
theorem sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n)
      = ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.homology n) := by
  have hX : ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n)
      = ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • v.obj (K.X n) :=
    (Finset.sum_subset hs fun x _ hx => by
      rw [obj_eq_zero_of_isZero v (isZero_X_of_notMem_Icc K a b hx), smul_zero]).symm
  have hH : ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.homology n)
      = ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • v.obj (K.homology n) :=
    (Finset.sum_subset hs fun x _ hx => by
      rw [obj_eq_zero_of_isZero v (isZero_homology_of_notMem_Icc K a b hx), smul_zero]).symm
  rw [hX, hH]
  rcases le_or_gt a b with hab | hab
  · rw [sum_negOnePow_obj_Icc_aux v K a b hab,
      obj_eq_zero_of_isZero v (K.isZero_of_isLE b (b + 1) (by omega)),
      obj_eq_zero_of_isZero v
        (isZero_kernel_of_isZero _ (K.isZero_of_isStrictlyLE b (b + 1) (by omega)))]
    simp
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Finset.sum_empty]

end CochainComplex

end AdditiveInvariant

variable [EssentiallySmall.{w} A]

/-- The tautological additive invariant `X ↦ [X]` with values in abelian `K₀`, along which the
general Euler–Poincaré statements specialize to their `K₀` forms. -/
private noncomputable def ofInvariant : AdditiveInvariant A (AbelianK0 A) :=
  liftEquiv.symm (AddMonoidHom.id (AbelianK0 A))

@[simp] private lemma ofInvariant_obj (X : A) : (ofInvariant (A := A)).obj X = of X := by
  simp [ofInvariant]

/-- **The homology relation in abelian `K₀`.** For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` in an
abelian category, `[ker S.g] + [ker S.f] = [S.homology] + [S.X₁]`. -/
theorem of_kernel_add_of_kernel (S : ShortComplex A) :
    (of (kernel S.g) : AbelianK0 A) + of (kernel S.f) = of S.homology + of S.X₁ := by
  simpa using AdditiveInvariant.obj_kernel_add_obj_kernel ofInvariant S

section CochainComplex

variable (K : CochainComplex A ℤ)

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` of the terms of a cochain complex over a finite
set `s` of degrees. The set of degrees is data: the value is the truncation of the alternating sum
to `s`, and `TauCeti.AbelianK0.eulerChar_eq_eulerChar` shows that it stops depending on `s` once
`s` contains the support of a bounded complex. -/
noncomputable def eulerChar (s : Finset ℤ) : AbelianK0 A :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.X n)

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Hⁿ K]` of the cohomology of a cochain complex over a
finite set `s` of degrees. -/
noncomputable def homologyEulerChar (s : Finset ℤ) : AbelianK0 A :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.homology n)

@[simp] theorem eulerChar_empty : eulerChar K ∅ = 0 := Finset.sum_empty

@[simp] theorem homologyEulerChar_empty : homologyEulerChar K ∅ = 0 := Finset.sum_empty

@[simp] theorem eulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    eulerChar K (insert n s) = ((n.negOnePow : ℤ)) • of (K.X n) + eulerChar K s :=
  Finset.sum_insert hn

@[simp] theorem homologyEulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    homologyEulerChar K (insert n s)
      = ((n.negOnePow : ℤ)) • of (K.homology n) + homologyEulerChar K s :=
  Finset.sum_insert hn

section Bounded

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

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
  simpa [eulerChar, homologyEulerChar] using
    AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology ofInvariant K a b hs

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
a quasi-isomorphism have the same alternating class of terms, over any finite range of degrees
containing both supports; this is what makes the Euler characteristic a function of the image of
the complex in the derived category. -/
theorem eulerChar_eq_of_quasiIso (aK bK aL bL : ℤ) [K.IsStrictlyGE aK] [K.IsStrictlyLE bK]
    [L.IsStrictlyGE aL] [L.IsStrictlyLE bL] {s : Finset ℤ} (hK : Finset.Icc aK bK ⊆ s)
    (hL : Finset.Icc aL bL ⊆ s) : eulerChar K s = eulerChar L s := by
  rw [eulerChar_eq_homologyEulerChar K aK bK hK, homologyEulerChar_eq_of_quasiIso f s,
    ← eulerChar_eq_homologyEulerChar L aL bL hL]

end QuasiIso

end CochainComplex

end AbelianK0

end TauCeti
