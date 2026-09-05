/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Cone
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Counterexamples for toric cones

This file collects the negative examples that fix the content of `TauCeti.Toric.IsToricCone`.

Toricity need not be preserved by arbitrary intersections when the additive map into the ambient
real vector space is not discrete. The example uses an injective map `ℤ⁴ →+ ℝ³` whose intersection
with the `z`-axis is dense. Two lattice-rational salient cones meet in an irrational ray
containing no nonzero image of a lattice vector.

Salience is a genuinely independent condition: the full line of the rank-one lattice `ℤ ⊆ ℝ` is a
finitely generated, lattice-rational pointed cone that is not toric.

## Main declarations

* `TauCeti.Toric.not_isLatticeRational_sqrtTwoCone_inf`: two toric cones whose intersection is not
  lattice rational, and `TauCeti.Toric.not_isToricCone_sqrtTwoCone_inf`, the resulting failure of
  toricity.
* `TauCeti.Toric.not_isToricCone_top_intCast`: a finitely generated, lattice-rational pointed cone
  that is not toric, because it is a line.

## References

The rationality condition is discussed in Chapter 1 of D. Cox, J. Little and H. Schenck,
*Toric Varieties*, and §1.2 of W. Fulton, *Introduction to Toric Varieties*.
-/

public section

namespace TauCeti.Toric

/-- The real-linear functional `x ↦ a * x.1 + b * x.2.1 + c * x.2.2` on `ℝ × ℝ × ℝ`. -/
private def coords (a b c : ℝ) : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := a * x.1 + b * x.2.1 + c * x.2.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp]
private lemma coords_apply (a b c : ℝ) (x : ℝ × ℝ × ℝ) :
    coords a b c x = a * x.1 + b * x.2.1 + c * x.2.2 := (rfl)

/-- `PointedCone.dual_hull` for the functionals `coords a b c`: nonnegativity on a generating set
spreads to the whole cone hull, because it says exactly that `coords a b c` lies in the dual cone
of the generating set for the evaluation pairing. -/
private lemma coords_nonneg_of_mem_hull (a b c : ℝ) {t : Set (ℝ × ℝ × ℝ)} {x : ℝ × ℝ × ℝ}
    (ht : ∀ y ∈ t, 0 ≤ coords a b c y) (hx : x ∈ PointedCone.hull ℝ t) :
    0 ≤ coords a b c x := by
  have h : coords a b c ∈ PointedCone.dual (Module.Dual.eval ℝ (ℝ × ℝ × ℝ)) t := ht
  rw [← PointedCone.dual_hull] at h
  exact h hx

/-- A functional `coords a b c` vanishing on a generating set vanishes on the whole cone hull,
by `coords_nonneg_of_mem_hull` applied to both signs. -/
private lemma coords_eq_zero_of_mem_hull (a b c : ℝ) {t : Set (ℝ × ℝ × ℝ)} {x : ℝ × ℝ × ℝ}
    (ht : ∀ y ∈ t, coords a b c y = 0) (hx : x ∈ PointedCone.hull ℝ t) :
    coords a b c x = 0 := by
  have h₁ := coords_nonneg_of_mem_hull a b c (fun y hy ↦ (ht y hy).ge) hx
  have h₂ := coords_nonneg_of_mem_hull (-a) (-b) (-c)
    (fun y hy ↦ by have := ht y hy; simp only [coords_apply] at this ⊢; linarith) hx
  simp only [coords_apply] at h₁ h₂ ⊢
  linarith

/-- The additive map `ℤ⁴ →+ ℝ³`, `(a, b, c, k) ↦ (a, b, c + √2 * k)`. It is injective and
has nondiscrete image: its intersection with the `z`-axis is dense in that axis. -/
noncomputable def sqrtTwoMap : (ℤ × ℤ × ℤ × ℤ) →+ (ℝ × ℝ × ℝ) where
  toFun v := ((v.1 : ℝ), (v.2.1 : ℝ), (v.2.2.1 : ℝ) + Real.sqrt 2 * (v.2.2.2 : ℝ))
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Int.cast_add]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    push_cast
    ring

@[simp]
theorem sqrtTwoMap_apply (v : ℤ × ℤ × ℤ × ℤ) :
    sqrtTwoMap v = ((v.1 : ℝ), (v.2.1 : ℝ), (v.2.2.1 : ℝ) + Real.sqrt 2 * (v.2.2.2 : ℝ)) := (rfl)

/-- Two integers with `a + √2 * b = 0` both vanish. -/
private lemma eq_zero_of_add_sqrtTwo_mul (a b : ℤ) (h : (a : ℝ) + Real.sqrt 2 * (b : ℝ) = 0) :
    a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    refine irrational_sqrt_two.ne_rational (-a) b ?_
    have hbne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.2 hb
    field_simp
    push_cast
    linarith
  subst hb
  simpa using h

/-- `sqrtTwoMap` is injective: the first two coordinates are read off directly, and
`c + √2 * k = 0` forces `c = k = 0` because `√2` is irrational. -/
theorem sqrtTwoMap_injective : Function.Injective sqrtTwoMap := by
  refine (injective_iff_map_eq_zero sqrtTwoMap).2 fun v hv ↦ ?_
  simp only [sqrtTwoMap_apply, Prod.mk_eq_zero] at hv
  obtain ⟨h₁, h₂, h₃⟩ := hv
  obtain ⟨hc, hk⟩ := eq_zero_of_add_sqrtTwo_mul _ _ h₃
  have h₁' : v.1 = 0 := by exact_mod_cast h₁
  have h₂' : v.2.1 = 0 := by exact_mod_cast h₂
  simp [Prod.ext_iff, h₁', h₂', hc, hk]

/-- The quadrant of the plane `z = 0` spanned by `(1, 0, 0)` and `(0, -1, 0)`. -/
def sqrtTwoCone₁ : PointedCone ℝ (ℝ × ℝ × ℝ) := PointedCone.hull ℝ {(1, 0, 0), (0, -1, 0)}

/-- The quadrant of the plane `z = x + √2 * y` spanned by `(1, 0, 1)` and `(0, -1, -√2)`. -/
noncomputable def sqrtTwoCone₂ : PointedCone ℝ (ℝ × ℝ × ℝ) :=
  PointedCone.hull ℝ {(1, 0, 1), (0, -1, -Real.sqrt 2)}

/-- `sqrtTwoCone₁` is generated by the lattice vectors `(1, 0, 0, 0)` and `(0, -1, 0, 0)`. -/
private lemma isLatticeRational_sqrtTwoCone₁ : IsLatticeRational sqrtTwoMap sqrtTwoCone₁ := by
  refine isLatticeRational_iff.mpr ⟨{(1, 0, 0, 0), (0, -1, 0, 0)}, ?_⟩
  rw [sqrtTwoCone₁]
  congr 1
  simp [Set.image_insert_eq]

/-- `sqrtTwoCone₂` is generated by the lattice vectors `(1, 0, 1, 0)` and `(0, -1, 0, -1)`. -/
private lemma isLatticeRational_sqrtTwoCone₂ : IsLatticeRational sqrtTwoMap sqrtTwoCone₂ := by
  refine isLatticeRational_iff.mpr ⟨{(1, 0, 1, 0), (0, -1, 0, -1)}, ?_⟩
  rw [sqrtTwoCone₂]
  congr 1
  simp [Set.image_insert_eq]

/-- The first coordinate is nonnegative on `sqrtTwoCone₁`. -/
private lemma fst_nonneg_of_mem_sqrtTwoCone₁ {x : ℝ × ℝ × ℝ} (hx : x ∈ sqrtTwoCone₁) :
    0 ≤ x.1 := by
  simpa using coords_nonneg_of_mem_hull 1 0 0 (by rintro y (rfl | rfl) <;> norm_num) hx

/-- The second coordinate is nonpositive on `sqrtTwoCone₁`. -/
private lemma snd_nonpos_of_mem_sqrtTwoCone₁ {x : ℝ × ℝ × ℝ} (hx : x ∈ sqrtTwoCone₁) :
    x.2.1 ≤ 0 := by
  have := coords_nonneg_of_mem_hull 0 (-1) 0 (by rintro y (rfl | rfl) <;> norm_num) hx
  simp only [coords_apply] at this
  linarith

/-- `sqrtTwoCone₁` lies in the plane `z = 0`. -/
private lemma thd_eq_zero_of_mem_sqrtTwoCone₁ {x : ℝ × ℝ × ℝ} (hx : x ∈ sqrtTwoCone₁) :
    x.2.2 = 0 := by
  have := coords_eq_zero_of_mem_hull 0 0 1 (by rintro y (rfl | rfl) <;> norm_num) hx
  simp only [coords_apply] at this
  linarith

/-- The first coordinate is nonnegative on `sqrtTwoCone₂`. -/
private lemma fst_nonneg_of_mem_sqrtTwoCone₂ {x : ℝ × ℝ × ℝ} (hx : x ∈ sqrtTwoCone₂) :
    0 ≤ x.1 := by
  simpa using coords_nonneg_of_mem_hull 1 0 0 (by rintro y (rfl | rfl) <;> norm_num) hx

/-- The second coordinate is nonpositive on `sqrtTwoCone₂`. -/
private lemma snd_nonpos_of_mem_sqrtTwoCone₂ {x : ℝ × ℝ × ℝ} (hx : x ∈ sqrtTwoCone₂) :
    x.2.1 ≤ 0 := by
  have := coords_nonneg_of_mem_hull 0 (-1) 0 (by rintro y (rfl | rfl) <;> norm_num) hx
  simp only [coords_apply] at this
  linarith

/-- `sqrtTwoCone₂` lies in the plane `z = x + √2 * y`. -/
private lemma thd_of_mem_sqrtTwoCone₂ {x : ℝ × ℝ × ℝ} (hx : x ∈ sqrtTwoCone₂) :
    x.2.2 = x.1 + Real.sqrt 2 * x.2.1 := by
  have := coords_eq_zero_of_mem_hull (-1) (-Real.sqrt 2) 1
    (by rintro y (rfl | rfl) <;> simp) hx
  simp only [coords_apply] at this
  linarith

/-- The first cone of the counterexample is a toric cone. -/
theorem isToricCone_sqrtTwoCone₁ : IsToricCone sqrtTwoMap sqrtTwoCone₁ := by
  refine ⟨isLatticeRational_sqrtTwoCone₁, fun x hx hne hnx ↦ hne ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ (thd_eq_zero_of_mem_sqrtTwoCone₁ hx))
  · exact le_antisymm
      (by simpa using neg_nonneg.1 (by simpa using fst_nonneg_of_mem_sqrtTwoCone₁ hnx))
      (fst_nonneg_of_mem_sqrtTwoCone₁ hx)
  · exact le_antisymm (snd_nonpos_of_mem_sqrtTwoCone₁ hx)
      (by simpa using neg_nonpos.1 (by simpa using snd_nonpos_of_mem_sqrtTwoCone₁ hnx))

/-- The second cone of the counterexample is a toric cone. -/
theorem isToricCone_sqrtTwoCone₂ : IsToricCone sqrtTwoMap sqrtTwoCone₂ := by
  refine ⟨isLatticeRational_sqrtTwoCone₂, fun x hx hne hnx ↦ hne ?_⟩
  have h1 : x.1 = 0 :=
    le_antisymm (by simpa using neg_nonneg.1 (by simpa using fst_nonneg_of_mem_sqrtTwoCone₂ hnx))
      (fst_nonneg_of_mem_sqrtTwoCone₂ hx)
  have h2 : x.2.1 = 0 :=
    le_antisymm (snd_nonpos_of_mem_sqrtTwoCone₂ hx)
      (by simpa using neg_nonpos.1 (by simpa using snd_nonpos_of_mem_sqrtTwoCone₂ hnx))
  refine Prod.ext h1 (Prod.ext h2 ?_)
  rw [thd_of_mem_sqrtTwoCone₂ hx, h1, h2]
  simp

/-- The vector `(√2, -1, 0)` lies in both cones of the counterexample. -/
private lemma mem_inf_sqrtTwoCone : ((Real.sqrt 2, -1, 0) : ℝ × ℝ × ℝ) ∈
    sqrtTwoCone₁ ⊓ sqrtTwoCone₂ := by
  constructor
  · have h1 : ((1 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ sqrtTwoCone₁ := PointedCone.subset_hull (by simp)
    have h2 : ((0 : ℝ), (-1 : ℝ), (0 : ℝ)) ∈ sqrtTwoCone₁ := PointedCone.subset_hull (by simp)
    simpa using add_mem (PointedCone.smul_mem _ (Real.sqrt_nonneg 2) h1) h2
  · have h1 : ((1 : ℝ), (0 : ℝ), (1 : ℝ)) ∈ sqrtTwoCone₂ := PointedCone.subset_hull (by simp)
    have h2 : ((0 : ℝ), (-1 : ℝ), -Real.sqrt 2) ∈ sqrtTwoCone₂ := PointedCone.subset_hull (by simp)
    simpa using add_mem (PointedCone.smul_mem _ (Real.sqrt_nonneg 2) h1) h2

/-- The only lattice vector landing in the intersection of the two cones is `0`: on the
intersection the third coordinate vanishes and `x + √2 * y = 0`, which for integers forces
`x = y = 0`. -/
private lemma sqrtTwoMap_eq_zero_of_mem_inf {v : ℤ × ℤ × ℤ × ℤ}
    (hv : sqrtTwoMap v ∈ sqrtTwoCone₁ ⊓ sqrtTwoCone₂) : sqrtTwoMap v = 0 := by
  obtain ⟨hv₁, hv₂⟩ := hv
  have h₃ : (v.2.2.1 : ℝ) + Real.sqrt 2 * (v.2.2.2 : ℝ) = 0 :=
    thd_eq_zero_of_mem_sqrtTwoCone₁ hv₁
  obtain ⟨hc, hk⟩ := eq_zero_of_add_sqrtTwo_mul _ _ h₃
  have hplane : (0 : ℝ) = (v.1 : ℝ) + Real.sqrt 2 * (v.2.1 : ℝ) := by
    simpa [h₃] using thd_of_mem_sqrtTwoCone₂ hv₂
  obtain ⟨ha, hb⟩ := eq_zero_of_add_sqrtTwo_mul _ _ hplane.symm
  simp [ha, hb, hc, hk]

/-- The intersection of the two cones is not lattice rational. It is the ray spanned by
`(√2, -1, 0)`, which contains no nonzero image of a lattice vector, whereas a lattice-rational
cone other than `⊥` always contains one. -/
theorem not_isLatticeRational_sqrtTwoCone_inf :
    ¬ IsLatticeRational sqrtTwoMap (sqrtTwoCone₁ ⊓ sqrtTwoCone₂) := by
  intro h
  have hne : sqrtTwoCone₁ ⊓ sqrtTwoCone₂ ≠ ⊥ := by
    intro hbot
    have hmem := mem_inf_sqrtTwoCone
    rw [hbot] at hmem
    have hzero : ((Real.sqrt 2, -1, 0) : ℝ × ℝ × ℝ) = 0 := hmem
    exact Real.sqrt_ne_zero'.2 (by norm_num) (congrArg Prod.fst hzero)
  obtain ⟨v, hv, hv0⟩ := h.exists_mem_ne_zero hne
  exact hv0 (sqrtTwoMap_eq_zero_of_mem_inf hv)

/-- **Toricity is not preserved by arbitrary intersections.** For the injective map
`sqrtTwoMap`, whose image is nondiscrete because its intersection with the `z`-axis is dense, the
two toric cones `sqrtTwoCone₁` and `sqrtTwoCone₂` meet in a cone that is not even lattice
rational, let alone toric. -/
theorem not_isToricCone_sqrtTwoCone_inf :
    ¬ IsToricCone sqrtTwoMap (sqrtTwoCone₁ ⊓ sqrtTwoCone₂) := fun h ↦
  not_isLatticeRational_sqrtTwoCone_inf h.rational

/-! ### Salience is an independent condition -/

/-- The full line of the rank-one lattice `ℤ ⊆ ℝ` is a lattice-rational pointed cone. Together
with `not_isToricCone_top_intCast` this shows that salience is a genuinely independent condition
in `IsToricCone`. -/
theorem isLatticeRational_top_intCast :
    IsLatticeRational (Int.castAddHom ℝ) (⊤ : PointedCone ℝ ℝ) := by
  refine isLatticeRational_iff.mpr ⟨{1, -1}, le_antisymm (fun x _ ↦ ?_) le_top⟩
  rcases le_total (0 : ℝ) x with hx | hx
  · have hmem : (1 : ℝ) ∈ PointedCone.hull ℝ ((Int.castAddHom ℝ) '' (({1, -1} : Finset ℤ) : Set ℤ))
      := PointedCone.subset_hull ⟨1, by simp, by simp⟩
    simpa using PointedCone.smul_mem _ hx hmem
  · have hmem : (-1 : ℝ) ∈
        PointedCone.hull ℝ ((Int.castAddHom ℝ) '' (({1, -1} : Finset ℤ) : Set ℤ)) :=
      PointedCone.subset_hull ⟨-1, by simp, by simp⟩
    simpa using PointedCone.smul_mem _ (neg_nonneg.2 hx) hmem

/-- **Salience is not implied by `PointedCone`.** The full line of the rank-one lattice `ℤ ⊆ ℝ` is
a finitely generated, lattice-rational pointed cone, but it is not a toric cone: it fails
salience. A cone of an affine toric variety is never a line. -/
theorem not_isToricCone_top_intCast :
    ¬ IsToricCone (Int.castAddHom ℝ) (⊤ : PointedCone ℝ ℝ) := fun h ↦
  h.salient 1 trivial one_ne_zero trivial

end TauCeti.Toric
