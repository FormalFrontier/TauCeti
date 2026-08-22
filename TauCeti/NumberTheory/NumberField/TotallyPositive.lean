/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Units
public import TauCeti.GroupTheory.Index
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally positive elements of a number field

An element `x` of a number field `K` is **totally positive** when it is strictly positive under
every real embedding `K →+* ℝ` — equivalently, at every real infinite place. This is the archimedean
positivity condition underlying the *narrow* class group of the multiquadratic roadmap (Layer 3):
the narrow class group `Cl⁺(K)` is the quotient of the fractional ideals by the principal ideals
admitting a totally positive generator. It surjects onto the ordinary class group `Cl(K)`
(forgetting the positivity condition), and the `2`-rank of `Cl⁺(K)` is what the genus-theory
`t - 1` formula (with `t` the number of ramified primes) computes for a **real quadratic** field
in the multiquadratic roadmap.

This file introduces the predicate and its multiplicative structure. The totally positive elements
are closed under multiplication and inversion and contain every nonzero square, so the totally
positive units form a subgroup of `Kˣ`. That subgroup is the kernel of the sign (signature) map on
units; the signs *not* realized by units measure the difference between `Cl⁺(K)` and `Cl(K)`.

The file also records that `totallyPositiveUnits` has **finite index** — a finite intersection, over
the real places, of the finite-index preimages of the positive units of `ℝ` — which is what makes
the narrow class group finite (see `NarrowClassGroup.Finite`).

## Main definitions and results

* `NumberField.IsTotallyPositive`: strict positivity at every real place, with
  `isTotallyPositive_iff` its introduction/elimination form.
* `NumberField.isTotallyPositive_one`, `IsTotallyPositive.mul`, `IsTotallyPositive.inv`,
  `isTotallyPositive_sq`: the multiplicative structure, including that nonzero squares are totally
  positive.
* `NumberField.isTotallyPositive_ratCast`: a positive rational number is totally positive, with
  `NumberField.isTotallyPositive_intCast` its integer special case.
* `NumberField.totallyPositiveUnits`: the subgroup of totally positive units of `Kˣ` (the
  kernel of the unit signature map), with `sq_mem_totallyPositiveUnits`. For a totally complex field
  it is everything (`totallyPositiveUnits_eq_top`), since total positivity is then vacuous
  (`not_isReal_of_isTotallyComplex` makes `IsTotallyPositive` `simp` to `True`).
* `NumberField.totallyPositiveIntegerUnits`: the corresponding subgroup of the arithmetic
  units `(𝓞 K)ˣ`, the preimage of `totallyPositiveUnits` under `(𝓞 K)ˣ → Kˣ`, with
  `mem_totallyPositiveIntegerUnits` and `sq_mem_totallyPositiveIntegerUnits`.
* `NumberField.norm_pos_of_isTotallyPositive`: the field norm of a nonzero totally positive
  element is strictly positive.
* `NumberField.finiteIndex_totallyPositiveUnits`: `totallyPositiveUnits` has finite index
  (via `Units.instFiniteIndexPosSubgroup` and the general `Subgroup.instFiniteIndexComap`).
-/

public section

open NumberField InfinitePlace

namespace NumberField

variable {K : Type*} [Field K]

/-- An element of a number field is **totally positive** when it is strictly positive under every
real embedding `K →+* ℝ` (equivalently, at every real infinite place `w`). For a totally complex
field the condition is vacuous; the content is at the real places. -/
def IsTotallyPositive (x : K) : Prop :=
  ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < embedding_of_isReal hw x

/-- Introduction and elimination form of `IsTotallyPositive`: total positivity is exactly strict
positivity at every real infinite place. -/
@[simp, grind =] theorem isTotallyPositive_iff {x : K} :
    IsTotallyPositive x ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < embedding_of_isReal hw x :=
  Iff.rfl

/-- The element `1` is totally positive: every real embedding sends it to `1 > 0`. -/
theorem isTotallyPositive_one : IsTotallyPositive (1 : K) :=
  isTotallyPositive_iff.mpr fun _ _ => by rw [map_one]; exact one_pos

/-- Totally positive elements are closed under multiplication: a product of positives is positive at
each real place. -/
theorem IsTotallyPositive.mul {x y : K} (hx : IsTotallyPositive x) (hy : IsTotallyPositive y) :
    IsTotallyPositive (x * y) :=
  isTotallyPositive_iff.mpr fun w hw => by rw [map_mul]; exact mul_pos (hx w hw) (hy w hw)

/-- A totally positive element has a totally positive inverse: real embeddings send inverses to
inverses, and the reciprocal of a positive real is positive. -/
theorem IsTotallyPositive.inv {x : K} (hx : IsTotallyPositive x) : IsTotallyPositive x⁻¹ :=
  isTotallyPositive_iff.mpr fun w hw => by rw [map_inv₀]; exact inv_pos.mpr (hx w hw)

/-- Every nonzero square is totally positive: at each real place its value is the square of a
nonzero real. -/
theorem isTotallyPositive_sq {x : K} (hx : x ≠ 0) : IsTotallyPositive (x ^ 2) :=
  isTotallyPositive_iff.mpr fun w hw => by
    rw [map_pow]; exact sq_pos_iff.mpr ((map_ne_zero _).mpr hx)

/-- A positive rational number is totally positive in any field: every real embedding fixes it.
The cast is `Rat.cast`, which agrees with `algebraMap ℚ K` whenever the latter is available. -/
theorem isTotallyPositive_ratCast {q : ℚ} (hq : 0 < q) :
    IsTotallyPositive ((q : ℚ) : K) :=
  isTotallyPositive_iff.mpr fun w hw => by
    rw [map_ratCast]
    exact_mod_cast hq

/-- A positive rational integer is totally positive: the integer special case of
`isTotallyPositive_ratCast`. -/
theorem isTotallyPositive_intCast {n : ℤ} (hn : 0 < n) :
    IsTotallyPositive ((n : ℤ) : K) := by
  rw [← Rat.cast_intCast (α := K) n]
  exact isTotallyPositive_ratCast (by exact_mod_cast hn)

/-- The subgroup of **totally positive units** of `Kˣ`: the intersection, over the real infinite
places `w`, of the preimages of the positive units of `ℝ` under the real embedding `w`. It is the
kernel of the sign (signature) map on units, and controls the comparison between the narrow class
group `Cl⁺(K)` and the ordinary class group `Cl(K)`. -/
noncomputable def totallyPositiveUnits : Subgroup Kˣ :=
  ⨅ (w : InfinitePlace K) (hw : w.IsReal),
    (Units.posSubgroup ℝ).comap (Units.map (embedding_of_isReal hw).toMonoidHom)

/-- A unit lies in `totallyPositiveUnits` exactly when its underlying field element is totally
positive. -/
@[simp]
theorem mem_totallyPositiveUnits {u : Kˣ} :
    u ∈ totallyPositiveUnits ↔ IsTotallyPositive (u : K) := by
  simp only [totallyPositiveUnits, Subgroup.mem_iInf, Subgroup.mem_comap,
    Units.mem_posSubgroup, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    isTotallyPositive_iff]

/-- Every square of a unit is a totally positive unit. -/
theorem sq_mem_totallyPositiveUnits (u : Kˣ) : u ^ 2 ∈ totallyPositiveUnits := by
  rw [mem_totallyPositiveUnits, Units.val_pow_eq_pow_val]
  exact isTotallyPositive_sq (Units.ne_zero u)

/-- A **totally complex** field has no real infinite places. As a `simp` lemma this discharges the
vacuous real-place hypotheses in totally-positive statements: `IsTotallyPositive x` then reduces to
`True` (via `isTotallyPositive_iff`), so total positivity is automatic for every element. -/
@[simp] theorem not_isReal_of_isTotallyComplex [IsTotallyComplex K] (w : InfinitePlace K) :
    ¬ w.IsReal :=
  not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)

/-- For a totally complex field every unit is (vacuously) totally positive:
`totallyPositiveUnits = ⊤`. -/
@[simp] theorem totallyPositiveUnits_eq_top [IsTotallyComplex K] :
    totallyPositiveUnits (K := K) = ⊤ := by
  ext u; simp

variable [NumberField K]

/-- The subgroup of **totally positive integer units** of `(𝓞 K)ˣ`: the preimage of
`totallyPositiveUnits` under the inclusion `(𝓞 K)ˣ → Kˣ`, i.e. the integer units whose image in `K`
is totally positive. It is the kernel of the integer-unit signature map; the signatures realized by
units — the quotient of `(𝓞 K)ˣ` by this subgroup — are the archimedean input to the comparison
between the narrow and ordinary class groups. -/
noncomputable def totallyPositiveIntegerUnits : Subgroup (𝓞 K)ˣ :=
  totallyPositiveUnits.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

omit [NumberField K] in
/-- Membership in `totallyPositiveIntegerUnits` is total positivity of the image in `K`. -/
@[simp] theorem mem_totallyPositiveIntegerUnits {u : (𝓞 K)ˣ} :
    u ∈ totallyPositiveIntegerUnits ↔ IsTotallyPositive (algebraMap (𝓞 K) K (u : 𝓞 K)) := by
  simp only [totallyPositiveIntegerUnits, Subgroup.mem_comap, mem_totallyPositiveUnits,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]

omit [NumberField K] in
/-- Every square of an integer unit is a totally positive integer unit. -/
theorem sq_mem_totallyPositiveIntegerUnits (u : (𝓞 K)ˣ) :
    u ^ 2 ∈ totallyPositiveIntegerUnits := by
  rw [totallyPositiveIntegerUnits, Subgroup.mem_comap, map_pow]
  exact sq_mem_totallyPositiveUnits _

omit [NumberField K] in
/-- For a totally complex field every integer unit is (vacuously) totally positive:
`totallyPositiveIntegerUnits = ⊤`. -/
@[simp] theorem totallyPositiveIntegerUnits_eq_top [IsTotallyComplex K] :
    totallyPositiveIntegerUnits (K := K) = ⊤ := by
  ext u; simp

/-- **The norm of a totally positive element is positive.** Group the complex embeddings of `K` by
the infinite place they define. A real place contributes the single factor
`embedding_of_isReal hw x`, which total positivity makes equal to `w x`; a complex place contributes
a conjugate pair `φ x · conj (φ x) = (w x) ^ 2`. So `Algebra.norm ℚ x` equals the product
`∏ w, w x ^ mult w`, which is `|Algebra.norm ℚ x|` by `InfinitePlace.prod_eq_abs_norm`; being
nonzero, it is positive.

Over a totally complex field the hypothesis `IsTotallyPositive x` is vacuous
(`not_isReal_of_isTotallyComplex`), so this covers imaginary quadratic fields as a special case. -/
theorem norm_pos_of_isTotallyPositive {x : K} (hx : x ≠ 0) (hpos : IsTotallyPositive x) :
    0 < Algebra.norm ℚ x := by
  classical
  -- Each infinite place contributes `w x ^ mult w`, with no sign lost at the real places.
  have key : ((Algebra.norm ℚ x : ℚ) : ℂ) =
      ((∏ w : InfinitePlace K, w x ^ mult w : ℝ) : ℂ) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x) (fun φ => by simp [RingHom.equivRatAlgHom]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases hw : IsReal w
    · -- A real place has a single embedding above it, namely `embedding w`.
      have hcard : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w).card = 1 := by
        rw [InfinitePlace.card_filter_mk_eq, hw.mult_eq_one]
      have hmem : embedding w ∈ Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mk_embedding]
      rw [Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hmem, fun y hy => Finset.card_le_one.mp hcard.le y hy _ hmem⟩,
        Finset.prod_singleton, hw.mult_eq_one, pow_one, ← embedding_of_isReal_apply hw]
      -- Total positivity identifies the real embedding with the place.
      have hval : w x = embedding_of_isReal hw x := by
        rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, abs_of_pos (hpos w hw)]
      rw [hval]
    · -- A complex place has the conjugate pair `embedding w`, `conj (embedding w)` above it.
      have hne : embedding w ≠ ComplexEmbedding.conjugate (embedding w) := fun h =>
        hw (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
      have hsub : ({embedding w, ComplexEmbedding.conjugate (embedding w)} : Finset (K →+* ℂ)) ⊆
          Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w := by
        intro φ hφ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hφ with rfl | rfl
        · exact mk_embedding w
        · rw [mk_conjugate_eq]; exact mk_embedding w
      have hcard : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w).card = 2 := by
        rw [InfinitePlace.card_filter_mk_eq, (not_isReal_iff_isComplex.mp hw).mult_eq_two]
      rw [(Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hne])).symm,
        Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, norm_embedding_eq,
        (not_isReal_iff_isComplex.mp hw).mult_eq_two]
  have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, w x ^ mult w := by
    exact_mod_cast key
  rw [InfinitePlace.prod_eq_abs_norm] at hreal
  have habs : |Algebra.norm ℚ x| = Algebra.norm ℚ x := by exact_mod_cast hreal.symm
  have hne : Algebra.norm ℚ x ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (Module.finBasis ℚ K)).mpr hx
  exact lt_of_le_of_ne (abs_eq_self.mp habs) (Ne.symm hne)

/-- `totallyPositiveUnits` has **finite index** in `Kˣ`: it is a finite intersection, over the real
infinite places, of the finite-index preimages of the positive units of `ℝ` (via the general
`Units.instFiniteIndexPosSubgroup` and `Subgroup.instFiniteIndexComap`). -/
instance finiteIndex_totallyPositiveUnits : (totallyPositiveUnits (K := K)).FiniteIndex := by
  rw [totallyPositiveUnits, iInf_subtype']
  exact Subgroup.finiteIndex_iInf fun _ => inferInstance

end NumberField
