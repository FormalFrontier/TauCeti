/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.RingTheory.Valuation.Discrete.Normalize

/-!
# Extensions of places: the ramification index and the relative degree

Let `F' / k'` be a field extension lying over `F / k`, with `F'` algebraic over `F`. Restricting
the valuation of a place `P'` of `F' / k'` to `F` gives a valuation of `F` that is trivial on the
constants and — because `F'` is algebraic over `F`, so that a valuation ring of `F'` containing
`F` would be all of `F'` — nontrivial. Normalizing it produces a place `P = P'.restrict k F` of
`F / k`, the place of `F` that `P'` *lies over*, and the index divided out in the normalization
is the **ramification index** `e(P' | P)`. The residue field of `P` embeds in the residue field
of `P'`, and the degree of that extension is the **relative degree** `f(P' | P)`.

The main theorem is the bound `e(P' | P) · f(P' | P) ≤ [F' : F]`: residues of elements of `𝒪_{P'}`
that are independent over `F_P`, multiplied by the powers `t^j` of a prime element for `P'` with
`0 ≤ j < e`, are independent over `F`, because the orders of the resulting blocks are pairwise
distinct modulo `e`.

## Main definitions

* `TauCeti.Place.restrict`: the place of `F / k` that a place of `F' / k'` lies over.
* `TauCeti.Place.ramificationIdx`: the ramification index `e(P' | P)`.
* `TauCeti.Place.relativeDegree`: the relative degree `f(P' | P) = [F'_{P'} : F_P]`.

## Main results

* `TauCeti.Place.ord_algebraMap_restrict`: the defining property `ord_{P'} = e · ord_P` on `F`.
* `TauCeti.Place.restrict_eq_iff_integers_le`, `TauCeti.Place.restrict_eq_iff_forall_ord_pos`
  and `TauCeti.Place.restrict_eq_iff_exists_ord_eq`: the three characterizations of `P' ∣ P`
  (Stichtenoth, Proposition 3.1.4), by the containment of valuation rings, by the containment of
  maximal ideals, and by the scaling of the order functions. Together with
  `TauCeti.Place.restrict` they say that every place of `F'` lies over exactly one place of `F`.
* `TauCeti.Place.linearIndependent_mul_pow_of_linearIndependent_residue`: the independence
  statement carrying the fundamental inequality, together with the three ingredients of its
  proof — `TauCeti.Place.ord_sum_eq_zero_of_isUnit`,
  `TauCeti.Place.sum_ne_zero_of_linearIndependent_residue` and
  `TauCeti.Place.ramificationIdx_dvd_ord_sum_of_linearIndependent_residue` — and the
  ultrametric estimate `TauCeti.Place.sum_ne_zero_of_ord_eq_mul_add_natCast` with
  `TauCeti.Place.ord_sum_le_of_ord_eq_mul_add_natCast` that combines them.
* `TauCeti.Place.ramificationIdx_mul_relativeDegree_le_finrank`: `e(P' ∣ P) · f(P' ∣ P) ≤
  [F' : F]`, with `TauCeti.Place.ramificationIdx_le_finrank` and
  `TauCeti.Place.relativeDegree_le_finrank` its two halves (Stichtenoth, Corollary 3.1.12).
* `TauCeti.Place.finiteDimensional_residueField_restrict`: the relative degree is finite, so it
  is not the junk value of `Module.finrank`; `TauCeti.Place.one_le_relativeDegree` and
  `TauCeti.Place.ramificationIdx_pos` are the matching lower bounds.
* `TauCeti.Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict`:
  `[k' : k] · deg P' = f(P' ∣ P) · deg P`, the comparison of the degrees of `P'` and of the place
  it lies over.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

open scoped WithZero

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section Restrict

variable (k F) (P' : Place k' F')

/-- The valuation of `P'` restricted to `F` is trivial on the constants of `F`. -/
private theorem isTrivialOn_comap : (P'.valuation.comap (algebraMap F F')).IsTrivialOn k where
  eq_one c hc := by
    have hmap : algebraMap F F' (algebraMap k F c) = algebraMap k' F' (algebraMap k k' c) := by
      rw [← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k k' F']
    have hc' : algebraMap k k' c ≠ 0 := fun h ↦ hc
      ((algebraMap k k').injective (by rw [h, map_zero]))
    simpa only [Valuation.comap_apply, hmap] using P'.isTrivialOn.eq_one _ hc'

/-- The order function of `P'` restricted to `F` is the order function of the restricted
valuation. -/
private theorem ord_comap (f : F) :
    Valuation.ord (P'.valuation.comap (algebraMap F F')) f = P'.ord (algebraMap F F' f) := by
  rw [Valuation.ord_def, ord_def, Valuation.comap_apply]

/-- The valuation of `P'` restricted to `F` is nontrivial: an algebraic extension of a field
contained in a valuation ring is contained in that valuation ring, so a place of `F'` trivial on
`F` would have all of `F'` as its valuation ring. -/
private theorem ordIndex_comap_ne_zero [Algebra.IsIntegral F F'] :
    Valuation.ordIndex (P'.valuation.comap (algebraMap F F')) ≠ 0 := fun h ↦ by
  have hall := (Valuation.ordIndex_eq_zero_iff _).mp h
  refine P'.integers_ne_top (top_unique fun y _ ↦ ?_)
  refine P'.mem_integers_of_isIntegral (R := F) (fun f ↦ ?_) (Algebra.IsIntegral.isIntegral y)
  exact P'.mem_integers_iff_ord_nonneg.mpr (by rw [← ord_comap F P' f, hall f])

variable [Algebra.IsIntegral F F']

/-- **The place of `F / k` that a place of `F' / k'` lies over**: the normalization of the
restriction of its valuation to `F` (Stichtenoth, Definition 3.1.2). Every place of `F'` lies
over exactly one place of `F`; which place is characterized in
`TauCeti.Place.restrict_eq_iff_integers_le`. -/
noncomputable def restrict : Place k F where
  valuation := (P'.valuation.comap (algebraMap F F')).normalization
  valuation_surjective :=
    Valuation.normalization_surjective _ (ordIndex_comap_ne_zero F P')
  isTrivialOn := by
    have := isTrivialOn_comap k F P'
    exact Valuation.IsTrivialOn.normalization _

/-- **The ramification index** `e(P' ∣ P)` of a place `P'` of `F' / k'` over the place `P` of
`F / k` it lies over: the factor by which the order function at `P'` scales the order function
at `P` (Stichtenoth, Definition 3.1.5). -/
noncomputable def ramificationIdx : ℕ :=
  Valuation.ordIndex (P'.valuation.comap (algebraMap F F'))

omit [Algebra.IsIntegral F F'] in
/-- The ramification index is the order index of the restricted valuation. -/
lemma ramificationIdx_def :
    ramificationIdx F P' = Valuation.ordIndex (P'.valuation.comap (algebraMap F F')) := by
  rw [ramificationIdx]

/-- The ramification index of a restricted place is positive. -/
theorem ramificationIdx_pos : 0 < ramificationIdx F P' :=
  Nat.pos_of_ne_zero (ordIndex_comap_ne_zero F P')

private theorem valuation_restrict :
    (P'.restrict k F).valuation = (P'.valuation.comap (algebraMap F F')).normalization := (rfl)

/-- **The defining property of the ramification index** (Stichtenoth, Definition 3.1.5): on `F`
the order function at `P'` is `e(P' ∣ P)` times the order function at `P`. -/
theorem ord_algebraMap_restrict (f : F) :
    P'.ord (algebraMap F F' f) = ramificationIdx F P' * (P'.restrict k F).ord f := by
  have key : (P'.restrict k F).ord f =
      Valuation.ord (P'.valuation.comap (algebraMap F F')).normalization f := by
    rw [ord_def, valuation_restrict, Valuation.ord_def]
  rw [← ord_comap F P' f, ramificationIdx, key,
    ← Valuation.ord_normalization_mul_ordIndex _ f, mul_comm]

/-- An element of `F` is integral at the restriction exactly when it is integral at `P'`. -/
theorem mem_integers_restrict_iff (f : F) :
    f ∈ (P'.restrict k F).integers ↔ algebraMap F F' f ∈ P'.integers := by
  rw [mem_integers_iff_ord_nonneg, mem_integers_iff_ord_nonneg, ord_algebraMap_restrict k F P' f]
  exact ⟨fun h ↦ mul_nonneg (by positivity) h,
    fun h ↦ nonneg_of_mul_nonneg_right h (by exact_mod_cast ramificationIdx_pos F P')⟩


/-- **`P' ∣ P` by valuation rings** (Stichtenoth, Proposition 3.1.4): the place of `F / k` that
`P'` lies over is the unique place whose valuation ring is carried into the valuation ring of
`P'`. -/
theorem restrict_eq_iff_integers_le (P : Place k F) :
    P'.restrict k F = P ↔ ∀ f ∈ P.integers, algebraMap F F' f ∈ P'.integers := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl f hf
    exact (mem_integers_restrict_iff k F P' f).mp hf
  · refine (eq_of_integers_le (SetLike.le_def.mpr fun f hf ↦ ?_)).symm
    exact (mem_integers_restrict_iff k F P' f).mpr (h f hf)

/-- **`P' ∣ P` by maximal ideals** (Stichtenoth, Proposition 3.1.4): it is enough that the
functions vanishing at `P` vanish at `P'`. -/
theorem restrict_eq_iff_forall_ord_pos (P : Place k F) :
    P'.restrict k F = P ↔ ∀ f : F, 0 < P.ord f → 0 < P'.ord (algebraMap F F' f) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl f hf
    rw [ord_algebraMap_restrict k F P' f]
    exact mul_pos (by exact_mod_cast ramificationIdx_pos F P') hf
  rw [restrict_eq_iff_integers_le]
  intro f hf
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [P.isUniformizer_iff_ord_eq_one] at ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hb : 0 < P'.ord (algebraMap F F' t) := h t (by omega)
  have hmap0 : algebraMap F F' f ≠ 0 := by simpa using hf0
  have hmapt0 : algebraMap F F' t ≠ 0 := by simpa using ht0
  refine P'.mem_integers_iff_ord_nonneg.mpr ?_
  by_contra hneg
  rw [not_le] at hneg
  set m := (P'.ord (algebraMap F F' t)).toNat with hm
  have hpos := h (f ^ m * t) (by
    rw [P.ord_mul (pow_ne_zero _ hf0) ht0, P.ord_pow, ht]
    have := P.mem_integers_iff_ord_nonneg.mp hf
    positivity)
  rw [map_mul, map_pow, P'.ord_mul (pow_ne_zero _ hmap0) hmapt0, P'.ord_pow] at hpos
  have hle : (m : ℤ) * P'.ord (algebraMap F F' f) ≤ -(m : ℤ) := by
    have : P'.ord (algebraMap F F' f) ≤ -1 := by omega
    nlinarith [Int.natCast_nonneg m]
  omega

/-- **`P' ∣ P` by the scaling of orders** (Stichtenoth, Proposition 3.1.4): the place `P'` lies
over `P` exactly when the order function at `P'` is a positive multiple of the order function at
`P` along `F`, and the multiple is then the ramification index. -/
theorem restrict_eq_iff_exists_ord_eq (P : Place k F) :
    P'.restrict k F = P ↔
      ∃ e : ℕ, 0 < e ∧ ∀ f : F, P'.ord (algebraMap F F' f) = e * P.ord f := by
  refine ⟨fun h ↦ ⟨ramificationIdx F P', ramificationIdx_pos F P', fun f ↦ ?_⟩, ?_⟩
  · rw [ord_algebraMap_restrict k F P' f, h]
  · rintro ⟨e, he, h⟩
    rw [restrict_eq_iff_forall_ord_pos]
    intro f hf
    rw [h f]
    exact mul_pos (by exact_mod_cast he) hf

/-- The ramification index is the only positive scaling factor between the two order
functions. -/
theorem ramificationIdx_eq_of_forall_ord_eq {e : ℕ}
    (h : ∀ f : F, P'.ord (algebraMap F F' f) = e * (P'.restrict k F).ord f) :
    ramificationIdx F P' = e := by
  obtain ⟨f, hf⟩ := (P'.restrict k F).ord_surjective 1
  have h1 := h f
  rw [ord_algebraMap_restrict k F P' f, hf] at h1
  exact_mod_cast by omega

end Restrict

section ResidueField

variable (k F) (P' : Place k' F') [Algebra.IsIntegral F F']

/-- The valuation of the restricted place extends along `F → F'`; hence Mathlib's generic
valuation-extension API supplies the valuation-ring algebra map, its locality, and the induced
residue-field extension. -/
instance instHasExtensionValuation :
    Valuation.HasExtension (P'.restrict k F).valuation P'.valuation where
  val_isEquiv_comap := by
    rw [valuation_restrict]
    exact Valuation.isEquiv_normalization _

/-- The valuation ring of the restriction is carried into the valuation ring of `P'`, so the
latter is an algebra over the former. -/
noncomputable instance instAlgebraIntegers : Algebra (P'.restrict k F).integers P'.integers :=
  (((algebraMap F F').comp (algebraMap (P'.restrict k F).integers F)).codRestrict
    P'.integers fun x ↦ (mem_integers_restrict_iff k F P' (x : F)).mp x.2).toAlgebra

@[simp]
theorem coe_algebraMap_integers (x : (P'.restrict k F).integers) :
    ((algebraMap (P'.restrict k F).integers P'.integers x : P'.integers) : F') =
      algebraMap F F' (x : F) := (rfl)

/-- The valuation-ring algebra map is local, so it induces the residue-field extension used by
`relativeDegree`. -/
instance instIsLocalHomIntegers :
    IsLocalHom (algebraMap (P'.restrict k F).integers P'.integers) where
  map_nonunit a ha := by
    have ha0 : (a : F) ≠ 0 := by
      rintro h
      have ha_eq_zero : a = 0 := Subtype.ext h
      rw [ha_eq_zero] at ha
      simp at ha
    have hmap0 : algebraMap F F' (a : F) ≠ 0 := by simpa using ha0
    have h1 : P'.ord (algebraMap F F' (a : F)) = 0 :=
      (P'.isUnit_iff_ord_eq_zero (x := algebraMap _ P'.integers a) (by simpa using hmap0)).mp ha
    rw [ord_algebraMap_restrict k F P' (a : F)] at h1
    have he : (ramificationIdx F P' : ℤ) ≠ 0 := by
      have := ramificationIdx_pos F P'
      omega
    exact ((P'.restrict k F).isUnit_iff_ord_eq_zero ha0).mpr
      ((mul_eq_zero.mp h1).resolve_left he)

/-- The **relative degree** `f(P' ∣ P) = [F'_{P'} : F_P]` of a place `P'` of `F' / k'` over the
place `P` of `F / k` it lies over (Stichtenoth, Definition 3.1.5). -/
noncomputable def relativeDegree : ℕ :=
  Module.finrank (P'.restrict k F).ResidueField P'.ResidueField

/-- The relative degree is the finrank of the extension of residue fields. -/
theorem relativeDegree_def :
    relativeDegree k F P' = Module.finrank (P'.restrict k F).ResidueField P'.ResidueField := by
  rw [relativeDegree]

/-- **The degree of a place and the degree of the place below it** (Stichtenoth, Section III.1):
the residue field `F'_{P'}` sits in the two towers `k ⊆ k' ⊆ F'_{P'}` and `k ⊆ F_P ⊆ F'_{P'}`,
whose successive degrees are `[k' : k]`, `deg P'` and `deg P`, `f(P' ∣ P)`.  Comparing them gives
`[k' : k] · deg P' = f(P' ∣ P) · deg P`.

The factor `[k' : k]` is mandatory and the identity is stated cross-multiplied: when the constant
field grows, `deg P'` falls short of `f(P' ∣ P) · deg P` by exactly that factor. -/
theorem finrank_mul_degree_eq_relativeDegree_mul_degree_restrict :
    Module.finrank k k' * P'.degree = relativeDegree k F P' * (P'.restrict k F).degree := by
  -- The residue field of `P'` is a `k`-algebra through the constants `k'` of `F'`.  This is a
  -- local instance: for `k = k'` it would compete with the constant-field algebra of `P'`.
  let _ : Algebra k P'.integers := ((algebraMap k' P'.integers).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' P'.integers := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k (P'.restrict k F).integers P'.integers := by
    refine .of_algebraMap_eq fun c ↦ Subtype.ext ?_
    rw [coe_algebraMap_integers, coe_algebraMap_constants, ← IsScalarTower.algebraMap_apply k F F']
    exact (P'.coe_algebraMap_constants (algebraMap k k' c)).trans
      (IsScalarTower.algebraMap_apply k k' F' c).symm
  rw [degree_eq_finrank, degree_eq_finrank, relativeDegree_def,
    Module.finrank_mul_finrank k k' P'.ResidueField,
    mul_comm (Module.finrank (P'.restrict k F).ResidueField P'.ResidueField),
    Module.finrank_mul_finrank k (P'.restrict k F).ResidueField P'.ResidueField]

end ResidueField

section Independence

variable (k F) (P' : Place k' F') [Algebra.IsIntegral F F']

private theorem valuation_lt_of_ord_lt {x y : F'} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : P'.ord y < P'.ord x) : P'.valuation x < P'.valuation y := by
  rw [P'.valuation_eq_exp_neg_ord hx, P'.valuation_eq_exp_neg_ord hy, WithZero.exp_lt_exp]
  omega

private theorem eq_of_mul_add_natCast_eq {e : ℕ} {j j' : Fin e} {a b : ℤ}
    (h : (e : ℤ) * a + (j : ℕ) = (e : ℤ) * b + (j' : ℕ)) : j = j' := by
  have key : ∀ (m : ℤ) (l : Fin e), ((e : ℤ) * m + (l : ℕ)) % (e : ℤ) = (l : ℕ) := by
    intro m l
    rw [add_comm, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast l.2)
  have h' := congrArg (· % (e : ℤ)) h
  simp only [key] at h'
  exact Fin.ext (by exact_mod_cast h')

/-- The valuation of a sum whose nonzero terms have pairwise distinct orders is the valuation of a
term of least order. -/
private theorem exists_valuation_sum_eq {e : ℕ} (A : Fin e → F')
    (hAord : ∀ j, A j ≠ 0 → ∃ m : ℤ, P'.ord (A j) = (e : ℤ) * m + (j : ℕ))
    {j₁ : Fin e} (hj₁ : A j₁ ≠ 0) :
    ∃ j₀, A j₀ ≠ 0 ∧ P'.ord (A j₀) ≤ P'.ord (A j₁) ∧
      P'.valuation (∑ j, A j) = P'.valuation (A j₀) := by
  classical
  set J : Finset (Fin e) := {j | A j ≠ 0} with hJdef
  have hJ : J.Nonempty := ⟨j₁, by simp [hJdef, hj₁]⟩
  obtain ⟨j₀, hj₀J, hj₀⟩ := J.exists_min_image (fun j ↦ P'.ord (A j)) hJ
  have hj₀A : A j₀ ≠ 0 := by simpa [hJdef] using hj₀J
  have hlt : ∀ j ∈ (Finset.univ : Finset (Fin e)) \ {j₀},
      P'.valuation (A j) < P'.valuation (A j₀) := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
    by_cases hAj : A j = 0
    · rw [hAj, map_zero]
      exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hj₀A)
    · obtain ⟨m, hm⟩ := hAord j hAj
      obtain ⟨m₀, hm₀⟩ := hAord j₀ hj₀A
      have hne : P'.ord (A j) ≠ P'.ord (A j₀) := by
        rw [hm, hm₀]
        exact fun hcontra ↦ hj.2 (eq_of_mul_add_natCast_eq hcontra)
      have hge := hj₀ j (by simp [hJdef, hAj])
      exact valuation_lt_of_ord_lt P' hAj hj₀A (by omega)
  exact ⟨j₀, hj₀A, hj₀ j₁ (by simp [hJdef, hj₁]),
    P'.valuation.map_sum_eq_of_lt (Finset.mem_univ j₀) hlt⟩

/-- **A sum whose nonzero terms have pairwise distinct orders is nonzero.** The hypothesis is the
form in which the distinctness is met in the extension theory: the order of `A j` is congruent to
`j` modulo `e`, so no two nonzero terms can cancel. -/
theorem sum_ne_zero_of_ord_eq_mul_add_natCast {e : ℕ} (A : Fin e → F')
    (hAord : ∀ j, A j ≠ 0 → ∃ m : ℤ, P'.ord (A j) = (e : ℤ) * m + (j : ℕ))
    {j₁ : Fin e} (hj₁ : A j₁ ≠ 0) : ∑ j, A j ≠ 0 := by
  obtain ⟨j₀, hj₀A, -, hval⟩ := exists_valuation_sum_eq P' A hAord hj₁
  intro hsum
  rw [hsum, map_zero] at hval
  exact (Valuation.ne_zero_iff _).mpr hj₀A hval.symm

/-- **The order of a sum whose nonzero terms have pairwise distinct orders is the least of them**;
in particular it is at most the order of any nonzero term. -/
theorem ord_sum_le_of_ord_eq_mul_add_natCast {e : ℕ} (A : Fin e → F')
    (hAord : ∀ j, A j ≠ 0 → ∃ m : ℤ, P'.ord (A j) = (e : ℤ) * m + (j : ℕ))
    {j₁ : Fin e} (hj₁ : A j₁ ≠ 0) : P'.ord (∑ j, A j) ≤ P'.ord (A j₁) := by
  obtain ⟨j₀, -, hle, hval⟩ := exists_valuation_sum_eq P' A hAord hj₁
  calc P'.ord (∑ j, A j) = P'.ord (A j₀) := by simp only [ord_def, hval]
    _ ≤ P'.ord (A j₁) := hle

/-- A combination of elements of `𝒪_{P'}` with coefficients in `𝒪_P`, one of them a unit, is a
unit at `P'` as soon as the residues of the elements are independent over the residue field of
`P`: its residue is the corresponding nontrivial combination of the residues. -/
private theorem ord_sum_eq_zero {ι : Type*} [Fintype ι] (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    (b : ι → (P'.restrict k F).integers) {i₀ : ι} (hb₀ : IsUnit (b i₀)) :
    (∑ i, algebraMap F F' (b i : F) * (s i : F')) ≠ 0 ∧
      P'.ord (∑ i, algebraMap F F' (b i : F) * (s i : F')) = 0 := by
  classical
  set B : P'.integers := ∑ i, algebraMap _ P'.integers (b i) * s i with hB
  have hcoe : (B : F') = ∑ i, algebraMap F F' (b i : F) * (s i : F') := by
    rw [hB]
    push_cast
    simp
  have hres : IsLocalRing.residue P'.integers B =
      ∑ i, IsLocalRing.residue _ (b i) • IsLocalRing.residue P'.integers (s i) := by
    rw [hB, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_residue]
  have hne : IsLocalRing.residue P'.integers B ≠ 0 := by
    rw [hres]
    intro h
    have hz := Fintype.linearIndependent_iff.mp hind _ h i₀
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    exact hz hb₀
  have hB0 : (B : F') ≠ 0 := fun h ↦ hne (by
    have hB_eq_zero : B = 0 := Subtype.ext h
    rw [hB_eq_zero, map_zero])
  have hunit : IsUnit B := by
    by_contra hu
    exact hne (by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hu)
  refine ⟨hcoe ▸ hB0, ?_⟩
  rw [← hcoe]
  exact (P'.isUnit_iff_ord_eq_zero hB0).mp hunit

/-- The order at `P'` of a nontrivial `F`-combination of elements of `𝒪_{P'}` with independent
residues is a multiple of the ramification index: dividing by the coefficient of least order
leaves a unit. -/
private theorem exists_ord_sum_eq_mul {ι : Type*} [Fintype ι] (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    (c : ι → F) {i₁ : ι} (hi₁ : c i₁ ≠ 0) :
    (∑ i, algebraMap F F' (c i) * (s i : F')) ≠ 0 ∧
      ∃ m : ℤ, P'.ord (∑ i, algebraMap F F' (c i) * (s i : F')) = ramificationIdx F P' * m := by
  classical
  set P := P'.restrict k F with hP
  set S : Finset ι := {i | c i ≠ 0} with hS
  have hSne : S.Nonempty := ⟨i₁, by simp [hS, hi₁]⟩
  obtain ⟨i₀, hi₀S, hi₀⟩ := S.exists_min_image (fun i ↦ P.ord (c i)) hSne
  have hd : c i₀ ≠ 0 := by simpa [hS] using hi₀S
  have hb : ∀ i, c i / c i₀ ∈ P.integers := by
    intro i
    rcases eq_or_ne (c i) 0 with h | h
    · simp [h]
    · rw [P.mem_integers_iff_ord_nonneg, P.ord_div h hd]
      have := hi₀ i (by simp [hS, h])
      omega
  set b : ι → P.integers := fun i ↦ ⟨c i / c i₀, hb i⟩ with hbdef
  have hb₀ : IsUnit (b i₀) := by
    have hb_eq_one : b i₀ = 1 := Subtype.ext (by simp [hbdef, div_self hd])
    rw [hb_eq_one]
    exact isUnit_one
  have hsum : ∑ i, algebraMap F F' (c i) * (s i : F') =
      algebraMap F F' (c i₀) * ∑ i, algebraMap F F' (b i : F) * (s i : F') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, ← map_mul]
    congr 2
    have hbi : ((b i : F)) = c i / c i₀ := rfl
    rw [hbi]
    field_simp
  obtain ⟨hne, hord⟩ := ord_sum_eq_zero k F P' s hind b hb₀
  have hd' : algebraMap F F' (c i₀) ≠ 0 := by simpa using hd
  refine ⟨by rw [hsum]; exact mul_ne_zero hd' hne, ⟨P.ord (c i₀), ?_⟩⟩
  rw [hsum, P'.ord_mul hd' hne, hord, add_zero, ord_algebraMap_restrict k F P' (c i₀)]

/-- A combination of elements of `𝒪_{P'}` with independent residues and coefficients in `𝒪_P`,
one of them a unit, has order zero at `P'` — that is, it is again a unit there. -/
theorem ord_sum_eq_zero_of_isUnit {ι : Type*} [Fintype ι] (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    (b : ι → (P'.restrict k F).integers) {i₀ : ι} (hb₀ : IsUnit (b i₀)) :
    P'.ord (∑ i, algebraMap F F' (b i : F) * (s i : F')) = 0 :=
  (ord_sum_eq_zero k F P' s hind b hb₀).2

/-- A nontrivial `F`-combination of elements of `𝒪_{P'}` whose residues are independent over the
residue field of the place below is nonzero. -/
theorem sum_ne_zero_of_linearIndependent_residue {ι : Type*} [Fintype ι] (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    (c : ι → F) {i₁ : ι} (hi₁ : c i₁ ≠ 0) :
    (∑ i, algebraMap F F' (c i) * (s i : F')) ≠ 0 :=
  (exists_ord_sum_eq_mul k F P' s hind c hi₁).1

/-- The order at `P'` of an `F`-combination of elements of `𝒪_{P'}` whose residues are independent
over the residue field of the place below is divisible by the ramification index, because such a
combination is a scalar in `F` times a unit at `P'`. -/
theorem ramificationIdx_dvd_ord_sum_of_linearIndependent_residue {ι : Type*} [Fintype ι]
    (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    (c : ι → F) :
    (ramificationIdx F P' : ℤ) ∣ P'.ord (∑ i, algebraMap F F' (c i) * (s i : F')) := by
  classical
  by_cases hc : ∀ i, c i = 0
  · simp [hc]
  · obtain ⟨i₁, hi₁⟩ := not_forall.mp hc
    exact (exists_ord_sum_eq_mul k F P' s hind c hi₁).2

/-- **The independence statement behind the fundamental inequality** (Stichtenoth,
Theorem 3.1.11): if the residues at `P'` of finitely many elements of `𝒪_{P'}` are independent
over the residue field of the place `P` below, and `t` is a prime element for `P'`, then the
products of those elements with `t ^ j` for `0 ≤ j < e(P' ∣ P)` are independent over `F`. The
reason is that the order at `P'` of an `F`-combination of the given elements is a multiple of
`e(P' ∣ P)`, so the `e(P' ∣ P)` blocks have pairwise distinct orders. -/
theorem linearIndependent_mul_pow_of_linearIndependent_residue {ι : Type*} [Finite ι]
    (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    {t : F'} (ht : P'.ord t = 1) :
    LinearIndependent F fun p : ι × Fin (ramificationIdx F P') ↦ (s p.1 : F') * t ^ (p.2 : ℕ) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  set e := ramificationIdx F P' with he
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hex
  rw [not_forall] at hex
  obtain ⟨⟨i₁, j₁⟩, hp₁⟩ := hex
  set A : Fin e → F' := fun j ↦ ∑ i, algebraMap F F' (c (i, j)) * (s i : F') with hA
  have hkey : ∑ j : Fin e, A j * t ^ (j : ℕ) = 0 := by
    rw [Fintype.sum_prod_type] at hc
    have hstep : ∀ j : Fin e, A j * t ^ (j : ℕ) = ∑ i, c (i, j) • ((s i : F') * t ^ (j : ℕ)) := by
      intro j
      rw [hA, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def, mul_assoc]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    simpa using hc
  have hAord : ∀ j : Fin e, A j ≠ 0 → ∃ m : ℤ, P'.ord (A j) = (e : ℤ) * m := by
    intro j hj
    by_cases hall : ∀ i, c (i, j) = 0
    · exact absurd (by simp [hA, hall]) hj
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      exact (exists_ord_sum_eq_mul k F P' s hind (fun i ↦ c (i, j)) hi).2
  have hTord : ∀ j : Fin e, A j * t ^ (j : ℕ) ≠ 0 →
      ∃ m : ℤ, P'.ord (A j * t ^ (j : ℕ)) = (e : ℤ) * m + (j : ℕ) := by
    intro j hj
    have hAj : A j ≠ 0 := fun h ↦ hj (by simp [h])
    obtain ⟨m, hm⟩ := hAord j hAj
    exact ⟨m, by rw [P'.ord_mul hAj (pow_ne_zero _ ht0), P'.ord_pow, ht, hm, mul_one]⟩
  have hA₁ : A j₁ ≠ 0 :=
    (exists_ord_sum_eq_mul k F P' s hind (fun i ↦ c (i, j₁)) (i₁ := i₁) hp₁).1
  exact (sum_ne_zero_of_ord_eq_mul_add_natCast P' (fun j ↦ A j * t ^ (j : ℕ)) hTord
    (mul_ne_zero hA₁ (pow_ne_zero _ ht0))) hkey

end Independence

section RamificationIdxBound

variable (F) (P' : Place k' F')

private theorem linearIndependent_pow_fin_ramificationIdx {t : F'} (ht : P'.ord t = 1) :
    LinearIndependent F fun j : Fin (ramificationIdx F P') ↦ t ^ (j : ℕ) := by
  classical
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  set e := ramificationIdx F P' with he
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hex
  rw [not_forall] at hex
  obtain ⟨j₁, hj₁⟩ := hex
  set A : Fin e → F' := fun j ↦ algebraMap F F' (c j) * t ^ (j : ℕ) with hA
  have hsum : ∑ j, A j = 0 := by
    simpa only [hA, Algebra.smul_def] using hc
  have hAord : ∀ j : Fin e, A j ≠ 0 →
      ∃ m : ℤ, P'.ord (A j) = (e : ℤ) * m + (j : ℕ) := by
    intro j hj
    have hjc : c j ≠ 0 := fun h ↦ hj (by simp [hA, h])
    obtain ⟨m, hm⟩ := Valuation.ordIndex_dvd_ord
      (P'.valuation.comap (algebraMap F F')) (c j)
    have hmap : algebraMap F F' (c j) ≠ 0 := by simpa using hjc
    refine ⟨m, ?_⟩
    rw [hA, P'.ord_mul hmap (pow_ne_zero _ ht0), P'.ord_pow, ht, mul_one,
      ← ord_comap F P' (c j), hm]
    have hidx : Valuation.ordIndex (P'.valuation.comap (algebraMap F F')) = e :=
      rfl.trans he.symm
    have hidx' : (Valuation.ordIndex (P'.valuation.comap (algebraMap F F')) : ℤ) = e := by
      exact_mod_cast hidx
    rw [hidx']
  have hA₁ : A j₁ ≠ 0 := by simp [hA, hj₁, ht0]
  exact (sum_ne_zero_of_ord_eq_mul_add_natCast P' A hAord hA₁) hsum

variable [FiniteDimensional F F']

/-- The ramification index of a place is at most the degree of the field extension. -/
theorem ramificationIdx_le_finrank : ramificationIdx F P' ≤ Module.finrank F F' := by
  obtain ⟨t, ht⟩ := P'.exists_isUniformizer
  rw [P'.isUniformizer_iff_ord_eq_one] at ht
  simpa using (linearIndependent_pow_fin_ramificationIdx F P' ht).fintype_card_le_finrank

end RamificationIdxBound

section Bound

variable (k F) (P' : Place k' F') [FiniteDimensional F F']

private theorem rank_residueField_le :
    Module.rank (P'.restrict k F).ResidueField P'.ResidueField ≤
      (Module.finrank F F' / ramificationIdx F P' : ℕ) := by
  classical
  obtain ⟨t, ht⟩ := P'.exists_isUniformizer
  rw [P'.isUniformizer_iff_ord_eq_one] at ht
  refine rank_le fun S hS ↦ ?_
  choose y hy using fun x : S ↦
    IsLocalRing.residue_surjective (R := P'.integers) (x : P'.ResidueField)
  have hind : LinearIndependent (P'.restrict k F).ResidueField
      fun x : S ↦ IsLocalRing.residue P'.integers (y x) := by
    simpa only [hy] using hS
  have hcard := (linearIndependent_mul_pow_of_linearIndependent_residue k F P' y hind
    ht).fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hcard
  exact (Nat.le_div_iff_mul_le (ramificationIdx_pos F P')).mpr hcard

/-- The residue field of a place is finite over the residue field of the place below it. -/
instance finiteDimensional_residueField_restrict :
    FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField :=
  Module.rank_lt_aleph0_iff.mp
    (lt_of_le_of_lt (rank_residueField_le k F P') (Cardinal.natCast_lt_aleph0))

/-- The relative degree is positive because a residue field extension is nontrivial. -/
theorem one_le_relativeDegree : 1 ≤ relativeDegree k F P' :=
  Module.finrank_pos

/-- **The fundamental inequality at a single place** (Stichtenoth, Theorem 3.1.11 and
Corollary 3.1.12): the ramification index times the relative degree of a place `P'` of `F' / k'`
over the place of `F / k` it lies over is at most the degree of the extension. -/
theorem ramificationIdx_mul_relativeDegree_le_finrank :
    ramificationIdx F P' * relativeDegree k F P' ≤ Module.finrank F F' := by
  calc ramificationIdx F P' * relativeDegree k F P'
      ≤ ramificationIdx F P' * (Module.finrank F F' / ramificationIdx F P') :=
        Nat.mul_le_mul_left _ (Module.finrank_le_of_rank_le (rank_residueField_le k F P'))
    _ ≤ Module.finrank F F' := by
        rw [mul_comm]
        exact Nat.div_mul_le_self _ _

/-- The relative degree of a place is at most the degree of the field extension. -/
theorem relativeDegree_le_finrank : relativeDegree k F P' ≤ Module.finrank F F' :=
  le_trans (Nat.le_mul_of_pos_left _ (ramificationIdx_pos F P'))
    (ramificationIdx_mul_relativeDegree_le_finrank k F P')

end Bound

end Place

end TauCeti
