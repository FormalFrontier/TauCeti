/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import TauCeti.FieldTheory.FunctionField.Place.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence

/-!
# Kummer's theorem: places over a place, from a factorization modulo that place

Let `P` be a place of an algebraic function field `F / k`, let `F' / k'` be a finite extension of
`F / k`, and let `y : F'` be integral over the valuation ring `𝒪_P`, say `φ (y) = 0` for a monic
`φ ∈ 𝒪_P[X]` whose image in `F[X]` is the minimal polynomial of `y`.  Reducing `φ` modulo the
maximal ideal of `𝒪_P` gives a polynomial over the residue field `F_P`, and **each monic
irreducible factor `γ` of that reduction produces a place `P'` of `F' / k'` over `P`** at which
`γ (y)` vanishes and whose relative degree is at least `deg γ`; distinct factors produce distinct
places.  This is the unconditional half of Kummer's theorem, Stichtenoth, *Algebraic Function
Fields and Codes*, 2nd ed., Theorem 3.3.7.

The construction is direct.  A monic lift `g ∈ 𝒪_P[X]` of `γ` spans, together with the maximal
ideal of `𝒪_P`, an ideal of `𝒪_P[y]` whose quotient is `F_P[X] / (γ)`, a field; the ideal is
therefore proper, and it is nonzero because it contains a uniformizer of `P`.  Stichtenoth's
existence theorem for places dominates it by a place `P'` of `F'`.  The valuation ring of `P'`
then contains `𝒪_P`, so `P'` lies over `P`; and `g (y)` lies in the maximal ideal of `P'`, so the
residue of `y` is a root of `γ` in `F'_{P'}`.  Since `γ` is irreducible it is the minimal
polynomial of that residue over `F_P`, which both bounds the relative degree below by `deg γ` and
shows that `γ` is recovered from `P'` — whence the distinctness of the places attached to distinct
factors.

⚠ Kummer's theorem in this unconditional form **bounds** the splitting of `P` in `F'` but does not
determine it: the ramification indices are not computed and there may be places over `P` that no
factor of the reduction produces.  The complementary statement, that the places produced are all
of them with `e (P' ∣ P) = ε` the multiplicity of `γ` in the reduction and `f (P' ∣ P) = deg γ`,
needs the monogenicity hypothesis `𝒪'_P = 𝒪_P[y]` (Stichtenoth, Corollary 3.3.8) and is not proved
here.

## Main definitions

* `TauCeti.Place.integersEval`: evaluation at `y : F'` of a polynomial over the valuation ring
  `𝒪_P` of a place `P` of `F / k`.

## Main results

* `TauCeti.Place.exists_monic_map_residue_eq`: monic polynomials over the residue field `F_P` lift
  to monic polynomials over `𝒪_P`.
* `TauCeti.Place.exists_restrict_eq_of_irreducible_map_residue`: **Kummer's theorem** for a single
  irreducible factor (Stichtenoth, Theorem 3.3.7).
* `TauCeti.Place.map_residue_eq_of_valuation_lt_one`: a place over `P` sees at most one
  irreducible factor, which is what makes the places of distinct factors distinct.
* `TauCeti.Place.exists_injective_restrict_eq`: **Kummer's theorem**, packaged: an injective
  family of places over `P`, indexed by a family of monic irreducible factors of the reduction of
  `φ`, whose relative degrees are at least the degrees of the factors.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.3.7.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-! ### Evaluating a polynomial integral at a place -/

section IntegersEval

variable (P : Place k F)

/-- Evaluation at `y : F'` of a polynomial whose coefficients are integral at the place `P` of
`F / k`, along the inclusions `𝒪_P ⊆ F ⊆ F'`. -/
noncomputable def integersEval (y : F') : P.integers[X] →+* F' :=
  eval₂RingHom ((algebraMap F F').comp (algebraMap P.integers F)) y

variable {P}

omit [Algebra k F'] [IsScalarTower k F F'] in
theorem integersEval_eq_aeval_map (y : F') (g : P.integers[X]) :
    P.integersEval y g = aeval y (g.map (algebraMap P.integers F)) := by
  rw [aeval_def, eval₂_map]
  rfl

omit [Algebra k F'] [IsScalarTower k F F'] in
@[simp]
theorem integersEval_C (y : F') (a : P.integers) :
    P.integersEval y (C a) = algebraMap F F' (a : F) := by
  rw [integersEval, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply,
    ValuationSubring.algebraMap_apply]

omit [Algebra k F'] [IsScalarTower k F F'] in
@[simp]
theorem integersEval_X (y : F') : P.integersEval y (X : P.integers[X]) = y := by
  rw [integersEval, coe_eval₂RingHom, eval₂_X]

theorem integersEval_algebraMap (y : F') (c : k) :
    P.integersEval y (C (algebraMap k P.integers c)) = algebraMap k F' c := by
  rw [integersEval_C, coe_algebraMap_constants, ← IsScalarTower.algebraMap_apply]

omit [Algebra k F'] [IsScalarTower k F F'] in
/-- A polynomial over `𝒪_P` vanishing at `y` is divisible by any monic `φ` over `𝒪_P` whose image
in `F[X]` is the minimal polynomial of `y`: division by a monic polynomial does not leave
`𝒪_P[X]`, so divisibility may be tested over `F`. -/
theorem dvd_of_integersEval_eq_zero {y : F'} {φ : P.integers[X]} (hφ : φ.Monic)
    (hmin : φ.map (algebraMap P.integers F) = minpoly F y) {q : P.integers[X]}
    (hq : P.integersEval y q = 0) : φ ∣ q := by
  refine (Polynomial.map_dvd_map (algebraMap P.integers F)
    (IsFractionRing.injective P.integers F) hφ).mp ?_
  rw [hmin]
  exact minpoly.dvd F y (by rw [← integersEval_eq_aeval_map, hq])

end IntegersEval

/-! ### Integrality of `y` at a place over `P` -/

section Integral

variable [FiniteDimensional F F']

omit [Algebra k F'] [IsScalarTower k k' F'] in
/-- A polynomial over `𝒪_P` whose image in `F[X]` is the minimal polynomial of `y : F'` is monic,
because `𝒪_P → F` is injective. -/
private theorem monic_of_map_eq_minpoly {P : Place k F} {y : F'} {φ : P.integers[X]}
    (hmin : φ.map (algebraMap P.integers F) = minpoly F y) : φ.Monic :=
  Polynomial.monic_of_injective (IsFractionRing.injective P.integers F)
    (hmin ▸ minpoly.monic (IsIntegral.of_finite F y))

/-- A root `y : F'` of a polynomial over `𝒪_P` whose image in `F[X]` is the minimal polynomial of
`y` is integral at every place of `F' / k'` lying over `P`: that polynomial is monic, the
valuation ring of such a place contains `𝒪_P`, and valuation rings are integrally closed. -/
private theorem mem_integers_of_map_eq_minpoly {P : Place k F} {P' : Place k' F'}
    (hres : P'.restrict k F = P) {y : F'} {φ : P.integers[X]}
    (hmin : φ.map (algebraMap P.integers F) = minpoly F y) : y ∈ P'.integers := by
  let _ : Algebra P.integers F' := ((algebraMap F F').comp (algebraMap P.integers F)).toAlgebra
  refine P'.mem_integers_of_isIntegral (fun r ↦ ?_) ⟨φ, monic_of_map_eq_minpoly hmin, ?_⟩
  · rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ValuationSubring.algebraMap_apply]
    exact (restrict_eq_iff_integers_le k F P' P).mp hres _ r.2
  · rw [RingHom.algebraMap_toAlgebra, ← coe_eval₂RingHom, ← integersEval,
      integersEval_eq_aeval_map, hmin]
    exact minpoly.aeval F y

end Integral

/-! ### The residue of `y` at a place over `P` -/

section Residue

variable (k F) [FiniteDimensional F F']

/-- **Kummer's theorem at a single place, in residue-field form**: if `g` is monic over `𝒪_P` with
irreducible reduction `γ` over the residue field `F_P`, and `g (y)` vanishes at a place `P'` of
`F' / k'` over `P` at which `y` is integral, then `γ` is the minimal polynomial over `F_P` of the
residue of `y` at `P'`. -/
private theorem minpoly_residue_eq (P' : Place k' F') {y : F'} (hy : y ∈ P'.integers)
    {g : (P'.restrict k F).integers[X]} (hg : g.Monic)
    (hirr : Irreducible (g.map (IsLocalRing.residue (P'.restrict k F).integers)))
    (hv : P'.valuation ((P'.restrict k F).integersEval y g) < 1) :
    minpoly (P'.restrict k F).ResidueField (IsLocalRing.residue P'.integers ⟨y, hy⟩) =
      g.map (IsLocalRing.residue (P'.restrict k F).integers) := by
  -- Evaluating `g` at `y` inside `𝒪_{P'}` and then including into `F'` is `integersEval`.
  have hcomp : (algebraMap P'.integers F').comp
      (algebraMap (P'.restrict k F).integers P'.integers) =
      (algebraMap F F').comp (algebraMap (P'.restrict k F).integers F) :=
    RingHom.ext fun a ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, ValuationSubring.algebraMap_apply,
        coe_algebraMap_integers, ValuationSubring.algebraMap_apply]
  have hcoe : algebraMap P'.integers F' (eval₂
      (algebraMap (P'.restrict k F).integers P'.integers) (⟨y, hy⟩ : P'.integers) g) =
      (P'.restrict k F).integersEval y g := by
    rw [hom_eval₂, hcomp, integersEval, coe_eval₂RingHom, ValuationSubring.algebraMap_apply]
  -- Hence its residue at `P'` vanishes, and that residue is `γ` evaluated at the residue of `y`.
  have hzero : IsLocalRing.residue P'.integers (eval₂
      (algebraMap (P'.restrict k F).integers P'.integers) (⟨y, hy⟩ : P'.integers) g) = 0 := by
    rw [P'.residue_eq_zero_iff_valuation_lt_one, ← ValuationSubring.algebraMap_apply, hcoe]
    exact hv
  have hres : (IsLocalRing.residue P'.integers).comp
      (algebraMap (P'.restrict k F).integers P'.integers) =
      (algebraMap (P'.restrict k F).ResidueField P'.ResidueField).comp
        (IsLocalRing.residue (P'.restrict k F).integers) :=
    RingHom.ext fun a ↦ (IsLocalRing.ResidueField.algebraMap_residue a).symm
  have hroot : aeval (IsLocalRing.residue P'.integers (⟨y, hy⟩ : P'.integers))
      (g.map (IsLocalRing.residue (P'.restrict k F).integers)) = 0 := by
    rw [aeval_def, eval₂_map, ← hres, ← hom_eval₂, hzero]
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot (hg.map _)).symm

variable {k F}

/-- **Kummer's theorem sees one factor per place**: a place `P'` over `P` at which two monic
polynomials with irreducible reductions both vanish reduces them to the same irreducible
polynomial, namely the minimal polynomial of the residue of `y`.  This is what makes the places
attached to distinct irreducible factors of the reduction of `φ` distinct (Stichtenoth,
Theorem 3.3.7). -/
theorem map_residue_eq_of_valuation_lt_one {P : Place k F} {P' : Place k' F'}
    (hres : P'.restrict k F = P) {y : F'} (hy : y ∈ P'.integers) {g₁ g₂ : P.integers[X]}
    (hg₁ : g₁.Monic) (hirr₁ : Irreducible (g₁.map (IsLocalRing.residue P.integers)))
    (hv₁ : P'.valuation (P.integersEval y g₁) < 1)
    (hg₂ : g₂.Monic) (hirr₂ : Irreducible (g₂.map (IsLocalRing.residue P.integers)))
    (hv₂ : P'.valuation (P.integersEval y g₂) < 1) :
    g₁.map (IsLocalRing.residue P.integers) = g₂.map (IsLocalRing.residue P.integers) := by
  subst hres
  rw [← minpoly_residue_eq k F P' hy hg₁ hirr₁ hv₁, minpoly_residue_eq k F P' hy hg₂ hirr₂ hv₂]

/-- **The relative degree bound of Kummer's theorem** (Stichtenoth, Theorem 3.3.7): a place `P'`
over `P` at which a monic `g` with irreducible reduction `γ` vanishes has relative degree at
least `deg γ`, because `γ` is the minimal polynomial of the residue of `y` at `P'`. -/
theorem natDegree_map_residue_le_relativeDegree {P : Place k F} {P' : Place k' F'}
    (hres : P'.restrict k F = P) {y : F'} (hy : y ∈ P'.integers) {g : P.integers[X]}
    (hg : g.Monic) (hirr : Irreducible (g.map (IsLocalRing.residue P.integers)))
    (hv : P'.valuation (P.integersEval y g) < 1) :
    (g.map (IsLocalRing.residue P.integers)).natDegree ≤ relativeDegree k F P' := by
  subst hres
  have hmin := minpoly_residue_eq k F P' hy hg hirr hv
  have hint : IsIntegral (P'.restrict k F).ResidueField
      (IsLocalRing.residue P'.integers (⟨y, hy⟩ : P'.integers)) :=
    ⟨_, hg.map _, by rw [← hmin]; exact minpoly.aeval _ _⟩
  rw [relativeDegree_def, ← hmin]
  exact Nat.le_of_dvd Module.finrank_pos (minpoly.degree_dvd hint)

end Residue

/-! ### Kummer's theorem -/

section Kummer

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']

/-- Every monic polynomial over the residue field `F_P` lifts to a monic polynomial over the
valuation ring `𝒪_P`. -/
theorem exists_monic_map_residue_eq (P : Place k F) {γ : P.ResidueField[X]} (hγ : γ.Monic) :
    ∃ g : P.integers[X], g.Monic ∧ g.map (IsLocalRing.residue P.integers) = γ := by
  obtain ⟨g, hmap, -, hmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts γ).mpr fun n ↦ IsLocalRing.residue_surjective (γ.coeff n)) hγ
  exact ⟨g, hmonic, hmap⟩

/-- **Kummer's theorem** (Stichtenoth, Theorem 3.3.7), for one irreducible factor.  Let `P` be a
place of `F / k`, let `y : F'` be a root of a monic `φ ∈ 𝒪_P[X]` whose image in `F[X]` is the
minimal polynomial of `y`, and let `g ∈ 𝒪_P[X]` be monic with irreducible reduction dividing the
reduction of `φ`.  Then some place `P'` of `F' / k'` lies over `P`, has `g (y)` in its maximal
ideal, and has relative degree at least the degree of the reduction of `g`.

The theorem bounds the splitting of `P` without determining it: nothing here says that every
place over `P` arises this way, and the ramification indices are not computed. -/
theorem exists_restrict_eq_of_irreducible_map_residue (hF : IsFunctionField k F) (P : Place k F)
    (y : F') {φ g : P.integers[X]}
    (hmin : φ.map (algebraMap P.integers F) = minpoly F y) (hg : g.Monic)
    (hirr : Irreducible (g.map (IsLocalRing.residue P.integers)))
    (hdvd : g.map (IsLocalRing.residue P.integers) ∣ φ.map (IsLocalRing.residue P.integers)) :
    ∃ P' : Place k' F', P'.restrict k F = P ∧ P'.valuation (P.integersEval y g) < 1 ∧
      (g.map (IsLocalRing.residue P.integers)).natDegree ≤ relativeDegree k F P' := by
  classical
  have hφ : φ.Monic := monic_of_map_eq_minpoly (F' := F') hmin
  set res := IsLocalRing.residue P.integers with hresdef
  set γ := g.map res with hγdef
  set ev := P.integersEval (F' := F') y with hevdef
  -- The reduction map to the field `F_P[X] / (γ)`; its kernel `K` contains `φ` and `g`.
  have hspan : Ideal.span {γ} ≠ ⊤ := fun h ↦ hirr.not_isUnit (Ideal.span_singleton_eq_top.mp h)
  have : Nontrivial (P.ResidueField[X] ⧸ Ideal.span {γ}) :=
    Ideal.Quotient.nontrivial_iff.mpr hspan
  set ψ : P.integers[X] →+* (P.ResidueField[X] ⧸ Ideal.span {γ}) :=
    (Ideal.Quotient.mk (Ideal.span {γ})).comp (mapRingHom res) with hψdef
  set K := RingHom.ker ψ with hKdef
  have hmemK : ∀ q : P.integers[X], q ∈ K ↔ γ ∣ q.map res := fun q ↦ by
    rw [hKdef, RingHom.mem_ker, hψdef, RingHom.comp_apply, coe_mapRingHom,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hKtop : K ≠ ⊤ := fun h ↦ by
    have h1 : ψ 1 = 0 := RingHom.mem_ker.mp ((Ideal.eq_top_iff_one K).mp h)
    exact one_ne_zero (α := P.ResidueField[X] ⧸ Ideal.span {γ}) (by rwa [map_one] at h1)
  -- The ideal of `𝒪_P[y]` it induces is proper, because the kernel of the evaluation map is
  -- generated by `φ`, which lies in `K`.
  have hkerle : RingHom.ker ev ≤ K := fun q hq ↦
    (hmemK q).mpr (hdvd.trans (Polynomial.map_dvd res
      (dvd_of_integersEval_eq_zero hφ hmin (RingHom.mem_ker.mp hq))))
  set J : Ideal ev.range := K.map ev.rangeRestrict with hJdef
  have hJtop : J ≠ ⊤ := fun h ↦ by
    have hcomap : Ideal.comap ev.rangeRestrict J = ⊤ := by rw [h, Ideal.comap_top]
    rw [hJdef, Ideal.comap_map_of_surjective _ ev.rangeRestrict_surjective,
      ← RingHom.ker_eq_comap_bot, ev.ker_rangeRestrict, sup_eq_left.mpr hkerle] at hcomap
    exact hKtop hcomap
  -- A uniformizer of `P` gives a nonzero element of that ideal.
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [P.isUniformizer_iff_ord_eq_one] at ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have htcoe : ((⟨t, htmem⟩ : P.integers) : F) = t := (rfl)
  have htK : C (⟨t, htmem⟩ : P.integers) ∈ K := by
    rw [hmemK, Polynomial.map_C, (P.residue_eq_zero_iff_ord_pos (by rw [htcoe]; exact ht0)).mpr
      (by rw [htcoe]; omega), map_zero]
    exact dvd_zero _
  have hJbot : J ≠ ⊥ := fun h ↦ by
    have hmem : ev.rangeRestrict (C (⟨t, htmem⟩ : P.integers)) ∈ J := Ideal.mem_map_of_mem _ htK
    rw [h, Ideal.mem_bot] at hmem
    have : ev (C (⟨t, htmem⟩ : P.integers)) = 0 := congrArg Subtype.val hmem
    rw [hevdef, integersEval_C] at this
    exact ht0 ((algebraMap F F').injective (by rwa [map_zero]))
  -- Stichtenoth's existence theorem dominates it by a place of `F'`.
  have hkA : ∀ c : k, algebraMap k F' c ∈ ev.range :=
    fun c ↦ ⟨C (algebraMap k P.integers c), integersEval_algebraMap y c⟩
  obtain ⟨Q, hQint, hQval⟩ := Place.exists_forall_mem_integers_and_valuation_lt_one
    (hF.finite_extension (E := F')) hkA hJtop hJbot
  set P' := constantsEquiv k k' F' Q with hP'def
  have hrestrict : P'.restrict k F = P := by
    refine (restrict_eq_iff_integers_le k F P' P).mpr fun f hf ↦ ?_
    rw [hP'def, integers_constantsEquiv]
    exact hQint ⟨algebraMap F F' f, C (⟨f, hf⟩ : P.integers), by rw [hevdef, integersEval_C]⟩
  have hvg : P'.valuation (P.integersEval y g) < 1 := by
    have hgK : g ∈ K := (hmemK g).mpr dvd_rfl
    simpa [hP'def, hevdef] using hQval _ (Ideal.mem_map_of_mem ev.rangeRestrict hgK)
  -- `y` is integral over `𝒪_P`, hence lies in the valuation ring of `P'`.
  exact ⟨P', hrestrict, hvg, natDegree_map_residue_le_relativeDegree hrestrict
    (mem_integers_of_map_eq_minpoly hrestrict hmin) hg hirr hvg⟩

/-- **Kummer's theorem** (Stichtenoth, Theorem 3.3.7), packaged.  Let `P` be a place of `F / k`
and let `y : F'` be a root of a monic `φ ∈ 𝒪_P[X]` whose image in `F[X]` is the minimal
polynomial of `y`.  To a family of pairwise distinct monic irreducible factors `γ i` of the
reduction of `φ` modulo `P` there is an injective family of places of `F' / k'` over `P`, the
place attached to `γ i` having relative degree at least `deg (γ i)`.

The factorization of the reduction of `φ` therefore bounds the splitting of `P` in `F' / F` from
below; determining it needs the monogenicity hypothesis of Stichtenoth's Corollary 3.3.8. -/
theorem exists_injective_restrict_eq (hF : IsFunctionField k F) (P : Place k F) (y : F')
    {φ : P.integers[X]} (hmin : φ.map (algebraMap P.integers F) = minpoly F y)
    {ι : Type*} {γ : ι → P.ResidueField[X]} (hmonic : ∀ i, (γ i).Monic)
    (hirr : ∀ i, Irreducible (γ i))
    (hdvd : ∀ i, γ i ∣ φ.map (IsLocalRing.residue P.integers)) (hinj : Function.Injective γ) :
    ∃ Q : ι → Place k' F', Function.Injective Q ∧
      ∀ i, (Q i).restrict k F = P ∧ (γ i).natDegree ≤ relativeDegree k F (Q i) := by
  choose g hgm hgmap using fun i ↦ P.exists_monic_map_residue_eq (hmonic i)
  choose Q hQres hQval hQdeg using fun i ↦ exists_restrict_eq_of_irreducible_map_residue
    (k' := k') hF P y hmin (hgm i) (hgmap i ▸ hirr i) (hgmap i ▸ hdvd i)
  -- `y` is integral over `𝒪_P`, so it has a residue at each of these places.
  have hyint : ∀ i, y ∈ (Q i).integers := fun i ↦
    mem_integers_of_map_eq_minpoly (hQres i) hmin
  refine ⟨Q, fun i j hij ↦ hinj ?_, fun i ↦ ⟨hQres i, hgmap i ▸ hQdeg i⟩⟩
  rw [← hgmap i, ← hgmap j]
  refine map_residue_eq_of_valuation_lt_one (hQres i) (hyint i) (hgm i) (hgmap i ▸ hirr i)
    (hQval i) (hgm j) (hgmap j ▸ hirr j) ?_
  rw [hij]
  exact hQval j

end Kummer

end Place

end TauCeti
