/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.ValenceFormula
public import TauCeti.NumberTheory.ModularForms.Order.SubgroupOrbits

/-!
# The valence formula at general level, transported along the norm map

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the norm `ModularForm.norm 𝒮ℒ f = ∏_{γ ∈ Γ \\ SL(2, ℤ)}
f ∣[k] γ` of a weight-`k` form on `Γ` is a level-one form of weight `k · [SL(2, ℤ) : Γ]`, and its
divisor is the `Γ`-divisor of `f` pushed forward. This file carries out that push-forward on the
**interior** of the upper half-plane and reads the level-one valence formula back as the
general-level one:

`Σ_{P ∈ Γ \ ℍ} (2 / |Stab_Γ P|) · ord_P f + ord_∞(Nm f) = k · [SL(2, ℤ) : Γ] / 12`.

The bookkeeping is the orbit–stabiliser count already available in
`TauCeti.card_fiber_orbitOfCosetTranslate_mul_cardStabilizerOnOrbit`: the cosets of `Γ` that
translate a point `p` into a given `Γ`-orbit `P` number `|Stab_{SL(2, ℤ)} p| / |Stab_Γ P|`, and
`|Stab_{SL(2, ℤ)} p| = 2 · e_p` is twice the level-one elliptic order. Dividing the count by `e_p`
therefore turns the level-one weight `1 / e_p` into the general-level weight `2 / |Stab_Γ P|`,
uniformly in `P`, with no case split on the elliptic points.

The index is the **full** coset index `[SL(2, ℤ) : Γ]`, not the projective one, and correspondingly
the weight is read on the matrix stabiliser rather than on the projective order `e_P`. That is the
only choice under which both sides are correct in odd weight with `-I ∉ Γ`, where the projective
norm is not even well defined; the projective statement
`Σ_P (1 / e_P) · ord_P f = k · [SL(2, ℤ) : ±Γ] / 12` is this one divided by
`|{±I} ∩ Γ|` on both sides. See `TauCeti.ModularForm.weightedOrderOfVanishingOnSubgroupOrbit`.

## Main declarations

* `TauCeti.ModularForm.slOrbitOfSubgroupOrbit`: the `SL(2, ℤ)`-orbit containing a `Γ`-orbit, with
  `TauCeti.ModularForm.finite_preimage_slOrbitOfSubgroupOrbit` — an `SL(2, ℤ)`-orbit contains only
  finitely many `Γ`-orbits.
* `TauCeti.ModularForm.weightedOrderOfVanishingOnSubgroupOrbit`: the general-level weighted
  vanishing order `2 · ord_P f / |Stab_Γ P|`, with
  `TauCeti.ModularForm.weightedOrderOfVanishingOnOrbit_eq_two_mul_div` identifying the level-one
  weight `ord_P f / e_P` as the same expression.
* `TauCeti.ModularForm.weightedOrderOfVanishingOnOrbit_norm_eq_finsum_mem`: the local
  redistribution — the level-one weight of the norm at one `SL(2, ℤ)`-orbit is the sum of the
  general-level weights of `f` over the `Γ`-orbits inside it.
* `TauCeti.ModularForm.finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_finsum_norm`: the global
  form of the same statement, the two divisor sums being equal.
* `TauCeti.ModularForm.valence_formula_finiteIndex`: **the general-level valence formula**, with
  the cusp term still read at level one on the norm.
* `TauCeti.ModularForm.twentyFour_mul_orderOfVanishingOnSubgroupOrbit_le` and
  `TauCeti.ModularForm.orderOfVanishingOnSubgroupOrbit_eq_zero_of_lt_twentyFour`: the single-orbit
  consequences, bounding the mass at one orbit by the total.

## Implementation notes

What remains for the full general-level formula of the ModularForms roadmap's Layer 1 is the
**cusp** half: distributing `ord_∞(Nm f)` over the cusps of `Γ`, each read in its width parameter.
The decomposition of the norm at `∞` that the distribution runs through is
`TauCeti.ModularForm.qExpansion_one_norm_order_eq` in `Norm/Trace.lean`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §3.
* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the norm-map route to
  general level, used there for the finite-index Sturm bound (`dim_gen_cong_levels`); the
  redistribution of the *exact* level-one identity carried out here is new.
-/

public section

open UpperHalfPlane MulAction

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup SL(2, ℤ)}

/-- The `SL(2, ℤ)`-orbit containing a `Γ`-orbit. -/
noncomputable def slOrbitOfSubgroupOrbit
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    orbitRel.Quotient SL(2, ℤ) ℍ :=
  Quotient.liftOn' o (fun p ↦ Quotient.mk'' p) fun a b ⟨g, hg⟩ ↦ by
    obtain ⟨γ, -, hγ⟩ := g.2
    refine Quotient.sound' ⟨γ, ?_⟩
    have hb : (g : GL (Fin 2) ℝ) • b = a := hg
    simpa only [MulAction.compHom_smul_def, hγ] using hb

@[simp]
lemma slOrbitOfSubgroupOrbit_mk (p : ℍ) :
    slOrbitOfSubgroupOrbit (Quotient.mk'' p : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) =
      Quotient.mk'' p :=
  (rfl)

/-- Every coset translate of `p` stays in the `SL(2, ℤ)`-orbit of `p`. -/
@[simp]
lemma slOrbitOfSubgroupOrbit_orbitOfCosetTranslate (p : ℍ)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    slOrbitOfSubgroupOrbit (orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) p q) =
      Quotient.mk'' p := by
  induction q using QuotientGroup.induction_on with
  | H h =>
    obtain ⟨γ, hγ⟩ := h.2
    have hq : orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) p
        (h : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
        Quotient.mk'' ((h : GL (Fin 2) ℝ)⁻¹ • p) := by
      simp
    rw [hq, slOrbitOfSubgroupOrbit_mk]
    refine Quotient.sound' ⟨γ⁻¹, ?_⟩
    simp [MulAction.compHom_smul_def, ← hγ]

/-- Conversely, every `Γ`-orbit inside the `SL(2, ℤ)`-orbit of `p` is a coset translate of `p`. -/
lemma exists_orbitOfCosetTranslate_eq
    {o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ} {p : ℍ}
    (ho : slOrbitOfSubgroupOrbit o = Quotient.mk'' p) :
    ∃ q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
      orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) p q = o := by
  induction o using Quotient.inductionOn' with
  | h z =>
    rw [slOrbitOfSubgroupOrbit_mk, Quotient.eq''] at ho
    obtain ⟨γ, hγ⟩ := ho
    have hγ' : γ • p = z := hγ
    -- the translating coset is the class of `γ⁻¹`, read inside `𝒮ℒ`
    set σ : 𝒮ℒ := ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹, ⟨γ⁻¹, rfl⟩⟩ with hσ
    refine ⟨(σ : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ), ?_⟩
    -- `QuotientGroup`'s `↑σ` is `⟦σ⟧`, which `orbitOfCosetTranslate_mk` needs `simp` to see
    have hval : orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) p
        (σ : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
        Quotient.mk'' ((σ : GL (Fin 2) ℝ)⁻¹ • p) := by
      simp
    rw [hval]
    congr 1
    rw [← hγ', MulAction.compHom_smul_def, hσ]
    simp

/-- The stabiliser of a point in `𝒮ℒ` has the order the level-one elliptic bookkeeping records:
twice the elliptic order of its orbit, the extra factor being `±I`. -/
lemma card_stabilizer_slGL_eq_two_mul_ellipticOrder (p : ℍ) :
    Nat.card (stabilizer 𝒮ℒ p) =
      2 * ModularGroup.ellipticOrder (Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ) := by
  have hcompat : ∀ γ : SL(2, ℤ),
      ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) • p = γ • p := by
    intro γ
    rw [Subgroup.smul_def, MulAction.compHom_smul_def]
    rfl
  have hker := card_stabilizer_eq_card_ker_mul_card_stabilizer
    (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
    (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict_surjective p hcompat
  rw [MonoidHom.ker_rangeRestrict,
    (MonoidHom.ker_eq_bot_iff _).mpr Matrix.SpecialLinearGroup.mapGL_injective] at hker
  simpa [← ModularGroup.cardStabilizerOnOrbit_eq_two_mul_ellipticOrder] using hker.symm

/-- A `Γ`-orbit outside the `SL(2, ℤ)`-orbit of `p` is no coset translate of `p`. -/
lemma card_fiber_orbitOfCosetTranslate_eq_zero (p : ℍ)
    {o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ}
    (ho : slOrbitOfSubgroupOrbit o ≠ Quotient.mk'' p) :
    Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
      orbitOfCosetTranslate p q = o} = 0 := by
  have : IsEmpty {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
      orbitOfCosetTranslate p q = o} :=
    ⟨fun q ↦ ho (by rw [← q.2, slOrbitOfSubgroupOrbit_orbitOfCosetTranslate])⟩
  simp

/-- **The multiplicity of a `Γ`-orbit in the norm at `p`.** For a `Γ`-orbit inside the
`SL(2, ℤ)`-orbit of `p`, the number of cosets translating `p` into it, times the order of its
stabiliser in `Γ`, is the order of the stabiliser of `p` in `SL(2, ℤ)` — twice the elliptic
order of the level-one orbit. -/
lemma card_fiber_orbitOfCosetTranslate_mul_cardStabilizerOnOrbit_eq (p : ℍ)
    {o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ}
    (ho : slOrbitOfSubgroupOrbit o = Quotient.mk'' p) :
    Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
        orbitOfCosetTranslate p q = o} * cardStabilizerOnOrbit o =
      2 * ModularGroup.ellipticOrder (Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ) := by
  obtain ⟨q, rfl⟩ := exists_orbitOfCosetTranslate_eq ho
  rw [card_fiber_orbitOfCosetTranslate_mul_cardStabilizerOnOrbit
      (Subgroup.map_le_range _ _) p q, card_stabilizer_slGL_eq_two_mul_ellipticOrder]

/-- **The stabiliser weight is positive.** A point of `ℍ` has a finite, nonempty stabiliser in any
subgroup of `SL(2, ℤ)` — it sits inside the finite `SL(2, ℤ)`-stabiliser, whose order the
orbit-stabiliser identity divides — so the denominator of
`weightedOrderOfVanishingOnSubgroupOrbit` never vanishes. -/
lemma cardStabilizerOnOrbit_ne_zero (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    cardStabilizerOnOrbit o ≠ 0 := by
  induction o using Quotient.inductionOn' with
  | h z =>
    intro h0
    have hprod := card_fiber_orbitOfCosetTranslate_mul_cardStabilizerOnOrbit_eq (Γ := Γ) z
      (o := Quotient.mk'' z) (slOrbitOfSubgroupOrbit_mk z)
    rw [h0, Nat.mul_zero] at hprod
    have := ModularGroup.ellipticOrder_pos (Quotient.mk'' z : orbitRel.Quotient SL(2, ℤ) ℍ)
    omega

/-- A single `SL(2, ℤ)`-orbit contains only finitely many `Γ`-orbits: each is a coset translate
of any of its points, and the coset space is finite. -/
lemma finite_preimage_slOrbitOfSubgroupOrbit
    [(Γ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex 𝒮ℒ] (P : orbitRel.Quotient SL(2, ℤ) ℍ) :
    (slOrbitOfSubgroupOrbit (Γ := Γ) ⁻¹' {P}).Finite := by
  induction P using Quotient.inductionOn' with
  | h p =>
    refine (Set.finite_range
      (orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (ℋ := 𝒮ℒ) p)).subset fun o ho ↦ ?_
    exact exists_orbitOfCosetTranslate_eq (by simpa using ho)

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- **The weighted vanishing order of a form on a `Γ`-orbit**: `2 · ord_P f / |Stab_Γ P|`, the
summand of the valence formula at general level.

The weight is written through the **matrix** stabiliser order, not through the projective one:
`Nat.card (stabilizer Γ P) = Nat.card ((center SL(2, ℤ)).subgroupOf Γ) * e_P` by
`TauCeti.card_stabilizer_eq_card_subgroupOf_mul_card_stabilizer_map`, so the weight is `1 / e_P`
when `-I ∈ Γ` and `2 / e_P` when `-I ∉ Γ`. That is the right normalisation for the norm map,
whose weight is `k · [SL(2, ℤ) : Γ]` for the **full** coset index: both sides of the general-level
formula double when `-I ∉ Γ`, and dividing by `2` there recovers the projective statement
`∑_P (1 / e_P) · ord_P f = k · [SL(2, ℤ) : ±Γ] / 12`.

At level one this is the same weight: `weightedOrderOfVanishingOnOrbit_eq_two_mul_div` below. -/
noncomputable def weightedOrderOfVanishingOnSubgroupOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) : ℚ :=
  2 * (orderOfVanishingOnSubgroupOrbit f o : ℚ) / (cardStabilizerOnOrbit o : ℚ)

/-- The defining equation of `weightedOrderOfVanishingOnSubgroupOrbit`. -/
lemma weightedOrderOfVanishingOnSubgroupOrbit_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    weightedOrderOfVanishingOnSubgroupOrbit f o =
      2 * (orderOfVanishingOnSubgroupOrbit f o : ℚ) / (cardStabilizerOnOrbit o : ℚ) :=
  (rfl)

/-- **The level-one weight is the same weight.** `ord_P f / e_P` is `2 · ord_P f` divided by the
order of the matrix stabiliser, because `-I` lies in `SL(2, ℤ)` and fixes every point. This is
what makes `weightedOrderOfVanishingOnSubgroupOrbit` the general-level form of
`weightedOrderOfVanishingOnOrbit` rather than a second convention. -/
lemma weightedOrderOfVanishingOnOrbit_eq_two_mul_div [SlashInvariantFormClass F 𝒮ℒ k] (f : F)
    (q : orbitRel.Quotient SL(2, ℤ) ℍ) :
    weightedOrderOfVanishingOnOrbit f q =
      2 * (orderOfVanishingOnOrbit f q : ℚ) / (cardStabilizerOnOrbit q : ℚ) := by
  have he : (ModularGroup.ellipticOrder q : ℚ) ≠ 0 := by
    exact_mod_cast (ModularGroup.ellipticOrder_pos q).ne'
  rw [weightedOrderOfVanishingOnOrbit_def,
    ModularGroup.cardStabilizerOnOrbit_eq_two_mul_ellipticOrder]
  push_cast
  field_simp

/-- **The level-one weight at a point redistributes over the `Γ`-orbits above it.** The weighted
vanishing order of the norm at the `SL(2, ℤ)`-orbit of `p` is the sum of the general-level
weighted orders of `f` over the `Γ`-orbits inside that orbit.

This is the local form of the general-level valence formula: each coset of `Γ` in `SL(2, ℤ)`
contributes one factor to the norm, the cosets landing in one `Γ`-orbit are counted by the
orbit-stabiliser identity, and the stabiliser weight is exactly what converts that count into
the weight `2 / |Stab_Γ P|`. -/
lemma weightedOrderOfVanishingOnOrbit_norm_eq_finsum_mem
    [(Γ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex 𝒮ℒ]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient SL(2, ℤ) ℍ) :
    weightedOrderOfVanishingOnOrbit (_root_.ModularForm.norm 𝒮ℒ f) P =
      ∑ᶠ o ∈ slOrbitOfSubgroupOrbit (Γ := Γ) ⁻¹' {P},
        weightedOrderOfVanishingOnSubgroupOrbit f o := by
  induction P using Quotient.inductionOn' with
  | h p =>
    have he : (ModularGroup.ellipticOrder
        (Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ) : ℚ) ≠ 0 := by
      exact_mod_cast (ModularGroup.ellipticOrder_pos _).ne'
    -- the multiplicity of a `Γ`-orbit, divided by the level-one weight, is the general-level weight
    have key : ∀ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        ((Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
              orbitOfCosetTranslate p q = o} • orderOfVanishingOnSubgroupOrbit f o : ℤ) : ℚ) *
            (ModularGroup.ellipticOrder (Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ) : ℚ)⁻¹ =
          Set.indicator (slOrbitOfSubgroupOrbit (Γ := Γ) ⁻¹'
              {(Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ)})
            (weightedOrderOfVanishingOnSubgroupOrbit f) o := by
      intro o
      by_cases ho : slOrbitOfSubgroupOrbit o = (Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ)
      · rw [Set.indicator_of_mem (by simpa using ho), weightedOrderOfVanishingOnSubgroupOrbit_def]
        have hprod := card_fiber_orbitOfCosetTranslate_mul_cardStabilizerOnOrbit_eq p ho
        have hc : (cardStabilizerOnOrbit o : ℚ) ≠ 0 := by
          exact_mod_cast cardStabilizerOnOrbit_ne_zero o
        have hprod' : (Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
            orbitOfCosetTranslate p q = o} : ℚ) * (cardStabilizerOnOrbit o : ℚ) =
            2 * (ModularGroup.ellipticOrder
              (Quotient.mk'' p : orbitRel.Quotient SL(2, ℤ) ℍ) : ℚ) := by
          exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) hprod
        rw [nsmul_eq_mul]
        push_cast
        field_simp
        linear_combination (orderOfVanishingOnSubgroupOrbit f o : ℚ) * hprod'
      · rw [Set.indicator_of_notMem (by simpa using ho),
          card_fiber_orbitOfCosetTranslate_eq_zero p ho]
        simp
    have hcast : ((∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
            orbitOfCosetTranslate p q = o} • orderOfVanishingOnSubgroupOrbit f o : ℤ) : ℚ) =
        ∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          ((Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
            orbitOfCosetTranslate p q = o} • orderOfVanishingOnSubgroupOrbit f o : ℤ) : ℚ) :=
      AddMonoidHom.map_finsum_of_injective (Int.castAddHom ℚ) Int.cast_injective _
    rw [weightedOrderOfVanishingOnOrbit_mk, orderOfVanishingAt_norm_eq_finsum_orbit f hf p,
      finsum_mem_def, div_eq_mul_inv, hcast, finsum_mul]
    exact finsum_congr key

/-- The general-level weighted order is nonnegative: a modular form is holomorphic and the
weight is positive. -/
lemma weightedOrderOfVanishingOnSubgroupOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    0 ≤ weightedOrderOfVanishingOnSubgroupOrbit f o := by
  rw [weightedOrderOfVanishingOnSubgroupOrbit_def]
  refine div_nonneg ?_ (by positivity)
  have := orderOfVanishingOnSubgroupOrbit_nonneg f o
  positivity

/-- Only finitely many `Γ`-orbits carry nonzero weighted order: the weight cannot create support
where the order has none. -/
lemma hasFiniteSupport_weightedOrderOfVanishingOnSubgroupOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (weightedOrderOfVanishingOnSubgroupOrbit (Γ := Γ) (k := k) f) := by
  refine (hasFiniteSupport_orderOfVanishingOnSubgroupOrbit f).subset fun o ho ↦ ?_
  simp only [Function.mem_support, ne_eq] at ho ⊢
  exact fun h0 ↦ ho (by rw [weightedOrderOfVanishingOnSubgroupOrbit_def, h0]; simp)

/-- **The interior mass of the norm, redistributed over the `Γ`-orbits.** The level-one weighted
divisor sum of `ModularForm.norm 𝒮ℒ f` is the general-level weighted divisor sum of `f`.

Each `SL(2, ℤ)`-orbit splits into finitely many `Γ`-orbits, and
`weightedOrderOfVanishingOnOrbit_norm_eq_finsum_mem` evaluates the level-one weight at that orbit
as the sum of the general-level weights over the pieces. -/
theorem finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_finsum_norm [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        weightedOrderOfVanishingOnSubgroupOrbit f o) =
      ∑ᶠ P : orbitRel.Quotient SL(2, ℤ) ℍ,
        weightedOrderOfVanishingOnOrbit (_root_.ModularForm.norm 𝒮ℒ f) P := by
  have hsupp : (Function.support
      (weightedOrderOfVanishingOnSubgroupOrbit (Γ := Γ) (k := k) f)).Finite :=
    hasFiniteSupport_weightedOrderOfVanishingOnSubgroupOrbit f
  set I := slOrbitOfSubgroupOrbit (Γ := Γ) ''
    Function.support (weightedOrderOfVanishingOnSubgroupOrbit (Γ := Γ) (k := k) f) with hIdef
  have hdisj : I.PairwiseDisjoint (fun P ↦ slOrbitOfSubgroupOrbit (Γ := Γ) ⁻¹' {P}) := by
    intro a _ b _ hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_preimage, Set.mem_singleton_iff]
    exact fun o h1 h2 ↦ hab (h1 ▸ h2)
  -- the `Γ`-orbits carrying mass are covered by the fibres above the finitely many
  -- `SL(2, ℤ)`-orbits they lie in
  have hsub : Function.support (weightedOrderOfVanishingOnSubgroupOrbit (Γ := Γ) (k := k) f) ⊆
      ⋃ P ∈ I, slOrbitOfSubgroupOrbit (Γ := Γ) ⁻¹' {P} := fun o ho ↦
    Set.mem_biUnion (show slOrbitOfSubgroupOrbit (Γ := Γ) o ∈ I from ⟨o, ho, rfl⟩) rfl
  rw [show (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        weightedOrderOfVanishingOnSubgroupOrbit f o) =
      ∑ᶠ o ∈ ⋃ P ∈ I, slOrbitOfSubgroupOrbit (Γ := Γ) ⁻¹' {P},
        weightedOrderOfVanishingOnSubgroupOrbit f o from by
      rw [finsum_mem_def, Set.indicator_eq_self.mpr hsub],
    finsum_mem_biUnion hdisj (hsupp.image _)
      fun P _ ↦ finite_preimage_slOrbitOfSubgroupOrbit P,
    finsum_mem_congr rfl fun P _ ↦
      (weightedOrderOfVanishingOnOrbit_norm_eq_finsum_mem f hf P).symm, finsum_mem_def]
  -- and every `SL(2, ℤ)`-orbit carrying mass in the norm is one of them
  refine congrArg finsum (Set.indicator_eq_self.mpr fun P hP ↦ ?_)
  rw [Function.mem_support, weightedOrderOfVanishingOnOrbit_norm_eq_finsum_mem f hf P] at hP
  by_contra hPI
  refine hP (finsum_mem_of_eqOn_zero fun o ho ↦ ?_)
  by_contra hne
  exact hPI ⟨o, hne, by simpa using ho⟩

/-- **The valence formula at general level, interior part.** For a nonzero weight-`k` modular
form on a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the weighted divisor sum over `Γ \ ℍ`, together
with the cusp order of the level-one norm, is `k · [SL(2, ℤ) : Γ] / 12`.

`Σ_{P ∈ Γ \ ℍ} (2 / |Stab_Γ P|) · ord_P f + ord_∞(Nm f) = k · [SL(2, ℤ) : Γ] / 12`.

This is `valence_formula_weighted` transported along the norm map: the interior mass is already
indexed by the `Γ`-orbits, weighted as the roadmap's `1 / e_P` up to the factor
`|Stab_Γ P| = |{±I} ∩ Γ| · e_P` (see `weightedOrderOfVanishingOnSubgroupOrbit`), and the index
is the **full** coset index, as it must be for odd weight with `-I ∉ Γ`.

The cusp term is still read at level one, on the norm. Distributing it over the cusps of `Γ`,
each weighted by its width, is the remaining step of the general-level formula; the norm's
`q`-expansion order at `∞` is decomposed in `TauCeti.ModularForm.qExpansion_one_norm_order_eq`. -/
theorem valence_formula_finiteIndex [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          weightedOrderOfVanishingOnSubgroupOrbit f o) +
        (qExpansionOrderAtCusp 1 ⇑(_root_.ModularForm.norm 𝒮ℒ f) : ℚ) =
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) / 12 := by
  have hf' : (⇑(_root_.ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) ≠ 0 := fun h0 ↦
    _root_.ModularForm.norm_ne_zero 𝒮ℒ hf (by ext τ; simpa using congrFun h0 τ)
  rw [finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_finsum_norm f hf,
    valence_formula_weighted _ hf']
  push_cast
  ring

/-! ### Consequences for a single orbit -/

/-- **The mass at one orbit is bounded by the total mass.** Every other term of the general-level
valence formula is nonnegative, so `24 · ord_P f ≤ k · [SL(2, ℤ) : Γ] · |Stab_Γ P|` for a nonzero
form — the general-level counterpart of
`TauCeti.ModularForm.twelve_mul_orderOfVanishingOnOrbit_le_weight_mul_ellipticOrder`, with the
`24` in place of `12` because the weight is read on the matrix stabiliser. -/
theorem twentyFour_mul_orderOfVanishingOnSubgroupOrbit_le [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    24 * orderOfVanishingOnSubgroupOrbit f o ≤
      k * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) *
        cardStabilizerOnOrbit o := by
  have hc : (0 : ℚ) < (cardStabilizerOnOrbit o : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (cardStabilizerOnOrbit_ne_zero o)
  have hsingle := single_le_finsum o (hasFiniteSupport_weightedOrderOfVanishingOnSubgroupOrbit f)
    (weightedOrderOfVanishingOnSubgroupOrbit_nonneg f)
  have hcusp : (0 : ℚ) ≤ (qExpansionOrderAtCusp 1 ⇑(_root_.ModularForm.norm 𝒮ℒ f) : ℚ) := by
    exact_mod_cast qExpansionOrderAtCusp_nonneg 1 ⇑(_root_.ModularForm.norm 𝒮ℒ f)
  have htotal := valence_formula_finiteIndex f hf
  have hle : weightedOrderOfVanishingOnSubgroupOrbit f o ≤
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) / 12 := by linarith
  rw [weightedOrderOfVanishingOnSubgroupOrbit_def, div_le_iff₀ hc] at hle
  have hq : (24 : ℚ) * (orderOfVanishingOnSubgroupOrbit f o : ℚ) ≤
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) *
        (cardStabilizerOnOrbit o : ℚ) := by linarith
  exact_mod_cast hq

/-- **A small enough weighted degree forces vanishing order zero at an orbit.** If `f` is nonzero
this says that `f` does not vanish there; the statement also covers the zero form, whose vanishing
order is zero by convention. -/
theorem orderOfVanishingOnSubgroupOrbit_eq_zero_of_lt_twentyFour [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ}
    (hk : k * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) *
      cardStabilizerOnOrbit o < 24) :
    orderOfVanishingOnSubgroupOrbit f o = 0 := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · induction o using Quotient.inductionOn' with
    | _ p => simp [hf]
  · have hbound := twentyFour_mul_orderOfVanishingOnSubgroupOrbit_le f hf o
    have := orderOfVanishingOnSubgroupOrbit_nonneg f o
    omega

end ModularForm

end TauCeti

end
