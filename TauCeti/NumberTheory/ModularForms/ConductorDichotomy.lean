/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ZMod.Divisibility
public import TauCeti.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.CuspDescent

/-!
# The level-lowering dichotomy

`CuspDescent.lean` builds the descent half of the conductor theorem: when the nebentypus `χ` is
trivial on the kernel of `(ZMod N)ˣ → (ZMod (N / l))ˣ`, the function `f` whose level-raise is a
cusp form of level `N` is itself a cusp form of level `N / l`. That is one horn of a dichotomy.
This file supplies the other horn — when `χ` is *not* trivial on that kernel, `f` vanishes — and
then puts the two together.

## The shape of the vanishing argument

The obstruction is read off a single unit. If `χ` is nontrivial on the kernel, pick `u` in the
kernel with `χ u ≠ 1`, and lift it to `Γ₀(N)`. Slashing `f` by the `diag(l, 1)`-conjugate of that
lift multiplies `f` by `χ u`. But the same conjugate can be *refactored*: `u` may be replaced by
any `u'` in its `ZMod.unitsMap`-coset at the cost of two translations `T ^ i` and `T ^ j`, and `f`
is `T`-periodic, so the translations contribute nothing. Choosing `u'` with `χ u' ≠ χ u` — which
is exactly what nontriviality on the kernel provides — exhibits `f ∣[k] A` as both `χ u • f` and
`χ u' • f` for one matrix `A`. Two distinct multipliers for one slash force `f = 0`.

The refactoring step needs the lift's lower-left entry to be *exactly* `N`, not merely divisible
by it, because `conjScale l · c` records the cofactor `c` and the argument compares the cofactors
of two lifts. `CongruenceSubgroup.gamma0Twist N p h` is already such a lift, so a unit `u` is
lifted by taking `p` to be the representative `(u : ZMod N).val`. Only the bottom row of that
lift is specified, so the congruence between the *upper*-left entries of two of them — the
shift `T ^ i` — is read off the determinants rather than off a formula for those entries.

## Main results

* `TauCeti.eq_zero_of_not_forall_apply_eq_one_of_unitsMap_eq_one`: **the vanishing horn**.
* `TauCeti.cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace`: the descent horn carries any
  character `χ₀` that `χ` pulls back from; the dichotomy specializes it to `hfac.χ₀`.
* `TauCeti.exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero`: **the level-lowering dichotomy**, in
  the roadmap's `DirichletCharacter` phrasing — either `χ` factors through `N / l` and `f` is a
  cusp form of level `N / l` for the lowered character, or `f = 0`.

## Implementation notes

`CuspDescent.lean` carries its character as the units homomorphism `(ZMod N)ˣ →* ℂˣ` that
`cuspFormCharSpace` is indexed by, with the descent hypothesis `∀ u, ZMod.unitsMap _ u = 1 →
χ u = 1`. The vanishing horn below is stated over the *same* homomorphism with the *negation* of
that hypothesis, so the dichotomy is a `by_cases` on one proposition and neither horn has to
restate the other's hypotheses. Only the final theorem is phrased over a `DirichletCharacter`,
where `FactorsThrough` and the lowered character `FactorsThrough.χ₀` live; the bridge between the
two phrasings is mathlib's `DirichletCharacter.factorsThrough_iff_ker_unitsMap`.

## References

* [Miyake, *Modular forms*][miyake1989], Theorem 4.6.4.
* Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck, Apache-2.0) at
  commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean` lines 542-887 —
  the Case B block of `conductor_theorem_dichotomy_cuspForm_strong`. The source's
  `levelRaiseConjOfDvd` is this repository's `conjScale`, its `levelRaiseFun l k f` is
  `l ^ (1 - k) • (f ∣[k] scaleGL l)`, and its `Gamma0MapUnits` is `(Gamma0Map N).toHomUnits`, so
  none of those three is ported again. Its explicit Bézout lift of a unit is this repository's
  `CongruenceSubgroup.gamma0Twist`, specialized at a representative of the unit, so that is not
  ported again either. The source's `exists_T_levelRaiseConj_T_factor` is already here as
  `exists_eq_T_zpow_mul_conjScale_mul_T_zpow`, and its `loweredCharacter` is mathlib's
  `DirichletCharacter.FactorsThrough.χ₀`.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### The lower-left entry of the Bézout twist -/

omit [NeZero N] in
/-- The lower-left entry of the Bézout twist at a unit, factored as `l * (N / l)`. This is the
shape `TauCeti.conjScale` asks for, and it records `N / l` as the cofactor. -/
private lemma gamma0TwistOfUnit_apply_one_zero_eq_mul {l : ℕ} (hlN : l ∣ N) (u : (ZMod N)ˣ) :
    gamma0TwistOfUnit u 1 0 = (l : ℤ) * ((N / l : ℕ) : ℤ) := by
  rw [gamma0TwistOfUnit_apply_one_zero]
  exact_mod_cast (Nat.mul_div_cancel' hlN).symm


/-! ### Refactoring the conjugated lift through a separating unit -/

/-- **The upper-left entries of two Bézout lifts are congruent too.** Only the bottom row of
`CongruenceSubgroup.gamma0Twist` is specified, so the shift `T ^ i` cannot be read off a formula
for the upper-left entries — and it does not have to be. The determinant makes the lower-right
entry invertible modulo the cofactor `Nl`, and cancelling it turns the congruence of the
lower-right entries into one of the upper-left entries. -/
private lemma dvd_sub_of_dvd_sub_of_det {l Nl a a' e e' b b' : ℤ}
    (hdet : a * e - b * (l * Nl) = 1) (hdet' : a' * e' - b' * (l * Nl) = 1)
    (he : Nl ∣ e - e') : Nl ∣ a - a' := by
  obtain ⟨c, hc⟩ := he
  have hcop : IsCoprime e Nl := ⟨a, -(b * l), by linear_combination hdet⟩
  refine hcop.symm.dvd_of_dvd_mul_right ⟨(b - b') * l - a' * c, ?_⟩
  linear_combination hdet - hdet' - a' * hc

/-- The matrix identity behind the refactoring: two Bézout lifts whose upper-left and lower-right
entries agree modulo the cofactor `Nl` differ by translations on both sides. The determinant
hypotheses are what pin the upper-right entries once the other three agree. -/
private lemma eq_T_mul_mul_T_of_sub_eq {l Nl i j a a' e e' b b' : ℤ} (hNl : Nl ≠ 0)
    (hi : i * Nl = a - a') (hj : j * Nl = e - e') (hdet : a * e - b * (l * Nl) = 1)
    (hdet' : a' * e' - b' * (l * Nl) = 1) : (!![a, l * b; Nl, e] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), i; 0, 1] * !![a', l * b'; Nl, e'] * !![(1 : ℤ), j; 0, 1] := by
  simp only [Matrix.mul_fin_two]
  congrm !![?_, ?_; ?_, ?_]
  · linear_combination -hi
  -- the upper-right entry is the only one the determinants are needed for: both sides agree
  -- after multiplying by the nonzero cofactor `Nl`, so cancel it
  · apply mul_left_cancel₀ hNl
    linear_combination -hdet + hdet' + (-e' - Nl * j) * hi + (-a) * hj
  · ring
  · linear_combination -hj

/-- **The refactoring step.** For a character not trivial on the kernel, the `diag(l, 1)`-conjugate
of the Bézout lift of `u` is a translate — on both sides — of the conjugate of the lift of some
`u'` on which the character takes a *different* value. Since the function the vanishing argument
is applied to is `T`-periodic, the two translations cost nothing, and the two sides therefore
exhibit one slash with two different multipliers. -/
private theorem exists_apply_ne_and_eq_T_zpow_mul_conjScale_mul_T_zpow {l : ℕ}
    (hlN : l ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ¬ ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hlN) u = 1 → χ u = 1) (u : (ZMod N)ˣ)
    : ∃ (i j : ℤ) (u' : (ZMod N)ˣ), χ u' ≠ χ u ∧
      conjScale l (gamma0TwistOfUnit u) ((N / l : ℕ) : ℤ)
        (gamma0TwistOfUnit_apply_one_zero_eq_mul hlN _) =
      ModularGroup.T ^ i * conjScale l (gamma0TwistOfUnit u') ((N / l : ℕ) : ℤ)
        (gamma0TwistOfUnit_apply_one_zero_eq_mul hlN _) * ModularGroup.T ^ j := by
  -- `l ≠ 0` is forced by `hlN` and `NeZero N`, so it is derived rather than demanded
  have : NeZero l := NeZero.of_dvd hlN
  -- the separation is `DirichletCharacter.exists_alt_unit_in_coset_with_char_separation`, read
  -- through `MulChar.ofUnitHom`; `hχ` is the negation of `FactorsThrough` by
  -- `DirichletCharacter.factorsThrough_iff_ker_unitsMap`, exactly as in the dichotomy below
  have hnfac : ¬ DirichletCharacter.FactorsThrough (MulChar.ofUnitHom χ) (N / l) := by
    refine fun hfac ↦ hχ fun v hv ↦ ?_
    simpa using MonoidHom.mem_ker.mp
      ((DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.div_dvd_of_dvd hlN)).mp hfac
        (MonoidHom.mem_ker.mpr hv))
  obtain ⟨u', hcoset, hne⟩ :=
    DirichletCharacter.exists_alt_unit_in_coset_with_char_separation
      (Nat.div_dvd_of_dvd hlN) hnfac u
  simp only [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply] at hne
  set Nl : ℤ := ((N / l : ℕ) : ℤ) with hNl
  have hNl_ne : Nl ≠ 0 := by
    rw [hNl, Nat.cast_ne_zero]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hlN) (Nat.pos_of_neZero l)).ne'
  -- the determinant of a lift, read through the factorization `N = l * (N / l)` of its
  -- lower-left entry: this is the only thing known about the upper row
  have hdet : ∀ v : (ZMod N)ˣ, gamma0TwistOfUnit v 0 0 * gamma0TwistOfUnit v 1 1 -
      gamma0TwistOfUnit v 0 1 * ((l : ℤ) * Nl) = 1 := fun v => by
    rw [← gamma0TwistOfUnit_apply_one_zero_eq_mul (l := l) hlN v]
    exact fin_two_mul_sub_mul_eq_one _
  -- the lower-right entries are the unit values, so the coset congruence is one between them
  have hdvd_e : Nl ∣ gamma0TwistOfUnit u 1 1 - gamma0TwistOfUnit u' 1 1 := by
    rw [gamma0TwistOfUnit_apply_one_one, gamma0TwistOfUnit_apply_one_one]
    exact ZMod.natCast_dvd_val_sub_of_unitsMap_eq (Nat.div_dvd_of_dvd hlN) _ _ hcoset.symm
  obtain ⟨i, hi⟩ := dvd_sub_of_dvd_sub_of_det (hdet u) (hdet u') hdvd_e
  obtain ⟨j, hj⟩ := hdvd_e
  refine ⟨i, j, u', hne, Subtype.ext ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow, coe_conjScale, coe_conjScale]
  exact eq_T_mul_mul_T_of_sub_eq hNl_ne (by rw [hi]; ring) (by rw [hj]; ring) (hdet u) (hdet u')


/-! ### The vanishing horn -/

/-- **The vanishing horn of the level-lowering dichotomy.** If the nebentypus `χ` of the
level-raise of `f` is *not* trivial on the kernel of `(ZMod N)ˣ → (ZMod (N / l))ˣ`, and `f` is
`T`-periodic, then `f = 0`.

The hypotheses `hnb` and `hT` are exactly the ones
`TauCeti.slash_mapGL_eq_self_of_mem_Gamma1_div` takes for the descent, and `hχ` is the negation
of the triviality that `TauCeti.cuspFormOfSmulSlashScaleGL` assumes, so this is the complementary
case of the descent and neither statement restates the other's hypotheses. -/
theorem eq_zero_of_not_forall_apply_eq_one_of_unitsMap_eq_one {l : ℕ} [NeZero l]
    (hlN : l ∣ N) (k : ℤ)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ¬ ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hlN) u = 1 → χ u = 1) (f : ℍ → ℂ)
    (hnb : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N), (f ∣[k] scaleGL l) ∣[k] mapGL ℝ γ = (χ ((Gamma0Map
      N).toHomUnits ⟨γ, hγ⟩) : ℂ) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) : f = 0 := by
  -- start from the identity unit; the separation supplies the partner that breaks the tie
  obtain ⟨i, j, u', hne, hfactor⟩ :=
    exists_apply_ne_and_eq_T_zpow_mul_conjScale_mul_T_zpow hlN hχ 1
  have hdet := det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨ModularGroup.T, rfl⟩)
  -- the multiplier attached to the lift of a unit is the character at that unit
  have hmul : ∀ v : (ZMod N)ˣ,
      f ∣[k] (mapGL ℝ (conjScale l (gamma0TwistOfUnit v) ((N / l : ℕ) : ℤ)
        (gamma0TwistOfUnit_apply_one_zero_eq_mul hlN _)) : GL (Fin 2) ℝ) = (χ v : ℂ) • f := by
    intro v
    have h := slash_conjScale_eq_smul_of_slash_scaleGL (k := k) f (gamma0TwistOfUnit v)
      (gamma0TwistOfUnit_apply_one_zero_eq_mul hlN _) (hnb _ (gamma0TwistOfUnit_mem_Gamma0 _))
    rwa [Gamma0Map_toHomUnits_gamma0TwistOfUnit] at h
  -- the same slash, read through the refactoring, has the multiplier of the separating unit
  have halt : f ∣[k] (mapGL ℝ (conjScale l (gamma0TwistOfUnit 1) ((N / l : ℕ) : ℤ)
      (gamma0TwistOfUnit_apply_one_zero_eq_mul hlN _)) : GL (Fin 2) ℝ) = (χ u' : ℂ) • f := by
    rw [hfactor, map_mul, map_mul, map_zpow, map_zpow]
    exact slash_zpow_mul_mul_zpow_eq_smul k f hdet hT (hmul u') i j
  -- one slash with two different multipliers forces the function to vanish
  have hsub : ((χ u' : ℂ) - (χ 1 : ℂ)) • f = 0 := by
    rw [sub_smul, ← halt, ← hmul 1, sub_self]
  exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr fun h ↦ hne (Units.ext h))


/-! ### The dichotomy -/

/-- **The descended cusp form carries the lowered nebentypus.** `cuspFormOfSmulSlashScaleGL`
produces a cusp form of level `N / l`; this identifies its nebentypus as any character `χ₀` on
`ZMod (N / l)` that `χ` pulls back from, which is the hypothesis `hcomp`, and that is what makes
the descent an eigenform statement rather than merely a level statement. The dichotomy below
specializes `χ₀` to `hfac.χ₀`. -/
theorem cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace {l : ℕ} [NeZero l]
    (hlN : l ∣ N) (k : ℤ) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / l))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hlN))) (f : ℍ → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hgχ : g ∈ cuspFormCharSpace k χ)
    (hg : ⇑g = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    cuspFormOfSmulSlashScaleGL l N hlN k χ
      (fun _ hu ↦ by rw [hcomp, MonoidHom.comp_apply, hu, map_one]) f g hgχ hg hT ∈
      cuspFormCharSpace k χ₀ := by
  -- `hcomp` already forces `χ` to be trivial on the kernel: `χ u = χ₀ (unitsMap … u) = χ₀ 1`
  have hχ : ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hlN) u = 1 → χ u = 1 :=
    fun _ hu ↦ by rw [hcomp, MonoidHom.comp_apply, hu, map_one]
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  intro γ'
  rw [coe_cuspFormOfSmulSlashScaleGL]
  -- any unit of level `N` over the label of `γ'` will do; `slash_mapGL_eq_smul_of_unitsMap_eq`
  -- is independent of the choice, and on such a unit `χ` is the lowered character at the label
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hlN)
    ((Gamma0Map (N / l)).toHomUnits γ')
  have hval : (χ u : ℂ) = (χ₀ ((Gamma0Map (N / l)).toHomUnits γ') : ℂ) := by
    rw [hcomp, MonoidHom.comp_apply, hu]
  rw [← hval]
  exact slash_mapGL_eq_smul_of_unitsMap_eq l N hlN k χ hχ f
    (nebentypus_slash_scaleGL_of_mem_cuspFormCharSpace hgχ hg) hT γ' u hu

/-- **The level-lowering dichotomy.** For `l ∣ N`, a Dirichlet character `χ` of level `N`, and a
`T`-periodic `f : ℍ → ℂ` whose level-raise by `l` is a cusp form in `S_k(N, χ)`: *either* `χ`
factors through `N / l` and `f` is itself a cusp form in `S_k(N / l, χ↓)` for the lowered
character, *or* `f = 0`.

This is Miyake's Theorem 4.6.4. The two horns are `TauCeti.cuspFormOfSmulSlashScaleGL` with
`TauCeti.cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace`, and
`TauCeti.eq_zero_of_not_forall_apply_eq_one_of_unitsMap_eq_one`; the case split is on the
single proposition that one assumes and the other negates. -/
theorem exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero {l : ℕ} [NeZero l]
    (hlN : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hgχ : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg : ⇑g = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ hfac : χ.FactorsThrough (N / l), ∃ F : CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k, F ∈
      cuspFormCharSpace k hfac.χ₀.toUnitHom ∧ ⇑F = f) ∨ f = 0 := by
  classical
  by_cases hfac : χ.FactorsThrough (N / l)
  · -- the lowered character is `hfac.χ₀`, and `hfac.eq_changeLevel` is what says `χ` is its
    -- pullback along the reduction
    have hcomp : χ.toUnitHom =
        hfac.χ₀.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hlN)) := by
      conv_lhs => rw [hfac.eq_changeLevel]
      rw [DirichletCharacter.changeLevel_toUnitHom]
    exact .inl ⟨hfac, _,
      cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace hlN k hcomp f g hgχ hg hT,
      coe_cuspFormOfSmulSlashScaleGL l N hlN k χ.toUnitHom _ f g hgχ hg hT⟩
  · refine .inr (eq_zero_of_not_forall_apply_eq_one_of_unitsMap_eq_one hlN k ?_ f
      (nebentypus_slash_scaleGL_of_mem_cuspFormCharSpace hgχ hg) hT)
    exact fun h ↦ hfac
      ((DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.div_dvd_of_dvd hlN)).mpr
        fun u hu ↦ MonoidHom.mem_ker.mpr (h u (MonoidHom.mem_ker.mp hu)))


end TauCeti

end
