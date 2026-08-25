/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.NumberTheory.Modular.Stabilizer
public import TauCeti.NumberTheory.ModularForms.Norm.Order

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# The order divisor at general level, on the orbit space

For a subgroup `Γ ≤ SL(2, ℤ)`, the vanishing order of a modular form on `Γ` is constant on
`Γ`-orbits of the upper half-plane: every element of `Γ` acts through a matrix of determinant
`1`, and the order is invariant along positive-determinant elements of the group of the form.
This file descends the order to the orbit space `Γ \ ℍ` and records that, for `Γ` of finite
index, only finitely many orbits carry nonzero order — the summation index of the general-level
valence formula.

The orbit space is spelled `MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ`, the
index type the rest of the general-level API already uses; the `Γ`-orbits and the orbits of the
image of `Γ` in `GL (Fin 2) ℝ` are the same subsets of `ℍ`.

Because that is an ordinary `MulAction.orbitRel.Quotient`, the *other* function the valence
formula indexes over it — the stabiliser order — needs no modular-specific definition at all:
`TauCeti.cardStabilizerOnOrbit` in `GroupTheory/GroupAction/Stabilizer.lean` applies to this
quotient directly. Only the vanishing order, below, needs the determinant-`1` argument that
makes it well defined here.

The finiteness is not reproved here. It is
`TauCeti.ModularForm.finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup`, which
bounds the image of the nonzero-order set in `𝒢 \ ℍ` for any `𝒢 ≤ GL (Fin 2) ℝ` of finite
relative index in `𝒮ℒ`, by the norm-map route of the Tau Ceti ModularForms roadmap's Layer 1
milestone **“General level — by the coset norm”**. What this file adds is the order *function*
on the quotient, which that statement deliberately does not provide: a general `𝒢` may contain
elements of negative determinant, under which the order is not known to be invariant, while the
image of a subgroup of `SL(2, ℤ)` has determinant `1` throughout.

## Main declarations

* `TauCeti.ModularForm.slOrbitOfSubgroupOrbit`: the `SL(2, ℤ)`-orbit containing a `Γ`-orbit, with
  `TauCeti.ModularForm.finite_preimage_slOrbitOfSubgroupOrbit` — an `SL(2, ℤ)`-orbit contains only
  finitely many `Γ`-orbits.
* `TauCeti.ModularForm.orderOfVanishingOnSubgroupOrbit`: the order descended to the
  `Γ`-orbit space.
* `TauCeti.ModularForm.orderOfVanishingOnSubgroupOrbit_nonneg`: that order is nonnegative.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnSubgroupOrbit`: finite support of
  the interior order divisor of a general-level modular form.
* `TauCeti.ModularForm.orderOfVanishingAt_quotientFunc_eq_orderOfVanishingOnSubgroupOrbit`: a
  coset factor of the norm vanishes at `p` to the order `f` has on the orbit `p` is translated
  into.
* `TauCeti.ModularForm.orderOfVanishingAt_norm_eq_finsum_orbit`: hence the order of the norm at
  `p` is a sum over `Γ \ ℍ`, each orbit weighted by how many cosets translate `p` into it.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the descent here is the
  level-one one, `TauCeti.ModularForm.orderOfVanishingOnOrbit` in `Order/Orbits.lean`, which is
  ported from AINTLIB, transposed from `SL(2, ℤ)` to `Γ`.
* `TauCeti.ModularForm.finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup` in
  `Norm/Order.lean` — the general-`𝒢` form of the norm-map route, arrived at concurrently with
  this file and consumed by it here, rather than reproved.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Chapter 3.
-/

public noncomputable section

open UpperHalfPlane MulAction

open scoped MatrixGroups ModularForm Modular

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

/-- **The multiplicity of a `Γ`-orbit among the coset translates of `p`.** For a `Γ`-orbit inside
the `SL(2, ℤ)`-orbit of `p`, the number of cosets translating `p` into it, times the order of its
stabiliser in `Γ`, is the order of the stabiliser of `p` in `SL(2, ℤ)` — twice the elliptic order
of the level-one orbit. -/
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
orbit-stabiliser identity divides — so its cardinality never vanishes. -/
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

/-- The vanishing order of a form for `Γ ≤ SL(2, ℤ)`, descended to the `Γ`-orbit space of
the upper half-plane. -/
public def orderOfVanishingOnSubgroupOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (q : MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) : ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt f) fun _ b ⟨g, hg⟩ ↦ by
    have hg' : g • b = _ := hg
    rw [← hg', Subgroup.smul_def,
      orderOfVanishingAt_smul f g.2 (det_pos_of_mem_slGL (Subgroup.map_le_range _ _ g.2)) b]

/-- Evaluating the descended order on the orbit of `p` recovers the vanishing order at `p`. -/
@[simp]
public lemma orderOfVanishingOnSubgroupOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ) :
    orderOfVanishingOnSubgroupOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold orderOfVanishingOnSubgroupOrbit
  rfl

/-- The vanishing order on an orbit is nonnegative: a modular form is holomorphic, so it has no
poles. -/
public lemma orderOfVanishingOnSubgroupOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (q : MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    0 ≤ orderOfVanishingOnSubgroupOrbit f q := by
  induction q using Quotient.inductionOn' with
  | _ p => simpa using orderOfVanishingAt_nonneg (ModularFormClass.holo f) p

/-- **The coset factors of the norm see exactly the orbits of the translates of the point.**
The factor indexed by `q` vanishes at `p` to the order `f` itself has on the orbit into which
`q` translates `p`.

This is what turns the coset sum of `orderOfVanishingAt_norm` into a sum over orbits: the
summand depends on `q` only through `orbitOfCosetTranslate p q`. -/
public lemma orderOfVanishingAt_quotientFunc_eq_orderOfVanishingOnSubgroupOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    orderOfVanishingAt (_root_.SlashInvariantForm.quotientFunc f q) p =
      orderOfVanishingOnSubgroupOrbit f (orbitOfCosetTranslate p q) := by
  induction q using Quotient.inductionOn with
  | h h =>
    rw [_root_.SlashInvariantForm.quotientFunc_mk, orbitOfCosetTranslate_mk,
      orderOfVanishingOnSubgroupOrbit_mk, orderOfVanishingAt_slash (k := k)]
    -- the slash acts by `h⁻¹`, which lies in `𝒮ℒ` and so has positive determinant
    exact det_pos_of_mem_slGL (inv_mem h.2)

/-- A modular form for a finite-index subgroup `Γ ≤ SL(2, ℤ)` has nonzero vanishing order on
only finitely many `Γ`-orbits in the upper half-plane.

This is the finite-support statement for the interior part of the general-level divisor. As at
level one, the zero form needs no exclusion: its order vanishes identically, so its support is
empty. -/
public theorem hasFiniteSupport_orderOfVanishingOnSubgroupOrbit
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (orderOfVanishingOnSubgroupOrbit f).HasFiniteSupport := by
  -- an orbit of nonzero order is the class of a point of nonzero order, so the support sits
  -- inside the image that the general-level finiteness lemma bounds
  refine (finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup f).subset ?_
  intro q hq
  induction q using Quotient.inductionOn' with
  | _ p => exact ⟨p, by simpa using hq, rfl⟩

/-- **The order of the norm at a point, regrouped over the orbit space.** The vanishing order
of `ModularForm.norm 𝒮ℒ f` at `p` is the sum, over the `Γ`-orbits of the upper half-plane, of
the descended order of `f` on the orbit weighted by how many cosets translate `p` into it.

This is the interior half of the general-level valence formula: the left-hand side is a level
one quantity, which the level-one formula evaluates, while the right-hand side is indexed by
`Γ \ ℍ`. The fibre counts become the ramification weights `1 / e_P` once the stabiliser
comparison converts them. -/
public theorem orderOfVanishingAt_norm_eq_finsum_orbit
    [(Γ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex 𝒮ℒ]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (p : ℍ) :
    orderOfVanishingAt (⇑(_root_.ModularForm.norm 𝒮ℒ f)) p =
      ∑ᶠ o : MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
          orbitOfCosetTranslate p q = o} • orderOfVanishingOnSubgroupOrbit f o := by
  classical
  have _ : Fintype (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  rw [orderOfVanishingAt_norm f hf p, finsum_eq_sum_of_fintype]
  simp only [orderOfVanishingAt_quotientFunc_eq_orderOfVanishingOnSubgroupOrbit]
  -- `𝒢`/`ℋ` are spelled out because `Finset.univ` is otherwise stuck on a metavariable
  rw [← Finset.sum_fiberwise_of_maps_to' fun q _ ↦ Finset.mem_image_of_mem
      (orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (ℋ := 𝒮ℒ) p) (Finset.mem_univ q),
    finsum_eq_sum_of_support_subset _ (s := Finset.image
      (orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (ℋ := 𝒮ℒ) p) Finset.univ) ?_]
  · exact Finset.sum_congr rfl fun o _ ↦ by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro o ho
    by_contra hmem
    have : IsEmpty {q // orbitOfCosetTranslate p q = o} :=
      ⟨fun q ↦ hmem (Finset.mem_coe.2 (Finset.mem_image.2 ⟨q.1, Finset.mem_univ _, q.2⟩))⟩
    exact ho (by simp)

end ModularForm

end TauCeti

end
