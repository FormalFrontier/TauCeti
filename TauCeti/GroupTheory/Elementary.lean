/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

/-!
# Elementary and hyperelementary groups

Fix a natural number `p`. A group is **`p`-elementary** when it is the internal direct product of a
cyclic subgroup of order prime to `p` and a `p`-subgroup, and **`p`-hyperelementary** when it has a
cyclic normal subgroup of order prime to `p` whose quotient is a `p`-group; a group is
**elementary** (respectively **hyperelementary**) when it is `p`-elementary (respectively
`p`-hyperelementary) for some prime `p`. Mathlib has `IsCyclic` and `IsPGroup` but no predicate
built from them in this shape, so this file supplies the two definitions together with the closure
properties they are used through.

The definitions are the ones Brauer's induction theorem is stated against: Artin's theorem writes a
character as a rational combination of characters induced from *cyclic* subgroups, and Brauer's
sharpens this to an integral combination of characters induced from *elementary* subgroups. That
the elementary groups include the cyclic ones is the content of
`TauCeti.isPElementary_of_isCyclic` below: a finite cyclic group is `p`-elementary for **every**
prime `p`, by splitting it as the product of its `p`-part and its `p'`-part.

## Main definitions

* `TauCeti.IsPElementary p G`: `G` is the internal direct product of a cyclic subgroup of order
  prime to `p` and a `p`-subgroup.
* `TauCeti.IsPHyperelementary p G`: `G` has a cyclic normal subgroup of order prime to `p` with
  `p`-group quotient.
* `TauCeti.IsElementary G`, `TauCeti.IsHyperelementary G`: the same, for some prime `p`.

Each of the four predicates is restated as an `Iff` by `TauCeti.isPElementary_def`,
`TauCeti.isPHyperelementary_def`, `TauCeti.isElementary_def` and `TauCeti.isHyperelementary_def`.

## Main results

* `TauCeti.isPElementary_of_isCyclic`: every finite cyclic group is `p`-elementary, for every
  prime `p`; hence `TauCeti.isElementary_of_isCyclic`, cyclic groups are elementary.
* `TauCeti.IsPElementary.isPHyperelementary`: `p`-elementary groups are `p`-hyperelementary.
* `TauCeti.IsPElementary.of_injective`, `TauCeti.IsPHyperelementary.of_injective`: both classes are
  closed under passing to a subgroup, in the form of an injective homomorphism into the group. The
  subgroup forms are `TauCeti.IsPElementary.subgroup` and `TauCeti.IsPHyperelementary.subgroup`.
* `TauCeti.IsHyperelementary.isSolvable`: a finite hyperelementary group is solvable, whence
  `TauCeti.not_isElementary_perm_fin_five`, the symmetric group on five letters is not elementary.

## Implementation notes

The `p`-group condition on the quotient in `TauCeti.IsPHyperelementary` is spelled out elementwise,
as `∀ g, ∃ k, g ^ p ^ k ∈ C`, rather than as `IsPGroup p (G ⧸ C)`. The two are equivalent
(`TauCeti.isPHyperelementary_iff_isPGroup_quotient`, and the two implications it is assembled from,
`TauCeti.isPGroup_quotient_of_forall_exists_pow_mem` and
`TauCeti.isPHyperelementary_of_isPGroup_quotient`), but the quotient `G ⧸ C` is a group only once
the normality of `C` is available as an instance, which an existential quantifier inside the
definition cannot supply. The elementwise form keeps the definition free of that bookkeeping and is
also the form the closure proofs use directly.

`TauCeti.IsPElementary` records the internal direct product decomposition as
`Subgroup.IsComplement'` together with elementwise commutation, rather than as normality of both
factors: this is the form the proofs consume, and normality of the cyclic factor is derived from it
in `TauCeti.normal_of_commute_of_isComplement'`.

## References

This supplies a prerequisite for
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`,
Layer 6 ("Elementary and hyperelementary subgroups"), which asks for exactly these two predicates
"from these orientations, with their basic closure properties", as the indexing sets of Artin's and
Brauer's induction theorems.

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II, §10.
-/

public section

namespace TauCeti

open Subgroup

section Defs

variable (p : ℕ) (G : Type*) [Group G]

/-- A group `G` is **`p`-elementary** when it is the internal direct product of a cyclic subgroup
of order prime to `p` and a `p`-subgroup: there are subgroups `C` and `P` of `G` with `C` cyclic of
order prime to `p`, `P` a `p`-group, every element of `C` commuting with every element of `P`, and
`C` a complement of `P`. -/
def IsPElementary : Prop :=
  ∃ C P : Subgroup G, IsCyclic C ∧ ¬ p ∣ Nat.card C ∧ IsPGroup p P ∧
    (∀ c ∈ C, ∀ x ∈ P, Commute c x) ∧ C.IsComplement' P

/-- A group `G` is **`p`-hyperelementary** when it has a cyclic normal subgroup `C` of order prime
to `p` whose quotient `G ⧸ C` is a `p`-group. The condition on the quotient is spelled elementwise,
as `∀ g, ∃ k, g ^ p ^ k ∈ C`; see `TauCeti.isPGroup_quotient_of_forall_exists_pow_mem` for the
identification with `IsPGroup p (G ⧸ C)`. -/
def IsPHyperelementary : Prop :=
  ∃ C : Subgroup G, C.Normal ∧ IsCyclic C ∧ ¬ p ∣ Nat.card C ∧
    ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ C

/-- A group is **elementary** when it is `p`-elementary for some prime `p`. -/
def IsElementary : Prop := ∃ q : ℕ, q.Prime ∧ IsPElementary q G

/-- A group is **hyperelementary** when it is `p`-hyperelementary for some prime `p`. -/
def IsHyperelementary : Prop := ∃ q : ℕ, q.Prime ∧ IsPHyperelementary q G

end Defs

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-! ### Restating the definitions

The four definitions above are `public` but not `@[expose]`, so downstream modules see their
statements and not their bodies: neither `unfold IsPElementary` nor `simp only [IsPElementary]`
is available there. The `Iff.rfl` lemmas in this section are therefore the only way to eliminate
the predicates outside this file, as `Subgroup.isComplement'_def` is for `Subgroup.IsComplement'`
and `isPrimePow_def` is for `IsPrimePow`.
-/

/-- `TauCeti.IsPElementary p G` unfolded: a decomposition of `G` into a cyclic subgroup of order
prime to `p` and a complementary `p`-subgroup commuting with it elementwise. -/
theorem isPElementary_def : IsPElementary p G ↔
    ∃ C P : Subgroup G, IsCyclic C ∧ ¬ p ∣ Nat.card C ∧ IsPGroup p P ∧
      (∀ c ∈ C, ∀ x ∈ P, Commute c x) ∧ C.IsComplement' P :=
  Iff.rfl

/-- `TauCeti.IsPHyperelementary p G` unfolded: a cyclic normal subgroup of order prime to `p` such
that every element of `G` has a `p`-power inside it. See
`TauCeti.isPHyperelementary_iff_isPGroup_quotient` for the quotient reading of the last clause. -/
theorem isPHyperelementary_def : IsPHyperelementary p G ↔
    ∃ C : Subgroup G, C.Normal ∧ IsCyclic C ∧ ¬ p ∣ Nat.card C ∧
      ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ C :=
  Iff.rfl

/-- `TauCeti.IsElementary G` unfolded: `p`-elementarity for some prime `p`. -/
theorem isElementary_def : IsElementary G ↔ ∃ q : ℕ, q.Prime ∧ IsPElementary q G :=
  Iff.rfl

/-- `TauCeti.IsHyperelementary G` unfolded: `p`-hyperelementarity for some prime `p`. -/
theorem isHyperelementary_def : IsHyperelementary G ↔ ∃ q : ℕ, q.Prime ∧ IsPHyperelementary q G :=
  Iff.rfl

/-! ### The quotient form of hyperelementarity -/

/-- If every element of `G` has a `p`-power lying in a normal subgroup `C`, the quotient `G ⧸ C` is
a `p`-group. This is the quotient reading of the last clause of `TauCeti.IsPHyperelementary`. -/
theorem isPGroup_quotient_of_forall_exists_pow_mem {C : Subgroup G} [C.Normal]
    (h : ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ C) : IsPGroup p (G ⧸ C) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := h g
  exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

/-- A cyclic normal subgroup of order prime to `p` with `p`-group quotient exhibits `G` as
`p`-hyperelementary. -/
theorem isPHyperelementary_of_isPGroup_quotient (C : Subgroup G) [hC : C.Normal]
    (h₁ : IsCyclic C) (h₂ : ¬ p ∣ Nat.card C) (h₃ : IsPGroup p (G ⧸ C)) :
    IsPHyperelementary p G := by
  refine ⟨C, hC, h₁, h₂, fun g => ?_⟩
  obtain ⟨k, hk⟩ := h₃ (g : G ⧸ C)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  exact ⟨k, hk⟩

/-- `G` is `p`-hyperelementary exactly when it has a cyclic normal subgroup `C` of order prime to
`p` with `IsPGroup p (G ⧸ C)`. This is the quotient form of the definition, with the normality
witness packaged so that it supplies the group structure on `G ⧸ C`. -/
theorem isPHyperelementary_iff_isPGroup_quotient : IsPHyperelementary p G ↔
    ∃ (C : Subgroup G) (hC : C.Normal),
      IsCyclic C ∧ ¬ p ∣ Nat.card C ∧ (letI := hC; IsPGroup p (G ⧸ C)) := by
  constructor
  · rintro ⟨C, hC, h₁, h₂, h₃⟩
    letI := hC
    exact ⟨C, hC, h₁, h₂, isPGroup_quotient_of_forall_exists_pow_mem h₃⟩
  · rintro ⟨C, hC, h₁, h₂, h₃⟩
    letI := hC
    exact isPHyperelementary_of_isPGroup_quotient C h₁ h₂ h₃

/-! ### Elementary groups are hyperelementary -/

/-- In a `p`-elementary decomposition the cyclic factor is normal: every element of `G` is a
product of an element of `C` with an element of `P`, and conjugation by the latter is trivial on
`C` because the two factors commute. -/
theorem normal_of_commute_of_isComplement' {C P : Subgroup G}
    (hcomm : ∀ c ∈ C, ∀ x ∈ P, Commute c x) (hcompl : C.IsComplement' P) : C.Normal := by
  constructor
  intro c hc g
  obtain ⟨⟨a, b⟩, rfl⟩ := hcompl.2 g
  have hb : (b : G) * c * (b : G)⁻¹ = c := by
    rw [(hcomm c hc b b.2).symm.eq, mul_inv_cancel_right]
  have heq : (a : G) * (b : G) * c * ((a : G) * (b : G))⁻¹ = (a : G) * c * (a : G)⁻¹ :=
    calc (a : G) * (b : G) * c * ((a : G) * (b : G))⁻¹
        = (a : G) * ((b : G) * c * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (a : G) * c * (a : G)⁻¹ := by rw [hb]
  rw [heq]
  exact C.mul_mem (C.mul_mem a.2 hc) (C.inv_mem a.2)

/-- A `p`-elementary group is `p`-hyperelementary: the cyclic factor is normal, and the quotient by
it is the `p`-group factor. -/
theorem IsPElementary.isPHyperelementary (h : IsPElementary p G) : IsPHyperelementary p G := by
  obtain ⟨C, P, hC, hCp, hP, hcomm, hcompl⟩ := h
  refine ⟨C, normal_of_commute_of_isComplement' hcomm hcompl, hC, hCp, fun g => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := hcompl.2 g
  obtain ⟨k, hk⟩ := hP b
  refine ⟨k, ?_⟩
  have hk' : (b : G) ^ p ^ k = 1 := by exact_mod_cast congrArg Subtype.val hk
  rw [(hcomm a a.2 b b.2).mul_pow, hk', mul_one]
  exact pow_mem a.2 _

/-- An elementary group is hyperelementary. -/
theorem IsElementary.isHyperelementary (h : IsElementary G) : IsHyperelementary G :=
  h.imp fun _ hq => ⟨hq.1, hq.2.isPHyperelementary⟩

/-! ### Basic examples -/

/-- A `p`-group is `p`-elementary, with trivial cyclic factor. -/
theorem isPElementary_of_isPGroup (hp : p ≠ 1) (h : IsPGroup p G) : IsPElementary p G := by
  refine ⟨⊥, ⊤, inferInstance, ?_, h.of_equiv topEquiv.symm, ?_, ?_⟩
  · simpa using hp
  · rintro c hc x -
    rw [mem_bot] at hc
    simp [hc]
  · exact isComplement'_bot_left.mpr rfl

/-- A finite cyclic group is `p`-elementary for **every** prime `p`: writing `Nat.card G` as
`p ^ a * m` with `p ∤ m` and taking a generator `g`, the subgroup generated by `g ^ (p ^ a)` is
cyclic of order `m` and the subgroup generated by `g ^ m` is a `p`-group of order `p ^ a`, and the
two are complementary because their orders are coprime.

So the elementary subgroups of a finite group include all its cyclic subgroups: Brauer's induction
theorem, indexed by elementary subgroups, refines Artin's, indexed by cyclic ones. -/
theorem isPElementary_of_isCyclic [Finite G] [IsCyclic G] (p : ℕ) [Fact p.Prime] :
    IsPElementary p G := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hq0 : ordProj[p] (Nat.card G) ≠ 0 := (Nat.ordProj_pos _ p).ne'
  have hm0 : ordCompl[p] (Nat.card G) ≠ 0 := (Nat.ordCompl_pos p hN0).ne'
  have hqm : ordProj[p] (Nat.card G) * ordCompl[p] (Nat.card G) = Nat.card G :=
    Nat.ordProj_mul_ordCompl_eq_self _ p
  have hmp : ¬ p ∣ ordCompl[p] (Nat.card G) :=
    Nat.not_dvd_ordCompl (Fact.out : p.Prime) hN0
  -- the `p'`-part and the `p`-part of `G`, as subgroups generated by powers of the generator
  have hcard : Nat.card (zpowers (g ^ ordProj[p] (Nat.card G))) = ordCompl[p] (Nat.card G) := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hq0 (hord ▸ Nat.ordProj_dvd _ p), hord]
  have hcard' : Nat.card (zpowers (g ^ ordCompl[p] (Nat.card G))) = ordProj[p] (Nat.card G) := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hm0 (hord ▸ Nat.ordCompl_dvd _ p), hord]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) hqm.symm
  have hcop : Nat.Coprime (ordCompl[p] (Nat.card G)) (ordProj[p] (Nat.card G)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hmp).symm
  have hpow : IsPGroup p (zpowers (g ^ ordCompl[p] (Nat.card G))) :=
    IsPGroup.of_card_dvd_pow (n := (Nat.card G).factorization p) (by rw [hcard'])
  refine ⟨zpowers (g ^ ordProj[p] (Nat.card G)), zpowers (g ^ ordCompl[p] (Nat.card G)),
    inferInstance, by rw [hcard]; exact hmp, hpow, fun c _ x _ => mul_comm' c x, ?_⟩
  exact isComplement'_of_coprime (by rw [hcard, hcard', mul_comm]; exact hqm)
    (by rw [hcard, hcard']; exact hcop)

/-- A finite cyclic group is elementary. -/
theorem isElementary_of_isCyclic [Finite G] [IsCyclic G] : IsElementary G :=
  ⟨2, Nat.prime_two, isPElementary_of_isCyclic 2⟩

/-- A finite cyclic group is hyperelementary. -/
theorem isHyperelementary_of_isCyclic [Finite G] [IsCyclic G] : IsHyperelementary G :=
  isElementary_of_isCyclic.isHyperelementary

/-! ### Closure under subgroups -/

/-- The comparison map from the preimage of a subgroup to that subgroup is injective as soon as the
underlying homomorphism is. Companion to Mathlib's
`MonoidHom.subgroupComap_surjective_of_surjective`. -/
theorem MonoidHom.subgroupComap_injective_of_injective {f : H →* G} (hf : Function.Injective f)
    (K : Subgroup G) : Function.Injective (f.subgroupComap K) :=
  fun _ _ hxy => Subtype.ext (hf (congrArg Subtype.val hxy))

/-- `p`-hyperelementarity passes to subgroups, in the form of an injective homomorphism into the
group. -/
theorem IsPHyperelementary.of_injective (h : IsPHyperelementary p G) (f : H →* G)
    (hf : Function.Injective f) : IsPHyperelementary p H := by
  obtain ⟨C, hCnormal, hCcyclic, hCp, hquot⟩ := h
  haveI := hCcyclic
  refine ⟨C.comap f, hCnormal.comap f,
    isCyclic_of_injective _ (MonoidHom.subgroupComap_injective_of_injective hf C),
    fun hdvd => hCp (hdvd.trans (Subgroup.card_comap_dvd_of_injective C f hf)), fun y => ?_⟩
  obtain ⟨k, hk⟩ := hquot (f y)
  exact ⟨k, mem_comap.mpr (by rwa [map_pow])⟩

/-- `p`-elementarity passes to subgroups, in the form of an injective homomorphism into the group.

The decomposition of a subgroup is inherited factor by factor: the crux is that the subgroup is
still the product of the two intersections, which follows from a Bézout identity between the orders
of the two factors, coprime because one is prime to `p` and the other is a power of `p`. -/
theorem IsPElementary.of_injective [Fact p.Prime] (h : IsPElementary p G) (f : H →* G)
    (hf : Function.Injective f) : IsPElementary p H := by
  obtain ⟨C, P, hC, hCp, hP, hcomm, hcompl⟩ := h
  haveI := hC
  set m := Nat.card C
  -- the two factors of a preimage, and the Bézout identity between their orders; the exponent
  -- killing the `p`-part is the one `hP` supplies for that element, so `P` need not be finite
  have key : ∀ y : H, ∃ c ∈ C.comap f, ∃ x ∈ P.comap f, c * x = y := by
    intro y
    obtain ⟨⟨a, b⟩, hab⟩ := hcompl.2 (f y)
    obtain ⟨k, hk⟩ := hP b
    set n := p ^ k
    have hcop : Nat.Coprime n m :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hCp)
    have ha : (a : G) ^ m = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by simpa using orderOf_dvd_natCard a)
    have hb : (b : G) ^ n = 1 := by exact_mod_cast congrArg Subtype.val hk
    have hyn : f (y ^ n) ∈ C := by
      rw [map_pow, ← hab, (hcomm a a.2 b b.2).mul_pow, hb, mul_one]
      exact pow_mem a.2 _
    have hym : f (y ^ m) ∈ P := by
      rw [map_pow, ← hab, (hcomm a a.2 b b.2).mul_pow, ha, one_mul]
      exact pow_mem b.2 _
    have hbez : ((1 : ℕ) : ℤ) = (n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m := by
      rw [← hcop]; exact Nat.gcd_eq_gcd_ab n m
    refine ⟨(y ^ n) ^ Nat.gcdA n m, zpow_mem (mem_comap.mpr hyn) _,
      (y ^ m) ^ Nat.gcdB n m, zpow_mem (mem_comap.mpr hym) _, ?_⟩
    rw [← zpow_natCast y n, ← zpow_natCast y m, ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hbez, Nat.cast_one, zpow_one]
  refine ⟨C.comap f, P.comap f,
    isCyclic_of_injective _ (MonoidHom.subgroupComap_injective_of_injective hf C),
    fun hdvd => hCp (hdvd.trans (Subgroup.card_comap_dvd_of_injective C f hf)),
    hP.of_injective _ (MonoidHom.subgroupComap_injective_of_injective hf P), ?_, ?_⟩
  · intro c hc x hx
    refine hf ?_
    rw [map_mul, map_mul]
    exact hcomm _ (mem_comap.mp hc) _ (mem_comap.mp hx)
  · refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_def]
      intro y hy₁ hy₂
      have : f y = 1 :=
        disjoint_def.mp hcompl.disjoint (mem_comap.mp hy₁) (mem_comap.mp hy₂)
      exact hf (this.trans (map_one f).symm)
    · refine Set.eq_univ_iff_forall.mpr fun y => ?_
      obtain ⟨c, hc, x, hx, hcx⟩ := key y
      exact Set.mem_mul.mpr ⟨c, hc, x, hx, hcx⟩

/-- `p`-hyperelementarity passes to subgroups. -/
theorem IsPHyperelementary.subgroup (h : IsPHyperelementary p G) (K : Subgroup G) :
    IsPHyperelementary p K :=
  h.of_injective K.subtype K.subtype_injective

/-- `p`-elementarity passes to subgroups. -/
theorem IsPElementary.subgroup [Fact p.Prime] (h : IsPElementary p G)
    (K : Subgroup G) : IsPElementary p K :=
  h.of_injective K.subtype K.subtype_injective

/-- Hyperelementarity passes to subgroups. -/
theorem IsHyperelementary.subgroup (h : IsHyperelementary G) (K : Subgroup G) :
    IsHyperelementary K :=
  h.imp fun _ hq => ⟨hq.1, hq.2.subgroup K⟩

/-- Elementarity passes to subgroups. -/
theorem IsElementary.subgroup (h : IsElementary G) (K : Subgroup G) :
    IsElementary K := by
  obtain ⟨q, hq, hqG⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  exact ⟨q, hq, hqG.subgroup K⟩

/-! ### Solvability -/

/-- A finite `p`-hyperelementary group is solvable: the cyclic normal subgroup `C` supplied by the
definition is abelian, hence solvable, and the quotient `G ⧸ C` is a `p`-group, hence nilpotent and
so solvable too. -/
theorem IsPHyperelementary.isSolvable [Finite G] [Fact p.Prime] (h : IsPHyperelementary p G) :
    Group.IsSolvable G := by
  obtain ⟨C, hCnormal, hCcyclic, -, hquot⟩ := h
  haveI := hCnormal
  haveI := hCcyclic
  haveI : Group.IsSolvable C := Group.isSolvable_of_comm fun a b => mul_comm' a b
  haveI : Group.IsNilpotent (G ⧸ C) :=
    IsPGroup.isNilpotent (isPGroup_quotient_of_forall_exists_pow_mem hquot)
  exact (Group.isSolvable_iff_subgroup_quotient C).mpr ⟨inferInstance, inferInstance⟩

/-- A finite hyperelementary group is solvable. -/
theorem IsHyperelementary.isSolvable [Finite G] (h : IsHyperelementary G) :
    Group.IsSolvable G := by
  obtain ⟨q, hq, hqG⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  exact hqG.isSolvable

/-- A finite elementary group is solvable. -/
theorem IsElementary.isSolvable [Finite G] (h : IsElementary G) : Group.IsSolvable G :=
  h.isHyperelementary.isSolvable

/-- The symmetric group on five letters is not hyperelementary, since it is not solvable. Together
with `TauCeti.isElementary_of_isCyclic` this pins the two predicates between the cyclic groups and
the solvable ones. -/
theorem not_isHyperelementary_perm_fin_five : ¬ IsHyperelementary (Equiv.Perm (Fin 5)) :=
  fun h => Equiv.Perm.not_isSolvable_fin_5 h.isSolvable

/-- The symmetric group on five letters is not elementary. -/
theorem not_isElementary_perm_fin_five : ¬ IsElementary (Equiv.Perm (Fin 5)) :=
  fun h => not_isHyperelementary_perm_fin_five h.isHyperelementary

end TauCeti
