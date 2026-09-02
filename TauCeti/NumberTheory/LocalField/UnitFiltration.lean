/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Group.Units

/-!
# The unit filtration of a nonarchimedean local field

The multiplicative group of a nonarchimedean local field `K` carries the decreasing filtration
by the *higher unit groups*

```text
U(K, 0) = 𝒪[K]ˣ,      U(K, i) = 1 + 𝓂[K] ^ i   for i ≥ 1,
```

a family of open compact subgroups of `Kˣ` forming a neighbourhood basis of `1`. This file
defines that family and proves the properties every later layer of the local-field theory uses.

## Main definitions

* `TauCeti.IsNonarchimedeanLocalField.unitFiltration K i : Subgroup Kˣ` is `U(K, i)`, defined
  uniformly in `i` as the image in `Kˣ` of the kernel of `𝒪[K]ˣ → (𝒪[K] ⧸ 𝓂[K] ^ i)ˣ`. The
  depth-zero case is not bolted on afterwards: `𝓂[K] ^ 0 = ⊤` makes that kernel all of `𝒪[K]ˣ`.

## Main results

* `TauCeti.IsNonarchimedeanLocalField.mem_unitFiltration_iff_sub_one_mem` is the congruence form
  of membership, `x ≡ 1 mod 𝓂[K] ^ i` for a unit `x` of `𝒪[K]`, and
  `TauCeti.IsNonarchimedeanLocalField.mem_unitFiltration_iff_valuation_le` is the valuation form,
  measured against a uniformizer. The two are the shapes used downstream and are proved
  equivalent here.
* `TauCeti.IsNonarchimedeanLocalField.unitFiltration_zero` and
  `TauCeti.IsNonarchimedeanLocalField.unitFiltration_one` identify the first two steps with
  Mathlib's `ValuationSubring.unitGroup` and `ValuationSubring.principalUnitGroup`.
* `TauCeti.IsNonarchimedeanLocalField.unitFiltration_antitone` and
  `TauCeti.IsNonarchimedeanLocalField.iInf_unitFiltration`: the family decreases and separates
  points.
* `TauCeti.IsNonarchimedeanLocalField.hasBasis_nhds_one_unitFiltration`,
  `TauCeti.IsNonarchimedeanLocalField.isOpen_unitFiltration` and
  `TauCeti.IsNonarchimedeanLocalField.isCompact_unitFiltration`: the family is a neighbourhood
  basis of `1` in `Kˣ`, and each of its members is open and compact.

## Implementation notes

Indices are natural numbers throughout, as the ramification layers compare `U(K, i)` with
ramification groups through an index shift written out at each such statement.

The valuation form of membership needs a uniformizer, which is passed as an explicit argument
`hπ : Irreducible π` rather than chosen: the statements below are then independent of that
choice, and a caller that already has a uniformizer does not have to match it against an
internal one.

## References

* J.-P. Serre, *Corps Locaux*, Ch. IV, §2 (the filtration `U^{(i)}` of the units).
* J. Neukirch, *Algebraic Number Theory*, Ch. II, §3 and §5 (the higher unit groups of a local
  field, their compactness, and the neighbourhood basis they form).
-/

public section

open Filter Topology ValuativeRel

namespace TauCeti

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A nonarchimedean local field is Hausdorff: it is a valued field for the uniformity of its
additive group. This is kept private because its only role here is to feed the compactness
criteria for `Kˣ`. -/
private instance : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable (K) in
/-- The unit filtration `U(K, i)` of a nonarchimedean local field: the image in `Kˣ` of the
kernel of the reduction `𝒪[K]ˣ → (𝒪[K] ⧸ 𝓂[K] ^ i)ˣ`.

For `i ≥ 1` this is the group of units congruent to `1` modulo `𝓂[K] ^ i`, and for `i = 0` it
is `𝒪[K]ˣ`, since `𝓂[K] ^ 0 = ⊤`. -/
noncomputable def unitFiltration (i : ℕ) : Subgroup Kˣ :=
  ((Units.map (Ideal.Quotient.mk (𝓂[K] ^ i)).toMonoidHom).ker).map
    (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K))

/-- Unfolding of `unitFiltration`: its elements are the units of `𝒪[K]` congruent to `1` modulo
`𝓂[K] ^ i`, viewed in `Kˣ`. -/
theorem mem_unitFiltration_iff {i : ℕ} {x : Kˣ} :
    x ∈ unitFiltration K i ↔ ∃ u : 𝒪[K]ˣ, (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ i ∧
      Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u = x := by
  simp [unitFiltration, MonoidHom.mem_ker, Units.ext_iff, Ideal.Quotient.mk_eq_one_iff_sub_mem]

/-- Membership of `U(K, i)`, congruence form: a unit of `𝒪[K]` lies in `U(K, i)` exactly when it
is congruent to `1` modulo `𝓂[K] ^ i`. -/
theorem mem_unitFiltration_iff_sub_one_mem {i : ℕ} {u : 𝒪[K]ˣ} :
    Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u ∈ unitFiltration K i ↔
      (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ i := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_unitFiltration_iff.mpr ⟨u, h, rfl⟩⟩
  obtain ⟨w, hw, hwu⟩ := mem_unitFiltration_iff.mp h
  obtain rfl : w = u := Units.map_injective Subtype.val_injective hwu
  exact hw

/-- Membership in `𝓂[K] ^ i`, read off the valuation. This is the elementwise form of
`Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow`. -/
private theorem mem_maximalIdeal_pow_iff {π : 𝒪[K]} (hπ : Irreducible π) (i : ℕ) (y : 𝒪[K]) :
    y ∈ 𝓂[K] ^ i ↔ valuation K (y : K) ≤ valuation K (π : K) ^ i :=
  Set.ext_iff.mp (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) i) y

/-- Membership of `U(K, i)`, valuation form: `x` is a unit of `𝒪[K]` and `x - 1` has valuation at
most that of `π ^ i`, for `π` a uniformizer. The first conjunct carries the content at `i = 0`,
where the second holds for every element of `𝒪[K]`; at positive depth it is instead the second
that implies the first, see `mem_unitFiltration_succ_iff_valuation_le`. -/
theorem mem_unitFiltration_iff_valuation_le {π : 𝒪[K]} (hπ : Irreducible π) (i : ℕ) {x : Kˣ} :
    x ∈ unitFiltration K i ↔
      valuation K (x : K) = 1 ∧ valuation K ((x : K) - 1) ≤ valuation K (π : K) ^ i := by
  have key := mem_maximalIdeal_pow_iff hπ i
  rw [mem_unitFiltration_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(Valuation.integer.integers (valuation K)).valuation_unit u,
      by simpa using (key _).mp hu⟩
  · rintro ⟨hx1, hx2⟩
    refine ⟨(Valuation.integer.integers (valuation K)).isUnit_of_one'
      (x := (⟨(x : K), hx1.le⟩ : 𝒪[K])) hx1 |>.unit, ?_, by ext; simp⟩
    rw [key]
    simpa using hx2

/-- At positive depth the valuation criterion is the single inequality on `x - 1`: it already
forces `x` to be a unit of `𝒪[K]`. -/
theorem mem_unitFiltration_succ_iff_valuation_le {π : 𝒪[K]} (hπ : Irreducible π) (i : ℕ)
    {x : Kˣ} :
    x ∈ unitFiltration K (i + 1) ↔ valuation K ((x : K) - 1) ≤ valuation K (π : K) ^ (i + 1) := by
  refine (mem_unitFiltration_iff_valuation_le hπ _).trans ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hlt : valuation K ((x : K) - 1) < valuation K 1 := by
    simpa using
      h.trans_lt (pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ) i.succ_ne_zero)
  simpa using Valuation.map_eq_of_sub_lt _ hlt

/-- The depth-zero step of the filtration is the unit group of `𝒪[K]`. -/
theorem unitFiltration_zero : unitFiltration K 0 = (valuation K).valuationSubring.unitGroup := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  ext x
  rw [mem_unitFiltration_iff_valuation_le hπ, Valuation.mem_unitGroup_iff]
  simp only [pow_zero, and_iff_left_iff_imp]
  intro hx
  calc valuation K ((x : K) - 1) ≤ max (valuation K (x : K)) (valuation K 1) :=
        Valuation.map_sub _ _ _
    _ = 1 := by simp [hx]

@[simp]
theorem mem_unitFiltration_zero {x : Kˣ} : x ∈ unitFiltration K 0 ↔ valuation K (x : K) = 1 := by
  rw [unitFiltration_zero, Valuation.mem_unitGroup_iff]

/-- The depth-one step of the filtration is the principal unit group. -/
theorem unitFiltration_one :
    unitFiltration K 1 = (valuation K).valuationSubring.principalUnitGroup := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  ext x
  rw [mem_unitFiltration_succ_iff_valuation_le hπ 0,
    ValuationSubring.mem_principalUnitGroup_iff, pow_one]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (Valuation.isEquiv_valuation_valuationSubring (valuation K)).lt_one_iff_lt_one.mp
      (h.trans_lt (Valuation.integer.v_irreducible_lt_one hπ))
  · have h' : valuation K ((x : K) - 1) < 1 :=
      (Valuation.isEquiv_valuation_valuationSubring (valuation K)).lt_one_iff_lt_one.mpr h
    have hy : (⟨(x : K) - 1, h'.le⟩ : 𝒪[K]) ∈ 𝓂[K] ^ 1 := by
      rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr h'
    simpa using (mem_maximalIdeal_pow_iff hπ 1 _).mp hy

/-- The unit filtration is decreasing. -/
theorem unitFiltration_antitone : Antitone (unitFiltration (K := K)) := by
  intro i j hij x hx
  obtain ⟨u, hu, rfl⟩ := mem_unitFiltration_iff.mp hx
  exact mem_unitFiltration_iff.mpr ⟨u, Ideal.pow_le_pow_right hij hu, rfl⟩

/-- Powers of a uniformizer are cofinal at the bottom of the value group: the value group of a
local field is generated by the value of a uniformizer, so every nonzero value strictly
dominates one of its powers. -/
private theorem exists_pow_valuation_lt {π : 𝒪[K]} (hπ : Irreducible π)
    {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) : ∃ i : ℕ, valuation K (π : K) ^ i < γ := by
  have hπ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hπ0 : 0 < valuation K (π : K) := Valuation.integer.v_irreducible_pos hπ
  rcases le_or_gt 1 γ with hγ1 | hγ1
  · exact ⟨1, by simpa using hπ1.trans_le hγ1⟩
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hy0 : (⟨y, hγ1.le⟩ : 𝒪[K]) ≠ 0 := by simpa [Subtype.ext_iff] using hγ
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  refine ⟨n + 1, ?_⟩
  have hu1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
    (Valuation.integer.integers (valuation K)).valuation_unit u
  have hval : valuation K y = valuation K (π : K) ^ n := by
    have := congrArg (fun z : 𝒪[K] ↦ valuation K (z : K)) hu
    simpa [hu1] using this
  rw [hval, pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos hπ0 n) hπ1

/-- The unit filtration separates points. -/
theorem iInf_unitFiltration : ⨅ i : ℕ, unitFiltration K i = ⊥ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  simp only [Subgroup.mem_iInf] at hx
  have hle : ∀ i : ℕ, valuation K ((x : K) - 1) ≤ valuation K (π : K) ^ i :=
    fun i ↦ ((mem_unitFiltration_iff_valuation_le hπ i).mp (hx i)).2
  have hzero : valuation K ((x : K) - 1) = 0 := by
    by_contra h
    obtain ⟨i, hi⟩ := exists_pow_valuation_lt hπ h
    exact absurd (hle i) hi.not_ge
  rw [Subgroup.mem_bot, Units.ext_iff, Units.val_one]
  exact sub_eq_zero.mp ((Valuation.zero_iff _).mp hzero)

/-- The unit filtration is a neighbourhood basis of `1` in `Kˣ`. -/
theorem hasBasis_nhds_one_unitFiltration :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ : ℕ ↦ True) fun i ↦ (unitFiltration K i : Set Kˣ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hπ0 : 0 < valuation K (π : K) := Valuation.integer.v_irreducible_pos hπ
  rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.nhds_eq_comap]
  refine ((IsValuativeTopology.hasBasis_nhds (1 : K)).comap
    (Units.val : Kˣ → K)).to_hasBasis ?_ ?_
  · rintro γ -
    obtain ⟨i, hi⟩ := exists_pow_valuation_lt hπ γ.ne_zero
    exact ⟨i, trivial, fun x hx ↦
      lt_of_le_of_lt ((mem_unitFiltration_iff_valuation_le hπ i).mp hx).2 hi⟩
  · rintro i -
    refine ⟨Units.mk0 (valuation K (π : K) ^ i) (pow_ne_zero i hπ0.ne'), trivial, fun x hx ↦ ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hx
    refine (mem_unitFiltration_iff_valuation_le hπ i).mpr ⟨?_, hx.le⟩
    have h1 : valuation K ((x : K) - 1) < valuation K 1 := by
      simpa using hx.trans_le (pow_le_one₀ zero_le hπ1.le)
    simpa using Valuation.map_eq_of_sub_lt _ h1

/-- Every step of the unit filtration is open in `Kˣ`. -/
theorem isOpen_unitFiltration (i : ℕ) : IsOpen (unitFiltration K i : Set Kˣ) :=
  Subgroup.isOpen_of_mem_nhds _ (hasBasis_nhds_one_unitFiltration.mem_of_mem (i := i) trivial)

/-- Every step of the unit filtration is compact in `Kˣ`. -/
theorem isCompact_unitFiltration (i : ℕ) : IsCompact (unitFiltration K i : Set Kˣ) := by
  have hcpt : IsCompact ((𝒪[K] : Subring K) : Set K) := by
    have h : ((𝒪[K] : Subring K) : Set K) = {x : K | valuation K x ≤ 1} :=
      Set.ext fun x ↦ Valuation.mem_integer_iff _ x
    rw [h]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have hzero : (unitFiltration K 0 : Set Kˣ) = ((𝒪[K] : Subring K).toSubmonoid.units : Set Kˣ) := by
    ext x
    have hv0 : valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    simp only [SetLike.mem_coe, mem_unitFiltration_zero, Submonoid.mem_units_iff,
      Subring.mem_toSubmonoid, Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    refine ⟨fun hx ↦ by simp [hx], fun ⟨h1, h2⟩ ↦ le_antisymm h1 ?_⟩
    rwa [inv_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm hv0))] at h2
  refine IsCompact.of_isClosed_subset ?_ (Subgroup.isClosed_of_isOpen _ (isOpen_unitFiltration i))
    (by exact_mod_cast unitFiltration_antitone (Nat.zero_le i))
  rw [hzero]
  exact Submonoid.units_isCompact hcpt

end IsNonarchimedeanLocalField

end TauCeti
