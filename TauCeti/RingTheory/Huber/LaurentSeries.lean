/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import TauCeti.RingTheory.Huber.Basic

/-!
# The formal Laurent series field is a Tate ring

For a field `K` the formal Laurent series `K⸨X⸩`, with the `X`-adic topology of Mathlib's
`LaurentSeries.valued` instance, are a Tate ring: the power series are an open subring, the
ideal `(X)` is a finitely generated ideal of definition, and `X` itself is a pseudouniformiser.

`K⸨X⸩` is the equal-characteristic Tate example of the roadmap's Layer-0 Examples row.

## Main definitions

* `TauCeti.Huber.LaurentSeries.idealOfDefinition`: the ideal `(X)` of `K⟦X⟧ ⊆ K⸨X⸩`.
* `TauCeti.Huber.LaurentSeries.pairOfDefinition`: the pair of definition `(K⟦X⟧, (X))`.

## Main results

* `TauCeti.Huber.LaurentSeries.mem_idealOfDefinition_pow_iff`: membership of `(X)ⁿ` is the
  valuation bound `v f ≤ exp (-n)`. `isAdic_idealOfDefinition` and
  `mem_pairOfDefinition_idealImage` are read off it; the openness of the ring of definition and
  the topological nilpotence of `X` come from Mathlib's valuation API instead.
* `TauCeti.Huber.LaurentSeries.isPseudoUniformizer_X`: `X` is a pseudouniformiser.
* `TauCeti.Huber.LaurentSeries.isHuberRing` and `TauCeti.Huber.LaurentSeries.isTateRing`.

## Implementation notes

The ring of definition is not built by hand: `LaurentSeries.val_le_one_iff_eq_coe` says that a
Laurent series has valuation at most one exactly when it is a power series, so Mathlib's
`LaurentSeries.powerSeries_as_subring` *is* the valuation subring and is open by
`Valued.isOpen_integer`.

The neighbourhood API of a `Valued` ring is phrased in the value group `ValueGroup₀ v` rather
than in `Γ₀`, so the two `private` lemmas below convert once, in each direction, between that
form and the `ℤᵐ⁰` bounds the rest of the file uses.

## Provenance

New work; the roadmap names no source for this row.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6, where Huber and Tate rings are introduced
  (Proposition and Definition 6.1) and `F⸨t⸩` is the standard equal-characteristic example of a
  Tate ring.
-/

public section

open Filter Topology WithZero PowerSeries
open scoped LaurentSeries

namespace TauCeti.Huber

namespace LaurentSeries

open _root_.LaurentSeries (powerSeries_as_subring powerSeriesEquivSubring val_le_one_iff_eq_coe
  valuation_X_pow)

variable (K : Type*) [Field K]

/-- The power series inside `K⸨X⸩` are exactly the elements of valuation at most one. -/
theorem coe_powerSeries_as_subring :
    ((powerSeries_as_subring K : Subring K⸨X⸩) : Set K⸨X⸩) = (Valued.v (R := K⸨X⸩)).integer := by
  ext f
  simp only [Valuation.mem_integer_iff, SetLike.mem_coe]
  rw [val_le_one_iff_eq_coe]
  exact ⟨by rintro ⟨g, -, rfl⟩; exact ⟨g, rfl⟩, by rintro ⟨g, rfl⟩; exact ⟨g, trivial, rfl⟩⟩

/-- The ring of definition is open, being the valuation subring. -/
theorem isOpen_powerSeries_as_subring :
    IsOpen ((powerSeries_as_subring K : Subring K⸨X⸩) : Set K⸨X⸩) :=
  (coe_powerSeries_as_subring K) ▸ Valued.isOpen_integer K⸨X⸩

/-- The power series *are* the valuation subring of `K⸨X⸩`, as subrings. -/
theorem powerSeries_as_subring_eq_integer :
    (powerSeries_as_subring K : Subring K⸨X⸩) = (Valued.v (R := K⸨X⸩)).integer :=
  SetLike.ext' (coe_powerSeries_as_subring K)

/-- The power series are the valuation integers of `K⸨X⸩`, packaged as `Valuation.Integers`.
This is Mathlib's `Valuation.integer.integers` transported along
`TauCeti.Huber.LaurentSeries.powerSeries_as_subring_eq_integer`, and is what lets the
divisibility/valuation dictionary `Valuation.Integers.dvd_iff_le` apply to `(X)ⁿ` directly. -/
theorem integers_powerSeries_as_subring :
    Valuation.Integers (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) (powerSeries_as_subring K) :=
  powerSeries_as_subring_eq_integer K ▸ Valuation.integer.integers _

/-- The variable `X`, viewed inside the ring of definition `K⟦X⟧ ⊆ K⸨X⸩`. -/
noncomputable def subringX : powerSeries_as_subring K := powerSeriesEquivSubring K PowerSeries.X

@[simp]
theorem coe_subringX : (subringX K : K⸨X⸩) = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := (rfl)

/-- The ideal of definition `(X)` of `K⟦X⟧ ⊆ K⸨X⸩`. -/
noncomputable def idealOfDefinition : Ideal (powerSeries_as_subring K) := Ideal.span {subringX K}

/-- Unfolding lemma for `TauCeti.Huber.LaurentSeries.idealOfDefinition`. -/
theorem idealOfDefinition_def : idealOfDefinition K = Ideal.span {subringX K} := (rfl)

variable {K}

/-- **The bridge to the valuation**: a power series lies in `(X)ⁿ` exactly when its valuation is
at most `exp (-n)`. -/
@[simp]
theorem mem_idealOfDefinition_pow_iff (n : ℕ) (f : powerSeries_as_subring K) :
    f ∈ idealOfDefinition K ^ n ↔ Valued.v (f : K⸨X⸩) ≤ exp (-(n : ℤ)) := by
  rw [idealOfDefinition_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (integers_powerSeries_as_subring K).dvd_iff_le]
  -- `algebraMap ↥(powerSeries_as_subring K) K⸨X⸩` is `Subtype.val`, so both sides are already
  -- the coercions; only the weight has to be evaluated.
  change Valued.v (f : K⸨X⸩) ≤ Valued.v ((subringX K : K⸨X⸩) ^ n) ↔
    Valued.v (f : K⸨X⸩) ≤ exp (-(n : ℤ))
  rw [coe_subringX, valuation_X_pow]

variable (K)

/-- The valuation ball cut out by `v (Xⁿ)` is a neighbourhood of zero. The bound is phrased with
`v (Xⁿ)` rather than `exp (-n)` so that it is visibly in the value group. -/
private theorem ball_mem_nhds (n : ℕ) :
    {x : K⸨X⸩ | Valued.v x < Valued.v (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n)} ∈ 𝓝 (0 : K⸨X⸩) := by
  refine Valued.mem_nhds_zero.mpr
    ⟨Units.mk0 (Valued.v.restrict (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n)) (by simp), ?_⟩
  exact fun _ hx ↦ Valued.v.restrict_lt_iff.mp hx

/-- Conversely every neighbourhood of zero contains a valuation ball with a bound in `ℤᵐ⁰`. -/
private theorem exists_ball_subset {s : Set K⸨X⸩} (hs : s ∈ 𝓝 (0 : K⸨X⸩)) :
    ∃ c : ℤᵐ⁰, c ≠ 0 ∧ {x : K⸨X⸩ | Valued.v x < c} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  exact ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1, by simp,
    fun x hx ↦ hγ (Valued.v.restrict_lt_iff_lt_embedding.mpr hx)⟩

/-- The subspace topology on `K⟦X⟧ ⊆ K⸨X⸩` is the `X`-adic topology. -/
theorem isAdic_idealOfDefinition : IsAdic (idealOfDefinition K) := by
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have hmem : (((idealOfDefinition K ^ n).toAddSubgroup :
        AddSubgroup (powerSeries_as_subring K)) : Set (powerSeries_as_subring K))
        ∈ 𝓝 (0 : powerSeries_as_subring K) := by
      rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero, Filter.mem_comap]
      refine ⟨_, ball_mem_nhds K n, fun f hf ↦ (mem_idealOfDefinition_pow_iff n f).mpr ?_⟩
      have hf' : Valued.v (f : K⸨X⸩)
          < Valued.v (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n) := hf
      rw [valuation_X_pow] at hf'
      exact hf'.le
    exact AddSubgroup.isOpen_of_mem_nhds _ hmem
  · rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨c, hc, hct⟩ := exists_ball_subset K ht
    refine ⟨(1 - log c).toNat, fun f hf ↦ hts (hct ?_)⟩
    refine lt_of_le_of_lt ((mem_idealOfDefinition_pow_iff _ f).mp hf) ?_
    rw [← lt_log_iff_exp_lt hc]
    omega

/-- **The pair of definition** `(K⟦X⟧, (X))` of `K⸨X⸩`. -/
noncomputable def pairOfDefinition : PairOfDefinition K⸨X⸩ where
  ringOfDefinition := powerSeries_as_subring K
  isOpen_ringOfDefinition := isOpen_powerSeries_as_subring K
  idealOfDefinition := idealOfDefinition K
  fg_idealOfDefinition := ⟨{subringX K}, by simp [idealOfDefinition_def]⟩
  isAdic_idealOfDefinition := isAdic_idealOfDefinition K

/-- The ring of definition of `TauCeti.Huber.LaurentSeries.pairOfDefinition` is the power series.

The ideal is characterised in membership form by
`TauCeti.Huber.LaurentSeries.mem_pairOfDefinition_idealOfDefinition_pow_iff`. An equation is
avoided rather than impossible: `idealOfDefinition`'s type
depends on `ringOfDefinition`, so an equation would be between two `Ideal` types that the
elaborator identifies only through that projection. -/
@[simp]
theorem pairOfDefinition_ringOfDefinition :
    (pairOfDefinition K).ringOfDefinition = powerSeries_as_subring K := (rfl)

/-- **The ideal of definition of `pairOfDefinition` is `(X)`**, in membership form.

The membership form is used because `idealOfDefinition`'s type depends on the pair's
`ringOfDefinition`; `f` is already taken in that dependent type, so nothing has to be
transported. -/
@[simp]
theorem mem_pairOfDefinition_idealOfDefinition_pow_iff {n : ℕ}
    {f : (pairOfDefinition K).ringOfDefinition} :
    f ∈ (pairOfDefinition K).idealOfDefinition ^ n ↔ Valued.v (f : K⸨X⸩) ≤ exp (-(n : ℤ)) :=
  mem_idealOfDefinition_pow_iff n f

/-- **The pair of definition is `(K⟦X⟧, (X))`**, said without touching the dependent field:
`PairOfDefinition.idealImage n` is the image of `(X)ⁿ` in `K⸨X⸩`, so it can be compared with a
valuation bound directly.

Deliberately not `@[simp]`: `PairOfDefinition.mem_idealImage` is itself a simp lemma, so simp
rewrites this left-hand side further, to an existential over the subring, and the `simpNF`
linter rejects the attribute. Rewrite with this lemma explicitly. -/
theorem mem_pairOfDefinition_idealImage (n : ℕ) (f : K⸨X⸩) :
    f ∈ (pairOfDefinition K).idealImage n ↔ Valued.v f ≤ exp (-(n : ℤ)) := by
  rw [PairOfDefinition.mem_idealImage]
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact (mem_idealOfDefinition_pow_iff n y).mp hy
  · have hle : Valued.v f ≤ 1 :=
      hf.trans (by simpa using exp_le_exp.mpr (by omega : (-(n : ℤ)) ≤ 0))
    have hmem : f ∈ powerSeries_as_subring K := by
      rw [← SetLike.mem_coe, coe_powerSeries_as_subring]
      exact hle
    exact ⟨⟨f, hmem⟩, (mem_idealOfDefinition_pow_iff n _).mpr hf, rfl⟩

/-- **`X` is a pseudouniformiser of `K⸨X⸩`**: it is a unit, since `K⸨X⸩` is a field, and
`v (Xⁿ) = exp (-n)` tends to zero. -/
theorem isPseudoUniformizer_X : IsPseudoUniformizer ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) :=
  isPseudoUniformizer_iff.mpr ⟨isUnit_iff_ne_zero.mpr
      (by simp),
    Valued.tendsto_zero_pow_of_le_exp_neg_one (by simpa using (valuation_X_pow (K := K) 1).le)⟩

/-- **`K⸨X⸩` is a Huber ring**, with `(K⟦X⟧, (X))` as a pair of definition. -/
instance isHuberRing : IsHuberRing K⸨X⸩ := ⟨⟨pairOfDefinition K⟩⟩

/-- **`K⸨X⸩` is a Tate ring**: `X` is a pseudouniformiser. -/
instance isTateRing : IsTateRing K⸨X⸩ where
  exists_isPseudoUniformizer := ⟨_, isPseudoUniformizer_X K⟩

end LaurentSeries

end TauCeti.Huber
