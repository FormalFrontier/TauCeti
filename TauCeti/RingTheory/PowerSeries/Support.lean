/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Power series supported on multiples of `d`

A power series is *supported on multiples of `d`* when every coefficient at an index not
divisible by `d` vanishes. The condition is preserved by the module operations, so the series
satisfying it form a submodule, and — over a commutative ring — they are exactly what the
substitution `q ↦ q ^ d` (`PowerSeries.expand`) produces.

That last statement is an equality of submodules, proved in both directions. The inclusion the
modular-form applications actually use is the easy one, that a level-raise *is* supported; the
converse recovers the series substituted into, as `PowerSeries.mk fun n ↦ P.coeff (d * n)`, and
is what makes the description of the supported submodule complete rather than one-sided.

Nothing here mentions a modular form: the predicate is about power series over any type with a
zero, and the modular-form consequences live in
`TauCeti/NumberTheory/ModularForms/Degeneracy.lean` and
`TauCeti/NumberTheory/ModularForms/Newforms/QSupport.lean`, the latter obtaining its submodule of
cusp forms by pulling `PowerSeries.supportedOnDvdSubmodule` back along the `q`-expansion.

## Main definitions

* `PowerSeries.IsSupportedOnDvd`: the support condition on a power series.
* `PowerSeries.supportedOnDvdSubmodule`: the same condition bundled as a submodule.

## Main results

* `PowerSeries.IsSupportedOnDvd.add`, `.smul`, `.neg`, `.sub`: the condition is preserved by the
  module operations, and `.one`, `.mul` by the ring ones.
* `PowerSeries.isSupportedOnDvd_expand`: the substitution `q ↦ q ^ d` lands in the supported
  series. This is the direction the modular-form applications use, so every `q ↦ q ^ d`
  statement about a `q`-expansion reduces to it.
* `PowerSeries.IsSupportedOnDvd.exists_expand` and
  `PowerSeries.isSupportedOnDvd_iff_exists_expand`: the converse and the resulting
  characterisation — a series is supported on multiples of `d` exactly when it is a `q ↦ q ^ d`
  substitution.
* `PowerSeries.range_expand_eq_supportedOnDvdSubmodule`: the same characterisation in submodule
  form, an equality rather than a containment.

## Typeclass assumptions

Each declaration assumes only what its own operation needs, which is worth recording because the
coefficient condition invites a uniform `[Semiring R]`:

* the predicate and `.zero` need only `[Zero R]`. `PowerSeries R` is `(Unit →₀ ℕ) → R`, so the
  condition is stated by evaluating that function. Going through `PowerSeries.coeff` instead — a
  bundled `R`-linear map — would force a semiring here and on every lemma below;
* `.add` needs `[AddMonoid R]` and `.neg`, `.sub` need `[AddGroup R]`: those are exactly where
  Mathlib puts `+` and `-` on `MvPowerSeries σ R`;
* `.smul` needs `[Semiring S] [AddCommMonoid R] [Module S R]`, Mathlib's only scalar action on
  power series;
* `.one` and `.mul` need `[Semiring R]`, since they are about the ring operations, and the
  `expand` lemmas need `[CommRing R]`, since `PowerSeries.expand` is an `R`-algebra homomorphism
  defined only there.

`isSupportedOnDvd_iff` restates the predicate through `coeff` for the semiring consumers, which is
how every use site spells it.

## Provenance

`IsSupportedOnDvd` and its closure lemmas `zero`, `add`, `smul`, `neg`, `sub`, `one` are adapted
from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean`. The source states them
over `ℂ`, inside its `HeckeRing.GL2.AtkinLehner` namespace; here each is stated over the weakest
coefficient structure its own operation needs — the predicate and `zero` over `[Zero R]`, `add`
over `[AddMonoid R]`, `neg` and `sub` over `[AddGroup R]`, `smul` over a module, `one` and `mul`
over `[Semiring R]` — and they are placed in the `PowerSeries` namespace under `RingTheory/`
accordingly, since nothing in them mentions a modular form. The modular-form consequences the
source draws from them are in `TauCeti/NumberTheory/ModularForms/Degeneracy.lean`.

The `expand` characterisation has no counterpart in the source, which reaches the same
conclusions by a coefficient computation at each use site.
-/

public section

namespace PowerSeries

/-! ### Pointwise evaluation

`PowerSeries R` unfolds to `(Unit →₀ ℕ) → R` and carries exactly the pointwise algebraic
structure, but it is a semireducible `def`, so Mathlib's `Pi.add_apply` and its siblings do not
match against it. The four lemmas below record that pointwise behaviour once and for all, so the
closure proofs further down are ordinary rewrites instead of restating the same definitional
equality inline at each use. They are private: a consumer with a semiring available works through
`PowerSeries.coeff`, whose `simp` lemmas cover this already. -/

private theorem apply_add {R : Type*} [AddMonoid R] (P Q : PowerSeries R) (x : Unit →₀ ℕ) :
    (P + Q) x = P x + Q x := rfl

private theorem apply_smul {R S : Type*} [Semiring S] [AddCommMonoid R] [Module S R] (c : S)
    (P : PowerSeries R) (x : Unit →₀ ℕ) : (c • P) x = c • P x := rfl

private theorem apply_neg {R : Type*} [AddGroup R] (P : PowerSeries R) (x : Unit →₀ ℕ) :
    (-P) x = -P x := rfl

private theorem apply_sub {R : Type*} [AddGroup R] (P Q : PowerSeries R) (x : Unit →₀ ℕ) :
    (P - Q) x = P x - Q x := rfl

/-- A power series is **supported on multiples of `d`** when its coefficient at every index
not divisible by `d` vanishes.

Stated by evaluating the underlying coefficient function — `PowerSeries R` is
`(Unit →₀ ℕ) → R` — rather than through `PowerSeries.coeff`, which is a bundled `R`-linear map
and would impose `[Semiring R]` on the predicate and on every closure lemma below. Only the
operation each lemma is about is then assumed: `[AddMonoid R]` for `add`, `[AddGroup R]` for
`neg` and `sub`, a semiring only where multiplication genuinely enters.
`isSupportedOnDvd_iff` is the `coeff` form, for use once there is a semiring to state it in. -/
def IsSupportedOnDvd {R : Type*} [Zero R] (d : ℕ) (P : PowerSeries R) : Prop :=
  ∀ n : ℕ, ¬ d ∣ n → P (Finsupp.single () n) = 0

/-- `IsSupportedOnDvd` in the `PowerSeries.coeff` spelling, which is how every consumer states
it. Definitionally the same condition: `coeff n` is evaluation at `Finsupp.single () n`. -/
theorem isSupportedOnDvd_iff {R : Type*} [Semiring R] {d : ℕ} {P : PowerSeries R} :
    IsSupportedOnDvd d P ↔ ∀ n : ℕ, ¬ d ∣ n → P.coeff n = 0 := (Iff.rfl)

namespace IsSupportedOnDvd

variable {R S : Type*} {d : ℕ} {P Q : PowerSeries R}

@[simp]
theorem zero [Zero R] (d : ℕ) : IsSupportedOnDvd d (0 : PowerSeries R) := fun _ _ ↦ rfl

theorem add [AddMonoid R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P + Q) := fun n hn ↦ by
  rw [apply_add, hP n hn, hQ n hn, zero_add]

theorem smul [Semiring S] [AddCommMonoid R] [Module S R] (c : S) (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (c • P) := fun n hn ↦ by
  rw [apply_smul, hP n hn, smul_zero]

theorem neg [AddGroup R] (hP : IsSupportedOnDvd d P) : IsSupportedOnDvd d (-P) := fun n hn ↦ by
  rw [apply_neg, hP n hn, neg_zero]

theorem sub [AddGroup R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P - Q) := fun n hn ↦ by
  rw [apply_sub, hP n hn, hQ n hn, sub_zero]

/-- The constant power series `1` is supported on multiples of any `d`: its only nonzero
coefficient sits at `0`, which every `d` divides. -/
@[simp]
theorem one [Semiring R] (d : ℕ) : IsSupportedOnDvd d (1 : PowerSeries R) :=
  isSupportedOnDvd_iff.2 fun n hn ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd (dvd_zero d) hn
    · simp [PowerSeries.coeff_one, hpos.ne']

/-- **The condition is closed under multiplication.** In a coefficient of `P * Q` at an index
`n` not divisible by `d`, each term `aᵢ · b_j` with `i + j = n` has one of its two factors at an
index away from the multiples of `d`: if `d ∣ i` then `d ∤ j`, since otherwise `d ∣ n`.

Both hypotheses are needed, and one-sidedness fails already over `ℕ`: `1` is supported on
multiples of `2` while `1 * X = X` is not. The coefficient semiring has to be named — over the
trivial one `X = 0`, which *is* supported. -/
theorem mul [Semiring R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P * Q) :=
  isSupportedOnDvd_iff.2 fun n hn ↦ by
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [Finset.mem_antidiagonal] at hx
    by_cases hi : d ∣ x.1
    · rw [isSupportedOnDvd_iff.1 hQ x.2 fun hj ↦ hn (hx ▸ hi.add hj), mul_zero]
    · rw [isSupportedOnDvd_iff.1 hP x.1 hi, zero_mul]

end IsSupportedOnDvd

/-- The submodule of power series supported on multiples of `d`. This is the bundled form of
`IsSupportedOnDvd`; its closure proofs are exactly the lemmas above. -/
def supportedOnDvdSubmodule (R : Type*) [Semiring R] (d : ℕ) : Submodule R (PowerSeries R) where
  carrier := {P | IsSupportedOnDvd d P}
  zero_mem' := IsSupportedOnDvd.zero d
  add_mem' hP hQ := hP.add hQ
  smul_mem' c _ hP := hP.smul c

@[simp]
theorem mem_supportedOnDvdSubmodule {R : Type*} [Semiring R] {d : ℕ} {P : PowerSeries R} :
    P ∈ supportedOnDvdSubmodule R d ↔ IsSupportedOnDvd d P := (Iff.rfl)

section Expand

variable {R : Type*} [CommRing R] {d : ℕ}

/-- **Substituting `q ↦ q ^ d` lands in the supported series.** Every coefficient of
`PowerSeries.expand d` sits at a multiple of `d`, which is the defining condition. This is the
bridge that turns a `q ↦ q ^ d` description of a series into the support condition, so the
support statements downstream never repeat the coefficient computation. -/
theorem isSupportedOnDvd_expand (hd : d ≠ 0) (P : PowerSeries R) :
    IsSupportedOnDvd d (P.expand d hd) := fun _ hn ↦ coeff_expand_of_not_dvd d hd P hn

/-- **Every supported series is a substitution `q ↦ q ^ d`**, the converse of
`PowerSeries.isSupportedOnDvd_expand`. The series substituted into is recovered by reading off
the coefficients that survive, `PowerSeries.mk fun n ↦ P.coeff (d * n)`: at an index `d * m` the
two sides agree by `PowerSeries.coeff_expand_mul`, and elsewhere both vanish — the left by
`PowerSeries.coeff_expand_of_not_dvd`, the right by hypothesis. -/
theorem IsSupportedOnDvd.exists_expand (hd : d ≠ 0) {P : PowerSeries R}
    (hP : IsSupportedOnDvd d P) : ∃ Q, expand d hd Q = P := by
  refine ⟨mk fun n ↦ P.coeff (d * n), PowerSeries.ext fun n ↦ ?_⟩
  by_cases h : d ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_expand_mul, coeff_mk]
  · rw [coeff_expand_of_not_dvd d hd _ h, isSupportedOnDvd_iff.1 hP n h]

/-- **Being supported on multiples of `d` is exactly being a substitution `q ↦ q ^ d`.** The two
directions are `PowerSeries.IsSupportedOnDvd.exists_expand` and
`PowerSeries.isSupportedOnDvd_expand`. -/
theorem isSupportedOnDvd_iff_exists_expand (hd : d ≠ 0) (P : PowerSeries R) :
    IsSupportedOnDvd d P ↔ ∃ Q, expand d hd Q = P :=
  ⟨fun hP ↦ hP.exists_expand hd, fun ⟨_, hQ⟩ ↦ hQ ▸ isSupportedOnDvd_expand hd _⟩

/-- **The range of `PowerSeries.expand d` is the supported submodule**, the bundled form of
`PowerSeries.isSupportedOnDvd_iff_exists_expand`. `expand` is an `AlgHom`, so the range is taken
of its underlying linear map. -/
theorem range_expand_eq_supportedOnDvdSubmodule (hd : d ≠ 0) :
    LinearMap.range (expand (R := R) d hd).toLinearMap = supportedOnDvdSubmodule R d :=
  SetLike.ext fun P ↦ (isSupportedOnDvd_iff_exists_expand hd P).symm

end Expand

end PowerSeries

end
