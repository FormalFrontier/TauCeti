/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.ModularForm

/-!
# The normalisation lemma: the double coset of `diag(1, p)` is the classical `Uₚ`

Two Hecke operators on `M_k(Γ₁(N))` have been built independently. `HeckeSlash/Gamma1.lean`
attaches one to an **arbitrary double coset** of the Hecke triple `(Γ₁(N), Δ₀(N))`, by slashing
against representatives of the coset and summing; `UpperTri/ModularForm.lean` builds the
**classical** operator at `p ∣ N`, the sum of the slashes by `!![1, b; 0, p]` for `b < p`, and
computes its effect on `q`-expansions. Nothing so far connects them, and until something does,
"the Hecke operator" names two objects.

This file identifies them, which is the roadmap's flagged *normalisation lemma*: for `p ∣ N`,

`heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) = heckeSlashUpperTriModularFormEnd k hpN`,

and likewise on cusp forms. These `simp` lemmas provide the normalization bridge between the
abstract and explicit constructions. Nebentypus preservation and the `q`-expansion recurrence
for the canonical `heckeTNat` operator are proved at every level-supported index in
`HeckeSlash/LevelSupported.lean`.

## How the two are matched

`HeckeSlash/Independence.lean` already shows that the abstract operator is the sum of the slashes
over **any** decomposition of the double coset into right cosets
(`heckeSlashSum_coe_eq_sum_of_rightCosets`); what was missing was a decomposition to feed it. That
is `HeckeRing/GL2/Gamma1/UpperTriCosets.lean`: at `p ∣ N` the `p` cosets
`Γ₁(N) · !![1, b; 0, p]` cover `Γ₁(N) · diag(1, p) · Γ₁(N)` and are pairwise distinct. Feeding
those in turns the abstract sum into `heckeSlashUpperTri`, and the two bundled endomorphisms
then agree because both are that function on the underlying `ℍ → ℂ`.

## Why level-supportedness, and the bundled `p ∣ N` case

The condition `p.primeFactors ⊆ N.primeFactors` makes the `p` upper-triangular representatives
exhaust the coset; for `p ∤ N` and `p` prime there is one further coset and the identification
below is false as stated. No primality is needed anywhere.

The function-level statement `heckeSlashSum_diagCosetGamma1` is proved under the weaker
hypothesis the coset decomposition actually uses — every prime factor of `p` divides `N` — since
the prime powers `q ^ r` with `q ∣ N` satisfy it without dividing `N`. The two bundled operators
stay at the special case `p ∣ N`, because `heckeSlashUpperTriModularFormEnd` is only constructed
there.

Following Miyake, Diamond–Shurman and Shimura, no separate `Uₚ` is introduced — this *is* `Tₚ` at
`p ∣ N`, and the identification proved here is what lets literature stated in either vocabulary be
consumed.

## Main results

* `HeckeRing.GL2.heckeSlashSum_diagCosetGamma1`: on underlying functions, the abstract slash sum
  of `diagCosetGamma1 N p` is `heckeSlashUpperTri k p`, at any index whose prime factors all
  divide the level — `p ∣ N` is the case the bundled operators below are stated at.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diagCosetGamma1`,
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_diagCosetGamma1`: **the normalisation lemma**, on
  `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.

## Provenance

No code is transcribed. The identification is the normalisation lemma the ModularForms roadmap
asks Layer 2(b) to keep; on the AINTLIB side (`LeanModularForms`, Chris Birkbeck, Apache-2.0) the
`p ∣ N` operator is the `heckeT_p_divN` branch of `heckeT_p_all`
(`LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean`), and the statement below is what ties that
branch to the abstract double-coset ring.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.2, Proposition 5.2.1.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (k : ℤ)

/-- The prime factors of a divisor of a nonzero level are prime factors of the level: the
hypothesis the coset decomposition asks for, in the form `p ∣ N` supplies. -/
private lemma primeFactors_subset_of_dvd (hpN : p ∣ N) : p.primeFactors ⊆ N.primeFactors :=
  Nat.primeFactors_mono hpN (NeZero.ne N)

/-- **The abstract slash sum of `diag(1, p)` is the classical upper-triangular sum**, at any
index supported on the level. This is `heckeSlashSum_coe_eq_sum_of_rightCosets` fed with the
decomposition of `HeckeRing/GL2/Gamma1/UpperTriCosets.lean`; slash-invariance of `f`, the one
hypothesis that lemma needs, is carried by the form class. -/
theorem heckeSlashSum_diagCosetGamma1 (hp : 0 < p) (hpN : p.primeFactors ⊆ N.primeFactors)
    {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) :
    heckeSlashSum k (diagCosetGamma1 N p) ⇑f = heckeSlashUpperTri k p ⇑f :=
  (heckeSlashSum_coe_eq_sum_of_rightCosets k (diagCosetGamma1 N p) (upperTriRep p)
    (doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets hp hpN)
    op_upperTriRep_smul_injective f).trans (heckeSlashUpperTri_def k p ⇑f).symm

/-- **The normalisation lemma on `M_k(Γ₁(N))`.** For `p ∣ N` the Hecke operator of the double
coset `Γ₁(N) · diag(1, p) · Γ₁(N)` is the classical operator of `UpperTri/ModularForm.lean` —
the operator modern papers write `Uₚ`. -/
@[simp]
theorem heckeSlashGamma1ModularFormEnd_diagCosetGamma1 (hpN : p ∣ N) :
    heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) =
      heckeSlashUpperTriModularFormEnd k hpN :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1ModularFormEnd, coe_heckeSlashUpperTriModularFormEnd,
      heckeSlashSum_diagCosetGamma1 k (Nat.pos_of_dvd_of_pos hpN (NeZero.pos N))
        (primeFactors_subset_of_dvd hpN) f]

/-- **The normalisation lemma on `S_k(Γ₁(N))`.** -/
@[simp]
theorem heckeSlashGamma1CuspFormEnd_diagCosetGamma1 (hpN : p ∣ N) :
    heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) = heckeSlashUpperTriCuspFormEnd k hpN :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1CuspFormEnd, coe_heckeSlashUpperTriCuspFormEnd,
      heckeSlashSum_diagCosetGamma1 k (Nat.pos_of_dvd_of_pos hpN (NeZero.pos N))
        (primeFactors_subset_of_dvd hpN) f]

end HeckeRing.GL2

end
