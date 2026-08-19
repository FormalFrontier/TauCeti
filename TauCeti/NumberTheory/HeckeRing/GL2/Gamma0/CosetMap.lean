/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset

/-!
# Comparing the `Γ₀(N)` and level-one double cosets

**Shimura, Propositions 3.30 and 3.31.** Since `Γ₀(N) ≤ SL₂(ℤ)` and `Δ₀(N) ≤ Δ`, sending
`Γ₀(N) α Γ₀(N)` to `SL₂(ℤ) α SL₂(ℤ)` is well defined on double cosets:

```lean
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)
```

and it is **injective on the cosets whose determinant is coprime to the level**
(`toLevelOneCoset_injOn`). Injectivity is the content: two `Γ₀(N)`-double cosets
with the same level-one double coset are recovered from it by intersecting with `Δ₀(N)`, which
is exactly `doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image`.

This is the injectivity step towards a later good-prime comparison of `R(Γ₀(N), Δ₀(N))` with
the level-one Hecke ring. Neither surjectivity nor compatibility with the Hecke-ring operations
is proved here: this file compares the two *coset types* only.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), the `cosetMap`
and `shimura_prop_3_31` section. The bespoke `Delta0_inclusion` there is `Submonoid.inclusion`
here, and AINTLIB's `HeckePair` bundle is Mathlib's `HeckeCoset`.

## Main definitions

* `HeckeRing.GL2.CoprimeDetCoset`: the same condition on a `Γ₀(N)`-double coset — well defined
  because the coefficients have determinant one, so the determinant is constant on a coset.
* `HeckeRing.GL2.toLevelOneCoset`: the map `Γ₀(N) α Γ₀(N) ↦ SL₂(ℤ) α SL₂(ℤ)`, the `Γ₀`
  specialisation of `HeckeCoset.map`.

## Main results

* `HeckeRing.GL2.toLevelOneCoset_mk`, `HeckeRing.GL2.coprimeDetCoset_mk`: the computation rules
  on a representative.
* `HeckeRing.GL2.toLevelOneCoset_injOn`: **Shimura, Proposition 3.31** — `toLevelOneCoset` is
  injective on the set of coprime-determinant double cosets.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.30 and 3.31.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **Shimura, Proposition 3.30.** Passing from a `Γ₀(N)`-double coset to the level-one double
coset of the same element, as the `HeckeCoset.map` of the three inclusions `Δ₀(N) ≤ Δ`,
`Γ₀(N) ≤ SL₂(ℤ)` (twice). -/
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
  HeckeCoset.map (Delta0_le_posDetInt N) (Gamma0Image_le_SLnZ N) (Gamma0Image_le_SLnZ N)

/-- The computation rule for `toLevelOneCoset`: it keeps the representative and forgets the
level. -/
@[simp] lemma toLevelOneCoset_mk (g : Delta0 N) :
    toLevelOneCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) g) =
      HeckeCoset.mk (SLnZ 2) (SLnZ 2) (Submonoid.inclusion (Delta0_le_posDetInt N) g) :=
  HeckeCoset.map_mk _ _ _ g

/-- The integral matrices of two elements of one `Γ₀(N)`-double coset have equal determinant:
`Γ₀(N) ≤ SL₂(ℤ)`, and the determinant is constant on an `SL₂(ℤ)`-double coset. -/
private lemma intMatrix_det_eq_of_mem_doubleCoset {a b : GL (Fin 2) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a (Gamma0Image N) (Gamma0Image N))
    {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (↑a : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (↑b : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ)) : B.det = A.det := by
  have hdet := det_eq_of_mem_doubleCoset_of_le_SLnZ 2 (Gamma0Image_le_SLnZ N)
    (Gamma0Image_le_SLnZ N) hb
  have hcast : ((B.det : ℤ) : ℚ) = ((A.det : ℤ) : ℚ) := by
    rw [Int.cast_det B, Int.cast_det A, ← hB, ← hA]; exact hdet
  exact_mod_cast hcast

/-- Coprimality of the determinant to the level depends only on the double coset. -/
private lemma coprimeDet_congr {a b : Delta0 N}
    (h : HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) a =
      HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) b) :
    CoprimeDet N a ↔ CoprimeDet N b := by
  obtain ⟨Aa, hAa, -, -, -⟩ := (mem_Delta0_iff N).mp a.2
  obtain ⟨Ab, hAb, -, -, -⟩ := (mem_Delta0_iff N).mp b.2
  have hba : Ab.det = Aa.det := intMatrix_det_eq_of_mem_doubleCoset N
    (HeckeCoset.eq_iff.mp h ▸ DoubleCoset.mem_doubleCoset_self _ _ _) hAa hAb
  rw [coprimeDet_iff N hAa, coprimeDet_iff N hAb, hba]

/-- Coprimality of the determinant to the level, as a predicate on `Γ₀(N)`-double cosets. -/
def CoprimeDetCoset : HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) → Prop :=
  Quotient.lift (CoprimeDet N)
    (fun _ _ hab ↦ propext (coprimeDet_congr N (Quotient.sound hab)))

/-- `CoprimeDetCoset` is `CoprimeDet` on any representative. -/
@[simp] lemma coprimeDetCoset_mk (g : Delta0 N) :
    CoprimeDetCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) g) ↔ CoprimeDet N g :=
  Iff.rfl

/-- **Shimura, Proposition 3.31.** `toLevelOneCoset` is injective on the double cosets whose
determinant is coprime to `N`: the level-one double coset determines the `Γ₀(N)` one, because
intersecting it with `Δ₀(N)` returns the latter. -/
theorem toLevelOneCoset_injOn :
    Set.InjOn (toLevelOneCoset N) {D | CoprimeDetCoset N D} := by
  rintro D₁ hD₁ D₂ hD₂ h
  -- work with representatives, so that `toLevelOneCoset_mk` applies
  have hD₁' : CoprimeDet N D₁.rep :=
    (coprimeDetCoset_mk N D₁.rep).mp (by rwa [HeckeCoset.mk_rep])
  have hD₂' : CoprimeDet N D₂.rep :=
    (coprimeDetCoset_mk N D₂.rep).mp (by rwa [HeckeCoset.mk_rep])
  rw [← HeckeCoset.mk_rep D₁, ← HeckeCoset.mk_rep D₂] at h ⊢
  rw [toLevelOneCoset_mk, toLevelOneCoset_mk, HeckeCoset.eq_iff, Submonoid.coe_inclusion,
    Submonoid.coe_inclusion] at h
  obtain ⟨Aa, hAa, -, -, -⟩ := (mem_Delta0_iff N).mp D₁.rep.2
  obtain ⟨Ab, hAb, -, -, -⟩ := (mem_Delta0_iff N).mp D₂.rep.2
  refine HeckeCoset.eq_iff.mpr ?_
  -- each `Γ₀(N)`-double coset is its level-one one cut down to `Δ₀(N)`, and those agree
  rw [← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image N _ D₁.rep.2 Aa hAa
      ((coprimeDet_iff N hAa).mp hD₁'),
    ← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image N _ D₂.rep.2 Ab hAb
      ((coprimeDet_iff N hAb).mp hD₂'), h]

end HeckeRing.GL2
