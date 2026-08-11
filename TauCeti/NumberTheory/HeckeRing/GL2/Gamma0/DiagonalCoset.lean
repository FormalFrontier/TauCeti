/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# The `Γ₀(N)`-double coset of a diagonal matrix

`diag(a₁, a₂)` lies in `Δ₀(N)` as soon as `a₁` is coprime to the level — the lower-left entry
vanishes, so the only condition beyond integrality and positive determinant is that the
upper-left entry be a unit modulo `N`. That gives the `Γ₀(N)`-level
analogue `diagCosetGamma0` of `diagCoset`, and it sits over the level-one one:

```lean
toLevelOneCoset N (diagCosetGamma0 N a hgcd) = diagCoset a
```

These are the double cosets the level-`N` Hecke operators are built from — `T(a₁, a₂)` at
level `N`. The bridge identifies the *image* of the level-`N` coset under `toLevelOneCoset`
with `diagCoset a`; it says nothing about the Hecke-ring operations, and it does not by itself
supply the coprime-determinant hypothesis that `toLevelOneCoset_injOn` needs.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), the
`diagMat_mem_Delta0_of_gcd` and `T_diag_Gamma0` declarations.

## Main definitions

* `HeckeRing.GL2.diagCosetGamma0`: the `Γ₀(N)`-double coset of `diag(a)`.

## Main results

* `HeckeRing.GL2.natDiagGL_mem_Delta0_of_coprime`: `diag(a) ∈ Δ₀(N)` when `a₁` is coprime
  to `N`.
* `HeckeRing.GL2.diagCosetGamma0_toSet`: its underlying set.
* `HeckeRing.GL2.toLevelOneCoset_diagCosetGamma0`: the `Γ₀(N)`-coset of `diag(a)` lies over the
  level-one coset `T(a)`.
* `HeckeRing.GL2.diagCosetGamma0_one`: the all-ones tuple gives the identity coset.
* `HeckeRing.GL2.diagCosetGamma0_of_not_pos`: so does any tuple that is not everywhere
  positive.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- A diagonal whose upper-left entry is coprime to `N` lies in `Δ₀(N)`: the lower-left entry
is zero, so only the unit condition has content — and when positivity fails `natDiagGL` is the
identity, which is in `Δ₀(N)` anyway. Coprimality is therefore only needed in the positive
branch, and the hypothesis asks for it only there. -/
lemma natDiagGL_mem_Delta0_of_coprime (a : Fin 2 → ℕ)
    (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) :
    natDiagGL 2 a ∈ Delta0 N := by
  by_cases ha : ∀ i, 0 < a i
  case neg => rw [natDiagGL_of_not_pos (n := 2) ha]; exact one_mem _
  refine (mem_Delta0_iff N).mpr ⟨Matrix.diagonal (fun i ↦ (a i : ℤ)), ?_, ?_, ?_, ?_⟩
  · rw [natDiagGL_coe 2 a ha]
    ext i j
    simp [Matrix.diagonal, Matrix.map_apply, apply_ite (Int.cast : ℤ → ℚ)]
  · exact natDiagGL_det_pos 2 a ha
  · simp [Matrix.diagonal_apply_ne]
  · simpa [Matrix.diagonal_apply_eq] using (ZMod.isUnit_iff_coprime (a 0) N).mpr (hgcd ha)

/-- The `Γ₀(N)`-double coset of `diag(a)` when the upper-left entry is coprime to the level:
the level-`N` analogue of `diagCoset`.

Coprimality stays in the signature because it is what puts the matrix in `Δ₀(N)`, but only
under positivity: without it `natDiagGL` falls back to the identity, which lies in `Δ₀(N)`
regardless of the level. -/
noncomputable def diagCosetGamma0 (a : Fin 2 → ℕ) (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) :=
  HeckeCoset.mk _ _ ⟨natDiagGL 2 a, natDiagGL_mem_Delta0_of_coprime N a hgcd⟩

/-- Defining equation for the sealed definition `diagCosetGamma0`. -/
lemma diagCosetGamma0_def (a : Fin 2 → ℕ) (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) :
    diagCosetGamma0 N a hgcd =
      HeckeCoset.mk (Gamma0Image N) (Gamma0Image N)
        ⟨natDiagGL 2 a, natDiagGL_mem_Delta0_of_coprime N a hgcd⟩ := (rfl)

/-- The underlying set of `diagCosetGamma0 a` is the `Γ₀(N)`-double coset of `diag(a)`. -/
@[simp] lemma diagCosetGamma0_toSet (a : Fin 2 → ℕ) (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) :
    (diagCosetGamma0 N a hgcd).toSet =
      DoubleCoset.doubleCoset (natDiagGL 2 a) (Gamma0Image N) (Gamma0Image N) :=
  HeckeCoset.toSet_mk _

/-- The `Γ₀(N)`-coset of `diag(a)` lies over the level-one coset `T(a)`: widening both
coefficient subgroups from `Γ₀(N)` to `SL₂(ℤ)` along `toLevelOneCoset` gives the double coset
of the same representative, hence exactly `diagCoset a`. (The `Γ₀(N)`-coset itself is in
general strictly smaller than the level-one one.) -/
@[simp] lemma toLevelOneCoset_diagCosetGamma0 (a : Fin 2 → ℕ)
    (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) :
    toLevelOneCoset N (diagCosetGamma0 N a hgcd) = diagCoset a := by
  refine HeckeCoset.toSet_injective ?_
  rw [diagCosetGamma0_def, toLevelOneCoset_mk, HeckeCoset.toSet_mk, diagCoset_toSet,
    Submonoid.coe_inclusion]

/-- The identity normal form, mirroring `diagCoset_one`: the all-ones tuple gives the identity
double coset, whatever proof of the coprimality condition is supplied. -/
@[simp] lemma diagCosetGamma0_one (h : (∀ _ : Fin 2, 0 < (1 : ℕ)) → Nat.Coprime 1 N) :
    diagCosetGamma0 N (fun _ ↦ 1) h = 1 :=
  congrArg (HeckeCoset.mk _ _) (Subtype.ext (natDiagGL_one 2))

/-- The junk normal form, mirroring `diagCoset_of_not_pos`: a tuple that is not everywhere
positive gives the identity coset, matching the junk value of `natDiagGL`. The coprimality
condition is vacuous in this branch, so it is irrelevant which proof is supplied. -/
@[simp] lemma diagCosetGamma0_of_not_pos {a : Fin 2 → ℕ}
    (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) (ha : ¬ ∀ i, 0 < a i) :
    diagCosetGamma0 N a hgcd = 1 :=
  congrArg (HeckeCoset.mk _ _) (Subtype.ext (natDiagGL_of_not_pos (n := 2) ha))

end HeckeRing.GL2
