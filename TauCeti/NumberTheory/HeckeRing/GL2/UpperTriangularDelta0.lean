/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DiagonalCoset
public import TauCeti.NumberTheory.HeckeRing.GLn.CosetDecomposition

/-!
# Upper-triangular coset representatives at level `N`

`GLn/CosetDecomposition.lean` constructs, from the bounded entry assignments
`UpperTriEntries n a`, a family `upperTriGL B = diag(a) · U(B)` of upper-triangular elements of
the double coset `SL_n(ℤ) · diag(a) · SL_n(ℤ)`, and shows that under positivity and a
divisibility chain on `a` distinct assignments give distinct left cosets. It does **not** claim
the family exhausts the left cosets, and neither does anything here. This file supplies what is
missing for level `N`: those elements lie in the semigroup `Δ₀(N)` where the Hecke pairs of
`Γ₀(N)` and `Γ₁(N)` take their elements.

The hypothesis is inherited from the diagonal case rather than invented. `upperTriGL B` factors
as `diag(a) · U(B)`, and `Δ₀(N)` is a submonoid, so it is enough that each factor lie in it. The
unipotent factor always does — everything below its diagonal vanishes, so it is in `Γ₀(N)` — and
the diagonal factor is `HeckeRing.GL2.natDiagGL_mem_Delta0_of_coprime`, which asks that `a₀` be
coprime to `N` when `a` is positive. So `B` contributes no condition at all, and that lemma is
the case `B = 0` of the one proved here.

The `T_p` application is `a = ![1, p]`, where the single component of `B` ranges over
`Fin (a₁ / a₀) = Fin p`: the `p` elements `[1, b; 0, p]` lie in `Δ₀(N)` for **every** level `N`,
since `a₀ = 1` is a unit modulo anything. `T_p` also involves the diagonal `[p, 0; 0, 1]`, which
is `natDiagGL 2 ![p, 1]` and whose membership is genuinely conditional on `p`. That the bound
`b ∈ Fin p` is carried by the type is the point of reusing this construction: the count of
upper-triangular representatives is `p`, not an unbounded family.

## Main results

* `HeckeRing.GL2.unitriSL_mem_Gamma0`: the unipotent factor `U(B)` lies in `Γ₀(N)`.
* `HeckeRing.GL2.upperTriGL_mem_Delta0_of_coprime`: `diag(a) · U(B) ∈ Δ₀(N)` when `a₀` is
  coprime to `N`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix CongruenceSubgroup

namespace HeckeRing.GL2

open HeckeRing.GLn

variable (N : ℕ)

/-- The unipotent factor `U(B)` of an upper-triangular representative lies in `Γ₀(N)`, for
every level: it is unitriangular, so its lower-left entry is `0`, which is what `Γ₀(N)` asks
for modulo `N`. The entry assignment `B` sits strictly above the diagonal and is irrelevant. -/
-- Deliberately not `@[simp]`, and the attribute is not available: every step of the proof is
-- already a simp lemma (`Gamma0_mem`, `coe_unitriSL`, `unitriMat_apply_eq_zero_of_lt`,
-- `Int.cast_zero`), so `simp` closes the goal on its own and `simpNF` rejects the attribute as
-- redundant with `simp can prove this`. The lemma is kept as the named fact to `exact`.
lemma unitriSL_mem_Gamma0 {a : Fin 2 → ℕ} (B : UpperTriEntries 2 a) :
    unitriSL B ∈ Gamma0 N :=
  Gamma0_mem.mpr <| by simp

/-- An upper-triangular coset representative `diag(a) · U(B)` lies in `Δ₀(N)` as soon as its
upper-left entry `a₀` is coprime to the level.

The two factors of `upperTriGL_def` land in `Δ₀(N)` separately. The unipotent factor does so
unconditionally, being in `Γ₀(N)`; the diagonal factor is
`natDiagGL_mem_Delta0_of_coprime`, whose hypothesis is inherited verbatim — including its
shape, since when positivity fails `natDiagGL` is the identity and no coprimality is needed.
The diagonal case `B = 0` of this lemma is that lemma. -/
lemma upperTriGL_mem_Delta0_of_coprime {a : Fin 2 → ℕ}
    (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) (B : UpperTriEntries 2 a) :
    upperTriGL B ∈ Delta0 N := by
  rw [upperTriGL_def]
  exact (Delta0 N).mul_mem (natDiagGL_mem_Delta0_of_coprime N a hgcd)
    (Gamma0Image_le_Delta0 N ((mem_Gamma0Image_iff N).mpr
      ⟨unitriSL B, unitriSL_mem_Gamma0 N B, rfl⟩))

end HeckeRing.GL2
