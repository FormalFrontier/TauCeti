/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators

/-!
# The bad-prime operator `U_p`

For a prime `p` dividing the level `N`, the classical operator often denoted `U_p` is not a
second Hecke operator: it is the bad-prime specialization of the uniform operator `T_p`. This
file introduces `heckeUNat` and `heckeUCuspNat` as aliases of `heckeTNat` and
`heckeTCuspNat`, with the hypotheses `p.Prime` and `p ∣ N` making the bad-prime convention
explicit in their types.

The theorem `heckeUNat_eq_heckeTNat` records the normalization promised by the ModularForms
roadmap. All operational properties of `U_p` are inherited directly from the existing `T_p`
API through this equality.

## Main definitions

* `HeckeRing.GL2.heckeUNat`: the bad-prime alias of `T_p` on modular forms.
* `HeckeRing.GL2.heckeUCuspNat`: the corresponding alias on cusp forms.

## Main results

* `HeckeRing.GL2.heckeUNat_eq_heckeTNat` and
  `HeckeRing.GL2.heckeUCuspNat_eq_heckeTCuspNat`: **`U_p = T_p`**.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Propositions 5.2.1--5.2.2 and equations (5.3)--(5.4).
* T. Miyake, *Modular forms*, §4.5, Lemma 4.5.7.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.12.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (k : ℤ)

/-- **The bad-prime operator `U_p` on `M_k(Γ₁(N))`.** For a prime `p ∣ N`, this is an alias
of the uniform Hecke operator `T_p`, not an independently defined operator. -/
noncomputable abbrev heckeUNat (p : ℕ) (hp : p.Prime) (_hpN : p ∣ N) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeTNat (N := N) k p (_hn := ⟨hp.ne_zero⟩)

/-- **The bad-prime operator `U_p` on `S_k(Γ₁(N))`.** It is the cusp-form alias of the
uniform operator `T_p`. -/
noncomputable abbrev heckeUCuspNat (p : ℕ) (hp : p.Prime) (_hpN : p ∣ N) :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeTCuspNat (N := N) k p (_hn := ⟨hp.ne_zero⟩)

/-- **At a prime dividing the level, `U_p = T_p` on modular forms.** -/
theorem heckeUNat_eq_heckeTNat (hp : p.Prime) (hpN : p ∣ N) :
    heckeUNat (N := N) k p hp hpN =
      heckeTNat (N := N) k p (_hn := ⟨hp.ne_zero⟩) :=
  (rfl)

/-- **At a prime dividing the level, `U_p = T_p` on cusp forms.** -/
theorem heckeUCuspNat_eq_heckeTCuspNat (hp : p.Prime) (hpN : p ∣ N) :
    heckeUCuspNat (N := N) k p hp hpN =
      heckeTCuspNat (N := N) k p (_hn := ⟨hp.ne_zero⟩) :=
  (rfl)

end HeckeRing.GL2

end
