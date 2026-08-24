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
roadmap. The companion lemmas identify the alias with the upper-triangular slash sum, prove that
it preserves every nebentypus space, and give its Fourier-coefficient formula

`a_m(U_p f) = a_{pm}(f)`.

Thus later newform arguments may use the modern `U_p` vocabulary without introducing an
independent operator or a translation layer.

## Main definitions

* `HeckeRing.GL2.heckeUNat`: the bad-prime alias of `T_p` on modular forms.
* `HeckeRing.GL2.heckeUCuspNat`: the corresponding alias on cusp forms.

## Main results

* `HeckeRing.GL2.heckeUNat_eq_heckeTNat` and
  `HeckeRing.GL2.heckeUCuspNat_eq_heckeTCuspNat`: **`U_p = T_p`**.
* `HeckeRing.GL2.heckeUNat_eq_upperTri` and
  `HeckeRing.GL2.heckeUCuspNat_eq_upperTri`: the upper-triangular slash-sum description.
* `HeckeRing.GL2.heckeUNat_mem_modFormCharSpace` and
  `HeckeRing.GL2.heckeUCuspNat_mem_cuspFormCharSpace`: preservation of nebentypus.
* `HeckeRing.GL2.qExpansion_coeff_heckeUNat` and
  `HeckeRing.GL2.qExpansion_coeff_heckeUCuspNat`: the bad-prime coefficient formula.

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

/-- At a bad prime, `U_p` is the upper-triangular slash-sum operator. -/
theorem heckeUNat_eq_upperTri (hp : p.Prime) (hpN : p ∣ N) :
    heckeUNat (N := N) k p hp hpN = heckeSlashUpperTriModularFormEnd k hpN := by
  rw [heckeUNat_eq_heckeTNat, heckeTNat_eq_upperTri]

/-- At a bad prime, the cusp-form `U_p` is the upper-triangular slash-sum operator. -/
theorem heckeUCuspNat_eq_upperTri (hp : p.Prime) (hpN : p ∣ N) :
    heckeUCuspNat (N := N) k p hp hpN = heckeSlashUpperTriCuspFormEnd k hpN := by
  rw [heckeUCuspNat_eq_heckeTCuspNat, heckeTCuspNat_eq_upperTri]

/-- **The bad-prime operator preserves nebentypus:** `U_p` maps `M_k(N, χ)` into itself. -/
theorem heckeUNat_mem_modFormCharSpace (hp : p.Prime) (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeUNat (N := N) k p hp hpN f ∈ modFormCharSpace k χ := by
  rw [heckeUNat_eq_upperTri]
  exact heckeSlashUpperTriModularFormEnd_mem_modFormCharSpace k hpN χ hf

/-- **The bad-prime operator preserves nebentypus on cusp forms:** `U_p` maps
`S_k(N, χ)` into itself. -/
theorem heckeUCuspNat_mem_cuspFormCharSpace (hp : p.Prime) (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    heckeUCuspNat (N := N) k p hp hpN f ∈ cuspFormCharSpace k χ := by
  rw [heckeUCuspNat_eq_upperTri]
  exact heckeSlashUpperTriCuspFormEnd_mem_cuspFormCharSpace k hpN χ hf

/-- **The Fourier-coefficient formula for `U_p`:** at a prime dividing the level,
`a_m(U_p f) = a_{pm}(f)`. -/
theorem qExpansion_coeff_heckeUNat (hp : p.Prime) (hpN : p ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeUNat (N := N) k p hp hpN f)).coeff m =
      (qExpansion 1 f).coeff (p * m) := by
  rw [heckeUNat_eq_upperTri]
  exact qExpansion_coeff_heckeSlashUpperTriModularFormEnd k hpN f m

/-- **The Fourier-coefficient formula for `U_p` on cusp forms:**
`a_m(U_p f) = a_{pm}(f)`. -/
theorem qExpansion_coeff_heckeUCuspNat (hp : p.Prime) (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeUCuspNat (N := N) k p hp hpN f)).coeff m =
      (qExpansion 1 f).coeff (p * m) := by
  rw [heckeUCuspNat_eq_upperTri]
  exact qExpansion_coeff_heckeSlashUpperTriCuspFormEnd k hpN f m

end HeckeRing.GL2

end
