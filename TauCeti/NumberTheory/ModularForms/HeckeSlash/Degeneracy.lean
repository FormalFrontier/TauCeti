/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Periodic

/-!
# `Tₚ` commutes with the degeneracy operator `V_d`

The degeneracy operator `V_d : S_k(Γ₁(M)) → S_k(Γ₁(N))`, `(V_d f) τ = f (d τ)`, raises the level
along `d * M ∣ N`. This file proves that it commutes with the Hecke operator `Tₚ` at every prime
`p` coprime to `N`, the input to the statement that `Tₚ` preserves the old and new subspaces.

## The shape of the proof

`Tₚ` at a prime is `heckeSlashUpperTri k p f + (⟨p⟩ f) ∣[k] diag(p, 1)`, and `V_d` is — up to the
normalising scalar `d ^ (k - 1)` — the slash by `diag(d, 1)`. So the theorem splits into a
statement about each summand, and each is proved in the `diag(d, 1)`-slash form, where the
normalising scalars are absent:

* the upper-triangular sum, which commutes by `heckeSlashUpperTri_slash_scaleRep_comm`
  (`HeckeSlash/UpperTri/Periodic.lean`): the two slashes do **not** commute termwise, but the
  part of `d b` that leaves the range `b < p` becomes a shift `T ^ q`, which invariance under `T`
  absorbs, and coprimality of `d` and `p` makes the surviving index a permutation of `Fin p`. The
  `Γ₁(M)`-invariance of `f` supplies that hypothesis, through `slash_mapGL_T`.
* the diamond term, which commutes because natural diagonal matrices do —
  `HeckeRing.GLn.natDiagGL_comm` — once `TauCeti.CuspForm.diamondOpCusp_levelRaise` has moved
  `⟨p⟩` across `V_d`.

## Main results

* `HeckeRing.GL2.heckeTCuspNat_levelRaise`: **`Tₚ (V_d f) = V_d (Tₚ f)`** for `p` prime and
  coprime to the raised level `N`.

## Provenance

The mathematics follows `heckeT_p_all_levelRaise_comm` and its supporting lemmas in the AINTLIB
[`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project, file
`LeanModularForms/HeckeRIngs/GL2/Newforms/LevelRaiseComm.lean`, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck, lines 45–311.
No proof code is transcribed: that development works with bare coset functions `heckeT_p_ut` and
`heckeT_p_fun` and a `Γ₁`-shift matrix of its own, and splits `Tₚ` on whether `p` divides the
level, whereas here `Tₚ` is the single-formula operator of `HeckeSlash/Operators.lean`, the shift is
Mathlib's `ModularGroup.T`, and the level-raise is the general `TauCeti.CuspForm.levelRaise` of
`ModularForms/Degeneracy.lean`, stated at `d * M ∣ N` rather than at `d * M = N`.
The reindexing half of that argument (source lines 66–190) lives with the upper-triangular sum in
`HeckeSlash/UpperTri/Periodic.lean`, which carries its own note.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.6.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn TauCeti

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {M d N p : ℕ} (k : ℤ)

/-! ### The shift matrix -/

/-- A `Γ₁(M)`-invariant function is fixed by the rational slash of `T`. -/
private lemma slash_mapGL_T {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), f ∣[k] γ = f) :
    f ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) = f :=
  ModularForm.slash_eq_of_mem_map_mapGL hf
    (Subgroup.mem_map_of_mem _ (zpow_one ModularGroup.T ▸ T_zpow_mem_Gamma1 M 1))

/-! ### `Tₚ` and `V_d` -/

/-- **`Tₚ` commutes with the degeneracy operator `V_d`.** For `d * M ∣ N` and a prime `p` coprime
to `N`, raising the level of `f` and then applying `Tₚ` at level `N` agrees with applying `Tₚ` at
level `M` and then raising the level.

Coprimality is not decoration: at `p ∣ N` the diamond term of `Tₚ` vanishes at level `N` but need
not vanish at level `M`, and `b ↦ d b mod p` stops being a permutation once `p ∣ d`. -/
@[grind =]
theorem heckeTCuspNat_levelRaise (hdvd : d * M ∣ N) (hp : p.Prime)
    (hpN : Nat.Coprime p N) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero N := ⟨fun hN ↦ hp.ne_one (by simpa [hN] using hpN)⟩
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
    haveI : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeTCuspNat k p (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) (heckeTCuspNat k p f) := by
  have : NeZero N := ⟨fun hN ↦ hp.ne_one (by simpa [hN] using hpN)⟩
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hMdvd : M ∣ N := dvd_of_mul_left_dvd hdvd
  have hpM : Nat.Coprime p M := hpN.coprime_dvd_right hMdvd
  have hpd : Nat.Coprime p d := hpN.coprime_dvd_right ((dvd_mul_right d M).trans hdvd)
  have hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f :=
    fun γ hγ ↦ SlashInvariantFormClass.slash_action_eq f γ hγ
  have hunits : ZMod.unitsMap hMdvd (ZMod.unitOfCoprime p hpN) = ZMod.unitOfCoprime p hpM := by
    ext
    simp [ZMod.unitsMap_def, ZMod.coe_unitOfCoprime]
  have hscale : ∀ g : ℍ → ℂ, g ∣[k] scaleGL d = g ∣[k] (scaleRep d : GL (Fin 2) ℚ) :=
    fun g ↦ by rw [ModularForm.rat_slash, scaleRep_def, map_natDiagGL_d_one_eq_scaleGL]
  refine DFunLike.coe_injective ?_
  simp only [coe_heckeTCuspNat_prime k hp, CuspForm.coe_levelRaise,
    diamondOpCuspNat_of_coprime k hpN, diamondOpCuspNat_of_coprime k hpM,
    CuspForm.diamondOpCusp_levelRaise hdvd k (ZMod.unitOfCoprime p hpN) f, hunits,
    SlashAction.add_slash, smul_add, heckeSlashUpperTri_smul, hscale]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [heckeSlashUpperTri_slash_scaleRep_comm k p hdpos hp.pos hpd.symm (slash_mapGL_T k hf)]
  · rw [ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p), ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, scaleRep_def, scaleRep_def, natDiagGL_comm]

end HeckeRing.GL2
