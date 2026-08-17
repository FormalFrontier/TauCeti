/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.Petersson.Orthogonal

/-!
# The old and new subspaces of `S_k(Γ₁(N))`

A cusp form of level `M` produces cusp forms of level `N` for every multiple `N` of `M`: if
`d * M ∣ N` then the level-raising operator `V_d`, `(V_d f)(τ) = f(dτ)` of
`TauCeti.CuspForm.levelRaise`, carries `S_k(Γ₁(M))` into `S_k(Γ₁(N))`. The **old subspace**
`S_k(Γ₁(N))ᵒˡᵈ` is the span of all of these images with `M` a *proper* divisor of `N`, and the
**new subspace** `S_k(Γ₁(N))ⁿᵉʷ` is its Petersson-orthogonal complement.

The properness condition is imposed as `M ≠ N`, which discards exactly one pair: `d * M ∣ N`
already forces `d = 1` when `M = N`, so the only excluded operator is the identity `V₁` at the
level itself. Every other pair contributes, including `M ∣ N` proper with `d = 1`, the plain
restriction of a lower-level form (`ofLe_mem_cuspFormsOld`).

The old subspace is stable under the diamond operators, because `V_d` intertwines them:
`⟨u⟩` at level `N` acts on `V_d f` as `⟨u mod M⟩` acts on `f`
(`TauCeti.CuspForm.diamondOpCusp_levelRaise`). This is the lemma behind the fixed-nebentypus
refinement `S_k(N, χ)ⁿᵉʷ = S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)` of Layer 3 of the ModularForms roadmap,
which additionally needs the diamond operators to be Petersson-unitary and is carried out in
`TauCeti/NumberTheory/ModularForms/Newforms/Nebentypus.lean`. The stability of the new subspace
under the Hecke operators is still missing: the Hecke action on forms is Layer 2 of that
roadmap, and does not yet exist.

## Main definitions

* `TauCeti.cuspFormsOld`: the old subspace `S_k(Γ₁(N))ᵒˡᵈ`.
* `TauCeti.cuspFormsNew`: the new subspace `S_k(Γ₁(N))ⁿᵉʷ`, the Petersson-orthogonal complement
  of the old one.

## Main results

* `TauCeti.levelRaise_mem_cuspFormsOld` and `TauCeti.cuspFormsOld_le`: the introduction and
  elimination rules for the old subspace.
* `TauCeti.cuspFormsOld_le_of_prime`: the sharper elimination rule of Diamond–Shurman, in which
  only the two degeneracy maps `S_k(Γ₁(N/p)) → S_k(Γ₁(N))` at each prime `p ∣ N` are tested.
* `TauCeti.mem_cuspFormsNew_iff`: a form is new exactly when it is Petersson-orthogonal to
  every level-raised form from a proper divisor level.
* `TauCeti.disjoint_cuspFormsOld_cuspFormsNew`: the two subspaces meet only in `0`.
* `TauCeti.sup_cuspFormsOld_cuspFormsNew_eq_top`: the old and new subspaces span the full
  cusp-form space.
* `TauCeti.CuspForm.diamondOpCusp_levelRaise`: `V_d` intertwines the diamond operators, whence
  `TauCeti.diamondOpCusp_mem_cuspFormsOld`, the diamond stability of the old subspace.
* `TauCeti.cuspFormsOld_one`, `TauCeti.cuspFormsNew_one`: at level one there are no oldforms,
  so every cusp form is new.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.6.
* Miyake, *Modular forms*, Section 4.6.
* AINTLIB's [`LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean`](https://github.com/CBirkbeck/AINTLIB/blob/dev/leanmodularforms/projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean),
  by the LeanModularForms contributors, for the `cuspFormsOld` and `cuspFormsNew` API.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

open _root_.CuspForm

variable {k : ℤ}

/-! ### Level transport at a divisor -/

/-- A factor of a divisor of a nonzero number is nonzero. -/
private lemma neZero_of_mul_dvd_left {d M N : ℕ} [NeZero N] (h : d * M ∣ N) : NeZero d :=
  ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using h)⟩

/-- A factor of a divisor of a nonzero number is nonzero. -/
private lemma neZero_of_mul_dvd_right {d M N : ℕ} [NeZero N] (h : d * M ∣ N) : NeZero M :=
  ⟨fun hM ↦ NeZero.ne N (by simpa [hM] using h)⟩

/-! ### The old subspace -/

/-- The **old subspace** `S_k(Γ₁(N))ᵒˡᵈ`: the subspace of `S_k(Γ₁(N))` spanned by the images of
the level-raising operators `V_d : S_k(Γ₁(M)) → S_k(Γ₁(N))` over all pairs `(M, d)` with
`d * M ∣ N` and `M` a proper divisor of `N`. Since `d * M ∣ N` forces `d = 1` when `M = N`, the
condition `M ≠ N` removes exactly the identity operator at level `N`. -/
def cuspFormsOld (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ (M : ℕ) (d : ℕ) (h : d * M ∣ N ∧ M ≠ N),
    have : NeZero d := neZero_of_mul_dvd_left h.1
    LinearMap.range (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd h.1))

variable {M d N : ℕ}

/-- **Introduction rule for the old subspace**: every level-raise from a proper divisor level
is old. -/
theorem levelRaise_mem_cuspFormsOld [NeZero N] (h : d * M ∣ N) (hM : M ≠ N)
    (k : ℤ) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using h)⟩
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f ∈ cuspFormsOld N k :=
  let _ := neZero_of_mul_dvd_left h
  Submodule.mem_iSup_of_mem M (Submodule.mem_iSup_of_mem d
    (Submodule.mem_iSup_of_mem ⟨h, hM⟩ ⟨f, CuspForm.levelRaiseₗ_apply d _ f⟩))

/-- **Elimination rule for the old subspace**: a subspace containing every level-raise from a
proper divisor level contains the whole old subspace. -/
theorem cuspFormsOld_le [NeZero N] {V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hV : ∀ (M d : ℕ) (h : d * M ∣ N), M ≠ N →
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        haveI : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using h)⟩
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f ∈ V) :
    cuspFormsOld N k ≤ V := by
  refine iSup_le fun M ↦ iSup_le fun d ↦ iSup_le fun h ↦ ?_
  have := neZero_of_mul_dvd_left h.1
  rintro _ ⟨f, rfl⟩
  rw [CuspForm.levelRaiseₗ_apply]
  exact hV M d h.1 h.2 f

/-- The restriction to level `N` of a cusp form of proper divisor level `M` is old: it is the
level-raise `V₁`. -/
theorem ofLe_mem_cuspFormsOld [NeZero N] (h : M ∣ N) (hM : M ≠ N) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    _root_.CuspForm.ofLe (Subgroup.map_mono (Gamma1_le_Gamma1_of_dvd h)) f ∈
      cuspFormsOld N k := by
  have h1 : 1 * M ∣ N := by rwa [one_mul]
  have := levelRaise_mem_cuspFormsOld h1 hM k f
  -- At `d = 1`, level-raising is exactly restriction along the subgroup inclusion.
  have levelRaise_one_eq_ofLe :
      CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) f =
        _root_.CuspForm.ofLe (Subgroup.map_mono (Gamma1_le_Gamma1_of_dvd h)) f :=
    _root_.CuspForm.ext fun τ ↦ (CuspForm.levelRaise_one_apply _ f τ).trans
      (congrFun (_root_.CuspForm.coe_ofLe _ f) τ).symm
  rwa [levelRaise_one_eq_ofLe] at this

/-- **Level one has no oldforms**: `1` has no proper divisors. -/
@[simp]
theorem cuspFormsOld_one (k : ℤ) : cuspFormsOld 1 k = ⊥ :=
  le_bot_iff.mp <| cuspFormsOld_le fun _ d h hM _ ↦
    absurd (Nat.dvd_one.mp ((Dvd.intro_left d rfl).trans h)) hM

/-- **The old subspace is generated by the prime-level degeneracy maps.** Every level-raise
`V_d f` from a proper divisor level factors through an intermediate level `L` with `p * L = N`
for a prime `p`, the last step being `V₁` or `V_p`. So the definition above, a supremum over
all proper divisor levels, agrees with Diamond–Shurman's presentation of the old subspace by
the two degeneracy maps `S_k(Γ₁(N/p)) → S_k(Γ₁(N))` attached to each prime `p ∣ N`: a subspace
closed under those already contains every oldform.

The factorization is `V_d = V_p ∘ V_{d/p}` when a prime `p` divides `d`, and
`V₁ = V₁ ∘ V₁` through the level `N/p` for a prime `p` dividing `N/M` otherwise. -/
theorem cuspFormsOld_le_of_prime [NeZero N]
    {V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hV : ∀ (p L : ℕ), p.Prime → ∀ (hpL : p * L = N) (d : ℕ) (hd : d = 1 ∨ d = p),
      ∀ g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k,
        have hdvd : d * L ∣ N := by
          rcases hd with rfl | rfl
          · exact ⟨p, by rw [← hpL]; ring⟩
          · exact ⟨1, by rw [← hpL, mul_one]⟩
        haveI : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using hdvd)⟩
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) g ∈ V) :
    cuspFormsOld N k ≤ V := by
  refine cuspFormsOld_le fun M d hdvd hM f ↦ ?_
  rcases eq_or_ne d 1 with rfl | hd1
  · -- `V₁` from a proper divisor level `M`: split off a prime factor `p` of `N / M`
    obtain ⟨m, hm⟩ : M ∣ N := by rwa [one_mul] at hdvd
    have hm1 : m ≠ 1 := fun h ↦ hM (by rw [hm, h, mul_one])
    obtain ⟨p, hp, t, ht⟩ : ∃ p, p.Prime ∧ ∃ t, m = p * t := by
      obtain ⟨p, hp, q, hq⟩ := Nat.exists_prime_and_dvd hm1
      exact ⟨p, hp, q, hq⟩
    have hpL : p * (M * t) = N := by rw [hm, ht]; ring
    have : NeZero (M * t) := ⟨fun h ↦ NeZero.ne N (by rw [← hpL, h, mul_zero])⟩
    have h1M : 1 * M ∣ M * t := ⟨t, by rw [one_mul]⟩
    have hmem := hV p (M * t) hp hpL 1 (Or.inl rfl)
      (CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1M) f)
    simpa only [CuspForm.levelRaise_levelRaise, one_mul] using hmem
  · -- `V_d` with `d ≠ 1`: split off a prime factor `q` of `d`
    obtain ⟨q, hq, e, he⟩ : ∃ q, q.Prime ∧ ∃ e, d = q * e := by
      obtain ⟨q, hq, e, hqe⟩ := Nat.exists_prime_and_dvd hd1
      exact ⟨q, hq, e, hqe⟩
    obtain ⟨s, hs⟩ := id hdvd
    have : NeZero q := ⟨hq.ne_zero⟩
    have : NeZero e := ⟨fun h ↦ NeZero.ne N (by rw [hs, he, h]; simp)⟩
    have hqL : q * (e * M * s) = N := by rw [hs, he]; ring
    have : NeZero (e * M * s) := ⟨fun h ↦ NeZero.ne N (by rw [← hqL, h, mul_zero])⟩
    have heM : e * M ∣ e * M * s := ⟨s, rfl⟩
    have hmem := hV q (e * M * s) hq hqL q (Or.inr rfl)
      (CuspForm.levelRaise e (Gamma1_map_le_conjAct_scaleGL_of_dvd heM) f)
    have levelRaise_index : e * q = d := by rw [he, Nat.mul_comm]
    simpa only [CuspForm.levelRaise_levelRaise, levelRaise_index] using hmem

/-! ### The new subspace -/

/-- The **new subspace** `S_k(Γ₁(N))ⁿᵉʷ`: the Petersson-orthogonal complement of the old
subspace inside `S_k(Γ₁(N))`. -/
def cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  CuspForm.peterssonOrthogonal (cuspFormsOld N k)

/-- Defining equation for the sealed `cuspFormsNew`: it is the Petersson-orthogonal complement
of the old subspace. -/
lemma cuspFormsNew_def (N : ℕ) [NeZero N] (k : ℤ) :
    cuspFormsNew N k = CuspForm.peterssonOrthogonal (cuspFormsOld N k) := (rfl)

/-- **Newness is tested on the level-raises.** A cusp form of level `N` is new exactly when it
is Petersson-orthogonal to `V_d g` for every cusp form `g` of proper divisor level. -/
@[simp]
theorem mem_cuspFormsNew_iff [NeZero N] {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} :
    f ∈ cuspFormsNew N k ↔ ∀ (M d : ℕ) (h : d * M ∣ N), M ≠ N →
      ∀ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        haveI : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using h)⟩
        peterssonInnerCosets
          (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g) f = 0 := by
  rw [cuspFormsNew]
  refine ⟨fun hf M d h hM g ↦ CuspForm.mem_peterssonOrthogonal_iff.mp hf _
    (levelRaise_mem_cuspFormsOld h hM k g), fun h ↦ ?_⟩
  rw [CuspForm.mem_peterssonOrthogonal_iff_le_ker]
  refine cuspFormsOld_le fun M d hdvd hM g ↦ ?_
  rw [LinearMap.mem_ker, CuspForm.peterssonInnerCosetsₛₗ_apply_apply,
    ← peterssonInnerCosets_conj_symm, h M d hdvd hM g, map_zero]

/-- **The old and new subspaces meet only in `0`**, by positive definiteness of the Petersson
product. -/
theorem disjoint_cuspFormsOld_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    Disjoint (cuspFormsOld N k) (cuspFormsNew N k) :=
  CuspForm.peterssonOrthogonal_disjoint _

/-- **The old and new subspaces span the full cusp-form space.** -/
theorem sup_cuspFormsOld_cuspFormsNew_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    cuspFormsOld N k ⊔ cuspFormsNew N k = ⊤ := by
  rw [cuspFormsNew]
  exact CuspForm.sup_peterssonOrthogonal_eq_top _

/-- **At level one every cusp form is new**, there being no oldforms to be orthogonal to. -/
@[simp]
theorem cuspFormsNew_one (k : ℤ) : cuspFormsNew 1 k = ⊤ := by
  rw [cuspFormsNew, cuspFormsOld_one, CuspForm.peterssonOrthogonal_bot]

/-! ### Diamond stability of the old subspace -/

/-- **The old subspace is diamond-stable.** -/
theorem diamondOpCusp_mem_cuspFormsOld [NeZero N] (u : (ZMod N)ˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOld N k) :
    diamondOpCusp k u f ∈ cuspFormsOld N k := by
  refine cuspFormsOld_le (V := (cuspFormsOld N k).comap (diamondOpCusp k u)) ?_ hf
  intro M d hdvd hM g
  have := neZero_of_mul_dvd_right hdvd
  rw [Submodule.mem_comap, CuspForm.diamondOpCusp_levelRaise hdvd]
  exact levelRaise_mem_cuspFormsOld hdvd hM k _

/-- The old subspace is diamond-stable, in the `Submodule.map` form. -/
theorem cuspFormsOld_map_diamondOpCusp_le [NeZero N] (u : (ZMod N)ˣ) (k : ℤ) :
    (cuspFormsOld N k).map (diamondOpCusp k u) ≤ cuspFormsOld N k := by
  rw [Submodule.map_le_iff_le_comap]
  exact fun _ hf ↦ diamondOpCusp_mem_cuspFormsOld u hf

end TauCeti
