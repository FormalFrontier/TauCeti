/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# The norm on `AdjoinRoot g` is a resultant

For a monic `g : R[X]` and any `p : R[X]`, the norm of `AdjoinRoot.mk g p` over `R` is the
resultant of `g` and `p`:

`Algebra.norm R (AdjoinRoot.mk g p) = g.resultant p g.natDegree p.natDegree`.

Write `m = g.natDegree` and `k = p.natDegree`. Mathlib's Sylvester map
`S : R[X]_m × R[X]_k →ₗ R[X]_(m + k)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S` is the resultant (`Polynomial.toMatrix_sylvesterMap'`). Taking `p = 1` gives
`Ψ : (u, v) ↦ g * v + u`, which for monic `g` is a linear *equivalence* — its inverse is division
with remainder, `q ↦ (q %ₘ g, q /ₘ g)` — and `det Ψ = resultant g 1 m k = 1`.

Then `S = Ψ ∘ₗ B` for the endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_m × R[X]_k`, which is
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)`. In the block decomposition `B` is lower triangular
with diagonal blocks `mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`. Finally
`AdjoinRoot.degreeLTEquiv hg : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into
multiplication by `mk g p`, whose determinant is the norm by definition.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.

## Main results

* `Polynomial.mulModByMonic` — multiplication by `p` on `R[X]_(g.natDegree)`, the map that
  `AdjoinRoot.degreeLTEquiv` turns into multiplication by `mk g p`.
* `Polynomial.sylvesterEquivOne` — the Sylvester map of `g` and `1` is a linear equivalence,
  inverted by division with remainder.
* `Polynomial.det_sylvesterBlock` — the block-triangular `B` has the determinant of its
  upper-left block.
* `AdjoinRoot.degreeLTEquiv` — `mk g` restricted to `R[X]_(g.natDegree)` is a linear equivalence
  onto `AdjoinRoot g`, with `coe_degreeLTEquiv_symm_apply`/`_mk` characterising its inverse.
* `AdjoinRoot.norm_mk_eq_det_mulModByMonic`, `AdjoinRoot.norm_mk_eq_resultant` — the norm as a
  determinant, and then as a resultant.

## Provenance

Adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file `EllipticCurves/Mathlib/Basic.lean` lines
694-919, where the result is a Mathlib-bound prerequisite of the explicit `2`-descent. The source
targets Lean `v4.32.0` and predates parts of Mathlib's current API, so this is a forward port
rather than a copy: `degreeLTEquiv` is built from Mathlib's `AdjoinRoot.modByMonicHom` instead of
from a bijectivity argument, and the source's `Monic.resultant_one_right` is replaced by
Mathlib's `Polynomial.resultant_one_right`.
-/

public section

noncomputable section

open Module LinearMap LinearEquiv

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`. This is the map
that `AdjoinRoot.degreeLTEquiv hg` turns into multiplication by `AdjoinRoot.mk g p`. -/
def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
theorem mulModByMonic_apply_coe (hg : g.Monic) (p : R[X]) (q : degreeLT R g.natDegree) :
    (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  (rfl)

/-- For monic `g`, the Sylvester map of `g` and `1`, namely `(u, v) ↦ g * v + u`, is a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`. Its inverse is division with
remainder, `q ↦ (q %ₘ g, q /ₘ g)`. This is the general-monic analogue of Mathlib's
`Polynomial.degreeLT.addLinearEquiv`, which is the case `g = X ^ m`. -/
def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    constructor
    · intro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · intro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
theorem coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  (rfl)

theorem coe_sylvesterEquivOne_apply (hg : g.Monic) (n : ℕ)
    (w : degreeLT R g.natDegree × degreeLT R n) :
    ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X])
      = g * (w.2 : R[X]) + (w.1 : R[X]) := by
  rw [← LinearEquiv.coe_coe, coe_sylvesterEquivOne, sylvesterMap_apply_coe, one_mul]

/-- The first coordinate of the inverse of `sylvesterEquivOne` is `· %ₘ g`. -/
@[simp]
theorem coe_sylvesterEquivOne_symm_fst (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X])) = (q : R[X]) %ₘ g := by
  nontriviality R
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have h : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, coe_sylvesterEquivOne_apply, hg.modByMonic_mul_add,
    (modByMonic_eq_self_iff hg).mpr h]

/-- The second coordinate of the inverse of `sylvesterEquivOne` is `· /ₘ g`. -/
@[simp]
theorem coe_sylvesterEquivOne_symm_snd (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).2 : R[X])) = (q : R[X]) /ₘ g := by
  nontriviality R
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have h : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, coe_sylvesterEquivOne_apply, hg.divByMonic_mul_add,
    (divByMonic_eq_zero_iff hg).mpr h, add_zero]

/-- The block-triangular endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`. -/
def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

theorem sylvesterBlock_eq (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    sylvesterBlock hg p hp
      = (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp :=
  (rfl)

/-- The first coordinate of `B (u, v)` is `(p * u) %ₘ g`. -/
@[simp]
theorem coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock_eq, comp_apply, LinearEquiv.coe_coe, coe_sylvesterEquivOne_symm_fst,
    sylvesterMap_apply_coe, hg.modByMonic_mul_add]

/-- The second coordinate of `B (u, v)` is `v + (p * u) /ₘ g`. -/
@[simp]
theorem coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock_eq, comp_apply, LinearEquiv.coe_coe, coe_sylvesterEquivOne_symm_snd,
    sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in
/-- The determinant of the block-triangular map `B` is the determinant of its upper-left block. -/
theorem det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  -- the upper-left block is `mulModByMonic hg p`, and `B` fixes `{0} × R[X]_n` pointwise
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp) (Subtype.ext <| by simp)
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Polynomial

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]}

/-- For monic `g`, `AdjoinRoot.mk g` restricted to the polynomials of degree `< g.natDegree` is a
linear equivalence onto `AdjoinRoot g`. Its inverse is Mathlib's `AdjoinRoot.modByMonicHom`,
corestricted to `R[X]_(g.natDegree)`.

Not to be confused with `Polynomial.degreeLTEquiv`, which reads the same submodule off as its
coefficient vector `Fin n → R`; the namespace says which target is meant. -/
def degreeLTEquiv (hg : g.Monic) : degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  LinearEquiv.ofLinearMap ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype)
    ((modByMonicHom hg).codRestrict _ fun a ↦ by
      obtain ⟨q, rfl⟩ := mk_surjective a
      rw [modByMonicHom_mk hg]
      exact modByMonic_mem_degreeLT hg q)
    (LinearMap.ext fun a ↦ mk_leftInverse hg a)
    (LinearMap.ext fun q ↦ Subtype.ext <| by
      nontriviality R
      rw [LinearMap.comp_apply]
      -- unwrap the corestriction: the underlying polynomial is `modByMonicHom hg (mk g q)`
      change modByMonicHom hg (mk g (q : R[X])) = (q : R[X])
      rw [modByMonicHom_mk hg]
      exact (modByMonic_eq_self_iff hg).mpr ((mem_degreeLT_natDegree_iff hg.ne_zero).mp q.2))

@[simp]
theorem degreeLTEquiv_apply (hg : g.Monic) (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  (rfl)

/-- The inverse of `degreeLTEquiv` is Mathlib's `AdjoinRoot.modByMonicHom`: it picks the
representative of degree `< g.natDegree`. -/
@[simp]
theorem coe_degreeLTEquiv_symm_apply (hg : g.Monic) (a : AdjoinRoot g) :
    (((degreeLTEquiv hg).symm a : degreeLT R g.natDegree) : R[X]) = modByMonicHom hg a :=
  (rfl)

/-- The inverse of `degreeLTEquiv` sends the class of `q` to `q %ₘ g`. Deliberately not `@[simp]`:
`coe_degreeLTEquiv_symm_apply` and Mathlib's `AdjoinRoot.modByMonicHom_mk` are both simp lemmas,
so the simp set already normalises this left-hand side and tagging it too would put it out of
simp-normal form. -/
theorem coe_degreeLTEquiv_symm_mk (hg : g.Monic) (q : R[X]) :
    (((degreeLTEquiv hg).symm (mk g q) : degreeLT R g.natDegree) : R[X]) = q %ₘ g := by
  rw [coe_degreeLTEquiv_symm_apply, modByMonicHom_mk hg]

/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
theorem norm_mk_eq_det_mulModByMonic (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  nontriviality R
  rw [Algebra.norm_apply, ← LinearMap.det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine LinearMap.ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [← modByMonicHom_mk hg, mk_leftInverse hg, map_mul]

/-- **The norm on `AdjoinRoot g` is a resultant.** For monic `g`, the norm of `AdjoinRoot.mk g p`
over the base ring is the resultant of `g` and `p`. Equivalently, it is the product of the values
of `p` at the roots of `g`. -/
theorem norm_mk_eq_resultant (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  nontriviality R
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock_eq, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← LinearMap.toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← LinearMap.det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    resultant_one_right, hg.coeff_natDegree, one_pow, one_mul]

end AdjoinRoot
