/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.Analysis.Polynomial.SymmetricPower
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Polynomial maps on the symmetric-power chart at colliding tuples

The elementary symmetric chart `TauCeti.Sym.coeffEquiv` presents the `n`-th symmetric power of an
algebraically closed field as the affine space `Fin n → 𝕜` of lower coefficients. Postcomposing
the points of a tuple with a map `φ : 𝕜 → 𝕜` induces a map on the chart, and at a tuple whose
points are pairwise distinct that map is analytic whenever `φ` is
(`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm`), by parametrizing the roots one by one
with the implicit function theorem. At a tuple where points collide that parametrization breaks
down, and this file settles the case that remains accessible by algebra: the map induced by a
univariate polynomial `q`. Its coordinate representation is then not merely analytic but
*polynomial* in the chart coordinates, at every tuple, colliding or not.

The mechanism is the fundamental theorem of symmetric polynomials. Substituting `q` into every
variable of the `(k + 1)`-st elementary symmetric polynomial using `MvPolynomial.bind₁` preserves
symmetry, so by Mathlib's fundamental theorem
(`MvPolynomial.esymmAlgHom_fin_bijective`) it is the substitution of the elementary symmetric
polynomials into a polynomial `W k`. Evaluating at a tuple `v` turns the left side into the
`(k+1)`-st elementary symmetric function of the `q`-images of the points of `v`
(`MvPolynomial.aeval_esymm_eq_multiset_esymm`), and translating the elementary symmetric
functions of `v` into chart coordinates is Vieta's formula (`Multiset.prod_X_sub_C_coeff`).
Reading the fundamental-theorem polynomials in the chart coordinates gives polynomials `Q` with
`coeffEquiv 𝕜 n (Sym.map (fun z => eval z q) ((coeffEquiv 𝕜 n).symm c)) i = eval c (Q i)`
for every coefficient tuple `c` (`TauCeti.Sym.exists_coeffEquiv_map_coeffEquiv_symm_eq_eval`),
whence analyticity everywhere
(`TauCeti.Sym.analyticOnNhd_coeffEquiv_map_coeffEquiv_symm_polynomial`).

Lane F4.1 of the analytic Heegaard Floer roadmap opens with "`Sym^g(Σ)` geometry: smooth complex
structure (elementary symmetric functions)", after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). The transition maps of the
elementary-symmetric atlas on `Sym^g(Σ)` are read in the holomorphic coordinates of the surface:
the multiplicity-free case of their analyticity is
`TauCeti/Analysis/Polynomial/SimpleRoots/Basic.lean`, its blockwise assembly across the disjoint
coordinate patches of a chart is `TauCeti/Analysis/Polynomial/SimpleRoots/Family.lean`, and this
file removes the distinctness hypothesis when the induced map is polynomial. For a general
holomorphic coordinate change an analytic approximation argument on top of the polynomial case is
still needed before the atlas can be packaged as a complex manifold.

## Main declarations

* `TauCeti.Sym.exists_coeffEquiv_map_coeffEquiv_symm_eq_eval`: the coordinate action of a
  polynomial map is polynomial in the chart coordinates, at every tuple.
* `TauCeti.Sym.analyticOnNhd_coeffEquiv_map_coeffEquiv_symm_polynomial`: consequently its
  coordinate representation is analytic everywhere, colliding or not.
-/

public section

open Polynomial

namespace TauCeti

/-! ### The coordinate action of a polynomial map on the chart -/

section ChartAlg

open _root_.MvPolynomial Finset

variable {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}

/-- The `j`-th variable of a fundamental-theorem polynomial, read in the elementary symmetric
chart: the `(j+1)`-st elementary symmetric function of a root tuple is `(-1) ^ (j+1)` times the
chart coordinate `n - (j+1)`, by Vieta's formulas. -/
private noncomputable def esymmInChart (j : Fin n) : MvPolynomial (Fin n) 𝕜 :=
  MvPolynomial.C ((-1 : 𝕜) ^ ((j : ℕ) + 1))
    * MvPolynomial.X (⟨n - ((j : ℕ) + 1), by have := j.isLt; omega⟩ : Fin n)

/-- The substitution of the elementary symmetric polynomials read in the elementary symmetric
chart: a fundamental-theorem polynomial in the elementary symmetric functions becomes a
polynomial in the chart coordinates. -/
private noncomputable def chartSubst : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] MvPolynomial (Fin n) 𝕜 :=
  MvPolynomial.aeval esymmInChart

/-- Evaluating the chart substitution at a tuple reads a fundamental-theorem polynomial in the
signed chart coordinates. -/
private theorem aeval_chartSubst (c : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    MvPolynomial.aeval c (chartSubst p)
      = MvPolynomial.aeval
          (fun j : Fin n => (-1 : 𝕜) ^ ((j : ℕ) + 1)
            * c (⟨n - ((j : ℕ) + 1), by have := j.isLt; omega⟩ : Fin n)) p := by
  rw [chartSubst, MvPolynomial.comp_aeval_apply]
  refine congrArg (fun g => MvPolynomial.aeval g p) (funext fun j => ?_)
  rw [MvPolynomial.aeval_eq_eval]
  simp only [esymmInChart, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

end ChartAlg

section Chart

open _root_.MvPolynomial Finset

variable {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

/-- The `(j+1)`-st elementary symmetric function of a tuple, read in the elementary symmetric
chart of the tuple itself, with the signs folded into the coordinates. -/
private theorem multiset_esymm_succ_eq_chart (v : Fin n → 𝕜) (j : Fin n) :
    (univ.val.map v).esymm ((j : ℕ) + 1)
      = (-1 : 𝕜) ^ ((j : ℕ) + 1)
        * Sym.coeffEquiv 𝕜 n (Sym.ofFn v)
            (⟨n - ((j : ℕ) + 1), by have := j.isLt; omega⟩ : Fin n) := by
  rw [Sym.coeffEquiv_apply, Sym.coe_ofFn, Fin.univ_val_map,
    Nat.sub_sub_self (by have := j.isLt; omega)]
  have hsign : (-1 : 𝕜) ^ ((j : ℕ) + 1) * (-1 : 𝕜) ^ ((j : ℕ) + 1) = 1 := by
    rw [← pow_add, ← Nat.two_mul, pow_mul]
    norm_num
  rw [← mul_assoc, hsign, one_mul]

/-- **The coordinate action of a polynomial map on the elementary symmetric chart is polynomial.**
Postcomposing the points of a tuple with the polynomial function of `q` acts on the chart
coordinates by the multivariate polynomials `Q`: for every coefficient tuple `c`, colliding or
not, the coordinates of the image tuple are the evaluations `eval c (Q i)`. -/
theorem Sym.exists_coeffEquiv_map_coeffEquiv_symm_eq_eval (q : 𝕜[X]) :
    ∃ Q : Fin n → MvPolynomial (Fin n) 𝕜, ∀ c : Fin n → 𝕜,
      Sym.coeffEquiv 𝕜 n (Sym.map (fun z => eval z q) ((Sym.coeffEquiv 𝕜 n).symm c))
        = fun i => eval c (Q i) := by
  classical
  -- the fundamental theorem of symmetric polynomials, applied to the substituted esymms
  have hftsf : ∀ k : Fin n, ∃ W : MvPolynomial (Fin n) 𝕜,
      MvPolynomial.aeval (fun j : Fin n => esymm (Fin n) 𝕜 ((j : ℕ) + 1)) W
        = MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
          (esymm (Fin n) 𝕜 ((k : ℕ) + 1)) := by
    intro k
    have hsymm :
        (MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
          (esymm (Fin n) 𝕜 ((k : ℕ) + 1))).IsSymmetric := by
      intro e
      calc
        MvPolynomial.rename e
            (MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
              (esymm (Fin n) 𝕜 ((k : ℕ) + 1))) =
            MvPolynomial.bind₁
              (fun i => MvPolynomial.rename e (Polynomial.aeval (MvPolynomial.X i) q))
              (esymm (Fin n) 𝕜 ((k : ℕ) + 1)) := by
          rw [MvPolynomial.rename_bind₁]
        _ = MvPolynomial.bind₁
              ((fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q) ∘ e)
              (esymm (Fin n) 𝕜 ((k : ℕ) + 1)) := by
          apply congrArg (fun f => MvPolynomial.bind₁ f (esymm (Fin n) 𝕜 ((k : ℕ) + 1)))
          funext i
          calc
            MvPolynomial.rename e (Polynomial.aeval (MvPolynomial.X i) q) =
                Polynomial.aeval (MvPolynomial.rename e (MvPolynomial.X i)) q :=
              (Polynomial.aeval_algHom_apply (MvPolynomial.rename e) (MvPolynomial.X i) q).symm
            _ = Polynomial.aeval (MvPolynomial.X (e i)) q := by rw [MvPolynomial.rename_X]
        _ = MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
              (MvPolynomial.rename e (esymm (Fin n) 𝕜 ((k : ℕ) + 1))) := by
          rw [MvPolynomial.bind₁_rename]
        _ = MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
              (esymm (Fin n) 𝕜 ((k : ℕ) + 1)) := by
          rw [esymm_isSymmetric]
    obtain ⟨W, hW⟩ := (esymmAlgHom_fin_bijective 𝕜 n).surjective
      (⟨MvPolynomial.bind₁ (fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) q)
          (esymm (Fin n) 𝕜 ((k : ℕ) + 1)), hsymm⟩ :
        symmetricSubalgebra (Fin n) 𝕜)
    refine ⟨W, ?_⟩
    simpa [MvPolynomial.esymmAlgHom_apply] using
      congrArg (fun s : symmetricSubalgebra (Fin n) 𝕜 => (s : MvPolynomial (Fin n) 𝕜)) hW
  choose W hW using hftsf
  refine ⟨fun i => MvPolynomial.C ((-1 : 𝕜) ^ (n - (i : ℕ)))
    * chartSubst (W (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n)), fun c => ?_⟩
  obtain ⟨v, hv⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv 𝕜 n).symm c)
  have hvc : Sym.coeffEquiv 𝕜 n (Sym.ofFn v) = c := (Equiv.eq_symm_apply _).1 hv
  funext i
  have hm : ((⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n) : ℕ) + 1 = n - (i : ℕ) := by
    have h : ((⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n) : ℕ)
        = n - ((i : ℕ) + 1) := rfl
    omega
  have hW' : MvPolynomial.aeval (fun j : Fin n => esymm (Fin n) 𝕜 ((j : ℕ) + 1))
      (W (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n))
      = MvPolynomial.bind₁ (fun j : Fin n => Polynomial.aeval (MvPolynomial.X j) q)
          (esymm (Fin n) 𝕜 (n - (i : ℕ))) := by
    rw [hW (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n), hm]
  calc Sym.coeffEquiv 𝕜 n (Sym.map (fun z => eval z q) ((Sym.coeffEquiv 𝕜 n).symm c)) i
      = Sym.coeffEquiv 𝕜 n (Sym.ofFn ((fun z => Polynomial.eval z q) ∘ v)) i := by
        rw [← hv, Sym.map_ofFn]
    _ = Sym.coeffEquiv 𝕜 n (Sym.ofFn (fun j => Polynomial.eval (v j) q)) i := rfl
    _ = (-1 : 𝕜) ^ (n - (i : ℕ))
        * (univ.val.map (fun j => Polynomial.eval (v j) q)).esymm (n - (i : ℕ)) := by
        rw [Sym.coeffEquiv_apply, Sym.coe_ofFn, Fin.univ_val_map]
    _ = (-1 : 𝕜) ^ (n - (i : ℕ))
        * MvPolynomial.aeval (fun j => Polynomial.eval (v j) q)
            (esymm (Fin n) 𝕜 (n - (i : ℕ))) := by
        rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    _ = (-1 : 𝕜) ^ (n - (i : ℕ))
        * MvPolynomial.aeval (fun j => Polynomial.aeval (v j) q)
            (esymm (Fin n) 𝕜 (n - (i : ℕ))) := by
        refine congrArg (fun g => (-1 : 𝕜) ^ (n - (i : ℕ))
          * MvPolynomial.aeval g (esymm (Fin n) 𝕜 (n - (i : ℕ))))
          (funext fun j => (congrFun (Polynomial.coe_aeval_eq_eval (v j)) q).symm)
    _ = (-1 : 𝕜) ^ (n - (i : ℕ))
        * MvPolynomial.aeval v
            (MvPolynomial.bind₁ (fun j : Fin n => Polynomial.aeval (MvPolynomial.X j) q)
              (esymm (Fin n) 𝕜 (n - (i : ℕ)))) := by
        rw [MvPolynomial.aeval_bind₁]
        refine congrArg (fun g => (-1 : 𝕜) ^ (n - (i : ℕ)) *
          MvPolynomial.aeval g (esymm (Fin n) 𝕜 (n - (i : ℕ)))) (funext fun j => ?_)
        calc
          Polynomial.aeval (v j) q =
              Polynomial.aeval (MvPolynomial.aeval v (MvPolynomial.X j)) q := by
            rw [MvPolynomial.aeval_X]
          _ = MvPolynomial.aeval v (Polynomial.aeval (MvPolynomial.X j) q) :=
            Polynomial.aeval_algHom_apply (MvPolynomial.aeval v) (MvPolynomial.X j) q
    _ = (-1 : 𝕜) ^ (n - (i : ℕ))
        * MvPolynomial.aeval v
            (MvPolynomial.aeval (fun j : Fin n => esymm (Fin n) 𝕜 ((j : ℕ) + 1))
              (W (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n))) := by
        rw [← hW']
    _ = (-1 : 𝕜) ^ (n - (i : ℕ))
        * MvPolynomial.aeval
            (fun j : Fin n => (-1 : 𝕜) ^ ((j : ℕ) + 1)
              * c (⟨n - ((j : ℕ) + 1), by have := j.isLt; omega⟩ : Fin n))
            (W (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n)) := by
        rw [MvPolynomial.comp_aeval_apply]
        refine congrArg (fun g => (-1 : 𝕜) ^ (n - (i : ℕ)) * MvPolynomial.aeval g
          (W (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n))) (funext fun j => ?_)
        rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, multiset_esymm_succ_eq_chart, hvc]
    _ = MvPolynomial.eval c (MvPolynomial.C ((-1 : 𝕜) ^ (n - (i : ℕ)))
          * chartSubst (W (⟨n - ((i : ℕ) + 1), by have := i.isLt; omega⟩ : Fin n))) := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval,
          ← aeval_chartSubst]

end Chart

section Analytic

open _root_.MvPolynomial Finset

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

/-- **The coordinate action of a polynomial map on the elementary symmetric chart is analytic
everywhere.** Postcomposing the points of a tuple with the polynomial function of `q` induces a
map whose coordinate representation is analytic on the whole chart; in particular no
distinctness of the tuple's points is assumed, so this covers the tuples where points collide. -/
theorem Sym.analyticOnNhd_coeffEquiv_map_coeffEquiv_symm_polynomial (q : 𝕜[X]) :
    AnalyticOnNhd 𝕜 (fun c => Sym.coeffEquiv 𝕜 n
      (Sym.map (fun z => eval z q) ((Sym.coeffEquiv 𝕜 n).symm c))) Set.univ := by
  obtain ⟨Q, hQ⟩ := Sym.exists_coeffEquiv_map_coeffEquiv_symm_eq_eval (𝕜 := 𝕜) (n := n) q
  refine fun c _ => AnalyticAt.congr (f := fun c i => MvPolynomial.eval c (Q i))
    (AnalyticAt.pi fun i => ?_) ?_
  · have hproj : ∀ i : Fin n, AnalyticAt 𝕜 (fun c : Fin n → 𝕜 => c i) c := fun i =>
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).analyticAt _
    simpa only [MvPolynomial.aeval_eq_eval] using
      (AnalyticAt.aeval_mvPolynomial hproj (Q i))
  · filter_upwards with c using (hQ c).symm

end Analytic

end TauCeti
