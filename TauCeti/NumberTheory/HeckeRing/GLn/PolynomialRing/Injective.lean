/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Basic

public section

/-!
# `pLocalSubring` is a polynomial ring for `n = 1, 2`

The injectivity half of **Shimura's Theorem 3.20** and the resulting isomorphism
`ℤ[X₁, …, Xₙ] ≃+* pLocalSubring`, for `n = 1` and `n = 2`. The generators and the surjectivity half
are in `PolynomialRing/Basic.lean`.

Injectivity is proved by a determinant/leading-term argument: the determinant of a double
coset representative is multiplicative, so a monomial in the generators has a predictable
leading elementary-divisor vector, and distinct monomials have distinct leading terms.

## Main results

* `HeckeRing.GLn.evalHom_one_injective`, `HeckeRing.GLn.evalHom_two_injective`:
  evaluation at the generators is injective for `n = 1` and `n = 2`.
* `HeckeRing.GLn.polynomialRingEquivOne`, `HeckeRing.GLn.polynomialRingEquivTwo`:
  **Shimura, Theorem 3.20** for `n = 1` and `n = 2` — `pLocalSubring ≅ ℤ[X₁, …, Xₙ]`.

## Implementation notes

The source states Theorem 3.20 at general `n`, dispatching on `n = 1` and `n = 2` and
leaving the remaining case as a gap. Here the two proved cases are stated directly, so
nothing rests on an unformalised step.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), the `Inj` section.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

open HeckeRing.GL2

/-- The `CommSemiring` structure this module needs on `IntegralHeckeRing n`, rebuilt locally
from `HeckeCosetModule.instSemiringHeckeRing` and `HeckeCosetModule.mul_comm_of_antiInvolution`.

`PolynomialRing/Basic.lean` carries the same reconstruction, but as a `local instance`, which
does not cross the module boundary; and `commSemiringIntegralHeckeRing` is a sealed `def`, so
registering it for typeclass search does not make its body reduce to the ambient
`NonAssocSemiring`. Writing the structure here makes it transparent exactly where this file
needs it, leaving the upstream definitions sealed for every other consumer. -/
noncomputable local instance localCommSemiringForInjectivity (n : ℕ) [NeZero n] :
    CommSemiring (IntegralHeckeRing n) :=
  { (HeckeCosetModule.instSemiringHeckeRing ℤ : Semiring (IntegralHeckeRing n)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution n)
      (transposeAntiInvolution_onHeckeCoset_eq_self n) }

/-- The product of two diagonal basis elements, unfolded: it is the structure-constant family
of their representatives. The `b₁ = b₂ = 1` case of `HeckeCosetModule.single_mul`.

Kept here rather than beside either parent. It needs `diagElem`, from
`GLn/DiagonalCosets.lean`, *and* `HeckeCosetModule.single_mul`, from the abstract Hecke-ring
layer; neither of those files can see the other's contents, and this is the first module
downstream of both. Moving it either way would mean widening a core file's imports for a
single lemma. -/
private lemma diagElem_mul_diagElem (a b : Fin 2 → ℕ) :
    diagElem a * diagElem b =
      HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (diagCoset a).rep (diagCoset b).rep := by
  rw [diagElem_def, diagElem_def]
  -- `single_mul_single` yields `1 • 1 • …` on the `Module ℤ` instance transported to
  -- `HeckeCosetModule`, which is not the instance `one_smul` picks for `ℤ`, so neither `rw`
  -- nor `simp` matches it in place. Stating the product `•`-free lets unification supply the
  -- instance — the idiom already used in `GL2/MultiplicationTable.lean`.
  have hmul : HeckeCosetModule.single ℤ (diagCoset a) 1 * HeckeCosetModule.single ℤ (diagCoset b) 1
      = HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (diagCoset a).rep (diagCoset b).rep := by
    rw [HeckeCosetModule.single_mul_single]
    exact (one_smul ℤ _).trans (one_smul ℤ _)
  exact hmul

/-- For n=1, `heckeGen(0)^k = diagElem(fun _ => p^k)`. -/
private lemma heckeGen_pow_one (p : ℕ) (hp : 0 < p) (k : ℕ) :
    heckeGen 1 p (0 : Fin 1) ^ k = diagElem (fun _ : Fin 1 ↦ p ^ k) := by
  -- `heckeGen` is sealed (`public section`, no `@[expose]`), so neither `rw [heckeGen]` nor
  -- `unfold` sees through it; `heckeGen_def` supplies the equation and this states its target.
  rw [show heckeGen 1 p (0 : Fin 1) = diagElem (fun _ : Fin 1 ↦ p) from by
    rw [heckeGen_def]; exact congrArg diagElem (heckeGenDiag_one_eq_const p)]
  exact diagElem_const_pow 1 p hp k

/-- For `n = 1` and any base `1 < p`, the cosets `diagCoset (fun _ => p^k)` are injective in `k`:
if they coincide for `b 0` and `s 0`, then `b 0 = s 0`. -/
private lemma T_diag_one_ppow_inj (p : ℕ) (hp : 1 < p) {b s : Fin 1 →₀ ℕ}
    (hb : (diagCoset (n := 1) (fun _ ↦ p ^ b 0) : HeckeCoset (posDetInt 1) (SLnZ 1) (SLnZ 1)) =
      diagCoset (fun _ ↦ p ^ s 0)) : b 0 = s 0 := by
  -- each diagonal here is constant, so the chain condition is `isDvdChain_const`
  have hdiv : ∀ c : Fin 1 →₀ ℕ, IsDvdChain (fun _ : Fin 1 ↦ p ^ c 0) :=
    fun c ↦ isDvdChain_const 1 (p ^ c 0)
  have hpos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le
  have heq := eq_of_diagCoset_eq (fun _ ↦ Nat.pow_pos hpos)
    (fun _ ↦ Nat.pow_pos hpos) (hdiv b) (hdiv s) hb
  exact Nat.pow_right_injective hp (congr_fun heq 0)

/-- For `n = 1` and any base `1 < p`, evaluation at the Hecke generator is injective. -/
theorem evalHom_one_injective (p : ℕ) (hp : 1 < p) : Function.Injective (evalHom 1 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : evalHom 1 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  set D := diagCoset (n := 1) (fun _ ↦ p ^ (s 0))
  have h0 : evalHom 1 p R D = 0 := by rw [hR]; rfl
  apply hcoeff
  suffices h : evalHom 1 p R D = MvPolynomial.coeff s R from h ▸ h0
  rw [evalHom_apply]
  classical
  -- each monomial `X^k` evaluates to the basis element at `T(p^k)`, so its contribution at
  -- `D = T(p^{s 0})` is its own coefficient when `k = s 0` and zero otherwise
  have hterm : ∀ x ∈ R.support,
      R.coeff x • (∏ i, heckeGen 1 p i ^ x i : IntegralHeckeRing 1) D =
        if x = s then R.coeff s else 0 := by
    intro x _
    rw [Fin.prod_univ_one, heckeGen_pow_one p (Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le),
      diagElem_def, HeckeCosetModule.single_apply]
    by_cases hxs : x = s
    · subst hxs; simp [D]
    · rw [ite_eq_right (fun hb ↦ hxs (Finsupp.ext fun j ↦ by
        rw [Fin.fin_one_eq_zero j]; exact T_diag_one_ppow_inj p hp hb)),
        ite_eq_right hxs, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq_of_mem' R.support s _ hs]

/-- A two-entry diagonal `![a, b]` is a divisibility chain iff `a ∣ b`. -/
private lemma divChain_two_of_dvd {a b : ℕ} (hab : a ∣ b) :
    IsDvdChain (![a, b] : Fin 2 → ℕ) :=
  isDvdChain_iff.mpr fun i j hij ↦ by
    fin_cases i <;> fin_cases j <;> simp_all

/-- Elements in the same SL_n double coset have the same determinant. The general fact is
`det_eq_of_mem_doubleCoset_SLnZ`; this is its `HeckeCoset` phrasing. -/
private lemma det_doubleCoset_eq {g₁ g₂ : posDetInt 2}
    (h : HeckeCoset.mk (SLnZ 2) (SLnZ 2) g₁ = HeckeCoset.mk (SLnZ 2) (SLnZ 2) g₂) :
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det :=
  det_eq_of_mem_doubleCoset_SLnZ 2
    (HeckeCoset.eq_iff.mp h ▸ DoubleCoset.mem_doubleCoset_self _ _ _)

/-- The diagonal product of rep(diagCoset a) equals ∏ a. -/
private lemma prod_rep_T_diag (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(↑(HeckeCoset.rep (diagCoset a)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ∏ i, (a i : ℚ) := by
  -- the representative and the explicit diagonal matrix lie in the same double coset
  have h_eq : HeckeCoset.mk (SLnZ 2) (SLnZ 2) (HeckeCoset.rep (diagCoset a)) =
      HeckeCoset.mk (SLnZ 2) (SLnZ 2) ⟨natDiagGL 2 a, natDiagGL_mem_posDetInt 2 a⟩ := by
    rw [HeckeCoset.mk_rep, diagCoset_def]
  exact (det_doubleCoset_eq h_eq).trans (natDiagGL_det 2 a ha)

/-- Every coset in the support of a mulMap output has determinant = det(g₁) * det(g₂). -/
private lemma det_mulMap_eq (g₁ g₂ : posDetInt 2)
    (p : DecompQuotient (SLnZ 2) (SLnZ 2) (g₁ : GL (Fin 2) ℚ) ×
      DecompQuotient (SLnZ 2) (SLnZ 2) (g₂ : GL (Fin 2) ℚ)) :
    (↑(↑(HeckeCoset.rep (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ p)) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
        (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  -- `mulMap` names the double coset of the explicit product `σ g₁ τ g₂`
  have h_eq := (HeckeCoset.mk_rep
      (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ p)).trans
    (HeckeCoset.mulMap_eq_mk (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ p)
  rw [det_doubleCoset_eq h_eq]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h1 := det_eq_one_of_mem_SLnZ 2 (p.1.out.2)
  have h2 := det_eq_one_of_mem_SLnZ 2 (p.2.out.2)
  rw [h1, h2]; ring

/-- If `D'` appears in the support of `m(rep D₁, rep D₂)`, then the determinant of its
representative is the product of the determinants of `rep D₁` and `rep D₂`. -/
private lemma det_rep_eq_mul_of_m_ne_zero (D₁ D₂ D' : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hm : (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D' ≠ 0) :
    (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
        (↑(↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  classical
  rw [HeckeCosetModule.structureConstants_apply] at hm
  -- a nonzero structure constant means `D'` is hit by `mulMap`
  have hD'_mem : D' ∈ Finset.univ.image
      (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) :=
    (HeckeCoset.mem_image_mulMap_iff _ _ _).mpr (Nat.cast_ne_zero.mp hm)
  rw [Finset.mem_image] at hD'_mem
  obtain ⟨p, _, hD'_eq⟩ := hD'_mem
  rw [← hD'_eq]; exact det_mulMap_eq (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p

/-- Determinant tracking: if `f` is supported on cosets of determinant `q^{a₀}`, then
`heckeGen(q,0)^{b₀} · f` is supported on cosets of determinant `q^{b₀ + a₀}`. -/
private lemma det_rep_T_gen_zero_pow_mul (q : ℕ) (hq : 0 < q) (a₀ b₀ : ℕ)
    (f : IntegralHeckeRing 2) (D' : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hf_det : ∀ D'', f D'' ≠ 0 →
      (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = ↑(q ^ a₀ : ℕ))
    (hD' : (heckeGen 2 q 0 ^ b₀ * f) D' ≠ 0) :
    (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ↑(q ^ (b₀ + a₀) : ℕ) := by
  induction b₀ generalizing f D' with
  | zero =>
    rw [pow_zero, one_mul] at hD'
    simpa only [Nat.zero_add] using hf_det D' hD'
  | succ n ih =>
    rw [pow_succ', mul_assoc] at hD'
    set g' := heckeGen 2 q 0 ^ n * f
    -- `heckeGen` and `diagElem` are both sealed, so neither side reduces here; the `_def`
    -- lemmas bridge them and this states the single-`Finsupp` spelling to rewrite with.
    rw [show heckeGen 2 q 0 = HeckeCosetModule.single ℤ (diagCoset (![1, q])) 1 from by
        rw [heckeGen_def, diagElem_def]
        exact congrArg (fun a ↦ HeckeCosetModule.single ℤ (diagCoset a) 1)
          (funext fun i ↦ by fin_cases i <;> simp [heckeGenDiag_apply])] at hD'
    obtain ⟨D₂, hD₂_mem, hD₂_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
      -- `IntegralHeckeRing` is a `def` over `Finsupp`, so evaluating a convolution at a coset
      -- holds by defeq but matches no `Finsupp` lemma through the wrapper; the expansion is
      -- stated and closed by the wrapper's own `mul_def`/`single_mul`/`sum_apply` chain.
      rw [show (HeckeCosetModule.single ℤ (diagCoset (![1, q])) 1 * g') D' =
          ∑ D₂ ∈ g'.support, g' D₂ *
            (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, q]))) (HeckeCoset.rep D₂)) D' from by
          rw [HeckeCosetModule.mul_def, HeckeCosetModule.single_mul,
            HeckeCosetModule.sum_apply, HeckeCosetModule.sum_def]
          simp only [HeckeCosetModule.smul_apply, one_mul]] at hD'
      exact hD')
    have hm_ne : (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (HeckeCoset.rep (diagCoset (![1, q])))
        (HeckeCoset.rep D₂)) D' ≠ 0 := fun h ↦ hD₂_ne (by rw [h, mul_zero])
    rw [det_rep_eq_mul_of_m_ne_zero _ _ _ hm_ne,
      -- `![…]` literals that are only extensionally equal do not unify syntactically, so the
      -- intended spelling is stated here for the following rewrite to match.
      show (↑(↑(HeckeCoset.rep (diagCoset (![1, q]))) : GL (Fin 2) ℚ) :
          Matrix (Fin 2) (Fin 2) ℚ).det = (q : ℚ) from by
        rw [prod_rep_T_diag (![1, q]) (fun i ↦ by fin_cases i <;> simp [hq])]
        simp [Fin.prod_univ_two],
      ih f D₂ hf_det (Finsupp.mem_support_iff.mp hD₂_mem)]
    push_cast; ring

/-- Every double coset in the support of `T(1,q)^{e₀} · T(q,q)^{e₁}` is a diagonal coset
`T(a)` for a positive divisibility chain `a`, whose entry product — the determinant of any
representative — is `q^(e₀ + 2·e₁)`.

This is what makes the exponent pair recoverable: the determinant pins `e₀ + 2·e₁`, and the
elementary-divisor order then separates the individual exponents. -/
private lemma T_gen_pow_support_qpower (q : ℕ) (hq : 0 < q) (e : Fin 2 → ℕ)
    (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hD : (heckeGen 2 q 0 ^ (e 0) * heckeGen 2 q 1 ^ (e 1)) D ≠ 0) :
    ∃ a : Fin 2 → ℕ, D = diagCoset a ∧ (∀ i, 0 < a i) ∧ IsDvdChain a ∧
      (∏ i, a i) = q ^ (e 0 + 2 * e 1) := by
  obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative D
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  have hf_det : ∀ D'', (heckeGen 2 q 1 ^ (e 1)) D'' ≠ 0 →
      (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q ^ (2 * e 1) : ℕ) := by
    classical
    intro D'' hD''
    rw [heckeGen_one_eq_heckeTScalar q hq,
      HeckeRing.GL2.heckeTScalar_pow q hq (e 1)] at hD''
    have h_eq : diagCoset (fun _ : Fin 2 ↦ q ^ (e 1)) = D'' := by
      by_contra h
      exact hD'' (by rw [diagElem_def, HeckeCosetModule.single_apply, ite_eq_right h])
    rw [← h_eq, prod_rep_T_diag _ (fun i ↦ by fin_cases i <;> simp [pow_pos hq])]
    push_cast [Fin.prod_univ_two, ← pow_add]; ring_nf
  have h_result := det_rep_T_gen_zero_pow_mul q hq (2 * e 1) (e 0) _ D hf_det hD
  rw [hD_eq, prod_rep_T_diag a ha_pos] at h_result
  exact mod_cast h_result

/-- `T_single(diagCoset a, α) * diagElem(c,c) = T_single(diagCoset(a * c), α)`. -/
private lemma T_single_diag_mul_T_scalar (c : ℕ) (hc : 0 < c)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (α : ℤ) :
    HeckeCosetModule.single ℤ (diagCoset a) α * diagElem (fun _ : Fin 2 ↦ c) =
    HeckeCosetModule.single ℤ (diagCoset (a * (fun _ : Fin 2 ↦ c))) α := by
  have h_single : HeckeCosetModule.single ℤ (diagCoset a) α =
      α • diagElem a := by
    -- `diagElem` is sealed, so `show` cannot see through it; `diagElem_def` is the bridge.
    rw [diagElem_def]
    exact (HeckeCosetModule.smul_single_one ℤ (diagCoset a) α).symm
  rw [h_single, smul_mul_assoc, diagElem_mul_const 2 a ha_pos c hc, diagElem_def]
  exact HeckeCosetModule.smul_single_one ℤ (diagCoset (a * fun _ ↦ c)) α

/-- **Reduction to the basis for products with a scalar coset.** Both statements below about
`f * diagElem (fun _ ↦ c)` evaluated at a fixed coset `D` are additive in `f`, so it is enough
to check them on the `single` basis. This lemma performs that reduction once: the `zero` and
`add` cases are pure `Finsupp`-through-the-wrapper bookkeeping and carry no content.

The target is packaged as an `F : IntegralHeckeRing 2 →+ ℤ` because additivity of the target is
exactly what the induction consumes. -/
private lemma eval_mul_diagElem_const_of_single (c : ℕ)
    (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) (F : IntegralHeckeRing 2 →+ ℤ)
    (hsingle : ∀ (D' : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) (α : ℤ),
      (HeckeCosetModule.single ℤ D' α * diagElem (fun _ : Fin 2 ↦ c)) D =
        F (HeckeCosetModule.single ℤ D' α))
    (f : IntegralHeckeRing 2) : (f * diagElem (fun _ : Fin 2 ↦ c)) D = F f := by
  classical
  induction f using HeckeCosetModule.induction_linear with
  | h0 =>
    -- `IntegralHeckeRing` is a `def` over `Finsupp`, so a ring element applied at a coset is
    -- `Finsupp` application through the wrapper: true by defeq, but nothing matches
    -- syntactically, so the shape is stated once here rather than at every use.
    change ((0 : IntegralHeckeRing 2) * diagElem (fun _ : Fin 2 ↦ c)) D = F 0
    rw [zero_mul, map_zero]; rfl
  | hadd g h ihg ihh =>
    set g' : IntegralHeckeRing 2 := g
    set h' : IntegralHeckeRing 2 := h
    change ((g' + h') * diagElem (fun _ : Fin 2 ↦ c)) D = F (g' + h')
    rw [add_mul, HeckeCosetModule.add_apply, map_add, ihg, ihh]
  | hsingle D' α => exact hsingle D' α

/-- Evaluation at a fixed coset, as an additive map on the Hecke ring. -/
private noncomputable def evalAddHom (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) :
    IntegralHeckeRing 2 →+ ℤ :=
  AddMonoidHom.mk' (fun f ↦ f D) (fun g h ↦ HeckeCosetModule.add_apply g h D)

/-- `evalAddHom D` is evaluation at `D`. -/
@[simp] private lemma evalAddHom_apply (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (f : IntegralHeckeRing 2) : evalAddHom D f = f D := rfl

/-- Scalar shift identity: for any `f : IntegralHeckeRing 2`, scalar `c > 0`, and positive
divisibility-chain `b`, evaluating `f * diagElem(c,c)` at `diagCoset(b * c)` equals
`f(diagCoset b)`. -/
private lemma T_mul_T_scalar_eval_shifted (c : ℕ) (hc : 0 < c) (f : IntegralHeckeRing 2)
    (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb_div : IsDvdChain b) :
    (f * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset (b * (fun _ : Fin 2 ↦ c))) = f (diagCoset b) := by
  classical
  refine eval_mul_diagElem_const_of_single c _ (evalAddHom (diagCoset b)) ?_ f
  intro D α
  obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative D
  rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos α]
  rw [evalAddHom_apply, HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
  by_cases hab : a = b
  · subst hab; rw [ite_eq_left rfl, ite_eq_left rfl]
  · have h_ne_1 : diagCoset (a * fun _ : Fin 2 ↦ c) ≠ diagCoset (b * fun _ : Fin 2 ↦ c) := by
      intro heq
      have h1_eq : a * (fun _ : Fin 2 ↦ c) = b * (fun _ : Fin 2 ↦ c) :=
        eq_of_diagCoset_eq (fun i ↦ Nat.mul_pos (ha_pos i) hc)
          (fun i ↦ Nat.mul_pos (hb_pos i) hc) (isDvdChain_mul 2 ha_div (isDvdChain_const 2 c))
          (isDvdChain_mul 2 hb_div (isDvdChain_const 2 c)) heq
      exact hab (funext fun i ↦ Nat.eq_of_mul_eq_mul_right hc (congr_fun h1_eq i))
    have h_ne_2 : diagCoset a ≠ diagCoset b := fun heq ↦ hab
      (eq_of_diagCoset_eq ha_pos hb_pos ha_div hb_div heq)
    rw [ite_eq_right h_ne_1, ite_eq_right h_ne_2]

/-- If `c ∤ d i` for some `i`, the evaluation of `f * diagElem(c,c)` at `diagCoset d` is zero. -/
private lemma T_mul_T_scalar_eval_zero_of_not_dvd (c : ℕ) (hc : 0 < c) (f : IntegralHeckeRing 2)
    (d : Fin 2 → ℕ)
    (hd_pos : ∀ i, 0 < d i) (hd_div : IsDvdChain d) (i₀ : Fin 2) (hi₀ : ¬ c ∣ d i₀) :
    (f * diagElem (fun _ : Fin 2 ↦ c)) (diagCoset d) = 0 := by
  classical
  refine eval_mul_diagElem_const_of_single c _ 0 ?_ f
  intro D α
  obtain ⟨a, ha_pos, ha_div, hD_eq⟩ := exists_diagonal_representative D
  rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos α, HeckeCosetModule.single_apply]
  have h_ne : diagCoset (a * fun _ : Fin 2 ↦ c) ≠ diagCoset d := by
    intro heq
    have h_eq : a * (fun _ : Fin 2 ↦ c) = d :=
      eq_of_diagCoset_eq (fun i ↦ Nat.mul_pos (ha_pos i) hc) hd_pos
        (isDvdChain_mul 2 ha_div (isDvdChain_const 2 c)) hd_div heq
    refine hi₀ ⟨a i₀, ?_⟩
    have h := congr_fun h_eq i₀
    simp only [Pi.mul_apply] at h
    linarith [h.symm]
  rw [ite_eq_right h_ne]
  rfl

/-- For `i ≥ 1`, evaluation of `f * heckeTScalar(p)^i` at `diagCoset ![1, k]` is zero
(since `p^i ∤ 1`). -/
private lemma T_mul_T_pp_pow_eval_at_one_zero (p : ℕ) (hp : 1 < p) (i k : ℕ) (hi : 1 ≤ i)
    (hk : 0 < k) (f : IntegralHeckeRing 2) :
    (f * heckeTScalar p ^ i) (diagCoset (![1, k] : Fin 2 → ℕ)) = 0 := by
  rw [HeckeRing.GL2.heckeTScalar_pow p (Nat.zero_lt_of_lt hp) i]
  apply T_mul_T_scalar_eval_zero_of_not_dvd (p^i) (pow_pos (Nat.zero_lt_of_lt hp) i) f
    (![1, k] : Fin 2 → ℕ) (fun idx ↦ by fin_cases idx <;> simp [hk])
    (divChain_two_of_dvd (one_dvd k)) 0
  simp only [Matrix.cons_val_zero]
  intro hdvd
  have hle : p ^ i ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
  have hge : p ≤ p ^ i := Nat.le_self_pow (by omega) p
  have hp2 : 2 ≤ p := hp
  omega

/-- `diagElem ![p^i, p^j] = heckeTDiag(1, p^{j-i}) * heckeTScalar(p)^i` for `i ≤ j` with `p`
prime. -/
private lemma T_elem_ppow_factor (p : ℕ) (hp : 0 < p) (i j : ℕ) (hij : i ≤ j) :
    diagElem (![p^i, p^j] : Fin 2 → ℕ) = heckeTDiag 1 (p ^ (j - i)) * heckeTScalar p ^ i := by
  rw [heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp _) (one_dvd _),
      HeckeRing.GL2.heckeTScalar_pow p hp i]
  have h_ji_pos : ∀ idx : Fin 2, 0 < (![1, p^(j-i)] : Fin 2 → ℕ) idx := by
    intro idx; fin_cases idx
    · simp
    · simp [pow_pos hp]
  rw [diagElem_mul_const 2 (![1, p^(j-i)] : Fin 2 → ℕ) h_ji_pos (p^i) (pow_pos hp _)]
  apply congrArg diagElem
  funext idx; fin_cases idx
  · simp [Pi.mul_apply]
  · simp [Pi.mul_apply, ← pow_add]; congr 1; omega

/-- The element `T(p, pⁿ)` does not contribute at `T(1, p^{n+1})` (for `n ≥ 1`). -/
private lemma T_elem_p_ppow_eval_at_one_ppow_succ_zero (p : ℕ) (hp : 1 < p) {n : ℕ}
    (hn : n ≠ 0) :
    (diagElem (![p, p ^ n] : Fin 2 → ℕ)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
  classical
  rw [diagElem_def, HeckeCosetModule.single_apply]
  refine ite_eq_right (fun heq ↦ ?_)
  have h_eq : (![p, p ^ n] : Fin 2 → ℕ) = (![1, p ^ (n + 1)] : Fin 2 → ℕ) :=
    eq_of_diagCoset_eq
      (fun i ↦ by fin_cases i <;> simp [Nat.zero_lt_of_lt hp, pow_pos (Nat.zero_lt_of_lt hp)])
      (fun i ↦ by fin_cases i <;> simp [pow_pos (Nat.zero_lt_of_lt hp)])
      (divChain_two_of_dvd (dvd_pow_self p hn)) (divChain_two_of_dvd (one_dvd _)) heq
  have := congr_fun h_eq 0
  simp only [Matrix.cons_val_zero] at this
  have := hp; omega

/-- `(T(1,p) · T(1, pⁿ))` evaluated at the leading coset `T(1, p^{n+1})` equals `1`. -/
private lemma T_ad_one_p_mul_T_ad_one_ppow_eval_leading (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (heckeTDiag 1 p * heckeTDiag 1 (p ^ n)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 := by
  classical
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [pow_zero, heckeTDiag_one_one, mul_one,
      heckeTDiag_eq_diagElem Nat.one_pos hp.pos (one_dvd _), diagElem_def,
      -- `![…]` literals that are only extensionally equal do not unify syntactically, so the
      -- intended spelling is stated here for the following rewrite to match.
      show (![1, p ^ (0 + 1)] : Fin 2 → ℕ) = (![1, p] : Fin 2 → ℕ) from by
        funext i; fin_cases i <;> simp,
      HeckeCosetModule.single_apply, ite_eq_left rfl]
  · rw [← heckeT_prime p hp, heckeT_prime_mul_heckeTDiag_one_prime_pow p hp n]
    -- `Finsupp.add_apply` holds through the `IntegralHeckeRing` wrapper by defeq but does not
    -- match syntactically, so the split is stated and closed by that lemma.
    rw [show (heckeTDiag 1 (p ^ (n + 1)) + (if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
              heckeTDiag p (p ^ n)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) =
          heckeTDiag 1 (p ^ (n + 1)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) +
            ((if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) • heckeTDiag p (p ^ n))
              (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) from Finsupp.add_apply _ _ _,
      heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp.pos _) (one_dvd _),
      heckeTDiag_eq_diagElem hp.pos (pow_pos hp.pos _) (dvd_pow_self p hn)]
    -- `diagElem` is sealed, so its value at its own coset does not reduce here; `diagElem_def`
    -- with `single_apply` gives it, and this states the result to rewrite with.
    rw [show (diagElem (![1, p ^ (n + 1)] : Fin 2 → ℕ))
          (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 from
        by rw [diagElem_def, HeckeCosetModule.single_apply, ite_eq_left rfl]]
    -- `Finsupp.smul_apply`, same obstruction as the `add_apply` above: true through the
    -- wrapper by defeq, not syntactically matchable, so the pushed-in form is stated.
    rw [show ((if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) • diagElem (![p, p ^ n] : Fin 2 → ℕ))
          (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) =
        (if n = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
          diagElem (![p, p ^ n] : Fin 2 → ℕ) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) from
        Finsupp.smul_apply _ _ _,
      T_elem_p_ppow_eval_at_one_ppow_succ_zero p hp.one_lt hn,
      smul_zero, add_zero]

/-- A non-leading support element `D₂` of `(T(1,p))ⁿ` contributes `0` to the product
`T(1,p) · (T(1,p))ⁿ` at the leading coset `T(1, p^{n+1})`. -/
private lemma T_ad_one_p_mul_supp_ne_leading_eval_zero (p : ℕ) (hp : p.Prime) (n : ℕ)
    (D₂ : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) (hD₂_ne_zero : ((heckeTDiag 1 p) ^ n) D₂ ≠ 0)
    (hD₂_ne : D₂ ≠ diagCoset (![1, p ^ n] : Fin 2 → ℕ)) :
    (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ)))
      (HeckeCoset.rep D₂)) (diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
  have hg_eq : (heckeTDiag 1 p) ^ n = (heckeGen 2 p 0) ^ n * (heckeGen 2 p 1) ^ 0 := by
    simp only [pow_zero, mul_one, heckeGen_zero_eq_heckeTDiag p hp.pos]
  obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower p hp.pos
      ![n, 0] D₂ (hg_eq ▸ hD₂_ne_zero)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at ha_det
  have ha_prod : a 0 * a 1 = p ^ n := Fin.prod_univ_two a ▸ ha_det
  obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp (ha_prod ▸ dvd_mul_right _ _)
  have ha1_eq : a 1 = p ^ (n - i) := by
    have h : p ^ i * a 1 = p ^ i * p ^ (n - i) := by
      -- `i + (n - i) = n` is a truncated-subtraction side condition that needs `hi_le`; no
      -- rewrite reaches it, so it is stated inline and discharged by `omega`.
      rw [← pow_add, show i + (n - i) = n from by omega, ← ha_prod, hi_eq]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h
  have ha_form : a = (![p ^ i, p ^ (n - i)] : Fin 2 → ℕ) := by
    funext k; fin_cases k
    · exact hi_eq
    · exact ha1_eq
  have hi_ge : 1 ≤ i := by
    by_contra h_not
    obtain rfl : i = 0 := by omega
    exact hD₂_ne (by rw [hDa, ha_form]; simp [pow_zero])
  have hi_le_sub : i ≤ n - i := by
    have h_div := ha_form ▸ isDvdChain_iff.mp ha_div (by decide : (0 : Fin 2) ≤ 1)
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h_div
  rw [hDa, ha_form, ← diagElem_mul_diagElem]
  -- `IntegralHeckeRing` is a `def` over `Finsupp`, so evaluating a ring element at a coset
  -- is `Finsupp` application through the wrapper: the equation holds by defeq but no
  -- `Finsupp` lemma matches syntactically, so the shape is stated rather than rewritten.
  change (diagElem (![1, p] : Fin 2 → ℕ) * diagElem (![p^i, p^(n-i)] : Fin 2 → ℕ)) _ = 0
  rw [T_elem_ppow_factor p hp.pos i (n - i) hi_le_sub, ← mul_assoc]
  exact T_mul_T_pp_pow_eval_at_one_zero p hp.one_lt i (p ^ (n + 1)) hi_ge (pow_pos hp.pos _) _

/-- Leading coefficient of `T(1,p)^a`: `(heckeTDiag 1 p)^a` evaluated at the leading coset
`diagCoset ![1, p^a]` equals 1. -/
private lemma T_ad_one_p_pow_eval_leading (p : ℕ) (hp : p.Prime) (a : ℕ) :
    ((heckeTDiag 1 p) ^ a) (diagCoset (![1, p ^ a] : Fin 2 → ℕ)) = 1 := by
  classical
  induction a with
  | zero =>
    -- `![1, 1]` and `fun _ ↦ 1` are extensionally but not syntactically equal, so the
    -- conversion is stated and proved pointwise before `diagElem_one` can apply.
    rw [pow_zero, pow_zero, show (![1, 1] : Fin 2 → ℕ) = (fun _ : Fin 2 ↦ 1) from by
        funext i; fin_cases i <;> rfl, ← diagElem_one]
    rw [diagElem_def, HeckeCosetModule.single_apply, ite_eq_left rfl]
  | succ n ih =>
    rw [pow_succ']
    set g := (heckeTDiag 1 p) ^ n
    set D_target : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
      diagCoset (![1, p ^ (n + 1)] : Fin 2 → ℕ)
    set D_leading : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
      diagCoset (![1, p ^ n] : Fin 2 → ℕ)
    rw [heckeTDiag_eq_diagElem Nat.one_pos hp.pos (one_dvd _), diagElem_def,
      HeckeCosetModule.mul_def, HeckeCosetModule.single_mul]
    -- Evaluate the convolution at `D_target` in the wrapper's own vocabulary: push the
    -- evaluation in with `sum_apply` first, then let `sum_def` expose the `Finset.sum`.
    rw [HeckeCosetModule.sum_apply, HeckeCosetModule.sum_def]
    simp only [HeckeCosetModule.smul_apply, one_mul]
    have h_leading_in_supp : D_leading ∈ g.support :=
      HeckeCosetModule.mem_support_iff.mpr (ih ▸ one_ne_zero)
    rw [← Finset.sum_erase_add _ _ h_leading_in_supp]
    have h_erased : ∀ D₂ ∈ g.support.erase D_leading,
        (g D₂ • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D₂)) D_target = 0 := by
      intro D₂ hD₂
      rw [Finset.mem_erase] at hD₂
      -- The `•` here and the one in `smul_apply` print alike but sit on different instance
      -- paths, so `rw`/`simp` cannot match it. Writing the equation out lets it elaborate
      -- with the goal's instances, and `smul_apply` then checks against it up to defeq.
      have hs : (g D₂ • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D₂.rep) D_target =
          g D₂ * (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D₂.rep) D_target :=
        HeckeCosetModule.smul_apply _ _ _
      rw [hs]
      rw [T_ad_one_p_mul_supp_ne_leading_eval_zero p hp n D₂
        (HeckeCosetModule.mem_support_iff.mp hD₂.2) hD₂.1, mul_zero]
    have h_sum_zero :
        ∑ x ∈ g.support.erase D_leading, (g x •
          HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep x)) D_target = 0 :=
      Finset.sum_eq_zero h_erased
    -- Goal: ∑ + (g D_leading • m ...) D_target = 1
    -- Strategy: prove the leading term equals 1, then linarith with h_sum_zero
    have h_leading_eq : (g D_leading •
        HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading))
          D_target = 1 := by
      have hs : (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D_leading.rep) D_target =
          g D_leading * (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (diagCoset (![1, p] : Fin 2 → ℕ)).rep D_leading.rep) D_target :=
        HeckeCosetModule.smul_apply _ _ _
      rw [hs, ih, one_mul, ← diagElem_mul_diagElem]
      rw [show diagElem (![1, p] : Fin 2 → ℕ) = heckeTDiag 1 p from
          (heckeTDiag_eq_diagElem Nat.one_pos hp.pos (one_dvd _)).symm,
        -- `![…]` literals that are only extensionally equal do not unify syntactically, so the
        -- intended spelling is stated here for the following rewrite to match.
        show diagElem (![1, p ^ n] : Fin 2 → ℕ) = heckeTDiag 1 (p ^ n) from
          (heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp.pos n) (one_dvd _)).symm]
      exact T_ad_one_p_mul_T_ad_one_ppow_eval_leading p hp n
    calc ∑ x ∈ g.support.erase D_leading, (g x •
          HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep x)) D_target +
          (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target
        = 0 + (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
              (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading))
              D_target :=
          by rw [h_sum_zero]
      _ = (g D_leading • HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
            (HeckeCoset.rep (diagCoset (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading))
            D_target :=
          zero_add _
      _ = 1 := h_leading_eq

/-- For `a₁ ≠ a₂`, evaluating `(heckeTDiag 1 p)^a₁` at the coset `T(1, p^{a₂})` gives `0`. -/
private lemma T_ad_one_p_pow_eval_at_one_ppow_of_ne (p : ℕ) (hp : p.Prime) {a₁ a₂ : ℕ}
    (ha_ne : a₁ ≠ a₂) :
    ((heckeTDiag 1 p) ^ a₁) (diagCoset (![1, p ^ a₂] : Fin 2 → ℕ)) = 0 := by
  by_contra h_ne_zero
  have hg_eq : (heckeTDiag 1 p) ^ a₁ = (heckeGen 2 p 0) ^ a₁ * (heckeGen 2 p 1) ^ 0 := by
    simp only [pow_zero, mul_one, heckeGen_zero_eq_heckeTDiag p hp.pos]
  obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower p hp.pos
      ![a₁, 0] (diagCoset (![1, p ^ a₂] : Fin 2 → ℕ)) (hg_eq ▸ h_ne_zero)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at ha_det
  have h_a_eq : a = (![1, p ^ a₂] : Fin 2 → ℕ) :=
    eq_of_diagCoset_eq ha_pos
      (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) ha_div
      (divChain_two_of_dvd (one_dvd _)) hDa.symm
  rw [h_a_eq, Fin.prod_univ_two] at ha_det
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at ha_det
  exact ha_ne (Nat.pow_right_injective hp.two_le ha_det.symm)

/-- `(heckeTDiag 1 p)^a₁` times the scalar `T(p^b, p^b)`, evaluated at the shifted leading coset
`T(p^b, p^{a₂+b})`, equals `(heckeTDiag 1 p)^a₁` evaluated at `T(1, p^{a₂})`. -/
private lemma T_ad_one_p_pow_mul_scalar_eval_at_one_ppow (p : ℕ) (hp : 0 < p) (a₁ a₂ b : ℕ) :
    ((heckeTDiag 1 p) ^ a₁ * diagElem (fun _ : Fin 2 ↦ p ^ b))
        (diagCoset (![p ^ b, p ^ (a₂ + b)] : Fin 2 → ℕ)) =
    ((heckeTDiag 1 p) ^ a₁) (diagCoset (![1, p ^ a₂] : Fin 2 → ℕ)) := by
  -- a `![…]` literal does not unify with a pointwise product syntactically, so the
  -- factorisation is stated and proved entrywise before the shifted-coset lemma can apply.
  rw [show (![p ^ b, p ^ (a₂ + b)] : Fin 2 → ℕ) =
      (![1, p ^ a₂] : Fin 2 → ℕ) * (fun _ : Fin 2 ↦ p ^ b) from by
        funext i; fin_cases i
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, pow_add]]
  exact T_mul_T_scalar_eval_shifted (p ^ b) (pow_pos hp _) _ _
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp]) (divChain_two_of_dvd (one_dvd _))

/-- Kronecker delta lemma: evaluating the monomial `heckeGen(p,0)^a₁ * heckeGen(p,1)^b₁` at the
diagonal coset `T(p^b₂, p^(a₂+b₂))` gives 1 iff `(a₁, b₁) = (a₂, b₂)`, and 0 otherwise,
under the hypothesis `b₂ ≤ b₁`. -/
private lemma monomial_eval_kronecker (p : ℕ) (hp : p.Prime)
    (a₁ b₁ a₂ b₂ : ℕ) (h : b₂ ≤ b₁) :
    (heckeGen 2 p 0 ^ a₁ * heckeGen 2 p 1 ^ b₁)
        (diagCoset (primePowDiag 2 p ![b₂, a₂ + b₂])) =
    if a₁ = a₂ ∧ b₁ = b₂ then 1 else 0 := by
  -- `primePowDiag_apply` is entrywise, so reaching the `![…]` literal takes a `funext`; the
  -- literal spelling is stated here for the rewrites that follow to match.
  rw [show (primePowDiag 2 p ![b₂, a₂ + b₂] : Fin 2 → ℕ) = (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ)
      from by funext i; fin_cases i <;> simp [primePowDiag_apply],
    heckeGen_zero_eq_heckeTDiag p hp.pos,
    heckeGen_one_eq_heckeTScalar p hp.pos,
    HeckeRing.GL2.heckeTScalar_pow p hp.pos b₁]
  by_cases hmatch : a₁ = a₂ ∧ b₁ = b₂
  · obtain ⟨ha, hb⟩ := hmatch
    rw [ite_eq_left ⟨ha, hb⟩, ha, ← hb, T_ad_one_p_pow_mul_scalar_eval_at_one_ppow p hp.pos,
      T_ad_one_p_pow_eval_leading p hp a₂]
  · rw [ite_eq_right hmatch]
    by_cases hbeq : b₁ = b₂
    · subst hbeq
      rw [T_ad_one_p_pow_mul_scalar_eval_at_one_ppow p hp.pos,
        T_ad_one_p_pow_eval_at_one_ppow_of_ne p hp (fun heq ↦ hmatch ⟨heq, rfl⟩)]
    · have h_not_dvd : ¬ p ^ b₁ ∣ (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) 0 := by
        simp only [Matrix.cons_val_zero, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
        omega
      exact T_mul_T_scalar_eval_zero_of_not_dvd (p ^ b₁) (pow_pos hp.pos _) _ _
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (divChain_two_of_dvd (pow_dvd_pow p (by omega))) 0 h_not_dvd

/-- n=2: evalHom is injective. -/
theorem evalHom_two_injective (p : ℕ) (hp : p.Prime) :
    Function.Injective (evalHom 2 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]; set R := P - Q
  have hR : evalHom 2 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hR_ne
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image R.support
    (fun d : Fin 2 →₀ ℕ ↦ d 1) (MvPolynomial.support_nonempty.mpr hR_ne)
  have hs_coeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  have h_zero : (evalHom 2 p R) (diagCoset (primePowDiag 2 p ![s 1, s 0 + s 1])) = 0 := by
    rw [hR]; rfl
  -- expand with the general evaluation rule, then normalise each rank-two summand
  rw [evalHom_apply] at h_zero
  rw [Finset.sum_congr rfl fun d _ ↦ by rw [Fin.prod_univ_two, smul_eq_mul]] at h_zero
  have h_delta : ∀ d ∈ R.support,
      R.coeff d * (heckeGen 2 p 0 ^ (d 0) * heckeGen 2 p 1 ^ (d 1))
          (diagCoset (primePowDiag 2 p ![s 1, s 0 + s 1])) =
      if d = s then R.coeff d else 0 := by
    intro d hd_mem
    rw [monomial_eval_kronecker p hp (d 0) (d 1) (s 0) (s 1) (hs_min d hd_mem)]
    by_cases hds : d = s
    · subst hds; simp
    · rw [ite_eq_right hds,
        ite_eq_right (fun ⟨h0, h1⟩ ↦ hds (by ext i; fin_cases i; exacts [h0, h1])), mul_zero]
  rw [Finset.sum_congr rfl h_delta, Finset.sum_ite_eq_of_mem' R.support s _ hs_mem] at h_zero
  exact hs_coeff h_zero

/-- Injectivity transfers from `evalHom` to its codomain restriction `evalHomLocal`: two
polynomials with the same image in `pLocalSubring` have the same image in the ambient ring. -/
lemma evalHomLocal_injective (n : ℕ) [NeZero n] (p : ℕ)
    (h_inj : Function.Injective (evalHom n p)) :
    Function.Injective (evalHomLocal n p) := by
  intro P Q hPQ
  refine h_inj ?_
  -- not `RingHom.injective_codRestrict`: its `f`, `s`, `h` are implicit and only solvable by
  -- unfolding `evalHomLocal`, which is sealed here ("definition is not exposed").
  -- `evalHomLocal_coe` is the exported stand-in for that unfolding.
  rw [← evalHomLocal_coe n p P, ← evalHomLocal_coe n p Q, hPQ]

variable (p : ℕ)

/-- **Shimura, Theorem 3.20 for `n = 1`**: the `p`-local Hecke ring of `GL₁` is the
polynomial ring `ℤ[X]` on the single generator `T(p)`.

Stated for `1 < p` rather than `p.Prime`: rank one needs only that `k ↦ p^k` is injective. -/
noncomputable def polynomialRingEquivOne (hp : 1 < p) :
    MvPolynomial (Fin 1) ℤ ≃+* pLocalSubring 1 p :=
  RingEquiv.ofBijective (evalHomLocal 1 p)
    ⟨evalHomLocal_injective 1 p (evalHom_one_injective p hp),
     evalHomLocal_one_surjective p (Nat.zero_lt_of_lt hp)⟩

/-- The rank-one presentation isomorphism is the evaluation map. -/
@[simp] lemma polynomialRingEquivOne_apply (hp : 1 < p) (f : MvPolynomial (Fin 1) ℤ) :
    polynomialRingEquivOne p hp f = evalHomLocal 1 p f := (rfl)

/-- **Shimura, Theorem 3.20 for `n = 2`**: the `p`-local Hecke ring of `GL₂` is the
polynomial ring `ℤ[X₁, X₂]` on the generators `T(1, p)` and `T(p, p)`. This is the case the
classical theory of modular forms uses.

Primality is genuine here: the rank-two argument runs through the `GL₂` recurrence. -/
noncomputable def polynomialRingEquivTwo (hp : p.Prime) :
    MvPolynomial (Fin 2) ℤ ≃+* pLocalSubring 2 p :=
  RingEquiv.ofBijective (evalHomLocal 2 p)
    ⟨evalHomLocal_injective 2 p (evalHom_two_injective p hp),
     evalHomLocal_two_surjective p hp⟩

/-- The rank-two presentation isomorphism is the evaluation map. -/
@[simp] lemma polynomialRingEquivTwo_apply (hp : p.Prime) (f : MvPolynomial (Fin 2) ℤ) :
    polynomialRingEquivTwo p hp f = evalHomLocal 2 p f := (rfl)

end HeckeRing.GLn
