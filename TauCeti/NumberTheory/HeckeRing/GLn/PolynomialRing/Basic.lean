/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Recurrence
public import TauCeti.NumberTheory.HeckeRing.GLn.PrimeDecomposition

public section

/-!
# Generators of the `p`-local Hecke ring

Towards **Shimura's Theorem 3.20**, that the `p`-local Hecke ring `pLocalSubring` of `GL_n` is a
polynomial ring `ℤ[X₁, …, Xₙ]` on the `n` diagonal prime cosets. This file sets up the
generators and proves the surjectivity half for `n = 1` and `n = 2`. The injectivity half —
algebraic independence of the generators — and the resulting isomorphisms live in the companion
file `PolynomialRing/Injective.lean`, which consumes `evalHom_def` and `evalHom_apply` from
here.

## Main definitions

* `HeckeRing.GLn.heckeGen k` — the `k`-th generator `T(1, …, 1, p, …, p)`, with `k + 1` entries
  equal to `p`.
* `HeckeRing.GLn.evalHom` — evaluation of `ℤ[X₁, …, Xₙ]` at the generators, into the ambient
  Hecke ring.
* `HeckeRing.GLn.evalHomLocal` — the same map with codomain `pLocalSubring n p`, which is the
  presentation map Theorem 3.20 is about.

## Main results

* `HeckeRing.GLn.evalHomLocal_two_surjective`,
  `HeckeRing.GLn.evalHomLocal_one_surjective`: the presentation is onto, `ℤ[X₁, X₂] ↠ R_p` and
  `ℤ[X₁] ↠ R_p` — the surjectivity half of Theorem 3.20 at `n = 2` and `n = 1`.
* `HeckeRing.GLn.heckeGen_mem_pLocalSubring`: each generator lies in `pLocalSubring`.
* `HeckeRing.GLn.pLocalSubring_two_le_evalHom_range`,
  `HeckeRing.GLn.pLocalSubring_one_le_evalHom_range`: the underlying inclusions of
  `pLocalSubring` into the range of `evalHom`, from which the two surjectivity statements
  above are read off.

## Implementation notes

The roadmap records that general `n` needs two further steps (uniqueness of the leading
double coset in the triangular expansion, and recovery of the generator exponents from the
leading elementary-divisor vector); those are not formalised in the source and are not
ported. Only the `n = 1` and `n = 2` cases below are proved, and they are the ones the
classical theory consumes.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), first three sections.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

/-- The `CommSemiring` structure this module needs on `IntegralHeckeRing n`, rebuilt **locally**
from the two public ingredients `HeckeCosetModule.instSemiringHeckeRing` and
`HeckeCosetModule.mul_comm_of_antiInvolution`.

`commSemiringIntegralHeckeRing` already packages exactly this, but as a sealed `def`: its body
does not reduce across the module boundary, so the `NonAssocSemiring` it carries is not
*definitionally* the ambient one and `MvPolynomial.eval₂Hom` will not typecheck against it.
Writing the same structure here makes its body transparent where it is needed and nowhere else,
which is why the upstream definitions stay sealed rather than `@[expose]`d. -/
noncomputable local instance commSemiringIntegralHeckeRingLocal [NeZero n] :
    CommSemiring (IntegralHeckeRing n) :=
  { (HeckeCosetModule.instSemiringHeckeRing ℤ : Semiring (IntegralHeckeRing n)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution n)
      (transposeAntiInvolution_onHeckeCoset_eq_self n) }

section TGen

variable (p : ℕ) (hp : p.Prime)

/-- The diagonal for the k-th generator: `(1,...,1,p,...,p)` with `n-1-k` ones
    followed by `k+1` entries of `p`. Here `k : Fin n`, giving `n` generators. -/
def heckeGenDiag (k : Fin n) : Fin n → ℕ :=
  fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p

@[simp]
lemma heckeGenDiag_apply (k : Fin n) (i : Fin n) :
    heckeGenDiag n p k i =
    if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p :=
  -- `(rfl)` rather than `rfl`: `heckeGenDiag` is not `@[expose]`d, so the parentheses opt out
  -- of exporting the definitional equality this lemma exists to replace.
  (rfl)

/-- At `n = 1` the generator diagonal is the constant `p`: the index condition
`i < 1 - 1 - 0` is never satisfied. -/
lemma heckeGenDiag_one_eq_const (p : ℕ) : heckeGenDiag 1 p (0 : Fin 1) = fun _ ↦ p := by
  funext i; simp [heckeGenDiag_apply]

/-- The heckeGen diagonal has p-power entries (each entry is 1 = p^0 or p = p^1). -/
lemma heckeGenDiag_eq_primePowDiag (k : Fin n) :
    heckeGenDiag n p k =
    primePowDiag n p (fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  funext i
  simp only [heckeGenDiag_apply, primePowDiag_apply]
  split_ifs <;> simp

/-- The exponent function for heckeGen is monotone. -/
lemma heckeGen_exp_monotone (k : Fin n) :
    Monotone (fun i : Fin n ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  intro i j hij
  simp only
  split_ifs <;> omega

variable [NeZero n]

include hp
/-- The k-th generator of pLocalSubring: `T(1,...,1,p,...,p)` with `k+1` entries of `p`. -/
noncomputable def heckeGen (k : Fin n) : IntegralHeckeRing n :=
  diagElem (heckeGenDiag n p k)

omit hp [NeZero n] in
/-- Defining equation for the sealed definition `heckeGen`. -/
lemma heckeGen_def (k : Fin n) : heckeGen n p k = diagElem (heckeGenDiag n p k) := (rfl)

omit hp in
/-- Each generator lies in the `p`-local subsemiring `R_p`. -/
lemma heckeGen_mem_pLocalSubring (k : Fin n) : heckeGen n p k ∈ pLocalSubring n p := by
  have h_eq : heckeGen n p k =
      diagElem (primePowDiag n p (fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1)) :=
    congrArg diagElem (heckeGenDiag_eq_primePowDiag n p k)
  rw [h_eq]
  exact diagElem_primePowDiag_mem_pLocalSubring n p _ (heckeGen_exp_monotone n k)

omit hp

end TGen

section PolynomialRing

variable [NeZero n] (p : ℕ) (hp : p.Prime)

/-- Evaluation homomorphism: `Xₖ ↦ heckeGen k`.
    Maps `ℤ[X₁,...,Xₙ]` into the Hecke algebra. -/
noncomputable def evalHom : MvPolynomial (Fin n) ℤ →+* IntegralHeckeRing n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (IntegralHeckeRing n)) (fun k ↦ heckeGen n p k)

/-- Defining equation for the sealed definition `evalHom`: evaluation of a polynomial at the
generators, with integer coefficients cast into the Hecke ring. -/
lemma evalHom_def : evalHom n p =
    MvPolynomial.eval₂Hom (Int.castRingHom (IntegralHeckeRing n)) (fun k ↦ heckeGen n p k) :=
  (rfl)

/-- `evalHom` sends the `k`-th variable to the `k`-th generator. -/
@[simp] lemma evalHom_X (k : Fin n) : evalHom n p (MvPolynomial.X k) = heckeGen n p k :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- `evalHom` sends a constant to its image under `ℤ → IntegralHeckeRing n`.

Deliberately not `@[simp]`: `simp` already discharges this through `eq_intCast` and
`map_intCast`, `evalHom` being a ring hom, and `simpNF` rejects the redundant marking. The
lemma is kept as the named computation rule for `rw`. -/
lemma evalHom_C (a : ℤ) : evalHom n p (MvPolynomial.C a) = (a : IntegralHeckeRing n) :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- **Evaluation rule for `evalHom` at a double coset.** The coefficient of `evalHom P` at `D`
is the sum, over the support of `P`, of `P.coeff d` times the coefficient of the monomial
`∏ heckeGen i ^ d i` at `D`.

This is the wrapper-level counterpart of `evalHom_def`: it is stated here, where `evalHom` and
`IntegralHeckeRing` are both transparent, so that consumers can evaluate a polynomial image at
a coset without depending on either definition reducing at their own use site. -/
lemma evalHom_apply (P : MvPolynomial (Fin n) ℤ)
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    evalHom n p P D =
      ∑ d ∈ P.support, P.coeff d • (∏ i, heckeGen n p i ^ d i : IntegralHeckeRing n) D := by
  rw [evalHom_def, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  refine (Finset.sum_apply' D).trans (Finset.sum_congr rfl fun d _ ↦ ?_)
  -- beta-reduce the cast left by `eval₂_eq'`, then turn the `ℤ`-multiple into a `ℤ`-scalar so
  -- that the wrapper's own `smul_apply` closes the goal
  change (((P.coeff d : ℤ) : IntegralHeckeRing n) * ∏ i, heckeGen n p i ^ d i) D = _
  rw [← zsmul_one (P.coeff d), smul_mul_assoc, one_mul]
  exact HeckeCosetModule.smul_apply _ _ _

/-- Each `heckeGen k` lies in the range of `evalHom`. -/
lemma heckeGen_mem_evalHom_range (k : Fin n) :
    heckeGen n p k ∈ (evalHom n p).range :=
  ⟨MvPolynomial.X k, MvPolynomial.eval₂Hom_X' _ _ _⟩

/-- Every value of `evalHom` lies in `R_p`: the generators do, and `pLocalSubring` is a subring,
so it absorbs the constants, sums and products that build an arbitrary polynomial. -/
lemma evalHom_mem_pLocalSubring (f : MvPolynomial (Fin n) ℤ) :
    evalHom n p f ∈ pLocalSubring n p := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [evalHom_C]; exact intCast_mem (pLocalSubring n p) a
  | add q r hq hr => rw [map_add]; exact (pLocalSubring n p).add_mem hq hr
  | mul_X q k hq =>
    rw [map_mul, evalHom_X]
    exact (pLocalSubring n p).mul_mem hq (heckeGen_mem_pLocalSubring n p k)

/-- The evaluation homomorphism with its true codomain: `ℤ[X₁, …, Xₙ] →+* R_p`.

`evalHom` lands in the ambient Hecke ring, which makes the results below mere inclusions;
this is the map whose surjectivity is the presentation statement of Theorem 3.20. -/
noncomputable def evalHomLocal : MvPolynomial (Fin n) ℤ →+* pLocalSubring n p :=
  (evalHom n p).codRestrict _ (evalHom_mem_pLocalSubring n p)

@[simp] lemma evalHomLocal_coe (f : MvPolynomial (Fin n) ℤ) :
    (evalHomLocal n p f : IntegralHeckeRing n) = evalHom n p f := (rfl)

/-- The computation rule of the presentation map: the `k`-th variable goes to the `k`-th
generator, taken in `pLocalSubring` rather than in the ambient ring. -/
@[simp] lemma evalHomLocal_X (k : Fin n) :
    evalHomLocal n p (MvPolynomial.X k) = ⟨heckeGen n p k, heckeGen_mem_pLocalSubring n p k⟩ :=
  Subtype.ext (evalHom_X n p k)

end PolynomialRing



open HeckeRing.GL2

/-- `heckeGen 2 p 0 = heckeTDiag 1 p`: the first generator is `T(1,p)`.

Positivity, not primality: nothing here needs `p` prime. -/
lemma heckeGen_zero_eq_heckeTDiag (p : ℕ) (hp : 0 < p) :
    heckeGen 2 p (0 : Fin 2) = heckeTDiag 1 p := by
  rw [heckeGen_def]
  have h : heckeGenDiag 2 p (0 : Fin 2) = ![1, p] := by
    funext i; simp only [heckeGenDiag_apply]; fin_cases i <;> simp
  rw [h, heckeTDiag_eq_diagElem Nat.one_pos hp (one_dvd _)]

/-- `heckeGen 2 p 1 = heckeTScalar p`: the second generator is the diamond operator.

Positivity, not primality, for the same reason as `heckeGen_zero_eq_heckeTDiag`. -/
lemma heckeGen_one_eq_heckeTScalar (p : ℕ) (hp : 0 < p) :
    heckeGen 2 p (1 : Fin 2) = heckeTScalar p := by
  rw [heckeGen_def]
  have h : heckeGenDiag 2 p (1 : Fin 2) = ![p, p] := by
    funext i; simp only [heckeGenDiag_apply]; fin_cases i <;> simp
  rw [h, heckeTScalar_of_pos hp]
  exact congrArg diagElem (funext fun i ↦ by fin_cases i <;> rfl)

/-- `heckeT(p) = heckeGen 0`: the sum T(p) is the first generator for p prime. -/
lemma heckeT_prime_eq_heckeGen_zero (p : ℕ) (hp : p.Prime) :
    heckeT ⟨p, hp.pos⟩ = heckeGen 2 p (0 : Fin 2) := by
  rw [heckeGen_zero_eq_heckeTDiag p hp.pos, heckeT_prime p hp]

private lemma heckeTScalar_mem_range (p : ℕ) (hp : p.Prime) :
    heckeTScalar p ∈ (evalHom 2 p).range := by
  rw [← heckeGen_one_eq_heckeTScalar p hp.pos]; exact heckeGen_mem_evalHom_range 2 p 1

/-- `heckeT(p^k)` lies in the range of the evaluation homomorphism, for all `k`. -/
lemma heckeT_prime_pow_mem_evalHom_range (p : ℕ) (hp : p.Prime) (k : ℕ) :
    heckeT ⟨p ^ k, pow_pos hp.pos k⟩ ∈ (evalHom 2 p).range := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
  match k with
  | 0 =>
    -- `p ^ 0` also occurs inside the `ℕ+` index's positivity proof, so `pow_zero` cannot
    -- rewrite it; `congr 1` reduces to the index equality, which is decided structurally.
    rw [show heckeT ⟨p ^ 0, pow_pos hp.pos 0⟩ = heckeT 1 from by congr 1, heckeT_one]
    exact (evalHom 2 p).range.one_mem
  | 1 =>
    have h1 : heckeT ⟨p ^ 1, pow_pos hp.pos 1⟩ = heckeT ⟨p, hp.pos⟩ := by
      congr 1; exact Subtype.ext (pow_one p)
    rw [h1, heckeT_prime_eq_heckeGen_zero p hp]; exact heckeGen_mem_evalHom_range 2 p 0
  | k + 2 =>
    have h_rec := heckeT_prime_pow_recurrence p hp (k + 1) (by omega)
    -- The recurrence is stated at index `k + 1`; truncated ℕ-subtraction writes its two
    -- exponents as `k + 1 - 1` and `k + 1 + 1`, which only `omega` identifies with `k`/`k + 2`.
    rw [show k + 1 - 1 = k from by omega, show k + 1 + 1 = k + 2 from by omega] at h_rec
    rw [h_rec, heckeT_prime_eq_heckeGen_zero p hp]
    exact (evalHom 2 p).range.sub_mem
      ((evalHom 2 p).range.mul_mem (heckeGen_mem_evalHom_range 2 p 0) (ih (k + 1) (by omega)))
      ((evalHom 2 p).range.zsmul_mem
        ((evalHom 2 p).range.mul_mem (heckeTScalar_mem_range p hp) (ih k (by omega))) (p : ℤ))

/-- `heckeTDiag(1, p^k)` lies in the range of the evaluation homomorphism. -/
lemma heckeTDiag_one_prime_pow_mem_evalHom_range (p : ℕ) (hp : p.Prime) (k : ℕ) :
    heckeTDiag 1 (p ^ k) ∈ (evalHom 2 p).range := by
  match k with
  | 0 => simp only [pow_zero, heckeTDiag_one_one]; exact (evalHom 2 p).range.one_mem
  | 1 =>
    rw [pow_one, ← heckeGen_zero_eq_heckeTDiag p hp.pos]
    exact heckeGen_mem_evalHom_range 2 p 0
  | k + 2 =>
    -- Same truncated-subtraction normalisation: the telescoping identity returns `k + 2 - 2`.
    rw [heckeTDiag_one_prime_pow_eq p hp (k + 2) (by omega), show k + 2 - 2 = k from by omega]
    exact (evalHom 2 p).range.sub_mem (heckeT_prime_pow_mem_evalHom_range p hp (k + 2))
      ((evalHom 2 p).range.mul_mem (heckeTScalar_mem_range p hp)
        (heckeT_prime_pow_mem_evalHom_range p hp k))

/-- `diagElem (primePowDiag 2 p e)` is in the evalHom range when `e` is monotone. -/
lemma diagElem_primePowDiag_mem_evalHom_range (p : ℕ) (hp : p.Prime) (e : Fin 2 → ℕ)
    (hmono : Monotone e) :
    diagElem (primePowDiag 2 p e) ∈ (evalHom 2 p).range := by
  -- Factor out the scalar `p ^ e 0`; the cofactor is `T(1, p ^ (e 1 - e 0))`. This covers
  -- `e 0 = 0` too, where the scalar factor is `1`, so no case split is needed.
  have h_le : e 0 ≤ e 1 := hmono (Fin.zero_le _)
  have h_eq : primePowDiag 2 p e = (fun _ ↦ p ^ (e 0)) * primePowDiag 2 p ![0, e 1 - e 0] := by
    funext i
    simp only [primePowDiag_apply, Pi.mul_apply]
    fin_cases i
    · simp
    · -- the second entry splits as `p ^ e 0 * p ^ (e 1 - e 0)` since `e 0 ≤ e 1`
      simp [Matrix.cons_val_one, ← pow_add, Nat.add_sub_cancel' h_le]
  rw [congrArg diagElem h_eq,
    ← diagElem_const_mul 2 (p ^ (e 0)) (pow_pos hp.pos _) (primePowDiag 2 p ![0, e 1 - e 0])
      (primePowDiag_pos 2 p hp.pos _)]
  apply (evalHom 2 p).range.mul_mem
  · rw [← heckeTScalar_pow p hp.pos (e 0), ← heckeGen_one_eq_heckeTScalar p hp.pos]
    exact (evalHom 2 p).range.pow_mem (heckeGen_mem_evalHom_range 2 p 1) _
  · have h2 : primePowDiag 2 p ![0, e 1 - e 0] = ![1, p ^ (e 1 - e 0)] := by
      funext i; simp only [primePowDiag_apply]; fin_cases i <;> simp
    rw [congrArg diagElem h2,
      ← heckeTDiag_eq_diagElem Nat.one_pos (pow_pos hp.pos _) (one_dvd _)]
    exact heckeTDiag_one_prime_pow_mem_evalHom_range p hp (e 1 - e 0)

/-- Surjectivity of `evalHom` at `n = 2`: `pLocalSubring 2 p` lies in the range of the
evaluation homomorphism `ℤ[X₁, X₂] → IntegralHeckeRing 2`. Together with
`heckeGen_mem_pLocalSubring` for the reverse inclusion, the two generators `T(1, p)` and
`T(p, p)` therefore generate the whole `p`-local Hecke ring of `GL₂`. -/
theorem pLocalSubring_two_le_evalHom_range (p : ℕ) (hp : p.Prime) :
    pLocalSubring 2 p ≤ (evalHom 2 p).range :=
  have : NeZero p := ⟨hp.pos.ne'⟩
  (pLocalSubring_le_iff 2 p _).2 fun e hmono ↦
    diagElem_primePowDiag_mem_evalHom_range p hp e hmono




/-- Surjectivity of `evalHom` at `n = 1`: `pLocalSubring 1 p` lies in the range of `evalHom`.
The `p`-local Hecke ring of `GL₁` is generated by the single element `T(p)`. -/
theorem pLocalSubring_one_le_evalHom_range (p : ℕ) (hp : 0 < p) :
    pLocalSubring 1 p ≤ (evalHom 1 p).range :=
  have : NeZero p := ⟨hp.ne'⟩
  (pLocalSubring_le_iff 1 p _).2 fun e _hmono ↦ by
  have he : primePowDiag 1 p e = fun _ ↦ p ^ (e 0) := by
    funext i
    simp only [primePowDiag_apply]
    congr 1
    exact congr_arg e (Subsingleton.elim i 0)
  rw [congrArg diagElem he, ← diagElem_const_pow 1 p hp (e 0),
    -- `heckeGenDiag 1 p 0` is a `Fin 1 → ℕ` that is only *extensionally* the constant `p`,
    -- so the two `diagElem` arguments are not syntactically equal and `rw` cannot match them.
    show diagElem (fun _ : Fin 1 ↦ p) = heckeGen 1 p (0 : Fin 1) from by
      rw [heckeGen_def]; exact (congrArg diagElem (heckeGenDiag_one_eq_const p)).symm]
  exact (evalHom 1 p).range.pow_mem (heckeGen_mem_evalHom_range 1 p 0) _

/-- **The presentation is onto at `n = 2`**: `ℤ[X₁, X₂] ↠ R_p`, the surjectivity half of
Shimura's Theorem 3.20. This is the inclusion above read through `evalHomLocal`, whose codomain
is `R_p` itself. -/
theorem evalHomLocal_two_surjective (p : ℕ) (hp : p.Prime) :
    Function.Surjective (evalHomLocal 2 p) := by
  rintro ⟨y, hy⟩
  obtain ⟨f, hf⟩ := pLocalSubring_two_le_evalHom_range p hp hy
  exact ⟨f, Subtype.ext hf⟩

/-- **The presentation is onto at `n = 1`**: `ℤ[X₁] ↠ R_p`. -/
theorem evalHomLocal_one_surjective (p : ℕ) (hp : 0 < p) :
    Function.Surjective (evalHomLocal 1 p) := by
  rintro ⟨y, hy⟩
  obtain ⟨f, hf⟩ := pLocalSubring_one_le_evalHom_range p hp hy
  exact ⟨f, Subtype.ext hf⟩

end HeckeRing.GLn
