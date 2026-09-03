/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Kummer–Dedekind: the primes over `p`, with their residue degrees and ramification indices

Let `R` be an integrally closed domain, let `S` be a Dedekind domain that is a torsion-free
`R`-algebra, let `x : S` be integral over `R`, and let `p` be a nonzero maximal ideal of `R` that
is prime to the conductor of `R[x]` in `S`.  Mathlib's `KummerDedekind` file matches the prime
factors of `p S` with the irreducible factors of `minpoly R x` modulo `p`, and matches their
multiplicities.  This file turns that match into the form ramification theory uses: a bijection

`p.primesOver S ≃ {normalized irreducible factors of minpoly R x mod p}`

under which the **residue degree** of a prime is the degree of the matching polynomial factor and
its **ramification index** is the multiplicity of that factor.  Together these say that the
factorization of `minpoly R x` modulo `p` computes the splitting of `p` in `S` completely, which
is the content of the Kummer–Dedekind criterion as it is used in practice.

The prime attached to a factor is explicit: it is `span (p S ∪ {Q (x)})` for any lift `Q` of the
factor, so the bijection can be evaluated on a concrete example.

## Main definitions

* `TauCeti.KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk`: the bijection between the
  primes of `S` over `p` and the normalized irreducible factors of `minpoly R x` modulo `p`.
* `TauCeti.KummerDedekind.quotientEquivQuotientSpan`: the isomorphism
  `(R ⧸ p)[X] ⧸ (Q) ≃+* S ⧸ span (p S ∪ {Q (x)})` for `Q` a lift of such a factor, which computes
  the residue field at the attached prime.

## Main results

* `TauCeti.KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk_symm_apply_coe`: the prime
  attached to the class of `Q` is `span (p S ∪ {Q (x)})`.
* `TauCeti.KummerDedekind.inertiaDeg_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply`: its
  residue degree is the degree of the factor.
* `TauCeti.KummerDedekind.ramificationIdx_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply`:
  its ramification index is the multiplicity of the factor in `minpoly R x` modulo `p`.

## Provenance

These are the arbitrary-Dedekind-domain form of Xavier Roblot's
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`,
`NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply` and
`NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply` of
`Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean`, and the proofs follow his, with the
`ℤ`-to-`ZMod p` plumbing that his statements need dropped.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, Proposition 8.3.
-/

public section

open Ideal Polynomial UniqueFactorizationMonoid

namespace TauCeti

namespace KummerDedekind

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
variable {x : S} {p : Ideal R}

variable (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
  (hx : (conductor R x).comap (algebraMap R S) ⊔ p = ⊤) (hx' : IsIntegral R x)

attribute [local instance] Ideal.Quotient.field

include hp hp0 hx hx'

open scoped Classical in
/-- **The Kummer–Dedekind criterion**: the primes of `S` lying over a nonzero maximal ideal `p` of
`R` prime to the conductor of `R[x]` correspond to the normalized irreducible factors of
`minpoly R x` modulo `p`. -/
noncomputable def primesOverEquivNormalizedFactorsMinPolyMk :
    p.primesOver S ≃
      {d : (R ⧸ p)[X] | d ∈ normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))} :=
  (Set.equivOfEq (Set.ext fun _ ↦
    Ideal.mem_primesOver_iff_mem_normalizedFactors S hp0)).trans
      (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hp hp0 hx hx')

open scoped Classical in
/-- The prime of `S` attached by
`TauCeti.KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk` to the class modulo `p` of a
lift `Q` is spanned by `p S` together with `Q (x)`. -/
theorem primesOverEquivNormalizedFactorsMinPolyMk_symm_apply_coe {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk p) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) :
    (((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm
        ⟨Q.map (Ideal.Quotient.mk p), hQ⟩ : p.primesOver S) : Ideal S) =
      span (p.map (algebraMap R S) ∪ {aeval x Q}) :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    hp hQ hp0 hx hx'

omit hp0 in
open scoped Classical in
/-- **The residue ring at a Kummer–Dedekind factor**: for `Q` a lift of a normalized irreducible
factor of `minpoly R x` modulo `p`, the quotient of `S` by the prime `span (p S ∪ {Q (x)})`
attached to that factor is `(R ⧸ p)[X]` modulo the factor. -/
noncomputable def quotientEquivQuotientSpan {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk p) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) :
    (R ⧸ p)[X] ⧸ span {Q.map (Ideal.Quotient.mk p)} ≃+*
      S ⧸ span (p.map (algebraMap R S) ∪ {aeval x Q}) :=
  have h0 : (minpoly R x).map (Ideal.Quotient.mk p) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic hx')
  have h₁ : span {Q.map (Ideal.Quotient.mk p)} =
      span {(minpoly R x).map (Ideal.Quotient.mk p)} ⊔ span {Q.map (Ideal.Quotient.mk p)} := by
    rw [← span_insert, span_pair_comm, span_pair_eq_span_left_iff_dvd.mpr]
    exact ((Polynomial.mem_normalizedFactors_iff h0).mp hQ).2.2
  have h₂ : p.map (algebraMap R S) ⊔ span {aeval x Q} =
      span (p.map (algebraMap R S) ∪ {aeval x Q}) := by
    rw [span_union, span_eq]
  ((Ideal.quotEquivOfEq h₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv _ (Ideal.map (Ideal.Quotient.mk (p.map (algebraMap R S)))
        (span {aeval x Q}))
      (KummerDedekind.quotMapEquivQuotQuotMap hx hx').symm (by
        simp [Ideal.map_span,
          KummerDedekind.quotMapEquivQuotQuotMap_symm_apply hx hx' Q])).trans <|
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq h₂)

omit hp0 in
open scoped Classical in
/-- `TauCeti.KummerDedekind.quotientEquivQuotientSpan` carries the class of a polynomial `P` over
`R ⧸ p` to the class of `P (x)`. -/
@[simp]
theorem quotientEquivQuotientSpan_mk {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk p) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) (P : R[X]) :
    quotientEquivQuotientSpan hp hx hx' hQ (Ideal.Quotient.mk
        (span {Q.map (Ideal.Quotient.mk p)}) (P.map (Ideal.Quotient.mk p))) =
      Ideal.Quotient.mk (span (p.map (algebraMap R S) ∪ {aeval x Q})) (aeval x P) := by
  simp only [quotientEquivQuotientSpan, RingEquiv.coe_trans, Function.comp_apply,
    Ideal.quotEquivOfEq_mk, DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk,
    DoubleQuot.quotQuotMk, RingHom.coe_comp, Ideal.quotientEquiv_mk,
    KummerDedekind.quotMapEquivQuotQuotMap_symm_apply hx hx' P]
  -- what is left is `DoubleQuot.quotQuotEquivQuotSup_quotQuotMk`, which the previous step has
  -- unfolded past, followed by `Ideal.quotEquivOfEq_mk`; both hold by `rfl`.
  rfl

open scoped Classical in
/-- **The residue degree of a Kummer–Dedekind factor is the degree of the factor**: the prime of
`S` over `p` attached to a normalized irreducible factor `d` of `minpoly R x` modulo `p` has
`Ideal.inertiaDeg` equal to `d.natDegree`. -/
theorem inertiaDeg_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply {d : (R ⧸ p)[X]}
    (hd : d ∈ normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) :
    (((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm ⟨d, hd⟩ :
      p.primesOver S) : Ideal S).inertiaDeg R = d.natDegree := by
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective d
  have hmem := ((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm ⟨_, hd⟩).2
  have hspan := primesOverEquivNormalizedFactorsMinPolyMk_symm_apply_coe hp hp0 hx hx' hd
  have hmax : (span (p.map (algebraMap R S) ∪ {aeval x Q})).IsMaximal :=
    hspan ▸ hmem.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 hmem)
  have hlies : (span (p.map (algebraMap R S) ∪ {aeval x Q})).LiesOver p := hspan ▸ hmem.2
  have : p.IsMaximal := hp
  rw [hspan, Ideal.inertiaDeg_eq_of_isMaximal p _, ← finrank_quotient_span_eq_natDegree
    (K := R ⧸ p) (f := Q.map (Ideal.Quotient.mk p))]
  refine (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl (R ⧸ p))
    (quotientEquivQuotientSpan hp hx hx' hd) ?_).symm
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  simpa [IsScalarTower.algebraMap_apply (R ⧸ p) ((R ⧸ p)[X])
    ((R ⧸ p)[X] ⧸ span {Q.map (Ideal.Quotient.mk p)})] using
    (quotientEquivQuotientSpan_mk hp hx hx' hd (C r)).symm

open scoped Classical in
/-- **The ramification index of a Kummer–Dedekind factor is its multiplicity**: the prime of `S`
over `p` attached to a normalized irreducible factor `d` of `minpoly R x` modulo `p` has
`Ideal.ramificationIdx` equal to the multiplicity of `d` in `minpoly R x` modulo `p`. -/
theorem ramificationIdx_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply {d : (R ⧸ p)[X]}
    (hd : d ∈ normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) :
    (((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm ⟨d, hd⟩ :
        p.primesOver S) : Ideal S).ramificationIdx R =
      multiplicity d ((minpoly R x).map (Ideal.Quotient.mk p)) := by
  have hmem := ((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm ⟨d, hd⟩).2
  have : (((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm ⟨d, hd⟩ :
    p.primesOver S) : Ideal S).IsPrime := hmem.1
  have : (((primesOverEquivNormalizedFactorsMinPolyMk hp hp0 hx hx').symm ⟨d, hd⟩ :
    p.primesOver S) : Ideal S).LiesOver p := hmem.2
  rw [IsDedekindDomain.ramificationIdx_eq_multiplicity p _ (Ideal.map_ne_bot_of_ne_bot hp0)]
  refine multiplicity_eq_of_emultiplicity_eq ?_
  have hfac := (Ideal.mem_primesOver_iff_mem_normalizedFactors S hp0).mp hmem
  rw [KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hp hp0 hx hx' hfac]
  congr 1
  exact congrArg Subtype.val ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    hp hp0 hx hx').apply_symm_apply ⟨d, hd⟩)

end KummerDedekind

end TauCeti
