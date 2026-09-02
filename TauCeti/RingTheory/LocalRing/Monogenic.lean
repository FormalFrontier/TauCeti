/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Monogenicity of a finite extension of discrete valuation rings

Let `S` be a discrete valuation ring, finite over a discrete valuation subring `R`, and assume
the residue extension `𝓀(S)/𝓀(R)` is separable.  This file proves that `S = R[β]` for a single
`β : S`.  Both the ramified and the unramified case are covered; Mathlib's
`IsLocalRing.exists_adjoin_eq_top` covers only the unramified (finite étale) case, where the
generator may be taken to be any lift of a primitive element of the residue extension.

The proof is Serre's: pick a lift `a` of a primitive element of the residue extension and a
polynomial `g : R[X]` lifting its minimal polynomial.  Then `g(a)` lies in the maximal ideal and
`g'(a)` is a unit, so one Newton step, replacing `a` by `a + π` for a uniformizer `π` when it is
needed, arranges
that `g(β)` *generates* the maximal ideal.  The subring `R[β]` then meets every residue class
modulo `𝓂(S)` and contains a uniformizer, hence meets every residue class modulo `𝓂(S) ^ n`;
taking `n` large enough that `𝓂(S) ^ n ⊆ 𝓂(R) S`, Nakayama's lemma gives `R[β] = S`.

## Main results

* `TauCeti.IsLocalRing.exists_span_eval_eq_maximalIdeal`: the Newton step.
* `TauCeti.IsDiscreteValuationRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal`: the criterion
  for a single element to generate `S` over `R`.
* `TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top`: a finite extension of discrete
  valuation rings with separable residue extension is monogenic.
* `TauCeti.IsDiscreteValuationRing.adjoin_eq_top_of_irreducible`: in the totally ramified case
  every uniformizer of `S` is a generator.
* `TauCeti.Algebra.powerBasisOfAdjoinEqTop`: the power basis attached to a generator, and
  `TauCeti.IsDiscreteValuationRing.nonempty_powerBasis`, the integral basis it produces here.

## References

* [J.-P. Serre, *Corps locaux*][serre1968], Chapter III, §6, Proposition 12.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

namespace IsLocalRing

section Newton

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- **Newton step at a principal maximal ideal.**  If `π` generates the maximal ideal of a local
ring `S`, and `f : S[X]` has a simple root at `a` modulo `𝓂(S)`, then `f` takes a value generating
`𝓂(S)` at some `b` congruent to `a` modulo `𝓂(S)`: either `a` itself works, or `a + π` does. -/
theorem exists_span_eval_eq_maximalIdeal {f : S[X]} {a π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) (ha : f.eval a ∈ maximalIdeal S)
    (ha' : IsUnit ((derivative f).eval a)) :
    ∃ b : S, b - a ∈ maximalIdeal S ∧ Ideal.span {f.eval b} = maximalIdeal S := by
  have hπmem : π ∈ maximalIdeal S := hπ ▸ Ideal.subset_span rfl
  by_cases h : Ideal.span {f.eval a} = maximalIdeal S
  · exact ⟨a, by simp, h⟩
  refine ⟨a + π, by simpa using hπmem, ?_⟩
  -- The failure of `a` forces `f.eval a ∈ 𝓂(S) ^ 2`, say `f.eval a = π ^ 2 * d`.
  obtain ⟨u, hu⟩ : ∃ u, f.eval a = π * u :=
    Ideal.mem_span_singleton.mp (hπ ▸ ha)
  have hu' : u ∈ maximalIdeal S := by
    by_contra hu'
    exact h (by rw [hu, Ideal.span_singleton_mul_right_unit (notMem_maximalIdeal.mp hu'), hπ])
  obtain ⟨d, hd⟩ : ∃ d, u = π * d := Ideal.mem_span_singleton.mp (hπ ▸ hu')
  obtain ⟨k, hk⟩ := binomExpansion f a π
  -- Now `f.eval (a + π) = π * ((derivative f).eval a + π * (d + k))`, with a unit on the right.
  have hfac : f.eval (a + π) = π * ((derivative f).eval a + π * (d + k)) := by
    rw [hk, hu, hd]; ring
  have hunit : IsUnit ((derivative f).eval a + π * (d + k)) := by
    refine notMem_maximalIdeal.mp fun hmem => notMem_maximalIdeal.mpr ha' ?_
    simpa using sub_mem hmem (Ideal.mul_mem_right (d + k) _ hπmem)
  rw [hfac, Ideal.span_singleton_mul_right_unit hunit, hπ]

end Newton

section Nakayama

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]

/-- If a subalgebra `T` meets every residue class of `S` modulo the maximal ideal and contains a
generator `π` of that maximal ideal, then it meets every residue class modulo any power of the
maximal ideal. -/
theorem sup_maximalIdeal_pow_eq_top {T : Subalgebra R S} {π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ (maximalIdeal S).restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (maximalIdeal S ^ n).restrictScalars R = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : maximalIdeal S ^ n = Ideal.span {π ^ n} := by
      rw [← hπ, Ideal.span_singleton_pow]
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (ih ▸ Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, m = π ^ n * u := by
      rw [Submodule.restrictScalars_mem, hpow, Ideal.mem_span_singleton] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (h ▸ Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + π ^ n * t', ?_, π ^ n * m', ?_, by ring⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem (pow_mem hπT n) ht')
    · rw [Submodule.restrictScalars_mem, pow_succ]
      exact Ideal.mul_mem_mul (hpow ▸ Ideal.mem_span_singleton_self _) hm'

end Nakayama

section Residue

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- If the residue of `β` generates the residue field extension, then `R[β]` meets every residue
class of `S` modulo the maximal ideal.  The proof is the forward half of Mathlib's
`IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top`, stopped one step earlier: that lemma
concludes with `𝓂(R) S` in place of `𝓂(S)`, which needs `S` unramified over `R` so that the two
ideals agree.  Here they do not, and the gap between them is closed instead by
`TauCeti.IsLocalRing.sup_maximalIdeal_pow_eq_top`. -/
theorem sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top {β : S}
    (hβ : Algebra.adjoin (ResidueField R) {residue S β} = ⊤) :
    (Algebra.adjoin R {β}).toSubmodule ⊔ (maximalIdeal S).restrictScalars R = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hβ
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨p, hp⟩ := hβ (residue S s)
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective _ residue_surjective p
  rw [← map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl] at hp
  refine Submodule.mem_sup.mpr ⟨aeval β q, ?_, s - aeval β q, ?_, by ring⟩
  · rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  · rw [Submodule.restrictScalars_mem, ← Ideal.Quotient.eq]
    exact hp.symm

end Residue

end IsLocalRing

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsIntegrallyClosed R] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- The power basis `1, β, …, β ^ (n - 1)` of `S` over `R` attached to a generator `β` of `S` as
an `R`-algebra, where `n` is the degree of the minimal polynomial of `β`.  This transports
Mathlib's `Algebra.adjoin.powerBasis'` along `Algebra.adjoin R {β} = ⊤`, and packages the integral
basis that a consumer of `TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top` wants. -/
noncomputable def powerBasisOfAdjoinEqTop {β : S} (h : Algebra.adjoin R {β} = ⊤) :
    PowerBasis R S :=
  (Algebra.adjoin.powerBasis' (IsIntegral.of_finite R β)).map
    ((Subalgebra.equivOfEq _ _ h).trans Subalgebra.topEquiv)

@[simp]
theorem powerBasisOfAdjoinEqTop_gen {β : S} (h : Algebra.adjoin R {β} = ⊤) :
    (powerBasisOfAdjoinEqTop h).gen = β := by
  simp [powerBasisOfAdjoinEqTop]

@[simp]
theorem powerBasisOfAdjoinEqTop_dim {β : S} (h : Algebra.adjoin R {β} = ⊤) :
    (powerBasisOfAdjoinEqTop h).dim = (minpoly R β).natDegree :=
  (rfl)

end Algebra

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [Module.Finite R S]
  [FaithfulSMul R S]

omit [Module.Finite R S] in
/-- The maximal ideal of `S` is nilpotent modulo the ideal generated by the maximal ideal of `R`:
some power of `𝓂(S)` lies in `𝓂(R) S`.  The exponent that works is the ramification index. -/
theorem exists_maximalIdeal_pow_le_map :
    ∃ n : ℕ, maximalIdeal S ^ n ≤ (maximalIdeal R).map (algebraMap R S) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  have hne : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := by
    refine fun hbot => (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr
      hϖ.ne_zero ?_
    exact (Submodule.eq_bot_iff _).mp hbot _
      (Ideal.mem_map_of_mem _ (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ))
  obtain ⟨n, hn⟩ := _root_.IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hπ
  exact ⟨n, by rw [hn, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

/-- **The generation criterion.**  An element `β` of `S` generates `S` as an `R`-algebra as soon as
its residue generates the residue field extension and some polynomial in `β` with coefficients in
`R` generates the maximal ideal of `S`. -/
theorem adjoin_eq_top_of_span_eval_eq_maximalIdeal {β : S} {g : R[X]}
    (hres : Algebra.adjoin (ResidueField R) {residue S β} = ⊤)
    (hgen : Ideal.span {aeval β g} = maximalIdeal S) :
    Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_map (R := R) (S := S)
  have hmem : aeval β g ∈ Algebra.adjoin R {β} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, rfl⟩
  have hsup := TauCeti.IsLocalRing.sup_maximalIdeal_pow_eq_top hgen hmem
    (TauCeti.IsLocalRing.sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top hres) n
  rw [← Algebra.toSubmodule_eq_top]
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (maximalIdeal_le_jacobson ⊥) ?_)
  rw [Ideal.smul_top_eq_map]
  exact hsup.ge.trans (sup_le_sup_left (Submodule.restrictScalars_mono R hn) _)

/-- **Local monogenicity.**  A finite extension of discrete valuation rings whose residue
extension is separable is generated by a single element.  Completeness of `R` is not needed: it
enters the classical statement only to guarantee that the integral closure of `R` in a finite
field extension is again a discrete valuation ring, which is here a hypothesis on `S`. -/
theorem exists_adjoin_eq_top [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    ∃ β : S, Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField S)
  obtain ⟨a, rfl⟩ := residue_surjective (R := S) α
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  -- A lift `g : R[X]` of the minimal polynomial of the residue of `a`.
  obtain ⟨g, hg⟩ := (mem_lifts _).mp
    (mem_lifts_of_surjective residue_surjective (minpoly (ResidueField R) (residue S a)))
  have hbridge : ∀ x : S, residue S (aeval x g) =
      aeval (residue S x) (minpoly (ResidueField R) (residue S a)) := fun x => by
    rw [map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl, hg]
  have hbridge' : ∀ x : S, residue S (aeval x (derivative g)) =
      aeval (residue S x) (derivative (minpoly (ResidueField R) (residue S a))) := fun x => by
    rw [map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl, ← derivative_map, hg]
  -- `g` has a simple root at `a` modulo the maximal ideal, so a Newton step applies.
  have hval : (g.map (algebraMap R S)).eval a ∈ maximalIdeal S := by
    rw [eval_map, ← aeval_def, ← residue_eq_zero_iff]
    exact (hbridge a).trans (minpoly.aeval _ _)
  have hder : IsUnit ((derivative (g.map (algebraMap R S))).eval a) := by
    rw [derivative_map, eval_map, ← aeval_def, ← residue_ne_zero_iff_isUnit, hbridge' a]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβa, hβ⟩ := TauCeti.IsLocalRing.exists_span_eval_eq_maximalIdeal
    hπ.maximalIdeal_eq.symm hval hder
  have hres : residue S β = residue S a := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hβa
  refine ⟨β, adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := g) ?_ ?_⟩
  · rw [hres, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite _ _), hα, IntermediateField.top_toSubalgebra]
  · rwa [aeval_def, ← eval_map]

/-- A finite extension of discrete valuation rings with separable residue extension admits a
power basis. -/
theorem nonempty_powerBasis [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    Nonempty (PowerBasis R S) :=
  let ⟨_, h⟩ := exists_adjoin_eq_top (R := R) (S := S)
  ⟨TauCeti.Algebra.powerBasisOfAdjoinEqTop h⟩

/-- **The totally ramified case.**  If the residue extension is trivial, every uniformizer of `S`
generates `S` over `R`.  This is the direction of the Eisenstein description of a totally ramified
extension that produces an integral power basis. -/
theorem adjoin_eq_top_of_irreducible
    (hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    {π : S} (hπ : Irreducible π) : Algebra.adjoin R {π} = ⊤ := by
  refine adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := X) ?_ (by simpa using
    hπ.maximalIdeal_eq.symm)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := hsurj x
  exact Subalgebra.algebraMap_mem _ y

end IsDiscreteValuationRing

end TauCeti
