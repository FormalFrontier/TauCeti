/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Valuation.ValuativeRel.Comap
public import TauCeti.RingTheory.Valuation.Trivial
public import Mathlib.RingTheory.Valuation.Quotient
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.Topology.Order
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The valuation spectrum of a ring

We define the valuation spectrum `Spv A` following Wedhorn, *Adic Spaces*
(arXiv:1910.05934v1), Definition 4.1.

## Main definitions

* `TauCeti.ValuationSpectrum A` : The valuation spectrum, the type of `ValuativeRel` instances
  on `A`.
* `TauCeti.ValuationSpectrum.basicOpen f s` : The basic open set `{v ∈ Spv A | v(f) ≤ v(s) ≠ 0}`.
* `TauCeti.ValuationSpectrum.comap φ` : The continuous map `Spv B → Spv A` induced by
  `φ : A →+* B`.
* `TauCeti.ValuationSpectrum.supp v` : The support ideal `{a ∈ A | v(a) = 0}`.
* `TauCeti.ValuationSpectrum.basicOpenFinset_inter` : **Wedhorn's step (i)** in the proof of
  Lemma 7.5, that the rational opens are stable under finite intersection.
* `TauCeti.ValuationSpectrum.isClosed_setOfPred_forall_vlt_one` : the sub-unit locus of a set
  of ring elements is closed — the closedness behind Wedhorn's Corollary 7.12.
* `TauCeti.ValuationSpectrum.quotientLift 𝔞 h` : Lift the implicitly inferred point `v` with
  `𝔞 ≤ supp v` to `Spv (A ⧸ 𝔞)`.
* `TauCeti.ValuationSpectrum.localizationComapSection S B v hS` : Lift `v` to a localization
  `Spv B`.
* `TauCeti.ValuationSpectrum.suppFun` : The continuous support map `Spv A → Spec A`.
* `TauCeti.ValuationSpectrum.trivialSection` : The continuous section of `suppFun` given by
  the trivial valuation attached to a prime ideal; in particular `suppFun` is surjective
  (`suppFun_surjective`).

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 4.1, Remark 4.3, Remark 4.4,
  Remark 4.6, Proposition 4.7(2)

Ported from the open Mathlib pull request
[leanprover-community/mathlib4#38009](https://github.com/leanprover-community/mathlib4/pull/38009)
(which supersedes an earlier draft in AINTLIB `projects/AdicSpaces`); this copy is deleted in
favour of the Mathlib declarations once that pull request reaches the pinned Mathlib.
-/

public section

namespace TauCeti

/-- The *valuation spectrum* `Spv A` of a commutative ring `A`. A point of `Spv A` is a
`ValuativeRel A`, but `Spv A` is kept as a distinct type so it can carry its own topology
without affecting `ValuativeRel A`. -/
@[ext]
structure ValuationSpectrum (A : Type*) [CommRing A] where
  ofValuativeRel ::
  /-- The underlying `ValuativeRel A` of a point `v : Spv A`. -/
  toValuativeRel : ValuativeRel A

@[inherit_doc] scoped notation "Spv" => ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- Two points of `Spv A` are equal as soon as their underlying `vle` relations agree. -/
lemma ext' {v₁ v₂ : Spv A}
    (h : ∀ x y, v₁.toValuativeRel.vle x y ↔ v₂.toValuativeRel.vle x y) : v₁ = v₂ :=
  ValuationSpectrum.ext (ValuativeRel.ext (funext₂ fun x y ↦ propext (h x y)))

/-- Construct a point of `Spv A` from a valuation `v : Valuation A Γ₀`. -/
def ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀) : Spv A :=
  ⟨ValuativeRel.ofValuation v⟩

/-- Two equivalent valuations define the same point of `Spv A`. -/
lemma ofValuation_eq_of_isEquiv {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]
    {v₁ : Valuation A Γ₀} {v₂ : Valuation A Γ'₀} (h : v₁.IsEquiv v₂) :
    ofValuation v₁ = ofValuation v₂ :=
  ext' fun x y ↦ h x y

/-- The basic open subset `Spv(A)(f/s) = {v ∈ Spv A | v(f) ≤ v(s) ∧ v(s) ≠ 0}`. -/
def basicOpen (f s : A) : Set (Spv A) :=
  {v | v.toValuativeRel.vle f s ∧ ¬ v.toValuativeRel.vle s 0}

/-- Membership in the basic open subset `Spv(A)(f/s)`, as a normal form. -/
@[simp]
lemma mem_basicOpen_iff (f s : A) (v : Spv A) :
    v ∈ basicOpen f s ↔ v.toValuativeRel.vle f s ∧ ¬ v.toValuativeRel.vle s 0 := Iff.rfl

/-- Scaling numerator and denominator by `t` shrinks the basic open subset:
`Spv(A)(tf/ts) ⊆ Spv(A)(f/s)`. -/
lemma basicOpen_mul_subset (t f s : A) : basicOpen (t * f) (t * s) ⊆ basicOpen f s := by
  rintro v ⟨h1, h2⟩
  have ht : ¬ v.toValuativeRel.vle t 0 :=
    fun ht ↦ h2 (by simpa using v.toValuativeRel.mul_vle_mul_left ht s)
  refine ⟨v.toValuativeRel.vle_mul_cancel ht ?_, fun hs ↦ h2 ?_⟩
  · rwa [mul_comm t f, mul_comm t s] at h1
  · simpa [mul_comm s t] using v.toValuativeRel.mul_vle_mul_left hs t

/-- The basic open subset for `f = s = 1` is the whole spectrum: `Spv(A)(1/1) = Spv A`.
Not `@[simp]`: `basicOpen_one_right` together with `ValuativeRel.vle_refl` already reduces
the left-hand side, so a `simp` attribute here would be redundant (`simpNF`). -/
lemma basicOpen_one : basicOpen (1 : A) 1 = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun v ↦
    ⟨v.toValuativeRel.vle_refl 1, v.toValuativeRel.not_vle_one_zero⟩

/-- The basic open subset for `f = s` consists of the points where `v(s) ≠ 0`:
`Spv(A)(s/s) = {v ∈ Spv A | v(s) ≠ 0}`. -/
lemma basicOpen_self (s : A) :
    basicOpen s s = {v : Spv A | ¬ v.toValuativeRel.vle s 0} :=
  Set.ext fun v ↦ ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨v.toValuativeRel.vle_refl s, h⟩⟩

/-- The basic open subset at denominator `1` needs no nonvanishing clause:
`Spv(A)(f/1) = {v ∈ Spv A | v(f) ≤ 1}`. -/
@[simp]
lemma basicOpen_one_right (f : A) :
    basicOpen f 1 = {v : Spv A | v.toValuativeRel.vle f 1} :=
  Set.ext fun v ↦ and_iff_left v.toValuativeRel.not_vle_one_zero

/-- The topology on `Spv A` generated by the basic open sets `basicOpen f s`
for `f, s : A`. -/
instance instTopologicalSpace : TopologicalSpace (Spv A) :=
  TopologicalSpace.generateFrom {U | ∃ f s : A, U = basicOpen f s}

/-- Each basic open subset is open in `Spv A`. -/
lemma isOpen_basicOpen (f s : A) : IsOpen (basicOpen f s) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, s, rfl⟩

/-- The topology of `Spv A` is generated by the basic opens (the defining equation of the
instance). -/
lemma instTopologicalSpace_eq_generateFrom :
    (instTopologicalSpace : TopologicalSpace (Spv A))
      = TopologicalSpace.generateFrom {U | ∃ f s : A, U = basicOpen f s} := (rfl)

/-- The valuative relation of a point is determined by its basic opens: `v(f) ≤ v(s)` holds
iff `v` lies in `basicOpen f s`, or `s` and `f` both lie in the support — the latter being
detected by the diagonal basic opens `basicOpen s s` and `basicOpen f f`. -/
lemma vle_iff_mem_basicOpen_or (v : Spv A) (f s : A) :
    v.toValuativeRel.vle f s ↔
      v ∈ basicOpen f s ∨ (v ∉ basicOpen s s ∧ v ∉ basicOpen f f) := by
  simp only [mem_basicOpen_iff, not_and, not_not, ValuativeRel.vle_refl, forall_const]
  constructor
  · intro h
    by_cases hs : v.toValuativeRel.vle s 0
    · exact Or.inr ⟨hs, v.toValuativeRel.vle_trans h hs⟩
    · exact Or.inl ⟨h, hs⟩
  · rintro (⟨h, _⟩ | ⟨_, hf⟩)
    · exact h
    · exact v.toValuativeRel.vle_trans hf (v.toValuativeRel.zero_vle s)

/-- **The sub-unit locus of a set of ring elements is closed**: demanding `v(a) < 1` at every
`a ∈ S` cuts out a closed subset of `Spv A`. The complement is the union over `a ∈ S` of the
basic opens `Spv(A)(1/a)` — the condition `1 ≤ v(a)` already forces `v(a) ≠ 0`, so no separate
nonvanishing clause survives.

This is the closedness underlying Wedhorn's Corollary 7.12: Theorem 7.10 describes `Cont A`
inside `Spv (A, IA)` by exactly such conditions, so `Cont A` is the trace of a closed set. -/
theorem isClosed_setOfPred_forall_vlt_one (S : Set A) :
    IsClosed {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vlt a 1} := by
  rw [← isOpen_compl_iff]
  have h : {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vlt a 1}ᶜ = ⋃ a ∈ S, basicOpen 1 a := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, ValuativeRel.vlt, not_forall, not_not,
      Set.mem_iUnion, mem_basicOpen_iff, exists_prop]
    constructor
    · rintro ⟨a, haS, h1⟩
      exact ⟨a, haS, h1, fun h0 ↦ v.toValuativeRel.not_vle_one_zero
        (v.toValuativeRel.vle_trans h1 h0)⟩
    · rintro ⟨a, haS, h1, -⟩
      exact ⟨a, haS, h1⟩
  rw [h]
  exact isOpen_biUnion fun a _ ↦ isOpen_basicOpen 1 a

/-- `Spv A` is T0: inseparable points agree on every basic open, hence carry the same
valuative relation. -/
instance : T0Space (Spv A) := by
  refine ⟨fun v w h ↦ ?_⟩
  have hmem : ∀ a b : A, v ∈ basicOpen a b ↔ w ∈ basicOpen a b := fun a b ↦
    h.mem_open_iff (isOpen_basicOpen a b)
  refine ext' fun f s ↦ ?_
  rw [vle_iff_mem_basicOpen_or, vle_iff_mem_basicOpen_or, hmem, hmem, hmem]

section Functoriality

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- The contravariant map `Spv B → Spv A` induced by `φ : A →+* B`. -/
def comap (φ : A →+* B) (v : Spv B) : Spv A :=
  ⟨ValuativeRel.comap φ v.toValuativeRel⟩

/-- The relation of a pulled-back point compares images under `φ`. -/
@[simp]
lemma comap_vle (φ : A →+* B) (v : Spv B) {a₁ a₂ : A} :
    (comap φ v).toValuativeRel.vle a₁ a₂ = v.toValuativeRel.vle (φ a₁) (φ a₂) :=
  propext (ValuativeRel.comap_vle φ v.toValuativeRel a₁ a₂)

/-- The strict relation of a pulled-back point compares images under `φ`. -/
@[simp]
lemma comap_vlt (φ : A →+* B) (v : Spv B) {a₁ a₂ : A} :
    (comap φ v).toValuativeRel.vlt a₁ a₂ = v.toValuativeRel.vlt (φ a₁) (φ a₂) :=
  propext (ValuativeRel.comap_vlt φ v.toValuativeRel a₁ a₂)

/-- `comap` is compatible with `ofValuation`. -/
@[simp]
lemma comap_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (φ : A →+* B) (v : Valuation B Γ₀) :
    comap φ (ofValuation v) = ofValuation (v.comap φ) :=
  ext' fun x y ↦ ValuativeRel.comap_vle φ (ValuativeRel.ofValuation v) x y

/-- The preimage of `Spv(A)(f/s)` under `comap φ` is `Spv(B)(φ(f)/φ(s))`. -/
lemma comap_preimage_basicOpen (φ : A →+* B) (f s : A) :
    comap φ ⁻¹' basicOpen f s = basicOpen (φ f) (φ s) := by
  ext v
  simp [basicOpen]

/-- `comap φ` is continuous. -/
lemma continuous_comap (φ : A →+* B) : Continuous (comap φ) :=
  continuous_generateFrom_iff.mpr fun _ ⟨f, s, hU⟩ ↦
    hU ▸ comap_preimage_basicOpen φ f s ▸ isOpen_basicOpen (φ f) (φ s)

/-- `comap` of the identity is the identity. -/
@[simp]
lemma comap_id : comap (RingHom.id A) = id := by
  funext v
  exact ValuationSpectrum.ext (ValuativeRel.comap_id v.toValuativeRel)

/-- `comap` is contravariantly functorial: `comap (ψ ∘ φ) = comap φ ∘ comap ψ`. -/
@[simp]
lemma comap_comp (φ : A →+* B) (ψ : B →+* C) :
    comap (ψ.comp φ) = comap φ ∘ comap ψ := by
  funext v
  exact ValuationSpectrum.ext (ValuativeRel.comap_comp φ ψ v.toValuativeRel)

/-- `comap φ` is injective when `φ` is surjective. -/
lemma comap_injective {φ : A →+* B} (hφ : Function.Surjective φ) :
    Function.Injective (comap φ) := by
  intro v₁ v₂ h
  refine ext' fun b₁ b₂ ↦ ?_
  obtain ⟨a₁, rfl⟩ := hφ b₁; obtain ⟨a₂, rfl⟩ := hφ b₂
  exact iff_of_eq (by simpa only [comap_vle] using congr_arg (fun v ↦ v.toValuativeRel.vle a₁ a₂) h)

end Functoriality

/-- The support ideal `{a ∈ A | v(a) = 0}` of a point `v : Spv A`. -/
def supp (v : Spv A) : Ideal A :=
  let := v.toValuativeRel
  ValuativeRel.supp A

/-- Membership in the support, as the relation `v(x) ≤ v(0)`. -/
@[simp]
lemma mem_supp_iff (v : Spv A) (x : A) : x ∈ v.supp ↔ v.toValuativeRel.vle x 0 :=
  let := v.toValuativeRel
  ValuativeRel.supp_def x

/-- The support of a point `v : Spv A` is a prime ideal. -/
instance instIsPrimeSupp (v : Spv A) : v.supp.IsPrime :=
  let := v.toValuativeRel
  inferInstanceAs (ValuativeRel.supp A).IsPrime

/-- `(ofValuation v).vle x y ↔ v x ≤ v y`. -/
@[simp]
lemma vle_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation A Γ₀) (x y : A) :
    (ofValuation v).toValuativeRel.vle x y ↔ v x ≤ v y := Iff.rfl

/-- The support of `ofValuation v` equals `v.supp`. -/
@[simp]
lemma supp_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation A Γ₀) : (ofValuation v).supp = v.supp := by
  ext x
  simp [mem_supp_iff, Valuation.mem_supp_iff]

/-- The canonical valuation associated to a point `v : Spv A`. -/
noncomputable def valuation (v : Spv A) :
    Valuation A (@ValuativeRel.ValueGroupWithZero A _ v.toValuativeRel) :=
  @ValuativeRel.valuation A _ v.toValuativeRel

/-- Comparison under the canonical valuation of a point is the point's valuative relation. -/
@[simp]
lemma valuation_le_iff (v : Spv A) (x y : A) :
    v.valuation x ≤ v.valuation y ↔ v.toValuativeRel.vle x y :=
  let := v.toValuativeRel
  ((ValuativeRel.valuation A).vle_iff_le (x := x) (y := y)).symm

/-- Strict comparison under the canonical valuation of a point is the point's strict valuative
relation — the strict sibling of `valuation_le_iff`, and the direct bridge between strict
valuation inequalities and `vlt` hypotheses. -/
@[simp]
lemma valuation_lt_iff (v : Spv A) (x y : A) :
    v.valuation x < v.valuation y ↔ v.toValuativeRel.vlt x y :=
  let := v.toValuativeRel
  ((ValuativeRel.valuation A).vlt_iff_lt (x := x) (y := y)).symm

/-- The support of `v : Spv A` equals the support of its canonical valuation. -/
lemma supp_eq_valuation_supp (v : Spv A) : v.supp = v.valuation.supp :=
  @ValuativeRel.supp_eq_valuation_supp A _ v.toValuativeRel

/-- The canonical valuation gives back the same point of `Spv`. -/
@[simp]
lemma ofValuation_valuation (v : Spv A) : ofValuation v.valuation = v := by
  let := v.toValuativeRel
  exact ext' fun x y ↦ (ValuativeRel.valuation A).vle_iff_le.symm

/-- The canonical valuation of the point determined by `w` is equivalent to `w`. -/
lemma isEquiv_valuation_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation A Γ₀) : Valuation.IsEquiv (ofValuation w).valuation w := by
  intro x y
  rw [valuation_le_iff, vle_ofValuation]

section Quotient

variable (𝔞 : Ideal A)

/-- `𝔞 ≤ supp(comap(mk 𝔞, w))` for all `w : Spv (A ⧸ 𝔞)`. -/
lemma self_le_supp_comap (w : Spv (A ⧸ 𝔞)) :
    𝔞 ≤ (comap (Ideal.Quotient.mk 𝔞) w).supp :=
  fun a ha ↦ by simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]

/-- Lift a point `v ∈ Spv A` with `𝔞 ≤ supp v` to `Spv (A ⧸ 𝔞)`. -/
noncomputable def quotientLift ⦃v : Spv A⦄ (h : 𝔞 ≤ v.supp) : Spv (A ⧸ 𝔞) :=
  ofValuation (v.valuation.onQuot (v.supp_eq_valuation_supp ▸ h))

/-- `comap (mk 𝔞) (quotientLift 𝔞 h) = v`. -/
@[simp]
lemma comap_quotientLift ⦃v : Spv A⦄ (h : 𝔞 ≤ v.supp) :
    comap (Ideal.Quotient.mk 𝔞) (quotientLift 𝔞 h) = v := by
  rw [quotientLift, comap_ofValuation,
    Valuation.onQuot_comap_eq v.valuation (v.supp_eq_valuation_supp ▸ h)]
  exact ofValuation_valuation v

/-- `quotientLift 𝔞 (self_le_supp_comap 𝔞 w) = w`. -/
@[simp]
lemma quotientLift_comap (w : Spv (A ⧸ 𝔞)) :
    quotientLift 𝔞 (self_le_supp_comap 𝔞 w) = w := by
  refine ext' fun x y ↦ ?_
  obtain ⟨a₁, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a₂, rfl⟩ := Ideal.Quotient.mk_surjective y
  let : ValuativeRel A := ValuativeRel.comap (Ideal.Quotient.mk 𝔞) w.toValuativeRel
  exact (ValuativeRel.valuation A).vle_iff_le.symm.trans
    (ValuativeRel.comap_vle (Ideal.Quotient.mk 𝔞) w.toValuativeRel a₁ a₂)

/-- The range of `comap (mk 𝔞)` is `{v ∈ Spv A | 𝔞 ≤ supp v}`. -/
lemma quotientMk_comap_range :
    Set.range (comap (Ideal.Quotient.mk 𝔞)) = {v : Spv A | 𝔞 ≤ v.supp} :=
  Set.ext fun _ ↦ ⟨fun ⟨w, hw⟩ ↦ hw ▸ self_le_supp_comap 𝔞 w,
    fun h ↦ ⟨quotientLift 𝔞 h, comap_quotientLift 𝔞 h⟩⟩

/-- `comap (mk 𝔞) : Spv (A ⧸ 𝔞) → Spv A` is a topological embedding. -/
lemma isEmbedding_comap_quotientMk :
    Topology.IsEmbedding (comap (Ideal.Quotient.mk 𝔞)) where
  eq_induced := by
    simp only [instTopologicalSpace, induced_generateFrom_eq]
    congr 1
    ext U
    constructor
    · rintro ⟨f', s', rfl⟩
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      exact ⟨_, ⟨f, s, rfl⟩, comap_preimage_basicOpen _ f s⟩
    · rintro ⟨_, ⟨f, s, rfl⟩, rfl⟩
      exact ⟨_, _, comap_preimage_basicOpen _ f s⟩
  injective := comap_injective Ideal.Quotient.mk_surjective

end Quotient

section Localization

variable (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]

/-- Send `v ∈ Spv A` with `S ≤ (supp v).primeCompl` to the localization `Spv B`, where `B` is a
localization of `A` at the submonoid `S`. -/
noncomputable def localizationComapSection (v : Spv A) (hS : S ≤ v.supp.primeCompl) : Spv B :=
  ofValuation ((v.valuation.extendToLocalization (fun _ hs ↦ Ideal.mem_primeCompl_iff.mpr
    (v.supp_eq_valuation_supp ▸ Ideal.mem_primeCompl_iff.mp (hS hs))) B))

/-- `comap (algebraMap A B) (localizationComapSection S B v hS) = v`. -/
@[simp]
lemma comap_localizationComapSection (v : Spv A) (hS : S ≤ v.supp.primeCompl) :
    comap (algebraMap A B) (localizationComapSection S B v hS) = v := by
  have hS' : S ≤ v.valuation.supp.primeCompl := fun _ hs ↦
    Ideal.mem_primeCompl_iff.mpr (v.supp_eq_valuation_supp ▸ Ideal.mem_primeCompl_iff.mp (hS hs))
  have key : (v.valuation.extendToLocalization hS' B).comap (algebraMap A B) = v.valuation :=
    Valuation.ext fun a ↦ Valuation.extendToLocalization_apply_map_apply _ hS' B a
  unfold localizationComapSection
  rw [comap_ofValuation, key]
  exact ofValuation_valuation v

/-- `S` is disjoint from `supp(comap(algebraMap, w))` for `w : Spv B`. -/
lemma submonoid_le_supp_primeCompl_comap_algebraMap (w : Spv B) :
    S ≤ (comap (algebraMap A B) w).supp.primeCompl := by
  intro s hs hmem
  rw [SetLike.mem_coe, mem_supp_iff, comap_vle, map_zero] at hmem
  let := w.toValuativeRel
  exact ValuativeRel.not_vle_zero_of_isUnit (IsLocalization.map_units B ⟨s, hs⟩) hmem

/-- The range of `comap (algebraMap A B)` is `{v | S ≤ supp(v).primeCompl}`. -/
lemma localization_comap_range :
    Set.range (comap (algebraMap A B)) = {v : Spv A | S ≤ v.supp.primeCompl} := by
  ext v
  simpa using ⟨fun ⟨w, hw⟩ ↦ hw ▸ submonoid_le_supp_primeCompl_comap_algebraMap S B w,
    fun h ↦ ⟨localizationComapSection S B v h, comap_localizationComapSection S B v h⟩⟩

end Localization

section PrimeSpectrum

/-! ### The support map to the prime spectrum -/

/-- The support map `Spv A → Spec A`. -/
def suppFun : Spv A → PrimeSpectrum A := fun v ↦ ⟨v.supp, inferInstance⟩

/-- The prime ideal underlying `suppFun v` is the support of `v`. -/
@[simp]
lemma suppFun_asIdeal (v : Spv A) : (suppFun v).asIdeal = v.supp := (rfl)

/-- `suppFun ⁻¹' D(f) = Spv(A)(f/f)`. -/
lemma suppFun_preimage_basicOpen (f : A) :
    suppFun ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) = basicOpen f f := by
  ext v
  simp [basicOpen_self, mem_supp_iff]

/-- `suppFun` is continuous. -/
theorem continuous_suppFun : Continuous (suppFun : Spv A → PrimeSpectrum A) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr fun _ ⟨f, hf⟩ ↦
    hf ▸ suppFun_preimage_basicOpen f ▸ isOpen_basicOpen f f

/-- `supp ∘ Spv(φ) = Spec(φ) ∘ supp`. -/
theorem suppFun_comap {B : Type*} [CommRing B] (φ : A →+* B) (v : Spv B) :
    suppFun (comap φ v) = PrimeSpectrum.comap φ (suppFun v) := by
  ext; simp [mem_supp_iff, comap_vle]

/-! ### The trivial-valuation section of the support map -/

/-- The trivial-valuation section of the support map (Wedhorn, Remark 4.6): the point of
`Spv A` given by the trivial valuation attached to a prime ideal. -/
noncomputable def trivialSection (p : PrimeSpectrum A) : Spv A :=
  ofValuation
    (Valuation.trivialValuation p.asIdeal : Valuation A (WithZero (Multiplicative ℤ)))

/-- The valuative relation of a trivial-valuation point: `v(f) ≤ v(s)` holds precisely
when `f` lies in the prime or `s` does not. -/
@[simp]
lemma trivialSection_vle_iff (p : PrimeSpectrum A) (f s : A) :
    (trivialSection p).toValuativeRel.vle f s ↔ f ∈ p.asIdeal ∨ s ∉ p.asIdeal := by
  rw [trivialSection, vle_ofValuation, Valuation.trivialValuation_apply,
    Valuation.trivialValuation_apply]
  constructor
  · intro h
    by_cases hf : f ∈ p.asIdeal
    · exact Or.inl hf
    · refine Or.inr fun hs ↦ ?_
      rw [ite_eq_right hf, ite_eq_left hs] at h
      simp at h
  · rintro (hf | hs)
    · simp [hf]
    · rw [ite_eq_right hs]
      split <;> simp

/-- `trivialSection` is a section of the support map. -/
@[simp]
lemma suppFun_trivialSection (p : PrimeSpectrum A) : suppFun (trivialSection p) = p := by
  ext x
  rw [suppFun_asIdeal, trivialSection, supp_ofValuation, Valuation.mem_supp_iff,
    Valuation.trivialValuation_eq_zero_iff]

/-- The preimage of a basic open under `trivialSection` is the corresponding basic open of
the prime spectrum: `trivialSection ⁻¹' Spv(A)(f/s) = D(s)`. -/
lemma trivialSection_preimage_basicOpen (f s : A) :
    trivialSection ⁻¹' basicOpen f s = (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A)) := by
  ext p
  have h0 : (0 : A) ∈ p.asIdeal := p.asIdeal.zero_mem
  simp only [Set.mem_preimage, mem_basicOpen_iff, trivialSection_vle_iff, SetLike.mem_coe,
    PrimeSpectrum.mem_basicOpen, h0, not_true_eq_false, or_false]
  tauto

/-- `trivialSection` is continuous. -/
lemma continuous_trivialSection :
    Continuous (trivialSection : PrimeSpectrum A → Spv A) :=
  continuous_generateFrom_iff.mpr fun _ ⟨f, s, hU⟩ ↦
    hU ▸ trivialSection_preimage_basicOpen f s ▸ (PrimeSpectrum.basicOpen s).isOpen

/-- The support map is surjective; the trivial valuations provide a section. -/
theorem suppFun_surjective : Function.Surjective (suppFun : Spv A → PrimeSpectrum A) :=
  fun p ↦ ⟨trivialSection p, suppFun_trivialSection p⟩

end PrimeSpectrum

section RationalOpenFinset

open Set

/-! ### Rational opens with a finite numerator set -/

/-- **Wedhorn's `Spv(A)(T/s)`** for a finite set `T`: the points where every `t ∈ T` is
dominated by `s`, and `s` is not in the support. -/
def basicOpenFinset (T : Finset A) (s : A) : Set (Spv A) :=
  {v | (∀ t ∈ T, v.toValuativeRel.vle t s) ∧ ¬ v.toValuativeRel.vle s 0}

@[simp]
lemma mem_basicOpenFinset_iff (T : Finset A) (s : A) (v : Spv A) :
    v ∈ basicOpenFinset T s ↔
      (∀ t ∈ T, v.toValuativeRel.vle t s) ∧ ¬ v.toValuativeRel.vle s 0 := Iff.rfl

/-- Each numerator gives back an ordinary basic open. -/
lemma basicOpenFinset_subset_basicOpen {T : Finset A} {s t : A} (ht : t ∈ T) :
    basicOpenFinset T s ⊆ basicOpen t s :=
  fun _ hv ↦ (mem_basicOpen_iff t s _).mpr ⟨hv.1 t ht, hv.2⟩

/-- `Spv(A)(T/s)` is the finite intersection of the basic opens `Spv(A)(t/s)` for `t` ranging
over `T ∪ {s}`; the extra `s` is what carries the nonvanishing clause when `T` is empty. -/
lemma basicOpenFinset_eq_biInter (T : Finset A) (s : A) :
    basicOpenFinset T s = ⋂ t ∈ insert s (T : Set A), basicOpen t s := by
  ext v
  simp only [mem_basicOpenFinset_iff, mem_iInter, mem_basicOpen_iff, Set.mem_insert_iff,
    Finset.mem_coe]
  refine ⟨fun h t ht ↦ ?_, fun h ↦ ⟨fun t ht ↦ (h t (Or.inr ht)).1, fun hs ↦ ?_⟩⟩
  · rcases ht with rfl | ht
    · exact ⟨v.toValuativeRel.vle_refl t, h.2⟩
    · exact ⟨h.1 t ht, h.2⟩
  · exact (h s (Or.inl rfl)).2 hs

lemma isOpen_basicOpenFinset (T : Finset A) (s : A) : IsOpen (basicOpenFinset T s) := by
  rw [basicOpenFinset_eq_biInter]
  exact Set.Finite.isOpen_biInter (T.finite_toSet.insert s) fun t _ ↦ isOpen_basicOpen t s

open scoped Classical in
/-- Inserting the denominator among the numerators changes nothing: the extra condition it adds
is `v s ≤ v s`. -/
@[simp]
lemma basicOpenFinset_insert_self (T : Finset A) (s : A) :
    basicOpenFinset (insert s T) s = basicOpenFinset T s := by
  ext v
  simp only [mem_basicOpenFinset_iff, Finset.mem_insert]
  exact ⟨fun ⟨h, hs⟩ ↦ ⟨fun t ht ↦ h t (Or.inr ht), hs⟩,
    fun ⟨h, hs⟩ ↦ ⟨fun t ht ↦ ht.elim (fun e ↦ e ▸ v.toValuativeRel.vle_refl s) (h t), hs⟩⟩

open scoped Classical Pointwise in
/-- **Wedhorn's step (i) in the proof of Lemma 7.5**: the rational opens are stable under finite
intersection. Writing `Uᵢ = insert sᵢ Tᵢ` for the numerator set augmented by its own denominator,

```text
Spv(A)(T₁/s₁) ∩ Spv(A)(T₂/s₂) = Spv(A)(U₁U₂ / s₁s₂).
```

The numerator sets on the right carry their own denominators, which
`basicOpenFinset_insert_self` shows costs nothing — the same absorption `IsAdmissible` performs
for the admissibility condition. -/
@[simp]
lemma basicOpenFinset_inter (T₁ T₂ : Finset A) (s₁ s₂ : A) :
    basicOpenFinset T₁ s₁ ∩ basicOpenFinset T₂ s₂
      = basicOpenFinset (insert s₁ T₁ * insert s₂ T₂) (s₁ * s₂) := by
  rw [← basicOpenFinset_insert_self T₁ s₁, ← basicOpenFinset_insert_self T₂ s₂]
  set U₁ := insert s₁ T₁ with hU₁
  set U₂ := insert s₂ T₂ with hU₂
  have h₁ : s₁ ∈ U₁ := Finset.mem_insert_self _ _
  have h₂ : s₂ ∈ U₂ := Finset.mem_insert_self _ _
  ext v
  simp only [Set.mem_inter_iff, mem_basicOpenFinset_iff, ← mem_supp_iff,
    (instIsPrimeSupp v).mul_mem_iff_mem_or_mem, not_or]
  constructor
  · rintro ⟨⟨hT₁, hs₁⟩, ⟨hT₂, hs₂⟩⟩
    refine ⟨?_, hs₁, hs₂⟩
    rintro _ ht
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Finset.mem_mul.mp ht
    exact v.toValuativeRel.mul_vle_mul (hT₁ t₁ ht₁) (hT₂ t₂ ht₂)
  · rintro ⟨hT, hs₁, hs₂⟩
    refine ⟨⟨fun t₁ ht₁ ↦ ?_, hs₁⟩, fun t₂ ht₂ ↦ ?_, hs₂⟩
    · exact v.toValuativeRel.vle_mul_cancel hs₂ (hT _ (Finset.mul_mem_mul ht₁ h₂))
    · refine v.toValuativeRel.vle_mul_cancel hs₁ ?_
      have := hT _ (Finset.mul_mem_mul h₁ ht₂)
      rwa [mul_comm s₁ t₂, mul_comm s₁ s₂] at this

end RationalOpenFinset
end ValuationSpectrum

end TauCeti
