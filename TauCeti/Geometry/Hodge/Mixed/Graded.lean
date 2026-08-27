/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Basic

/-!
# The pure Hodge structure on a complex graded piece

The purity axiom of a mixed Hodge structure is imposed on the *rational* graded pieces: the
complexification `ℂ ⊗[ℚ] grᵂ_k` of `grᵂ_k = W_k / W_{k-1}` carries a pure Hodge structure of
weight `k`. The mixed theory itself, however, runs inside the complex model: Deligne's bigrading
`I^{p,q}` is built from the Hodge filtration `F`, its conjugate, and the complexified weight
filtration `WC`, and its elements are compared with the Hodge components of
`WC_k / WC_{k-1}`. This file moves the pure structure from the first model to the second.

The transport is the identification `TauCeti.Hodge.gradedComplexEquiv`, and what makes it
legitimate is that this identification intertwines the two conjugations
(`TauCeti.Hodge.gradedComplexEquiv_latticeConj`): the canonical conjugation of a complexified
rational space on the left, and on the right the conjugation that lattice conjugation induces on
the complex graded piece, each step of `WC` being the complexification of a rational subspace and
therefore conjugation-stable.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.gradedConjugation`: the conjugation induced by lattice
  conjugation on the `k`-th complex graded piece.
* `TauCeti.Hodge.MixedHodgeStructure.complexGradedHodgeStructure`: the pure Hodge structure of
  weight `k` carried by `WC_k / WC_{k-1}`, with its filtration
  `TauCeti.Hodge.complexGradedF` and its Hodge components computed.
* `TauCeti.Hodge.MixedHodgeStructure.isInternal_complexGradedHodgeStructure_piece`: the Hodge
  decomposition of a complex graded piece.
* `TauCeti.Hodge.MixedHodgeStructure.mk_mem_complexGradedHodgeStructure_piece`: a vector of `W_k`
  that lies in `F^p` and lies in `conj F^{k-p}` modulo `W_{k-1}` has its class in the Hodge
  component `H^{p,k-p}` of the graded piece. This is the form in which the pieces of Deligne's
  bigrading meet the graded Hodge structure, and
  `TauCeti.Hodge.MixedHodgeStructure.mem_complexGradedHodgeStructure_piece_iff` shows the
  criterion is exact. `TauCeti.Hodge.MixedHodgeStructure.mk_mem_complexGradedHodgeStructure_F`
  and its conjugate analogue are the corresponding criteria for the two induced filtrations.

## References

The graded-piece comparison and the bidegree bookkeeping follow Peters–Steenbrink, *Mixed Hodge
Structures*, Ch. 3, and Deligne, *Théorie de Hodge II*, §1.2.1 and 1.2.10.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

namespace MixedHodgeStructure

variable (mhs : MixedHodgeStructure hℚ hℂ)

/-- The conjugation induced by lattice conjugation on the `k`-th graded piece of the complexified
weight filtration. -/
noncomputable def gradedConjugation (k : ℤ) : Conjugation (weightGradedComplex mhs.WC k) :=
  gradedComplexConjugation hℚ hℂ mhs.WQ k

/-- The induced conjugation acts on a class through lattice conjugation of a representative. -/
@[simp]
theorem gradedConjugation_mk (k : ℤ) (x : mhs.WC k) :
    (mhs.gradedConjugation k).toEquiv (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨latticeConj hℂ (x : Vℂ),
        (rationalToComplexSubmodule_conj hℚ hℂ (mhs.WQ k)).le ⟨x, x.2, rfl⟩⟩ :=
  gradedComplexConjugation_mk hℚ hℂ mhs.WQ k x

/-- The comparison of the rational and complex models of the `k`-th graded piece intertwines the
canonical conjugation of the former with the induced conjugation of the latter. -/
theorem gradedComplexEquiv_gradedConjugation (k : ℤ)
    (x : ℂ ⊗[ℚ] weightGradedRat mhs.WQ k) :
    gradedComplexEquiv hℚ hℂ mhs.WQ mhs.WQ_monotone k
        (latticeConj (isBaseChange_ratTensorMap ℂ (weightGradedRat mhs.WQ k)) x) =
      (mhs.gradedConjugation k).toEquiv
        (gradedComplexEquiv hℚ hℂ mhs.WQ mhs.WQ_monotone k x) :=
  gradedComplexEquiv_latticeConj hℚ hℂ mhs.WQ mhs.WQ_monotone k x

/-- The inverse comparison intertwines the conjugations, in the form the transport of a Hodge
structure consumes. -/
theorem gradedComplexEquiv_symm_gradedConjugation (k : ℤ)
    (y : weightGradedComplex mhs.WC k) :
    (gradedComplexEquiv hℚ hℂ mhs.WQ mhs.WQ_monotone k).symm
        ((mhs.gradedConjugation k).toEquiv y) =
      (latticeConjugation (isBaseChange_ratTensorMap ℂ (weightGradedRat mhs.WQ k))).toEquiv
        ((gradedComplexEquiv hℚ hℂ mhs.WQ mhs.WQ_monotone k).symm y) :=
  gradedComplexEquiv_symm_latticeConj hℚ hℂ mhs.WQ mhs.WQ_monotone k y

/-- **The `k`-th complex graded piece of a mixed Hodge structure is a pure Hodge structure of
weight `k`.** Its conjugation is the one lattice conjugation induces on `WC_k / WC_{k-1}`, and its
filtration is the one the Hodge filtration induces there; purity is transported from the rational
graded piece along `TauCeti.Hodge.gradedComplexEquiv`, which is legitimate because that
identification intertwines the conjugations. -/
noncomputable def complexGradedHodgeStructure (k : ℤ) :
    HodgeStructureOn (weightGradedComplex mhs.WC k) (mhs.gradedConjugation k) k :=
  HodgeStructureOn.comap (gradedComplexEquiv hℚ hℂ mhs.WQ mhs.WQ_monotone k).symm
    (mhs.gradedComplexEquiv_symm_gradedConjugation k) (mhs.gradedHodgeStructure k)

/-- The filtration of the graded pure structure is the filtration induced by `F` on the complex
graded piece, on the nose. -/
@[simp]
theorem complexGradedHodgeStructure_F (k p : ℤ) :
    (mhs.complexGradedHodgeStructure k).F p = complexGradedF mhs.WC mhs.F k p := by
  rw [complexGradedHodgeStructure, HodgeStructureOn.comap_F, gradedHodgeStructure_F]
  ext y
  simp

/-- The conjugate filtration of the graded pure structure is the filtration induced by the
conjugate of `F`. -/
@[simp]
theorem complexGradedHodgeStructure_conjF (k p : ℤ) :
    (mhs.complexGradedHodgeStructure k).conjF p =
      complexGradedF mhs.WC (fun q ↦ (mhs.F q).map (latticeConj hℂ)) k p := by
  rw [HodgeStructureOn.conjF_def, complexGradedHodgeStructure_F, gradedConjugation]
  exact map_gradedComplexConjugation_complexGradedF hℚ hℂ mhs.WQ mhs.F k p

/-- The Hodge components of the graded pure structure, spelled out in terms of the Hodge
filtration and its conjugate. -/
theorem complexGradedHodgeStructure_piece (k p : ℤ) :
    (mhs.complexGradedHodgeStructure k).piece p =
      complexGradedF mhs.WC mhs.F k p ⊓
        complexGradedF mhs.WC (fun q ↦ (mhs.F q).map (latticeConj hℂ)) k (k - p) := by
  rw [HodgeStructureOn.piece_def, complexGradedHodgeStructure_F,
    complexGradedHodgeStructure_conjF]

/-- The comparison of the two models of a graded piece carries Hodge components to Hodge
components. -/
theorem map_gradedHodgeStructure_piece (k p : ℤ) :
    ((mhs.gradedHodgeStructure k).piece p).map
        (gradedComplexEquiv hℚ hℂ mhs.WQ mhs.WQ_monotone k).toLinearMap =
      (mhs.complexGradedHodgeStructure k).piece p := by
  rw [complexGradedHodgeStructure, HodgeStructureOn.comap_piece,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]

/-- **The Hodge decomposition of a complex graded piece**: the Hodge components of
`WC_k / WC_{k-1}` are an internal direct sum. -/
theorem isInternal_complexGradedHodgeStructure_piece (k : ℤ) :
    DirectSum.IsInternal (mhs.complexGradedHodgeStructure k).piece :=
  HodgeStructureOn.isInternal_piece _

/-- A vector of `W_k` lying in `F^p` has its class in the `p`-th step of the filtration induced on
the graded piece. -/
theorem mk_mem_complexGradedHodgeStructure_F (k p : ℤ) (y : mhs.WC k) (hF : (y : Vℂ) ∈ mhs.F p) :
    Submodule.Quotient.mk y ∈ (mhs.complexGradedHodgeStructure k).F p := by
  rw [complexGradedHodgeStructure_F, mem_complexGradedF_iff]
  exact ⟨y, hF, rfl⟩

/-- A vector of `W_k` lying in `conj F^p` has its class in the `p`-th step of the conjugate
filtration induced on the graded piece. -/
theorem mk_mem_complexGradedHodgeStructure_conjF (k p : ℤ) (y : mhs.WC k)
    (hF : (y : Vℂ) ∈ mhs.conjF p) :
    Submodule.Quotient.mk y ∈ (mhs.complexGradedHodgeStructure k).conjF p := by
  rw [complexGradedHodgeStructure_conjF, mem_complexGradedF_iff]
  exact ⟨y, by rwa [← conjF_def], rfl⟩

/-- **A representative criterion for the Hodge components of a complex graded piece.** A vector of
`W_k` that lies in `F^p`, and that lies in the conjugate `conj F^{k-p}` modulo `W_{k-1}`, has its
class in the Hodge component `H^{p,k-p}` of the graded piece.

The second hypothesis is weaker than membership of `conj F^{k-p}`, and the weakening is what makes
the criterion usable: in the mixed theory the conjugation relations hold only modulo lower steps
of the weight filtration, which is exactly the shape in which the pieces of Deligne's bigrading
`I^{p,q}` present themselves. -/
theorem mk_mem_complexGradedHodgeStructure_piece (k p : ℤ) (y : mhs.WC k)
    (hF : (y : Vℂ) ∈ mhs.F p)
    (hconj : (y : Vℂ) ∈ (mhs.F (k - p)).map (latticeConj hℂ) ⊔ mhs.WC (k - 1)) :
    Submodule.Quotient.mk y ∈ (mhs.complexGradedHodgeStructure k).piece p := by
  rw [complexGradedHodgeStructure_piece]
  refine ⟨(mem_complexGradedF_iff mhs.WC mhs.F k p _).2 ⟨y, hF, rfl⟩, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hconj
  have hbk : b ∈ mhs.WC k := mhs.WC_monotone (by omega) hb
  have hak : a ∈ mhs.WC k := by
    have hay : a = (y : Vℂ) - b := eq_sub_of_add_eq hab
    rw [hay]
    exact Submodule.sub_mem _ y.2 hbk
  refine (mem_complexGradedF_iff mhs.WC _ k (k - p) _).2 ⟨⟨a, hak⟩, ha,
    (weightGradedComplex_mk_eq_mk_iff mhs.WC k ⟨a, hak⟩ y).2 ?_⟩
  have hay : a - (y : Vℂ) = -b := by rw [← hab]; abel
  rw [hay]
  exact Submodule.neg_mem _ hb

/-- **The Hodge components of a complex graded piece, by representatives.** A class lies in the
component `H^{p,k-p}` exactly when it has a representative in `W_k` that lies in `F^p` and lies in
`conj F^{k-p}` modulo `W_{k-1}`.

The forward direction is what turns a statement about the graded piece back into one about
representatives in `W_k`; the backward direction is
`TauCeti.Hodge.MixedHodgeStructure.mk_mem_complexGradedHodgeStructure_piece`. -/
theorem mem_complexGradedHodgeStructure_piece_iff (k p : ℤ)
    (u : weightGradedComplex mhs.WC k) :
    u ∈ (mhs.complexGradedHodgeStructure k).piece p ↔
      ∃ y : mhs.WC k, (y : Vℂ) ∈ mhs.F p ∧
        (y : Vℂ) ∈ (mhs.F (k - p)).map (latticeConj hℂ) ⊔ mhs.WC (k - 1) ∧
        Submodule.Quotient.mk y = u := by
  constructor
  · intro hu
    rw [complexGradedHodgeStructure_piece] at hu
    obtain ⟨y₁, hy₁, hy₁u⟩ := (mem_complexGradedF_iff mhs.WC mhs.F k p u).1 hu.1
    obtain ⟨y₂, hy₂, hy₂u⟩ :=
      (mem_complexGradedF_iff mhs.WC _ k (k - p) u).1 hu.2
    refine ⟨y₁, hy₁, ?_, hy₁u⟩
    have hdiff : (y₁ : Vℂ) - (y₂ : Vℂ) ∈ mhs.WC (k - 1) :=
      (weightGradedComplex_mk_eq_mk_iff mhs.WC k y₁ y₂).1 (hy₁u.trans hy₂u.symm)
    have hsplit : (y₁ : Vℂ) = (y₂ : Vℂ) + ((y₁ : Vℂ) - (y₂ : Vℂ)) := by abel
    rw [hsplit]
    exact Submodule.add_mem_sup hy₂ hdiff
  · rintro ⟨y, hF, hconj, rfl⟩
    exact mhs.mk_mem_complexGradedHodgeStructure_piece k p y hF hconj

end MixedHodgeStructure

end TauCeti.Hodge
