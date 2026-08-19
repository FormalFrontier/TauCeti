/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra

/-!
# The Kostant integral form of the pinned split Lie algebra of a Dynkin type

`TauCeti.DynkinType.lieAlgebra` is the split Lie algebra of a valid Dynkin type, realized by Geck's
construction as an explicit Lie subalgebra of `GeckIndex`-indexed rational matrices, with Chevalley
generators `TauCeti.DynkinType.lieBasis` numbered by Bourbaki node. This file forms the Kostant
`ℤ`-form of its universal enveloping algebra from exactly that numbered data, and records the
defining matrix representation the form is destined to act through.

Four things are needed before the divided powers of the Kostant form can be exponentiated into
root subgroups, and all four are supplied here.

*The form itself.* `TauCeti.DynkinType.kostantForm` is
`TauCeti.UniversalEnvelopingAlgebra.kostantForm` applied to the raising and lowering generators,
gathered as one family `TauCeti.DynkinType.chevalleyGenerator` indexed by `Fin t.rank ⊕ Fin t.rank`,
and to the Cartan generators. Because the raising and lowering generators already generate the whole
Lie algebra, `TauCeti.DynkinType.span_kostantForm_eq_top` says the form spans `U(L)` over `ℚ`
without further hypotheses: it is an integral form, not merely a subring.

*A representation to act in.* Geck's Lie algebra consists of actual matrices, so its defining
action on `GeckIndex → ℚ` is available with no representation theory at all:
`TauCeti.DynkinType.geckRepresentation` is the algebra map extending it, and it is faithful on the
Lie algebra by `TauCeti.DynkinType.geckRepresentation_ι_injective`.

*Nilpotency and weights.* `TauCeti.DynkinType.isNilpotent_geckRepresentation_chevalleyGenerator`
says every numbered generator acts nilpotently, which is what makes its divided-power exponential a
finite sum; and `TauCeti.DynkinType.geckRepresentation_cartanGenerator_apply_single` says each
standard coordinate vector is a joint eigenvector of the Cartan generators, with the *integer*
eigenvalue `TauCeti.DynkinType.geckWeight`. In the Bourbaki numbering that weight is zero on the
`b.support` coordinates and is the Cartan pairing `⟨α_k, α_i^∨⟩` on the coordinate of the root
`α_k`, so the standard lattice of the Geck module is a weight lattice for the pinned Cartan.

*A `ℤ`-module to act on.* `TauCeti.DynkinType.geckLattice` is the `ℤ`-span of the images of the
standard coordinate vectors under the whole Kostant form. It is stable under the form by
construction and spans the Geck module over `ℚ`, so it discharges the stability hypothesis that
every Kostant root-subgroup consumer has so far carried.

What is deliberately *not* proved is that `geckLattice` is finitely generated over `ℤ`. That is the
remaining half of the admissible-lattice statement of Humphreys §27 and needs the integral
Poincaré--Birkhoff--Witt theorem; it is also what a matrix realization of the resulting root
subgroups would need. Nor is the pinned Lie algebra asserted to be semisimple, which
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/LieAlgebra.lean` already records as not
claimed. This file is the numbered input those later steps consume.

## Main definitions

* `TauCeti.DynkinType.chevalleyGenerator`: the raising and lowering generators as one numbered
  family.
* `TauCeti.DynkinType.kostantForm`: the Kostant integral form of the pinned split Lie algebra.
* `TauCeti.DynkinType.geckRepresentation`: the defining matrix representation of `U(L)`.
* `TauCeti.DynkinType.geckWeight`: the integral weight of a Geck coordinate.
* `TauCeti.DynkinType.geckLattice`: the integral orbit of the standard lattice of the Geck module.

## Main results

* `TauCeti.DynkinType.span_kostantForm_eq_top`: the Kostant form spans the enveloping algebra
  over `ℚ`.
* `TauCeti.DynkinType.isNilpotent_geckRepresentation_chevalleyGenerator`: each numbered generator
  acts nilpotently.
* `TauCeti.DynkinType.geckRepresentation_cartanGenerator_apply_single`: the standard coordinate
  vectors are joint eigenvectors of the Cartan generators, with integer eigenvalues.
* `TauCeti.DynkinType.geckRepresentation_mem_geckLattice` and
  `TauCeti.DynkinType.span_geckLattice_eq_top`: the integral orbit is stable under the Kostant form
  and spans the Geck module over `ℚ`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the split reductive group scheme
over `ℤ` to be constructed "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping
algebra". This file is the first instance in which that form is attached to the pinned data of a
Dynkin type rather than carried as a hypothesis, and its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.DynkinType

open RootPairing.GeckConstruction Set

open scoped _root_.Matrix

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads
-- them; `TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/LieAlgebra.lean` activates the
-- same instance locally.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

variable (t : DynkinType) (ht : t.Valid)

/-! ## The numbered generators -/

/-- **The nilpotent Chevalley generators of the pinned Lie algebra**, gathered into a single family
numbered by `Fin t.rank ⊕ Fin t.rank`: the left summand carries the raising generators and the
right summand the lowering ones.

The Kostant integral form is generated by the divided powers of a single family of root vectors,
so the two halves of a pinning have to be presented as one indexed family before it can be
formed. -/
@[expose] def chevalleyGenerator : Fin t.rank ⊕ Fin t.rank → t.lieAlgebra ht :=
  Sum.elim (t.lieBasis ht).e (t.lieBasis ht).f

@[simp] theorem chevalleyGenerator_inl (i : Fin t.rank) :
    t.chevalleyGenerator ht (Sum.inl i) = (t.lieBasis ht).e i := rfl

@[simp] theorem chevalleyGenerator_inr (i : Fin t.rank) :
    t.chevalleyGenerator ht (Sum.inr i) = (t.lieBasis ht).f i := rfl

/-- The numbered generators are exactly the raising and lowering generators. -/
theorem range_chevalleyGenerator :
    range (t.chevalleyGenerator ht) =
      range (t.lieBasis ht).e ∪ range (t.lieBasis ht).f :=
  Sum.elim_range _ _

/-- **The Cartan generators of the pinned Lie algebra**, numbered by Bourbaki node. This is the
family of Cartan vectors whose binomial coefficients generate the Kostant form. -/
@[expose] def cartanGenerator : Fin t.rank → t.lieAlgebra ht := (t.lieBasis ht).h

@[simp] theorem cartanGenerator_apply (i : Fin t.rank) :
    t.cartanGenerator ht i = (t.lieBasis ht).h i := rfl

/-- The numbered root and Cartan generators generate the pinned Lie algebra. The raising and
lowering generators already do, by `TauCeti.DynkinType.lieSpan_lieBasis_e_union_f_eq_top`; the
Cartan generators are along for the ride because the Kostant form needs both families. -/
theorem lieSpan_range_chevalleyGenerator_union_range_cartanGenerator :
    LieSubalgebra.lieSpan ℚ (t.lieAlgebra ht)
      (range (t.chevalleyGenerator ht) ∪ range (t.cartanGenerator ht)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← t.lieSpan_lieBasis_e_union_f_eq_top ht]
  refine LieSubalgebra.lieSpan_mono ?_
  rw [range_chevalleyGenerator]
  exact subset_union_left

/-! ## The Kostant integral form -/

/-- **The Kostant integral form of the pinned split Lie algebra of a valid Dynkin type**: the
subring of `U(L)` generated by the divided powers of the numbered raising and lowering generators
together with the binomial coefficients of the numbered Cartan generators. -/
def kostantForm :
    Subring (_root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)) :=
  UniversalEnvelopingAlgebra.kostantForm (t.chevalleyGenerator ht) (t.cartanGenerator ht)

theorem kostantForm_def :
    t.kostantForm ht =
      UniversalEnvelopingAlgebra.kostantForm (t.chevalleyGenerator ht) (t.cartanGenerator ht) :=
  (rfl)

/-- Every divided power of a numbered raising or lowering generator lies in the Kostant form. -/
theorem dividedPower_mem_kostantForm (i : Fin t.rank ⊕ Fin t.rank) (n : ℕ) :
    Associative.dividedPower n
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleyGenerator ht i)) ∈ t.kostantForm ht :=
  UniversalEnvelopingAlgebra.dividedPower_mem_kostantForm _ _ i n

/-- Every binomial coefficient of a numbered Cartan generator lies in the Kostant form. -/
theorem ringChoose_mem_kostantForm (i : Fin t.rank) (n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.cartanGenerator ht i)) n ∈
      t.kostantForm ht :=
  UniversalEnvelopingAlgebra.ringChoose_mem_kostantForm _ _ i n

/-- **The Kostant form is an integral form.** Its `ℚ`-span is the whole universal enveloping
algebra of the pinned split Lie algebra.

This is the half of "`U_ℤ` is a `ℤ`-form of `U(L)`" that does not need the integral
Poincaré--Birkhoff--Witt theorem, and the pinned generators discharge its hypothesis outright:
`TauCeti.DynkinType.lieSpan_lieBasis_e_union_f_eq_top` is part of the numbered data. -/
theorem span_kostantForm_eq_top :
    Submodule.span ℚ (t.kostantForm ht :
        Set (_root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht))) = ⊤ :=
  UniversalEnvelopingAlgebra.span_kostantForm_eq_top _ _
    (t.lieSpan_range_chevalleyGenerator_union_range_cartanGenerator ht)

/-! ## The defining representation -/

/-- **The defining representation of the pinned split Lie algebra**, extended to its universal
enveloping algebra. Geck's Lie algebra is a Lie subalgebra of matrices, so the representation is
the matrix action on coordinate vectors; no existence theorem for a faithful representation is
invoked. -/
def geckRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ]
      Module.End ℚ (t.GeckIndex ht → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    (LieHom.comp
      (AlgHom.toLieHom
        (Matrix.toLinAlgEquiv' (n := t.GeckIndex ht) (R := ℚ)).toAlgHom)
      (t.lieAlgebra ht).incl)

-- Neither this lemma nor its pointwise form below is a `simp` lemma: `simp` unfolds `ι` through
-- Mathlib's `UniversalEnvelopingAlgebra.ι_apply`, so a left-hand side mentioning `ι` is not in
-- simp-normal form.
/-- A Lie generator acts through its underlying matrix. -/
theorem geckRepresentation_ι (x : t.lieAlgebra ht) :
    t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Matrix.toLinAlgEquiv' (x : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply ℚ _ x

/-- The pointwise form of `TauCeti.DynkinType.geckRepresentation_ι`: a Lie generator acts by
multiplying a coordinate vector by its underlying matrix. -/
theorem geckRepresentation_ι_apply (x : t.lieAlgebra ht) (v : t.GeckIndex ht → ℚ) :
    t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      (x : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *ᵥ v := by
  rw [geckRepresentation_ι, Matrix.toLinAlgEquiv'_apply]

/-- **The defining representation is faithful.** Distinct elements of the pinned Lie algebra act
differently, so the Lie algebra embeds in the endomorphisms of the Geck module. -/
theorem geckRepresentation_ι_injective :
    Function.Injective fun x : t.lieAlgebra ht =>
      t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  intro x y hxy
  simp only [geckRepresentation_ι] at hxy
  exact Subtype.ext (Matrix.toLinAlgEquiv'.injective hxy)

/-! ## Nilpotency of the numbered generators -/

/-- **Every numbered generator acts nilpotently.** This is what makes the divided-power
exponential of a root vector a finite sum, hence an automorphism of any stable lattice over any
value ring. -/
theorem isNilpotent_geckRepresentation_chevalleyGenerator (i : Fin t.rank ⊕ Fin t.rank) :
    IsNilpotent (t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleyGenerator ht i))) := by
  rw [geckRepresentation_ι]
  refine IsNilpotent.map ?_ (Matrix.toLinAlgEquiv' (n := t.GeckIndex ht) (R := ℚ)).toRingHom
  cases i with
  | inl i => exact t.isNilpotent_coe_lieBasis_e ht i
  | inr i => exact t.isNilpotent_coe_lieBasis_f ht i

/-! ## The weights of the Geck module -/

/-- **The integral weight of a Geck coordinate**, in the Bourbaki numbering: zero on the
coordinates indexed by the pinned base support, and the Cartan pairing `⟨α_k, α_i^∨⟩` on the
coordinate indexed by the root `α_k`.

Geck's Cartan matrices are diagonal with these entries, so this is the weight function of the
standard lattice of the Geck module, and it takes values in `ℤ` rather than merely in `ℚ`. -/
@[expose] def geckWeight : t.GeckIndex ht → Fin t.rank → ℤ :=
  Sum.elim 0 fun k i => (t.rationalRootSystem ht).pairingIn ℤ k (t.simpleSupportEquiv ht i)

@[simp] theorem geckWeight_inl (x : (t.rationalBase ht).support) (i : Fin t.rank) :
    t.geckWeight ht (Sum.inl x) i = 0 := rfl

@[simp] theorem geckWeight_inr (k : Fin t.numRoots) (i : Fin t.rank) :
    t.geckWeight ht (Sum.inr k) i =
      (t.rationalRootSystem ht).pairingIn ℤ k (t.simpleSupportEquiv ht i) := rfl

/-- **The standard coordinate vectors are joint eigenvectors of the Cartan generators**, with the
integer eigenvalues recorded by `TauCeti.DynkinType.geckWeight`.

This is the pinned split torus in embryo: the diagonal action of the Cartan subalgebra on the
standard lattice of the Geck module is by integral characters, numbered by Bourbaki node. -/
theorem geckRepresentation_cartanGenerator_apply_single (i : Fin t.rank) (x : t.GeckIndex ht) :
    t.geckRepresentation ht (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.cartanGenerator ht i))
        (Pi.single x 1) = (t.geckWeight ht x i : ℚ) • Pi.single x 1 := by
  classical
  rw [geckRepresentation_ι_apply, cartanGenerator_apply, coe_lieBasis_h, h_eq_diagonal,
    Matrix.diagonal_mulVec_single, mul_one, ← Pi.single_smul', smul_eq_mul, mul_one]
  cases x with
  | inl x => simp [geckWeight]
  | inr k => simp [geckWeight]

/-! ## The integral orbit of the standard lattice -/

/-- **The integral orbit of the standard lattice of the Geck module**: the `ℤ`-span of the images
of the standard coordinate vectors under the Kostant integral form.

Every downstream consumer of a Kostant root subgroup takes a `ℤ`-submodule preserved by the whole
integral form as a hypothesis. This one is preserved by construction, by
`TauCeti.DynkinType.geckRepresentation_mem_geckLattice`, and it is full by
`TauCeti.DynkinType.span_geckLattice_eq_top`. It is *not* asserted to be finitely generated, which
is the remaining half of the admissible-lattice statement of Humphreys §27 and needs the integral
Poincaré--Birkhoff--Witt theorem. -/
def geckLattice : Submodule ℤ (t.GeckIndex ht → ℚ) :=
  Submodule.span ℤ
    {v | ∃ u ∈ t.kostantForm ht, ∃ x, t.geckRepresentation ht u (Pi.single x 1) = v}

/-- Every standard coordinate vector lies in the integral orbit, the identity of the enveloping
algebra being one of the elements the orbit is taken over. -/
theorem single_mem_geckLattice (x : t.GeckIndex ht) :
    Pi.single x (1 : ℚ) ∈ t.geckLattice ht :=
  Submodule.subset_span ⟨1, (t.kostantForm ht).one_mem, x, by rw [map_one, Module.End.one_apply]⟩

/-- **The integral orbit is stable under the Kostant form.** This is the hypothesis a Kostant root
subgroup needs of the lattice it acts on, and it holds here because the orbit is taken over a
subring: acting again multiplies inside the form. -/
theorem geckRepresentation_mem_geckLattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht)} (hu : u ∈ t.kostantForm ht)
    {v : t.GeckIndex ht → ℚ} (hv : v ∈ t.geckLattice ht) :
    t.geckRepresentation ht u v ∈ t.geckLattice ht := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨u', hu', x, rfl⟩ := hw
      refine Submodule.subset_span ⟨u * u', (t.kostantForm ht).mul_mem hu hu', x, ?_⟩
      rw [map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_zsmul]; exact Submodule.smul_mem _ c ha

/-- **The integral orbit is full.** It spans the Geck module over `ℚ`, because it already contains
the standard coordinate vectors. -/
theorem span_geckLattice_eq_top :
    Submodule.span ℚ (t.geckLattice ht : Set (t.GeckIndex ht → ℚ)) = ⊤ := by
  classical
  refine top_le_iff.mp ?_
  rw [← (Pi.basisFun ℚ (t.GeckIndex ht)).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro - ⟨x, rfl⟩
  exact Submodule.subset_span (by simpa using t.single_mem_geckLattice ht x)

end

end TauCeti.DynkinType
