/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.RegularSubcomodule
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.Coalgebra.Subcoalgebra.Finite
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# A linearly reductive unipotent affine group is trivial

Let `H` be a reduced finite-type commutative Hopf algebra over an algebraically closed field `k`
all of whose points are unipotent. Kolchin's theorem, in the form already available from
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding`, gives a nonzero fixed vector in every
nonzero finite-dimensional comodule, hence in every nonzero subcomodule of one. If `H` is also
linearly reductive, the fixed subcomodule of a finite-dimensional comodule has a subcomodule
complement, which then has no nonzero fixed vector and so vanishes: the coaction of every
finite-dimensional comodule is trivial.

Applying this to the finite-dimensional subcoalgebras of the regular comodule, which exhaust `H`
over a field, gives `Δ h = h ⊗ 1` for every `h`, hence `h = ε(h) · 1`. So the counit is injective,
the augmentation ideal vanishes, and the counit is a bialgebra equivalence `H ≃ k`; equivalently
the group of points over every commutative value algebra is trivial.

Smoothness may replace reducedness, since a smooth algebra over a field is reduced. That is the
form the roadmap's definitions are stated in, so it is also given for the object properties
`TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty` and
`TauCeti.linearlyReductiveCommHopfAlgProperty`.

## Main declarations

* `TauCeti.Comodule.exists_mem_ne_zero_coact_eq_tmul_one_of_forall_isUnipotentPoint`: every
  nonzero subcomodule of a finite-dimensional comodule over a unipotent group has a nonzero fixed
  vector.
* `TauCeti.Comodule.coact_eq_tmul_one_of_isCompletelyReducible_of_forall_isUnipotentPoint`: a
  unipotent group acts trivially on every completely reducible finite-dimensional
  representation.
* `TauCeti.HopfAlgebra.comul_eq_tmul_one_of_isLinearlyReductive_of_forall_exists_fixed`: the
  regular comodule of a linearly reductive coalgebra with enough fixed vectors is trivial; this is
  the step of the argument that does not mention unipotence.
* `TauCeti.HopfAlgebra.comul_eq_tmul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint` and
  `TauCeti.HopfAlgebra.eq_counit_smul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint`: the
  coordinate algebra of a linearly reductive unipotent group is spanned by `1`.
* `TauCeti.HopfAlgebra.counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint`: **a
  linearly reductive unipotent affine group is trivial**, together with its smooth form
  `TauCeti.HopfAlgebra.counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint` and
  the object-property form
  `counitBialgEquivOfLinearlyReductive` in the
  `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty` namespace.
* `TauCeti.HopfAlgebra.subsingleton_algHom_of_isLinearlyReductive_of_forall_isUnipotentPoint`: the
  functor-of-points form of triviality.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.45 and §22.42: a linearly reductive group
  has no nontrivial unipotent normal subgroup, of which this is the case where the whole group is
  unipotent.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2 and §8.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

This is the first theorem relating the two Layer 6 notions of the ReductiveGroups roadmap,
reductivity defined by a trivial geometric unipotent radical and linear reductivity defined by
complete reducibility. It is the step that rules out unipotent subgroups; deducing reductivity
from linear reductivity in general still needs the invariants of a normal closed subgroup to be
a subrepresentation of the ambient group.
-/

public section

open scoped TensorProduct

namespace TauCeti

open WithConv

universe u v w

noncomputable section

variable {k : Type u} {H : Type v}
variable [Field k] [CommRing H] [HopfAlgebra k H]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

namespace Comodule

variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]

/-- Kolchin's theorem, applied to a nonzero subcomodule: over a reduced finite-type commutative
Hopf algebra with unipotent points, every nonzero subcomodule of a finite-dimensional comodule
contains a nonzero vector fixed by the ambient coaction. -/
theorem exists_mem_ne_zero_coact_eq_tmul_one_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] [FiniteDimensional k M]
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g)
    (N : Subcomodule k H M) (hN : N ≠ ⊥) :
    ∃ v ∈ N, v ≠ 0 ∧ coact (R := k) (C := H) (M := M) v = v ⊗ₜ[k] (1 : H) := by
  obtain ⟨w, hwN, hw0⟩ := Subcomodule.ne_bot_iff.mp hN
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  -- `↥N` and `↥N.toSubmodule` subtype the same carrier, so finite-dimensionality transfers.
  have _ : FiniteDimensional k N := inferInstanceAs (FiniteDimensional k N.toSubmodule)
  have _ : Nontrivial N := ⟨⟨⟨w, hwN⟩, 0, fun hc ↦ hw0 (congrArg Subtype.val hc)⟩⟩
  obtain ⟨v, hv, hvc⟩ :=
    (hasNonzeroFixedVector_iff (k := k) (H := H) (M := N)).mp
      (hasNonzeroFixedVector_of_forall_isUnipotentPoint (M := N) hH)
  exact ⟨v, v.2, fun hc ↦ hv (Subtype.ext hc), Subcomodule.coact_coe_eq_tmul_one N hvc⟩

/-- If a finite-dimensional comodule over a reduced finite-type commutative Hopf algebra with
unipotent points is completely reducible, then the coaction is trivial on it: the represented
unipotent group acts trivially on every completely reducible representation. -/
theorem coact_eq_tmul_one_of_isCompletelyReducible_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] [FiniteDimensional k M]
    (hcr : IsCompletelyReducible k H M)
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) (m : M) :
    coact (R := k) (C := H) (M := M) m = m ⊗ₜ[k] (1 : H) :=
  coact_eq_tmul_one_of_isCompletelyReducible_of_forall_exists_fixed hcr
    (exists_mem_ne_zero_coact_eq_tmul_one_of_forall_isUnipotentPoint hH) m

end Comodule

namespace HopfAlgebra

variable (k' : Type u) (H' : Type v) [Field k'] [AddCommGroup H'] [Module k' H']
  [Coalgebra k' H'] [One H'] in
/-- If `H` is linearly reductive and every nonzero subcomodule of a finite-dimensional comodule
contains a nonzero fixed vector, then comultiplication sends every element `h` to `h ⊗ 1`: the
regular comodule is trivial.

This is the coalgebra-level core of the triviality theorem. The element `h` lies in a
finite-dimensional subcoalgebra, hence in a finite-dimensional subcomodule of the regular
comodule, on which complete reducibility and the supply of fixed vectors force the coaction to be
trivial. Unipotence enters only through that supply of fixed vectors. -/
theorem comul_eq_tmul_one_of_isLinearlyReductive_of_forall_exists_fixed
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k' H')
    (hfix : ∀ (V : Type v) [AddCommGroup V] [Module k' V] [Comodule k' H' V]
      [FiniteDimensional k' V] (N : Subcomodule k' H' V), N ≠ ⊥ →
        ∃ v ∈ N, v ≠ 0 ∧ Comodule.coact (R := k') (C := H') (M := V) v =
          v ⊗ₜ[k'] (1 : H'))
    (h : H') : Coalgebra.comul (R := k') h = h ⊗ₜ[k'] (1 : H') := by
  obtain ⟨D, hDfin, hD⟩ := Subcoalgebra.exists_finiteDimensional_subcoalgebra_mem (k := k') h
  set N : Subcomodule k' H' H' := D.toRegularSubcomodule with hNdef
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k'
  have hNfin : FiniteDimensional k' N.toSubmodule := by
    rw [hNdef, Subcoalgebra.toRegularSubcomodule_toSubmodule]
    exact hDfin
  -- `↥N` and `↥N.toSubmodule` subtype the same carrier, so finite-dimensionality transfers.
  have _ : FiniteDimensional k' N := hNfin
  have hmem : h ∈ N := Subcoalgebra.mem_toRegularSubcomodule.mpr hD
  have hfixN := Comodule.coact_eq_tmul_one_of_isCompletelyReducible_of_forall_exists_fixed
    hlr.isCompletelyReducible (hfix N) ⟨h, hmem⟩
  have hpush := Subcomodule.coact_coe_eq_tmul_one N hfixN
  rwa [Comodule.instSelf_coact] at hpush

variable (k H) in
/-- In a linearly reductive reduced finite-type commutative Hopf algebra over an algebraically
closed field with unipotent points, comultiplication sends every element `h` to `h ⊗ 1`: the
regular comodule is trivial. -/
theorem comul_eq_tmul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) (h : H) :
    Coalgebra.comul (R := k) h = h ⊗ₜ[k] (1 : H) :=
  comul_eq_tmul_one_of_isLinearlyReductive_of_forall_exists_fixed k H hlr
    (fun _ _ _ _ _ N hN ↦
      Comodule.exists_mem_ne_zero_coact_eq_tmul_one_of_forall_isUnipotentPoint hH N hN) h

variable (k H) in
/-- Under the same hypotheses every element is a scalar multiple of `1`, the scalar being its
counit. -/
theorem eq_counit_smul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) (h : H) :
    h = Coalgebra.counit (R := k) h • (1 : H) :=
  Coalgebra.eq_counit_smul_of_comul_eq_tmul
    (comul_eq_tmul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint k H hlr hH h)

variable (k H) in
/-- Under the same hypotheses the augmentation ideal vanishes: the counit is injective. -/
theorem augmentation_eq_bot_of_isLinearlyReductive_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    HopfIdeal.augmentation k H = ⊥ := by
  refine HopfIdeal.ext fun x ↦ ?_
  rw [HopfIdeal.mem_augmentation, HopfIdeal.mem_bot]
  refine ⟨fun hx ↦ ?_, fun hx ↦ by rw [hx, map_zero]⟩
  rw [eq_counit_smul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint k H hlr hH x, hx,
    zero_smul]

variable (k H) in
/-- **A linearly reductive unipotent affine group is trivial.**

A reduced finite-type commutative Hopf algebra over an algebraically closed field, all of whose
points are unipotent, is bialgebra-equivalent to the ground field via its counit as soon as it is
linearly reductive. -/
def counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    H ≃ₐc[k] k :=
  HopfIdeal.counitBialgEquivOfAugmentationEqBot
    (augmentation_eq_bot_of_isLinearlyReductive_of_forall_isUnipotentPoint k H hlr hH)

variable (k H) in
/-- The triviality equivalence is the counit. -/
@[simp]
theorem counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint_apply
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) (x : H) :
    counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint k H hlr hH x =
      Bialgebra.counitBialgHom k H x := by
  rw [counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint]
  exact HopfIdeal.counitBialgEquivOfAugmentationEqBot_apply _ _

variable (k H) in
/-- The inverse of the triviality equivalence is the structure map. -/
@[simp]
theorem counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint_symm_apply
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) (r : k) :
    (counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint k H hlr hH).symm r =
      algebraMap k H r := by
  rw [counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint]
  exact HopfIdeal.counitBialgEquivOfAugmentationEqBot_symm_apply _ _

variable (k H) in
/-- Under the same hypotheses the group of points over every commutative value algebra is
trivial: this is the functor-of-points form of the statement that the group is trivial. -/
theorem subsingleton_algHom_of_isLinearlyReductive_of_forall_isUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g)
    (A : Type w) [CommRing A] [Algebra k A] :
    Subsingleton (H →ₐ[k] A) := by
  refine ⟨fun f g ↦ AlgHom.ext fun h ↦ ?_⟩
  rw [eq_counit_smul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint k H hlr hH h]
  simp

variable (k H) in
/-- The smooth form of
`TauCeti.HopfAlgebra.counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint`: over a
field, smoothness supplies the reducedness hypothesis. -/
def counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint
    [IsAlgClosed k] [Algebra.FiniteType k H] (hsm : Algebra.Smooth k H)
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    H ≃ₐc[k] k :=
  letI := hsm
  letI : IsReduced H := isReduced_of_smooth_of_field k H
  counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint k H hlr hH

variable (k H) in
/-- The smooth triviality equivalence is the counit. -/
@[simp]
theorem counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint_apply
    [IsAlgClosed k] [Algebra.FiniteType k H] (hsm : Algebra.Smooth k H)
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) (x : H) :
    counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint k H hsm hlr hH x =
      Bialgebra.counitBialgHom k H x := by
  let _ := hsm
  let _ : IsReduced H := isReduced_of_smooth_of_field k H
  rw [counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint]
  exact counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint_apply k H hlr hH x

variable (k H) in
/-- The inverse of the smooth triviality equivalence is the structure map. -/
@[simp]
theorem counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint_symm_apply
    [IsAlgClosed k] [Algebra.FiniteType k H] (hsm : Algebra.Smooth k H)
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) (r : k) :
    (counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint k H hsm hlr hH).symm
        r = algebraMap k H r := by
  let _ := hsm
  let _ : IsReduced H := isReduced_of_smooth_of_field k H
  rw [counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint]
  exact counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint_symm_apply k H hlr hH r

end HopfAlgebra

namespace geometricallyUnipotentPointsCommHopfAlgProperty

/-- **A smooth linearly reductive unipotent affine group of finite type over an algebraically
closed field is trivial**, stated for the object properties on commutative Hopf algebras: the
counit is a bialgebra equivalence onto the ground field. -/
def counitBialgEquivOfLinearlyReductive [IsAlgClosed k] [Algebra.FiniteType k H]
    (hu : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hsm : Algebra.Smooth k H)
    (hlr : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.of k H)) :
    H ≃ₐc[k] k :=
  HopfAlgebra.counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint k H hsm
    ((linearlyReductiveCommHopfAlgProperty_iff k (CommHopfAlgCat.of k H)).mp hlr)
    (forall_isUnipotentPoint hu)

/-- The object-property triviality equivalence is the counit. -/
@[simp]
theorem counitBialgEquivOfLinearlyReductive_apply [IsAlgClosed k] [Algebra.FiniteType k H]
    (hu : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hsm : Algebra.Smooth k H)
    (hlr : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.of k H)) (x : H) :
    counitBialgEquivOfLinearlyReductive hu hsm hlr x = Bialgebra.counitBialgHom k H x := by
  rw [counitBialgEquivOfLinearlyReductive]
  exact HopfAlgebra.counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint_apply
    k H hsm _ _ x

/-- The inverse of the object-property triviality equivalence is the structure map. -/
@[simp]
theorem counitBialgEquivOfLinearlyReductive_symm_apply [IsAlgClosed k] [Algebra.FiniteType k H]
    (hu : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hsm : Algebra.Smooth k H)
    (hlr : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.of k H)) (r : k) :
    (counitBialgEquivOfLinearlyReductive hu hsm hlr).symm r = algebraMap k H r := by
  rw [counitBialgEquivOfLinearlyReductive]
  exact
    HopfAlgebra.counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint_symm_apply
      k H hsm _ _ r

end geometricallyUnipotentPointsCommHopfAlgProperty

end

end TauCeti
