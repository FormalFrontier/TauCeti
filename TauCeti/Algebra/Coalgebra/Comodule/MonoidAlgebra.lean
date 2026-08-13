/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# The weight decomposition of a comodule over a monoid algebra

Let `R[G]` be the monoid algebra of a type `G` over a commutative semiring `R`. Its coalgebra
structure makes every `single g 1` a group-like element. This file proves that a right
`R[G]`-comodule `V` is the internal direct sum of its weight submodules

`weightSpace R G V g = {v | ρ v = v ⊗ single g 1}`,

each of which is a subcomodule. When `G` is a commutative group, `R[G]` is the coordinate Hopf
algebra of the diagonalizable group `D(G)`, and this says that its representations decompose into
character spaces.

The proof is the classical one and uses nothing beyond the comodule axioms. Writing the coaction
of `v` as `ρ v = ∑ g, v g ⊗ single g 1`, which is possible because `R[G]` is free on the
group-like elements, the counit axiom says that the coefficients sum to `v` and coassociativity
says that the `h`-coefficient of `v g` is `v g` when `h = g` and `0` otherwise. The coefficient
maps are therefore orthogonal idempotents with images the weight submodules, which gives both the
spanning and the independence half of the decomposition.

## Main definitions

* `TauCeti.Comodule.tensorComponent`: the `g`-th coefficient map of `V ⊗[R] R[G]`.
* `TauCeti.Comodule.tensorCoeffEquiv`: the coefficients of an element of `V ⊗[R] R[G]`, as a
  finitely supported family.
* `TauCeti.Comodule.weightDecomposition`: the weight components of a comodule, as a linear map to
  finitely supported families.
* `TauCeti.Comodule.weightProj`: the projection onto the `g`-weight component.
* `TauCeti.Comodule.weightSpace`: the `g`-weight submodule, where the coaction is `v ↦ v ⊗ g`.
* `TauCeti.Comodule.weightSubcomodule`: the weight submodule as a subcomodule.

## Main results

* `TauCeti.Comodule.weightDecomposition_sum`: the weight components of a vector sum to it.
* `TauCeti.Comodule.weightProj_weightProj_self` and
  `TauCeti.Comodule.weightProj_weightProj_of_ne`: the weight projections are orthogonal
  idempotents.
* `TauCeti.Comodule.weightProj_mem_weightSpace`: each weight component lies in its weight
  submodule.
* `TauCeti.Comodule.isInternal_weightSpace`: **a comodule over a monoid algebra is the internal
  direct sum of its weight submodules.**
* `TauCeti.Comodule.endOfPoint_tmul_of_mem_weightSpace`: an algebra map out of `R[G]` acts on the
  `g`-weight submodule by multiplication by its value at the group-like element `single g 1`.
* `TauCeti.Comodule.Hom.map_mem_weightSpace`: a comodule morphism preserves the weight
  submodules.
* `TauCeti.Comodule.range_weightProj`: the `g`-weight submodule is the range of the `g`-weight
  projection.
* `TauCeti.Comodule.finite_setOf_weightSpace_ne_bot`: **a comodule finitely generated as a module
  has only finitely many weights.**

## Implementation notes

Only the coalgebra structure of `R[G]` is used, so `G` is an arbitrary type: no multiplication on
`G` and no algebra structure on `R[G]` enter the argument. That `R[G]` is free on `G` is used
through `TensorProduct.finsuppScalarRight`, which presents `V ⊗[R] R[G]` as the finitely supported
functions `G →₀ V` and so supplies the finite support of the weight decomposition for free; this is
also the only place where decidable equality on `G` is used internally, and it is discharged
classically.

## References

For a commutative group `G`, this specializes to the standard statement that representations of a
diagonalizable group are diagonalizable; see Waterhouse, *Introduction to Affine Group Schemes*,
§3.2, and Milne, *Algebraic Groups* (2017), Theorem 12.12.

It supplies a prerequisite for the Tau Ceti reductive-groups roadmap, `ReductiveGroups/README.md`
in TauCetiRoadmap: Layer 6 asks for the linear reductivity of tori ("over an algebraically closed
field of characteristic `p`, a connected group is linearly reductive iff it is a torus"), of which
this is the substantive direction for a split torus, and Layer 7's root datum of a split pair
`(G, T)` is read off the weight decomposition of `Lie G` under `T` that this file provides. The
diagonalizable group `D(G) = Spec R[G]` itself is in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic`.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe u v w

namespace Comodule

variable (R : Type u) (G : Type v) (V : Type w)
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/-! ## Coefficients of a tensor with a monoid algebra -/

section Component

/-- The `g`-th coefficient map of `V ⊗[R] R[G]`, sending `v ⊗ x` to `x.coeff g • v`. The coaction
of a comodule over `R[G]` is recovered from these coefficients, which are its weight
components. -/
noncomputable def tensorComponent (g : G) : V ⊗[R] MonoidAlgebra R G →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ
    (Finsupp.lapply g ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap).lTensor V

variable {R G V}

@[simp]
theorem tensorComponent_tmul (g : G) (v : V) (x : MonoidAlgebra R G) :
    tensorComponent R G V g (v ⊗ₜ[R] x) = x.coeff g • v := by
  simp [tensorComponent]

variable (R G V)

/-- The coefficients of an element of `V ⊗[R] R[G]`, as a finitely supported family. -/
noncomputable def tensorCoeffEquiv : V ⊗[R] MonoidAlgebra R G ≃ₗ[R] G →₀ V := by
  classical
  exact (LinearEquiv.lTensor V (MonoidAlgebra.coeffLinearEquiv R)).trans
    (TensorProduct.finsuppScalarRight R R V G)

variable {R G V}

/-- The coefficient family of an element of `V ⊗[R] R[G]` is given by the coefficient maps. -/
@[simp]
theorem tensorCoeffEquiv_apply (t : V ⊗[R] MonoidAlgebra R G) (g : G) :
    tensorCoeffEquiv R G V t g = tensorComponent R G V g t := by
  classical
  have h : (Finsupp.lapply g).comp (tensorCoeffEquiv R G V).toLinearMap =
      tensorComponent R G V g := TensorProduct.ext' fun v x => by simp [tensorCoeffEquiv]
  exact congr($h t)

/-- The coefficient family of a pure tensor scales the vector by the coefficients. -/
@[simp]
theorem tensorCoeffEquiv_tmul (v : V) (x : MonoidAlgebra R G) :
    tensorCoeffEquiv R G V (v ⊗ₜ[R] x) =
      Finsupp.mapRange (fun r : R => r • v) (zero_smul R v) x.coeff :=
  by
    classical
    exact Finsupp.ext fun g => by simp

@[simp]
theorem tensorCoeffEquiv_symm_single (g : G) (v : V) :
    (tensorCoeffEquiv R G V).symm (Finsupp.single g v) =
      v ⊗ₜ[R] MonoidAlgebra.single g (1 : R) := by
  classical
  simp [tensorCoeffEquiv, LinearEquiv.symm_lTensor]

end Component

/-! ## The weight components of a comodule -/

section Weight

variable [Comodule R (MonoidAlgebra R G) V]

/-- The projection of a comodule over `R[G]` onto its `g`-weight component. -/
noncomputable def weightProj (g : G) : V →ₗ[R] V :=
  tensorComponent R G V g ∘ₗ coact (R := R) (C := MonoidAlgebra R G) (M := V)

variable {R G V} in
/-- The `g`-weight component of `v` is the `g`-th coefficient of its coaction.

This is deliberately not a `simp` lemma: `weightProj_weightProj_self` and
`weightProj_weightProj_of_ne` are the simp-normal form of a composite of weight projections, and
they could never fire if `simp` first unfolded every `weightProj` to a coefficient of a coaction. -/
theorem weightProj_apply (g : G) (v : V) :
    weightProj R G V g v = tensorComponent R G V g (coact (R := R) (C := MonoidAlgebra R G) v) :=
  (rfl)

/-- The weight components of a comodule over `R[G]`, read off its coaction as a finitely supported
family. -/
noncomputable def weightDecomposition : V →ₗ[R] (G →₀ V) :=
  (tensorCoeffEquiv R G V).toLinearMap ∘ₗ coact (R := R) (C := MonoidAlgebra R G) (M := V)

variable {R G V}

@[simp]
theorem weightDecomposition_apply (v : V) (g : G) :
    weightDecomposition R G V v g = weightProj R G V g v := by
  simp [weightDecomposition, weightProj_apply]

/-- The coaction is determined by the weight components. -/
theorem coact_eq_symm_weightDecomposition (v : V) :
    coact (R := R) (C := MonoidAlgebra R G) v =
      (tensorCoeffEquiv R G V).symm (weightDecomposition R G V v) := by
  simp [weightDecomposition]

end Weight

/-! ### The counit axiom: the weight components sum to the vector -/

section Counit

variable {R G V}

private theorem counit_eq_sum (x : MonoidAlgebra R G) :
    Coalgebra.counit (R := R) x = x.coeff.sum fun _ r => r := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  rw [Finsupp.sum, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun g _ => by simp

variable (R G V) in
/-- Adding up all the coefficients of a finitely supported family. -/
private noncomputable def totalSum : (G →₀ V) →ₗ[R] V := Finsupp.lsum R fun _ => LinearMap.id

private theorem totalSum_apply (f : G →₀ V) : totalSum R G V f = f.sum fun _ w => w := rfl

variable (R G V) in
private theorem totalSum_comp_tensorCoeffEquiv :
    totalSum R G V ∘ₗ (tensorCoeffEquiv R G V).toLinearMap =
      (TensorProduct.rid R V).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := MonoidAlgebra R G)).lTensor V := by
  classical
  refine TensorProduct.ext' fun v x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, counit_eq_sum, totalSum_apply,
    tensorCoeffEquiv_tmul]
  rw [Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.sum, Finsupp.sum, Finset.sum_smul]

variable [Comodule R (MonoidAlgebra R G) V]

/-- **The weight components of a vector sum to it.** This is the counit axiom of the coaction. -/
theorem weightDecomposition_sum (v : V) :
    (weightDecomposition R G V v).sum (fun _ w => w) = v := by
  classical
  have h := congr($(totalSum_comp_tensorCoeffEquiv R G V)
    (coact (R := R) (C := MonoidAlgebra R G) v))
  simpa [totalSum_apply, weightDecomposition] using h

end Counit

/-! ### Coassociativity: the weight projections are orthogonal idempotents -/

section Coassoc

/-- The pair of coefficient maps of `R[G] ⊗[R] R[G]`, contracted to a scalar. -/
private noncomputable def pairCoeff (h g : G) :
    MonoidAlgebra R G ⊗[R] MonoidAlgebra R G →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap ∘ₗ
    TensorProduct.map (Finsupp.lapply h ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)
      (Finsupp.lapply g ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)

/-- The double coefficient map of `V ⊗[R] (R[G] ⊗[R] R[G])`. -/
private noncomputable def doubleComponent (h g : G) :
    V ⊗[R] (MonoidAlgebra R G ⊗[R] MonoidAlgebra R G) →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ (pairCoeff R G h g).lTensor V

variable {R G V}

private theorem pairCoeff_tmul (h g : G) (x y : MonoidAlgebra R G) :
    pairCoeff R G h g (x ⊗ₜ[R] y) = x.coeff h * y.coeff g := by
  simp [pairCoeff]

private theorem doubleComponent_tmul (h g : G) (v : V) (x y : MonoidAlgebra R G) :
    doubleComponent R G V h g (v ⊗ₜ[R] (x ⊗ₜ[R] y)) = (x.coeff h * y.coeff g) • v := by
  simp [doubleComponent, pairCoeff_tmul]

/-- Reassociating, the double coefficient map is a composite of two single ones. -/
private theorem doubleComponent_comp_assoc (h g : G) :
    doubleComponent R G V h g ∘ₗ
        (TensorProduct.assoc R V (MonoidAlgebra R G) (MonoidAlgebra R G)).toLinearMap =
      tensorComponent R G V h ∘ₗ tensorComponent R G (V ⊗[R] MonoidAlgebra R G) g :=
  TensorProduct.ext_threefold fun v x y => by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_tmul, doubleComponent_tmul, tensorComponent_tmul, map_smul, mul_smul]
    exact smul_comm _ _ _

/-- Composed with the comultiplication of `R[G]`, the pair of coefficient maps at equal indices is
a single coefficient map: the elements `single g 1` are group-like. -/
private theorem pairCoeff_comp_comul_self (g : G) :
    pairCoeff R G g g ∘ₗ Coalgebra.comul (R := R) (A := MonoidAlgebra R G) =
      Finsupp.lapply g ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
  refine MonoidAlgebra.lhom_ext' fun k => ?_
  ext
  by_cases hk : k = g <;> simp [pairCoeff_tmul, MonoidAlgebra.comul_single, hk]

/-- Composed with the comultiplication of `R[G]`, the pair of coefficient maps at distinct indices
vanishes. -/
private theorem pairCoeff_comp_comul_of_ne {h g : G} (hne : h ≠ g) :
    pairCoeff R G h g ∘ₗ Coalgebra.comul (R := R) (A := MonoidAlgebra R G) = 0 := by
  refine MonoidAlgebra.lhom_ext' fun k => ?_
  ext
  by_cases hk : k = g <;> simp [pairCoeff_tmul, MonoidAlgebra.comul_single, hk, hne]

variable [Comodule R (MonoidAlgebra R G) V]

/-- Taking a coefficient of the coaction on the left factor is the coaction of the coefficient. -/
private theorem tensorComponent_comp_rTensor_coact (g : G) :
    tensorComponent R G (V ⊗[R] MonoidAlgebra R G) g ∘ₗ
        (coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor (MonoidAlgebra R G) =
      coact (R := R) (C := MonoidAlgebra R G) (M := V) ∘ₗ tensorComponent R G V g :=
  TensorProduct.ext' fun v x => by simp

private theorem weightProj_weightProj_eq (h g : G) (v : V) :
    weightProj R G V h (weightProj R G V g v) =
      doubleComponent R G V h g
        ((Coalgebra.comul (R := R) (A := MonoidAlgebra R G)).lTensor V
          (coact (R := R) (C := MonoidAlgebra R G) v)) := by
  have key := congr($(doubleComponent_comp_assoc (R := R) (G := G) (V := V) h g)
    ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor (MonoidAlgebra R G)
      (coact (R := R) (C := MonoidAlgebra R G) v)))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, coassoc_apply] at key
  have hcomp := congr($(tensorComponent_comp_rTensor_coact (R := R) (G := G) (V := V) g)
    (coact (R := R) (C := MonoidAlgebra R G) v))
  simp only [LinearMap.coe_comp, Function.comp_apply] at hcomp
  rw [key, hcomp]
  rw [weightProj_apply, weightProj_apply]

/-- **The weight projections are idempotent.** -/
@[simp]
theorem weightProj_weightProj_self (g : G) (v : V) :
    weightProj R G V g (weightProj R G V g v) = weightProj R G V g v := by
  rw [weightProj_weightProj_eq]
  have h : doubleComponent R G V g g ∘ₗ
      (Coalgebra.comul (R := R) (A := MonoidAlgebra R G)).lTensor V =
        tensorComponent R G V g := by
    rw [doubleComponent, tensorComponent, LinearMap.comp_assoc, ← LinearMap.lTensor_comp,
      pairCoeff_comp_comul_self]
  exact congr($h (coact (R := R) (C := MonoidAlgebra R G) v))

/-- **The weight projections at distinct indices are orthogonal.** -/
@[simp]
theorem weightProj_weightProj_of_ne {h g : G} (hne : h ≠ g) (v : V) :
    weightProj R G V h (weightProj R G V g v) = 0 := by
  rw [weightProj_weightProj_eq]
  have h0 : doubleComponent R G V h g ∘ₗ
      (Coalgebra.comul (R := R) (A := MonoidAlgebra R G)).lTensor V = 0 := by
    rw [doubleComponent, LinearMap.comp_assoc, ← LinearMap.lTensor_comp,
      pairCoeff_comp_comul_of_ne hne, LinearMap.lTensor_zero, LinearMap.comp_zero]
  exact congr($h0 (coact (R := R) (C := MonoidAlgebra R G) v))

end Coassoc

/-! ## The weight submodules -/

section WeightSpace

variable [Comodule R (MonoidAlgebra R G) V]

/-- The `g`-weight submodule of a comodule over `R[G]`: the vectors whose coaction is
`v ↦ v ⊗ single g 1`. -/
def weightSpace (g : G) : Submodule R V where
  carrier := {v | coact (R := R) (C := MonoidAlgebra R G) v =
    v ⊗ₜ[R] MonoidAlgebra.single g (1 : R)}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb, TensorProduct.add_tmul]
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_smul, ha, TensorProduct.smul_tmul']

variable {R G V}

@[simp]
theorem mem_weightSpace {g : G} {v : V} :
    v ∈ weightSpace R G V g ↔
      coact (R := R) (C := MonoidAlgebra R G) v = v ⊗ₜ[R] MonoidAlgebra.single g (1 : R) :=
  Iff.rfl

/-- On its own weight submodule the weight projection is the identity. -/
theorem weightProj_of_mem {g : G} {v : V} (hv : v ∈ weightSpace R G V g) :
    weightProj R G V g v = v := by
  simp [weightProj_apply, mem_weightSpace.mp hv]

/-- A weight projection kills the weight submodules at all other indices. -/
theorem weightProj_of_mem_of_ne {h g : G} (hne : h ≠ g) {v : V} (hv : v ∈ weightSpace R G V g) :
    weightProj R G V h v = 0 := by
  classical
  simp [weightProj_apply, mem_weightSpace.mp hv, Ne.symm hne]

/-- **Each weight component lies in its weight submodule.** -/
theorem weightProj_mem_weightSpace (g : G) (v : V) :
    weightProj R G V g v ∈ weightSpace R G V g := by
  classical
  have hsingle : weightDecomposition R G V (weightProj R G V g v) =
      Finsupp.single g (weightProj R G V g v) := by
    refine Finsupp.ext fun h => ?_
    rw [weightDecomposition_apply]
    by_cases hh : g = h
    · subst hh
      simp
    · simp [hh, weightProj_weightProj_of_ne (Ne.symm hh)]
  rw [mem_weightSpace, coact_eq_symm_weightDecomposition, hsingle,
    tensorCoeffEquiv_symm_single]

/-- The coaction on a weight component is diagonal. This is `weightProj_mem_weightSpace` in the
`simp` normal form of membership in `weightSpace`, and is what discharges such membership goals. -/
@[simp]
theorem coact_weightProj (g : G) (v : V) :
    coact (R := R) (C := MonoidAlgebra R G) (weightProj R G V g v) =
      weightProj R G V g v ⊗ₜ[R] MonoidAlgebra.single g (1 : R) :=
  weightProj_mem_weightSpace g v

variable (R G V)

/-- The weight submodules span the whole comodule. -/
theorem iSup_weightSpace_eq_top : ⨆ g : G, weightSpace R G V g = ⊤ := by
  classical
  refine top_unique fun v _ => ?_
  rw [← weightDecomposition_sum (R := R) (G := G) (V := V) v, Finsupp.sum]
  refine Submodule.sum_mem _ fun g _ => Submodule.mem_iSup_of_mem g ?_
  rw [weightDecomposition_apply]
  exact weightProj_mem_weightSpace g v

/-- The weight submodules are independent. -/
theorem iSupIndep_weightSpace : iSupIndep (weightSpace R G V) := by
  intro g
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hker : (⨆ h, ⨆ _ : h ≠ g, weightSpace R G V h) ≤
      LinearMap.ker (weightProj R G V g) :=
    iSup_le fun h => iSup_le fun hne => fun w hw => weightProj_of_mem_of_ne (Ne.symm hne) hw
  have h0 : weightProj R G V g v = 0 := hker hv'
  rwa [weightProj_of_mem hv] at h0

section Internal

attribute [local instance] Classical.decEq

variable {R G V}

/-- The weight projections read off the components of an element of the direct sum of the weight
submodules. -/
private theorem weightProj_coeAddMonoidHom (g : G)
    (x : ⨁ h : G, weightSpace R G V h) :
    weightProj R G V g (DirectSum.coeAddMonoidHom (weightSpace R G V) x) = (x g : V) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of h w =>
    rw [DirectSum.coeAddMonoidHom_of, DirectSum.coe_of_apply]
    by_cases hh : h = g
    · subst hh
      simp [weightProj_of_mem w.2]
    · simp [hh, weightProj_of_mem_of_ne (Ne.symm hh) w.2]
  | add x y hx hy => simp [hx, hy]

variable (R G V)

/-- **A comodule over a monoid algebra is the internal direct sum of its weight submodules.**
When `G` is a commutative group, this is the weight-space decomposition of a representation of
the diagonalizable group `D(G) = Spec R[G]`.

The independence and spanning statements above are packaged here by hand rather than through
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`, which needs a ring: over a semiring
the lattice-theoretic independence is too weak, whereas the weight projections give the
decomposition directly. -/
theorem isInternal_weightSpace : DirectSum.IsInternal (weightSpace R G V) := by
  classical
  refine ⟨fun x y hxy => DFinsupp.ext fun g => Subtype.ext ?_, fun v => ?_⟩
  · rw [← weightProj_coeAddMonoidHom (R := R) (G := G) (V := V) g x,
      ← weightProj_coeAddMonoidHom (R := R) (G := G) (V := V) g y, hxy]
  · refine ⟨∑ g ∈ (weightDecomposition R G V v).support,
      DirectSum.of (fun h : G => weightSpace R G V h) g
        ⟨weightProj R G V g v, weightProj_mem_weightSpace g v⟩, ?_⟩
    rw [map_sum]
    simpa [Finsupp.sum] using weightDecomposition_sum (R := R) (G := G) (V := V) v

end Internal

/-- The `g`-weight submodule as a subcomodule: the decomposition is one of comodules, not merely
of modules. -/
def weightSubcomodule (g : G) : Subcomodule R (MonoidAlgebra R G) V where
  carrier := weightSpace R G V g
  coact_mem' v hv := by
    refine ⟨(⟨v, hv⟩ : weightSpace R G V g) ⊗ₜ[R] MonoidAlgebra.single g (1 : R), ?_⟩
    rw [TensorProduct.map_tmul]
    exact (mem_weightSpace.mp hv).symm

variable {R G V}

@[simp]
theorem weightSubcomodule_toSubmodule (g : G) :
    (weightSubcomodule R G V g).toSubmodule = weightSpace R G V g :=
  (rfl)

@[simp]
theorem mem_weightSubcomodule {g : G} {v : V} :
    v ∈ weightSubcomodule R G V g ↔ v ∈ weightSpace R G V g :=
  (Iff.rfl)

/-! ### Functoriality and finiteness -/

variable {W : Type*} [AddCommMonoid W] [Module R W] [Comodule R (MonoidAlgebra R G) W]

namespace Hom

/-- A morphism of comodules over `R[G]` sends the `g`-weight submodule into the `g`-weight
submodule. -/
theorem map_mem_weightSpace (f : Hom R (MonoidAlgebra R G) V W) {g : G} {v : V}
    (hv : v ∈ weightSpace R G V g) : f v ∈ weightSpace R G W g := by
  rw [mem_weightSpace] at hv ⊢
  rw [← Hom.map_coact_apply f v, hv, TensorProduct.map_tmul]
  rfl

/-- A morphism of comodules over `R[G]` maps the `g`-weight submodule into the `g`-weight
submodule. -/
theorem map_weightSpace_le (f : Hom R (MonoidAlgebra R G) V W) (g : G) :
    (weightSpace R G V g).map f.toLinearMap ≤ weightSpace R G W g := by
  rintro _ ⟨v, hv, rfl⟩
  exact f.map_mem_weightSpace hv

end Hom

variable (R G V)

/-- The `g`-weight submodule is the range of the `g`-weight projection: the projection is
idempotent with image the submodule it projects onto. -/
@[simp]
theorem range_weightProj (g : G) :
    LinearMap.range (weightProj R G V g) = weightSpace R G V g := by
  refine le_antisymm ?_ fun v hv => ⟨v, weightProj_of_mem hv⟩
  rintro _ ⟨v, rfl⟩
  exact weightProj_mem_weightSpace g v

/-- **A comodule over `R[G]` that is finitely generated as a module has only finitely many
weights.**

For a representation of the diagonalizable group `D(G)` this is the finiteness of its set of
weights, and for the adjoint representation of an affine group scheme under a split torus it is
the finiteness of the set of roots. -/
theorem finite_setOf_weightSpace_ne_bot [Module.Finite R V] :
    {g : G | weightSpace R G V g ≠ ⊥}.Finite := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := V)
  refine Set.Finite.subset
    (S.biUnion fun v => (weightDecomposition R G V v).support).finite_toSet fun g hg => ?_
  by_contra hgS
  refine hg (le_antisymm ?_ bot_le)
  have hgS' : g ∉ S.biUnion fun v => (weightDecomposition R G V v).support := by
    simpa using hgS
  rw [Finset.mem_biUnion] at hgS'
  push Not at hgS'
  rw [← range_weightProj R G V g, LinearMap.range_eq_map, ← hS, Submodule.map_span,
    Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  have : weightDecomposition R G V v g = 0 :=
    Finsupp.notMem_support_iff.mp (hgS' v (Finset.mem_coe.mp hv))
  rw [weightDecomposition_apply] at this
  simp [this]

end WeightSpace

/-! ## The action associated to an algebra map out of the monoid algebra -/

section Points

variable [Monoid G] [Comodule R (MonoidAlgebra R G) V]
variable {A : Type*} [CommSemiring A] [Algebra R A]

variable {R G V}

/-- **The endomorphism associated to an algebra map out of `R[G]` acts by a scalar on each
weight submodule.** When `G` is a commutative group, these algebra maps are points of `D(G)`, and
the scalar `f (single g 1)` is the value of the character `g` at the point `f`. -/
theorem endOfPoint_tmul_of_mem_weightSpace (f : MonoidAlgebra R G →ₐ[R] A) (a : A) {g : G} {v : V}
    (hv : v ∈ weightSpace R G V g) :
    endOfPoint V f (a ⊗ₜ[R] v) = (a * f (MonoidAlgebra.single g (1 : R))) ⊗ₜ[R] v := by
  rw [endOfPoint_tmul, mem_weightSpace.mp hv]
  simp [TensorProduct.smul_tmul']

end Points

end Comodule

end TauCeti
