/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.PointsFunctor
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry
public import TauCeti.CategoryTheory.Aut.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.SpinWeight
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.GraphAutomorphism

/-!
# The graph automorphism of the full-weight type-D spin carrier

For `4 ≤ n`, `TauCeti.TypeDSpinCarrier.groupScheme` is the explicit full-weight Chevalley carrier
of type `Dₙ`, cut out inside `GL_(2^n)` over `ℤ` by the split spin representation and its exterior
coordinate lattice. The Dynkin diagram `Dₙ` carries the involution exchanging its two fork nodes,
`TauCeti.graphPermD`, and this file equips the carrier with the automorphism realizing it.

The datum the construction consumes is a lattice-preserving linear automorphism of the spin module
which intertwines the numbered Serre generators along that node exchange, acts monomially on the
chosen coordinate basis, and permutes the weights compatibly.
`TauCeti/RepresentationTheory/Spin/Polarization/TypeD/GraphAutomorphism.lean` already supplies the
first two: the graph operator, creation at the final coordinate minus annihilation at it, is the
spin action of a Clifford generator of a vector of norm `-1`, it preserves the coordinate lattice
in both directions, and it intertwines the numbered generators. What this file adds is the
remaining coordinate bookkeeping, and then the descent.

On the exterior basis vector indexed by a sign set `s` the graph operator acts by a single
coordinate move: it creates the final coordinate when `s` misses it and annihilates it when `s`
carries it, in both cases up to the shuffle sign that moves that coordinate to the front. So the
basis is permuted by the final-sign toggle `TauCeti.DynkinType.typeDSpinGraphPerm` and rescaled by
a sign, which is `TauCeti.TypeDSpinCarrier.graphBasisScale`. That toggle exchanges the two fork
coordinates of every spin weight, which is the weight compatibility. Both hypotheses in hand, the
numbered-symmetry construction of a Kostant toral closure descends the operator to
`TauCeti.TypeDSpinCarrier.graphAut`, an automorphism `γ` of the carrier with

```text
γ (x_i(u)) = x_{σ i}(u),
```

on every Bourbaki-numbered raising and lowering root subgroup, `σ` the fork exchange, and with
`γ ^ 2 = 1`.

The graph operator itself squares to `-1`, so the signed permutation matrix
`TauCeti.TypeDSpinCarrier.graphAutMatrix` squares to the scalar `-1`: the two signs at a
graph-exchanged pair of coordinates multiply to `-1`, which is
`TauCeti.TypeDSpinCarrier.graphBasisScale_graphBasisPerm_mul`. The automorphism of the carrier is
conjugation by that matrix, and `-1` is central, so conjugating twice is the identity whatever the
value ring.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the spin group scheme or the pinned simply connected Chevalley--Demazure group scheme of type
`Dₙ`, or that any group mentioned is finite, perfect, or simple.

## Main definitions

* `TauCeti.TypeDSpinCarrier.graphRootPerm`: the fork exchange on the numbered root generators.
* `TauCeti.TypeDSpinCarrier.graphBasisPerm` and `TauCeti.TypeDSpinCarrier.graphBasisScale`: the
  permutation and the signs by which the graph operator acts on the spin coordinate basis.
* `TauCeti.TypeDSpinCarrier.graphAut`: the graph automorphism of the type-`Dₙ` spin carrier.
* `TauCeti.TypeDSpinCarrier.graphAutMatrix` and `TauCeti.TypeDSpinCarrier.graphAutPoints`: the
  signed permutation matrix of the coordinate involution, and conjugation by it on the
  matrix-valued points of the carrier.

## Main results

* `TauCeti.TypeDSpinCarrier.graphOperator_latticeBasis`: the graph operator acts monomially on the
  spin coordinate basis.
* `TauCeti.TypeDSpinCarrier.basisWeight_graphBasisPerm`: the coordinate involution is equivariant
  for the fork exchange of the Bourbaki nodes on the spin weights.
* `TauCeti.TypeDSpinCarrier.rootSubgroup_comp_graphAut_hom` and
  `TauCeti.TypeDSpinCarrier.graphAutPoints_rootSubgroupPoints`: the pinning equation
  `γ (x_i(u)) = x_{σ i}(u)`, on the carrier and on its matrix-valued points.
* `TauCeti.TypeDSpinCarrier.weightTorus_comp_graphAut_hom` and
  `TauCeti.TypeDSpinCarrier.graphAutPoints_weightTorusPoints`: the graph automorphism relabels the
  coordinates of the represented spin weight torus by the fork exchange.
* `TauCeti.TypeDSpinCarrier.schemePointsMulEquiv_graphAut_comp_carrierι`: on every algebra-valued
  point of the carrier, the automorphism of the carrier is the conjugation that the automorphism on
  points performs, so the two are the same action.
* `TauCeti.TypeDSpinCarrier.graphAut_sq` and
  `TauCeti.TypeDSpinCarrier.graphAutPoints_apply_apply`: the order relation `γ ^ 2 = 1`, on the
  carrier and on points.
* `TauCeti.TypeDSpinCarrier.graphAutMatrix_mul_self`: the matrix implementing it squares to `-1`.
* `TauCeti.TypeDSpinCarrier.pointsMap_comp_graphAutPoints`: the automorphism on points is natural
  in the value ring, so in particular it commutes with the Frobenius of
  `TauCeti/Algebra/Lie/Orthogonal/TypeD/SpinCarrier/Frobenius.lean`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spinor model and the
  action of the Clifford generators on it.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for the graph automorphism of `Dₙ` and the
  twisted family it defines.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15, for
  the graph-twisted Steinberg endomorphisms.
* J. E. Humphreys, *Linear Algebraic Groups*, §27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV, for the numbering of the
  `Dₙ` diagram whose last two nodes the symmetry exchanges.

What this feeds is the graph-twisted family `²Dₙ(q)`, whose Steinberg endomorphism is `γ ∘ Frob_q`
for the `γ` built here and the `q`-power Frobenius of
`TauCeti/Algebra/Lie/Orthogonal/TypeD/SpinCarrier/Frobenius.lean`, on the very carrier
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean` attaches to the three families on a type-`D`
diagram. The type-`A` counterpart of this construction is
`TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/GraphAutomorphism.lean`, and the counterpart on
the Geck carrier is
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/GeckLattice/GraphAutomorphism.lean`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

universe v v'

noncomputable section

variable (n : ℕ)

/-! ## The fork exchange on the numbered generators and on the coordinate basis -/

/-- The fork exchange on the numbered type-`Dₙ` root generators: the permutation
`TauCeti.graphPermD` of the Bourbaki nodes, acting the same way on the raising and on the lowering
half of the numbering. -/
def graphRootPerm (hn : 2 ≤ n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  Equiv.sumCongr (graphPermD n (by omega)) (graphPermD n (by omega))

-- Deliberately not `@[simp]`: unfolding `graphRootPerm` to `Sum.map` erases it as a head symbol,
-- which takes `graphRootPerm_apply_apply` and `rootSubgroup_comp_graphAut_inv` below out of simp
-- normal form.
/-- The fork exchange acts on the numbered root generators by the same node permutation on each
half of the numbering. -/
theorem graphRootPerm_apply (hn : 2 ≤ n) (k : Fin n ⊕ Fin n) :
    graphRootPerm n hn k =
      Sum.map (graphPermD n (by omega)) (graphPermD n (by omega)) k := by
  rw [graphRootPerm]
  exact Equiv.sumCongr_apply _ _ k

/-- **The fork exchange on the numbered root generators is an involution**, matching the
involutivity of the fork exchange on the diagram. -/
@[simp]
theorem graphRootPerm_apply_apply (hn : 2 ≤ n) (k : Fin n ⊕ Fin n) :
    graphRootPerm n hn (graphRootPerm n hn k) = k := by
  rw [graphRootPerm_apply, graphRootPerm_apply]
  cases k with
  | inl j => rw [Sum.map_inl, Sum.map_inl, graphPermD_apply_apply]
  | inr j => rw [Sum.map_inr, Sum.map_inr, graphPermD_apply_apply]

/-- The involution of the spin coordinate basis realizing the fork exchange: it toggles the final
sign of the sign set indexing a basis vector. -/
def graphBasisPerm (hn : 1 ≤ n) : Equiv.Perm (Fin (dimension n)) :=
  (Fintype.equivFin (Finset (Fin n))).permCongr (DynkinType.typeDSpinGraphPerm n (by omega))

/-- The sign set of a graph-permuted basis index is the toggle of the original sign set. -/
@[simp]
theorem signSet_graphBasisPerm (hn : 1 ≤ n) (i : Fin (dimension n)) :
    signSet n (graphBasisPerm n hn i) =
      DynkinType.typeDSpinGraphPerm n (by omega) (signSet n i) := by
  rw [graphBasisPerm, signSet, signSet, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- **The graph operator of the split type-`Dₙ` spin module**: creation at the final coordinate
minus annihilation at it, the spin action of the Clifford generator of
`TauCeti.SpinPolarizationData.typeDGraphVector`. -/
abbrev graphOperator (hn : 2 ≤ n) :
    ExteriorAlgebra ℚ (polarization n).W ≃ₗ[ℚ] ExteriorAlgebra ℚ (polarization n).W :=
  (polarization n).typeDGraphOperator (polarizationBasis n) (by omega)

/-- **The scaling coefficient by which the graph operator acts on a spin coordinate basis
vector.** It is a sign: the shuffle sign that moves the final coordinate to the front, negated on
the basis vectors whose sign set already carries that coordinate, where the annihilating half of
the graph operator acts. -/
def graphBasisScale (hn : 1 ≤ n) (i : Fin (dimension n)) : ℤ :=
  if (⟨n - 1, by omega⟩ : Fin n) ∈ signSet n i then
    -(TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n) (signSet n i) : ℤ)
  else
    (TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n)
      (insert (⟨n - 1, by omega⟩ : Fin n) (signSet n i)) : ℤ)

/-- **The graph operator acts monomially on the spin coordinate basis**: it carries the basis
vector at `i` to a sign times the one at `TauCeti.TypeDSpinCarrier.graphBasisPerm i`. This is the
hypothesis under which a numbered symmetry descends to the Kostant toral closure. -/
theorem graphOperator_latticeBasis (hn : 2 ≤ n) (i : Fin (dimension n)) :
    graphOperator n hn ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) =
      ((graphBasisScale n (by omega) i • latticeBasis n (graphBasisPerm n (by omega) i) :
        (lattice n).toAddSubgroup) : ExteriorAlgebra ℚ (polarization n).W) := by
  rw [coe_latticeBasis, AddSubgroup.coe_zsmul, coe_latticeBasis, graphBasisScale,
    signSet_graphBasisPerm]
  by_cases hs : (⟨n - 1, by omega⟩ : Fin n) ∈ signSet n i
  · rw [ite_eq_left hs, DynkinType.typeDSpinGraphPerm_of_mem n (by omega) hs]
    exact (polarization n).typeDGraphOperator_basis_of_mem (polarizationBasis n) (by omega) hs
  · rw [ite_eq_right hs, DynkinType.typeDSpinGraphPerm_of_notMem n (by omega) hs]
    exact (polarization n).typeDGraphOperator_basis_of_notMem (polarizationBasis n) (by omega) hs

/-- **The final-sign toggle is an involution of the coordinate basis**, matching the involutivity
of the fork exchange on the diagram. -/
@[simp]
theorem graphBasisPerm_apply_apply (hn : 1 ≤ n) (i : Fin (dimension n)) :
    graphBasisPerm n hn (graphBasisPerm n hn i) = i := by
  apply (Fintype.equivFin (Finset (Fin n))).symm.injective
  rw [← signSet, ← signSet, signSet_graphBasisPerm, signSet_graphBasisPerm,
    DynkinType.typeDSpinGraphPerm_apply_apply]

/-- **The two signs at a graph-exchanged pair of basis vectors multiply to `-1`**, which is the
coordinate reading of the graph operator squaring to `-1`. -/
@[simp]
theorem graphBasisScale_graphBasisPerm_mul (hn : 1 ≤ n) (i : Fin (dimension n)) :
    graphBasisScale n hn (graphBasisPerm n hn i) * graphBasisScale n hn i = -1 := by
  have hunit : ∀ u : ℤˣ, (u : ℤ) * (u : ℤ) = 1 := fun u => by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [graphBasisScale, graphBasisScale, signSet_graphBasisPerm]
  by_cases hs : (⟨n - 1, by omega⟩ : Fin n) ∈ signSet n i
  · rw [ite_eq_left hs, DynkinType.typeDSpinGraphPerm_of_mem n (by omega) hs,
      ite_eq_right (Finset.notMem_erase _ _), Finset.insert_erase hs]
    rw [mul_neg, hunit]
  · rw [ite_eq_right hs, DynkinType.typeDSpinGraphPerm_of_notMem n (by omega) hs,
      ite_eq_left (Finset.mem_insert_self _ _)]
    rw [neg_mul, hunit]

/-! ## The weight compatibility -/

/-- **The final-sign toggle of the spin weights is equivariant for the fork exchange of the
Bourbaki nodes.** This is the compatibility between the coordinate involution and the diagram
symmetry that lets the graph operator descend to the carrier. -/
theorem basisWeight_graphBasisPerm (hn : 2 ≤ n) (i : Fin (dimension n)) (k : Fin n) :
    basisWeight n (graphBasisPerm n (by omega) i) (graphPermD n (by omega) k) =
      basisWeight n i k := by
  rw [basisWeight, signSet_graphBasisPerm,
    DynkinType.typeDSpinWeight_typeDSpinGraphPerm_apply (by omega)]
  exact congrArg (DynkinType.typeDSpinWeight (signSet n i)) (graphPermD_apply_apply n (by omega) k)

/-! ## The graph automorphism of the carrier -/

variable (hn : 4 ≤ n)

/-- The graph operator intertwines the represented numbered root generators along the fork
exchange, stated through `UniversalEnvelopingAlgebra.ι` as the numbered Kostant symmetry
construction takes that hypothesis. -/
private theorem graphOperator_rep_rootGenerator :
    ∀ (k : Fin n ⊕ Fin n) (x : ExteriorAlgebra ℚ (polarization n).W),
      graphOperator n (by omega)
          (rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (TauCeti.serreRootGenerator (CartanMatrix.D n) k)) x) =
        rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (TauCeti.serreRootGenerator (CartanMatrix.D n) (graphRootPerm n (by omega) k)))
          (graphOperator n (by omega) x) := by
  intro k x
  rw [graphRootPerm_apply]
  exact (polarization n).typeDGraphOperator_typeDSpinRep_rootGenerator
    (polarizationBasis n) hn k x

/-- The graph operator preserves the spin coordinate lattice in both directions, phrased as
membership of the underlying additive subgroup, which is the shape the numbered-symmetry
construction takes its lattice hypothesis in. The content is
`TauCeti.SpinPolarizationData.typeDGraphOperator_mem_integralLattice_iff`. -/
private theorem graphOperator_mem_lattice_iff :
    ∀ x : ExteriorAlgebra ℚ (polarization n).W,
      graphOperator n (by omega) x ∈ (lattice n).toAddSubgroup ↔ x ∈ (lattice n).toAddSubgroup :=
  fun x => (polarization n).typeDGraphOperator_mem_integralLattice_iff
    (polarizationBasis n) (by omega)

/-- The numbered symmetry of the Kostant toral closure attached to the fork exchange. -/
private def toralGraphAut :
    Aut (kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)) :=
  kostantToralNumberedSymmetryIso
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)
    ⇑(graphRootPerm n (by omega)) (graphOperator n (by omega))
    (graphOperator_mem_lattice_iff n hn)
    (graphOperator_rep_rootGenerator n hn)
    (graphRootPerm n (by omega)).surjective
    (graphBasisPerm n (by omega)) (graphBasisScale n (by omega))
    (graphOperator_latticeBasis n (by omega))
    (graphPermD n (by omega)) (basisWeight_graphBasisPerm n (by omega))

/-- **The graph automorphism of the type-`Dₙ` spin carrier**: the automorphism realizing the fork
exchange of the two final Bourbaki nodes. It renumbers the pinned root subgroups by that exchange
without changing their parameters, and relabels the coordinates of the represented spin weight
torus.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, or that the
carrier is the pinned simply connected Chevalley--Demazure group scheme of type `Dₙ`. -/
def graphAut : Aut (groupScheme n hn) :=
  Aut.autMulEquivOfIso (eqToIso (groupScheme_eq_kostantToralGroupScheme n hn).symm)
    (toralGraphAut n hn)

private theorem graphAut_hom :
    (graphAut n hn).hom =
      eqToHom (groupScheme_eq_kostantToralGroupScheme n hn) ≫ (toralGraphAut n hn).hom ≫
        eqToHom (groupScheme_eq_kostantToralGroupScheme n hn).symm := by
  rw [graphAut, TauCeti.CategoryTheory.autMulEquivOfIso_hom, eqToIso.inv, eqToIso.hom]

/-- **The graph automorphism renumbers every pinned raising and lowering root subgroup by the fork
exchange, without changing its additive parameter.** This is the equation `γ (x_α(t)) = x_{γ α}(t)`
that pins a graph automorphism, on the type-`Dₙ` spin carrier. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_graphAut_hom (k : Fin n ⊕ Fin n) :
    rootSubgroup n hn k ≫ (graphAut n hn).hom =
      rootSubgroup n hn (graphRootPerm n (by omega) k) := by
  rw [graphAut_hom, rootSubgroup_def, rootSubgroup_def, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, toralGraphAut, ← Category.assoc,
    kostantRootSubgroupToToral_comp_numberedSymmetryIso_hom]

/-- The inverse graph automorphism restores the original numbering of a pinned root subgroup. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_graphAut_inv (k : Fin n ⊕ Fin n) :
    rootSubgroup n hn (graphRootPerm n (by omega) k) ≫ (graphAut n hn).inv =
      rootSubgroup n hn k := by
  rw [← rootSubgroup_comp_graphAut_hom n hn k, Category.assoc,
    (graphAut n hn).hom_inv_id, Category.comp_id]

/-- **The graph automorphism relabels the coordinates of the represented spin weight torus** by
the fork exchange. Nothing here asserts that this morphism is an immersion, so this is an equation
of morphisms and not a statement that `γ` normalizes a subgroup scheme. -/
@[reassoc (attr := simp)]
theorem weightTorus_comp_graphAut_hom :
    weightTorus n hn ≫ (graphAut n hn).hom =
      SplitTorus.relabel ℤ (graphPermD n (by omega)) ≫ weightTorus n hn := by
  rw [graphAut_hom, weightTorus_def, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, toralGraphAut, ← Category.assoc,
    kostantWeightTorusToToral_comp_numberedSymmetryIso_hom, Category.assoc]
  congr 2
  rw [inv_eq_iff_mul_eq_one, ← pow_two, graphPermD_sq]

/-- **The graph automorphism of the type-`Dₙ` spin carrier is an involution**, matching the order
of the fork exchange of the diagram. -/
@[simp]
theorem graphAut_sq : graphAut n hn ^ 2 = 1 := by
  have hrootIter : (⇑(graphRootPerm n (by omega)))^[2] = id := by
    funext k
    rw [Function.iterate_succ_apply, Function.iterate_one, graphRootPerm_apply_apply, id_eq]
  have htoral : toralGraphAut n hn ^ 2 = 1 :=
    kostantToralNumberedSymmetryIso_pow_eq_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2
      hrootIter (graphPermD_sq n (by omega))
  rw [graphAut, ← map_pow, htoral, map_one]

/-! ## The graph automorphism on matrix-valued points -/

/-- **The matrix of the spin coordinate involution** over a value ring: the signed permutation
matrix of `TauCeti.TypeDSpinCarrier.graphBasisPerm`, with the signs of
`TauCeti.TypeDSpinCarrier.graphBasisScale`. Conjugation by it is the action on matrix-valued
points of the graph automorphism of the carrier. -/
def graphAutMatrix (A : Type v) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin (dimension n)) A :=
  kostantNumberedSymmetryMatrix (lattice n).toAddSubgroup (latticeBasis n)
    (graphOperator n (by omega)) (graphOperator_mem_lattice_iff n hn) A

/-- The entries of the graph matrix: the `j`-th column carries the sign at `j` in the row
`graphBasisPerm j` and vanishes elsewhere. -/
theorem coe_graphAutMatrix_apply (A : Type v) [CommRing A] (i j : Fin (dimension n)) :
    (graphAutMatrix n hn A : Matrix (Fin (dimension n)) (Fin (dimension n)) A) i j =
      if i = graphBasisPerm n (by omega) j then
        algebraMap ℤ A (graphBasisScale n (by omega) j)
      else 0 := by
  rw [graphAutMatrix]
  exact coe_kostantNumberedSymmetryMatrix_apply_of_monomial (lattice n).toAddSubgroup
    (latticeBasis n) (graphOperator n (by omega)) (graphOperator_mem_lattice_iff n hn)
    (graphBasisPerm n (by omega)) (graphBasisScale n (by omega))
    (graphOperator_latticeBasis n (by omega)) A i j

/-- **The graph matrix squares to the scalar `-1`.** Its two signs at a graph-exchanged pair of
coordinates multiply to `-1`, and `-1` is central, so conjugation by it is nonetheless an
involution. -/
@[simp]
theorem graphAutMatrix_mul_self (A : Type v) [CommRing A] :
    graphAutMatrix n hn A * graphAutMatrix n hn A = -1 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_neg, Units.val_one]
  ext i j
  rw [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply,
    Finset.sum_eq_single (graphBasisPerm n (by omega) j)]
  · rw [coe_graphAutMatrix_apply, coe_graphAutMatrix_apply, graphBasisPerm_apply_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [ite_eq_left (rfl : graphBasisPerm n (by omega) i = graphBasisPerm n (by omega) i),
        ite_eq_left (rfl : i = i), ← map_mul, graphBasisScale_graphBasisPerm_mul,
        map_neg, map_one, ite_eq_left (rfl : i = i)]
    · rw [ite_eq_right hij, ite_eq_right hij, zero_mul, neg_zero]
  · intro k _ hk
    rw [coe_graphAutMatrix_apply, coe_graphAutMatrix_apply, ite_eq_right hk, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The graph matrix commutes with extension of the value ring. -/
@[simp]
theorem map_graphAutMatrix {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f (graphAutMatrix n hn A) = graphAutMatrix n hn B :=
  map_kostantNumberedSymmetryMatrix _ _ _ _ f

/-- The matrix-valued points of the carrier are the points of the Kostant toral closure of the
type-`Dₙ` spin data. -/
private theorem points_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    points n hn A =
      kostantToralPointsSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A := by
  rw [points_def, kostantToralPointsSubgroup_def, definingIdeal_def]

/-- **The graph matrix normalizes the matrix-valued points of the carrier.** -/
theorem map_points_conj_graphAutMatrix (A : Type v) [CommRing A] :
    (points n hn A).map
        ((MulAut.conj (graphAutMatrix n hn A) :
          Matrix.GeneralLinearGroup (Fin (dimension n)) A ≃*
            Matrix.GeneralLinearGroup (Fin (dimension n)) A) : _ →* _) =
      points n hn A := by
  rw [points_eq_kostantToralPointsSubgroup, graphAutMatrix]
  exact map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)
    ⇑(graphRootPerm n (by omega)) (graphOperator n (by omega))
    (graphOperator_mem_lattice_iff n hn)
    (graphOperator_rep_rootGenerator n hn)
    (graphRootPerm n (by omega)).surjective
    (graphBasisPerm n (by omega)) (graphBasisScale n (by omega))
    (graphOperator_latticeBasis n (by omega))
    (graphPermD n (by omega)) (basisWeight_graphBasisPerm n (by omega)) A

/-- The graph matrix, as an element of the normalizer of the carrier points. -/
private def graphAutNormalizer (A : Type v) [CommRing A] :
    Subgroup.normalizer
      (points n hn A : Set (Matrix.GeneralLinearGroup (Fin (dimension n)) A)) :=
  ⟨graphAutMatrix n hn A, Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_points_conj_graphAutMatrix n hn A)⟩

/-- **The graph automorphism on the matrix-valued points of the type-`Dₙ` spin carrier**:
conjugation by the graph matrix. It renumbers the pinned root subgroups by the fork exchange
without changing their parameters, and relabels the coordinates of a spin weight-torus point. -/
def graphAutPoints (A : Type v) [CommRing A] : MulAut (points n hn A) :=
  (points n hn A).normalizerMonoidHom (graphAutNormalizer n hn A)

/-- The graph automorphism on points is conjugation by the graph matrix. -/
@[simp]
theorem coe_graphAutPoints (A : Type v) [CommRing A] (g : points n hn A) :
    (graphAutPoints n hn A g : Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      graphAutMatrix n hn A * g * (graphAutMatrix n hn A)⁻¹ :=
  (rfl)

/-- The inverse graph automorphism on points is conjugation by the inverse graph matrix. -/
@[simp]
theorem coe_graphAutPoints_symm (A : Type v) [CommRing A] (g : points n hn A) :
    ((graphAutPoints n hn A).symm g : Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      (graphAutMatrix n hn A)⁻¹ * g * graphAutMatrix n hn A :=
  (rfl)

/-- **The graph automorphism on points is the map the graph automorphism of the carrier induces.**
On every algebra-valued point of the carrier, composing with
`TauCeti.TypeDSpinCarrier.graphAut` and including into `GL_(2^n)` conjugates the point's matrix by
`TauCeti.TypeDSpinCarrier.graphAutMatrix`, which is what `TauCeti.TypeDSpinCarrier.graphAutPoints`
does by `TauCeti.TypeDSpinCarrier.coe_graphAutPoints`. So the automorphism of the carrier and the
one on its matrix-valued points are the same action. -/
theorem schemePointsMulEquiv_graphAut_comp_carrierι (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ (groupScheme n hn).X) :
    GeneralLinear.schemePointsMulEquiv (dimension n) A
        (p ≫ ((graphAut n hn).hom ≫ carrierι n hn).hom.hom) =
      graphAutMatrix n hn A *
          GeneralLinear.schemePointsMulEquiv (dimension n) A (p ≫ (carrierι n hn).hom.hom) *
        (graphAutMatrix n hn A)⁻¹ := by
  have hcomp : (graphAut n hn).hom ≫ carrierι n hn =
      eqToHom (groupScheme_eq_kostantToralGroupScheme n hn) ≫ (toralGraphAut n hn).hom ≫
        kostantToralGroupSchemeι
          (TauCeti.serreRootGenerator (CartanMatrix.D n))
          (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
          (rep_kostantForm_mem_lattice n hn)
          (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
    rw [graphAut_hom, carrierι_def]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hcomp, carrierι_def, graphAutMatrix]
  simpa only [toralGraphAut, Grp.comp_hom_hom, Category.assoc] using
    schemePointsMulEquiv_kostantToralNumberedSymmetryIso
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)
      ⇑(graphRootPerm n (by omega)) (graphOperator n (by omega))
      (graphOperator_mem_lattice_iff n hn)
      (graphOperator_rep_rootGenerator n hn)
      (graphRootPerm n (by omega)).surjective
      (graphBasisPerm n (by omega)) (graphBasisScale n (by omega))
      (graphOperator_latticeBasis n (by omega))
      (graphPermD n (by omega)) (basisWeight_graphBasisPerm n (by omega)) A
      (p ≫ (eqToHom (groupScheme_eq_kostantToralGroupScheme n hn)).hom.hom)

/-- **The graph automorphism renumbers the pinned root subgroups on matrix-valued points**,
without changing their additive parameter. This is the equation `γ (x_α(t)) = x_{γ α}(t)` that
pins a graph automorphism, read on the points of the carrier. -/
@[simp]
theorem graphAutPoints_rootSubgroupPoints (A : Type v) [CommRing A] (k : Fin n ⊕ Fin n)
    (u : Multiplicative A) :
    graphAutPoints n hn A (rootSubgroupPoints n hn k A u) =
      rootSubgroupPoints n hn (graphRootPerm n (by omega) k) A u := by
  refine Subtype.ext ?_
  rw [coe_graphAutPoints, coe_rootSubgroupPoints, coe_rootSubgroupPoints, graphAutMatrix]
  exact kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) ⇑(graphRootPerm n (by omega)) (graphOperator n (by omega))
    (graphOperator_mem_lattice_iff n hn) (graphOperator_rep_rootGenerator n hn) A k _

/-- **The graph automorphism relabels the coordinates of a spin weight-torus point** by the fork
exchange of the Bourbaki nodes. The signs of the graph matrix cancel from the conjugation, so only
the coordinate permutation survives. -/
@[simp]
theorem graphAutPoints_weightTorusPoints (A : Type v) [CommRing A] (s : Fin n → Aˣ) :
    graphAutPoints n hn A (weightTorusPoints n hn A s) =
      weightTorusPoints n hn A (fun k => s (graphPermD n (by omega) k)) := by
  have hchar : ∀ i : Fin (dimension n),
      torusCharacter s (basisWeight n ((graphBasisPerm n (by omega))⁻¹ i)) =
        torusCharacter (fun k => s (graphPermD n (by omega) k)) (basisWeight n i) := by
    intro i
    have hperm : (graphBasisPerm n (by omega))⁻¹ i = graphBasisPerm n (by omega) i := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, graphBasisPerm_apply_apply]
    have hwt : basisWeight n (graphBasisPerm n (by omega) i) =
        basisWeight n i ∘ graphPermD n (by omega) := by
      funext k
      have := basisWeight_graphBasisPerm n (by omega) i (graphPermD n (by omega) k)
      rwa [graphPermD_apply_apply n (by omega)] at this
    rw [hperm, hwt, ← torusCharacter_mulEquivArrowCongr]
    exact congrArg (fun z => torusCharacter z (basisWeight n i))
      (funext fun k => by
        rw [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, graphPermD_symm])
  refine Subtype.ext ?_
  rw [coe_graphAutPoints, coe_weightTorusPoints, coe_weightTorusPoints, kostantTorusMatrix_apply,
    kostantTorusMatrix_apply, graphAutMatrix,
    kostantNumberedSymmetryMatrix_conj_diagGL (lattice n).toAddSubgroup (latticeBasis n)
      (graphOperator n (by omega)) (graphOperator_mem_lattice_iff n hn)
      (graphBasisPerm n (by omega)) (graphBasisScale n (by omega))
      (graphOperator_latticeBasis n (by omega)) A]
  exact congrArg diagGL (funext hchar)

/-- **The graph automorphism on points is an involution.** The graph matrix squares to the central
scalar `-1`, so conjugating twice is the identity even where that scalar is not `1`. -/
@[simp]
theorem graphAutPoints_apply_apply (A : Type v) [CommRing A] (g : points n hn A) :
    graphAutPoints n hn A (graphAutPoints n hn A g) = g := by
  refine Subtype.ext ?_
  rw [coe_graphAutPoints, coe_graphAutPoints]
  have hgroup : graphAutMatrix n hn A * (graphAutMatrix n hn A * (g : _) *
        (graphAutMatrix n hn A)⁻¹) * (graphAutMatrix n hn A)⁻¹ =
      (graphAutMatrix n hn A * graphAutMatrix n hn A) * (g : _) *
        (graphAutMatrix n hn A * graphAutMatrix n hn A)⁻¹ := by
    group
  rw [hgroup, graphAutMatrix_mul_self, inv_neg, inv_one, neg_one_mul, mul_neg, mul_one,
    neg_neg]

/-- **The graph automorphism on points is natural in the value ring.** In particular it commutes
with the Frobenius endomorphism of the points of the carrier. -/
theorem pointsMap_comp_graphAutPoints {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (pointsMap n hn f).comp (graphAutPoints n hn A).toMonoidHom =
      (graphAutPoints n hn B).toMonoidHom.comp (pointsMap n hn f) := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, coe_pointsMap, coe_graphAutPoints, coe_graphAutPoints,
    coe_pointsMap, map_mul, map_mul, map_inv, map_graphAutMatrix]

end

end TauCeti.TypeDSpinCarrier
