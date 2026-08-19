/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
public import TauCeti.Algebra.Lie.Basis.Reindex
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# The pinned split Lie algebra of a Dynkin type

`TauCeti.DynkinType.simplyConnectedRootDatum` pins one integral root datum per valid Dynkin type,
and `TauCeti.DynkinType.rationalRootSystem` reads it as a root system over `ℚ`. This file feeds
that root system to Geck's construction and names the resulting Lie algebra:
`TauCeti.DynkinType.lieAlgebra` is a Lie subalgebra of the square matrices indexed by one
coordinate per Bourbaki node and one per root, spanned by the explicit matrices Geck writes down
from the root data. No existence theorem is invoked: every element of the carrier traces back to
the pinned root tables.

The two hypotheses Geck's construction needs beyond a root system, reducedness and irreducibility,
are supplied by `TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/Rational.lean`, so what
remains here is the numbering. Geck indexes his generators by the support of a base, which is a
subtype of the root index type, whereas the conventions a consumer states — which node is long,
which pair of nodes a diagram automorphism exchanges — are stated against `Fin t.rank` in the
Bourbaki numbering. `TauCeti.DynkinType.lieBasis` is therefore Geck's basis renumbered along
`TauCeti.DynkinType.simpleSupportEquiv`, and its Cartan matrix is then literally
`TauCeti.DynkinType.cartanMatrix`, not a reindexed copy of it that would have to be compared with
the pinned one.

Nothing is claimed here about the Lie algebra beyond the relations carried by a
`LieAlgebra.Basis`. In particular it is not asserted to be semisimple: Mathlib derives that from
Geck's construction over an algebraically closed field, and `ℚ` is not one. The Cartan subalgebra
is a Cartan subalgebra, which is what the basis does give, and the one fact a Chevalley--Demazure
construction consumes next that the basis does not already carry is recorded: the generators `e`
and `f` are nilpotent as matrices. Their generation of the whole Lie algebra is exposed as
`TauCeti.DynkinType.lieSpan_lieBasis_e_union_f`.

## Main definitions

* `TauCeti.DynkinType.GeckIndex`: the index set of the matrices, one coordinate per Bourbaki node
  and one per root.
* `TauCeti.DynkinType.lieAlgebra`: the split Lie algebra of a valid Dynkin type.
* `TauCeti.DynkinType.cartanSubalgebra`: its distinguished Cartan subalgebra.
* `TauCeti.DynkinType.lieBasis`: its Chevalley generators, numbered by Bourbaki node.

## Main results

* `TauCeti.DynkinType.A_lieBasis`: the Cartan matrix of the basis is the pinned Cartan matrix of
  the Dynkin type.
* `TauCeti.DynkinType.coe_lieBasis_h`, `coe_lieBasis_e`, and `coe_lieBasis_f`: each generator is
  the explicit matrix Geck attaches to the corresponding simple root.
* `TauCeti.DynkinType.lie_lieBasis_h_e` and `TauCeti.DynkinType.lie_lieBasis_h_f`: the two
  relations that mention the Cartan matrix, read against the pinned numbering.
* `TauCeti.DynkinType.lieSpan_lieBasis_e_union_f`: the raising and lowering generators span the
  pinned Lie algebra.
* `TauCeti.DynkinType.isNilpotent_coe_lieBasis_e` and
  `TauCeti.DynkinType.isNilpotent_coe_lieBasis_f`: the raising and lowering generators are
  nilpotent matrices.
* `TauCeti.DynkinType.finrank_cartanSubalgebra`: the Cartan subalgebra has dimension `t.rank`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--IX, for the numbering.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2, for the Chevalley basis of a split semisimple
  Lie algebra.

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the split reductive group scheme
over `ℤ` to be constructed "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping
algebra", from the root data `DynkinType.simplyConnectedRootDatum` of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. This file supplies the Lie algebra and
the numbered Chevalley generators that the Kostant `ℤ`-form of `TauCeti/Algebra/Lie/`
`UniversalEnveloping/Kostant/` is formed from, whose consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.DynkinType

open RootPairing.GeckConstruction

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads
-- them; Mathlib's own Geck modules activate the same instance locally.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-- The index set of the matrices realizing the pinned Lie algebra: one coordinate for each
Bourbaki node and one for each root of the pinned root system. -/
abbrev GeckIndex : Type := (t.rationalBase ht).support ⊕ Fin t.numRoots

/-- **The split Lie algebra of a valid Dynkin type.** This is Geck's construction applied to the
pinned rational root system: the Lie subalgebra of `GeckIndex`-indexed matrices generated by the
explicit matrices `RootPairing.GeckConstruction.h`, `e` and `f` attached to the simple roots. -/
def lieAlgebra : LieSubalgebra ℚ (Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) :=
  RootPairing.GeckConstruction.lieAlgebra (t.rationalBase ht)

/-- The pinned Lie algebra is Geck's construction on the pinned rational base. -/
@[simp] theorem lieAlgebra_def :
    t.lieAlgebra ht = RootPairing.GeckConstruction.lieAlgebra (t.rationalBase ht) := (rfl)

/-- The distinguished Cartan subalgebra of `TauCeti.DynkinType.lieAlgebra`, spanned by the
diagonal matrices attached to the simple coroots. -/
def cartanSubalgebra : LieSubalgebra ℚ (t.lieAlgebra ht) :=
  RootPairing.GeckConstruction.cartanSubalgebra' (t.rationalBase ht)

/-- The distinguished Cartan subalgebra is the one supplied by Geck's construction. -/
@[simp] theorem cartanSubalgebra_def :
    t.cartanSubalgebra ht =
      (RootPairing.GeckConstruction.cartanSubalgebra (t.rationalBase ht)).comap
        (t.lieAlgebra ht).incl := (rfl)

/-- **The Chevalley generators of the pinned Lie algebra, numbered by Bourbaki node.** This is
Geck's basis, whose nodes are the support of the pinned base, renumbered along
`TauCeti.DynkinType.simpleSupportEquiv`. -/
def lieBasis : LieAlgebra.Basis (Fin t.rank) (t.cartanSubalgebra ht) :=
  (RootPairing.GeckConstruction.basis (t.rationalBase ht)).reindex (t.simpleSupportEquiv ht)

/-! ## The generators as explicit matrices -/

/-- The Bourbaki-numbered Cartan generator is Geck's explicit diagonal matrix for the
corresponding simple root. -/
@[simp] theorem coe_lieBasis_h (i : Fin t.rank) :
    ((t.lieBasis ht).h i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      RootPairing.GeckConstruction.h (t.simpleSupportEquiv ht i) := by
  rw [lieBasis, LieAlgebra.Basis.reindex_h]
  rfl

/-- The Bourbaki-numbered raising generator is Geck's explicit matrix for the corresponding
simple root. -/
@[simp] theorem coe_lieBasis_e (i : Fin t.rank) :
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      RootPairing.GeckConstruction.e (t.simpleSupportEquiv ht i) := by
  rw [lieBasis, LieAlgebra.Basis.reindex_e]
  rfl

/-- The Bourbaki-numbered lowering generator is Geck's explicit matrix for the corresponding
simple root. -/
@[simp] theorem coe_lieBasis_f (i : Fin t.rank) :
    ((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      RootPairing.GeckConstruction.f (t.simpleSupportEquiv ht i) := by
  rw [lieBasis, LieAlgebra.Basis.reindex_f]
  rfl

/-- The Bourbaki-numbered raising and lowering generators span the pinned Lie algebra. -/
theorem lieSpan_lieBasis_e_union_f :
    LieSubalgebra.lieSpan ℚ (t.lieAlgebra ht)
      (Set.range (t.lieBasis ht).e ∪ Set.range (t.lieBasis ht).f) = ⊤ :=
  (t.lieBasis ht).span_ef

/-! ## The pinned Cartan matrix and the relations -/

/-- **The Cartan matrix of the pinned Chevalley generators is the Cartan matrix of the Dynkin
type**, in the Bourbaki numbering. -/
@[simp] theorem A_lieBasis : (t.lieBasis ht).A = t.cartanMatrix := by
  ext i j
  rw [lieBasis, LieAlgebra.Basis.reindex_A, Matrix.submatrix_apply, basis_A_eq,
    cartanMatrix_rationalBase]

/-- The action of a Cartan generator on a raising generator, against the pinned Cartan matrix. -/
theorem lie_lieBasis_h_e (i j : Fin t.rank) :
    ⁅(t.lieBasis ht).h j, (t.lieBasis ht).e i⁆ = t.cartanMatrix i j • (t.lieBasis ht).e i := by
  rw [(t.lieBasis ht).lie_h_e, A_lieBasis]

/-- The action of a Cartan generator on a lowering generator, against the pinned Cartan matrix. -/
theorem lie_lieBasis_h_f (i j : Fin t.rank) :
    ⁅(t.lieBasis ht).h j, (t.lieBasis ht).f i⁆ = -t.cartanMatrix i j • (t.lieBasis ht).f i := by
  rw [(t.lieBasis ht).lie_h_f, A_lieBasis]

/-! ## Nilpotency -/

/-- The explicit raising matrices are nilpotent. -/
theorem isNilpotent_coe_lieBasis_e (i : Fin t.rank) :
    IsNilpotent ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) := by
  rw [coe_lieBasis_e]
  exact isNilpotent_e _

/-- The lowering generators are nilpotent matrices. -/
theorem isNilpotent_coe_lieBasis_f (i : Fin t.rank) :
    IsNilpotent ((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) := by
  rw [coe_lieBasis_f]
  exact isNilpotent_f _

/-! ## The Cartan subalgebra -/

instance instIsLieAbelianCartanSubalgebra : IsLieAbelian (t.cartanSubalgebra ht) :=
  (t.lieBasis ht).isLieAbelian_cartan

instance instIsCartanSubalgebraCartanSubalgebra : (t.cartanSubalgebra ht).IsCartanSubalgebra :=
  (t.lieBasis ht).isCartanSubalgebra

/-- The Cartan generators are a basis of the Cartan subalgebra. -/
def cartanBasis : Module.Basis (Fin t.rank) ℚ (t.cartanSubalgebra ht) :=
  (Module.Basis.span (t.lieBasis ht).linInd).map
    (LinearEquiv.ofEq _ _ (t.lieBasis ht).coe_cartan_eq_span).symm

/-- The `i`-th vector of that basis is the `i`-th Cartan generator. -/
@[simp] theorem coe_cartanBasis (i : Fin t.rank) :
    (t.cartanBasis ht i : t.lieAlgebra ht) = (t.lieBasis ht).h i := by
  simp only [cartanBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/-- **The Cartan subalgebra has dimension the rank of the Dynkin diagram.** -/
theorem finrank_cartanSubalgebra : Module.finrank ℚ (t.cartanSubalgebra ht) = t.rank := by
  simpa using Module.finrank_eq_card_basis (t.cartanBasis ht)

end

end TauCeti.DynkinType
