/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
public import TauCeti.Algebra.Lie.Basis.Cartan
public import TauCeti.Algebra.Lie.Basis.Reindex
import TauCeti.Algebra.Lie.Weights.Automorphism
public import TauCeti.LinearAlgebra.RootSystem.GeckConstruction.ChevalleyInvolution
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# The pinned split Lie algebra of a Dynkin type

`TauCeti.DynkinType.simplyConnectedRootDatum` pins one integral root datum per valid Dynkin type,
and `TauCeti.DynkinType.rationalRootSystem` reads it as a root system over `ℚ`. This file feeds
that root system to Geck's construction and names the resulting Lie algebra:
`TauCeti.DynkinType.lieAlgebra` is a Lie subalgebra of the square matrices indexed by one
coordinate per element of the pinned base support and one per root, spanned by the explicit
matrices Geck writes down from the root data. The base support is identified with the Bourbaki
nodes below. No existence theorem is invoked: every element of the carrier traces back to the
pinned root tables.

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
`TauCeti.DynkinType.lieSpan_lieBasis_e_union_f_eq_top`.

## Main definitions

* `TauCeti.DynkinType.GeckIndex`: the index set of the matrices, one coordinate per element of the
  pinned base support and one per root.
* `TauCeti.DynkinType.lieAlgebra`: the split Lie algebra of a valid Dynkin type.
* `TauCeti.DynkinType.cartanSubalgebra`: its distinguished Cartan subalgebra.
* `TauCeti.DynkinType.lieBasis`: its Chevalley generators, numbered by Bourbaki node.
* `TauCeti.DynkinType.geckLieEquiv`: the identification of the named carrier with Geck's, as an
  equivalence of Lie algebras.
* `TauCeti.DynkinType.chevalleyInvolution`: its signed Chevalley involution.

## Main results

* `TauCeti.DynkinType.lieBasis_A_eq`: the Cartan matrix of the basis is the pinned Cartan matrix of
  the Dynkin type.
* `TauCeti.DynkinType.coe_lieBasis_h`, `coe_lieBasis_e`, and `coe_lieBasis_f`: each generator is
  the explicit matrix Geck attaches to the corresponding simple root.
* `TauCeti.DynkinType.lie_lieBasis_h_e` and `TauCeti.DynkinType.lie_lieBasis_h_f`: the two
  relations that mention the Cartan matrix, read against the pinned numbering.
* `TauCeti.DynkinType.lieSpan_lieBasis_e_union_f_eq_top`: the raising and lowering generators
  span the pinned Lie algebra.
* `TauCeti.DynkinType.isNilpotent_coe_lieBasis_e` and
  `TauCeti.DynkinType.isNilpotent_coe_lieBasis_f`: the raising and lowering generators are
  nilpotent matrices.
* `TauCeti.DynkinType.finrank_cartanSubalgebra`: the Cartan subalgebra has dimension `t.rank`.
* `TauCeti.DynkinType.geckLieEquiv_chevalleyInvolution`: the involution is Geck's, read through
  that identification.
* `TauCeti.DynkinType.chevalleyInvolution_lieBasis_h`,
  `TauCeti.DynkinType.chevalleyInvolution_lieBasis_e` and
  `TauCeti.DynkinType.chevalleyInvolution_lieBasis_f`: the involution on the numbered generators.
* `TauCeti.DynkinType.chevalleyInvolution_cartan`: the involution acts by negation on the entire
  distinguished Cartan subalgebra.
* `TauCeti.DynkinType.map_rootSpace_chevalleyInvolution`: it exchanges the root spaces indexed by
  opposite Cartan functionals.

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
element of the pinned base support and one for each root of the pinned root system. The former is
identified with the Bourbaki nodes by `TauCeti.DynkinType.simpleSupportEquiv`. -/
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
  (RootPairing.GeckConstruction.basis (t.rationalBase ht)).reindex (t.simpleSupportEquiv ht).symm

/-! ## The generators as explicit matrices -/

/-- The Bourbaki-numbered Cartan generator is Geck's explicit diagonal matrix for the
corresponding simple root. -/
@[simp] theorem coe_lieBasis_h (i : Fin t.rank) :
    ((t.lieBasis ht).h i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      RootPairing.GeckConstruction.h (t.simpleSupportEquiv ht i) := by
  rw [lieBasis, LieAlgebra.Basis.reindex_h]
  -- Mathlib defines the underlying `basis.h` value by this constructor and provides no separate
  -- coercion theorem, so the final equality is definitional.
  rfl

/-- The Bourbaki-numbered raising generator is Geck's explicit matrix for the corresponding
simple root. -/
@[simp] theorem coe_lieBasis_e (i : Fin t.rank) :
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      RootPairing.GeckConstruction.e (t.simpleSupportEquiv ht i) := by
  rw [lieBasis, LieAlgebra.Basis.reindex_e]
  -- As for `basis.h`, Mathlib provides no separate coercion theorem for this constructor field.
  rfl

/-- The Bourbaki-numbered lowering generator is Geck's explicit matrix for the corresponding
simple root. -/
@[simp] theorem coe_lieBasis_f (i : Fin t.rank) :
    ((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      RootPairing.GeckConstruction.f (t.simpleSupportEquiv ht i) := by
  rw [lieBasis, LieAlgebra.Basis.reindex_f]
  -- As for `basis.h`, Mathlib provides no separate coercion theorem for this constructor field.
  rfl

/-- The Bourbaki-numbered raising and lowering generators span the pinned Lie algebra. -/
theorem lieSpan_lieBasis_e_union_f_eq_top :
    LieSubalgebra.lieSpan ℚ (t.lieAlgebra ht)
      (Set.range (t.lieBasis ht).e ∪ Set.range (t.lieBasis ht).f) = ⊤ :=
  (t.lieBasis ht).span_ef

/-! ## The pinned Cartan matrix and the relations -/

/-- **The Cartan matrix of the pinned Chevalley generators is the Cartan matrix of the Dynkin
type**, in the Bourbaki numbering. -/
@[simp] theorem lieBasis_A_eq : (t.lieBasis ht).A = t.cartanMatrix := by
  ext i j
  rw [lieBasis, LieAlgebra.Basis.reindex_A, Matrix.submatrix_apply, Equiv.symm_symm,
    basis_A_eq, cartanMatrix_rationalBase]

/-- The action of a Cartan generator on a raising generator, against the pinned Cartan matrix. -/
@[simp] theorem lie_lieBasis_h_e (i j : Fin t.rank) :
    ⁅(t.lieBasis ht).h j, (t.lieBasis ht).e i⁆ = t.cartanMatrix i j • (t.lieBasis ht).e i := by
  rw [(t.lieBasis ht).lie_h_e, lieBasis_A_eq]

/-- The action of a Cartan generator on a lowering generator, against the pinned Cartan matrix. -/
@[simp] theorem lie_lieBasis_h_f (i j : Fin t.rank) :
    ⁅(t.lieBasis ht).h j, (t.lieBasis ht).f i⁆ = -t.cartanMatrix i j • (t.lieBasis ht).f i := by
  rw [(t.lieBasis ht).lie_h_f, lieBasis_A_eq]

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
  (t.lieBasis ht).cartanBasis

/-- The `i`-th vector of that basis is the `i`-th Cartan generator. -/
@[simp] theorem coe_cartanBasis (i : Fin t.rank) :
    (t.cartanBasis ht i : t.lieAlgebra ht) = (t.lieBasis ht).h i := by simp [cartanBasis]

/-- **The Cartan subalgebra has dimension the rank of the Dynkin diagram.** -/
theorem finrank_cartanSubalgebra : Module.finrank ℚ (t.cartanSubalgebra ht) = t.rank := by
  simpa using (t.lieBasis ht).finrank_cartan

/-! ## The Chevalley involution -/

/-- The pinned Lie algebra and Geck's construction on the pinned rational base are the same
subalgebra of matrices, `TauCeti.DynkinType.lieAlgebra_def`; this is that identification as an
equivalence of Lie algebras. It carries Geck's automorphisms over to the named carrier without
unfolding it. -/
def geckLieEquiv :
    t.lieAlgebra ht ≃ₗ⁅ℚ⁆ RootPairing.GeckConstruction.lieAlgebra (t.rationalBase ht) :=
  LieEquiv.ofEq _ _ (by rw [lieAlgebra_def])

/-- **The Chevalley involution of the pinned split Lie algebra**: the automorphism
`hᵢ ↦ -hᵢ`, `eᵢ ↦ -fᵢ`, `fᵢ ↦ -eᵢ` of `TauCeti.DynkinType.lieAlgebra`. It is
`TauCeti.geckChevalleyInvolution` of the pinned rational base, read against the Bourbaki
numbering. -/
def chevalleyInvolution : t.lieAlgebra ht ≃ₗ⁅ℚ⁆ t.lieAlgebra ht :=
  ((t.geckLieEquiv ht).trans (geckChevalleyInvolution (t.rationalBase ht))).trans
    (t.geckLieEquiv ht).symm

/-- The pinned Chevalley involution is Geck's involution, read through the identification of the
two carriers. -/
@[simp]
theorem geckLieEquiv_chevalleyInvolution (x : t.lieAlgebra ht) :
    t.geckLieEquiv ht (t.chevalleyInvolution ht x) =
      geckChevalleyInvolution (t.rationalBase ht) (t.geckLieEquiv ht x) :=
  (t.geckLieEquiv ht).apply_symm_apply _

-- The generator formulas for `TauCeti.geckChevalleyInvolution` are stated for the bundled
-- subtype elements, so each Bourbaki-numbered generator is first written in that shape.
private theorem geckLieEquiv_lieBasis_h (i : Fin t.rank) : t.geckLieEquiv ht ((t.lieBasis ht).h i) =
    ⟨RootPairing.GeckConstruction.h (t.simpleSupportEquiv ht i), h_mem_lieAlgebra _⟩ :=
  Subtype.ext (t.coe_lieBasis_h ht i)

private theorem geckLieEquiv_lieBasis_e (i : Fin t.rank) : t.geckLieEquiv ht ((t.lieBasis ht).e i) =
    ⟨RootPairing.GeckConstruction.e (t.simpleSupportEquiv ht i), e_mem_lieAlgebra _⟩ :=
  Subtype.ext (t.coe_lieBasis_e ht i)

private theorem geckLieEquiv_lieBasis_f (i : Fin t.rank) : t.geckLieEquiv ht ((t.lieBasis ht).f i) =
    ⟨RootPairing.GeckConstruction.f (t.simpleSupportEquiv ht i), f_mem_lieAlgebra _⟩ :=
  Subtype.ext (t.coe_lieBasis_f ht i)

/-- **The Chevalley involution negates each Cartan generator**, `hᵢ ↦ -hᵢ`. -/
@[simp] theorem chevalleyInvolution_lieBasis_h (i : Fin t.rank) :
    t.chevalleyInvolution ht ((t.lieBasis ht).h i) = -(t.lieBasis ht).h i := by
  rw [← EmbeddingLike.apply_eq_iff_eq (t.geckLieEquiv ht), geckLieEquiv_chevalleyInvolution,
    map_neg, geckLieEquiv_lieBasis_h]
  exact geckChevalleyInvolution_h (t.rationalBase ht) (t.simpleSupportEquiv ht i)

/-- **The Chevalley involution sends each raising generator to minus the lowering generator with
the same Bourbaki number**, `eᵢ ↦ -fᵢ`. -/
@[simp] theorem chevalleyInvolution_lieBasis_e (i : Fin t.rank) :
    t.chevalleyInvolution ht ((t.lieBasis ht).e i) = -(t.lieBasis ht).f i := by
  rw [← EmbeddingLike.apply_eq_iff_eq (t.geckLieEquiv ht), geckLieEquiv_chevalleyInvolution,
    map_neg, geckLieEquiv_lieBasis_e, geckLieEquiv_lieBasis_f]
  exact geckChevalleyInvolution_e (t.rationalBase ht) (t.simpleSupportEquiv ht i)

/-- **The Chevalley involution sends each lowering generator to minus the raising generator with
the same Bourbaki number**, `fᵢ ↦ -eᵢ`. -/
@[simp] theorem chevalleyInvolution_lieBasis_f (i : Fin t.rank) :
    t.chevalleyInvolution ht ((t.lieBasis ht).f i) = -(t.lieBasis ht).e i := by
  rw [← EmbeddingLike.apply_eq_iff_eq (t.geckLieEquiv ht), geckLieEquiv_chevalleyInvolution,
    map_neg, geckLieEquiv_lieBasis_e, geckLieEquiv_lieBasis_f]
  exact geckChevalleyInvolution_f (t.rationalBase ht) (t.simpleSupportEquiv ht i)

/-- The Chevalley involution of the pinned split Lie algebra is its own inverse. -/
@[simp] theorem chevalleyInvolution_symm :
    (t.chevalleyInvolution ht).symm = t.chevalleyInvolution ht := by
  refine LieEquiv.ext fun x => ?_
  rw [LieEquiv.symm_apply_eq, ← EmbeddingLike.apply_eq_iff_eq (t.geckLieEquiv ht),
    geckLieEquiv_chevalleyInvolution, geckLieEquiv_chevalleyInvolution]
  exact (geckChevalleyInvolution_geckChevalleyInvolution (t.rationalBase ht) _).symm

/-! ## Action on the Cartan subalgebra and weights -/

/-- **The pinned Chevalley involution acts by negation on the entire distinguished Cartan
subalgebra.** The numbered Cartan generators are a module basis, so their defining formula
determines the restriction of the involution. -/
@[simp]
theorem chevalleyInvolution_cartan (x : t.cartanSubalgebra ht) :
    t.chevalleyInvolution ht (x : t.lieAlgebra ht) = -(x : t.lieAlgebra ht) := by
  let f : t.cartanSubalgebra ht →ₗ[ℚ] t.lieAlgebra ht :=
    (t.chevalleyInvolution ht).toLieHom.toLinearMap.comp
      (t.cartanSubalgebra ht).incl.toLinearMap
  let g : t.cartanSubalgebra ht →ₗ[ℚ] t.lieAlgebra ht :=
    -(t.cartanSubalgebra ht).incl.toLinearMap
  have hfg : f = g := (t.cartanBasis ht).ext fun i ↦ by
    -- Expose the two linear maps on a Cartan basis vector.
    change t.chevalleyInvolution ht ((t.cartanBasis ht i : t.cartanSubalgebra ht) :
      t.lieAlgebra ht) = -((t.cartanBasis ht i : t.cartanSubalgebra ht) : t.lieAlgebra ht)
    rw [t.coe_cartanBasis ht, t.chevalleyInvolution_lieBasis_h ht]
  exact LinearMap.congr_fun hfg x

/-- The pinned Chevalley involution normalizes the distinguished Cartan subalgebra. This is the
hypothesis used to restrict it to the Cartan and to form its induced permutation of weights. -/
@[simp]
theorem map_chevalleyInvolution_cartanSubalgebra :
    ((RootPairing.GeckConstruction.cartanSubalgebra (t.rationalBase ht)).comap
        (t.lieAlgebra ht).incl).map (t.chevalleyInvolution ht).toLieHom =
      t.cartanSubalgebra ht := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Expose the Lie-homomorphism coercion in the mapped-subalgebra membership goal.
    change t.chevalleyInvolution ht x ∈ t.cartanSubalgebra ht
    rw [t.chevalleyInvolution_cartan ht ⟨x, hx⟩]
    exact neg_mem hx
  · intro hy
    refine ⟨-y, neg_mem hy, ?_⟩
    -- Expose the Lie-homomorphism coercion in the witness equation.
    change t.chevalleyInvolution ht (-y) = y
    rw [t.chevalleyInvolution_cartan ht ⟨-y, neg_mem hy⟩]
    simp

/-- Restricting the pinned Chevalley involution to the distinguished Cartan subalgebra gives
pointwise negation. -/
@[simp]
theorem chevalleyInvolution_ofSubalgebras_apply (x : t.cartanSubalgebra ht) :
    (t.chevalleyInvolution ht).ofSubalgebras (t.cartanSubalgebra ht)
        (t.cartanSubalgebra ht) (by
          simpa only [cartanSubalgebra_def] using
            t.map_chevalleyInvolution_cartanSubalgebra ht) x = -x := by
  apply Subtype.ext
  rw [LieEquiv.ofSubalgebras_apply, t.chevalleyInvolution_cartan ht]
  rfl

/-- The inverse of the restriction of the pinned Chevalley involution to the distinguished Cartan
subalgebra is also pointwise negation. -/
@[simp]
theorem chevalleyInvolution_ofSubalgebras_symm_apply (x : t.cartanSubalgebra ht) :
    ((t.chevalleyInvolution ht).ofSubalgebras (t.cartanSubalgebra ht)
        (t.cartanSubalgebra ht) (by
          simpa only [cartanSubalgebra_def] using
            t.map_chevalleyInvolution_cartanSubalgebra ht)).symm x = -x := by
  apply Subtype.ext
  rw [LieEquiv.ofSubalgebras_symm_apply, t.chevalleyInvolution_symm ht,
    t.chevalleyInvolution_cartan ht]
  rfl

/-- Precomposing a Cartan functional with the inverse restriction of the pinned Chevalley
involution negates that functional. -/
@[simp]
theorem comp_chevalleyInvolution_ofSubalgebras_symm
    (χ : Module.Dual ℚ (t.cartanSubalgebra ht)) :
    (χ : t.cartanSubalgebra ht → ℚ) ∘
        ((t.chevalleyInvolution ht).ofSubalgebras (t.cartanSubalgebra ht)
          (t.cartanSubalgebra ht)
          (by
            simpa only [cartanSubalgebra_def] using
              t.map_chevalleyInvolution_cartanSubalgebra ht)).symm = -(χ : _ → ℚ) := by
  funext x
  rw [Function.comp_apply, t.chevalleyInvolution_ofSubalgebras_symm_apply ht]
  simp

/-- **The pinned Chevalley involution exchanges opposite root spaces.** For every Cartan
functional `χ`, it carries the `χ`-root space onto the root space indexed by `-χ`. -/
@[simp]
theorem map_rootSpace_chevalleyInvolution
    (χ : Module.Dual ℚ (t.cartanSubalgebra ht)) :
    (LieAlgebra.rootSpace (t.cartanSubalgebra ht) χ).toSubmodule.map
        ((t.chevalleyInvolution ht).toLinearEquiv :
          t.lieAlgebra ht →ₗ[ℚ] t.lieAlgebra ht) =
      (LieAlgebra.rootSpace (t.cartanSubalgebra ht) (-χ)).toSubmodule := by
  rw [map_rootSpace_eq (t.chevalleyInvolution ht)
    (by
      simpa only [cartanSubalgebra_def] using
        t.map_chevalleyInvolution_cartanSubalgebra ht)]
  congr 2
  exact t.comp_chevalleyInvolution_ofSubalgebras_symm ht χ

end

end TauCeti.DynkinType
