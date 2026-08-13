/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the column module carries the matrix action of `Mathlib.LinearAlgebra.Matrix.Action`,
-- and the length of the regular module appears in the exported statements.
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.RingTheory.Length
-- Non-public: used only inside proofs.  Reindexing a matrix ring, and the comparison of simple
-- modules over a simple Artinian ring (which brings with it simplicity and semisimplicity of a
-- matrix ring over a division ring) are the engines of the arguments below; neither is mentioned
-- by an exported statement.
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.RingTheory.Semisimple.SimpleArtinian

/-!
# The degree and the division ring of a matrix presentation are invariants

Artin--Wedderburn presents a simple Artinian ring as a matrix ring `Matᵢ(D)` over a division ring,
and a semisimple ring as a finite product of such blocks.  Mathlib supplies the presentation but
says nothing about how much of it is determined by the ring: `TauCeti.card_blocks_eq` shows the
*number* of blocks is an invariant and `TauCeti.blocks_equiv_simpleModules` matches the blocks with
the simple modules, but both are silent about the two remaining pieces of data, the size `ι` of a
block and its division ring `D`.  This file determines both, for a *single* block: it does not treat
a product of blocks; `TauCeti.wedderburn_blocks_unique` applies the result here after matching the
factors of two product presentations.

The content is a description of those two data of `A = Matᵢ(D)` in terms that transport along a
ring isomorphism.  The **column module** `ι → D`, on which `A` acts by `Matrix.mulVec`, is a simple
`A`-module (`TauCeti.Matrix.isSimpleModule_pi`), its endomorphism ring is `Dᵐᵒᵖ`
(`TauCeti.Matrix.mulOppositeRingEquivEnd`), and the regular module is the direct sum of the
`Fintype.card ι` columns (`TauCeti.Matrix.linearEquivPi`).  So the *size* is the length of the
regular module, and the *division ring* is the opposite endomorphism ring of a minimal left ideal.
Both are manifestly invariant, and a ring isomorphism `f : R ≃+* Matᵢ(D)`, read through
`RingEquiv.toSemilinearEquiv` as an `f`-semilinear isomorphism of regular modules, carries them
back to `R`.

## Main results

* `TauCeti.Matrix.isSimpleModule_pi`, `TauCeti.Matrix.mulOppositeRingEquivEnd`,
  `TauCeti.Matrix.linearEquivPi`: the column module of `Matᵢ(D)` is simple with endomorphism ring
  `Dᵐᵒᵖ`, and the regular module is `Fintype.card ι` copies of it.
* `TauCeti.length_eq_card_of_ringEquiv_matrix`: a ring presented as `Matᵢ(D)` has regular module of
  length `Fintype.card ι`.
* `TauCeti.nonempty_end_ringEquiv_of_ringEquiv_matrix`: for a ring presented as `Matᵢ(D)`, the
  endomorphism ring of any simple left ideal is `Dᵐᵒᵖ`.
* `TauCeti.card_eq_of_ringEquiv_matrix`, `TauCeti.nonempty_ringEquiv_of_ringEquiv_matrix` and the
  packaged `TauCeti.wedderburn_data_unique`: **two matrix presentations of the same ring have the
  same size and isomorphic division rings.**
* `TauCeti.nonempty_ringEquiv_matrix_iff`: the resulting classification, that `Matᵢ(D) ≃+* Mat_κ(E)`
  holds exactly when `ι` and `κ` have the same cardinality and `D ≃+* E`.

## Implementation notes

The index type `ι` is an arbitrary `Fintype`, not `Fin n`; the `Fin n` shape that the
Artin--Wedderburn theorems produce is the corollary `TauCeti.wedderburn_data_unique`.  `Nonempty ι`
is essential and not decoration wherever the division ring is involved: `Mat_∅(D)` is the trivial
ring for every `D`, so an empty block determines no `D` at all.  It is the hypothesis `NeZero n`
supplies in `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing` and in
`TauCeti.card_blocks_eq`.  The statements about the size alone hold for every `ι`, the empty case
saying that the trivial ring has regular module of length `0`, and are stated without it.

Everything is stated for the *left* regular module, matching the convention of `IsSemisimpleRing`,
so the simple module is the column module -- on which a matrix acts by `Matrix.mulVec` -- and the
endomorphism ring, acting on the other side, comes out as `Dᵐᵒᵖ` rather than `D`.  This is also
Mathlib's convention in `IsSimpleRing.exists_ringEquiv_matrix_end_mulOpposite`.

Note that `DecidableEq ι` is needed to make `Matᵢ(D)` a ring, but not to state the transport
results, whose types mention only the multiplication and addition of `Matᵢ(D)`; those are therefore
stated without it and use `classical` internally.

The matching of the blocks of two product presentations is proved downstream in
`TauCeti/RingTheory/Semisimple/Wedderburn/Uniqueness.lean`: the coordinate central idempotents
recover the factor permutation, and the theorem in this file then identifies the data in each
factor.

## References

This is the single-block case of the Layer 2 target "uniqueness / invariance" -- the degrees `nᵢ`
and the division rings `Dᵢ` of a Wedderburn presentation are determined by the ring -- of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md);
the product-level result is `TauCeti.wedderburn_blocks_unique`.

See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §26.
-/

public section

namespace TauCeti

open Matrix

section Block

variable {ι : Type*} [Fintype ι] {D : Type*}

section DivisionSemiring

variable [DivisionSemiring D]

/-- **A nonzero column vector generates the column module.**  Over a division semiring one can solve
`A *ᵥ v = w` for `A` as soon as `v ≠ 0`: put `w` in the column of `A` indexed by a coordinate where
`v` does not vanish, scaled by the inverse of that coordinate. -/
theorem Matrix.exists_mulVec_eq {v : ι → D} (hv : v ≠ 0) (w : ι → D) :
    ∃ A : Matrix ι ι D, A *ᵥ v = w := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  rw [Pi.zero_apply] at hj
  refine ⟨Matrix.of fun i k ↦ if k = j then w i * (v j)⁻¹ else 0, funext fun i ↦ ?_⟩
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp [mul_assoc, inv_mul_cancel₀ hj]
  · intro k _ hk
    simp [hk]
  · simp

end DivisionSemiring

section Semiring

variable [DecidableEq ι] [Semiring D]

/-- Right multiplication by an element of `D` on column vectors.  It commutes with left
multiplication by a matrix, so it is an endomorphism of the column module, and these are all of
them (`TauCeti.Matrix.mulOppositeRingEquivEnd`). -/
def Matrix.rightMul (d : D) : Module.End (Matrix ι ι D) (ι → D) where
  toFun v i := v i * d
  map_add' u v := funext fun i ↦ add_mul ..
  map_smul' A v := funext fun i ↦ by
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

-- The definitions in this file are deliberately not `@[expose]`d: the `simp` lemmas below are the
-- interface, and they are proved through the equation lemmas rather than by `rfl`.
@[simp]
theorem Matrix.rightMul_apply (d : D) (v : ι → D) (i : ι) : Matrix.rightMul d v i = v i * d := by
  simp [Matrix.rightMul]

variable (ι D) in
/-- **The regular module of a matrix ring is the direct sum of its columns.**  Left multiplication
acts on each column separately, so `Matᵢ(D)` is `Fintype.card ι` copies of the column module. -/
def Matrix.linearEquivPi : Matrix ι ι D ≃ₗ[Matrix ι ι D] (ι → (ι → D)) where
  toFun A j i := A i j
  invFun f := Matrix.of fun i j ↦ f j i
  map_add' _ _ := rfl
  map_smul' B A := funext fun j ↦ funext fun i ↦ by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem Matrix.linearEquivPi_apply (A : Matrix ι ι D) (j i : ι) :
    Matrix.linearEquivPi ι D A j i = A i j := by
  simp only [Matrix.linearEquivPi]
  rfl

@[simp]
theorem Matrix.linearEquivPi_symm_apply (f : ι → ι → D) (i j : ι) :
    (Matrix.linearEquivPi ι D).symm f i j = f j i := by
  simp only [Matrix.linearEquivPi]
  rfl

end Semiring

section DivisionRing

variable [DecidableEq ι] [DivisionRing D]

/-- **The column module of a matrix ring over a division ring is simple.**  This is the simple
module of the Wedderburn block `Matᵢ(D)`; since a matrix ring over a division ring is simple
Artinian, every simple `Matᵢ(D)`-module is isomorphic to it. -/
instance Matrix.isSimpleModule_pi [Nonempty ι] :
    IsSimpleModule (Matrix ι ι D) (ι → D) := by
  have : IsSimpleOrder (Submodule (Matrix ι ι D) (ι → D)) := by
    refine ⟨fun N ↦ or_iff_not_imp_left.mpr fun hN ↦ ?_⟩
    obtain ⟨v, hvN, hv⟩ := N.exists_mem_ne_zero_of_ne_bot hN
    refine eq_top_iff.mpr fun w _ ↦ ?_
    obtain ⟨A, hA⟩ := Matrix.exists_mulVec_eq hv w
    exact hA ▸ N.smul_mem A hvN
  exact ⟨⟩

variable (ι D) in
/-- **The endomorphism ring of the column module of `Matᵢ(D)` is `Dᵐᵒᵖ`.**  An endomorphism commutes
with the matrices carrying one coordinate to another, so it is right multiplication by the single
scalar recording its value at a standard basis vector.  The multiplication is reversed because the
scalars act on the side opposite to the matrices. -/
noncomputable def Matrix.mulOppositeRingEquivEnd [Nonempty ι] :
    Dᵐᵒᵖ ≃+* Module.End (Matrix ι ι D) (ι → D) :=
  RingEquiv.ofBijective
    ({ toFun d := Matrix.rightMul d.unop
       map_one' := by ext v i; simp
       map_mul' d e := by ext v i; simp [mul_assoc]
       map_zero' := by ext v i; simp
       map_add' d e := by ext v i; simp [mul_add] } :
      Dᵐᵒᵖ →+* Module.End (Matrix ι ι D) (ι → D)) <| by
    obtain ⟨j⟩ := ‹Nonempty ι›
    constructor
    · refine (injective_iff_map_eq_zero _).mpr fun d hd ↦ ?_
      have := congrFun
        (congrArg (fun g : Module.End (Matrix ι ι D) (ι → D) ↦ g (Pi.single j 1)) hd) j
      simpa using this
    · -- The value of `f` at the `j`-th standard basis vector determines `f`.
      intro f
      refine ⟨MulOpposite.op (f (Pi.single j 1) j), ?_⟩
      ext v i
      -- Each `v` is the image of that basis vector under the matrix with `v` in the `j`-th column.
      have hA : Matrix.mulVec (Matrix.of fun i k ↦ if k = j then v i else 0)
          (Pi.single j (1 : D)) = v := by
        refine funext fun i ↦ ?_
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j] <;> simp +contextual
      have hf := congrFun
        (f.map_smul (Matrix.of fun i k ↦ if k = j then v i else 0) (Pi.single j 1)) i
      rw [Matrix.smul_eq_mulVec, hA] at hf
      rw [hf]
      simp [Matrix.mulVec, dotProduct]

@[simp]
theorem Matrix.mulOppositeRingEquivEnd_apply [Nonempty ι] (d : Dᵐᵒᵖ) :
    Matrix.mulOppositeRingEquivEnd ι D d = Matrix.rightMul d.unop := by
  simp [Matrix.mulOppositeRingEquivEnd]

variable (ι D) in
/-- **The regular module of `Matᵢ(D)` has length `Fintype.card ι`**: it is the direct sum of its
`Fintype.card ι` columns, and each column is simple.  For empty `ι` both sides are `0`, the ring
being trivial. -/
theorem Matrix.length_self_eq_card :
    Module.length (Matrix ι ι D) (Matrix ι ι D) = Fintype.card ι := by
  rw [(Matrix.linearEquivPi ι D).length_eq, Module.length_pi_of_fintype]
  rcases isEmpty_or_nonempty ι with h | h <;> simp

end DivisionRing

end Block

section Transport

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] {D : Type*} [DivisionRing D]

/-- **The size of a matrix presentation is the length of the regular module**, hence an invariant of
the ring: a ring isomorphism `f : R ≃+* Matᵢ(D)` is an `f`-semilinear isomorphism of regular
modules, so it identifies the two lattices of left ideals. -/
theorem length_eq_card_of_ringEquiv_matrix (f : R ≃+* Matrix ι ι D) :
    Module.length R R = Fintype.card ι := by
  classical
  have hpair := RingHomInvPair.of_ringEquiv f
  have := hpair.symm
  rw [← Matrix.length_self_eq_card ι D]
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f.toSemilinearEquiv)

/-- **The division ring of a matrix presentation is the opposite endomorphism ring of any simple
left ideal**, hence an invariant of the ring.

The `f`-semilinear isomorphism of regular modules carries `I` to a simple left ideal of `Matᵢ(D)`
and identifies the two endomorphism rings; over the simple Artinian ring `Matᵢ(D)` that ideal is
isomorphic to the column module, whose endomorphism ring is `Dᵐᵒᵖ`. -/
theorem nonempty_end_ringEquiv_of_ringEquiv_matrix [Nonempty ι] (f : R ≃+* Matrix ι ι D)
    (I : Submodule R R) [IsSimpleModule R I] :
    Nonempty (Module.End R I ≃+* Dᵐᵒᵖ) := by
  classical
  have hpair := RingHomInvPair.of_ringEquiv f
  have := hpair.symm
  have key : IsSimpleModule (Matrix ι ι D)
      (Submodule.orderIsoMapComap f.toSemilinearEquiv I) :=
    isSimpleModule_iff_isAtom.mpr
      (((Submodule.orderIsoMapComap f.toSemilinearEquiv).isAtom_iff I).mpr
        (isSimpleModule_iff_isAtom.mp ‹_›))
  obtain ⟨g⟩ := IsIsotypicOfType.of_isSimpleRing (Matrix ι ι D) (ι → D) (Matrix ι ι D)
    (Submodule.orderIsoMapComap f.toSemilinearEquiv I)
  exact ⟨((f.toSemilinearEquiv.submoduleMap I).conjRingEquiv.trans g.conjRingEquiv).trans
    (Matrix.mulOppositeRingEquivEnd ι D).symm⟩

end Transport

section Uniqueness

variable {R : Type*} [Ring R]
  {ι : Type*} [Fintype ι] {D : Type*} [DivisionRing D]
  {κ : Type*} [Fintype κ] {E : Type*} [DivisionRing E]

/-- **The size of a matrix presentation is unique**: two presentations of one ring as a matrix ring
over a division ring have equally many rows. -/
theorem card_eq_of_ringEquiv_matrix (f : R ≃+* Matrix ι ι D) (g : R ≃+* Matrix κ κ E) :
    Fintype.card ι = Fintype.card κ := by
  have h := (length_eq_card_of_ringEquiv_matrix f).symm.trans
    (length_eq_card_of_ringEquiv_matrix g)
  exact_mod_cast h

/-- **The division ring of a matrix presentation is unique up to isomorphism**: two presentations of
one ring as a matrix ring over a division ring have isomorphic division rings.

Both division rings are computed from a single minimal left ideal of the ring, so no comparison of
choices is needed: they are the two readings of one and the same endomorphism ring. -/
theorem nonempty_ringEquiv_of_ringEquiv_matrix [Nonempty ι] [Nonempty κ]
    (f : R ≃+* Matrix ι ι D) (g : R ≃+* Matrix κ κ E) : Nonempty (D ≃+* E) := by
  classical
  have : IsSimpleRing R := IsSimpleRing.of_ringEquiv f.symm inferInstance
  have : IsSemisimpleRing R := f.symm.isSemisimpleRing
  -- `R` is nontrivial, so it has a minimal left ideal; simplicity of `R` is only used for that.
  obtain ⟨I, hI⟩ := IsAtomic.exists_atom (Submodule R R)
  rw [← isSimpleModule_iff_isAtom] at hI
  obtain ⟨eD⟩ := nonempty_end_ringEquiv_of_ringEquiv_matrix f I
  obtain ⟨eE⟩ := nonempty_end_ringEquiv_of_ringEquiv_matrix g I
  exact ⟨RingEquiv.unop (eD.symm.trans eE)⟩

/-- **Matrix rings over division rings are classified by their size and their division ring.**  Two
of them are isomorphic exactly when they have equally many rows and isomorphic division rings.

The forward direction is the uniqueness above, applied to the two presentations of `Matᵢ(D)` given
by the identity and by the isomorphism; the converse reindexes along an equivalence of the two
index types (`Matrix.reindexRingEquiv`) and then transports the entries
(`RingEquiv.mapMatrix`). -/
theorem nonempty_ringEquiv_matrix_iff [Nonempty ι] [Nonempty κ] :
    Nonempty (Matrix ι ι D ≃+* Matrix κ κ E) ↔
      Fintype.card ι = Fintype.card κ ∧ Nonempty (D ≃+* E) := by
  classical
  refine ⟨fun ⟨φ⟩ ↦ ⟨card_eq_of_ringEquiv_matrix (.refl _) φ,
    nonempty_ringEquiv_of_ringEquiv_matrix (.refl _) φ⟩, fun ⟨hcard, ⟨d⟩⟩ ↦ ?_⟩
  exact ⟨(Matrix.reindexRingEquiv D (Fintype.equivOfCardEq hcard)).trans d.mapMatrix⟩

/-- **Uniqueness of the Wedderburn data of a simple Artinian ring.**  Two presentations of a ring as
a matrix ring over a division ring have the same degree and isomorphic division rings.

This is the `Fin n` shape produced by `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`; the
positivity hypotheses `NeZero n` are the ones that theorem supplies, and they are essential, since
`Mat₀(D)` is the trivial ring for every `D`. -/
theorem wedderburn_data_unique {n m : ℕ} [NeZero n] [NeZero m]
    (f : R ≃+* Matrix (Fin n) (Fin n) D) (g : R ≃+* Matrix (Fin m) (Fin m) E) :
    n = m ∧ Nonempty (D ≃+* E) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne m))
  refine ⟨?_, nonempty_ringEquiv_of_ringEquiv_matrix f g⟩
  simpa using card_eq_of_ringEquiv_matrix f g

end Uniqueness

end TauCeti
