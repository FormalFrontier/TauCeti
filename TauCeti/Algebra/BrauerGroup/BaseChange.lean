/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.BrauerGroup.Group` is imported publicly: `BrauerGroup`, its `CommGroup`
-- structure, the class map `TauCeti.BrauerGroup.mk` and the constructor `TauCeti.CSA.op` all occur
-- in the statements below. It re-exports `TauCeti.Algebra.BrauerGroup.Trivial` and, through it,
-- `TauCeti.Algebra.BrauerGroup.Basic`, `TauCeti.IsBrauerTrivial`, `TauCeti.CSA.of`,
-- `TauCeti.CSA.base`, `TauCeti.CSA.tensorProduct` and `TauCeti.Algebra.IsSplittingField`, which is
-- why none of those is imported again here.
public import TauCeti.Algebra.BrauerGroup.Group
-- `TauCeti.Algebra.CentralSimple.BaseChange` is imported publicly: it is what makes `L ⊗[K] A`
-- visible to instance search as a central simple `L`-algebra, so that `TauCeti.CSA.baseChange`
-- below typechecks, and it re-exports the three compatibilities of scalar extension used in the
-- proofs, `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`, `baseChangeOpAlgEquiv` and
-- `baseChangeTowerAlgEquiv`.
public import TauCeti.Algebra.CentralSimple.BaseChange
-- Non-public: none of these appears in the type of an exported declaration.
-- `TauCeti.Algebra.matrixCoeffBaseChangeAlgEquiv` is used only inside the proof that base change
-- respects Brauer equivalence, and the fundamental theorem of algebra and the real quaternions
-- only by the worked examples at the end of the file.
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.CentralSimple.Quaternion
import TauCeti.Algebra.Matrix.BaseChange

/-!
# Base change is a homomorphism of Brauer groups

Let `L / K` be an extension of fields. Scalar extension sends a finite-dimensional central simple
`K`-algebra `A` to the finite-dimensional central simple `L`-algebra `L ⊗[K] A`
(`TauCeti/Algebra/CentralSimple/BaseChange.lean`), and this file shows that the assignment descends
to a group homomorphism

`TauCeti.BrauerGroup.baseChange K L : BrauerGroup K →* BrauerGroup L`.

Three things have to be checked, and each is an isomorphism of algebras that is already on record.
Well-definedness on classes is `TauCeti.Algebra.matrixCoeffBaseChangeAlgEquiv`, base change
commuting with forming a matrix algebra: it turns a witness `Mₙ(A) ≃ₐ[K] Mₘ(B)` of a Brauer
equivalence into a witness `Mₙ(L ⊗[K] A) ≃ₐ[L] Mₘ(L ⊗[K] B)` in the same two sizes.
Multiplicativity is `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`, distributivity of
scalar extension over `⊗`. That the identity goes to the identity is
`Algebra.TensorProduct.rid`, `L ⊗[K] K ≃ₐ[L] L`.

The two functor laws come with it: base change along `K = K` is the identity homomorphism
(`TauCeti.BrauerGroup.baseChange_self`) and base change composes along a tower `K → L → M`
(`TauCeti.BrauerGroup.baseChange_comp`), the latter by
`TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`. Both are equalities of homomorphisms, not
merely isomorphisms, so `K ↦ BrauerGroup K` is functorial on the nose.

## The kernel

A class dies under `baseChange K L` exactly when its algebras become Brauer trivial over `L`
(`TauCeti.BrauerGroup.mk_mem_ker_baseChange_iff`), and an algebra **split** by `L` -- one with
`L ⊗[K] A` a full matrix algebra over `L`, `TauCeti.Algebra.IsSplittingField` -- does die
(`TauCeti.BrauerGroup.mk_mem_ker_baseChange_of_isSplittingField`). The converse, that a class in
the kernel is split rather than merely Brauer trivial over `L`, is the same gap as in
`TauCeti/Algebra/BrauerGroup/Trivial.lean`: it needs the *uniqueness* half of Artin-Wedderburn, so
that a central division algebra Brauer equivalent to its base field is that base field. That is
Layer 2 of the roadmap below and is not yet available in the repository, so it is not claimed here.

What is available unconditionally is the extreme case: over an algebraically closed `L` the whole
of `BrauerGroup L` is trivial, so `baseChange K L` is the trivial homomorphism
(`TauCeti.BrauerGroup.baseChange_eq_one_of_isAlgClosed`) and every class of `BrauerGroup K` is
killed by some extension.

## References

This is the **Base change preserves central simplicity, then is a homomorphism** bullet of Layer 6
of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
whose first half is `TauCeti/Algebra/CentralSimple/BaseChange.lean`.
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.2 and
§2.4, and R. S. Pierce, *Associative Algebras*, Springer GTM 88 (1982), Chapter 12.
-/

public section

universe u

namespace TauCeti

open scoped TensorProduct

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]

/-! ### The scalar extension of a central simple algebra -/

/-- **The scalar extension of a central simple algebra**, bundled as a term of `CSA L`.

That `L ⊗[K] A` really is a finite-dimensional central simple `L`-algebra is
`TauCeti/Algebra/CentralSimple/BaseChange.lean`: centrality is
`TauCeti.Algebra.IsCentral.baseChange` and simplicity is
`TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` with `L` as the simple factor, both
instances, so there is no glue here. -/
abbrev CSA.baseChange (A : CSA.{u, u} K) : CSA.{u, u} L := CSA.of L (L ⊗[K] A)

/-- **Base change respects Brauer equivalence**, so it descends to a map of Brauer classes.

The witness is the one of the hypothesis, in the same two sizes: base change commutes with forming
a matrix algebra (`TauCeti.Algebra.matrixCoeffBaseChangeAlgEquiv`), so extending
`Mₙ(A) ≃ₐ[K] Mₘ(B)` to `L` and moving the matrices outside gives
`Mₙ(L ⊗[K] A) ≃ₐ[L] Mₘ(L ⊗[K] B)`. -/
theorem isBrauerEquivalent_baseChange_congr {A B : CSA.{u, u} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (CSA.baseChange L A) (CSA.baseChange L B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ⟨?_⟩⟩
  exact (Algebra.matrixCoeffBaseChangeAlgEquiv K L (Fin n) (A : Type u)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := L) (A₁ := L)) e).trans
      (Algebra.matrixCoeffBaseChangeAlgEquiv K L (Fin m) (B : Type u)))

namespace BrauerGroup

variable (K)

/-! ### The homomorphism -/

/-- **Base change of Brauer classes**: the group homomorphism
`BrauerGroup K →* BrauerGroup L` induced by `A ↦ L ⊗[K] A`.

It is well defined by `TauCeti.isBrauerEquivalent_baseChange_congr`, multiplicative by
`TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`, and unital by
`Algebra.TensorProduct.rid`.

`@[expose]` so that `TauCeti.BrauerGroup.baseChange_mk`, the defining property that everything
below is stated through, holds by `rfl`. -/
@[expose]
def baseChange : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} L where
  toFun x := Quotient.liftOn x (fun A ↦ mk (CSA.baseChange L A))
    fun _ _ h ↦ Quotient.sound (isBrauerEquivalent_baseChange_congr L h)
  map_one' := mk_eq_mk_of_algEquiv (Algebra.TensorProduct.rid K L L)
  map_mul' x y := Quotient.inductionOn₂ x y fun A B ↦
    mk_eq_mk_of_algEquiv (Algebra.TensorProduct.baseChangeTensorAlgEquiv K L A B)

/-- **The class of the scalar extension is the base change of the class**: the defining property of
`TauCeti.BrauerGroup.baseChange`. -/
@[simp]
theorem baseChange_mk (A : CSA.{u, u} K) : baseChange K L (mk A) = mk (CSA.baseChange L A) :=
  rfl

/-- **Base change commutes with passing to the opposite algebra.**

The two classes are also equal because both are `(baseChange K L (mk A))⁻¹`, by `map_inv` and
`TauCeti.BrauerGroup.mk_op`; the reason recorded here is the sharper one, that the two algebras are
already isomorphic (`TauCeti.Algebra.TensorProduct.baseChangeOpAlgEquiv`). -/
theorem baseChange_mk_op (A : CSA.{u, u} K) :
    baseChange K L (mk (CSA.op A)) = mk (CSA.op (CSA.baseChange L A)) :=
  mk_eq_mk_of_algEquiv (Algebra.TensorProduct.baseChangeOpAlgEquiv K L A)

/-! ### Functoriality -/

/-- **Base change along the identity is the identity**: `K ⊗[K] A ≃ₐ[K] A`. -/
@[simp]
theorem baseChange_self : baseChange K K = MonoidHom.id (BrauerGroup.{u, u} K) := by
  ext x
  induction x using BrauerGroup.inductionOn with
  | h A => exact mk_eq_mk_of_algEquiv (Algebra.TensorProduct.lid K A)

variable (M : Type u) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **Base change composes along a tower** `K → L → M`, by
`TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`. With
`TauCeti.BrauerGroup.baseChange_self` this makes `K ↦ BrauerGroup K` a functor from fields to
abelian groups. -/
theorem baseChange_comp : (baseChange L M).comp (baseChange K L) = baseChange K M := by
  ext x
  induction x using BrauerGroup.inductionOn with
  | h A => exact mk_eq_mk_of_algEquiv (Algebra.TensorProduct.baseChangeTowerAlgEquiv K L A M)

/-- **Base change composes along a tower**, applied to a class. -/
theorem baseChange_baseChange (x : BrauerGroup.{u, u} K) :
    baseChange L M (baseChange K L x) = baseChange K M x :=
  DFunLike.congr_fun (baseChange_comp K L M) x

/-! ### The kernel -/

/-- **A class lies in the kernel of base change to `L` exactly when its algebras become Brauer
trivial over `L`.** -/
theorem mk_mem_ker_baseChange_iff (A : CSA.{u, u} K) :
    mk A ∈ (baseChange K L).ker ↔ IsBrauerTrivial (CSA.baseChange L A) :=
  MonoidHom.mem_ker.trans mk_eq_one_iff

variable {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **An algebra split by `L` has trivial class over `L`.**

This is the half of "the kernel is the classes split by `L`" that the available theory gives: `L`
splitting `A` says `L ⊗[K] A` is a full matrix algebra over `L`, and a full matrix algebra is
Brauer trivial. The converse needs the uniqueness half of Artin-Wedderburn; see the module
docstring. -/
theorem baseChange_mk_eq_one_of_isSplittingField (h : Algebra.IsSplittingField K A L) :
    baseChange K L (mk (CSA.of K A)) = 1 :=
  mk_eq_one_of_isSplittingField ((Algebra.isSplittingField_baseChange_self_iff K A L).2 h)

/-- **An algebra split by `L` has its class in the kernel of base change to `L`.** -/
theorem mk_mem_ker_baseChange_of_isSplittingField (h : Algebra.IsSplittingField K A L) :
    mk (CSA.of K A) ∈ (baseChange K L).ker :=
  MonoidHom.mem_ker.2 (baseChange_mk_eq_one_of_isSplittingField K L h)

/-- **Every Brauer class dies over an algebraically closed extension**, so base change to one is
the trivial homomorphism: an algebraically closed field has trivial Brauer group
(`TauCeti.subsingleton_brauerGroup_of_isAlgClosed`), and there is nowhere else for a class to
go. -/
theorem baseChange_eq_one_of_isAlgClosed [IsAlgClosed L] : baseChange K L = 1 := by
  have := subsingleton_brauerGroup_of_isAlgClosed.{u, u} (K := L)
  ext x
  exact Subsingleton.elim _ _

end BrauerGroup

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- Complexification kills the Brauer class of the real quaternions, because `ℂ` is algebraically
closed and so has trivial Brauer group.

That this is a *nontrivial* class being killed -- that `ℍ[ℝ]` is not already split over `ℝ`, so
that the kernel of `TauCeti.BrauerGroup.baseChange ℝ ℂ` is bigger than `1` -- is a separate matter,
and one this file does not settle: it needs the uniqueness half of Artin-Wedderburn, as does the
expectation `BrauerGroup ℝ ≃ ℤ/2`. -/
example : BrauerGroup.baseChange ℝ ℂ (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])) = 1 := by
  rw [BrauerGroup.baseChange_eq_one_of_isAlgClosed, MonoidHom.one_apply]

/-- The same class, killed through the splitting field rather than through the triviality of
`BrauerGroup ℂ`: `TauCeti.Algebra.isSplittingField_of_isAlgClosed` says `ℂ` splits every
finite-dimensional central simple `ℝ`-algebra, and a split algebra lies in the kernel. -/
example : BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) ∈ (BrauerGroup.baseChange ℝ ℂ).ker :=
  BrauerGroup.mk_mem_ker_baseChange_of_isSplittingField ℝ ℂ
    (Algebra.isSplittingField_of_isAlgClosed ℝ ℍ[ℝ] ℂ)

end Examples

end TauCeti
