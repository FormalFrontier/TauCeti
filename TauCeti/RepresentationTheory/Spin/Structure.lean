/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.End
public import TauCeti.LinearAlgebra.Matrix.ToLin
public import TauCeti.RepresentationTheory.Spin.Polarization.Exists
public import TauCeti.RepresentationTheory.Spin.Representation
-- Private: `CliffordAlgebra.finrank_eq_two_pow`, `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` and
-- the freeness and finiteness instances they carry are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` is used only inside a proof.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- Private: `IsSimpleRing.of_ringEquiv` is used only inside a proof.
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# The structure theorem for an even-dimensional Clifford algebra

A polarization of a quadratic space `(V, Q)` splits it as `W ⊕ W' ⊕ L` and makes the exterior
algebra `S = ⋀·W` a module over `CliffordAlgebra Q` — the Fock model `TauCeti.spinAction`. That
action is always *onto* `Module.End K S` when `W` is finite free
(`TauCeti.spinAction_surjective`): every endomorphism of `S` is a polynomial in the creation and
annihilation operators.

This file proves the **structure theorem**, which is a dimension count. Deforming a quadratic form
deforms the multiplication of its Clifford algebra and leaves the size alone, so
`finrank (CliffordAlgebra Q) = 2 ^ finrank V` for every form
(`CliffordAlgebra.finrank_eq_two_pow`), while `finrank (Module.End K S) = (2 ^ finrank W) ^ 2`.
The dimension bookkeeping for a polarization, in
`TauCeti/RepresentationTheory/Spin/Polarization/Basic.lean`, shows that in even dimension
`finrank W` is exactly half of `finrank V`. The two dimensions therefore agree, and the surjection
`TauCeti.spinAction` is forced to be an isomorphism:

`TauCeti.SpinPolarizationData.cliffordEquivEnd : CliffordAlgebra Q ≃ₐ[K] Module.End K (⋀·W)`,

or, in a basis of `S`, `TauCeti.SpinPolarizationData.cliffordEquivMatrix`, the matrix algebra
`M_{2^l}(K)` for `finrank V = 2 * l`. Since `TauCeti.SpinPolarizationData.ofNondegenerate` builds a
polarization for every finite-dimensional nondegenerate quadratic space over a separably closed
field of characteristic different from two, this specializes to the field-level statement
`CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul`, and with it the simplicity and
the centrality of the Clifford algebra there — so it is a central simple algebra, split by
construction.

The direction of the argument is worth recording: the spin module is built first and the structure
theorem is derived *from* it.

The odd-dimensional case is not proved here. There `finrank L = 1`, the count gives
`finrank (CliffordAlgebra Q) = 2 * (2 ^ l) ^ 2`, and `TauCeti.spinAction` has a kernel: the
Clifford algebra is a product of two matrix algebras and the action factors through one central
idempotent. Identifying that splitting is separate work.

## Main definitions

* `TauCeti.SpinPolarizationData.cliffordEquivEnd`: the structure theorem in operator form, the
  Fock action promoted to an algebra isomorphism onto `Module.End K (⋀·W)`.
* `TauCeti.SpinPolarizationData.cliffordEquivMatrix`: the same isomorphism read in a basis of the
  spinor module, onto `Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) K`.

## Main results

* `TauCeti.spinAction_bijective`: the Fock action is faithful, hence
  bijective, in even dimension.
* `CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul`,
  `CliffordAlgebra.isSimpleRing_of_even_finrank` and
  `CliffordAlgebra.isCentral_of_even_finrank`: over a separably closed field of characteristic
  different from two, the Clifford algebra of a nondegenerate form on an even-dimensional space is
  a matrix algebra, hence simple with center the base field.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9: the
  Clifford algebra of an even-dimensional space acts on `⋀·W` through the full endomorphism
  algebra, and the dimension count that makes the action an isomorphism.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The even-dimensional case".
-/

public section

open Module QuadraticMap

namespace TauCeti

universe u v

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-! ### The structure theorem in even dimension

The count is `finrank (CliffordAlgebra Q) = 2 ^ finrank V = 2 ^ (2 * l) = (2 ^ l) ^ 2 =
finrank (Module.End K S)`, where the outer two equalities hold for every quadratic form on a
finite free module and the inner one is the even-dimensional reading of the summand dimensions
above. Injectivity of the Fock action is then forced by its surjectivity. Two is inverted
throughout, as it already is in the dimension count `CliffordAlgebra.finrank_eq_two_pow`. -/

section Structure

variable [Invertible (2 : K)] [FiniteDimensional K V]

omit [Invertible (2 : K)] in
/-- **The spinor module has dimension `2 ^ l`** when the polarized quadratic space has dimension
`2 * l`. -/
theorem finrank_exteriorAlgebra_W_of_finrank_eq_two_mul {l : ℕ}
    (hV : finrank K V = 2 * l) : finrank K (ExteriorAlgebra K P.W) = 2 ^ l := by
  rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, P.finrank_W_of_finrank_eq_two_mul hV]

/-- **The Clifford algebra and the operator algebra of the spinor module have equal dimension** in
even dimension: `2 ^ (2 * l)` on the left, `(2 ^ l) ^ 2` on the right. This is the dimension count
that upgrades the surjection `spinAction_surjective` to an isomorphism. -/
theorem finrank_cliffordAlgebra_eq_finrank_end (h : Even (finrank K V)) :
    finrank K (CliffordAlgebra Q) = finrank K (Module.End K (ExteriorAlgebra K P.W)) := by
  obtain ⟨l, hl⟩ := h
  have hS : finrank K (ExteriorAlgebra K P.W) = 2 ^ l :=
    P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul (by omega)
  have hEnd : finrank K (Module.End K (ExteriorAlgebra K P.W)) =
      finrank K (ExteriorAlgebra K P.W) * finrank K (ExteriorAlgebra K P.W) :=
    Module.finrank_linearMap K K (ExteriorAlgebra K P.W) (ExteriorAlgebra K P.W)
  rw [hEnd, CliffordAlgebra.finrank_eq_two_pow, hS, hl, pow_add]

end Structure

end SpinPolarizationData

section Structure

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

/-- **The Fock action is faithful in even dimension.** It is surjective onto an algebra of the same
dimension, so it is injective. -/
theorem spinAction_injective (h : Even (finrank K V)) :
    Function.Injective (spinAction Q P) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (spinAction Q P).toLinearMap)
    (P.finrank_cliffordAlgebra_eq_finrank_end h)).2 (spinAction_surjective P)

/-- **The Fock action is bijective in even dimension**: surjective for every polarization with a
finite free isotropic summand, and injective by the dimension count. -/
theorem spinAction_bijective (h : Even (finrank K V)) :
    Function.Bijective (spinAction Q P) :=
  ⟨spinAction_injective P h, spinAction_surjective P⟩

end Structure

namespace SpinPolarizationData

section Structure

private theorem even_of_eq_two_mul {n l : ℕ} (h : n = 2 * l) : Even n := ⟨l, by omega⟩

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

local instance : Module.Finite K (ExteriorAlgebra K P.W) :=
  TauCeti.ExteriorAlgebra.instFinite

/-- **The structure theorem in operator form**: for an even-dimensional polarized quadratic space,
the Fock action is an isomorphism of `K`-algebras from `CliffordAlgebra Q` onto the endomorphism
algebra of the spinor module `S = ⋀·W`. -/
noncomputable def cliffordEquivEnd (h : Even (finrank K V)) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  AlgEquiv.ofBijective (spinAction Q P) (spinAction_bijective P h)

@[simp]
theorem cliffordEquivEnd_apply (h : Even (finrank K V)) (x : CliffordAlgebra Q) :
    P.cliffordEquivEnd h x = spinAction Q P x :=
  -- `(rfl)`, not `rfl`: the body of `cliffordEquivEnd` is not `@[expose]`d.
  (rfl)

/-- **The structure theorem**: the Clifford algebra of a polarized quadratic space of dimension
`2 * l` is the matrix algebra `M_{2^l}(K)`, read in a basis of the spinor module `⋀·W`, which has
dimension `2 ^ l`. -/
noncomputable def cliffordEquivMatrix {l : ℕ} (hV : finrank K V = 2 * l) :
    CliffordAlgebra Q ≃ₐ[K] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) K :=
  (P.cliffordEquivEnd (even_of_eq_two_mul hV)).trans
    (Algebra.endAlgEquivMatrix K (ExteriorAlgebra K P.W)
      (P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul hV))

/-- The matrix form of the structure theorem is the Fock action followed by the chosen-basis
identification of endomorphisms with matrices. -/
@[simp]
theorem cliffordEquivMatrix_apply {l : ℕ} (hV : finrank K V = 2 * l)
    (x : CliffordAlgebra Q) :
    P.cliffordEquivMatrix hV x =
      Algebra.endAlgEquivMatrix K (ExteriorAlgebra K P.W)
        (P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul hV) (spinAction Q P x) := by
  rw [cliffordEquivMatrix, AlgEquiv.trans_apply,
    P.cliffordEquivEnd_apply (even_of_eq_two_mul hV)]

/-- **An even-dimensional polarized Clifford algebra is a simple ring.** The Fock action identifies
it with the endomorphism algebra of its nonzero finite-dimensional spinor module. -/
theorem isSimpleRing (P : SpinPolarizationData Q) (h : Even (finrank K V)) :
    IsSimpleRing (CliffordAlgebra Q) :=
  IsSimpleRing.of_ringEquiv (cliffordEquivEnd P h).symm.toRingEquiv inferInstance

/-- **An even-dimensional polarized Clifford algebra has center the base field.** The Fock action
identifies it with the endomorphism algebra of its spinor module. -/
theorem isCentral (P : SpinPolarizationData Q) (h : Even (finrank K V)) :
    Algebra.IsCentral K (CliffordAlgebra Q) :=
  Algebra.IsCentral.of_algEquiv K _ _ (cliffordEquivEnd P h).symm

end Structure

end SpinPolarizationData

end TauCeti

/-! ### The field-level structure theorem

A finite-dimensional nondegenerate quadratic space over a separably closed field of characteristic
different from two is polarized by `TauCeti.SpinPolarizationData.ofNondegenerate`, so in even
dimension the statements above become statements about the Clifford algebra alone. -/

namespace CliffordAlgebra

open TauCeti

universe u v

variable {F : Type u} [Field F] [NeZero (2 : F)] [IsSepClosed F]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- **The structure theorem over a separably closed field**: the Clifford algebra of a
nondegenerate quadratic form on a `2l`-dimensional space is the matrix algebra `M_{2^l}(F)`.

The isomorphism is not canonical — it is read in a basis of the spinor module of a polarization,
and neither the polarization nor the basis is unique — so the statement is `Nonempty`. The
polarization-dependent isomorphism itself is
`TauCeti.SpinPolarizationData.cliffordEquivMatrix`. -/
theorem nonempty_algEquiv_matrix_of_finrank_eq_two_mul {l : ℕ} (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * l) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact ⟨(SpinPolarizationData.ofNondegenerate Q hQ).cliffordEquivMatrix hV⟩

/-- **The Clifford algebra of a nondegenerate quadratic form on an even-dimensional space over a
separably closed field is a simple ring**, being the endomorphism algebra of its spinor module. -/
theorem isSimpleRing_of_even_finrank (hQ : Q.Nondegenerate) (hV : Even (finrank F V)) :
    IsSimpleRing (CliffordAlgebra Q) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact SpinPolarizationData.isSimpleRing (SpinPolarizationData.ofNondegenerate Q hQ) hV

/-- **The Clifford algebra of a nondegenerate quadratic form on an even-dimensional space over a
separably closed field has center the base field**: it is the endomorphism algebra of the spinor
module, whose center is the scalars. With `CliffordAlgebra.isSimpleRing_of_even_finrank` this makes
it a central simple algebra over `F`, split by construction. -/
theorem isCentral_of_even_finrank (hQ : Q.Nondegenerate) (hV : Even (finrank F V)) :
    Algebra.IsCentral F (CliffordAlgebra Q) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact SpinPolarizationData.isCentral (SpinPolarizationData.ofNondegenerate Q hQ) hV

end CliffordAlgebra
