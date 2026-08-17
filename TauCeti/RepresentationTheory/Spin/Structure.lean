/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.End
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.SimpleRing.Matrix
public import TauCeti.RepresentationTheory.Spin.Polarization.Exists
public import TauCeti.RepresentationTheory.Spin.Representation
-- Private: `CliffordAlgebra.finrank_eq_two_pow`, `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` and
-- the freeness and finiteness instances they carry are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: `Subspace.dual_finrank_eq` and `Module.forall_dual_apply_eq_zero_iff` are used only
-- inside proofs.
import Mathlib.LinearAlgebra.Dual.Lemmas
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
annihilation operators. This file draws the two conclusions that surjectivity alone supports.

The first needs no hypothesis on the dimension. A surjection onto `Module.End K S` cannot leave a
proper nonzero subspace of `S` invariant, so **`S` is a simple Clifford module**
(`TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_spinAction_invariant`). This is the
irreducibility of the spinor representation of the Clifford algebra, and it is a statement about
the Clifford algebra only: the spin group is smaller, and in even dimension it preserves the
exterior-parity splitting `S = S⁺ ⊕ S⁻` (in `TauCeti/RepresentationTheory/Spin/HalfSpin.lean`), so
no group-level irreducibility follows from this.

The second is the **structure theorem**, and it is a dimension count. Deforming a quadratic form
deforms the multiplication of its Clifford algebra and leaves the size alone, so
`finrank (CliffordAlgebra Q) = 2 ^ finrank V` for every form
(`CliffordAlgebra.finrank_eq_two_pow`), while `finrank (Module.End K S) = (2 ^ finrank W) ^ 2`.
A polarization always has `finrank V = 2 * finrank W + finrank L` with `finrank L ≤ 1`, because the
polar pairing identifies `W'` with the dual of `W` and the coordinate `lineCoordinate` embeds `L`
in the scalar line. So in even dimension `L` vanishes, `finrank W` is exactly half of `finrank V`,
the two dimensions agree, and the surjection `TauCeti.spinAction` is forced to be an isomorphism:

`TauCeti.SpinPolarizationData.cliffordEquivEnd : CliffordAlgebra Q ≃ₐ[K] Module.End K (⋀·W)`,

or, in a basis of `S`, `TauCeti.SpinPolarizationData.cliffordEquivMatrix`, the matrix algebra
`M_{2^l}(K)` for `finrank V = 2 * l`. Since `TauCeti.SpinPolarizationData.ofNondegenerate` builds a
polarization for every finite-dimensional nondegenerate quadratic space over a separably closed
field of characteristic different from two, this specializes to the field-level statement
`CliffordAlgebra.nonempty_algEquiv_matrix_of_even`, and with it the simplicity and the centrality
of the Clifford algebra there — so it is a central simple algebra, split by construction.

The direction of the argument is worth recording, because the reverse is tempting and unavailable:
the spin module is built first and the structure theorem is derived *from* it. Nothing here uses
the structure theorem to prove the spin module simple.

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

* `TauCeti.SpinPolarizationData.finrank_eq_two_mul_finrank_W_add_finrank_line` and
  `TauCeti.SpinPolarizationData.finrank_line_le_one`: the dimension bookkeeping of a polarization,
  with `TauCeti.SpinPolarizationData.line_eq_bot_of_even` and
  `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul` as the even-dimensional readings.
* `TauCeti.SpinPolarizationData.spinAction_bijective`: the Fock action is faithful, hence
  bijective, in even dimension.
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_spinAction_invariant`: the spinor module is a
  simple Clifford module, in every dimension.
* `CliffordAlgebra.nonempty_algEquiv_matrix_of_even`,
  `CliffordAlgebra.isSimpleRing_of_even` and `CliffordAlgebra.isCentral_of_even`: over a separably
  closed field of characteristic different from two, the Clifford algebra of a nondegenerate form
  on an even-dimensional space is a matrix algebra, hence simple with center the base field.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9: the
  Clifford algebra of an even-dimensional space acts on `⋀·W` through the full endomorphism
  algebra, and the dimension count that makes the action an isomorphism.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The even-dimensional case", and Layer 4, "Irreducibility".
-/

public section

open Module QuadraticMap

namespace TauCeti

universe u v

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-! ### The dimensions of the three summands

A polarization is a decomposition `V = W ⊕ W' ⊕ L` in which the polar form pairs `W` with `W'`
perfectly and `L` sits inside the scalar line. The first fact makes the two isotropic summands
equidimensional and the second bounds the remainder by one dimension, so the dimension of `V`
determines the dimension of `W` up to the parity of `finrank V`. -/

/-- **The two isotropic summands of a polarization have the same dimension.** The polar form
identifies the second with the dual of the first, and a space and its dual have the same
dimension. -/
theorem finrank_W'_eq_finrank_W : finrank K P.W' = finrank K P.W := by
  rw [P.pairingEquiv.finrank_eq, Subspace.dual_finrank_eq]

/-- **The orthogonal remainder of a polarization is at most a line.** Its scalar coordinate
`SpinPolarizationData.lineCoordinate` is injective into `K`, which is one-dimensional. -/
theorem finrank_line_le_one : finrank K P.line ≤ 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := P.lineCoordinate)
    P.lineCoordinate_injective
  simpa using h

section Finrank

variable [FiniteDimensional K V]

/-- **The dimension of a polarized quadratic space**: twice the dimension of the isotropic summand
`W`, plus the dimension of the remainder. Together with `finrank_line_le_one` this pins
`finrank W` to `finrank V / 2`. -/
theorem finrank_eq_two_mul_finrank_W_add_finrank_line :
    finrank K V = 2 * finrank K P.W + finrank K P.line := by
  rw [← P.decompositionEquiv.finrank_eq, finrank_prod, finrank_prod, P.finrank_W'_eq_finrank_W]
  ring

/-- **In even dimension a polarization has no remainder.** The remainder is at most a line and
carries the parity of `finrank V`, so an even-dimensional space forces it to vanish. This is the
hypothesis under which the exterior parity of `⋀·W` splits the spin representation, in
`TauCeti/RepresentationTheory/Spin/HalfSpin.lean`. -/
theorem line_eq_bot_of_even (h : Even (finrank K V)) : P.line = ⊥ := by
  obtain ⟨m, hm⟩ := h
  have h₁ := P.finrank_line_le_one
  have h₂ := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- **In even dimension the isotropic summand has half the dimension.** A maximal isotropic
subspace of a `2l`-dimensional quadratic space has dimension `l`, so the spinor module `⋀·W` has
dimension `2 ^ l`. -/
theorem finrank_W_of_finrank_eq_two_mul {l : ℕ} (hV : finrank K V = 2 * l) :
    finrank K P.W = l := by
  have h₁ := P.finrank_line_le_one
  have h₂ := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  omega

end Finrank

/-! ### The spinor module is a simple Clifford module

Surjectivity of the Fock action is already enough: a subspace invariant under every endomorphism
of `S` is `⊥` or `⊤`. No hypothesis on the dimension of `V`, on nondegeneracy, or on the remainder
`L` enters, so this covers the odd-dimensional case as well, where the action has a kernel. -/

/-- **The spinor module is a simple Clifford module.** A submodule of `S = ⋀·W` carried into
itself by the Fock action of every Clifford element is `⊥` or `⊤`: this is the irreducibility of
the spinor representation of `CliffordAlgebra Q`.

It is *not* irreducibility of the spin representation of the group. The spin group is much smaller
than the Clifford algebra, and in even dimension the half-spin summands `TauCeti.spinPlus` and
`TauCeti.spinMinus` are invariant under `TauCeti.spinRep`, so `S` splits as a representation of the
group as soon as both summands are nonzero. What fails for them here is the invariance hypothesis:
an odd Clifford element exchanges the two summands. -/
theorem eq_bot_or_eq_top_of_spinAction_invariant [Module.Free K P.W] [Module.Finite K P.W]
    {N : Submodule K (ExteriorAlgebra K P.W)}
    (hN : ∀ (x : CliffordAlgebra Q) (s : ExteriorAlgebra K P.W), s ∈ N → spinAction Q P x s ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  rcases eq_or_ne N ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (eq_top_iff.2 fun t _ ↦ ?_)
  obtain ⟨s, hsN, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K (ExteriorAlgebra K P.W), ψ s ≠ 0 := by
    by_contra hcon
    exact hs ((Module.forall_dual_apply_eq_zero_iff K s).1 (by simpa using hcon))
  obtain ⟨x, hx⟩ := spinAction_surjective P
    (LinearMap.toSpanSingleton K (ExteriorAlgebra K P.W) ((ψ s)⁻¹ • t) ∘ₗ ψ)
  have hmem := hN x s hsN
  rw [hx] at hmem
  simpa [LinearMap.toSpanSingleton_apply, smul_smul, mul_inv_cancel₀ hψ] using hmem

/-! ### The structure theorem in even dimension

The count is `finrank (CliffordAlgebra Q) = 2 ^ finrank V = 2 ^ (2 * l) = (2 ^ l) ^ 2 =
finrank (Module.End K S)`, where the outer two equalities hold for every quadratic form on a
finite free module and the inner one is the even-dimensional reading of the summand dimensions
above. Injectivity of the Fock action is then forced by its surjectivity. Two is inverted
throughout, as it already is in the dimension count `CliffordAlgebra.finrank_eq_two_pow`. -/

section Structure

variable [Invertible (2 : K)] [FiniteDimensional K V]

/-- **The Clifford algebra and the operator algebra of the spinor module have equal dimension** in
even dimension: `2 ^ (2 * l)` on the left, `(2 ^ l) ^ 2` on the right. This is the whole content of
the structure theorem; everything else is linear algebra. -/
theorem finrank_cliffordAlgebra_eq_finrank_end (h : Even (finrank K V)) :
    finrank K (CliffordAlgebra Q) = finrank K (Module.End K (ExteriorAlgebra K P.W)) := by
  obtain ⟨l, hl⟩ := h
  have hW : finrank K P.W = l := P.finrank_W_of_finrank_eq_two_mul (by omega)
  have hEnd : finrank K (Module.End K (ExteriorAlgebra K P.W)) =
      finrank K (ExteriorAlgebra K P.W) * finrank K (ExteriorAlgebra K P.W) :=
    Module.finrank_linearMap K K (ExteriorAlgebra K P.W) (ExteriorAlgebra K P.W)
  rw [hEnd, CliffordAlgebra.finrank_eq_two_pow, TauCeti.ExteriorAlgebra.finrank_eq_two_pow, hW, hl,
    pow_add]

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
  ⟨P.spinAction_injective h, spinAction_surjective P⟩

/-- **The structure theorem in operator form**: for an even-dimensional polarized quadratic space,
the Fock action is an isomorphism of `K`-algebras from `CliffordAlgebra Q` onto the endomorphism
algebra of the spinor module `S = ⋀·W`. -/
noncomputable def cliffordEquivEnd (h : Even (finrank K V)) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  AlgEquiv.ofBijective (spinAction Q P) (P.spinAction_bijective h)

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
  (P.cliffordEquivEnd ⟨l, by omega⟩).trans
    (algEquivMatrix (Module.finBasisOfFinrankEq K (ExteriorAlgebra K P.W)
      (by rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, P.finrank_W_of_finrank_eq_two_mul hV])))

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
theorem nonempty_algEquiv_matrix_of_even {l : ℕ} (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * l) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact ⟨(SpinPolarizationData.ofNondegenerate Q hQ).cliffordEquivMatrix hV⟩

/-- **An even-dimensional Clifford algebra over a separably closed field is a simple ring**, being
a matrix algebra over a field. -/
theorem isSimpleRing_of_even (hQ : Q.Nondegenerate) (hV : Even (finrank F V)) :
    IsSimpleRing (CliffordAlgebra Q) := by
  obtain ⟨l, hl⟩ := hV
  obtain ⟨e⟩ := nonempty_algEquiv_matrix_of_even (l := l) hQ (by omega)
  have : Nonempty (Fin (2 ^ l)) := ⟨⟨0, Nat.two_pow_pos l⟩⟩
  exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance

/-- **An even-dimensional Clifford algebra over a separably closed field has center the base
field**: it is the endomorphism algebra of the spinor module, whose center is the scalars. With
`CliffordAlgebra.isSimpleRing_of_even` this makes it a central simple algebra over `F`, split by
construction. -/
theorem isCentral_of_even (hQ : Q.Nondegenerate) (hV : Even (finrank F V)) :
    Algebra.IsCentral F (CliffordAlgebra Q) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact Algebra.IsCentral.of_algEquiv F _ _
    ((SpinPolarizationData.ofNondegenerate Q hQ).cliffordEquivEnd hV).symm

end CliffordAlgebra
