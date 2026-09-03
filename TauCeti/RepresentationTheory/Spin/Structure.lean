/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.End
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.Matrix.ToLin
public import TauCeti.RepresentationTheory.Spin.Polarization.Exists
public import TauCeti.RepresentationTheory.Spin.Dimension
-- Private: `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` is used only inside a proof.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- Private: `LinearMap.ofIsCompl` and its evaluation lemmas are used only inside proofs.
import Mathlib.LinearAlgebra.Projection
-- Private: `IsSimpleRing.of_ringEquiv` is used only inside a proof.
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# The structure theorem for an even-dimensional Clifford algebra

A polarization of a quadratic space `(V, Q)` splits it as `W ⊕ W' ⊕ L` and makes the exterior
algebra `S = ⋀·W` a module over `CliffordAlgebra Q` — the Fock model `TauCeti.spinAction`. That
action is *onto* `Module.End K S` when `W` is finite free (`TauCeti.spinAction_surjective`): every
endomorphism of `S` is a polynomial in the creation and annihilation operators.

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
`CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul`.

The direction of the argument is worth recording: the spin module is built first and the structure
theorem is derived *from* it.

The same action identifies the even Clifford subalgebra with the product of the endomorphism
algebras of the exterior-parity summands `S⁺` and `S⁻`. Surjectivity onto that product is the
substance: an endomorphism preserving both summands comes from a unique Clifford element, and its
odd component must vanish because it both preserves and reverses parity.

The odd-dimensional case is not proved here. There `finrank L = 1` and the count gives
`finrank (CliffordAlgebra Q) = 2 * (2 ^ l) ^ 2`, so `TauCeti.spinAction` cannot be injective. Away
from characteristic two the centre of the Clifford algebra of a nondegenerate odd-dimensional form
is a quadratic étale algebra over `K`, so over a separably closed field it is `K × K`, the Clifford
algebra is a product of two matrix algebras, and the action factors through one of the two central
idempotents. Over a general field that centre can be a field, and then there is no such product
decomposition. The idempotent half of that splitting is proved in
`TauCeti/LinearAlgebra/CliffordAlgebra/OddSplitting.lean`: `CliffordAlgebra.equivEvenProd` splits
the Clifford algebra of a central odd square root of one as two copies of its even subalgebra, and
`CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed` supplies that square root over a
separably closed field. What is still separate work is identifying `even Q` for an odd-dimensional
form with a matrix algebra, which is what would turn that product into the product of two matrix
algebras.

## Main definitions

* `TauCeti.SpinPolarizationData.cliffordEquivEnd`: the structure theorem in operator form, the
  Fock action promoted to an algebra isomorphism onto `Module.End K (⋀·W)`.
* `TauCeti.SpinPolarizationData.cliffordEquivMatrix`: the same isomorphism read in a basis of the
  spinor module, onto `Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) K`.
* `TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`: the even structure theorem in operator
  form, onto the product of the endomorphism algebras of `S⁺` and `S⁻`.
* `TauCeti.SpinPolarizationData.evenCliffordEquivProdMatrix`: its product-of-matrix-algebras form.

## Main results

* `TauCeti.spinAction_bijective`: the Fock action is faithful, hence
  bijective, in even dimension.
* `TauCeti.evenSpinActionProd_surjective`: the even Clifford action exhausts the paired
  endomorphism algebras of the half-spin summands.
* `CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul`: the matrix-algebra equivalence
  over a separably closed field.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9 and
  Proposition 20.15: the
  Clifford algebra of an even-dimensional space acts on `⋀·W` through the full endomorphism
  algebra, the dimension count that makes the action an isomorphism, and the product decomposition
  of the even subalgebra on the two half-spin summands.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The even-dimensional case".
-/

public section

open CliffordAlgebra Module QuadraticMap

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

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

/-- **The structure theorem in operator form**: for an even-dimensional polarized quadratic space,
the Fock action is an isomorphism of `K`-algebras from `CliffordAlgebra Q` onto the endomorphism
algebra of the spinor module `S = ⋀·W`. -/
noncomputable def cliffordEquivEnd (h : Even (finrank K V)) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  AlgEquiv.ofBijective (spinAction Q P) (spinAction_bijective P h)

/-- The operator form of the structure theorem is the Fock action itself. -/
@[simp]
theorem cliffordEquivEnd_apply (h : Even (finrank K V)) (x : CliffordAlgebra Q) :
    P.cliffordEquivEnd h x = spinAction Q P x := by
  rw [cliffordEquivEnd]
  exact congrFun (AlgEquiv.coe_ofBijective _ _) x

/-- **The structure theorem**: the Clifford algebra of a polarized quadratic space of dimension
`2 * l` is the matrix algebra `M_{2^l}(K)`, read in a basis of the spinor module `⋀·W`, which has
dimension `2 ^ l`. -/
noncomputable def cliffordEquivMatrix {l : ℕ} (hV : finrank K V = 2 * l) :
    CliffordAlgebra Q ≃ₐ[K] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) K :=
  (P.cliffordEquivEnd (hV ▸ even_two_mul l)).trans
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
    P.cliffordEquivEnd_apply (hV ▸ even_two_mul l)]

/-- **An even-dimensional polarized Clifford algebra is a simple ring.** The Fock action identifies
it with the endomorphism algebra of its nonzero finite-dimensional spinor module. -/
theorem isSimpleRing_cliffordAlgebra (P : SpinPolarizationData Q) (h : Even (finrank K V)) :
    IsSimpleRing (CliffordAlgebra Q) :=
  IsSimpleRing.of_ringEquiv (cliffordEquivEnd P h).symm.toRingEquiv inferInstance

/-- **An even-dimensional polarized Clifford algebra has center the base field.** The Fock action
identifies it with the endomorphism algebra of its spinor module. -/
theorem isCentral_cliffordAlgebra (P : SpinPolarizationData Q) (h : Even (finrank K V)) :
    Algebra.IsCentral K (CliffordAlgebra Q) :=
  Algebra.IsCentral.of_algEquiv K _ _ (cliffordEquivEnd P h).symm

end Structure

end SpinPolarizationData

/-! ### The even structure theorem

For an even-dimensional polarized quadratic space the Fock action is an isomorphism
`CliffordAlgebra Q ≃ₐ[K] Module.End K S`. Under it the even subalgebra is carried onto the
endomorphisms preserving the parity splitting `S = S⁺ ⊕ S⁻`, which is the product of the two
endomorphism algebras; that is the content of this section. -/

section EvenStructure

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
private theorem spinAction_eq_zero_on_of_maps_le
    (M N : Submodule K (ExteriorAlgebra K P.W)) (hMN : Disjoint M N)
    {x₀ x₁ : CliffordAlgebra Q} (heven : M.map (spinAction Q P x₀) ≤ M)
    (hodd : M.map (spinAction Q P x₁) ≤ N)
    (hmap : M.map (spinAction Q P (x₀ + x₁)) ≤ M) :
    Set.EqOn (spinAction Q P x₁) 0 M := by
  intro s hs
  have hN : spinAction Q P x₁ s ∈ N := hodd ⟨s, hs, rfl⟩
  have hM : spinAction Q P x₁ s ∈ M := by
    rw [map_add] at hmap
    have hadd := hmap ⟨s, hs, rfl⟩
    rw [LinearMap.add_apply] at hadd
    simpa only [add_sub_cancel_left] using M.sub_mem hadd (heven ⟨s, hs, rfl⟩)
  have : spinAction Q P x₁ s ∈ (⊥ : Submodule K (ExteriorAlgebra K P.W)) := by
    rw [← disjoint_iff.1 hMN]
    exact ⟨hM, hN⟩
  simpa using this

/-- **A Clifford element whose action preserves both half-spin summands is even.** Splitting it
into an even and an odd part, the odd part acts by an operator that both preserves and reverses
exterior parity, so it acts by zero; in even dimension the Fock action is faithful, so the odd part
itself vanishes. -/
theorem mem_even_of_map_spinPlus_le_of_map_spinMinus_le (hline : P.line = ⊥)
    {x : CliffordAlgebra Q}
    (hplus : (spinPlus Q P).map (spinAction Q P x) ≤ spinPlus Q P)
    (hminus : (spinMinus Q P).map (spinAction Q P x) ≤ spinMinus Q P) :
    x ∈ CliffordAlgebra.even Q := by
  have hxsplit : x ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
    rw [codisjoint_iff.1 (CliffordAlgebra.evenOdd_isCompl (Q := Q)).codisjoint]
    trivial
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.1 hxsplit
  have hx₀even : x₀ ∈ CliffordAlgebra.even Q := by
    rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
    exact hx₀
  -- The odd part acts by zero on each summand, so by zero.
  have hzeroplus : Set.EqOn (spinAction Q P x₁) 0 (spinPlus Q P) :=
    spinAction_eq_zero_on_of_maps_le P (spinPlus Q P) (spinMinus Q P)
      (isCompl_spinPlus_spinMinus P).disjoint
      (by rintro _ ⟨s, hs, rfl⟩; rw [spinPlus_def] at hs ⊢
          exact spinAction_mem_evenOdd_of_mem_even P hline hx₀even hs)
      (map_spinAction_spinPlus_le_spinMinus P hline hx₁) hplus
  have hzerominus : Set.EqOn (spinAction Q P x₁) 0 (spinMinus Q P) :=
    spinAction_eq_zero_on_of_maps_le P (spinMinus Q P) (spinPlus Q P)
      (isCompl_spinPlus_spinMinus P).symm.disjoint
      (by rintro _ ⟨s, hs, rfl⟩; rw [spinMinus_def] at hs ⊢
          exact spinAction_mem_evenOdd_of_mem_even P hline hx₀even hs)
      (map_spinAction_spinMinus_le_spinPlus P hline hx₁) hminus
  have hzero : spinAction Q P x₁ = 0 :=
    LinearMap.ext_on_codisjoint (isCompl_spinPlus_spinMinus P).codisjoint
      hzeroplus hzerominus
  have hx₁zero : x₁ = 0 :=
    spinAction_injective P (P.even_finrank_of_line_eq_bot hline) (by rw [hzero, map_zero])
  rw [hx₁zero, add_zero]
  exact hx₀even

/-- **An endomorphism of the spinor module preserving both half-spin summands is the action of an
even Clifford element.** -/
theorem exists_mem_even_spinAction_eq (hline : P.line = ⊥)
    (f : Module.End K (ExteriorAlgebra K P.W))
    (hplus : (spinPlus Q P).map f ≤ spinPlus Q P)
    (hminus : (spinMinus Q P).map f ≤ spinMinus Q P) :
    ∃ x : CliffordAlgebra.even Q, spinAction Q P x = f := by
  obtain ⟨y, rfl⟩ := spinAction_surjective P f
  exact ⟨⟨y, mem_even_of_map_spinPlus_le_of_map_spinMinus_le P hline hplus hminus⟩, rfl⟩

/-- **The even subalgebra acts faithfully on the pair of half-spin summands.** An even element
acting by zero on both acts by zero on their sum, which is all of `S`, and in even dimension the
Fock action is faithful. -/
theorem evenSpinActionProd_injective (hline : P.line = ⊥) :
    Function.Injective (evenSpinActionProd Q P hline) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  rw [evenSpinActionProd_apply, Prod.mk_eq_zero] at hx
  have hzeroplus : Set.EqOn (spinAction Q P x) 0 (spinPlus Q P) := by
    intro s hs
    have := congrArg
      (fun g : Module.End K (spinPlus Q P) => (g ⟨s, hs⟩ : ExteriorAlgebra K P.W)) hx.1
    simpa using this
  have hzerominus : Set.EqOn (spinAction Q P x) 0 (spinMinus Q P) := by
    intro s hs
    have := congrArg
      (fun g : Module.End K (spinMinus Q P) => (g ⟨s, hs⟩ : ExteriorAlgebra K P.W)) hx.2
    simpa using this
  have hzero : spinAction Q P x = 0 :=
    LinearMap.ext_on_codisjoint (isCompl_spinPlus_spinMinus P).codisjoint
      hzeroplus hzerominus
  exact Subtype.ext
    (spinAction_injective P (P.even_finrank_of_line_eq_bot hline) (by simp [hzero]))

/-- **The even subalgebra exhausts the pair of endomorphism algebras.** A pair of endomorphisms of
the two summands assembles, along the splitting `S = S⁺ ⊕ S⁻`, into a parity-preserving
endomorphism of `S`, and those are exactly the actions of even Clifford elements. -/
theorem evenSpinActionProd_surjective (hline : P.line = ⊥) :
    Function.Surjective (evenSpinActionProd Q P hline) := by
  rintro ⟨g₁, g₂⟩
  have hc := isCompl_spinPlus_spinMinus P
  set f : Module.End K (ExteriorAlgebra K P.W) :=
    LinearMap.ofIsCompl hc ((spinPlus Q P).subtype ∘ₗ g₁) ((spinMinus Q P).subtype ∘ₗ g₂)
    with hfdef
  have hfplus : ∀ (s : ExteriorAlgebra K P.W) (hs : s ∈ spinPlus Q P),
      f s = (g₁ ⟨s, hs⟩ : ExteriorAlgebra K P.W) := by
    intro s hs
    rw [hfdef]
    exact LinearMap.ofIsCompl_apply_left hc ⟨s, hs⟩
  have hfminus : ∀ (s : ExteriorAlgebra K P.W) (hs : s ∈ spinMinus Q P),
      f s = (g₂ ⟨s, hs⟩ : ExteriorAlgebra K P.W) := by
    intro s hs
    rw [hfdef]
    exact LinearMap.ofIsCompl_apply_right hc ⟨s, hs⟩
  obtain ⟨x, hx⟩ := exists_mem_even_spinAction_eq P hline f
    (by rintro _ ⟨s, hs, rfl⟩; rw [hfplus s hs]; exact (g₁ ⟨s, hs⟩).2)
    (by rintro _ ⟨s, hs, rfl⟩; rw [hfminus s hs]; exact (g₂ ⟨s, hs⟩).2)
  refine ⟨x, ?_⟩
  rw [evenSpinActionProd_apply, Prod.mk.injEq]
  constructor
  · refine LinearMap.ext fun s => Subtype.ext ?_
    rw [coe_spinPlusAction_apply, hx, hfplus s s.2]
  · refine LinearMap.ext fun s => Subtype.ext ?_
    rw [coe_spinMinusAction_apply, hx, hfminus s s.2]

/-- The even Clifford action on `S⁺` is onto its full endomorphism algebra. -/
theorem spinPlusAction_surjective (hline : P.line = ⊥) :
    Function.Surjective (spinPlusAction Q P hline) := by
  intro g
  obtain ⟨x, hx⟩ := Prod.fst_surjective.comp (evenSpinActionProd_surjective P hline) g
  exact ⟨x, by simpa only [Function.comp_apply, evenSpinActionProd_apply] using hx⟩

/-- The even Clifford action on `S⁻` is onto its full endomorphism algebra. -/
theorem spinMinusAction_surjective (hline : P.line = ⊥) :
    Function.Surjective (spinMinusAction Q P hline) := by
  intro g
  obtain ⟨x, hx⟩ := Prod.snd_surjective.comp (evenSpinActionProd_surjective P hline) g
  exact ⟨x, by simpa only [Function.comp_apply, evenSpinActionProd_apply] using hx⟩

/-- **The even structure theorem**: for an even-dimensional polarized quadratic space the even
Clifford subalgebra is the product of the endomorphism algebras of the two half-spin summands.

This is the even-subalgebra companion of `TauCeti.SpinPolarizationData.cliffordEquivEnd`. It gives
the invariant-subspace dichotomy for both summands, which is simplicity for `S⁺` and, when
`P.W ≠ ⊥`, for `S⁻`; it also distinguishes their two even-Clifford actions. -/
noncomputable def SpinPolarizationData.evenCliffordEquivProdEnd (hline : P.line = ⊥) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K (spinPlus Q P) × Module.End K (spinMinus Q P) :=
  AlgEquiv.ofBijective (evenSpinActionProd Q P hline)
    ⟨evenSpinActionProd_injective P hline, evenSpinActionProd_surjective P hline⟩

@[simp]
theorem SpinPolarizationData.evenCliffordEquivProdEnd_apply (hline : P.line = ⊥)
    (x : CliffordAlgebra.even Q) :
    P.evenCliffordEquivProdEnd hline x = evenSpinActionProd Q P hline x := by
  rw [evenCliffordEquivProdEnd]
  exact congrFun (AlgEquiv.coe_ofBijective _ _) x

/-- **The matrix form of the even structure theorem**: in dimension `2 * l`, the even Clifford
subalgebra is a product of two matrix algebras of size `2 ^ (l - 1)`. -/
noncomputable def SpinPolarizationData.evenCliffordEquivProdMatrix {l : ℕ}
    (hW : P.W ≠ ⊥) (hV : finrank K V = 2 * l) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Matrix (Fin (2 ^ (l - 1))) (Fin (2 ^ (l - 1))) K ×
        Matrix (Fin (2 ^ (l - 1))) (Fin (2 ^ (l - 1))) K := by
  have hline := P.line_eq_bot_of_even_finrank (hV ▸ even_two_mul l)
  have hWfin := P.finrank_W_of_finrank_eq_two_mul hV
  have hplus : finrank K (spinPlus Q P) = 2 ^ (l - 1) := by
    rw [finrank_spinPlus P hW, hWfin]
  have hminus : finrank K (spinMinus Q P) = 2 ^ (l - 1) := by
    rw [finrank_spinMinus P hW, hWfin]
  exact (P.evenCliffordEquivProdEnd hline).trans
    ((Algebra.endAlgEquivMatrix K _ hplus).prodCongr
      (Algebra.endAlgEquivMatrix K _ hminus))

/-- The matrix form of the even structure theorem is the pair of half-spin actions, followed by
the chosen-basis identifications of their endomorphism algebras with matrix algebras. -/
@[simp]
theorem SpinPolarizationData.evenCliffordEquivProdMatrix_apply {l : ℕ}
    (hW : P.W ≠ ⊥) (hV : finrank K V = 2 * l) (x : CliffordAlgebra.even Q) :
    P.evenCliffordEquivProdMatrix hW hV x =
      (Algebra.endAlgEquivMatrix K (spinPlus Q P)
          (by rw [finrank_spinPlus P hW, P.finrank_W_of_finrank_eq_two_mul hV])
          (spinPlusAction Q P (P.line_eq_bot_of_even_finrank (hV ▸ even_two_mul l)) x),
        Algebra.endAlgEquivMatrix K (spinMinus Q P)
          (by rw [finrank_spinMinus P hW, P.finrank_W_of_finrank_eq_two_mul hV])
          (spinMinusAction Q P (P.line_eq_bot_of_even_finrank (hV ▸ even_two_mul l)) x)) := by
  simp [evenCliffordEquivProdMatrix]

end EvenStructure

end TauCeti

/-! ### The field-level structure theorem

A finite-dimensional nondegenerate quadratic space over a separably closed field of characteristic
different from two is polarized by `TauCeti.SpinPolarizationData.ofNondegenerate`, giving the split
matrix-algebra statement. -/

namespace CliffordAlgebra

open TauCeti

universe u v

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- **The structure theorem over a separably closed field**: the Clifford algebra of a
nondegenerate quadratic form on a `2l`-dimensional space is the matrix algebra `M_{2^l}(F)`.

The isomorphism is not canonical — it is read in a basis of the spinor module of a polarization,
and neither the polarization nor the basis is unique — so the statement is `Nonempty`. The
polarization-dependent isomorphism itself is
`TauCeti.SpinPolarizationData.cliffordEquivMatrix`. -/
theorem nonempty_algEquiv_matrix_of_finrank_eq_two_mul [IsSepClosed F] {l : ℕ}
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * l) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact ⟨(SpinPolarizationData.ofNondegenerate Q hQ).cliffordEquivMatrix hV⟩

end CliffordAlgebra
