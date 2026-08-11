/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Data.Sym.Basic
public import TauCeti.LinearAlgebra.SymmetricPower.Lift

/-!
# A basis of a symmetric tensor power

A basis `b : Basis κ R M` induces a basis of every symmetric tensor power `Sym[R]^n M`, indexed by
the **unordered** `n`-tuples `Sym κ n` of basis indices: the basis vector at `s` is the pure
symmetric tensor of the basis vectors listed by `s`. This is the symmetric counterpart of
`Basis.piTensorProduct`, whose index type is the ordered tuples `Fin n → κ`, and of
`Module.Basis.exteriorPower`, whose index type is the `n`-element subsets.

The coordinate map is built from the tensor-power basis: reading a pure tensor of basis vectors as
the unordered tuple of its indices is invariant under permuting the factors, so it descends to the
symmetric power by `SymmetricPower.lift`. Its inverse sends an unordered tuple to the pure
symmetric tensor of the corresponding basis vectors, which is well defined because any two
orderings of an unordered tuple differ by a permutation.

## Main definitions

* `SymmetricPower.tprodOfSym`: the pure symmetric tensor whose factors are listed, without order,
  by a point of `Sym κ n`.
* `Module.Basis.symmetricPower`: the induced basis of `Sym[R]^n M`.

## Main results

* `SymmetricPower.finrank_eq`: the rank of `Sym[R]^n M` is `Nat.multichoose (finrank R M) n`.
* `SymmetricPower.trace_map_of_apply_basis`: the trace on `Sym[R]^n M` of an endomorphism that is
  diagonal in a basis is the sum, over the unordered `n`-tuples of basis indices, of the product
  of the corresponding eigenvalues. This is the complete homogeneous symmetric polynomial in the
  eigenvalues, and is the symmetric counterpart of
  `exteriorPower.trace_map_of_apply_basis`.
-/

public section

open Module
open scoped TensorProduct

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-! ### Pure symmetric tensors indexed by unordered tuples -/

variable (R) in
/-- The pure symmetric tensor whose factors are the members of a family `v : κ → M` listed, with
multiplicity but without order, by a point of `Sym κ n`. -/
noncomputable def tprodOfSym (v : κ → M) (s : Sym κ n) : Sym[R]^n M :=
  ⨂ₛ[R] i, v (TauCeti.Sym.toFn s i)

/-- Reading off an ordered tuple of factors gives the pure symmetric tensor of those factors: the
choice of ordering hidden in `TauCeti.Sym.toFn` does not matter. -/
@[simp]
theorem tprodOfSym_ofFn (v : κ → M) (f : Fin n → κ) :
    tprodOfSym R v (TauCeti.Sym.ofFn f) = ⨂ₛ[R] i, v (f i) := by
  obtain ⟨σ, hσ⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1
    (TauCeti.Sym.ofFn_toFn (TauCeti.Sym.ofFn f))
  conv_rhs => rw [← hσ]
  exact (tprod_equiv (R := R) σ fun i => v (TauCeti.Sym.toFn (TauCeti.Sym.ofFn f) i)).symm

/-! ### The coordinate map in a basis -/

variable (b : Basis κ R M)

/-- Reading a pure tensor of basis vectors as the unordered tuple of its indices, on the tensor
power. -/
private noncomputable def toFinsuppAux : (⨂[R] (_ : Fin n), M) →ₗ[R] (Sym κ n →₀ R) :=
  (Basis.piTensorProduct fun _ : Fin n => b).constr R
    fun f => Finsupp.single (TauCeti.Sym.ofFn f) 1

private theorem toFinsuppAux_tprod_basis (f : Fin n → κ) :
    toFinsuppAux b (⨂ₜ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsuppAux, ← Basis.piTensorProduct_apply, Basis.constr_basis]

/-- Permuting the factors of a pure tensor does not change the unordered tuple of its indices. -/
private theorem toFinsuppAux_reindex (e : Equiv.Perm (Fin n)) :
    (toFinsuppAux b) ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin n => M) e).toLinearMap =
      toFinsuppAux b := by
  refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.piTensorProduct_apply,
    PiTensorProduct.reindex_tprod]
  rw [show (fun i => b (f (e.symm i))) = fun i => b ((f ∘ e.symm) i) from rfl,
    toFinsuppAux_tprod_basis, toFinsuppAux_tprod_basis, TauCeti.Sym.ofFn_comp_perm]

/-- The multilinear form of the coordinate map, before descending to the symmetric power. -/
private noncomputable def toFinsuppMultilinear :
    MultilinearMap R (fun _ : Fin n ↦ M) (Sym κ n →₀ R) :=
  (toFinsuppAux b).compMultilinearMap (PiTensorProduct.tprod R)

private theorem toFinsuppMultilinear_domDomCongr (e : Equiv.Perm (Fin n)) :
    (toFinsuppMultilinear b).domDomCongr e = toFinsuppMultilinear b := by
  refine MultilinearMap.ext fun m => ?_
  have h := congrFun (congrArg DFunLike.coe (toFinsuppAux_reindex b e.symm)) (⨂ₜ[R] i, m i)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod] at h
  simpa [toFinsuppMultilinear] using h

variable (n) in
/-- The coordinates of a symmetric tensor in the basis induced by `b`: a pure tensor of basis
vectors is sent to the unordered tuple of its indices. -/
noncomputable def toFinsupp : Sym[R]^n M →ₗ[R] (Sym κ n →₀ R) :=
  lift (toFinsuppMultilinear b) (toFinsuppMultilinear_domDomCongr b)

@[simp]
theorem toFinsupp_tprod_basis (f : Fin n → κ) :
    toFinsupp n b (⨂ₛ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsupp, lift_tprod, toFinsuppMultilinear, LinearMap.compMultilinearMap_apply,
    toFinsuppAux_tprod_basis]

variable (n) in
/-- The symmetric power of a free module is free on the unordered `n`-tuples of basis indices. -/
noncomputable def linearEquivFinsupp : Sym[R]^n M ≃ₗ[R] (Sym κ n →₀ R) :=
  LinearEquiv.ofLinearMap (toFinsupp n b) (Finsupp.linearCombination R (tprodOfSym R b))
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
      rw [Finsupp.linearCombination_single, one_smul, ← TauCeti.Sym.ofFn_toFn s, tprodOfSym_ofFn,
        toFinsupp_tprod_basis, TauCeti.Sym.ofFn_toFn])
    (by
      have key : (Finsupp.linearCombination R (tprodOfSym R b)) ∘ₗ (toFinsupp n b) ∘ₗ
          mk R (Fin n) M = mk R (Fin n) M := by
        refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Basis.piTensorProduct_apply,
          show mk R (Fin n) M (⨂ₜ[R] i, b (f i)) = ⨂ₛ[R] i, b (f i) from rfl,
          toFinsupp_tprod_basis, Finsupp.linearCombination_single, one_smul, tprodOfSym_ofFn]
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.1 (range_mk R (Fin n) M) x
      exact congrFun (congrArg DFunLike.coe key) y)

@[simp]
theorem linearEquivFinsupp_symm_single (s : Sym κ n) :
    (linearEquivFinsupp n b).symm (Finsupp.single s 1) = tprodOfSym R b s := by
  rw [linearEquivFinsupp, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    Finsupp.linearCombination_single, one_smul]

variable (n) in
/-- **A basis of the symmetric tensor power**: a basis of `M` induces a basis of `Sym[R]^n M`
indexed by the unordered `n`-tuples of basis indices. -/
noncomputable def _root_.Module.Basis.symmetricPower : Basis (Sym κ n) R (Sym[R]^n M) :=
  Basis.ofRepr (linearEquivFinsupp n b)

@[simp]
theorem _root_.Module.Basis.symmetricPower_apply (s : Sym κ n) :
    b.symmetricPower n s = tprodOfSym R b s :=
  linearEquivFinsupp_symm_single b s

end CommSemiring

/-! ### Freeness, rank, and traces -/

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- A symmetric power of a free module is free, on the unordered tuples of basis indices. -/
instance free [Module.Free R M] : Module.Free R (Sym[R]^n M) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R M).symmetricPower n)

/-- The rank of a symmetric power of a finite free module: the number of unordered `n`-tuples of
basis indices, `Nat.multichoose (finrank R M) n`. -/
theorem finrank_eq [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (Sym[R]^n M) = Nat.multichoose (Module.finrank R M) n := by
  classical
  rw [Module.finrank_eq_card_basis ((Module.Free.chooseBasis R M).symmetricPower n),
    Sym.card_sym_eq_multichoose, Module.finrank_eq_card_chooseBasisIndex]

/-- If an endomorphism is diagonal in a finite basis, then its trace on the `n`th symmetric power
is the sum, over the unordered `n`-tuples of basis indices, of the product of the corresponding
eigenvalues. -/
theorem trace_map_of_apply_basis [Fintype κ] [DecidableEq κ] (b : Basis κ R M) (f : M →ₗ[R] M)
    (a : κ → R) (n : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (Sym[R]^n M) (map (ι := Fin n) f) =
      ∑ s : Sym κ n, ((s : Multiset κ).map a).prod := by
  classical
  have hdiag : ∀ s : Sym κ n, map (ι := Fin n) f (b.symmetricPower n s) =
      ((s : Multiset κ).map a).prod • b.symmetricPower n s := by
    intro s
    conv_lhs => rw [Basis.symmetricPower_apply, tprodOfSym, map_tprod]
    rw [show (fun i => f (b (TauCeti.Sym.toFn s i))) =
        fun i => a (TauCeti.Sym.toFn s i) • b (TauCeti.Sym.toFn s i) from
      funext fun i => hf _, (tprod R).map_smul_univ, Basis.symmetricPower_apply, tprodOfSym]
    congr 1
    conv_rhs => rw [← TauCeti.Sym.ofFn_toFn s]
    rw [TauCeti.Sym.coe_ofFn, Multiset.map_coe, List.map_ofFn, Multiset.prod_coe,
      List.prod_ofFn, Function.comp_def]
  rw [LinearMap.trace_eq_matrix_trace R (b.symmetricPower n), Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hdiag s, map_smul, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

end CommRing

end SymmetricPower
