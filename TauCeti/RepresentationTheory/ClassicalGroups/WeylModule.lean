/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import TauCeti.Combinatorics.Young.StandardTableau.Reading
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower
public import TauCeti.RepresentationTheory.Symmetric.Relabel
public import TauCeti.RepresentationTheory.Tensor.PermRange

/-!
# The Weyl construction: a Young symmetrizer cuts out a `GL n k`-subrepresentation

Weyl's construction produces representations of `GL n k` from representations of the symmetric
group: a Young symmetrizer `c_t ∈ ℚ[S_d]` acts on the tensor power `(kⁿ)^{⊗d}` by permuting
tensor factors, and, because that action commutes with the diagonal action of `GL n k`, its
image is a `GL n k`-subrepresentation.  This file builds that image, the **Weyl module** of `t`.

The two inputs are already available: the image of a group-algebra element on a tensor power, as
a subrepresentation (`TauCeti.tensorPowerRange`, built from the commuting actions), and the
Young symmetrizer transported into the base ring
(`TauCeti.YoungTableau.youngSymmetrizerOver`).  Specializing the first to the standard
representation of `GL n k` and the second to a Young symmetrizer gives
`TauCeti.YoungTableau.weylModule`.

Two facts make the construction usable.  Relabeling the tableau moves the Weyl module by the
corresponding factor permutation, which is itself `GL n k`-equivariant, so the Weyl modules of
two tableaux of the same shape are isomorphic representations
(`TauCeti.YoungTableau.weylRepEquiv`): up to isomorphism the Weyl module depends only on the
shape.  That is what makes the shape-indexed form `TauCeti.weylModuleOfShape`, the Weyl module of
the row-superstandard tableau of `μ`, a legitimate representative of them all.  And the Weyl
module is nonzero exactly when the shape has at most `n` rows
(`TauCeti.YoungTableau.weylModule_eq_bot_iff`).  Nonvanishing
(`TauCeti.YoungTableau.weylModule_ne_bot`) is proved by evaluating a coordinate functional on
`c_t · (e_{r(1)} ⊗ ⋯ ⊗ e_{r(d)})`, where `r` records the row of each label: the surviving terms
are exactly the row group, each contributing `1`, so the value is the order of the row group,
nonzero in characteristic zero.  Vanishing (`TauCeti.YoungTableau.weylModule_eq_bot`) is the
transposition trick: if the first column is longer than `n` then, on each basis pure tensor, two
of its labels carry the same basis index, so their transposition lies in the column group and
fixes that pure tensor while negating `c_t`; the value is its own negative, hence zero because
`2` is invertible.

The Young symmetrizer is built over `ℚ`, so the coefficients are transported into the base ring
along `algebraMap ℚ k`; the base ring is therefore a `ℚ`-algebra throughout.  That alone makes
`2` invertible, which is all the vanishing statement needs.  Nonvanishing needs characteristic
zero, and a `ℚ`-algebra has characteristic zero as soon as it is nontrivial, so the nonvanishing
statements carry a `Nontrivial` hypothesis instead.  This is the characteristic-zero setting the
roadmap works in.

## Main definitions

* `TauCeti.YoungTableau.weylModule`: the Weyl module of a tableau, a subrepresentation of
  `(kⁿ)^{⊗|μ|}`, with `weylRep` the action of `GL n k` on it.
* `TauCeti.weylModuleOfShape`: the Weyl module of a shape, namely that of its row-superstandard
  tableau, with `weylRepOfShape` the action of `GL n k` on it and `weylFDRepOfShape` its bundled
  finite-dimensional form over a field.

## Main results

* `TauCeti.YoungTableau.weylRepEquiv`: the Weyl modules of two tableaux of the same shape are
  isomorphic representations of `GL n k`, and `TauCeti.YoungTableau.weylRepEquivOfShape`
  identifies each of them with the shape-indexed one.
* `TauCeti.YoungTableau.weylModule_ne_bot`: the Weyl module is nonzero when the shape has at
  most `n` rows.
* `TauCeti.YoungTableau.weylModule_eq_bot`: the Weyl module vanishes when the shape has more
  than `n` rows.
* `TauCeti.YoungTableau.weylModule_eq_bot_iff`: the two directions combined, the vanishing
  criterion.

## References

* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton-harris1991],
  Lecture 6, "Weyl's construction".
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 2, "Young symmetrizers and the Schur functor", where this object is pinned as
  `schurFunctor`.  It is named `weylModule` here because what is constructed is the module, not
  a functor: the Schur functor of `μ` is a functor in the underlying module, and only its value
  at `kⁿ` is built.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

/-! ## The Weyl module of a Young tableau -/

namespace YoungTableau

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ) {μ : YoungDiagram}

/-- **The Weyl module** of a `μ`-tableau `t`: the image of the Young symmetrizer `c_t` acting on
the `|μ|`-fold tensor power of the standard representation of `GL n k`, a subrepresentation
because the symmetric-group and general-linear actions commute.

Fulton and Harris write this as `𝕊^μ(kⁿ)`, the value at `kⁿ` of the Schur functor of `μ`; only
the value is built here, and no functoriality in the underlying module is claimed. -/
noncomputable def weylModule (t : YoungTableau μ) :
    Subrepresentation (tensorPowerRep k n μ.card) :=
  tensorPowerRange (stdRep k n) μ.card (youngSymmetrizerOver k t)

/-- The submodule underlying the Weyl module is the range of the Young symmetrizer acting on the
tensor power. -/
theorem weylModule_toSubmodule (t : YoungTableau μ) :
    (weylModule k n t).toSubmodule =
      LinearMap.range (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) := by
  rw [weylModule, tensorPowerRange_toSubmodule, permTensorActionAlgHom_def, permTensorAction_def]

/-- The action of `GL n k` on the Weyl module. -/
noncomputable abbrev weylRep (t : YoungTableau μ) :
    Representation k (GL (Fin n) k) (weylModule k n t).toSubmodule :=
  (weylModule k n t).toRepresentation

/-- The action on the Weyl module is the restriction of the action on the tensor power. -/
@[simp]
theorem weylRep_apply_coe (t : YoungTableau μ) (g : GL (Fin n) k)
    (x : (weylModule k n t).toSubmodule) :
    ((weylRep k n t g x : (weylModule k n t).toSubmodule) : ⨂[k]^μ.card (Fin n → k)) =
      tensorPowerRep k n μ.card g x :=
  (rfl)

/-! ### Independence of the tableau -/

variable {k n}

/-- Relabeling the tableau by `σ` moves the Weyl module by the permutation of the tensor factors
that `σ` induces. -/
theorem weylModule_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    (weylModule k n (relabel σ t)).toSubmodule =
      (weylModule k n t).toSubmodule.map (permTensorAction k n μ.card σ) := by
  rw [weylModule, weylModule, youngSymmetrizerOver_relabel,
    tensorPowerRange_conj (stdRep k n) μ.card (youngSymmetrizerOver k t) σ,
    permTensorAction_apply]

/-- Permuting the tensor factors by `σ` as a linear equivalence from the Weyl module of `t` to
the Weyl module of the relabeled tableau `σt`. -/
noncomputable def weylRelabelEquiv (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    (weylModule k n t).toSubmodule ≃ₗ[k] (weylModule k n (relabel σ t)).toSubmodule :=
  (PiTensorProduct.reindex k (fun _ : Fin μ.card => Fin n → k) σ).ofSubmodules _ _
    (by rw [weylModule_relabel σ t, permTensorAction_apply])

/-- The relabeling equivalence is induced by permuting the tensor factors. -/
@[simp]
theorem weylRelabelEquiv_apply_coe (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ)
    (x : (weylModule k n t).toSubmodule) :
    ((weylRelabelEquiv σ t x : (weylModule k n (relabel σ t)).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = permTensorAction k n μ.card σ x := by
  rw [permTensorAction_apply]
  rfl

/-- Permuting the tensor factors is `GL n k`-equivariant, so it is an isomorphism of
representations from the Weyl module of `t` to the Weyl module of `σt`. -/
noncomputable def weylRelabelRepEquiv (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    (weylRep k n t).Equiv (weylRep k n (relabel σ t)) :=
  Representation.Equiv.mk (weylRelabelEquiv σ t) fun g => by
    ext x
    have h := congrArg (fun f : Module.End k (⨂[k]^μ.card (Fin n → k)) =>
        f (x : ⨂[k]^μ.card (Fin n → k)))
      (commute_permTensorAction_tensorPowerRep k n μ.card σ g)
    simp only [Module.End.mul_apply] at h
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      weylRelabelEquiv_apply_coe, weylRep_apply_coe] using h

/-- The Weyl modules of two tableaux of the same shape are isomorphic representations of
`GL n k`: up to isomorphism the Weyl module depends only on the shape. -/
noncomputable def weylRepEquiv (t t' : YoungTableau μ) :
    (weylRep k n t).Equiv (weylRep k n t') :=
  relabel_relabelPerm t t' ▸ weylRelabelRepEquiv (relabelPerm t t') t

/-! ### The vanishing criterion -/

open Finset in
/-- The Weyl module of a `μ`-tableau is nonzero as soon as `μ` has at most `n` rows.

Evaluating the coordinate functional dual to `e_{r(1)} ⊗ ⋯ ⊗ e_{r(d)}` on `c_t` applied to that
same pure tensor, where `r ℓ` is the row of the label `ℓ`, leaves exactly the terms indexed by
the row group of `t`, each with coefficient `1`; the value is therefore the order of the row
group, which is nonzero because the base ring has characteristic zero. -/
theorem weylModule_ne_bot [Nontrivial k] (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) :
    (weylModule k n t).toSubmodule ≠ ⊥ := by
  classical
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  -- the row of each label, as an index of the standard basis of `kⁿ`
  have hr : ∀ ℓ : Fin μ.card, rowIndex t ℓ < n := by
    intro ℓ
    have hmem : ((t.symm ℓ : ℕ × ℕ).1, (t.symm ℓ : ℕ × ℕ).2) ∈ μ := (t.symm ℓ).2
    have h1 := YoungDiagram.mem_iff_lt_colLen.mp hmem
    rw [rowIndex_def]
    exact lt_of_lt_of_le (lt_of_lt_of_le h1 (μ.colLen_anti 0 _ (Nat.zero_le _))) hn
  set r : Fin μ.card → Fin n := fun ℓ => ⟨rowIndex t ℓ, hr ℓ⟩ with hrdef
  set φ : (⨂[k]^μ.card (Fin n → k)) →ₗ[k] k :=
    PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra k (Fin μ.card) k).compLinearMap fun ℓ => LinearMap.proj (r ℓ))
    with hφdef
  have hφ : ∀ s : Fin μ.card → Fin n,
      φ (PiTensorProduct.tprod k fun ℓ => Pi.single (s ℓ) (1 : k)) =
        if ∀ ℓ, r ℓ = s ℓ then 1 else 0 := by
    intro s
    rw [hφdef, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    simp only [LinearMap.proj_apply, Pi.single_apply]
    exact Finset.prod_boole.trans (by simp)
  -- the row group is exactly the set of permutations surviving the evaluation
  set S : Finset (Equiv.Perm (Fin μ.card)) := {σ | σ ∈ rowSubgroup t} with hSdef
  have hmemS : ∀ σ : Equiv.Perm (Fin μ.card), σ ∈ S ↔ σ ∈ rowSubgroup t := by
    intro σ; rw [hSdef]; simp
  have hcond : ∀ σ : Equiv.Perm (Fin μ.card),
      (∀ ℓ, r ℓ = r (σ.symm ℓ)) ↔ σ ∈ rowSubgroup t := by
    intro σ
    rw [← inv_mem_iff (G := Equiv.Perm (Fin μ.card)), mem_rowSubgroup]
    constructor
    · intro h ℓ; exact (congrArg Fin.val (h ℓ)).symm
    · intro h ℓ; exact Fin.ext (h ℓ).symm
  -- evaluate the functional on the image of the standard pure tensor
  set v : ⨂[k]^μ.card (Fin n → k) :=
    PiTensorProduct.tprod k fun ℓ => Pi.single (r ℓ) (1 : k) with hvdef
  have key : φ (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) v) = (S.card : k) := by
    rw [hvdef, permTensorActionAlgHom_apply_tprod, map_finsuppSum]
    have hterm : ∀ σ : Equiv.Perm (Fin μ.card), ∀ x : k,
        φ (x • PiTensorProduct.tprod k fun i => Pi.single (r (σ.symm i)) (1 : k)) =
          if σ ∈ rowSubgroup t then x else 0 := by
      intro σ x
      rw [map_smul, hφ (fun i => r (σ.symm i))]
      by_cases h : σ ∈ rowSubgroup t
      · rw [if_pos ((hcond σ).mpr h), if_pos h, smul_eq_mul, mul_one]
      · rw [if_neg fun hc => h ((hcond σ).mp hc), if_neg h, smul_zero]
    rw [Finsupp.sum_congr (g2 := fun σ x => if σ ∈ rowSubgroup t then x else 0)
      fun σ _ => hterm σ _]
    rw [Finsupp.sum]
    have hcoeff : ∀ σ ∈ rowSubgroup t, (youngSymmetrizerOver k t).coeff σ = 1 := by
      intro σ hσ
      rw [youngSymmetrizerOver_coeff, youngSymmetrizer_coeff_of_mem_rowSubgroup t hσ, map_one]
    have hsub : S ⊆ (youngSymmetrizerOver k t).coeff.support := by
      intro σ hσ
      rw [Finsupp.mem_support_iff, hcoeff σ ((hmemS σ).mp hσ)]
      exact one_ne_zero
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilter : (youngSymmetrizerOver k t).coeff.support.filter (· ∈ rowSubgroup t) = S := by
      ext σ
      simp only [Finset.mem_filter, hmemS]
      exact ⟨fun h => h.2, fun h => ⟨hsub ((hmemS σ).mpr h), h⟩⟩
    rw [hfilter, Finset.sum_congr rfl fun σ hσ => hcoeff σ ((hmemS σ).mp hσ), Finset.sum_const,
      nsmul_eq_mul, mul_one]
  intro hbot
  have hmem : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) v ∈
      (weylModule k n t).toSubmodule := by
    rw [weylModule_toSubmodule]
    exact LinearMap.mem_range_self _ v
  rw [hbot, Submodule.mem_bot k] at hmem
  rw [hmem, map_zero] at key
  have hne : (S.card : k) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (a := 1) ?_)
    exact (hmemS 1).mpr (one_mem _)
  exact hne key.symm

/-- The Weyl module of a `μ`-tableau vanishes as soon as `μ` has more than `n` rows.

The `|μ|`-fold tensor power is spanned by the pure tensors `e_{p(1)} ⊗ ⋯ ⊗ e_{p(d)}` of standard
basis vectors.  The first column of `μ` is longer than `n`, so two of its labels `x ≠ y` have
`p x = p y`; the transposition of `x` and `y` then lies in the column group of `t`, so it fixes
that pure tensor while multiplying `c_t` on the right by it negates `c_t`.  The value of `c_t` on
the pure tensor is therefore its own negative, hence zero because `2` is invertible in a
`ℚ`-algebra. -/
theorem weylModule_eq_bot (t : YoungTableau μ) (hn : n < μ.colLen 0) :
    (weylModule k n t).toSubmodule = ⊥ := by
  classical
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (2 : k) := by
    have h := Invertible.map (algebraMap ℚ k) (2 : ℚ)
    rwa [map_ofNat] at h
  -- the labels of the first column outnumber the basis indices
  have hcard : Fintype.card {ℓ : Fin μ.card // colIndex t ℓ = 0} = μ.colLen 0 := by
    rw [μ.colLen_eq_card, ← Fintype.card_coe]
    exact Fintype.card_congr (colFiberEquiv t 0)
  have hzero : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) = 0 := by
    refine (Basis.piTensorProduct fun _ : Fin μ.card => Pi.basisFun k (Fin n)).ext fun p => ?_
    rw [Basis.piTensorProduct_apply, LinearMap.zero_apply]
    simp only [Pi.basisFun_apply]
    -- two labels of the first column carry the same basis index
    obtain ⟨a, b, hab, hpab⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun ℓ : {ℓ : Fin μ.card // colIndex t ℓ = 0} => p ℓ)
        (by rw [hcard, Fintype.card_fin]; exact hn)
    have hxy : (a : Fin μ.card) ≠ (b : Fin μ.card) := fun h => hab (Subtype.ext h)
    have hτ : Equiv.swap (a : Fin μ.card) (b : Fin μ.card) ∈ colSubgroup t :=
      swap_mem_colSubgroup (by rw [a.2, b.2])
    -- their transposition fixes the pure tensor
    have hfix : (fun i => (Pi.single
          (p ((Equiv.swap (a : Fin μ.card) (b : Fin μ.card)).symm i)) (1 : k) : Fin n → k)) =
        fun i => (Pi.single (p i) (1 : k) : Fin n → k) := by
      funext i
      rw [Equiv.symm_swap]
      rcases eq_or_ne i (a : Fin μ.card) with rfl | h1
      · rw [Equiv.swap_apply_left, hpab]
      · rcases eq_or_ne i (b : Fin μ.card) with rfl | h2
        · rw [Equiv.swap_apply_right, hpab]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    -- and multiplying the symmetrizer on the right by it negates the symmetrizer
    have hc : youngSymmetrizerOver k t *
        MonoidAlgebra.single (Equiv.swap (a : Fin μ.card) (b : Fin μ.card)) 1 =
        -youngSymmetrizerOver k t := by
      have h := mul_youngSymmetrizer_right t ⟨_, hτ⟩
      rw [Equiv.Perm.sign_swap hxy] at h
      have h' := congrArg (MonoidAlgebra.mapAlgHom (Equiv.Perm (Fin μ.card)) (Algebra.ofId ℚ k))
        (by simpa using h :
          youngSymmetrizer t *
              MonoidAlgebra.single (Equiv.swap (a : Fin μ.card) (b : Fin μ.card)) 1 =
            -youngSymmetrizer t)
      rw [map_mul, map_neg, MonoidAlgebra.mapAlgHom_single, map_one] at h'
      rwa [youngSymmetrizerOver_def]
    -- so the value of the symmetrizer on the pure tensor is its own negative
    have h : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t *
          MonoidAlgebra.single (Equiv.swap (a : Fin μ.card) (b : Fin μ.card)) 1)
          (PiTensorProduct.tprod k fun i => (Pi.single (p i) (1 : k) : Fin n → k)) =
        permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
          (PiTensorProduct.tprod k fun i => (Pi.single (p i) (1 : k) : Fin n → k)) := by
      rw [map_mul, Module.End.mul_apply, ← MonoidAlgebra.of_apply, permTensorActionAlgHom_of,
        permTensorAction_apply, LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod, hfix]
    have hneg : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
          (PiTensorProduct.tprod k fun i => (Pi.single (p i) (1 : k) : Fin n → k)) =
        -permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
          (PiTensorProduct.tprod k fun i => (Pi.single (p i) (1 : k) : Fin n → k)) := by
      conv_lhs => rw [← h]
      rw [hc, map_neg, LinearMap.neg_apply]
    have htwo : (2 : k) • permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
        (PiTensorProduct.tprod k fun i => (Pi.single (p i) (1 : k) : Fin n → k)) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hneg]
      rw [add_neg_cancel]
    have := congrArg (fun w => (⅟(2 : k)) • w) htwo
    simpa [smul_smul] using this
  rw [weylModule_toSubmodule, hzero, LinearMap.range_zero]

/-- **The vanishing criterion for the Weyl module**: it vanishes exactly when the shape has more
rows than the dimension of the standard representation. -/
theorem weylModule_eq_bot_iff [Nontrivial k] (t : YoungTableau μ) :
    (weylModule k n t).toSubmodule = ⊥ ↔ n < μ.colLen 0 := by
  refine ⟨fun h => ?_, weylModule_eq_bot t⟩
  by_contra hle
  exact weylModule_ne_bot t (not_lt.mp hle) h

/-! ### Invariants of the Weyl module -/

/-- The Weyl modules of two tableaux of the same shape are isomorphic `k`-modules, so their
`Module.finrank` values agree; over a field this is the equality of their dimensions. -/
theorem finrank_weylModule_eq (t t' : YoungTableau μ) :
    Module.finrank k (weylModule k n t).toSubmodule =
      Module.finrank k (weylModule k n t').toSubmodule :=
  (weylRepEquiv t t').toLinearEquiv.finrank_eq

/-- The Weyl module of a shape with at most `n` rows is nontrivial. -/
theorem nontrivial_weylModule [Nontrivial k] (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) :
    Nontrivial (weylModule k n t).toSubmodule :=
  Submodule.nontrivial_iff_ne_bot.mpr (weylModule_ne_bot t hn)

end YoungTableau

/-! ## The Weyl module of a shape -/

section Shape

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ)

/-- **The Weyl module of a shape** `μ`: the Weyl module of the row-superstandard tableau of `μ`,
the canonical `μ`-tableau.  Since the Weyl modules of two `μ`-tableaux are isomorphic
representations, this is a legitimate shape-indexed representative of them all; the
identification is `TauCeti.YoungTableau.weylRepEquivOfShape`.

This is the object the classical-groups roadmap pins as `schurFunctor n μ`. -/
noncomputable def weylModuleOfShape (μ : YoungDiagram) :
    Subrepresentation (tensorPowerRep k n μ.card) :=
  YoungTableau.weylModule k n (StandardYoungTableau.rowSuperstandard μ).toEquiv

/-- The action of `GL n k` on the Weyl module of a shape. -/
noncomputable abbrev weylRepOfShape (μ : YoungDiagram) :
    Representation k (GL (Fin n) k) (weylModuleOfShape k n μ).toSubmodule :=
  (weylModuleOfShape k n μ).toRepresentation

/-- The Weyl module of any `μ`-tableau is isomorphic, as a representation of `GL n k`, to the
Weyl module of the shape `μ`. -/
noncomputable def YoungTableau.weylRepEquivOfShape {μ : YoungDiagram} (t : YoungTableau μ) :
    (YoungTableau.weylRep k n t).Equiv (weylRepOfShape k n μ) :=
  YoungTableau.weylRepEquiv t _

end Shape

section Field

variable (k : Type u) [Field k] [Algebra ℚ k] (n : ℕ)

/-- The Weyl module of a shape, bundled as an object of `FDRep`.

A submodule of the tensor power is finitely generated only once the base ring is well behaved
enough, so this bundled form asks for a field, whereas `weylModuleOfShape` itself does not. -/
noncomputable abbrev weylFDRepOfShape (μ : YoungDiagram) : FDRep k (GL (Fin n) k) :=
  FDRep.of (V := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ)

end Field

end TauCeti
