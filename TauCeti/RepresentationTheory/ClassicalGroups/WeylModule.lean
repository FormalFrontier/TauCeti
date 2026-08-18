/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Data.Complex.Basic
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

The Young symmetrizer available here is the one built over `ℚ` in
`TauCeti.YoungTableau.youngSymmetrizer`, so its coefficients reach the base ring along
`algebraMap ℚ k`; the base ring is therefore a `ℚ`-algebra throughout.  That is a consequence of
how `c_t` is currently defined, not of `c_t` itself, whose coefficients are integral: an integral
Young symmetrizer would let the construction run over any commutative ring, and building one is a
separate topic.  What the two halves of the criterion actually use of the hypothesis is much
less.  Vanishing needs only that `2` is invertible, which a `ℚ`-algebra gives.  Nonvanishing needs
characteristic zero, and a `ℚ`-algebra has characteristic zero as soon as it is nontrivial, so the
nonvanishing statements carry a `Nontrivial` hypothesis instead.  This is the characteristic-zero
setting the roadmap works in.

## Main definitions

* `TauCeti.YoungTableau.weylModule`: the Weyl module of a tableau, a subrepresentation of
  `(kⁿ)^{⊗|μ|}`, with `weylRep` the action of `GL n k` on it.
* `TauCeti.weylModuleOfShape`: the Weyl module of a shape, namely that of its row-superstandard
  tableau, with `weylRepOfShape` the action of `GL n k` on it and `weylFDRepOfShape` its bundled
  form in `FDRep`, over a Noetherian base ring.
* `TauCeti.schurFunctor`: the roadmap-pinned name, `weylFDRepOfShape` at `k = ℂ`.

## Main results

* `TauCeti.YoungTableau.weylRepEquiv`: the Weyl modules of two tableaux of the same shape are
  isomorphic representations of `GL n k`, and `TauCeti.YoungTableau.weylRepEquivOfShape`
  identifies each of them with the shape-indexed one.
* `TauCeti.YoungTableau.weylModule_ne_bot`: the Weyl module is nonzero when the shape has at
  most `n` rows.
* `TauCeti.YoungTableau.weylModule_eq_bot`: the Weyl module vanishes when the shape has more
  than `n` rows.
* `TauCeti.YoungTableau.weylModule_eq_bot_iff`: the two directions combined, the vanishing
  criterion, with `TauCeti.weylModuleOfShape_eq_bot_iff` its shape-indexed form.

## References

* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton-harris1991],
  Lecture 6, "Weyl's construction".
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 2, "Young symmetrizers and the Schur functor", where this object is pinned as
  `schurFunctor`.  The construction itself is named `weylModule` here because what is constructed
  is the module, not a functor: the Schur functor of `μ` is a functor in the underlying module,
  and only its value at `kⁿ` is built.  The pinned name is supplied as `TauCeti.schurFunctor`,
  the definitional re-export at `k = ℂ` of the bundled form, so that later roadmap layers can
  consume it under the name they are written against.

  Of that bullet, the `GLₙ`-subrepresentation, the fixed choice of tableau, the canonical
  isomorphism between the images for different tableaux, and the vanishing criterion are built
  here.  The bullet's two remaining deliverables, the extreme cases `S^{(d)} V ≅ Symᵈ V` and
  `S^{(1ᵈ)} V ≅ ⋀ᵈ V`, are proved in
  `TauCeti/RepresentationTheory/ClassicalGroups/ExtremeShape.lean`, against
  `TauCeti.YoungTableau.weylModule_toSubmodule` and `TauCeti.weylRepOfShape` and without
  unfolding anything built here.
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

/-- The Weyl module is the image of the Young symmetrizer of `t` acting on the tensor power, so
the general lemmas about `TauCeti.tensorPowerRange` apply to it. -/
theorem weylModule_def (t : YoungTableau μ) :
    weylModule k n t = tensorPowerRange (stdRep k n) μ.card (youngSymmetrizerOver k t) :=
  (rfl)

/-- The submodule underlying the Weyl module is the range of the Young symmetrizer acting on the
tensor power. -/
@[simp]
theorem weylModule_toSubmodule (t : YoungTableau μ) :
    (weylModule k n t).toSubmodule =
      LinearMap.range (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) := by
  rw [weylModule, tensorPowerRange_toSubmodule, permTensorActionAlgHom_def, permTensorAction_def]

/-- The action of `GL n k` on the Weyl module. -/
noncomputable abbrev weylRep (t : YoungTableau μ) :
    Representation k (GL (Fin n) k) (weylModule k n t).toSubmodule :=
  (weylModule k n t).toRepresentation

/-- The action on the Weyl module is the restriction of the action on the tensor power. -/
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

/-- **Every label of a `μ`-tableau has row index below `n`** once `μ` has at most `n` rows: the
row of a label is bounded by the length of the first column. -/
private theorem rowIndex_lt_of_colLen_le (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n)
    (ℓ : Fin μ.card) : rowIndex t ℓ < n := by
  have hmem : ((t.symm ℓ : ℕ × ℕ).1, (t.symm ℓ : ℕ × ℕ).2) ∈ μ := (t.symm ℓ).2
  have h1 := YoungDiagram.mem_iff_lt_colLen.mp hmem
  rw [rowIndex_def]
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 (μ.colLen_anti 0 _ (Nat.zero_le _))) hn

/-- **The symmetrizer's diagonal coefficient is the order of the row group.** Write `r ℓ` for the
row of the label `ℓ`. The `r`-coordinate of `c_t • e_r` in the monomial basis is the number of
permutations lying in the row group of `t`. -/
private theorem repr_symmetrizer_tensorPowerBasis_eq_card_rowSubgroup (t : YoungTableau μ)
    (hn : μ.colLen 0 ≤ n) :
    (tensorPowerBasis k n μ.card).repr
        (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
          (tensorPowerBasis k n μ.card fun ℓ =>
            (⟨rowIndex t ℓ, rowIndex_lt_of_colLen_le t hn ℓ⟩ : Fin n)))
        (fun ℓ => (⟨rowIndex t ℓ, rowIndex_lt_of_colLen_le t hn ℓ⟩ : Fin n)) =
      (Nat.card (rowSubgroup t) : k) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  set r : Fin μ.card → Fin n := fun ℓ => ⟨rowIndex t ℓ, rowIndex_lt_of_colLen_le t hn ℓ⟩
  -- the row group is exactly the set of permutations surviving the evaluation
  set S : Finset (Equiv.Perm (Fin μ.card)) := {σ | σ ∈ rowSubgroup t} with hSdef
  have hmemS : ∀ σ : Equiv.Perm (Fin μ.card), σ ∈ S ↔ σ ∈ rowSubgroup t := by
    intro σ; rw [hSdef]; simp
  have hcond : ∀ σ : Equiv.Perm (Fin μ.card),
      (fun ℓ => r (σ.symm ℓ)) = r ↔ σ ∈ rowSubgroup t := by
    intro σ
    rw [← inv_mem_iff (G := Equiv.Perm (Fin μ.card)), mem_rowSubgroup]
    exact ⟨fun h ℓ => congrArg Fin.val (congrFun h ℓ), fun h => funext fun ℓ => Fin.ext (h ℓ)⟩
  have hSNat : Nat.card (rowSubgroup t) = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hSNat, permTensorActionAlgHom_apply_tensorPowerBasis, map_sum, Finset.sum_apply']
  have hterm : ∀ σ ∈ (youngSymmetrizerOver k t).coeff.support,
      ((tensorPowerBasis k n μ.card).repr
          ((youngSymmetrizerOver k t).coeff σ •
            tensorPowerBasis k n μ.card fun i => r (σ.symm i))) r =
        if σ ∈ rowSubgroup t then (youngSymmetrizerOver k t).coeff σ else 0 := by
    intro σ _
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    exact if_congr (hcond σ) rfl rfl
  rw [Finset.sum_congr rfl hterm]
  have hcoeff : ∀ σ ∈ rowSubgroup t, (youngSymmetrizerOver k t).coeff σ = 1 := by
    intro σ hσ
    rw [youngSymmetrizerOver_coeff, youngSymmetrizer_coeff_eq_one_of_mem_rowSubgroup t hσ,
      map_one]
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

/-- **The symmetrizer does not annihilate the monomial basis vector of a tableau.** Write `r ℓ` for
the row of the label `ℓ`; the `r`-coordinate of `c_t • e_r` in the monomial basis is nonzero. -/
private theorem repr_symmetrizer_tensorPowerBasis_ne_zero [Nontrivial k] (t : YoungTableau μ)
    (hn : μ.colLen 0 ≤ n) :
    (tensorPowerBasis k n μ.card).repr
        (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
          (tensorPowerBasis k n μ.card fun ℓ =>
            (⟨rowIndex t ℓ, rowIndex_lt_of_colLen_le t hn ℓ⟩ : Fin n)))
        (fun ℓ => (⟨rowIndex t ℓ, rowIndex_lt_of_colLen_le t hn ℓ⟩ : Fin n)) ≠ 0 := by
  classical
  -- the coefficient is the order of the row group, and characteristic zero keeps it nonzero
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  rw [repr_symmetrizer_tensorPowerBasis_eq_card_rowSubgroup t hn]
  exact Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)

/-- The Weyl module of a `μ`-tableau is nonzero as soon as `μ` has at most `n` rows.

The image of the standard pure tensor `e_{r(1)} ⊗ ⋯ ⊗ e_{r(d)}` under the symmetrizer, where
`r ℓ` is the row of the label `ℓ`, is detected by the dual coordinate functional, so it is not
zero and the module it generates is not `⊥`. -/
theorem weylModule_ne_bot [Nontrivial k] (t : YoungTableau μ) (hn : μ.colLen 0 ≤ n) :
    weylModule k n t ≠ ⊥ := by
  intro hbot
  -- the submodule underlying the zero subrepresentation is `⊥`
  have hbot' : (weylModule k n t).toSubmodule = ⊥ := by rw [hbot]; rfl
  have hmem : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
      (tensorPowerBasis k n μ.card fun ℓ =>
        (⟨rowIndex t ℓ, rowIndex_lt_of_colLen_le t hn ℓ⟩ : Fin n))
      ∈ (weylModule k n t).toSubmodule := by
    rw [weylModule_toSubmodule]
    exact LinearMap.mem_range_self _ _
  rw [hbot', Submodule.mem_bot k] at hmem
  exact repr_symmetrizer_tensorPowerBasis_ne_zero t hn (by rw [hmem, map_zero]; rfl)

/-- When `μ` has more than `n` rows, any index function `p : Fin μ.card → Fin n` repeats a value on
the first column of `t`: two distinct labels of that column carry the same basis index. -/
private theorem exists_ne_and_apply_eq_of_lt_colLen (t : YoungTableau μ) (hn : n < μ.colLen 0)
    (p : Fin μ.card → Fin n) :
    ∃ a b : Fin μ.card, colIndex t a = 0 ∧ colIndex t b = 0 ∧ a ≠ b ∧ p a = p b := by
  classical
  have hcard : Fintype.card {ℓ : Fin μ.card // colIndex t ℓ = 0} = μ.colLen 0 := by
    rw [μ.colLen_eq_card, ← Fintype.card_coe]
    exact Fintype.card_congr (colFiberEquiv t 0)
  obtain ⟨a, b, hab, hpab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun ℓ : {ℓ : Fin μ.card // colIndex t ℓ = 0} => p ℓ)
      (by rw [hcard, Fintype.card_fin]; exact hn)
  exact ⟨a, b, a.2, b.2, fun h => hab (Subtype.ext h), hpab⟩

/-- Transposing two labels of the same column that `p` sends to the same basis index fixes the
monomial basis vector at `p` while negating `c_t`, so the symmetrizer's value there is its own
negative. -/
private theorem permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_eq_neg
    (t : YoungTableau μ) {p : Fin μ.card → Fin n} {a b : Fin μ.card}
    (hcol : colIndex t a = colIndex t b) (hab : a ≠ b) (hpab : p a = p b) :
    permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
        (tensorPowerBasis k n μ.card p) =
      -permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
        (tensorPowerBasis k n μ.card p) := by
  have hτ : Equiv.swap a b ∈ colSubgroup t := swap_mem_colSubgroup hcol
  -- the transposition permutes the index function back to itself
  have hswap : (fun i => p ((Equiv.swap a b).symm i)) = p :=
    funext fun i => by rw [Equiv.symm_swap]; exact Equiv.apply_swap_eq_self hpab i
  have h : permTensorActionAlgHom k n μ.card
        (youngSymmetrizerOver k t * MonoidAlgebra.single (Equiv.swap a b) 1)
        (tensorPowerBasis k n μ.card p) =
      permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
        (tensorPowerBasis k n μ.card p) := by
    rw [map_mul, Module.End.mul_apply, permTensorActionAlgHom_single_tensorPowerBasis, one_smul,
      hswap]
  -- a transposition of the column group has sign `-1`, and `c_t` is alternating under it
  have hneg : youngSymmetrizerOver k t * MonoidAlgebra.single (Equiv.swap a b) 1 =
      -youngSymmetrizerOver k t := by
    simpa [Equiv.Perm.sign_swap hab] using mul_youngSymmetrizerOver_right k t ⟨_, hτ⟩
  conv_lhs => rw [← h]
  rw [hneg, map_neg, LinearMap.neg_apply]

/-- **The symmetrizer annihilates the whole tensor power when `μ` has more than `n` rows.** On each
monomial basis vector two labels of the first column share a basis index, so their transposition
fixes it while negating `c_t`; the value is its own negative, hence zero since `2` is invertible. -/
private theorem permTensorActionAlgHom_youngSymmetrizerOver_eq_zero (t : YoungTableau μ)
    (hn : n < μ.colLen 0) :
    permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) = 0 := by
  have : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have : Invertible (2 : k) := by
    have h := Invertible.map (algebraMap ℚ k) (2 : ℚ)
    rwa [map_ofNat] at h
  refine (tensorPowerBasis k n μ.card).ext fun p => ?_
  rw [LinearMap.zero_apply]
  obtain ⟨a, b, ha, hb, hab, hpab⟩ := exists_ne_and_apply_eq_of_lt_colLen t hn p
  have hneg :=
    permTensorActionAlgHom_youngSymmetrizerOver_tensorPowerBasis_eq_neg (k := k) t
      (ha.trans hb.symm) hab hpab
  have htwo : (2 : k) • permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
      (tensorPowerBasis k n μ.card p) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    rw [add_neg_cancel]
  simpa [smul_smul] using congrArg (fun w => (⅟(2 : k)) • w) htwo

/-- The Weyl module of a `μ`-tableau vanishes as soon as `μ` has more than `n` rows.

The `|μ|`-fold tensor power is spanned by the monomial basis vectors `e_{p(1)} ⊗ ⋯ ⊗ e_{p(d)}`.
The first column of `μ` is longer than `n`, so on each of them two labels of that column share a
basis index; their transposition lies in the column group, fixing the vector while negating `c_t`.
The value of `c_t` is therefore its own negative, hence zero because `2` is invertible in a
`ℚ`-algebra. -/
theorem weylModule_eq_bot (t : YoungTableau μ) (hn : n < μ.colLen 0) :
    weylModule k n t = ⊥ := by
  -- subrepresentations are equal when their underlying submodules are
  refine Subrepresentation.toSubmodule_injective ?_
  rw [weylModule_toSubmodule, permTensorActionAlgHom_youngSymmetrizerOver_eq_zero t hn,
    LinearMap.range_zero]
  rfl

/-- **The vanishing criterion for the Weyl module**: it vanishes exactly when the shape has more
rows than the dimension of the standard representation. -/
theorem weylModule_eq_bot_iff [Nontrivial k] (t : YoungTableau μ) :
    weylModule k n t = ⊥ ↔ n < μ.colLen 0 := by
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
    Nontrivial (weylModule k n t).toSubmodule := by
  refine Submodule.nontrivial_iff_ne_bot.mpr ?_
  intro h
  exact weylModule_ne_bot t hn (Subrepresentation.toSubmodule_injective h)

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
  YoungTableau.weylModule k n (StandardYoungTableau.rowSuperstandard μ).toTableau

/-- The Weyl module of a shape is the Weyl module of its row-superstandard tableau, so the
tableau-indexed lemmas apply to it. -/
theorem weylModuleOfShape_def (μ : YoungDiagram) :
    weylModuleOfShape k n μ =
      YoungTableau.weylModule k n (StandardYoungTableau.rowSuperstandard μ).toTableau :=
  (rfl)

/-- The action of `GL n k` on the Weyl module of a shape. -/
noncomputable abbrev weylRepOfShape (μ : YoungDiagram) :
    Representation k (GL (Fin n) k) (weylModuleOfShape k n μ).toSubmodule :=
  (weylModuleOfShape k n μ).toRepresentation

/-- The submodule underlying the Weyl module of a shape is the range of the Young symmetrizer of
its row-superstandard tableau acting on the tensor power. -/
@[simp]
theorem weylModuleOfShape_toSubmodule (μ : YoungDiagram) :
    (weylModuleOfShape k n μ).toSubmodule =
      LinearMap.range (permTensorActionAlgHom k n μ.card
        (YoungTableau.youngSymmetrizerOver k
          (StandardYoungTableau.rowSuperstandard μ).toTableau)) :=
  YoungTableau.weylModule_toSubmodule k n _

/-- The action on the Weyl module of a shape is the restriction of the action on the tensor
power. -/
theorem weylRepOfShape_apply_coe (μ : YoungDiagram) (g : GL (Fin n) k)
    (x : (weylModuleOfShape k n μ).toSubmodule) :
    ((weylRepOfShape k n μ g x : (weylModuleOfShape k n μ).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = tensorPowerRep k n μ.card g x :=
  (rfl)

/-- The Weyl module of any `μ`-tableau is isomorphic, as a representation of `GL n k`, to the
Weyl module of the shape `μ`. -/
noncomputable def YoungTableau.weylRepEquivOfShape {μ : YoungDiagram} (t : YoungTableau μ) :
    (YoungTableau.weylRep k n t).Equiv (weylRepOfShape k n μ) :=
  YoungTableau.weylRepEquiv t _

/-- **The vanishing criterion for the Weyl module of a shape**: it vanishes exactly when the
shape has more rows than the dimension of the standard representation. -/
theorem weylModuleOfShape_eq_bot_iff [Nontrivial k] (μ : YoungDiagram) :
    weylModuleOfShape k n μ = ⊥ ↔ n < μ.colLen 0 :=
  YoungTableau.weylModule_eq_bot_iff _

/-- The Weyl module of a shape with at most `n` rows is nontrivial. -/
theorem nontrivial_weylModuleOfShape [Nontrivial k] (μ : YoungDiagram) (hn : μ.colLen 0 ≤ n) :
    Nontrivial (weylModuleOfShape k n μ).toSubmodule :=
  YoungTableau.nontrivial_weylModule _ hn

end Shape

section Bundled

variable (k : Type u) [CommRing k] [Algebra ℚ k] [IsNoetherianRing k] (n : ℕ)

/-- The Weyl module of a shape, bundled as an object of `FDRep`.

`FDRep` is the category of finitely generated representations over any ring, and a submodule of
the tensor power is finitely generated as soon as the base ring is Noetherian, which is all this
bundled form asks; a field is the case of interest, and is Noetherian. -/
noncomputable abbrev weylFDRepOfShape (μ : YoungDiagram) : FDRep k (GL (Fin n) k) :=
  FDRep.of (V := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ)

end Bundled

/-- **The Schur functor** `𝕊^μ(ℂⁿ)` in the roadmap's pinned form: the Weyl module of the shape
`μ` over `ℂ`, bundled as an object of `FDRep ℂ (GL (Fin n) ℂ)`.

This is a definitional re-export of `TauCeti.weylFDRepOfShape` at `k = ℂ`, under the name later
roadmap layers are written against; the general form, over any Noetherian commutative ring that
is a `ℚ`-algebra, is `TauCeti.weylFDRepOfShape`, and the unbundled construction is
`TauCeti.weylModuleOfShape`. -/
noncomputable abbrev schurFunctor (n : ℕ) (μ : YoungDiagram) : FDRep ℂ (GL (Fin n) ℂ) :=
  weylFDRepOfShape ℂ n μ

end TauCeti
