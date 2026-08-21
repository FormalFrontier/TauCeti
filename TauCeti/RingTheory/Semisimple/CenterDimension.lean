/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finite
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# The center bounds the number of simple modules of a semisimple algebra

A semisimple ring `R` has finitely many isomorphism classes of simple modules, indexed by the
isotypic components of the regular module (`TauCeti.simpleSubmoduleClassesEquiv`). When `R` is an
algebra over a field `k`, this file bounds that number by the dimension of the center:

`Nat.card (isotypicComponents R R) ≤ Module.finrank k (Subalgebra.center k R)`.

The bound is the counting half of Artin-Wedderburn, obtained without choosing a presentation
`R ≃+* ∏ᵢ Matₙᵢ(Dᵢ)`: for such a product the center is `∏ᵢ Z(Dᵢ)`, of dimension at least the number
of blocks, and the argument here says exactly that intrinsically. Where
`TauCeti.card_blocks_eq` compares two presentations, this bound mentions none.

The mechanism is that each isotypic component of the regular module contains a nonzero *central*
element (`TauCeti.exists_ne_zero_mem_center_of_mem_isotypicComponents`). Writing `1 = ∑_c e_c` along
the decomposition of `R` into its isotypic components, the summand `e_c` is central because for
`z : R` the two decompositions `z = ∑_c z * e_c` and `z = ∑_c e_c * z` have their `c`-th terms in
the same summand: the first because `c` is a left ideal, the second because an isotypic component of
the regular module is *two-sided* (`TauCeti.isTwoSided_of_mem_isotypicComponents`, Mathlib's
`isFullyInvariant_iff_isTwoSided` read on `isotypicComponents R R`). It is nonzero because the same
uniqueness gives `x * e_c = x` for `x ∈ c`. Elements chosen one from each summand of an independent
family are linearly independent, so the components are at most as many as the dimension of the
center.

Nothing here needs `R` itself to be finite-dimensional: only the center is assumed finite as a
`k`-module, which is what a group algebra supplies through its class-sum basis.

## Main results

* `TauCeti.isTwoSided_of_mem_isotypicComponents`: an isotypic component of the regular module is a
  two-sided ideal.
* `TauCeti.exists_ne_zero_mem_center_of_mem_isotypicComponents`: it contains a nonzero central
  element.
* `TauCeti.card_isotypicComponents_le_finrank_center`: the number of isotypic components of the
  regular module is at most the dimension of the center.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §25.
* [Semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
  Layer 2, "Artin-Wedderburn, assembled with uniqueness".
-/

public section

namespace TauCeti

open scoped BigOperators

variable {R : Type*} [Ring R]

/-- **An isotypic component of the regular module is a two-sided ideal.** Mathlib's
`Submodule.IsFullyInvariant.of_mem_isotypicComponents` makes it invariant under every endomorphism
of the regular module, and those endomorphisms are the right multiplications. -/
theorem isTwoSided_of_mem_isotypicComponents {c : Ideal R} (hc : c ∈ isotypicComponents R R) :
    c.IsTwoSided :=
  isFullyInvariant_iff_isTwoSided.mp (Submodule.IsFullyInvariant.of_mem_isotypicComponents hc)

section Field

variable (k R : Type*) [Field k] [Ring R] [Algebra k R] [IsSemisimpleRing R]

/-- The decomposition of `1` along the isotypic components of the regular module: a family of
nonzero central elements, one in each component. This is the whole content of the section; the two
public statements below read off the parts of it that they need. -/
private theorem exists_center_family :
    ∃ e : isotypicComponents R R → R, (∀ c, e c ∈ c.1) ∧ (∀ c, e c ≠ 0) ∧
      ∀ c, e c ∈ Subalgebra.center k R := by
  classical
  let _ : Fintype (isotypicComponents R R) := Fintype.ofFinite _
  have hind : iSupIndep fun c : isotypicComponents R R ↦ c.1 :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R R)
  have htop : ⨆ c : isotypicComponents R R, c.1 = ⊤ :=
    (sSup_eq_iSup' (isotypicComponents R R)).symm.trans (sSup_isotypicComponents R R)
  -- Any two decompositions along the components agree term by term.
  have huniq : ∀ a b : isotypicComponents R R → R, (∀ c, a c ∈ c.1) → (∀ c, b c ∈ c.1) →
      ∑ c, a c = ∑ c, b c → ∀ c, a c = b c := fun a b ha hb hab c ↦
    (iSupIndep_iff_finsetSum_eq_imp_eq _).mp hind Finset.univ a b
      (fun i _ ↦ ⟨ha i, hb i⟩) hab c (Finset.mem_univ c)
  obtain ⟨v, hv⟩ : ∃ v : ∀ c : isotypicComponents R R, c.1, ∑ c, (v c : R) = 1 :=
    (Submodule.mem_iSup_finset_iff_exists_sum _ 1).mp (by simp [htop])
  have hleft : ∀ (x : R) (d : isotypicComponents R R), x * (v d : R) ∈ d.1 := fun x d ↦ by
    simpa only [smul_eq_mul] using d.1.smul_mem x (v d).2
  refine ⟨fun c ↦ (v c : R), fun c ↦ (v c).2, fun c hc ↦ ?_, fun c ↦ ?_⟩
  · -- A vanishing summand would kill its own component.
    refine absurd ((Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_) (bot_lt_isotypicComponents c.2).ne'
    have hb : ∀ d : isotypicComponents R R, (if d = c then x else 0) ∈ d.1 := fun d ↦ by
      split
      · next h => exact h ▸ hx
      · exact d.1.zero_mem
    have hsum : ∑ d, x * (v d : R) = ∑ d, if d = c then x else 0 := by
      rw [← Finset.mul_sum, hv, mul_one, Finset.sum_ite_eq' Finset.univ c fun _ ↦ x,
        ite_eq_left (Finset.mem_univ c)]
    simpa [hc] using (huniq _ _ (hleft x) hb hsum c).symm
  · -- Centrality: multiplying `1 = ∑ e_d` on either side decomposes the same element.
    rw [Subalgebra.mem_center_iff]
    intro z
    have hright : ∀ d : isotypicComponents R R, (v d : R) * z ∈ d.1 := fun d ↦ by
      have := isTwoSided_of_mem_isotypicComponents d.2
      exact Ideal.mul_mem_right z _ (v d).2
    have hsum : ∑ d, z * (v d : R) = ∑ d, (v d : R) * z := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, hv, mul_one, one_mul]
    exact huniq _ _ (hleft z) hright hsum c

/-- **Every isotypic component of the regular module contains a nonzero central element.** It is the
corresponding summand of the decomposition of `1`; only these two properties are recorded, being all
that the dimension count below consumes. -/
theorem exists_ne_zero_mem_center_of_mem_isotypicComponents {c : Submodule R R}
    (hc : c ∈ isotypicComponents R R) :
    ∃ e : R, e ∈ c ∧ e ≠ 0 ∧ e ∈ Subalgebra.center k R := by
  obtain ⟨e, hmem, hne, hcen⟩ := exists_center_family k R
  exact ⟨e ⟨c, hc⟩, hmem ⟨c, hc⟩, hne ⟨c, hc⟩, hcen ⟨c, hc⟩⟩

/-- **The center bounds the number of isomorphism classes of simple modules.** Over a semisimple
`k`-algebra whose center is finite-dimensional, the isotypic components of the regular module, which
`TauCeti.simpleSubmoduleClassesEquiv` identifies with the isomorphism classes of simple modules, are
at most as many as the dimension of the center.

For a group algebra the right-hand side is the number of conjugacy classes, by
`TauCeti.finrank_center_monoidAlgebra`. -/
theorem card_isotypicComponents_le_finrank_center [Module.Finite k (Subalgebra.center k R)] :
    Nat.card (isotypicComponents R R) ≤ Module.finrank k (Subalgebra.center k R) := by
  classical
  let _ : Fintype (isotypicComponents R R) := Fintype.ofFinite _
  obtain ⟨e, hmem, hne, hcen⟩ := exists_center_family k R
  have hind : iSupIndep fun c : isotypicComponents R R ↦ c.1 :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R R)
  -- The chosen elements are linearly independent over `k`, one from each independent summand.
  have hli : LinearIndependent k e := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hmem' : ∀ c ∈ s, g c • e c ∈ c.1 := fun c _ ↦ by
      simpa only [Algebra.smul_def, smul_eq_mul] using
        c.1.smul_mem (algebraMap k R (g c)) (hmem c)
    have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind s
      (fun c ↦ g c • e c) hmem' hg i hi
    by_contra hgi
    exact hne i (by rw [← one_smul k (e i), ← inv_mul_cancel₀ hgi, mul_smul, hzero, smul_zero])
  -- Read the independence inside the center and count.
  have hli' : LinearIndependent k fun c ↦ (⟨e c, hcen c⟩ : Subalgebra.center k R) :=
    LinearIndependent.of_comp (Subalgebra.center k R).val.toLinearMap hli
  simpa using hli'.fintype_card_le_finrank

end Field

end TauCeti
