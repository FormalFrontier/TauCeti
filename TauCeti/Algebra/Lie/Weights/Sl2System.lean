/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Basic

/-!
# Root vectors normalised against the coroots

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, and let `H` be a splitting Cartan subalgebra. Each root `α` has a
one-dimensional root space `Lα`, so a root vector is determined by a scalar, and Mathlib's
`LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero` produces one root vector at a time:
for a single root `α` there are `e ∈ Lα` and `f ∈ L₍₋α₎` with `⁅e, f⁆ = α^∨`.

Chevalley's construction needs those choices made **simultaneously and compatibly**, for all roots
at once: a family `x : Weight K H L → L` with `x α ∈ Lα` and

`⁅x α, x (-α)⁆ = α^∨`   for every root `α`.

This file defines that condition as `TauCeti.IsSl2System` — the name records what it says, that
`(α^∨, x α, x (-α))` is an `sl₂` triple for every root — and proves that such a family exists.

Choosing the root vectors one root at a time does not give a system: the vector chosen for `-α` and
the partner of the vector chosen for `α` are two elements of the same line, and they need not agree.
The construction below therefore chooses one root out of each pair `{α, -α}` and reads off the
vector at the other root from the triple already chosen, which is possible because `α ↦ -α` is a
fixed-point-free involution on the roots. That selection is
`TauCeti.exists_rootPairRepresentatives`, stated separately because every later rescaling of a
normalised family has to make the same choice. The resulting family satisfies the normalisation
on the nose, in both directions, because an `sl₂` triple stays one when `e` and `f` are exchanged
and `h` is negated, and `(-α)^∨ = -α^∨`.

Beyond the definition and the existence theorem, the file records what a system gives: the `sl₂`
triple at each root, the resulting nonvanishing and the identification of each root space as the
line it spans, the Cartan relation `⁅β^∨, x α⁆ = α(β^∨) • x α`, the grading `⁅x α, x β⁆ ∈ L₍α+β₎`
with its vanishing when `α + β` is not a root, that the root vectors together with `H` span `L`,
the Killing pairing of opposite normalized root vectors, and that two systems differ by scalars
`c α` subject to `c α * c (-α) = 1`.

## What this is not

An `IsSl2System` is not yet a Chevalley basis, and this file does not claim it is. A Chevalley basis
asks in addition that the structure constants `c α β` in `⁅x α, x β⁆ = c α β • x (α + β)` be the
integers `±(p + 1)`, `p` the root-string parameter, and Bourbaki's *Chevalley system* asks moreover
that the family be exchanged with its negatives by the Chevalley involution. Neither condition is
imposed here: the normalisation `⁅x α, x (-α)⁆ = α^∨` alone is what pins the Cartan part of the
would-be integral form, and it is a prerequisite of both, since the structure constants are only
defined once the root vectors are.

## Main definitions

* `TauCeti.IsSl2System`: a family of root vectors, one for each weight, normalised so that
  `⁅x α, x (-α)⁆ = α^∨` at every root and carrying no data at a zero weight.

## Main results

* `TauCeti.Weight.ne_neg_of_isNonZero`: negation fixes no root.
* `TauCeti.exists_rootPairRepresentatives`: a set of weights containing exactly one of
  `α` and `-α` for every root `α`.
* `TauCeti.exists_isSl2System`: such a family exists.
* `TauCeti.IsSl2System.isSl2Triple`: `(α^∨, x α, x (-α))` is an `sl₂` triple.
* `TauCeti.IsSl2System.toSubmodule_rootSpace_eq_span`: `x α` spans the root space of `α`.
* `TauCeti.IsSl2System.killingForm_root_neg_eq`: the Killing pairing of opposite normalized root
  vectors is `2 / α((cartanEquivDual H)⁻¹ α)`.
* `TauCeti.IsSl2System.lie_coroot`: the Cartan relation.
* `TauCeti.IsSl2System.isNilpotent_ad_rootVector`: every member of the family acts nilpotently in
  the adjoint representation.
* `TauCeti.IsSl2System.lie_mem_rootSpace_add` and
  `TauCeti.IsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot`: the root grading of the bracket.
* `TauCeti.IsSl2System.exists_lie_eq_smul_of_coe_eq_add`: the structure constants exist.
* `TauCeti.IsSl2System.span_range_sup_toSubmodule_eq_top`: the root vectors and `H` span `L`.
* `TauCeti.IsSl2System.eq_of_forall_isNonZero`: a system is determined by its root vectors.
* `TauCeti.IsSl2System.mul_eq_one_of_eq_smul`: two systems differ by scalars `c` with
  `c α * c (-α) = 1`.
* `TauCeti.IsSl2System.smul`: rescaling by scalars inverse on opposite roots preserves a normalised
  system.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §2, no. 4.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- A family of root vectors normalised against the coroots: `x α` lies in the root space of `α`,
and `⁅x α, x (-α)⁆` is the coroot `α^∨` for every root `α`. Equivalently, `(α^∨, x α, x (-α))` is
an `sl₂` triple for every root `α`, whence the name.

Only the roots carry data: the value at a zero weight is pinned to `0`, so that a system is
determined by its root vectors, as `TauCeti.IsSl2System.eq_of_forall_isNonZero` records. -/
structure IsSl2System (x : Weight K H L → L) : Prop where
  /-- Each member of the family is a root vector for its own root. -/
  mem_rootSpace (α : Weight K H L) : x α ∈ rootSpace H α
  /-- The members at `α` and `-α` are normalised so that their bracket is the coroot of `α`. -/
  lie_neg (α : Weight K H L) (hα : α.IsNonZero) : ⁅x α, x (-α)⁆ = (coroot α : L)
  /-- The family carries no data at a zero weight. -/
  eq_zero_of_isZero (α : Weight K H L) (hα : α.IsZero) : x α = 0

namespace IsSl2System

variable {x y : Weight K H L → L} (hx : IsSl2System x) (α β : Weight K H L)

include hx

/-- The Cartan relation: a coroot acts on a root vector by the corresponding Cartan number. -/
theorem lie_coroot : ⁅(coroot β : L), x α⁆ = α (coroot β) • x α := by
  rw [← LieSubalgebra.coe_bracket_of_module]
  exact lie_eq_smul_of_mem_rootSpace (hx.mem_rootSpace α) (coroot β)

/-- The `sl₂` triple attached to a root by a normalised family of root vectors. -/
theorem isSl2Triple (hα : α.IsNonZero) : IsSl2Triple (coroot α : L) (x α) (x (-α)) where
  h_ne_zero := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero, coroot_eq_zero_iff] using hα
  lie_e_f := hx.lie_neg α hα
  lie_h_e_nsmul := by
    rw [hx.lie_coroot α α, root_apply_coroot hα, two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [hx.lie_coroot (-α) α, Weight.coe_neg, Pi.neg_apply, root_apply_coroot hα, neg_smul,
      two_smul, two_smul]

/-- A root vector of a normalised family is nonzero, being the `e` of an `sl₂` triple. -/
theorem ne_zero (hα : α.IsNonZero) : x α ≠ 0 := (hx.isSl2Triple α hα).e_ne_zero

/-- **Every member of a normalised root-vector system acts nilpotently in the adjoint
representation.** At a root this is the nilpotency of `ad` on a root space; at a zero weight the
member is `0`. This is the nilpotency hypothesis for divided-power exponentials; lattice stability
supplies their integrality separately. -/
theorem isNilpotent_ad_rootVector : _root_.IsNilpotent (LieAlgebra.ad K L (x α)) := by
  rcases eq_or_ne (α : H → K) 0 with h0 | h0
  · rw [hx.eq_zero_of_isZero α h0, map_zero]
    exact IsNilpotent.zero
  · exact LieAlgebra.isNilpotent_ad_of_mem_rootSpace H h0 (hx.mem_rootSpace α)

/-- The Killing pairing of opposite vectors in a normalised root-vector system is
`2 / α((cartanEquivDual H)⁻¹ α)`. -/
theorem killingForm_root_neg_eq (hα : α.IsNonZero) :
    killingForm K L (x α) (x (-α)) =
      2 * (α ((cartanEquivDual H).symm α))⁻¹ := by
  have hdual : ((cartanEquivDual H).symm α : L) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using fun hzero ↦
      root_apply_cartanEquivDual_symm_ne_zero hα (by rw [hzero, map_zero])
  rw [← (smul_left_injective K hdual).eq_iff]
  rw [← lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    (hx.mem_rootSpace α) (hx.mem_rootSpace (-α)), hx.lie_neg α hα, coroot]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, Submodule.coe_smul_of_tower]
  norm_num

/-- A root vector of a normalised family spans its root space. -/
theorem toSubmodule_rootSpace_eq_span (hα : α.IsNonZero) :
    (rootSpace H α).toSubmodule = K ∙ x α :=
  LieAlgebra.IsKilling.toSubmodule_rootSpace_eq_span α hα _ (hx.ne_zero α hα)
    (hx.mem_rootSpace α)

omit [CharZero K] in
/-- The root grading: the bracket of two root vectors lies in the root space of the sum. -/
theorem lie_mem_rootSpace_add : ⁅x α, x β⁆ ∈ rootSpace H ((α : H → K) + β) :=
  mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β (hx.mem_rootSpace α)
    (hx.mem_rootSpace β)

omit [CharZero K] in
/-- Two root vectors bracket to zero when the sum of their roots is not itself a root. -/
theorem lie_eq_zero_of_rootSpace_add_eq_bot (h : rootSpace H ((α : H → K) + β) = ⊥) :
    ⁅x α, x β⁆ = 0 := by
  simpa [h] using hx.lie_mem_rootSpace_add α β

/-- The structure constants of a normalised family: when the sum of two roots is again a root, the
bracket of the two root vectors is a multiple of the root vector at the sum. The normalisation says
nothing about the constants themselves; pinning them to the integers `±(p + 1)` is exactly what
upgrades a normalised family to a Chevalley basis. -/
theorem exists_lie_eq_smul_of_coe_eq_add (γ : Weight K H L) (hγ : γ.IsNonZero)
    (h : (γ : H → K) = (α : H → K) + β) : ∃ c : K, ⁅x α, x β⁆ = c • x γ := by
  have hmem : ⁅x α, x β⁆ ∈ K ∙ x γ := by
    rw [← hx.toSubmodule_rootSpace_eq_span γ hγ, h]
    exact hx.lie_mem_rootSpace_add α β
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

/-- The root vectors of a normalised family span `L` over the Cartan subalgebra: together with `H`
they span the whole Lie algebra. -/
theorem span_range_sup_toSubmodule_eq_top :
    Submodule.span K (Set.range x) ⊔ H.toSubmodule = ⊤ := by
  have htop : (⨆ α : Weight K H L, (rootSpace H α).toSubmodule) = ⊤ :=
    LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K H L)
  rw [← top_le_iff, ← htop]
  refine iSup_le fun α ↦ ?_
  by_cases hα : α.IsNonZero
  · refine le_sup_of_le_left ?_
    rw [hx.toSubmodule_rootSpace_eq_span α hα, Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span (Set.mem_range_self α)
  · refine le_sup_of_le_right (le_of_eq ?_)
    have h0 : (α : H → K) = 0 := not_not.mp hα
    rw [h0, rootSpace_zero_eq K L H]
    simp

variable (hy : IsSl2System y)

include hy

omit [CharZero K] in
/-- A normalised family is determined by its root vectors: two systems agreeing at every root
agree everywhere, since both vanish at a zero weight. -/
theorem eq_of_forall_isNonZero (h : ∀ α : Weight K H L, α.IsNonZero → x α = y α) : x = y := by
  funext α
  by_cases hα : α.IsNonZero
  · exact h α hα
  · rw [hx.eq_zero_of_isZero α (not_not.mp hα), hy.eq_zero_of_isZero α (not_not.mp hα)]

/-- Two normalised families differ by a scalar at each root, since the root spaces are lines. -/
theorem exists_ne_zero_eq_smul (hα : α.IsNonZero) : ∃ c : K, c ≠ 0 ∧ y α = c • x α := by
  have hmem : y α ∈ K ∙ x α := by
    rw [← hx.toSubmodule_rootSpace_eq_span α hα]
    exact hy.mem_rootSpace α
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, fun hc₀ ↦ hy.ne_zero α hα ?_, hc.symm⟩
  rw [← hc, hc₀, zero_smul]

/-- The scalars relating two normalised families are inverse to one another at `α` and `-α`: this
is the one constraint the normalisation `⁅x α, x (-α)⁆ = α^∨` imposes on those scalars. -/
theorem mul_eq_one_of_eq_smul (hα : α.IsNonZero) {c d : K} (hc : y α = c • x α)
    (hd : y (-α) = d • x (-α)) : c * d = 1 := by
  have hcoroot : (coroot α : L) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero, coroot_eq_zero_iff] using hα
  have key : (coroot α : L) = (c * d) • (coroot α : L) := by
    conv_lhs => rw [← hy.lie_neg α hα]
    rw [hc, hd, smul_lie, lie_smul, smul_smul, hx.lie_neg α hα]
  refine smul_left_injective K hcoroot ?_
  simpa only [one_smul] using key.symm

omit [CharZero K] hy in
/-- Rescaling a normalised family by scalars inverse on opposite roots preserves its
normalisation. -/
theorem smul (u : Weight K H L → K) (hu : ∀ α, α.IsNonZero → u α * u (-α) = 1) :
    IsSl2System fun α ↦ u α • x α where
  mem_rootSpace α := Submodule.smul_mem _ _ (hx.mem_rootSpace α)
  lie_neg α hα := by
    rw [smul_lie, lie_smul, smul_smul, hx.lie_neg α hα, hu α hα, one_smul]
  eq_zero_of_isZero α hα := by rw [hx.eq_zero_of_isZero α hα, smul_zero]

end IsSl2System

/-- **A root is not its own negative.** Evaluating at the coroot separates the two: a root takes
the value `2` there, and its negative the value `-2`. -/
theorem Weight.ne_neg_of_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : α ≠ -α := by
  intro h
  have e1 : α (coroot α) = 2 := root_apply_coroot hα
  have e2 : ((-α : Weight K H L) : H → K) (coroot α) = -2 := by
    rw [Weight.coe_neg, Pi.neg_apply, e1]
  rw [← h, e1] at e2
  norm_num at e2

variable (K H) in
/-- **One root out of each opposite pair.** There is a set of weights containing, for every root
`α`, exactly one of `α` and `-α`.

Negation is a fixed-point-free involution on the roots by
`TauCeti.Weight.ne_neg_of_isNonZero`, so a set of representatives for the equivalence relation it
generates is such a set. The choice is what a
construction has to make whenever it treats `α` and `-α` asymmetrically, as the normalisation
`⁅x α, x (-α)⁆ = α^∨` and the rescalings preserving it both force it to. -/
theorem exists_rootPairRepresentatives :
    ∃ s : Set (Weight K H L), ∀ α : Weight K H L, α.IsNonZero → (α ∈ s ↔ -α ∉ s) := by
  classical
  set r : Weight K H L → Weight K H L → Prop := fun α β ↦ β = α ∨ β = -α
  have hrsymm : ∀ {α β : Weight K H L}, r α β → r β α := by
    rintro α β (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (neg_neg α).symm
  have hrtrans : ∀ {α β γ : Weight K H L}, r α β → r β γ → r α γ := by
    rintro α β γ (rfl | rfl) (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg α)
  let S : Setoid (Weight K H L) := ⟨r, fun _ ↦ Or.inl rfl, hrsymm, hrtrans⟩
  have hmem : ∀ β : Weight K H L,
      β ∈ Set.range (fun q : Quotient S ↦ q.out) ↔ (Quotient.mk S β).out = β := by
    refine fun β ↦ ⟨?_, fun h ↦ ⟨Quotient.mk S β, h⟩⟩
    rintro ⟨q, rfl⟩
    rw [Quotient.out_eq]
  refine ⟨Set.range fun q : Quotient S ↦ q.out, fun α hα ↦ ?_⟩
  have hmk : Quotient.mk S (-α) = Quotient.mk S α := Quotient.sound (Or.inr (neg_neg α).symm)
  simp only [hmem, hmk]
  refine ⟨fun h₁ h₂ ↦ Weight.ne_neg_of_isNonZero hα (h₁.symm.trans h₂), fun h ↦ ?_⟩
  rcases Quotient.mk_out (s := S) α with h' | h'
  · exact h'.symm
  · exact absurd (neg_eq_iff_eq_neg.mpr h').symm h

variable (K H) in
/-- **Existence of a normalised family of root vectors.** Root vectors can be chosen for all roots
at once so that `⁅x α, x (-α)⁆ = α^∨` holds at every root, and not merely one root at a time.

The construction picks one root from each pair `{α, -α}`, takes the `sl₂` triple Mathlib attaches
to it, assigns `e` to the chosen root and `f` to its negative, and `0` to a zero weight. -/
theorem exists_isSl2System : ∃ x : Weight K H L → L, IsSl2System x := by
  classical
  -- A set `s` of roots containing exactly one of `α` and `-α`.
  obtain ⟨s, hs⟩ := exists_rootPairRepresentatives K H (L := L)
  have hone : ∀ α : Weight K H L, α.IsNonZero → α ∈ s ∨ (-α) ∈ s := fun α hα ↦
    or_iff_not_imp_left.2 fun h ↦ not_not.1 fun h' ↦ h ((hs α hα).2 h')
  have hnot : ∀ α : Weight K H L, α.IsNonZero → ¬(α ∈ s ∧ (-α) ∈ s) := fun α hα h ↦
    (hs α hα).1 h.1 h.2
  -- An `sl₂` triple at every root, indexed by the root it is attached to.
  have key : ∀ γ : Weight K H L, ∃ p : L × L,
      (γ.IsNonZero → IsSl2Triple (coroot γ : L) p.1 p.2) ∧
        p.1 ∈ rootSpace H γ ∧ p.2 ∈ rootSpace H (-γ) := by
    intro γ
    by_cases hγ : γ.IsNonZero
    · obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hγ
      obtain rfl := ht.h_eq_coroot hγ he hf
      exact ⟨(e, f), fun _ ↦ ht, he, hf⟩
    · exact ⟨(0, 0), fun h ↦ absurd h hγ, zero_mem _, zero_mem _⟩
  choose p hp hp₁ hp₂ using key
  refine ⟨fun α ↦ if α.IsNonZero then (if α ∈ s then (p α).1 else (p (-α)).2) else 0,
    ⟨fun α ↦ ?_, fun α hα ↦ ?_, fun α hα ↦ ite_eq_right (not_not_intro hα)⟩⟩
  · by_cases hα : α.IsNonZero
    · rw [ite_eq_left hα]
      by_cases h : α ∈ s
      · rw [ite_eq_left h]
        exact hp₁ α
      · rw [ite_eq_right h]
        simpa only [Weight.coe_neg, neg_neg] using hp₂ (-α)
    · rw [ite_eq_right hα]
      exact zero_mem _
  · rw [ite_eq_left hα, ite_eq_left hα.neg]
    by_cases h : α ∈ s
    · have h' : (-α) ∉ s := fun h' ↦ hnot α hα ⟨h, h'⟩
      rw [ite_eq_left h, ite_eq_right h', neg_neg]
      exact (hp α hα).lie_e_f
    · have h' : (-α) ∈ s := (hone α hα).resolve_left h
      rw [ite_eq_right h, ite_eq_left h', ← lie_skew, (hp (-α) hα.neg).lie_e_f, coroot_neg]
      simp

end TauCeti
