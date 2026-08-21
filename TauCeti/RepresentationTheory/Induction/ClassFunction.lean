/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction

/-!
# The induced class function

Induction of representations along a finite-index subgroup `S ≤ G` sends a character of `S` to a
character of `G`, by the coset-representative formula
`TauCeti.character_indFDRep_sum_quotient`.  That formula makes sense for an arbitrary function on
`S`, and this file takes it as the definition of the **induced class function**
`TauCeti.indClassFun`.  It is the linearization of induction on characters, and the map that turns
the restriction/induction pair into an adjoint pair on class functions.

Nothing here mentions a representation, so the file sits below
`TauCeti.RepresentationTheory.Induction.Character`, which imports it to identify the induced
character with the induced class function of a character (`TauCeti.indClassFun_ofFDRep_character`)
and to deduce `TauCeti.character_ind` from `TauCeti.indClassFun_eq_natCard_inv_mul_sum`.

## Main definitions

* `TauCeti.indTerm f g x`: the summand attached to a representative `x`, namely `f (x⁻¹ g x)`
  when `x⁻¹ g x` lies in the subgroup and `0` otherwise.  It is the summand of the
  induced-character formula too, which the character file uses at `f = ρ.character`, together
  with the coset-invariance lemma `TauCeti.indTerm_eq_of_mk_eq` and the evaluations
  `TauCeti.indTerm_conj` and `TauCeti.indTerm_one`.
* `TauCeti.indClassFun S f`: the function `G → k` obtained from `f : S → k` by summing `f` over
  those left coset representatives that conjugate `g` into `S`.  There is no division by `|S|`,
  so it needs no invertibility hypothesis and no more than an additive commutative monoid of
  coefficients.
* `TauCeti.indClassFunAddHom S`: the same construction packaged as an additive map
  `(S → k) →+ (G → k)`, which is what lets a property be propagated through the additive
  generation of an `AddSubgroup` of functions.
* `TauCeti.ClassFunction.ind S`: the same construction packaged as a `k`-linear map
  `ClassFunction k S →ₗ[k] ClassFunction k G`.

## Main statements

* `TauCeti.indClassFun_mem_classFunction`: the induced function of a class function is a class
  function.
* `TauCeti.natCard_mul_indClassFun`: the group-sum form, `|S| · (Ind f)(g) = ∑_{x ∈ G} f(x⁻¹gx)`,
  and its averaged corollary `TauCeti.indClassFun_eq_natCard_inv_mul_sum`.
* `TauCeti.indClassFun_comp_subtype_mul`: the **projection formula**,
  `Ind_S^G ((Res_S f) · ψ) = f · Ind_S^G ψ` for a class function `f` of `G`.

Frobenius reciprocity for class functions, `⟨Ind f, h⟩_G = ⟨f, Res h⟩_S`, is
`TauCeti.frobenius_reciprocity_classFunction`; it needs the pairing, so it lives with the other
reciprocities in `TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity`.

## Implementation notes

The definition sums over `Quotient.out` representatives of `G ⧸ S`, so it literally matches
`TauCeti.character_indFDRep_sum_quotient`.  For a general `f` the individual summands depend on
that choice of representatives; being a class function is a sufficient condition for them not to,
and that is what `TauCeti.indClassFun_mem_classFunction` extracts, in the form of conjugation
invariance of the total sum.  It is the only regime the results below use.

`TauCeti.indTerm` and the lemmas that evaluate it are shared, not internal to this file:
`TauCeti.RepresentationTheory.Induction.Character` sums it over right cosets and
`TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity` sums it over all of `G`.  Only
`indTerm_mul`, which serves the proof of `TauCeti.indTerm_eq_of_mk_eq` alone, is private.

## References

* [Induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
  Layer 6 (`indClassFun`).
* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.2.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}

section AddCommMonoid

variable [AddCommMonoid k]

open scoped Classical in
/-- The summand of the induced class function attached to a representative `x`: the value of `f`
at `x⁻¹ * g * x` when that element lies in the subgroup, and `0` otherwise.

Specialized to the character of a representation of `S` this is the summand of the
induced-character formula `TauCeti.character_indFDRep_sum_quotient`. -/
noncomputable def indTerm (f : S → k) (g x : G) : k :=
  if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0

open scoped Classical in
/-- The defining case split of `TauCeti.indTerm`. -/
theorem indTerm_apply (f : S → k) (g x : G) :
    indTerm f g x = if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 :=
  (rfl)

/-- Conjugating the argument of the summand translates the representative. -/
theorem indTerm_conj (f : S → k) (g x c : G) :
    indTerm f (c * g * c⁻¹) x = indTerm f g (c⁻¹ * x) := by
  classical
  have h : x⁻¹ * (c * g * c⁻¹) * x = (c⁻¹ * x)⁻¹ * g * (c⁻¹ * x) := by group
  simp only [indTerm, h]

open scoped Classical in
/-- The value of the summand at the identity representative. -/
theorem indTerm_one (f : S → k) (g : G) :
    indTerm f g 1 = if h : g ∈ S then f ⟨g, h⟩ else 0 := by
  simp [indTerm]

open scoped Classical in
/-- **The induced class function.**  For `f : S → k` and `g : G`, sum `f (t⁻¹ g t)` over those
left coset representatives `t` of `S` in `G` with `t⁻¹ g t ∈ S`.

The sum has no division by `|S|`, so the definition needs nothing of the coefficients beyond
addition; the averaged group-sum form is `TauCeti.indClassFun_eq_natCard_inv_mul_sum`.  On a
character it is the character of the induced representation, by
`TauCeti.indClassFun_ofFDRep_character`.

The representatives are the fixed `Quotient.out` ones, so this is a function of `f` alone; but it
is only for a class function `f` that the individual summands, and hence the sum, are independent
of the representatives chosen.  `TauCeti.ClassFunction.ind` is the bundled form on
`TauCeti.ClassFunction k S`, and is the canonical API. -/
noncomputable def indClassFun (S : Subgroup G) [S.FiniteIndex] (f : S → k) : G → k := fun g =>
  letI := Fintype.ofFinite (G ⧸ S)
  ∑ t : G ⧸ S, indTerm f g (Quotient.out t)

open scoped Classical in
/-- The defining coset sum of `TauCeti.indClassFun`. -/
theorem indClassFun_apply [S.FiniteIndex] (f : S → k) (g : G) :
    indClassFun S f g =
      letI := Fintype.ofFinite (G ⧸ S)
      ∑ t : G ⧸ S,
        if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ S then
          f ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩
        else 0 :=
  (rfl)

/-! ### Additivity -/

private theorem indTerm_zero (g x : G) : indTerm (S := S) (0 : S → k) g x = 0 := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]

private theorem indTerm_add (f₁ f₂ : S → k) (g x : G) :
    indTerm (f₁ + f₂) g x = indTerm f₁ g x + indTerm f₂ g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]

/-- Induction of class functions kills the zero function. -/
@[simp]
theorem indClassFun_zero [S.FiniteIndex] : indClassFun S (0 : S → k) = 0 := by
  funext g
  simp [indClassFun, indTerm_zero]

/-- Induction of class functions is additive. -/
@[simp]
theorem indClassFun_add [S.FiniteIndex] (f₁ f₂ : S → k) :
    indClassFun S (f₁ + f₂) = indClassFun S f₁ + indClassFun S f₂ := by
  funext g
  simp [indClassFun, indTerm_add, Finset.sum_add_distrib]

/-- **Induction of functions on a finite-index subgroup, as an additive map.**  It is
`TauCeti.indClassFun` bundled by the two lemmas above, which is what lets a property be propagated
through the additive generation of an `AddSubgroup` of functions; `TauCeti.ClassFunction.ind` is
the finer bundling, as a `k`-linear map on class functions. -/
noncomputable def indClassFunAddHom (S : Subgroup G) [S.FiniteIndex] :
    (S → k) →+ (G → k) where
  toFun := indClassFun S
  map_zero' := indClassFun_zero
  map_add' := indClassFun_add

private theorem indClassFunAddHom_apply_aux (S : Subgroup G) [S.FiniteIndex] (ψ : S → k) :
    indClassFunAddHom S ψ = indClassFun S ψ :=
  rfl

@[simp]
theorem indClassFunAddHom_apply (S : Subgroup G) [S.FiniteIndex] (ψ : S → k) :
    indClassFunAddHom S ψ = indClassFun S ψ :=
  indClassFunAddHom_apply_aux S ψ

end AddCommMonoid

section Semiring

variable [Semiring k]

private theorem indTerm_smul (c : k) (f : S → k) (g x : G) :
    indTerm (c • f) g x = c * indTerm f g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]

/-- Induction of class functions is homogeneous. -/
@[simp]
theorem indClassFun_smul [S.FiniteIndex] (c : k) (f : S → k) :
    indClassFun S (c • f) = c • indClassFun S f := by
  funext g
  simp [indClassFun, indTerm_smul, Finset.mul_sum]

/-! ### Conjugation invariance -/

section ClassFun

variable {f : S → k}

/-- Replacing a representative `x` by `x * s` for `s` in the subgroup does not change the
summand, because `f` is constant on conjugacy classes of the subgroup.

It is private: `TauCeti.indTerm_eq_of_mk_eq` is the form every consumer uses. -/
private theorem indTerm_mul (hf : f ∈ ClassFunction k S) (g x : G) (s : S) :
    indTerm f g (x * s) = indTerm f g x := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ S
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∈ S := by
      simpa [mul_assoc] using S.mul_mem (S.mul_mem (S.inv_mem s.2) hx) s.2
    rw [indTerm, dite_eq_left hxs, indTerm, dite_eq_left hx]
    have helem : (⟨(x * (s : G))⁻¹ * g * (x * s), hxs⟩ : S) =
        s⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [helem, ClassFunction.mem_iff.mp hf ⟨x⁻¹ * g * x, hx⟩ s⁻¹]
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∉ S := by
      intro h
      exact hx (by simpa [mul_assoc] using S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2))
    rw [indTerm, dite_eq_right hxs, indTerm, dite_eq_right hx]

/-- The summand of the induced class function depends only on the left coset of its
representative. -/
theorem indTerm_eq_of_mk_eq (hf : f ∈ ClassFunction k S) (g x y : G)
    (hxy : (QuotientGroup.mk x : G ⧸ S) = QuotientGroup.mk y) :
    indTerm f g x = indTerm f g y := by
  have hs : x⁻¹ * y ∈ S := QuotientGroup.leftRel_apply.mp (Quotient.exact' hxy)
  have hy : x * ((⟨x⁻¹ * y, hs⟩ : S) : G) = y := by simp
  rw [← hy, indTerm_mul hf]

/-- **The induced function of a class function is a class function.** -/
theorem indClassFun_mem_classFunction [S.FiniteIndex] (hf : f ∈ ClassFunction k S) :
    indClassFun S f ∈ ClassFunction k G := by
  refine ClassFunction.mem_iff.mpr fun g c => ?_
  let := Fintype.ofFinite (G ⧸ S)
  calc indClassFun S f (c * g * c⁻¹)
      = ∑ t : G ⧸ S, indTerm f g (c⁻¹ * Quotient.out t) := by
        simp only [indClassFun, indTerm_conj]
    _ = ∑ t : G ⧸ S, indTerm f g (Quotient.out ((c⁻¹ : G) • t)) := by
        refine Finset.sum_congr rfl fun t _ => indTerm_eq_of_mk_eq hf _ _ _ ?_
        rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out, QuotientGroup.out_eq']
    _ = ∑ t : G ⧸ S, indTerm f g (Quotient.out t) :=
        Fintype.sum_equiv (MulAction.toPerm (c⁻¹ : G)) _ _ fun _ => rfl
    _ = indClassFun S f g := rfl

end ClassFun

/-! ### The group-sum form -/

open scoped Classical in
/-- **The group-sum form of the induced class function**, with no division: summing the
conjugation summand over all of `G` rather than over coset representatives multiplies the induced
class function by the order of the subgroup. -/
theorem natCard_mul_indClassFun [Fintype G] {f : S → k} (hf : f ∈ ClassFunction k S) (g : G) :
    (Nat.card S : k) * indClassFun S f g =
      ∑ x : G, if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 := by
  let := Fintype.ofFinite (G ⧸ S)
  let e : G ≃ (G ⧸ S) × S := Subgroup.groupEquivQuotientProdSubgroup
  have hterm (q : G ⧸ S) (s : S) : indTerm f g (e.symm (q, s)) = indTerm f g q.out := by
    refine indTerm_eq_of_mk_eq hf _ _ _ ?_
    exact (congrArg Prod.fst (e.apply_symm_apply (q, s))).trans (Quotient.out_eq' q).symm
  calc (Nat.card S : k) * indClassFun S f g
      = ∑ q : G ⧸ S, ∑ _s : S, indTerm f g q.out := by
        simp [indClassFun, Finset.mul_sum]
    _ = ∑ q : G ⧸ S, ∑ s : S, indTerm f g (e.symm (q, s)) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ => (hterm q s).symm
    _ = ∑ x : G, indTerm f g x := by
        rw [← e.symm.sum_comp (fun x => indTerm f g x), Fintype.sum_prod_type]
    -- the remaining step only unfolds the summand
    _ = _ := rfl

/-! ### The projection formula -/

section Projection

variable {f : G → k}

/-- **The projection formula, on a single summand.**  The summand only ever evaluates a function on
`S` at a conjugate of `g`, so multiplying by the restriction of a class function `f` of `G`
multiplies the summand by the constant `f g`.

It is private: `TauCeti.indClassFun_comp_subtype_mul` is the projection formula every consumer
uses. -/
private theorem indTerm_comp_subtype_mul (hf : f ∈ ClassFunction k G) (ψ : S → k) (g x : G) :
    indTerm ((fun s : S => f s) * ψ) g x = f g * indTerm ψ g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S
  · have hconj : f (x⁻¹ * g * x) = f g := by
      simpa using ClassFunction.mem_iff.mp hf g x⁻¹
    simp [indTerm, h, hconj]
  · simp [indTerm, h]

/-- **The projection formula for the induced class function**:
`Ind_S^G ((Res_S f) · ψ) = f · Ind_S^G ψ` for a class function `f` of `G` and an arbitrary
function `ψ` on `S`.

This is the class-function shadow of the tensor identity `TauCeti.indProjection`, and it is what
makes induction a map of modules over the ring of class functions: an induced function may be
multiplied by `f` either before or after inducing.  Only `f` is required to be a class function;
the identity is pointwise in `ψ`. -/
theorem indClassFun_comp_subtype_mul [S.FiniteIndex] (hf : f ∈ ClassFunction k G) (ψ : S → k) :
    indClassFun S ((fun s : S => f s) * ψ) = f * indClassFun S ψ := by
  funext g
  simp only [indClassFun, Pi.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => indTerm_comp_subtype_mul hf ψ g _

end Projection

/-! ### The induced class function as a linear map -/

namespace ClassFunction

/-- **Induction of class functions**, packaged as a `k`-linear map
`ClassFunction k S →ₗ[k] ClassFunction k G`. -/
noncomputable def ind (S : Subgroup G) [S.FiniteIndex] :
    ClassFunction k S →ₗ[k] ClassFunction k G where
  toFun f := ⟨indClassFun S f.1, indClassFun_mem_classFunction f.2⟩
  map_add' f₁ f₂ := Subtype.ext (indClassFun_add f₁.1 f₂.1)
  map_smul' c f := Subtype.ext (indClassFun_smul c f.1)

@[simp]
theorem ind_apply [S.FiniteIndex] (f : ClassFunction k S) (g : G) :
    (ind S f).1 g = indClassFun S f.1 g :=
  (rfl)

end ClassFunction

end Semiring

/-! ### Averaging -/

section Field

variable [Field k]

open scoped Classical in
/-- **The averaged group-sum form of the induced class function.**  The order of the subgroup must
be invertible in the coefficient field; without that hypothesis
`TauCeti.natCard_mul_indClassFun` is the division-free identity to use. -/
theorem indClassFun_eq_natCard_inv_mul_sum [Fintype G] {f : S → k}
    (hS : IsUnit (Nat.card S : k)) (hf : f ∈ ClassFunction k S) (g : G) :
    indClassFun S f g =
      (Nat.card S : k)⁻¹ * ∑ x : G, if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 := by
  rw [← natCard_mul_indClassFun hf g, ← mul_assoc, inv_mul_cancel₀ hS.ne_zero, one_mul]

end Field

end TauCeti
