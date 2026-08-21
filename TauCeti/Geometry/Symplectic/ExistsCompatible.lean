/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.Geometry.Symplectic.Restrict

/-!
# Every symplectic vector space carries a compatible almost complex structure

Tameness and compatibility of an almost complex structure `J` with a symplectic form `ω` are the
standing hypotheses of the analytic Heegaard Floer roadmap. The repository already supplied
compatible structures for several standard models and their transports, but an arbitrary
symplectic form on an arbitrary finite-dimensional real vector space came with no supply of
structures at all. This file removes that gap, proving

`TauCeti.SymplecticForm.exists_compatible`: for every symplectic form `ω` on a finite-dimensional
real vector space `V` there is an almost complex structure `J` with `ω.Compatible J`.

The proof is the classical linear normal-form induction, splitting off one *hyperbolic pair* at a
time rather than diagonalizing a metric. Nondegeneracy provides, for any `x ≠ 0`, a partner `y`
with `ω x y = 1`; the plane `L = span {x, y}` meets its symplectic complement `L^ω` only in `0`, so
`ω` restricts nondegenerately to both, `V = L ⊕ L^ω`, and `ω` is the product of the two
restrictions. On `L` the pair `(x, y)` identifies `(L, ω|_L)` with the standard plane `(ℝ × ℝ, ω₀)`
of `TauCeti.stdSymplecticForm`, which is compatible with
`TauCeti.AlmostComplexStructure.product`; on `L^ω`, whose dimension has dropped by two, the
inductive hypothesis applies. The two structures are recombined by
`TauCeti.SymplecticForm.prod_compatible` and transported back along the splitting. This proves the
nonemptiness part of the standard statement that the space of `ω`-compatible almost complex
structures is nonempty and contractible; contractibility is not addressed here. The conventions
are those of McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.2, which
`TauCeti/Geometry/Symplectic/AlmostComplex.lean` already follows.

## Main declarations

* `TauCeti.SymplecticForm.compatible_prod_transport_of_splitting`: compatible structures on the
  two summands of a symplectic splitting assemble into one on the whole space.
* `TauCeti.SymplecticForm.exists_compatible` and `TauCeti.SymplecticForm.exists_tames`: the
  existence theorems.
* `TauCeti.SymplecticForm.even_finrank` and `TauCeti.SymplecticForm.isEmpty_of_odd_finrank`: a
  symplectic vector space has even dimension, so an odd-dimensional space carries no symplectic
  form at all.
-/

public section

namespace TauCeti

namespace SymplecticForm

open Module

universe u

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Compatible structures on the two halves of a symplectic splitting `V = L ⊕ L^ω` assemble into
a compatible structure on `V`. -/
lemma compatible_prod_transport_of_splitting (ω : SymplecticForm V) {L : Submodule ℝ V}
    (hcompl : IsCompl L (ω.orthogonal L))
    (JL : AlmostComplexStructure L) (JL' : AlmostComplexStructure (ω.orthogonal L))
    (hJL : (ω.restrict L (ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl
      hcompl.disjoint)).Compatible JL)
    (hJL' : (ω.restrict (ω.orthogonal L)
      (ω.nondegenerate_restrict_orthogonal_of_isCompl hcompl)).Compatible JL') :
    ω.Compatible
      ((JL.prod JL').transport (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl)) := by
  have hcomp := (prod_compatible hJL hJL').transport
    (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl)
  rwa [isSymplectomorphism_iff_transport_eq.1
    (ω.isSymplectomorphism_prodEquivOfIsCompl hcompl)] at hcomp

/-! ### Hyperbolic pairs and the standard plane -/

section Plane

variable (ω : SymplecticForm V) {x y : V}

/-- The parametrization `(a, b) ↦ a • x + b • y` of the plane spanned by a pair of vectors. -/
private def pairMap (x y : V) : (ℝ × ℝ) →ₗ[ℝ] V :=
  (LinearMap.toSpanSingleton ℝ V x).coprod (LinearMap.toSpanSingleton ℝ V y)

private lemma pairMap_apply (x y : V) (p : ℝ × ℝ) : pairMap x y p = p.1 • x + p.2 • y := rfl

private lemma pairMap_injective (h : ω x y = 1) : Function.Injective (pairMap x y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  rw [pairMap_apply] at hp
  have ha : p.1 = 0 := by
    have : ω (p.1 • x + p.2 • y) y = 0 := by rw [hp]; simp
    simpa [h] using this
  have hb : p.2 = 0 := by
    have : ω x (p.1 • x + p.2 • y) = 0 := by rw [hp]; simp
    simpa [h] using this
  exact Prod.ext_iff.2 ⟨ha, hb⟩

private lemma range_pairMap (x y : V) :
    LinearMap.range (pairMap x y) = Submodule.span ℝ ({x, y} : Set V) := by
  simp [pairMap, LinearMap.range_coprod, LinearMap.range_toSpanSingleton,
    Submodule.span_insert]

/-- The plane spanned by a hyperbolic pair `x, y` with `ω x y = 1`, presented as a linear copy of
the standard plane `ℝ × ℝ`. -/
private noncomputable def planeEquiv (h : ω x y = 1) :
    (ℝ × ℝ) ≃ₗ[ℝ] (Submodule.span ℝ ({x, y} : Set V)) :=
  (LinearEquiv.ofInjective (pairMap x y) (ω.pairMap_injective h)).trans
    (LinearEquiv.ofEq _ _ (range_pairMap x y))

private lemma coe_planeEquiv_apply (h : ω x y = 1) (p : ℝ × ℝ) :
    ((ω.planeEquiv h p : Submodule.span ℝ ({x, y} : Set V)) : V) = p.1 • x + p.2 • y := rfl

/-- Read through the parametrization by a hyperbolic pair, `ω` becomes the standard symplectic
form of the plane `ℝ × ℝ`. -/
private lemma isSymplectomorphism_planeEquiv (h : ω x y = 1)
    (hL : (ω.toBilinForm.restrict (Submodule.span ℝ ({x, y} : Set V))).Nondegenerate) :
    IsSymplectomorphism (stdSymplecticForm (V := ℝ))
      (ω.restrict (Submodule.span ℝ ({x, y} : Set V)) hL) (ω.planeEquiv h) := by
  rw [isSymplectomorphism_iff]
  intro p q
  simp only [restrict_apply, coe_planeEquiv_apply, ω.apply_smul_add_smul, h,
    stdSymplecticForm_apply, Real.inner_apply]
  ring

/-- The plane spanned by a hyperbolic pair carries a compatible almost complex structure,
transported from the standard compatible triple on `ℝ × ℝ`. -/
private lemma exists_compatible_restrict_span_pair (h : ω x y = 1)
    (hL : (ω.toBilinForm.restrict (Submodule.span ℝ ({x, y} : Set V))).Nondegenerate) :
    ∃ J : AlmostComplexStructure (Submodule.span ℝ ({x, y} : Set V)),
      (ω.restrict (Submodule.span ℝ ({x, y} : Set V)) hL).Compatible J := by
  refine ⟨(AlmostComplexStructure.product ℝ).transport (ω.planeEquiv h), ?_⟩
  have hcomp := (stdSymplecticForm_compatible_product (V := ℝ)).transport (ω.planeEquiv h)
  rwa [isSymplectomorphism_iff_transport_eq.1 (ω.isSymplectomorphism_planeEquiv h hL)] at hcomp

end Plane

/-! ### Existence of a compatible almost complex structure -/

/-- On a zero-dimensional space the zero endomorphism is an almost complex structure, and it is
compatible with the unique symplectic form. -/
private lemma exists_compatible_of_subsingleton [Subsingleton V] (ω : SymplecticForm V) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J := by
  refine ⟨⟨0, by ext v; simp [Subsingleton.elim v (0 : V)]⟩, Compatible.of_tames ?_ ?_⟩
  · rw [invariant_iff]
    intro v w
    rw [Subsingleton.elim v (0 : V), Subsingleton.elim w (0 : V)]
    simp
  · exact fun v hv => absurd (Subsingleton.elim v (0 : V)) hv

private theorem exists_compatible_aux (n : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U] (ω : SymplecticForm U),
      finrank ℝ U ≤ n → ∃ J : AlmostComplexStructure U, ω.Compatible J := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U _ _ _ ω hn
    rcases subsingleton_or_nontrivial U with _ | _
    · exact ω.exists_compatible_of_subsingleton
    obtain ⟨x, hx⟩ := exists_ne (0 : U)
    obtain ⟨y, hxy⟩ := ω.exists_apply_eq_one hx
    have hdisj : Disjoint (Submodule.span ℝ ({x, y} : Set U))
        (ω.orthogonal (Submodule.span ℝ ({x, y} : Set U))) :=
      ω.disjoint_span_pair_orthogonal (by simp [hxy])
    have hcompl : IsCompl (Submodule.span ℝ ({x, y} : Set U))
        (ω.orthogonal (Submodule.span ℝ ({x, y} : Set U))) :=
      (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint ω.isRefl).2 hdisj
    obtain ⟨JL, hJL⟩ :=
      ω.exists_compatible_restrict_span_pair hxy
        (ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl hcompl.disjoint)
    have hxmem : x ∈ Submodule.span ℝ ({x, y} : Set U) := Submodule.subset_span (by simp)
    have hUpos : 0 < finrank ℝ U := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx⟩
    have hLpos : 0 < finrank ℝ (Submodule.span ℝ ({x, y} : Set U)) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hxmem⟩, by simpa using hx⟩
    have hlt : finrank ℝ (ω.orthogonal (Submodule.span ℝ ({x, y} : Set U))) < finrank ℝ U := by
      rw [ω.finrank_orthogonal _]
      exact Nat.sub_lt hUpos hLpos
    obtain ⟨JL', hJL'⟩ := ih _ (lt_of_lt_of_le hlt hn)
      (ω.restrict _ (ω.nondegenerate_restrict_orthogonal_of_isCompl hcompl)) le_rfl
    exact ⟨_, ω.compatible_prod_transport_of_splitting hcompl JL JL' hJL hJL'⟩

/-- **Every symplectic vector space carries a compatible almost complex structure.**

For a symplectic form `ω` on a finite-dimensional real vector space there is an almost complex
structure `J` that is `ω`-invariant and satisfies `ω(v, Jv) > 0` for `v ≠ 0`. In particular the
pointwise compatibility hypothesis on a symplectic vector space is satisfiable; the smooth
fibrewise statement is not proved here. -/
theorem exists_compatible [FiniteDimensional ℝ V] (ω : SymplecticForm V) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J :=
  exists_compatible_aux _ ω le_rfl

/-- Every finite-dimensional symplectic vector space is tamed by some almost complex structure. -/
theorem exists_tames [FiniteDimensional ℝ V] (ω : SymplecticForm V) :
    ∃ J : AlmostComplexStructure V, ω.Tames J :=
  let ⟨J, hJ⟩ := ω.exists_compatible
  ⟨J, hJ.tames⟩

/-- A finite-dimensional symplectic vector space has even dimension. -/
theorem even_finrank [FiniteDimensional ℝ V] (ω : SymplecticForm V) : Even (finrank ℝ V) :=
  let ⟨J, _⟩ := ω.exists_compatible
  J.even_finrank_real

/-- A real vector space of odd dimension carries no symplectic form. -/
theorem isEmpty_of_odd_finrank [FiniteDimensional ℝ V] (h : Odd (finrank ℝ V)) :
    IsEmpty (SymplecticForm V) :=
  ⟨fun ω => (Nat.not_even_iff_odd.2 h) ω.even_finrank⟩

end SymplecticForm

end TauCeti
