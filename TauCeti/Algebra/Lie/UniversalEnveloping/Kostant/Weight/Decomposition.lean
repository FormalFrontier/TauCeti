/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.LinearAlgebra.Eigenspace.Binomial

/-!
# Admissible lattices decompose into weight components

Let `U_ℤ = kostantForm e h` be a Kostant integral form in `U(L)`, acting through `ρ` on a rational
vector space `V`, and let `M ≤ V` be a `U_ℤ`-stable additive subgroup — an *admissible lattice*
once it is also a lattice. A designated Cartan vector `h j` acts on `V` by an operator whose
eigenvalues on a representation with integral weights are integers, and the question this file
answers is whether an element of `M` has *all* of its weight components in `M`. It does, and this
is what makes the weight components of an admissible lattice into lattices themselves.

Nothing about `M` forces this: `M` is only assumed stable, and the projection onto a weight space
is a Lagrange interpolation polynomial in the Cartan operator with rational coefficients, so it
does not obviously preserve an integral structure. The point is that the Kostant form contains not
just the Cartan vector `h j` but all of its binomial coefficients `(h j choose k)`, and even all
the coefficients `(h j - a choose k)` of its integer translates
(`TauCeti.UniversalEnvelopingAlgebra.ringChoose_ι_sub_intCast_mem_kostantForm`). Those act on a
vector of weight `a + i` by the ordinary binomial coefficient `(i choose k)`, and Newton's
forward-difference formula (`TauCeti.exists_forall_sum_mul_choose_eq`) writes *any* prescribed
integer values on `i = 0, …, N` as an integral combination of them. Choosing the values to be the
indicator of a single weight produces a genuine projector inside `U_ℤ`, which is
`TauCeti.UniversalEnvelopingAlgebra.exists_mem_kostantForm_forall_apply_eq`.

A weight of the whole Cartan family is an integer-valued function on the Cartan indices, and two
distinct weights differ at some single index, so grouping summands by their value there reduces
the simultaneous statement
`TauCeti.UniversalEnvelopingAlgebra.jointWeightComponent_mem_of_kostantStable`
to the one-index one. That is Humphreys' Lemma 27.1: an admissible lattice contains every joint
weight component of each of its elements, so it is the direct sum of the lattices it cuts out of the
weight spaces. For a single Cartan direction the decomposition is packaged as a submodule identity,
`TauCeti.UniversalEnvelopingAlgebra.iSup_weightComponent_eq` together with
`TauCeti.UniversalEnvelopingAlgebra.iSupIndep_weightComponent`.

This is the input the pinned Chevalley--Demazure group scheme of Layer 9 needs before its split
maximal torus can be written down, since the torus is exactly what acts by a character on each
weight component.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.exists_mem_kostantForm_forall_apply_eq`: prescribed integer
  scalars on a window of consecutive weights are realized by a single element of the Kostant form.
* `TauCeti.UniversalEnvelopingAlgebra.weightComponent_mem_of_kostantStable`: every weight component
  for one Cartan vector of an element of a Kostant-stable subgroup lies in that subgroup.
* `TauCeti.UniversalEnvelopingAlgebra.jointWeightComponent_mem_of_kostantStable`: the same for the
  joint weight components of the whole Cartan family.
* `TauCeti.UniversalEnvelopingAlgebra.weightComponent`: the weight components of a `ℤ`-submodule.
* `TauCeti.UniversalEnvelopingAlgebra.iSup_weightComponent_eq` and
  `TauCeti.UniversalEnvelopingAlgebra.iSupIndep_weightComponent`: a Kostant-stable `ℤ`-submodule of
  a module with integral weights is the direct sum of its weight components.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Finset

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

attribute [local instance] TauCeti.moduleNNRat

variable (e : ι → L) (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

/-! ## Separating weights inside the Kostant form -/

/-- **The Kostant form separates the weights in a window.** Given a base weight `a`, a window
length `N` and prescribed integer values `g 0, …, g N`, some element of the Kostant integral form
acts by the scalar `g i` on every vector of weight `a + i`, simultaneously for all `i ≤ N`.

The element is the integral combination `∑ k ≤ N, c k • (h j - a choose k)` supplied by Newton's
forward-difference formula; each summand lies in the form because the Cartan binomial coefficients
of a designated Cartan vector survive integer translation of their argument. -/
theorem exists_mem_kostantForm_forall_apply_eq (j : κ) (a : ℤ) (N : ℕ) (g : ℕ → ℤ) :
    ∃ u ∈ kostantForm e h, ∀ i ≤ N, ∀ x : V,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) x = ((a + i : ℤ) : ℚ) • x →
        ρ u x = (g i : ℚ) • x := by
  obtain ⟨c, hc⟩ := TauCeti.exists_forall_sum_mul_choose_eq N g
  refine ⟨∑ k ∈ range (N + 1), c k •
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j) -
      (a : _root_.UniversalEnvelopingAlgebra ℚ L)) k, ?_, ?_⟩
  · exact sum_mem fun k _ =>
      zsmul_mem (ringChoose_ι_sub_intCast_mem_kostantForm e h j a k) (c k)
  · intro i hi x hx
    have hshift : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j) -
        (a : _root_.UniversalEnvelopingAlgebra ℚ L)) x = (i : ℚ) • x := by
      rw [map_sub, map_intCast, LinearMap.sub_apply, hx, Module.End.intCast_apply,
        ← Int.cast_smul_eq_zsmul ℚ a x, ← sub_smul]
      norm_num
    have hterm : ∀ k ∈ range (N + 1),
        (ρ (c k • Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j) -
          (a : _root_.UniversalEnvelopingAlgebra ℚ L)) k)) x =
          ((c k : ℚ) * (i.choose k : ℚ)) • x := by
      intro k _
      rw [map_zsmul, LinearMap.smul_apply, Ring.map_choose,
        TauCeti.ringChoose_end_apply_of_apply_eq_natCast_smul hshift k,
        ← Int.cast_smul_eq_zsmul ℚ (c k), smul_smul]
    rw [map_sum, LinearMap.sum_apply, sum_congr rfl hterm, ← sum_smul]
    congr 1
    exact_mod_cast hc i hi

/-! ## Weight components of a stable subgroup -/

/-- **A Kostant-stable subgroup contains the weight components of its elements.** If a vector of
`M` is written as a finite sum of vectors of pairwise distinct integer weights for the Cartan
vector `h j`, then each of those vectors already lies in `M`.

This is the integrality statement behind Humphreys' Lemma 27.1: the projector onto a single weight
has rational coefficients as a polynomial in the Cartan operator, yet it is realized inside the
Kostant integral form. -/
theorem weightComponent_mem_of_kostantStable
    {S : Type*} [SetLike S V] {M : S}
    (hM : ∀ u ∈ kostantForm e h, ∀ x ∈ M, ρ u x ∈ M) (j : κ)
    {s : Finset ℤ} {w : ℤ → V}
    (hw : ∀ m ∈ s, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) (w m) = (m : ℚ) • w m)
    (hv : (∑ m ∈ s, w m) ∈ M) {m₀ : ℤ} (hm₀ : m₀ ∈ s) : w m₀ ∈ M := by
  classical
  have hs : s.Nonempty := ⟨m₀, hm₀⟩
  obtain ⟨u, hu, hu'⟩ := exists_mem_kostantForm_forall_apply_eq e h ρ j (s.min' hs)
    (s.max' hs - s.min' hs).toNat (fun i => if s.min' hs + i = m₀ then 1 else 0)
  have hterm : ∀ m ∈ s, ρ u (w m) = if m = m₀ then w m else 0 := by
    intro m hm
    have hmin : s.min' hs ≤ m := s.min'_le m hm
    have hmax : m ≤ s.max' hs := s.le_max' m hm
    have hval : s.min' hs + ((m - s.min' hs).toNat : ℤ) = m := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have hle : (m - s.min' hs).toNat ≤ (s.max' hs - s.min' hs).toNat := by omega
    have := hu' _ hle (w m) (by rw [hw m hm, hval])
    rw [this, hval]
    by_cases hmm : m = m₀ <;> simp [hmm]
  have key : ρ u (∑ m ∈ s, w m) = w m₀ := by
    rw [map_sum, sum_congr rfl hterm, sum_ite_eq' s m₀ w]
    simp [hm₀]
  exact key ▸ hM u hu _ hv

/-- **A Kostant-stable subgroup contains the joint weight components of its elements.** A weight
is an integer-valued function on the designated Cartan vectors, and a vector of `M` written as a
finite sum of simultaneous eigenvectors of pairwise distinct weights has each summand in `M`.

Two distinct weights differ at some Cartan index, so grouping the summands by their value at that
index and applying the one-index statement strips off at least one weight while keeping `l₀`. The
induction is on the set of weights involved, which shrinks strictly at every step. -/
theorem jointWeightComponent_mem_of_kostantStable
    {S : Type*} [SetLike S V] {M : S}
    (hM : ∀ u ∈ kostantForm e h, ∀ x ∈ M, ρ u x ∈ M)
    {s : Finset (κ → ℤ)} {w : (κ → ℤ) → V}
    (hw : ∀ l ∈ s, ∀ j : κ,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) (w l) = (l j : ℚ) • w l)
    (hv : (∑ l ∈ s, w l) ∈ M) {l₀ : κ → ℤ} (hl₀ : l₀ ∈ s) : w l₀ ∈ M := by
  classical
  revert hw hv hl₀
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hw hv hl₀
    by_cases hcase : ∀ l ∈ s, l = l₀
    · rw [Finset.eq_singleton_iff_unique_mem.2 ⟨hl₀, hcase⟩, Finset.sum_singleton] at hv
      exact hv
    · push Not at hcase
      obtain ⟨l₁, hl₁s, hl₁⟩ := hcase
      obtain ⟨j, hj⟩ : ∃ j : κ, l₁ j ≠ l₀ j := by
        by_contra hcon
        push Not at hcon
        exact hl₁ (funext hcon)
      refine ih (s.filter fun l => l j = l₀ j) (Finset.filter_ssubset.2 ⟨l₁, hl₁s, hj⟩)
        (fun l hl j' => hw l (Finset.mem_filter.1 hl).1 j') ?_
        (Finset.mem_filter.2 ⟨hl₀, rfl⟩)
      refine weightComponent_mem_of_kostantStable e h ρ hM j (s := s.image fun l => l j)
        (w := fun m => ∑ l ∈ s.filter fun l => l j = m, w l) (fun m _ => ?_) ?_
        (Finset.mem_image_of_mem _ hl₀)
      · simp only [map_sum, Finset.smul_sum]
        exact Finset.sum_congr rfl fun l hl => by
          rw [hw l (Finset.mem_filter.1 hl).1 j, (Finset.mem_filter.1 hl).2]
      · rw [Finset.sum_fiberwise_of_maps_to (fun l hl => Finset.mem_image_of_mem _ hl) w]
        exact hv

/-! ## The direct-sum decomposition -/

/-- The `m`-th weight component of a `ℤ`-submodule `M` of `V`: the part of `M` lying in the
`m`-eigenspace of the operator by which the Cartan vector `h j` acts. -/
def weightComponent (M : Submodule ℤ V) (j : κ) (m : ℤ) : Submodule ℤ V :=
  M ⊓ (Module.End.eigenspace (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)))
    (m : ℚ)).restrictScalars ℤ

/-- Membership in a weight component: an element of `M` whose weight for the Cartan vector `h j`
is `m`. -/
@[simp]
theorem mem_weightComponent_iff {M : Submodule ℤ V} {j : κ} {m : ℤ} {x : V} :
    x ∈ weightComponent h ρ M j m ↔
      x ∈ M ∧ ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) x = (m : ℚ) • x := by
  rw [weightComponent, Submodule.mem_inf]
  exact and_congr_right fun _ => Module.End.mem_eigenspace_iff

/-- A weight component of `M` is contained in `M`. -/
theorem weightComponent_le (M : Submodule ℤ V) (j : κ) (m : ℤ) :
    weightComponent h ρ M j m ≤ M := inf_le_left

/-- **A Kostant-stable lattice is spanned by its weight components.** If the Cartan vector `h j`
acts on `V` with integral weights, then a `ℤ`-submodule stable under the Kostant integral form is
the sum of the pieces it cuts out of the weight spaces. -/
theorem iSup_weightComponent_eq {M : Submodule ℤ V}
    (hM : ∀ u ∈ kostantForm e h, ∀ x ∈ M, ρ u x ∈ M) (j : κ)
    (hV : ⨆ m : ℤ, Module.End.eigenspace
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j))) (m : ℚ) = ⊤) :
    ⨆ m : ℤ, weightComponent h ρ M j m = M := by
  classical
  refine le_antisymm (iSup_le fun m => weightComponent_le h ρ M j m) fun x hx => ?_
  have hxV : x ∈ ⨆ m : ℤ, Module.End.eigenspace
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j))) (m : ℚ) := hV ▸ Submodule.mem_top
  rw [Submodule.mem_iSup_iff_exists_dfinsupp'] at hxV
  obtain ⟨f, hf⟩ := hxV
  rw [DFinsupp.sum] at hf
  have hw : ∀ m ∈ f.support,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) (f m : V) = (m : ℚ) • (f m : V) :=
    fun m _ => Module.End.mem_eigenspace_iff.1 (f m).2
  rw [← hf]
  refine sum_mem fun m hm => Submodule.mem_iSup_of_mem m ?_
  rw [mem_weightComponent_iff]
  exact ⟨weightComponent_mem_of_kostantStable e h ρ hM j hw (hf ▸ hx) hm, hw m hm⟩

/-- **The weight components of a `ℤ`-submodule are independent.** They inherit independence from
the eigenspaces of the Cartan operator, so the sum in
`TauCeti.UniversalEnvelopingAlgebra.iSup_weightComponent_eq` is direct. -/
theorem iSupIndep_weightComponent (M : Submodule ℤ V) (j : κ) :
    iSupIndep (weightComponent h ρ M j) := by
  have hQ : iSupIndep fun m : ℤ => Module.End.eigenspace
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j))) (m : ℚ) :=
    (Module.End.eigenspaces_iSupIndep _).comp fun _ _ hab => by exact_mod_cast hab
  intro m
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ n, ⨆ (_ : n ≠ m), weightComponent h ρ M j n) ≤
      (⨆ n, ⨆ (_ : n ≠ m), Module.End.eigenspace
        (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j))) (n : ℚ)).restrictScalars ℤ :=
    iSup_le fun n => iSup_le fun hn =>
      le_trans inf_le_right (Submodule.restrictScalars_mono ℤ (le_iSup₂ (f := fun n (_ : n ≠ m) =>
        Module.End.eigenspace (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j))) (n : ℚ))
        n hn))
  exact Submodule.disjoint_def.1 (hQ m) x
    (Module.End.mem_eigenspace_iff.2 ((mem_weightComponent_iff h ρ).1 hx).2) (hle hx')

end TauCeti.UniversalEnvelopingAlgebra
