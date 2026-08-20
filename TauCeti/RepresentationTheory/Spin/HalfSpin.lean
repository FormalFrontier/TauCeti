/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.Spin.Representation
-- Private: `CliffordAlgebra.contractLeft_mem_evenOdd` is used only inside a proof, and
-- `CliffordAction` imports this module privately too, so it is not available transitively.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
-- Private: `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
-- `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one` are used only inside a proof.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
-- Private: `Subrepresentation.mem_toSubmodule`, `Subrepresentation.toSubmodule_bot` and
-- `Subrepresentation.toSubmodule_top` are used only inside a proof.
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The half-spin summands of the spin representation

`TauCeti.spinAction` makes the exterior algebra `S = ⋀·W` of the isotropic summand of a
polarization a module over the Clifford algebra, and `TauCeti.spinRep` restricts that action
along the inclusion of `spinGroup Q` — the spin representation proper — as `TauCeti.pinRep` does
along the inclusion of `pinGroup Q`.

The exterior algebra is itself `ℤ/2`-graded, by exterior parity, and `S` splits as the sum
`S⁺ ⊕ S⁻` of the even and the odd part. Whether that splitting is a splitting *of
representations* is the substance of this file, and it depends on the polarization.

* A vector of `W` acts by exterior multiplication and a vector of `W'` by contraction, and both
  reverse parity. So **when the polarization has no line summand** every vector acts by a
  parity-reversing operator, an even Clifford element acts by a parity-*preserving* one, and —
  since the spin group is even — `S⁺` and `S⁻` are subrepresentations of `spinRep`.
* A vector `z` of the line summand acts by `P.lineCoordinate z` times the grade involution, an
  operator that *preserves* parity, so with a line present an even Clifford element need not
  preserve parity at all. Concretely, take `V` a three-dimensional complex vector space carrying
  a nondegenerate quadratic form, polarized in the standard way: `W` and `W'` are dual isotropic
  lines and the line summand is their anisotropic orthogonal complement. Then `S = ⋀·W` is
  two-dimensional, `spinGroup Q` is a copy of `SL₂` acting on `S` by its standard representation,
  and that representation has no one-dimensional subrepresentation, so the parity splitting is
  not invariant there. The hypothesis `P.line = ⊥` below is therefore not a convenience; the
  statement is false without it.

The grading statement `TauCeti.spinAction_mem_evenOdd` is proved once, for an arbitrary parity of
the acting Clifford element, and the half-spin invariance and the parity shift by odd elements are
both read off it. Its two inputs are that exterior multiplication raises the exterior degree
(Mathlib's `CliffordAlgebra.evenOdd_mul_le`) and that contraction lowers it
(`CliffordAlgebra.contractLeft_mem_evenOdd`); the induction that propagates them from a
single vector to a general Clifford element is Mathlib's `CliffordAlgebra.evenOdd_induction`.

Nothing here needs a field, a nondegeneracy hypothesis, or a finite dimension: like
`TauCeti.spinAction` itself, everything holds over the commutative ring the polarization data
lives over. Their dimensions, which need a field and a finite dimension, are counted in
`TauCeti/RepresentationTheory/Spin/Dimension.lean`. Their invariant-subspace dichotomies over a
field are proved in `TauCeti/RepresentationTheory/Spin/Irreducible.lean`; their highest weights
belong to the complex theory and are not proved here.

## Main definitions

* `TauCeti.spinPlus` and `TauCeti.spinMinus`: the even and odd half-spin summands of `S`.
* `TauCeti.spinPlusSubrep` and `TauCeti.spinMinusSubrep`: those summands bundled as
  subrepresentations of `spinRep`, for a polarization without a line summand.
* `TauCeti.spinPlusAction` and `TauCeti.spinMinusAction`: the actions of the even Clifford
  subalgebra on the two summands, and `TauCeti.evenSpinActionProd` their product.

## Main results

* `TauCeti.spinAction_mem_evenOdd`: **the Clifford action is graded** for a polarization without
  a line summand, and `TauCeti.spinAction_mem_evenOdd_of_mem_even`: an even Clifford element
  preserves exterior parity.
* `TauCeti.spinPlus_invariant` and `TauCeti.spinMinus_invariant`: **the half-spin summands are
  invariant** under the spin representation.
* `TauCeti.isCompl_spinPlus_spinMinus`: the two summands are complementary, so `S = S⁺ ⊕ S⁻`, with
  `TauCeti.spinPlus_sup_spinMinus` and `TauCeti.spinPlus_inf_spinMinus` its two halves, and
  `TauCeti.isCompl_spinPlusSubrep_spinMinusSubrep`: the same in the lattice of subrepresentations
  of `spinRep`, so the splitting is one of representations.
* `TauCeti.nontrivial_spinPlus` and `TauCeti.nontrivial_spinMinus`: neither summand is zero, the
  odd one as soon as `W` is nonzero.
* `TauCeti.spinPlusAction_spinGroup` and `TauCeti.spinMinusAction_spinGroup`: the two bundlings
  agree, in that the even-subalgebra actions restrict along the spin group to the
  subrepresentations of `spinRep`.
* `TauCeti.map_spinAction_spinPlus_le_spinMinus` and
  `TauCeti.map_spinAction_spinMinus_le_spinPlus`: an odd Clifford element carries each of the two
  summands into the other, so the invariance argument does not extend from the spin group — which
  is even — to the pin group, which in general is not. That is why the splitting is stated for
  `spinRep` and not for `pinRep`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1–20.2: the spin
  module `S = ⋀·W` of a maximal isotropic subspace and its splitting into the half-spin summands
  `S⁺` and `S⁻` (§20.1), and the pin and spin groups acting on it (§20.2) — the construction
  formalised here.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 4, "The spin representation of the group" and "The half-spin summands".
-/

public section

open CliffordAlgebra

namespace TauCeti

universe u v

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]

variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-! ### The half-spin summands -/

/-- **The even half-spin summand** `S⁺ = ⋀ᵉᵛᵉⁿ W`, the even half of the exterior parity grading
of the spinor module. -/
def spinPlus (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    Submodule K (ExteriorAlgebra K P.W) :=
  evenOdd (0 : QuadraticForm K P.W) 0

/-- **The odd half-spin summand** `S⁻ = ⋀ᵒᵈᵈ W`, the odd half of the exterior parity grading of
the spinor module. -/
def spinMinus (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    Submodule K (ExteriorAlgebra K P.W) :=
  evenOdd (0 : QuadraticForm K P.W) 1

theorem spinPlus_def : spinPlus Q P = evenOdd (0 : QuadraticForm K P.W) 0 :=
  -- `(rfl)`, not `rfl`: the body of `spinPlus` is not `@[expose]`d.
  (rfl)

theorem spinMinus_def : spinMinus Q P = evenOdd (0 : QuadraticForm K P.W) 1 :=
  -- `(rfl)`, not `rfl`: the body of `spinMinus` is not `@[expose]`d.
  (rfl)

/-- **A spinor lies in `S⁺` exactly when it is of even exterior parity.** -/
@[simp]
theorem mem_spinPlus {s : ExteriorAlgebra K P.W} :
    s ∈ spinPlus Q P ↔ s ∈ evenOdd (0 : QuadraticForm K P.W) 0 := by
  rw [spinPlus_def]

/-- **A spinor lies in `S⁻` exactly when it is of odd exterior parity.** -/
@[simp]
theorem mem_spinMinus {s : ExteriorAlgebra K P.W} :
    s ∈ spinMinus Q P ↔ s ∈ evenOdd (0 : QuadraticForm K P.W) 1 := by
  rw [spinMinus_def]

/-- **The spinor module is the sum of its two half-spin summands**, `S = S⁺ ⊕ S⁻`. This is the
exterior parity grading, and it holds for every polarization. Invariance of the summands
(`TauCeti.spinPlus_invariant`) does not: it needs a polarization without a line summand. -/
theorem isCompl_spinPlus_spinMinus : IsCompl (spinPlus Q P) (spinMinus Q P) := by
  rw [spinPlus_def, spinMinus_def]
  exact evenOdd_isCompl _

/-- **The two half-spin summands span the spinor module**: every spinor is the sum of an even and
an odd one. -/
@[simp]
theorem spinPlus_sup_spinMinus : spinPlus Q P ⊔ spinMinus Q P = ⊤ :=
  codisjoint_iff.1 (isCompl_spinPlus_spinMinus P).codisjoint

/-- **The two half-spin summands meet only in zero**: a spinor of both parities vanishes. -/
@[simp]
theorem spinPlus_inf_spinMinus : spinPlus Q P ⊓ spinMinus Q P = ⊥ :=
  disjoint_iff.1 (isCompl_spinPlus_spinMinus P).disjoint

/-- **The even half-spin summand is never zero**: it contains the scalar `1`, of exterior degree
zero. Unlike `TauCeti.nontrivial_spinMinus` this needs no hypothesis on the isotropic summand. -/
theorem nontrivial_spinPlus [Nontrivial K] : Nontrivial (spinPlus Q P) :=
  ⟨⟨1, by rw [spinPlus_def]; exact SetLike.one_mem_graded _⟩, 0,
    fun h => (one_ne_zero : (1 : ExteriorAlgebra K P.W) ≠ 0)
      (by simpa using congrArg Subtype.val h)⟩

/-- **The odd half-spin summand is nonzero** as soon as the isotropic summand is. For `W = ⊥`
the spinor module is the ground ring, entirely even, and this fails. -/
theorem nontrivial_spinMinus (hW : P.W ≠ ⊥) : Nontrivial (spinMinus Q P) := by
  let _ : Nontrivial P.W := Submodule.nontrivial_iff_ne_bot.2 hW
  obtain ⟨w, hw⟩ := exists_ne (0 : P.W)
  refine ⟨⟨ExteriorAlgebra.ι K w, ?_⟩, 0, ?_⟩
  · rw [spinMinus_def]
    exact ι_mem_evenOdd_one (0 : QuadraticForm K P.W) w
  · intro h
    apply hw
    rw [← ExteriorAlgebra.ι_eq_zero_iff (R := K)]
    simpa using congrArg Subtype.val h

/-! ### The Clifford action is graded

The parity of the operator by which a Clifford element acts on `S` is the parity of the element,
provided the polarization has no line summand. -/

/-- **Without a line summand every vector acts oddly.** Exterior multiplication raises the
exterior degree by one and contraction lowers it by one, and in `ZMod 2` those are the same
shift; the grade involution, which would preserve the degree, is — up to the scalar coordinate —
the operator of a line vector, and is absent here. -/
private theorem cliffordOperator_mem_evenOdd (hline : P.line = ⊥) (v : V) {j : ZMod 2}
    {s : ExteriorAlgebra K P.W} (hs : s ∈ evenOdd (0 : QuadraticForm K P.W) j) :
    P.cliffordOperator v s ∈ evenOdd (0 : QuadraticForm K P.W) (j + 1) := by
  obtain ⟨c, rfl⟩ := P.decompositionEquiv.surjective v
  obtain ⟨⟨x, y⟩, z⟩ := c
  have hz : (z : V) = 0 := Submodule.mem_bot K |>.mp (hline ▸ z.2)
  rw [P.decompositionEquiv_apply, hz, add_zero, map_add, LinearMap.add_apply,
    P.cliffordOperator_coe_W, P.cliffordOperator_coe_W']
  refine add_mem ?_ ?_
  · rw [P.wedge_apply, ← add_comm (1 : ZMod 2) j]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one (0 : QuadraticForm K P.W) (x : P.W)) hs
  · rw [P.contract_apply]
    exact CliffordAlgebra.contractLeft_mem_evenOdd _ hs

/-- **The Clifford action on the spinor module is graded** when the polarization has no line
summand: a Clifford element of parity `i` shifts the exterior parity of a spinor by `i`. -/
theorem spinAction_mem_evenOdd (hline : P.line = ⊥) {i j : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) {s : ExteriorAlgebra K P.W}
    (hs : s ∈ evenOdd (0 : QuadraticForm K P.W) j) :
    spinAction Q P x s ∈ evenOdd (0 : QuadraticForm K P.W) (i + j) := by
  -- A pair of vectors shifts the exterior parity twice, which in `ZMod 2` is not at all.
  have htwice : ∀ c : ZMod 2, c + 1 + 1 = c := by decide
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    -- `i.val` is `0` or `1`, so `v` is a scalar or a vector.
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · obtain ⟨r, rfl⟩ := CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero hv
      simpa using Submodule.smul_mem _ r hs
    · obtain ⟨a, rfl⟩ := CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one hv
      rw [spinAction_ι, add_comm]
      exact cliffordOperator_mem_evenOdd P hline a hs
  | add x y hx hy ihx ihy => simpa only [map_add, LinearMap.add_apply] using add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, spinAction_ι, spinAction_ι,
      ← htwice (i + j)]
    exact cliffordOperator_mem_evenOdd P hline m₁ (cliffordOperator_mem_evenOdd P hline m₂ ih)

/-- **An even Clifford element preserves exterior parity**, when the polarization has no line
summand. This is the `i = 0` case of `TauCeti.spinAction_mem_evenOdd`, and the form the spin
group consumes. -/
theorem spinAction_mem_evenOdd_of_mem_even (hline : P.line = ⊥) {x : CliffordAlgebra Q}
    (hx : x ∈ CliffordAlgebra.even Q) {j : ZMod 2} {s : ExteriorAlgebra K P.W}
    (hs : s ∈ evenOdd (0 : QuadraticForm K P.W) j) :
    spinAction Q P x s ∈ evenOdd (0 : QuadraticForm K P.W) j := by
  have hx' : x ∈ evenOdd Q 0 := by
    rw [← CliffordAlgebra.even_toSubmodule Q]
    exact (Subalgebra.mem_toSubmodule _).mpr hx
  simpa only [zero_add] using spinAction_mem_evenOdd P hline hx' hs

/-! ### The even Clifford subalgebra acting on the two half-spin summands -/

private noncomputable def restrictSpinAction (N : Submodule K (ExteriorAlgebra K P.W))
    (hN : ∀ (x : CliffordAlgebra.even Q) (s : ExteriorAlgebra K P.W),
      s ∈ N → spinAction Q P x s ∈ N) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K N where
  toFun x := (spinAction Q P x).restrict (hN x)
  map_one' := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_mul' _ _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_zero' := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_add' _ _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  commutes' _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp

/-- **The action of the even Clifford subalgebra on the even half-spin summand** `S⁺`, for a
polarization without a line summand. -/
noncomputable def spinPlusAction (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (spinPlus Q P) :=
  restrictSpinAction P (spinPlus Q P) fun x s hs => by
    rw [spinPlus_def] at hs ⊢
    exact spinAction_mem_evenOdd_of_mem_even P hline x.2 hs

/-- **The action of the even Clifford subalgebra on the odd half-spin summand** `S⁻`. -/
noncomputable def spinMinusAction (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (spinMinus Q P) :=
  restrictSpinAction P (spinMinus Q P) fun x s hs => by
    rw [spinMinus_def] at hs ⊢
    exact spinAction_mem_evenOdd_of_mem_even P hline x.2 hs

/-- The action of an even Clifford element on `S⁺` is the Fock action. -/
@[simp]
theorem coe_spinPlusAction_apply (hline : P.line = ⊥) (x : CliffordAlgebra.even Q)
    (s : spinPlus Q P) :
    (spinPlusAction Q P hline x s : ExteriorAlgebra K P.W) = spinAction Q P x s :=
  (rfl)

/-- The action of an even Clifford element on `S⁻` is the Fock action. -/
@[simp]
theorem coe_spinMinusAction_apply (hline : P.line = ⊥) (x : CliffordAlgebra.even Q)
    (s : spinMinus Q P) :
    (spinMinusAction Q P hline x s : ExteriorAlgebra K P.W) = spinAction Q P x s :=
  (rfl)

/-- **The paired actions of the even Clifford subalgebra on the half-spin summands.** -/
noncomputable def evenSpinActionProd (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) :
    CliffordAlgebra.even Q →ₐ[K]
      Module.End K (spinPlus Q P) × Module.End K (spinMinus Q P) :=
  (spinPlusAction Q P hline).prod (spinMinusAction Q P hline)

@[simp]
theorem evenSpinActionProd_apply (hline : P.line = ⊥) (x : CliffordAlgebra.even Q) :
    evenSpinActionProd Q P hline x =
      (spinPlusAction Q P hline x, spinMinusAction Q P hline x) :=
  (rfl)

/-! ### Invariance of the half-spin summands -/

/-- **The even half-spin summand is invariant** under the spin representation, when the
polarization has no line summand: the spin group lies in the even Clifford subalgebra, and an
even element preserves exterior parity. -/
theorem spinPlus_invariant (hline : P.line = ⊥) (g : spinGroup Q) :
    (spinPlus Q P).map (spinRep Q P g) ≤ spinPlus Q P := by
  rintro _ ⟨s, hs, rfl⟩
  rw [spinPlus_def] at hs ⊢
  rw [spinRep_apply]
  exact spinAction_mem_evenOdd_of_mem_even P hline (spinGroup.mem_even g.2) hs

/-- **The odd half-spin summand is invariant** under the spin representation, when the
polarization has no line summand. -/
theorem spinMinus_invariant (hline : P.line = ⊥) (g : spinGroup Q) :
    (spinMinus Q P).map (spinRep Q P g) ≤ spinMinus Q P := by
  rintro _ ⟨s, hs, rfl⟩
  rw [spinMinus_def] at hs ⊢
  rw [spinRep_apply]
  exact spinAction_mem_evenOdd_of_mem_even P hline (spinGroup.mem_even g.2) hs

/-- **The even half-spin summand as a subrepresentation** of the spin representation. -/
def spinPlusSubrep (hline : P.line = ⊥) : Subrepresentation (spinRep Q P) where
  toSubmodule := spinPlus Q P
  apply_mem_toSubmodule g _ hv := spinPlus_invariant P hline g ⟨_, hv, rfl⟩

/-- **The odd half-spin summand as a subrepresentation** of the spin representation. -/
def spinMinusSubrep (hline : P.line = ⊥) : Subrepresentation (spinRep Q P) where
  toSubmodule := spinMinus Q P
  apply_mem_toSubmodule g _ hv := spinMinus_invariant P hline g ⟨_, hv, rfl⟩

@[simp]
theorem toSubmodule_spinPlusSubrep (hline : P.line = ⊥) :
    (spinPlusSubrep P hline).toSubmodule = spinPlus Q P :=
  -- `(rfl)`, not `rfl`: the body of `spinPlusSubrep` is not `@[expose]`d.
  (rfl)

@[simp]
theorem toSubmodule_spinMinusSubrep (hline : P.line = ⊥) :
    (spinMinusSubrep P hline).toSubmodule = spinMinus Q P :=
  -- `(rfl)`, not `rfl`: the body of `spinMinusSubrep` is not `@[expose]`d.
  (rfl)

/-- Membership in the even half-spin subrepresentation is membership in `S⁺`. A goal about a
`Subrepresentation` is stated through its `SetLike` membership, on which
`TauCeti.toSubmodule_spinPlusSubrep` cannot fire. -/
@[simp]
theorem mem_spinPlusSubrep (hline : P.line = ⊥) {s : ExteriorAlgebra K P.W} :
    s ∈ spinPlusSubrep P hline ↔ s ∈ spinPlus Q P := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_spinPlusSubrep]

/-- Membership in the odd half-spin subrepresentation is membership in `S⁻`. -/
@[simp]
theorem mem_spinMinusSubrep (hline : P.line = ⊥) {s : ExteriorAlgebra K P.W} :
    s ∈ spinMinusSubrep P hline ↔ s ∈ spinMinus Q P := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_spinMinusSubrep]

/-- The even-subalgebra action on `S⁺`, restricted to the spin group, is the representation
carried by the even half-spin subrepresentation. -/
theorem spinPlusAction_spinGroup (hline : P.line = ⊥) (g : spinGroup Q)
    (s : spinPlus Q P) :
    (spinPlusAction Q P hline ⟨g, spinGroup.mem_even g.2⟩ s : ExteriorAlgebra K P.W) =
      ((spinPlusSubrep P hline).toRepresentation g
        ⟨s, (mem_spinPlusSubrep P hline).2 s.2⟩ : ExteriorAlgebra K P.W) := by
  change spinAction Q P g s = spinRep Q P g s
  rw [spinRep_apply]

/-- The even-subalgebra action on `S⁻`, restricted to the spin group, is the representation
carried by the odd half-spin subrepresentation. -/
theorem spinMinusAction_spinGroup (hline : P.line = ⊥) (g : spinGroup Q)
    (s : spinMinus Q P) :
    (spinMinusAction Q P hline ⟨g, spinGroup.mem_even g.2⟩ s : ExteriorAlgebra K P.W) =
      ((spinMinusSubrep P hline).toRepresentation g
        ⟨s, (mem_spinMinusSubrep P hline).2 s.2⟩ : ExteriorAlgebra K P.W) := by
  change spinAction Q P g s = spinRep Q P g s
  rw [spinRep_apply]

/-- **The spin representation is the sum of its two half-spin subrepresentations.** This is
`TauCeti.isCompl_spinPlus_spinMinus` read in the lattice of subrepresentations of `spinRep`, where
it says that the parity splitting of `S` is a splitting of the spin representation itself. -/
theorem isCompl_spinPlusSubrep_spinMinusSubrep (hline : P.line = ⊥) :
    IsCompl (spinPlusSubrep P hline) (spinMinusSubrep P hline) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  refine ⟨Subrepresentation.toSubmodule_injective ?_, Subrepresentation.toSubmodule_injective ?_⟩
  · simp
  · simp

/-! ### Odd elements carry each summand into the other

An odd Clifford element maps `S⁺` into `S⁻` and `S⁻` into `S⁺`. Unlike the spin group, the pin
group need not lie in the even subalgebra, so the invariance argument does not extend to it, and
that is why the half-spin splitting is stated for `spinRep` and not for `pinRep`. Nothing here
says that `pinRep` really does fail to preserve the splitting: that would need an odd element of
the pin group whose action does not kill the summand — which for some `Q` there is none of, the
pin group then being even — and it is not proved here. -/

/-- **An odd Clifford element carries `S⁺` into `S⁻`.** -/
theorem map_spinAction_spinPlus_le_spinMinus (hline : P.line = ⊥) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 1) : (spinPlus Q P).map (spinAction Q P x) ≤ spinMinus Q P := by
  rintro _ ⟨s, hs, rfl⟩
  rw [spinPlus_def] at hs
  rw [spinMinus_def]
  simpa only [add_zero] using spinAction_mem_evenOdd P hline hx hs

/-- **An odd Clifford element carries `S⁻` into `S⁺`.** -/
theorem map_spinAction_spinMinus_le_spinPlus (hline : P.line = ⊥) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 1) : (spinMinus Q P).map (spinAction Q P x) ≤ spinPlus Q P := by
  rintro _ ⟨s, hs, rfl⟩
  rw [spinMinus_def] at hs
  -- An odd element applied to an odd spinor lands in parity `1 + 1`, which is `0`.
  have hparity : (1 : ZMod 2) + 1 = 0 := by decide
  rw [spinPlus_def, ← hparity]
  exact spinAction_mem_evenOdd P hline hx hs

end TauCeti
