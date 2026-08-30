/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# The cap, the cup, and the Brauer relations on the symplectic tensor square

The symplectic group acts on `V = k^{2n}` preserving the standard alternating form of
`Matrix.J`, and that form is a map `V ⊗ V → k`: read as a diagram it is a **cap**, an arc joining
the two bottom points. The matrix `-J`, read as a bivector `1 ↦ ∑ₓ ∑_y (-J) x y • eₓ ⊗ e_y`, is
the same arc drawn at the top, the **cup** `k → V ⊗ V`. Composing a cap with a cup gives the
Brauer diagram `e` on two strands, and permuting the two tensor factors gives, up to a sign, the
crossing `s`. Together with the identity these are the three Brauer diagrams on two strands, and
this file proves the three relations they satisfy on `V^{⊗2}`,

`s * s = 1`, `e * e = δ • e`, `s * e = e * s = e`, with the loop value `δ = -2n = -dim V`,

together with the invariance of the cap and the cup under the symplectic group, from which both
generators commute with the diagonal symplectic action.

## The sign convention

The orthogonal story of `TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal`
is repeated here with one genuine change, and it is a change of sign. The coordinate dot product
is symmetric, so there the crossing is the bare flip of the two tensor factors. The standard
symplectic form is alternating, so the bare flip `TauCeti.symplecticFlip` *anti*commutes with the
cap and with the cup (`TauCeti.symplecticCap_comp_symplecticFlip` and
`TauCeti.symplecticFlip_comp_symplecticCup`), and the relations `s * e = e = e * s` fail for it.
The Brauer crossing is therefore taken to be **minus** the flip,
`TauCeti.symplecticCrossing`, and with that choice all three relations hold. This is the sign that
has to be fixed before a Brauer action on `V^{⊗k}` is well defined.

The sign is forced, not chosen. The two anti-invariances give `flip * e = -e`, so if the bare flip
were the crossing then `s * e = e` would force `2 • e = 0`, which is false over `ℂ` for `n ≥ 1`
because `cap ∘ e ∘ cup` is multiplication by `(-2n)^2`. Re-ordering the arcs does not repair it:
each of the two orderings only changes `cap` or `cup` by a sign, which changes `e` by a sign at
most and leaves `cap ∘ flip = -cap` and `flip ∘ cup = -cup` -- hence `flip * e = -e` -- intact.
So on the permutation diagrams the symplectic Brauer action is the *sign-twisted* permutation
action rather than the bare one; that twist is the standard symplectic convention, and it is the
same phenomenon that makes the Brauer parameter negative.

The loop value is negative for the same reason. A closed loop is a cup stacked under a cap, so it
contracts the pairing `J` against the copairing `-J`, and that contraction is
`-∑ₓ ∑_y (J x y) * (J x y) = -tr (J * Jᵀ) = -tr 1 = -2n`. It is `-dim V` rather than `dim V`; it
is not the trace of `J`, which vanishes.

## Implementation notes

The alternating form needs subtraction, so, unlike the orthogonal file, the cap, the cup, the
crossing and the Brauer relations are stated over a commutative ring rather than a commutative
semiring. The flip of the two tensor factors and its involutivity carry no sign, so they are
stated over a commutative semiring.

The two invariance statements are recorded for a bare matrix rather than only for an element of
`Matrix.symplecticGroup (Fin n) k`, because they consume the defining identity from opposite
sides: the cap is preserved by every `A` with `Aᵀ * J * A = J`, and the cup by every `A` with
`A * J * Aᵀ = J`. The two conditions are equivalent, and Mathlib records both
(`SymplecticGroup.mem_iff'` and `SymplecticGroup.mem_iff`), but which side a proof uses is the
visible difference between contracting a pair of inputs and expanding a pair of outputs.

The flip is given a name of its own, unlike in the orthogonal file, for two reasons: it differs
from the Brauer crossing by the sign above, and the Layer 8 action
`TauCeti.permTensorAction` is set up for the coordinate space `Fin n → k`, so it does not apply to
the symplectic `(Fin n ⊕ Fin n) → k`.

The index set is `Fin n ⊕ Fin n` rather than a general `l ⊕ l`, even though `Matrix.J` and
`Matrix.symplecticGroup` are defined for a general `l`, because the invariant form
`TauCeti.stdSymplecticBilinForm` and the standard representation `TauCeti.stdSymplecticRep` that
this file consumes are pinned at `Fin n`.

The bookkeeping for pure tensors on two strands that this file shares with the orthogonal one --
`TauCeti.sum_pi_fin_two` and `TauCeti.tprod_fin_two` -- carries no symplectic content and lives in
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Basic`.

## Main definitions

* `TauCeti.symplecticCap`: the cap `V ⊗ V → k`, the standard alternating form.
* `TauCeti.symplecticCup`: the cup `k → V ⊗ V`, the bivector of `-J`.
* `TauCeti.symplecticCupCap`: the Brauer generator `e`, the composite `cup ∘ₗ cap`.
* `TauCeti.symplecticFlip`: the flip of the two tensor factors.
* `TauCeti.symplecticCrossing`: the Brauer generator `s`, minus the flip.

## Main results

* `TauCeti.symplecticCap_comp_symplecticCup`: the loop value, `cap ∘ cup = -2n`.
* `TauCeti.symplecticCupCap_mul_self`: `e * e = (-2n) • e`.
* `TauCeti.symplecticCrossing_mul_self`: `s * s = 1`.
* `TauCeti.symplecticCrossing_mul_symplecticCupCap` and
  `TauCeti.symplecticCupCap_mul_symplecticCrossing`: `s * e = e` and `e * s = e`.
* `TauCeti.symplecticCap_comp_piTensorProductMap` and
  `TauCeti.piTensorProductMap_comp_symplecticCup`: the cap and the cup are invariant.
* `TauCeti.commute_symplecticCupCap_tensorPower` and
  `TauCeti.commute_symplecticCrossing_tensorPower`: both generators commute with the diagonal
  action of the symplectic group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 9.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, "The invariant form and the action on `V^{⊗k}`", the symplectic case.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section Flip

variable [CommSemiring k]

/-- **The flip** of the two tensor factors of `V^{⊗2}`. It is *not* the Brauer crossing: the
crossing is its negative, see `TauCeti.symplecticCrossing`. -/
noncomputable def symplecticFlip : Module.End k (⨂[k]^2 ((Fin n ⊕ Fin n) → k)) :=
  PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin 2) (Equiv.swap 0 1)

@[simp]
theorem symplecticFlip_tprod (v : Fin 2 → ((Fin n ⊕ Fin n) → k)) :
    symplecticFlip k n (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k ![v 1, v 0] := by
  rw [symplecticFlip, PiTensorProduct.reindexRepresentation_apply, LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The flip is an involution: swapping the two tensor factors twice is the identity. -/
@[simp]
theorem symplecticFlip_mul_self : symplecticFlip k n * symplecticFlip k n = 1 := by
  rw [symplecticFlip, ← map_mul, Equiv.swap_mul_self, map_one]

end Flip

variable [CommRing k]

section Cap

/-- The standard alternating form as a multilinear map on two copies of `k^{2n}`. This is an
implementation detail of `TauCeti.symplecticCap`; the public interface is
`TauCeti.symplecticCap_tprod`. -/
private noncomputable def symplecticCapMultilinear :
    MultilinearMap k (fun _ : Fin 2 => ((Fin n ⊕ Fin n) → k)) k :=
  ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
    Matrix.J (Fin n) k x y •
      (MultilinearMap.mkPiAlgebra k (Fin 2) k).compLinearMap
        ![LinearMap.proj x, LinearMap.proj y]

private theorem symplecticCapMultilinear_apply (v : Fin 2 → ((Fin n ⊕ Fin n) → k)) :
    symplecticCapMultilinear k n v = stdSymplecticBilinForm k n (v 0) (v 1) := by
  rw [stdSymplecticBilinForm_apply, ← Matrix.toBilin'_apply' (Matrix.J (Fin n) k) (v 0) (v 1),
    Matrix.toBilin'_apply]
  simp only [symplecticCapMultilinear, _root_.sum_apply, _root_.smul_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **The cap**: the standard alternating form, read as a linear map on the tensor square. It is
the invariant form of the symplectic group, drawn as an arc joining the two bottom points of a
Brauer diagram. -/
noncomputable def symplecticCap : (⨂[k]^2 ((Fin n ⊕ Fin n) → k)) →ₗ[k] k :=
  PiTensorProduct.lift (symplecticCapMultilinear k n)

@[simp]
theorem symplecticCap_tprod (v : Fin 2 → ((Fin n ⊕ Fin n) → k)) :
    symplecticCap k n (PiTensorProduct.tprod k v) =
      stdSymplecticBilinForm k n (v 0) (v 1) := by
  rw [symplecticCap, PiTensorProduct.lift.tprod, symplecticCapMultilinear_apply]

/-- The cap on a pair of standard basis vectors reads off the matrix entry of `J`. -/
theorem symplecticCap_tprod_single (x y : Fin n ⊕ Fin n) :
    symplecticCap k n
        (PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)]) =
      Matrix.J (Fin n) k x y := by
  rw [symplecticCap_tprod, stdSymplecticBilinForm_apply,
    ← Matrix.toBilin'_apply' (Matrix.J (Fin n) k)]
  simp

end Cap

section Cup

/-- **The cup**: minus the bivector of `J`, that is the bivector of `-J`, drawn as an arc joining
the two top points of a Brauer diagram. Since `Matrix.J_squared` gives `J * J = -1`, the matrix
`-J` is the inverse `J⁻¹`, so this is the copairing inverse to the pairing that the cap contracts
against. It is not a two-sided inverse of `TauCeti.symplecticCap` as a linear map -- as a pairing
and a copairing the two have different sources and targets, and
`TauCeti.symplecticCap_comp_symplecticCup` computes their composite to be multiplication by
`-2n`. -/
noncomputable def symplecticCup : k →ₗ[k] (⨂[k]^2 ((Fin n ⊕ Fin n) → k)) :=
  LinearMap.toSpanSingleton k _
    (-∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
      Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)])

@[simp]
theorem symplecticCup_apply (c : k) :
    symplecticCup k n c =
      c • -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)] :=
  (rfl)

theorem symplecticCup_apply_one :
    symplecticCup k n 1 =
      -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)] := by
  rw [symplecticCup_apply, one_smul]

end Cup

section Loop

/-- `J` is antisymmetric, entrywise. -/
private theorem J_apply_swap (x y : Fin n ⊕ Fin n) :
    Matrix.J (Fin n) k y x = -Matrix.J (Fin n) k x y := by
  have h := congrFun (congrFun (Matrix.J_transpose (Fin n) k) x) y
  simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h

/-- Each row of `J` pairs with itself to `1`, because `J * Jᵀ = 1`. -/
private theorem sum_J_mul_J (x : Fin n ⊕ Fin n) :
    ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y = 1 := by
  have hJ : Matrix.J (Fin n) k * (Matrix.J (Fin n) k)ᵀ = 1 := by
    rw [Matrix.J_transpose, Matrix.mul_neg, Matrix.J_squared, neg_neg]
  have h := congrFun (congrFun hJ x) x
  simpa only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.transpose_apply] using h

/-- **The loop value.** A cup stacked under a cap closes into a loop, and the loop contracts the
pairing `J` against the copairing `-J`: the value is `-∑ₓ ∑_y (J x y) * (J x y)`, which is
`-tr (J * Jᵀ) = -tr 1 = -2n`. -/
theorem symplecticCap_comp_symplecticCup_apply (c : k) :
    symplecticCap k n (symplecticCup k n c) = -(2 * n : k) * c := by
  have h : symplecticCap k n
      (-∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)]) =
      -(2 * n : k) := by
    rw [map_neg, map_sum]
    have h1 : ∀ x : Fin n ⊕ Fin n, symplecticCap k n
        (∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)]) = 1 := by
      intro x
      rw [map_sum]
      simp only [map_smul, symplecticCap_tprod_single, smul_eq_mul]
      exact sum_J_mul_J k n x
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_const, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [symplecticCup_apply, map_smul, h, smul_eq_mul, mul_comm]

/-- The loop value, as an identity of linear maps: `cap ∘ cup` is multiplication by `-2n`. -/
theorem symplecticCap_comp_symplecticCup :
    symplecticCap k n ∘ₗ symplecticCup k n = -(2 * n : k) • LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  rw [LinearMap.comp_apply, symplecticCap_comp_symplecticCup_apply, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul]

end Loop

section Generators

/-- **The Brauer generator `e`** on two strands: a cap on the two inputs followed by a cup on the
two outputs. The name follows the written order of the composite `cup ∘ₗ cap`, as in
`TauCeti.symplecticCap_comp_symplecticCup` for the loop. -/
noncomputable def symplecticCupCap : Module.End k (⨂[k]^2 ((Fin n ⊕ Fin n) → k)) :=
  symplecticCup k n ∘ₗ symplecticCap k n

@[simp]
theorem symplecticCupCap_apply (x : ⨂[k]^2 ((Fin n ⊕ Fin n) → k)) :
    symplecticCupCap k n x = symplecticCup k n (symplecticCap k n x) :=
  (rfl)

/-- **The relation `e² = δ e`** at the loop value `δ = -2n`: the middle of `e * e` is a closed
loop. -/
@[simp]
theorem symplecticCupCap_mul_self :
    symplecticCupCap k n * symplecticCupCap k n = -(2 * n : k) • symplecticCupCap k n := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, symplecticCupCap_apply, symplecticCupCap_apply,
    symplecticCap_comp_symplecticCup_apply, ← smul_eq_mul, map_smul]

/-- **The Brauer crossing `s`** on two strands: *minus* the flip of the two tensor factors. The
sign is forced by the alternating form; see the module docstring. -/
noncomputable def symplecticCrossing : Module.End k (⨂[k]^2 ((Fin n ⊕ Fin n) → k)) :=
  -symplecticFlip k n

/-- The crossing swaps the two factors of a pure tensor and changes its sign. -/
@[simp]
theorem symplecticCrossing_tprod (v : Fin 2 → ((Fin n ⊕ Fin n) → k)) :
    symplecticCrossing k n (PiTensorProduct.tprod k v) =
      -PiTensorProduct.tprod k ![v 1, v 0] := by
  rw [symplecticCrossing, LinearMap.neg_apply, symplecticFlip_tprod]

/-- **The relation `s² = 1`**: the crossing is an involution. The two signs cancel, so this is the
bare statement that the flip is an involution. -/
@[simp]
theorem symplecticCrossing_mul_self :
    symplecticCrossing k n * symplecticCrossing k n = 1 := by
  have h : symplecticCrossing k n * symplecticCrossing k n
      = symplecticFlip k n * symplecticFlip k n := by
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, symplecticCrossing, LinearMap.neg_apply, map_neg, neg_neg]
  rw [h, symplecticFlip_mul_self]

/-- The flip **anti**fixes the cup: swapping the two top points of the arc reverses its
orientation, because the bivector of `J` is antisymmetric. -/
theorem symplecticFlip_comp_symplecticCup :
    symplecticFlip k n ∘ₗ symplecticCup k n = -symplecticCup k n := by
  have key : symplecticFlip k n
      (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)]) =
      -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)] := by
    simp only [map_sum, map_smul, symplecticFlip_tprod, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [J_apply_swap k n a b]
    exact neg_smul (M := ⨂[k]^2 ((Fin n ⊕ Fin n) → k)) _ _
  refine LinearMap.ext_ring ?_
  rw [LinearMap.comp_apply, symplecticCup_apply_one, LinearMap.neg_apply, symplecticCup_apply_one,
    map_neg, key]

/-- The flip **anti**fixes the cap: the standard symplectic form is alternating. -/
theorem symplecticCap_comp_symplecticFlip :
    symplecticCap k n ∘ₗ symplecticFlip k n = -symplecticCap k n := by
  refine PiTensorProduct.ext ?_
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    symplecticFlip_tprod, symplecticCap_tprod, Matrix.cons_val_zero, Matrix.cons_val_one,
    LinearMap.neg_apply]
  exact ((isAlt_stdSymplecticBilinForm k n).neg_eq (v 0) (v 1)).symm

/-- The crossing fixes the cup: the two sign changes cancel. -/
theorem symplecticCrossing_comp_symplecticCup :
    symplecticCrossing k n ∘ₗ symplecticCup k n = symplecticCup k n := by
  have h1 := LinearMap.congr_fun (symplecticFlip_comp_symplecticCup k n) 1
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h1
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, symplecticCrossing, LinearMap.neg_apply, h1, neg_neg]

/-- The crossing fixes the cap: the two sign changes cancel. -/
theorem symplecticCap_comp_symplecticCrossing :
    symplecticCap k n ∘ₗ symplecticCrossing k n = symplecticCap k n := by
  refine LinearMap.ext fun x => ?_
  have h1 := LinearMap.congr_fun (symplecticCap_comp_symplecticFlip k n) x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h1
  simp only [LinearMap.comp_apply, symplecticCrossing, LinearMap.neg_apply, map_neg, h1,
    neg_neg]

/-- **The relation `s e = e`**: the crossing is absorbed by the cup on top of `e`. -/
@[simp]
theorem symplecticCrossing_mul_symplecticCupCap :
    symplecticCrossing k n * symplecticCupCap k n = symplecticCupCap k n := by
  refine LinearMap.ext fun x => ?_
  simpa only [Module.End.mul_apply, symplecticCupCap_apply, LinearMap.coe_comp,
    Function.comp_apply] using
    LinearMap.congr_fun (symplecticCrossing_comp_symplecticCup k n) (symplecticCap k n x)

/-- **The relation `e s = e`**: the crossing is absorbed by the cap at the bottom of `e`. -/
@[simp]
theorem symplecticCupCap_mul_symplecticCrossing :
    symplecticCupCap k n * symplecticCrossing k n = symplecticCupCap k n := by
  refine LinearMap.ext fun x => ?_
  simpa only [Module.End.mul_apply, symplecticCupCap_apply, LinearMap.coe_comp,
    Function.comp_apply] using
    congrArg (symplecticCup k n)
      (LinearMap.congr_fun (symplecticCap_comp_symplecticCrossing k n) x)

end Generators

section Invariance

variable {k n}

/-- **The cap is invariant** under every matrix `A` with `Aᵀ * J * A = J`: such a matrix preserves
the standard alternating form, which is what the cap contracts against. -/
theorem symplecticCap_comp_piTensorProductMap
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k) :
    symplecticCap k n ∘ₗ PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A) =
      symplecticCap k n := by
  refine PiTensorProduct.ext ?_
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    PiTensorProduct.map_tprod, symplecticCap_tprod, Matrix.mulVecLin_apply,
    stdSymplecticBilinForm_apply]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hA, ← Matrix.dotProduct_mulVec]

/-- Two nested double sums may be exchanged as a whole. -/
private theorem sum_comm_four {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (F : ι → ι → ι → ι → M) :
    ∑ x : ι, ∑ y : ι, ∑ p : ι, ∑ q : ι, F x y p q
      = ∑ p : ι, ∑ q : ι, ∑ x : ι, ∑ y : ι, F x y p q :=
  calc ∑ x : ι, ∑ y : ι, ∑ p : ι, ∑ q : ι, F x y p q
      = ∑ x : ι, ∑ p : ι, ∑ y : ι, ∑ q : ι, F x y p q :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p : ι, ∑ x : ι, ∑ y : ι, ∑ q : ι, F x y p q := Finset.sum_comm
    _ = ∑ p : ι, ∑ x : ι, ∑ q : ι, ∑ y : ι, F x y p q :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p : ι, ∑ q : ι, ∑ x : ι, ∑ y : ι, F x y p q :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Applying a matrix in both tensor factors turns the bivector of `K` into the bivector of the
congruate `A * K * Aᵀ`. This is the computation behind the invariance of the cup. -/
private theorem piTensorProductMap_bivector
    (A K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) :
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
        (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, K x y •
          PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)]) =
      ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, (A * K * Aᵀ) p q •
        PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)] := by
  have hcol : ∀ x : Fin n ⊕ Fin n,
      A *ᵥ Pi.single x (1 : k) = ∑ p : Fin n ⊕ Fin n, A p x • Pi.single p (1 : k) := by
    intro x
    rw [Matrix.mulVec_single_one, ← (Pi.basisFun k (Fin n ⊕ Fin n)).sum_repr (A.col x)]
    simp [Matrix.col_apply]
  -- Expand both slots in the standard basis and collect the coefficients.
  have hstep : ∀ x y : Fin n ⊕ Fin n,
      PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
          (PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)]) =
        ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, (A p x * A q y) •
          PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)] := by
    intro x y
    have hfun : (fun i : Fin 2 =>
        Matrix.mulVecLin A (![Pi.single x (1 : k), Pi.single y (1 : k)] i)) =
        fun i : Fin 2 => ∑ p : Fin n ⊕ Fin n, A p (![x, y] i) • Pi.single p (1 : k) := by
      funext i
      fin_cases i <;> simp [hcol]
    rw [PiTensorProduct.map_tprod, hfun,
      MultilinearMap.map_sum (PiTensorProduct.tprod k)
        (g := fun i : Fin 2 => fun p : Fin n ⊕ Fin n =>
          A p (![x, y] i) • Pi.single p (1 : k)),
      ← sum_pi_fin_two fun p q => (A p x * A q y) •
        PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)]]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hr : PiTensorProduct.tprod k (fun i : Fin 2 => Pi.single (r i) (1 : k))
        = PiTensorProduct.tprod k ![Pi.single (r 0) (1 : k), Pi.single (r 1) (1 : k)] :=
      tprod_fin_two _
    rw [MultilinearMap.map_smul_univ, hr, Fin.prod_univ_two]
    simp
  have hcoef : ∀ p q : Fin n ⊕ Fin n,
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, K x y * (A p x * A q y) = (A * K * Aᵀ) p q := by
    intro p q
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  calc
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
        (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, K x y •
          PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)])
        = ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n,
            (K x y * (A p x * A q y)) •
              PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)] := by
          simp only [map_sum, map_smul, hstep, Finset.smul_sum, smul_smul]
    _ = ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
          (K x y * (A p x * A q y)) •
            PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)] :=
          sum_comm_four _
    _ = ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, (A * K * Aᵀ) p q •
          PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)] := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          simp only [← Finset.sum_smul]
          rw [hcoef p q]

/-- **The cup is invariant** under every matrix `A` with `A * J * Aᵀ = J`. This is the other
one-sided identity: the cap consumes `Aᵀ * J * A = J` and the cup consumes `A * J * Aᵀ = J`. -/
theorem piTensorProductMap_comp_symplecticCup
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : A * Matrix.J (Fin n) k * Aᵀ = Matrix.J (Fin n) k) :
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A) ∘ₗ symplecticCup k n =
      symplecticCup k n := by
  refine LinearMap.ext_ring ?_
  rw [LinearMap.comp_apply, symplecticCup_apply_one, map_neg, piTensorProductMap_bivector, hA]

end Invariance

section Group

/-- The cap is invariant under the diagonal action of the symplectic group. -/
theorem symplecticCap_comp_tensorPower (g : Matrix.symplecticGroup (Fin n) k) :
    symplecticCap k n ∘ₗ (stdSymplecticRep k n).tensorPower 2 g = symplecticCap k n := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    symplecticCap_comp_piTensorProductMap
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.prop)

/-- The cup is invariant under the diagonal action of the symplectic group. -/
theorem tensorPower_comp_symplecticCup (g : Matrix.symplecticGroup (Fin n) k) :
    ((stdSymplecticRep k n).tensorPower 2 g) ∘ₗ symplecticCup k n = symplecticCup k n := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    piTensorProductMap_comp_symplecticCup
      ((SymplecticGroup.mem_iff (l := Fin n) (R := k)).mp g.prop)

/-- **The Brauer generator `e` commutes with the symplectic group.** This is the two-strand case
of the statement that the diagram action and the symplectic action centralize one another. -/
theorem commute_symplecticCupCap_tensorPower (g : Matrix.symplecticGroup (Fin n) k) :
    Commute (symplecticCupCap k n) ((stdSymplecticRep k n).tensorPower 2 g) := by
  have hcap := LinearMap.congr_fun (symplecticCap_comp_tensorPower k n g)
  have hcup := LinearMap.congr_fun (tensorPower_comp_symplecticCup k n g)
  simp only [LinearMap.coe_comp, Function.comp_apply] at hcap hcup
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, symplecticCupCap_apply, symplecticCupCap_apply,
    hcap x, hcup (symplecticCap k n x)]

/-- The flip commutes with the diagonal action of the symplectic group: permuting the tensor
factors commutes with applying the same matrix in each of them. -/
theorem commute_symplecticFlip_tensorPower (g : Matrix.symplecticGroup (Fin n) k) :
    Commute (symplecticFlip k n) ((stdSymplecticRep k n).tensorPower 2 g) := by
  rw [Representation.tensorPower_apply, stdSymplecticRep_apply, symplecticFlip]
  exact PiTensorProduct.commute_reindexRepresentation_map k ((Fin n ⊕ Fin n) → k) (Fin 2)
    (Equiv.swap 0 1) (Matrix.mulVecLin _)

/-- **The Brauer generator `s` commutes with the symplectic group**, the sign being central. -/
theorem commute_symplecticCrossing_tensorPower (g : Matrix.symplecticGroup (Fin n) k) :
    Commute (symplecticCrossing k n) ((stdSymplecticRep k n).tensorPower 2 g) := by
  refine LinearMap.ext fun x => ?_
  have h := LinearMap.congr_fun (commute_symplecticFlip_tensorPower k n g) x
  simp only [Module.End.mul_apply] at h ⊢
  simp only [symplecticCrossing, LinearMap.neg_apply, map_neg, h]

end Group

end TauCeti
