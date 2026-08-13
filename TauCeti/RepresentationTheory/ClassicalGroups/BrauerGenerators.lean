/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Orthogonal
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower

/-!
# The cap, the cup, and the Brauer relations on the tensor square

The orthogonal group acts on `V = kⁿ` preserving the coordinate dot product, and the dot product
is a map `V ⊗ V → k`: read as a diagram it is a **cap**, an arc joining the two bottom points.
Its inverse copairing `k → V ⊗ V`, the **cup** `1 ↦ ∑ⱼ eⱼ ⊗ eⱼ`, is the same arc drawn at the
top. Composing a cap with a cup gives the diagram `e` on two strands, and permuting the two
tensor factors gives the crossing `s`. Together with the identity these are the three Brauer
diagrams on two strands, and this file proves the three relations they satisfy on `V^{⊗2}`,

`s * s = 1`, `e * e = δ • e`, `s * e = e * s = e`, with the loop value `δ = n = dim V`,

together with the invariance of the cap and the cup under the orthogonal group, from which `e`
commutes with the diagonal orthogonal action. The loop value is where the dimension enters: a
closed loop, a cup stacked under a cap, evaluates to the trace `n` of the dot product.

The two invariance statements are recorded for a bare matrix rather than only for an element of
`Matrix.orthogonalGroup (Fin n) k`, because they consume the defining identity from opposite
sides: the cap is preserved by every `A` with `Aᵀ * A = 1`, and the cup by every `A` with
`A * Aᵀ = 1`. The two conditions are equivalent, and Mathlib's orthogonal group records both, but
which side a proof uses is the visible difference between contracting a pair of inputs and
expanding a pair of outputs.

The crossing is *not* given a name of its own: it is the Layer 8 permutation action
`TauCeti.permTensorAction k n 2 (Equiv.swap 0 1)` of the transposition, which is exactly the
statement that the symmetric group sits inside the Brauer algebra as the diagrams with no arc.

## Main definitions

* `TauCeti.orthogonalCap`: the cap `V ⊗ V → k`, the coordinate dot product.
* `TauCeti.orthogonalCup`: the cup `k → V ⊗ V`, `1 ↦ ∑ⱼ eⱼ ⊗ eⱼ`.
* `TauCeti.orthogonalCapCup`: the Brauer generator `e`, a cap followed by a cup.

## Main results

* `TauCeti.orthogonalCap_comp_orthogonalCup`: the loop value, `cap ∘ cup = n`.
* `TauCeti.orthogonalCapCup_mul_self`: `e * e = n • e`.
* `TauCeti.permTensorAction_swap_mul_orthogonalCapCup` and
  `TauCeti.orthogonalCapCup_mul_permTensorAction_swap`: `s * e = e` and `e * s = e`.
* `TauCeti.permTensorAction_swap_mul_self`: `s * s = 1`.
* `TauCeti.orthogonalCap_comp_map` and `TauCeti.map_comp_orthogonalCup`: the cap and the cup are
  invariant.
* `TauCeti.commute_orthogonalCapCup_tensorPower` and
  `TauCeti.commute_permTensorAction_tensorPower_stdOrthogonalRep`: both Brauer generators commute
  with the diagonal action of the orthogonal group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 9.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, "The invariant form and the action on `V^{⊗k}`", and the worked example "Brauer duality
  on `(ℂ³)^{⊗2}` for `O(3)`".
-/

@[expose] public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ) [CommRing k]

section Cap

/-- The coordinate dot product as a multilinear map on two copies of `kⁿ`. -/
noncomputable def orthogonalCapMultilinear :
    MultilinearMap k (fun _ : Fin 2 => (Fin n → k)) k :=
  ∑ j : Fin n,
    (MultilinearMap.mkPiAlgebra k (Fin 2) k).compLinearMap fun _ : Fin 2 => LinearMap.proj j

@[simp]
theorem orthogonalCapMultilinear_apply (v : Fin 2 → (Fin n → k)) :
    orthogonalCapMultilinear k n v = v 0 ⬝ᵥ v 1 := by
  simp [orthogonalCapMultilinear, Fin.prod_univ_two, dotProduct]

/-- **The cap**: the coordinate dot product, read as a linear map on the tensor square. It is the
invariant symmetric form of the orthogonal group, drawn as an arc joining the two bottom points
of a Brauer diagram. -/
noncomputable def orthogonalCap : (⨂[k]^2 (Fin n → k)) →ₗ[k] k :=
  PiTensorProduct.lift (orthogonalCapMultilinear k n)

@[simp]
theorem orthogonalCap_tprod (v : Fin 2 → (Fin n → k)) :
    orthogonalCap k n (PiTensorProduct.tprod k v) = v 0 ⬝ᵥ v 1 := by
  rw [orthogonalCap, PiTensorProduct.lift.tprod, orthogonalCapMultilinear_apply]

end Cap

section Cup

/-- **The cup**: the copairing `1 ↦ ∑ⱼ eⱼ ⊗ eⱼ` inverse to the cap, drawn as an arc joining the
two top points of a Brauer diagram. -/
noncomputable def orthogonalCup : k →ₗ[k] (⨂[k]^2 (Fin n → k)) :=
  LinearMap.toSpanSingleton k _
    (∑ j : Fin n, PiTensorProduct.tprod k fun _ : Fin 2 => Pi.single j (1 : k))

theorem orthogonalCup_apply (c : k) :
    orthogonalCup k n c =
      c • ∑ j : Fin n, PiTensorProduct.tprod k fun _ : Fin 2 => Pi.single j (1 : k) :=
  (rfl)

@[simp]
theorem orthogonalCup_one :
    orthogonalCup k n 1 =
      ∑ j : Fin n, PiTensorProduct.tprod k fun _ : Fin 2 => Pi.single j (1 : k) := by
  rw [orthogonalCup_apply, one_smul]

end Cup

section Loop

/-- **The loop value.** A cup stacked under a cap closes into a loop, and the loop evaluates to
the trace `n` of the coordinate dot product. -/
theorem orthogonalCap_orthogonalCup (c : k) :
    orthogonalCap k n (orthogonalCup k n c) = (n : k) * c := by
  rw [orthogonalCup_apply, map_smul, map_sum]
  have h : ∀ j : Fin n,
      orthogonalCap k n (PiTensorProduct.tprod k fun _ : Fin 2 => Pi.single j (1 : k)) = 1 := by
    intro j
    rw [orthogonalCap_tprod]
    simp
  simp [h, mul_comm]

/-- The loop value, as an identity of linear maps: `cap ∘ cup` is multiplication by `n`. -/
theorem orthogonalCap_comp_orthogonalCup :
    orthogonalCap k n ∘ₗ orthogonalCup k n = (n : k) • LinearMap.id := by
  ext
  simp

end Loop

section Generators

/-- **The Brauer generator `e`** on two strands: a cap on the two inputs followed by a cup on the
two outputs. -/
noncomputable def orthogonalCapCup : Module.End k (⨂[k]^2 (Fin n → k)) :=
  orthogonalCup k n ∘ₗ orthogonalCap k n

theorem orthogonalCapCup_apply (x : ⨂[k]^2 (Fin n → k)) :
    orthogonalCapCup k n x = orthogonalCup k n (orthogonalCap k n x) :=
  (rfl)

/-- **The relation `e² = δ e`** at the loop value `δ = n`: the middle of `e * e` is a closed
loop. -/
theorem orthogonalCapCup_mul_self :
    orthogonalCapCup k n * orthogonalCapCup k n = (n : k) • orthogonalCapCup k n := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, orthogonalCapCup_apply, orthogonalCapCup_apply,
    orthogonalCap_orthogonalCup, ← smul_eq_mul, map_smul]

/-- **The relation `s² = 1`**: the crossing is an involution. -/
theorem permTensorAction_swap_mul_self :
    permTensorAction k n 2 (Equiv.swap 0 1) * permTensorAction k n 2 (Equiv.swap 0 1) = 1 := by
  rw [← map_mul, Equiv.swap_mul_self, map_one]

/-- The crossing fixes the cup: the cup joins the two top points, and swapping them is the same
arc. -/
theorem permTensorAction_swap_comp_orthogonalCup :
    permTensorAction k n 2 (Equiv.swap 0 1) ∘ₗ orthogonalCup k n = orthogonalCup k n := by
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, orthogonalCup_one, map_sum,
    permTensorAction_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod]

/-- The crossing fixes the cap: the coordinate dot product is symmetric. -/
theorem orthogonalCap_comp_permTensorAction_swap :
    orthogonalCap k n ∘ₗ permTensorAction k n 2 (Equiv.swap 0 1) = orthogonalCap k n := by
  refine PiTensorProduct.ext ?_
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    permTensorAction_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod,
    orthogonalCap_tprod, Equiv.symm_swap]
  exact dotProduct_comm _ _

/-- **The relation `s e = e`**: the crossing is absorbed by the cup on top of `e`. -/
theorem permTensorAction_swap_mul_orthogonalCapCup :
    permTensorAction k n 2 (Equiv.swap 0 1) * orthogonalCapCup k n = orthogonalCapCup k n := by
  refine LinearMap.ext fun x => ?_
  simpa only [Module.End.mul_apply, orthogonalCapCup_apply, LinearMap.coe_comp,
    Function.comp_apply] using
    LinearMap.congr_fun (permTensorAction_swap_comp_orthogonalCup k n) (orthogonalCap k n x)

/-- **The relation `e s = e`**: the crossing is absorbed by the cap at the bottom of `e`. -/
theorem orthogonalCapCup_mul_permTensorAction_swap :
    orthogonalCapCup k n * permTensorAction k n 2 (Equiv.swap 0 1) = orthogonalCapCup k n := by
  refine LinearMap.ext fun x => ?_
  simpa only [Module.End.mul_apply, orthogonalCapCup_apply, LinearMap.coe_comp,
    Function.comp_apply] using
    congrArg (orthogonalCup k n)
      (LinearMap.congr_fun (orthogonalCap_comp_permTensorAction_swap k n) x)

end Generators

section Invariance

variable {k n}

/-- **The cap is invariant** under every matrix `A` with `Aᵀ * A = 1`: such a matrix preserves
the coordinate dot product, which is what the cap contracts against. -/
theorem orthogonalCap_comp_map {A : Matrix (Fin n) (Fin n) k} (hA : Aᵀ * A = 1) :
    orthogonalCap k n ∘ₗ PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A) =
      orthogonalCap k n := by
  have hmem : A ∈ Matrix.orthogonalGroup (Fin n) k :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) k).mpr hA
  refine PiTensorProduct.ext ?_
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    PiTensorProduct.map_tprod, orthogonalCap_tprod, Matrix.mulVecLin_apply]
  simpa only [stdOrthogonalRep_apply_apply] using
    stdOrthogonalRep_dotProduct_stdOrthogonalRep k n ⟨A, hmem⟩ (v 0) (v 1)

/-- The `j`-th column of a matrix, expanded in the standard basis. -/
private theorem mulVec_single_eq_sum (A : Matrix (Fin n) (Fin n) k) (j : Fin n) :
    A *ᵥ Pi.single j (1 : k) = ∑ p : Fin n, A p j • Pi.single p (1 : k) := by
  funext q
  rw [Finset.sum_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm]

/-- A sum over the functions `Fin 2 → Fin n` is a double sum. -/
private theorem sum_pi_fin_two {M : Type*} [AddCommMonoid M] (f : Fin n → Fin n → M) :
    ∑ r : Fin 2 → Fin n, f (r 0) (r 1) = ∑ p : Fin n, ∑ q : Fin n, f p q :=
  Eq.trans
    (Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Fin n) _
      (fun pq : Fin n × Fin n => f pq.1 pq.2) fun _ => rfl)
    (Fintype.sum_prod_type' f)

/-- A pure tensor of standard basis vectors on two strands, written in `![·, ·]` form. -/
private theorem tprod_single_pi_fin_two (r : Fin 2 → Fin n) :
    PiTensorProduct.tprod k (fun i : Fin 2 => Pi.single (r i) (1 : k))
      = PiTensorProduct.tprod k ![Pi.single (r 0) (1 : k), Pi.single (r 1) (1 : k)] := by
  congr 1
  funext i
  fin_cases i <;> simp

/-- **The cup is invariant** under every matrix `A` with `A * Aᵀ = 1`. This is the other one-sided
identity: the cap consumes `Aᵀ * A = 1` and the cup consumes `A * Aᵀ = 1`. -/
theorem map_comp_orthogonalCup {A : Matrix (Fin n) (Fin n) k} (hA : A * Aᵀ = 1) :
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A) ∘ₗ orthogonalCup k n =
      orthogonalCup k n := by
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, orthogonalCup_one, map_sum,
    PiTensorProduct.map_tprod, Matrix.mulVecLin_apply]
  -- Expand each column of `A` in the standard basis and collect the coefficients.
  calc
    ∑ j : Fin n, PiTensorProduct.tprod k (fun _ : Fin 2 => A *ᵥ Pi.single j (1 : k))
        = ∑ j : Fin n, ∑ r : Fin 2 → Fin n,
            (∏ i : Fin 2, A (r i) j) •
              PiTensorProduct.tprod k fun i : Fin 2 => Pi.single (r i) (1 : k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp_rw [mulVec_single_eq_sum A j]
          rw [MultilinearMap.map_sum (PiTensorProduct.tprod k)
            (g := fun _ : Fin 2 => fun p : Fin n => A p j • Pi.single p (1 : k))]
          exact Finset.sum_congr rfl fun r _ => MultilinearMap.map_smul_univ _ _ _
    _ = ∑ r : Fin 2 → Fin n,
          ((1 : Matrix (Fin n) (Fin n) k) (r 0) (r 1)) •
            PiTensorProduct.tprod k fun i : Fin 2 => Pi.single (r i) (1 : k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_smul, ← hA]
          congr 1
          simp [Matrix.mul_apply, Fin.prod_univ_two]
    _ = ∑ p : Fin n, ∑ q : Fin n,
          ((1 : Matrix (Fin n) (Fin n) k) p q) •
            PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)] := by
          rw [← sum_pi_fin_two fun p q => ((1 : Matrix (Fin n) (Fin n) k) p q) •
            PiTensorProduct.tprod k ![Pi.single p (1 : k), Pi.single q (1 : k)]]
          exact Finset.sum_congr rfl fun r _ => by rw [tprod_single_pi_fin_two]
    _ = ∑ j : Fin n, PiTensorProduct.tprod k fun _ : Fin 2 => Pi.single j (1 : k) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single p]
          · rw [Matrix.one_apply_eq, one_smul]
            congr 1
            funext i
            fin_cases i <;> simp
          · intro q _ hq
            rw [Matrix.one_apply_ne (Ne.symm hq), zero_smul]
          · intro h
            exact absurd (Finset.mem_univ p) h

variable (k n)

/-- The cap is invariant under the diagonal action of the orthogonal group. -/
theorem orthogonalCap_comp_tensorPower (g : Matrix.orthogonalGroup (Fin n) k) :
    orthogonalCap k n ∘ₗ (stdOrthogonalRep k n).tensorPower 2 g = orthogonalCap k n := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    orthogonalCap_comp_map ((Matrix.mem_orthogonalGroup_iff' (Fin n) k).mp g.prop)

/-- The cup is invariant under the diagonal action of the orthogonal group. -/
theorem tensorPower_comp_orthogonalCup (g : Matrix.orthogonalGroup (Fin n) k) :
    ((stdOrthogonalRep k n).tensorPower 2 g) ∘ₗ orthogonalCup k n = orthogonalCup k n := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    map_comp_orthogonalCup ((Matrix.mem_orthogonalGroup_iff (Fin n) k).mp g.prop)

/-- **The Brauer generator `e` commutes with the orthogonal group.** This is the two-strand case
of the statement that the diagram action and the orthogonal action centralize one another. -/
theorem commute_orthogonalCapCup_tensorPower (g : Matrix.orthogonalGroup (Fin n) k) :
    Commute (orthogonalCapCup k n) ((stdOrthogonalRep k n).tensorPower 2 g) := by
  have hcap := LinearMap.congr_fun (orthogonalCap_comp_tensorPower k n g)
  have hcup := LinearMap.congr_fun (tensorPower_comp_orthogonalCup k n g)
  simp only [LinearMap.coe_comp, Function.comp_apply] at hcap hcup
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, orthogonalCapCup_apply, orthogonalCapCup_apply,
    hcap x, hcup (orthogonalCap k n x)]

/-- **The crossing commutes with the orthogonal group**, the two-strand case of the commuting
symmetric-group and orthogonal actions. It is the restriction along `O(n) ↪ GL(n)` of the
general-linear statement `TauCeti.commute_permTensorAction_tensorPowerRep`. -/
theorem commute_permTensorAction_tensorPower_stdOrthogonalRep (σ : Equiv.Perm (Fin 2))
    (g : Matrix.orthogonalGroup (Fin n) k) :
    Commute (permTensorAction k n 2 σ) ((stdOrthogonalRep k n).tensorPower 2 g) := by
  have h := commute_permTensorAction_tensorPowerRep k n 2 σ (orthogonalGroupToGL k n g)
  rwa [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply, orthogonalGroupToGL_coe,
    ← stdOrthogonalRep_apply k n g, ← Representation.tensorPower_apply] at h

end Invariance

end TauCeti
