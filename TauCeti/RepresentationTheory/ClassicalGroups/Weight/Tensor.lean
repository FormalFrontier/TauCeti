/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic

/-!
# Weights add on a tensor product

A diagonal matrix acts on a pure tensor of weight vectors by the product of the two scalars, so a
tensor product of weight vectors is again a weight vector and its weight is the **sum** of the two
weights (`TauCeti.tmul_mem_weightSpace_tprod`). This file promotes that one-line computation to a
decomposition: once each factor is spanned by its weight spaces, so is the tensor product, and its
weight-`l` space is exactly the sum of the products of the weight spaces of the factors over the
pairs of weights adding up to `l`.

The two directions are of quite different natures. The inclusion of the sum of products into the
weight space is the computation above and needs only a commutative ring, and so does the fact that
the weight spaces of the tensor product span it — that one is the distributivity of
`Submodule.map₂` over suprema, applied to `TensorProduct.map₂_mk_top_top_eq_top`. The reverse
inclusion is not a computation at all: it says that a weight vector of the tensor product has no
component outside the pieces just constructed, and that is read off the **independence** of the
weight spaces (`TauCeti.iSupIndep_weightSpace`) through
`iSupIndep.le_iff_eq_of_iSup_eq_top`. So it inherits the standing hypothesis of the weight theory,
that distinct weights give distinct characters of the torus, and with it the coefficients: over
`𝔽₂` the torus is trivial and nothing is independent.

The determinant powers are the worked case, and they need neither ingredient above. Because
`det ^ m` is the one-dimensional representation on which the torus acts by the character of the
constant weight `fun _ ↦ m`, the identification `W ⊗[k] k ≃ₗ[k] W` carries the action of
`ρ ⊗ det ^ m` to the action of `ρ` rescaled by that one character, which cancels off the
eigen-relation. So tensoring with `det ^ m` **translates** the weights of an *arbitrary*
representation by the constant sequence `m` (`TauCeti.weightSpace_tprod_detPowerRep`), over a
commutative ring, with no separation of weights and no assumption that `ρ` is weight-decomposed.
What is proved here is exactly that translation of weight spaces; it is the step that the
classification of the irreducible rational representations of `GL n` as `det`-twists of the
polynomial ones runs on, but that classification needs the highest-weight theory and is not proved
here.

## Main results

* `TauCeti.tmul_mem_weightSpace_tprod`: a pure tensor of weight vectors has the sum of the two
  weights.
* `TauCeti.iSup_weightSpace_tprod_eq_top`: **the weight spaces of a tensor product span it**, as
  soon as the weight spaces of each factor span.
* `TauCeti.weightSpace_tprod`: **weights add.** The weight-`l` space of a tensor product is the
  sum, over the weights `a` of the first factor, of the products of the weight space of `a` with
  the weight space of `l - a` in the second.
* `TauCeti.isInternal_weightSpace_tprod`: **a tensor product of weight-decomposed representations
  is weight-decomposed.**
* `TauCeti.weightSpace_tprod_detPowerRep` and
  `TauCeti.map_rid_weightSpace_tprod_detPowerRep`: **tensoring with `det ^ m` translates weights
  by the constant sequence `m`**, for an arbitrary representation, the second statement reading
  the translation through `W ⊗[k] k ≃ₗ[k] W`.

## Implementation notes

The sum defining the weight-`l` space is indexed by a single weight `a`, the weight of the first
factor, with `l - a` the weight of the second; indexing instead by the pairs `(a, b)` with
`a + b = l` would carry a subtype through every rewrite for no gain.

The products of weight spaces are written with `Submodule.map₂ (TensorProduct.mk k W W')` rather
than with a tensor product of submodules: `Submodule.map₂` is the image of the pure tensors, which
is what the statements need, and it comes with the distributivity over suprema that the spanning
proof runs on.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix TensorProduct

universe u v w

namespace TauCeti

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}
variable {W : Type v} [AddCommGroup W] [Module k W]
variable {W' : Type w} [AddCommGroup W'] [Module k W']
variable {ρ : Representation k (GL (Fin n) k) W} {σ : Representation k (GL (Fin n) k) W'}

/-! ## Pure tensors of weight vectors -/

/-- **A pure tensor of weight vectors is a weight vector of the sum of the two weights**: a
diagonal matrix scales the two factors by the two characters, hence the tensor by their product,
and characters multiply when weights are added. -/
theorem tmul_mem_weightSpace_tprod {a b : Fin n → ℤ} {w : W} {w' : W'}
    (hw : w ∈ weightSpace ρ a) (hw' : w' ∈ weightSpace σ b) :
    w ⊗ₜ[k] w' ∈ weightSpace (ρ.tprod σ) (a + b) := by
  rw [mem_weightSpace_iff]
  intro t
  rw [Representation.tprod_apply, TensorProduct.map_tmul, apply_of_mem_weightSpace hw t,
    apply_of_mem_weightSpace hw' t, TensorProduct.smul_tmul_smul, weightChar_add]
  rfl

/-- The product of the weight-`a` space of one representation with the weight-`b` space of another
lies in the weight-`(a + b)` space of their tensor product. -/
theorem map₂_weightSpace_le_weightSpace_tprod (ρ : Representation k (GL (Fin n) k) W)
    (σ : Representation k (GL (Fin n) k) W') (a b : Fin n → ℤ) :
    Submodule.map₂ (TensorProduct.mk k W W') (weightSpace ρ a) (weightSpace σ b)
      ≤ weightSpace (ρ.tprod σ) (a + b) :=
  Submodule.map₂_le.mpr fun _ hw _ hw' ↦ tmul_mem_weightSpace_tprod hw hw'

/-- The sum, over the weights `a` of the first factor, of the products of the weight-`a` space with
the weight-`(l - a)` space of the second factor lies in the weight-`l` space of the tensor
product. This is the easy half of `TauCeti.weightSpace_tprod`. -/
theorem iSup_map₂_weightSpace_le_weightSpace_tprod (ρ : Representation k (GL (Fin n) k) W)
    (σ : Representation k (GL (Fin n) k) W') (l : Fin n → ℤ) :
    ⨆ a : Fin n → ℤ,
        Submodule.map₂ (TensorProduct.mk k W W') (weightSpace ρ a) (weightSpace σ (l - a))
      ≤ weightSpace (ρ.tprod σ) l := by
  refine iSup_le fun a ↦ ?_
  exact le_of_le_of_eq (map₂_weightSpace_le_weightSpace_tprod ρ σ a (l - a))
    (by rw [add_sub_cancel])

/-! ## Spanning -/

/-- The products of weight spaces of the two factors already exhaust the tensor product, once the
weight spaces of each factor span it. This is the shared engine of
`TauCeti.iSup_weightSpace_tprod_eq_top` and `TauCeti.weightSpace_tprod`, and is not part of the
API. -/
private theorem iSup_iSup_map₂_weightSpace_eq_top (hρ : ⨆ a : Fin n → ℤ, weightSpace ρ a = ⊤)
    (hσ : ⨆ b : Fin n → ℤ, weightSpace σ b = ⊤) :
    ⨆ l : Fin n → ℤ, ⨆ a : Fin n → ℤ,
        Submodule.map₂ (TensorProduct.mk k W W') (weightSpace ρ a) (weightSpace σ (l - a)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← TensorProduct.map₂_mk_top_top_eq_top k W W', ← hρ, ← hσ, Submodule.map₂_iSup_left]
  refine iSup_le fun a ↦ ?_
  rw [Submodule.map₂_iSup_right]
  refine iSup_le fun b ↦ le_trans ?_ (le_iSup _ (a + b))
  refine le_trans (le_of_eq ?_) (le_iSup _ a)
  rw [add_sub_cancel_left]

/-- **The weight spaces of a tensor product span it**, as soon as the weight spaces of each factor
span. No separation of weights is needed: this is the computation
`TauCeti.tmul_mem_weightSpace_tprod` on pure tensors, spread over the whole tensor product. -/
theorem iSup_weightSpace_tprod_eq_top (hρ : ⨆ a : Fin n → ℤ, weightSpace ρ a = ⊤)
    (hσ : ⨆ b : Fin n → ℤ, weightSpace σ b = ⊤) :
    ⨆ l : Fin n → ℤ, weightSpace (ρ.tprod σ) l = ⊤ :=
  top_le_iff.mp <| (iSup_iSup_map₂_weightSpace_eq_top hρ hσ).ge.trans <|
    iSup_mono fun l ↦ iSup_map₂_weightSpace_le_weightSpace_tprod ρ σ l

/-! ## The determinant twist -/

/-- The identification `W ⊗[k] k ≃ₗ[k] W` carries the action of `ρ ⊗ det ^ m` to the action of `ρ`
rescaled by `det ^ m`. -/
private theorem rid_tprod_detPowerRep_apply (ρ : Representation k (GL (Fin n) k) W) (m : ℤ)
    (g : GL (Fin n) k) (x : W ⊗[k] k) :
    TensorProduct.rid k W ((ρ.tprod (detPowerRep k n m)) g x)
      = (↑(GeneralLinearGroup.det g ^ m) : k) • ρ g (TensorProduct.rid k W x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w c =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, detPowerRep_apply,
      TensorProduct.rid_tmul, TensorProduct.rid_tmul, map_smul, smul_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, smul_add]

/-- **A vector of `ρ ⊗ det ^ m` has weight `l` exactly when the vector of `ρ` it corresponds to
under `W ⊗[k] k ≃ₗ[k] W` has weight `l - m`.** A torus element acts on `det ^ m` by the character
of the constant weight `m`, so the twist multiplies every character by that one; the constant
weight is then cancelled off the eigen-relation, which is why no separation of weights and no
decomposition of `ρ` is involved. -/
private theorem mem_weightSpace_tprod_detPowerRep_iff (ρ : Representation k (GL (Fin n) k) W)
    (m : ℤ) (l : Fin n → ℤ) (x : W ⊗[k] k) :
    x ∈ weightSpace (ρ.tprod (detPowerRep k n m)) l ↔
      TensorProduct.rid k W x ∈ weightSpace ρ (l - fun _ ↦ m) := by
  rw [mem_weightSpace_iff, mem_weightSpace_iff]
  refine forall_congr' fun t ↦ ?_
  have hl : weightChar k l t = (∏ i, t i) ^ m * weightChar k (l - fun _ ↦ m) t := by
    conv_lhs => rw [show l = (fun _ ↦ m) + (l - fun _ ↦ m) by abel]
    rw [weightChar_add, MonoidHom.mul_apply, weightChar_const]
  rw [← (TensorProduct.rid k W).injective.eq_iff, rid_tprod_detPowerRep_apply, map_smul,
    det_diagGL, hl, Units.val_mul, mul_smul]
  exact (Units.isUnit _).smul_left_cancel

/-- The vectors `w ⊗ₜ c` with `w` in a submodule `S` of `W` are exactly the vectors that
`W ⊗[k] k ≃ₗ[k] W` sends into `S`. -/
private theorem map₂_mk_top_eq_comap_rid (S : Submodule k W) :
    Submodule.map₂ (TensorProduct.mk k W k) S ⊤
      = Submodule.comap (TensorProduct.rid k W).toLinearMap S := by
  refine le_antisymm (Submodule.map₂_le.mpr fun w hw c _ ↦ ?_) fun x hx ↦ ?_
  · simpa using Submodule.smul_mem _ c hw
  · rw [← (TensorProduct.rid k W).symm_apply_apply x, TensorProduct.rid_symm_apply]
    exact Submodule.apply_mem_map₂ _ hx Submodule.mem_top

/-- **Tensoring with `det ^ m` translates weights by the constant sequence `m`**: the weight-`l`
space of `ρ ⊗ det ^ m` consists of the tensors `w ⊗ₜ c` with `w` of weight `l - m`. This holds for
every representation `ρ` over every commutative ring, since `det ^ m` is the one-dimensional
representation on which the torus acts by the character of the constant weight `m`. Nothing beyond
this translation of weight spaces is claimed: it is the computation underlying the classification
of the irreducible rational representations of `GL n` as `det`-twists of the polynomial ones,
which is not proved here. -/
theorem weightSpace_tprod_detPowerRep (ρ : Representation k (GL (Fin n) k) W) (m : ℤ)
    (l : Fin n → ℤ) :
    weightSpace (ρ.tprod (detPowerRep k n m)) l
      = Submodule.map₂ (TensorProduct.mk k W k) (weightSpace ρ (l - fun _ ↦ m)) ⊤ := by
  rw [map₂_mk_top_eq_comap_rid]
  exact SetLike.ext fun x ↦ mem_weightSpace_tprod_detPowerRep_iff ρ m l x

/-- **The determinant twist read through `W ⊗[k] k ≃ₗ[k] W`**: the weight-`l` space of
`ρ ⊗ det ^ m` corresponds to the weight-`(l - m)` space of `ρ`. This is
`TauCeti.weightSpace_tprod_detPowerRep` with the trailing scalar factor discarded. -/
theorem map_rid_weightSpace_tprod_detPowerRep (ρ : Representation k (GL (Fin n) k) W) (m : ℤ)
    (l : Fin n → ℤ) :
    Submodule.map (TensorProduct.rid k W).toLinearMap
        (weightSpace (ρ.tprod (detPowerRep k n m)) l)
      = weightSpace ρ (l - fun _ ↦ m) := by
  rw [weightSpace_tprod_detPowerRep, map₂_mk_top_eq_comap_rid,
    Submodule.map_comap_eq_of_surjective (TensorProduct.rid k W).surjective]

end CommRing

/-! ## Weights add

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section Field

variable {k : Type u} [Field k] {n : ℕ}
variable {W : Type v} [AddCommGroup W] [Module k W]
variable {W' : Type w} [AddCommGroup W'] [Module k W']
variable {ρ : Representation k (GL (Fin n) k) W} {σ : Representation k (GL (Fin n) k) W'}

/-- **Weights add.** The weight-`l` space of a tensor product is the sum, over the weights `a` of
the first factor, of the products of the weight-`a` space with the weight-`(l - a)` space of the
second factor.

Only the inclusion `≥` is a computation; the inclusion `≤` says that a weight vector of the tensor
product has no component outside those products, and comes from the independence of the weight
spaces, whence the separation hypothesis. -/
theorem weightSpace_tprod (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (hρ : ⨆ a : Fin n → ℤ, weightSpace ρ a = ⊤) (hσ : ⨆ b : Fin n → ℤ, weightSpace σ b = ⊤)
    (l : Fin n → ℤ) :
    weightSpace (ρ.tprod σ) l
      = ⨆ a : Fin n → ℤ,
          Submodule.map₂ (TensorProduct.mk k W W') (weightSpace ρ a) (weightSpace σ (l - a)) :=
  (congrFun
    (((iSupIndep_weightSpace hchar (ρ.tprod σ)).le_iff_eq_of_iSup_eq_top
        (iSup_iSup_map₂_weightSpace_eq_top hρ hσ)).mp
      (iSup_map₂_weightSpace_le_weightSpace_tprod ρ σ)) l).symm

/-- **A tensor product of weight-decomposed representations is weight-decomposed.** Only the
spanning half of the hypothesis on each factor is needed: once weights are separated, the
independence of the weight spaces of the tensor product is automatic
(`TauCeti.iSupIndep_weightSpace`). -/
theorem isInternal_weightSpace_tprod (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (hρ : ⨆ a : Fin n → ℤ, weightSpace ρ a = ⊤) (hσ : ⨆ b : Fin n → ℤ, weightSpace σ b = ⊤) :
    DirectSum.IsInternal fun l : Fin n → ℤ ↦ weightSpace (ρ.tprod σ) l :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_weightSpace hchar _, iSup_weightSpace_tprod_eq_top hρ hσ⟩

/-- **The tensor square of the standard representation is the internal direct sum of its weight
spaces**, the first case of the weight-space decomposition beyond the standard representation
itself. -/
theorem isInternal_weightSpace_tprod_stdRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ ↦
      weightSpace ((stdRep k n).tprod (stdRep k n)) l :=
  isInternal_weightSpace_tprod hchar iSup_weightSpace_stdRep iSup_weightSpace_stdRep

end Field

end TauCeti
