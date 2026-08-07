/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.Degree` is imported publicly: `TauCeti.Algebra.deg` appears in the
-- statement of `TauCeti.Algebra.deg_baseChange`, and the module re-exports the centrality and
-- simplicity of a tensor product, which is what makes `L ⊗[K] A` central simple over `L` visible to
-- instance search from this import alone. `Mathlib.LinearAlgebra.TensorProduct.Opposite` is public
-- because `Aᵐᵒᵖ` occurs in the type of `TauCeti.Algebra.TensorProduct.baseChangeOpAlgEquiv` and
-- because the compiler needs `Algebra.TensorProduct.opAlgEquiv`, used in its body, to be public.
public import TauCeti.Algebra.CentralSimple.Degree
public import Mathlib.LinearAlgebra.TensorProduct.Opposite
-- Non-public: none of these appears in the type of an exported declaration. The retraction
-- `LinearMap.exists_leftInverse_of_injective` and Mathlib's `distribBaseChange` and
-- `algEquivOfLinearEquivTensorProduct` are used only inside proofs and definition bodies, and the
-- complex numbers and the real quaternions only by the worked examples at the end of the file
-- (`TauCeti.Algebra.Central.Quaternion` re-exports `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]`
-- notation there).
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.Central.Quaternion

/-!
# Base change preserves central simplicity

Let `A` be a central simple algebra over a field `K` and let `L / K` be a field extension. This file
proves that the scalar extension `L ⊗[K] A` is central simple *over `L`*.

Simplicity is already available: it is a statement about `L ⊗[K] A` as a ring, so
`TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` applies with `L` the simple factor and `A`
the central simple one. The content here is the other half, centrality over `L`, which is a
genuinely different statement from the centrality over `K` proved in
`TauCeti/Algebra/Central/TensorProduct.lean`: that one asks both factors to be central over `K`, and
for a nontrivial extension the factor `L` is not.

The proof is short once the centralizer computation is available. The centre of `L ⊗[K] A` is
contained in the centralizer of `1 ⊗ A`, which is `L ⊗ 1` because `A` is central over `K`; and
`L ⊗ 1` is exactly the image of `L`.

## Main results

* `TauCeti.Algebra.IsCentral.baseChange`: **`L ⊗[K] A` is central over `L`** when `A` is central
  over `K` and `L` is a commutative `K`-algebra free as a `K`-module. It is an instance, so
  together with `TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` instance search sees
  `L ⊗[K] A` as a central simple `L`-algebra with no glue.
* `TauCeti.Algebra.IsCentral.of_baseChange`: the converse over a field `K`, so centrality is not
  merely preserved by base change but **detected** by it.
* `TauCeti.Algebra.isCentral_baseChange_iff`: the two packaged as an equivalence.
* `TauCeti.Algebra.deg_baseChange`: base change **preserves the degree**,
  `deg L (L ⊗[K] A) = deg K A`.
* `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` and
  `TauCeti.Algebra.TensorProduct.baseChangeOpAlgEquiv`: base change is compatible with `⊗` and with
  `ᵐᵒᵖ`, as `L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B)` and
  `L ⊗[K] Aᵐᵒᵖ ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ`.

Together these are what will let base change descend to a homomorphism of Brauer groups: the first
four statements say the class of `L ⊗[K] A` is defined, and the last two say the assignment respects
the multiplication and the inversion of classes.

## Implementation notes

The forward direction is stated over a commutative semiring `K` and a commutative `K`-algebra `L`
that is free as a `K`-module, the hypotheses the centralizer computation
`TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff` needs; a field extension is the case of
interest and satisfies them. The converse genuinely needs `K` to be a field: it splits off a
`K`-linear retraction `L → K` of the structure map, which is where the vector-space hypothesis
enters, and `L` need only be a nontrivial commutative `K`-algebra.

Both directions are about the `L`-algebra structure on `L ⊗[K] A` coming from the left factor, which
is Mathlib's `Algebra.TensorProduct.leftAlgebra`; `TauCeti.Algebra.deg_baseChange` is read off
`Module.finrank_baseChange` through the characteristic property
`TauCeti.Algebra.deg_eq_of_finrank_eq_sq`, so it never unfolds `TauCeti.Algebra.deg`.

The two compatibility equivalences carry no central-simplicity hypotheses at all - they are
statements about scalar extension as such - but they live here rather than in a general
tensor-product file because it is the central-simple theory that needs them, and because they are
what pairs with the centrality above to make the whole scalar extension a map of central simple
algebras.

The worked examples at the end check both directions on the two standard test cases: `ℂ ⊗[ℝ] ℍ[ℝ]`
is central simple over `ℂ` of degree `2`, while `ℂ ⊗[ℝ] ℂ` is *not* central over `ℂ`, because `ℂ` is
not central over `ℝ`. The second is the failure the converse detects, and it is the reason the
centrality hypothesis on `A` cannot be dropped from the forward direction.

## References

This proves the theorem named in the **Base change preserves central simplicity, then is a
homomorphism** bullet of Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
together with the two compatibilities that bullet asks for. The induced homomorphism of Brauer
groups itself waits on the group structure of `BrauerGroup K`, a separate bullet of the same layer.
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra.IsCentral

section Forward

variable (K L A : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Module.Free K L]
  [Semiring A] [Algebra K A]

/-- **Base change preserves centrality.** If `A` is a central `K`-algebra and `L` is a commutative
`K`-algebra which is free as a `K`-module, then the scalar extension `L ⊗[K] A` is central over
`L`.

Freeness of `L` and centrality of `A` are both used, through the centralizer computation
`TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff`: an element of `L ⊗[K] A` commuting with
every `1 ⊗ₜ a` is of the form `l ⊗ₜ 1`, that is, a scalar. Centrality of `A` cannot be dropped, and
`ℂ ⊗[ℝ] ℂ` is the standard witness. -/
instance baseChange [Algebra.IsCentral K A] : Algebra.IsCentral L (L ⊗[K] A) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    -- Transport to `A ⊗[K] L`, where the centralizer of `A ⊗ 1` is already computed.
    set e := Algebra.TensorProduct.comm K L A with he
    have h : ∀ a : A, Commute (a ⊗ₜ[K] (1 : L)) (e x) := fun a => by
      have := congrArg e (hx ((1 : L) ⊗ₜ[K] a))
      simpa [Commute, SemiconjBy, he, Algebra.TensorProduct.comm_tmul] using this
    obtain ⟨l, hl⟩ := Algebra.TensorProduct.forall_commute_tmul_one_iff.mp h
    refine Algebra.mem_bot.mpr ⟨l, e.injective ?_⟩
    rw [hl, he]
    simp [Algebra.TensorProduct.algebraMap_apply]

end Forward

section Converse

variable {K L A : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L]
  [Semiring A] [Algebra K A]

/-- **Base change detects centrality.** Over a field `K`, if the scalar extension `L ⊗[K] A` is
central over a nontrivial commutative `K`-algebra `L`, then `A` was already central over `K`.

The centre of `A` lands in the centre of `L ⊗[K] A` under `a ↦ 1 ⊗ₜ a`, so a central `a` satisfies
`1 ⊗ₜ a = l ⊗ₜ 1` for some `l : L`. Applying `L ⊗[K] A → A` built from a `K`-linear retraction of
`K → L` turns that identity into `a = g l • 1`. -/
theorem of_baseChange [Algebra.IsCentral L (L ⊗[K] A)] : Algebra.IsCentral K A where
  out a ha := by
    rw [Subalgebra.mem_center_iff] at ha
    -- `1 ⊗ₜ a` is central in `L ⊗[K] A`; centrality of the ring does not depend on the base.
    have hcentral : (1 : L) ⊗ₜ[K] a ∈ Subalgebra.center L (L ⊗[K] A) := by
      refine Subalgebra.mem_center_iff.mpr fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul l b => simp [Algebra.TensorProduct.tmul_mul_tmul, ha b]
      | add y z hy hz => simp [add_mul, mul_add, hy, hz]
    obtain ⟨l, hl⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcentral)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply] at hl
    -- A `K`-linear retraction of the structure map `K → L`.
    have hinj : Function.Injective (Algebra.linearMap K L) := fun x y h =>
      (algebraMap K L).injective (by simpa using h)
    obtain ⟨g, hg⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot (f := Algebra.linearMap K L) |>.mpr hinj)
    have hg1 : g 1 = 1 := by
      simpa using congrArg (fun f : K →ₗ[K] K => f 1) hg
    -- Contract `L ⊗[K] A → K ⊗[K] A → A` along `g`.
    have := congrArg
      (⇑((TensorProduct.lid K A).toLinearMap.comp (TensorProduct.map g LinearMap.id))) hl
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_coe, id_eq, LinearEquiv.coe_coe, TensorProduct.lid_tmul, hg1, one_smul] at this
    exact Algebra.mem_bot.mpr ⟨g l, by rw [Algebra.algebraMap_eq_smul_one, this]⟩

end Converse

end Algebra.IsCentral

namespace Algebra

section Iff

variable (K L A : Type*) [Field K] [CommRing L] [Nontrivial L] [Algebra K L]
  [Semiring A] [Algebra K A]

/-- **Centrality passes both ways along a scalar extension.** Over a field `K`, an algebra `A` is
central exactly when its scalar extension along a nontrivial commutative `K`-algebra `L` is central
over `L`. Freeness of `L` is automatic here, `K` being a field. -/
theorem isCentral_baseChange_iff :
    Algebra.IsCentral L (L ⊗[K] A) ↔ Algebra.IsCentral K A :=
  ⟨fun _ => Algebra.IsCentral.of_baseChange (K := K) (L := L) (A := A),
    fun _ => Algebra.IsCentral.baseChange K L A⟩

end Iff

/-! ### The degree of a scalar extension -/

section Degree

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **Base change preserves the degree** of a finite-dimensional central simple algebra: the scalar
extension `L ⊗[K] A` has the same dimension over `L` that `A` has over `K`, and that dimension is
the square of `deg K A`, so the two degrees agree. -/
theorem deg_baseChange : deg L (L ⊗[K] A) = deg K A :=
  deg_eq_of_finrank_eq_sq (by
    rw [Module.finrank_baseChange (R := L) (S := K) (M' := A), deg_sq])

end Degree

end Algebra

/-! ### Base change is compatible with `⊗` and with `ᵐᵒᵖ` -/

namespace Algebra.TensorProduct

variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L]
  [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- **Base change distributes over the tensor product**: extending `A ⊗[K] B` to `L` is the same as
extending each factor and tensoring over `L`.

This is Mathlib's linear equivalence `TensorProduct.AlgebraTensorModule.distribBaseChange` upgraded
to an algebra equivalence; the multiplicativity is checked on pure tensors, where both sides are
`(l₁ * l₂) ⊗ₜ (a₁ * a₂)` tensored with `1 ⊗ₜ (b₁ * b₂)`. No hypothesis beyond associativity of the
scalars is needed, so neither factor has to be central or simple. -/
@[expose] def baseChangeTensorAlgEquiv :
    L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K L A B)
    (fun l₁ l₂ z₁ z₂ => by
      induction z₁ using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [TensorProduct.tmul_add, add_mul, hx, hy]
      | tmul a₁ b₁ =>
        induction z₂ using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [TensorProduct.tmul_add, mul_add, hx, hy]
        | tmul a₂ b₂ => simp [Algebra.TensorProduct.tmul_mul_tmul])
    (by simp [Algebra.TensorProduct.one_def])

@[simp]
theorem baseChangeTensorAlgEquiv_tmul (l : L) (a : A) (b : B) :
    baseChangeTensorAlgEquiv K L A B (l ⊗ₜ[K] (a ⊗ₜ[K] b)) = (l ⊗ₜ[K] a) ⊗ₜ[L] (1 ⊗ₜ[K] b) :=
  rfl

/-- **Base change commutes with passing to the opposite algebra.** Together with
`TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` this is what makes base change respect both
the multiplication and the inversion of Brauer classes. -/
@[expose] def baseChangeOpAlgEquiv : L ⊗[K] Aᵐᵒᵖ ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ :=
  (Algebra.TensorProduct.congr (AlgEquiv.toOpposite L L)
      (AlgEquiv.refl (R := K) (A₁ := Aᵐᵒᵖ))).trans (Algebra.TensorProduct.opAlgEquiv K L L A)

@[simp]
theorem baseChangeOpAlgEquiv_tmul (l : L) (a : Aᵐᵒᵖ) :
    baseChangeOpAlgEquiv K L A (l ⊗ₜ[K] a) = MulOpposite.op (l ⊗ₜ[K] a.unop) :=
  rfl

end Algebra.TensorProduct

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- Complexifying the real quaternions gives a central `ℂ`-algebra: instance search finds it. -/
example : Algebra.IsCentral ℂ (ℂ ⊗[ℝ] ℍ[ℝ]) := inferInstance

/-- It is simple too, so `ℂ ⊗[ℝ] ℍ[ℝ]` is a central simple `ℂ`-algebra with no glue at all. -/
example : IsSimpleRing (ℂ ⊗[ℝ] ℍ[ℝ]) := inferInstance

/-- Complexification keeps the degree: `ℂ ⊗[ℝ] ℍ[ℝ]` has degree `2`, like `ℍ[ℝ]` itself. (Being
split over the algebraically closed `ℂ`, it is in fact `M₂(ℂ)`.) -/
example : Algebra.deg ℂ (ℂ ⊗[ℝ] ℍ[ℝ]) = 2 := by
  rw [Algebra.deg_baseChange]
  exact Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)

/-- The negative control for `TauCeti.Algebra.IsCentral.baseChange`: `ℂ ⊗[ℝ] ℂ` is not central over
`ℂ`, because `ℂ` is not central over `ℝ`. So centrality of the algebra being extended is doing real
work, and `ℂ` is exactly the simple finite-dimensional `ℝ`-algebra that base change excludes.

The proof runs the converse `TauCeti.Algebra.IsCentral.of_baseChange` backwards: assuming
`ℂ ⊗[ℝ] ℂ` central over `ℂ` makes `ℂ` central over `ℝ`, and then `Complex.I`, central because `ℂ` is
commutative, would have to be real. -/
example : ¬ Algebra.IsCentral ℂ (ℂ ⊗[ℝ] ℂ) := fun _ => by
  have h : Algebra.IsCentral ℝ ℂ := Algebra.IsCentral.of_baseChange (K := ℝ) (L := ℂ) (A := ℂ)
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp
    (h.out (Subalgebra.mem_center_iff.mpr fun b => mul_comm b Complex.I))
  simpa using congrArg Complex.im hr

end Examples

end TauCeti
