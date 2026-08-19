/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.IsSplittingField` and `TauCeti.Algebra.deg` occur in the statements below, and
-- `TauCeti.Algebra.isSplittingField_iff_deg` is how the splitting is assembled. This import also
-- re-exports `Mathlib.RingTheory.TensorProduct.Basic` (the `⊗[K]` notation and the algebra
-- structure on `L ⊗[K] A`) and, through `TauCeti.Algebra.CentralSimple.Degree`, the simplicity of
-- `L ⊗[K] A` as an instance -- which is what makes the action below faithful.
public import TauCeti.Algebra.CentralSimple.Splitting
-- `TauCeti.Bimodule` supplies the left-right action transported to the orientation used here.
public import TauCeti.Algebra.CentralSimple.Bimodule
-- Non-public: none of these appears in the type of an exported declaration. The tower law and the
-- dimension of an endomorphism algebra, the injective-implies-surjective criterion, the matrix
-- form of an endomorphism algebra and the faithfulness of a module over a simple ring are used
-- only inside proofs, and the complex numbers and the real quaternions only by the worked examples.
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Algebra.Central.Quaternion
import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.RingTheory.Semisimple.DoubleCentralizer

/-!
# Subfields of a central simple algebra, and the ones that split it

Let `A` be a finite-dimensional central simple algebra over a field `K`. A **subfield** of `A` is a
field `L` together with a `K`-algebra homomorphism `f : L →ₐ[K] A`; no injectivity hypothesis is
needed, because a ring homomorphism out of a field into a nontrivial ring is automatically
injective (`RingHom.injective`), so `f` really does exhibit `L` as a subfield of `A`.

This file proves the two facts about such an `L` that Layer 6 of the semisimple-algebra roadmap
asks for:

* its degree is bounded by the degree of the algebra,
  `Module.finrank K L ≤ TauCeti.Algebra.deg K A`;
* when that bound is attained, **`L` splits `A`**: `L ⊗[K] A ≃ₐ[L] M_{deg K A}(L)`.

Together these say that a subfield of degree `deg K A` is a *maximal* subfield -- nothing bigger
fits -- and that a maximal subfield of that degree is a splitting field. This is the classical
route to a splitting field that stays inside the algebra, in contrast with the algebraically
closed extension of `TauCeti/Algebra/CentralSimple/Splitting.lean`, which leaves it.

## The module that does the work

Both statements come from one construction. A subfield `f : L →ₐ[K] A` makes `A` into an
`A`-`L`-bimodule: `A` acts on the left by multiplication and `L` on the right through `f`. Because
`L` is *commutative* this right action is packaged as a left action of the scalar extension
`L ⊗[K] A` itself -- no opposite algebra is needed on the `L` side -- and the resulting module is
`TauCeti.BaseChangeModule f`, with `l ⊗ₜ a` acting by `x ↦ a * x * f l`.

Restricting that action along `L → L ⊗[K] A` makes `BaseChangeModule f` an `L`-vector space, of
dimension `Module.finrank K A / Module.finrank K L` by the tower law, and the action becomes an
`L`-algebra homomorphism

`TauCeti.BaseChangeModule.toEndL f : L ⊗[K] A →ₐ[L] Module.End L (BaseChangeModule f)`.

It is **injective**, because `L ⊗[K] A` is a simple ring (base change of a central simple algebra)
and a nontrivial module over a simple ring is faithful
(`TauCeti.faithfulSMul_of_isSimpleRing`). Everything else is dimension counting: writing
`n = deg K A`, `d = Module.finrank K L` and `m = Module.finrank L (BaseChangeModule f)`, injectivity
gives `n ^ 2 ≤ m ^ 2` and the tower law gives `d * m = n ^ 2`, whence `d ≤ n`; and when `d = n` the
two dimensions agree, so the injection is onto and `L ⊗[K] A` *is* the endomorphism algebra
`Module.End L (BaseChangeModule f)`, a matrix algebra of size `m = n`.

## Main results

* `TauCeti.BaseChangeModule`: `A` as a module over the scalar extension `L ⊗[K] A`, with the action
  `TauCeti.BaseChangeModule.toEnd` and its `L`-algebra form `TauCeti.BaseChangeModule.toEndL`.
* `TauCeti.BaseChangeModule.toEndL_injective`: the action is faithful.
* `TauCeti.Algebra.finrank_le_deg`: **a subfield of a central simple algebra has degree at most the
  degree of the algebra.**
* `TauCeti.BaseChangeModule.algEquivEnd` and `TauCeti.Algebra.isSplittingField_of_finrank_eq_deg`:
  **a subfield of degree `deg K A` splits `A`**, through the identification
  `L ⊗[K] A ≃ₐ[L] Module.End L (BaseChangeModule f)`.
* `TauCeti.Algebra.bijective_of_finrank_eq_deg`: a subfield of degree `deg K A` is **maximal**: any
  subfield of `A` receiving it does so by an isomorphism.

## Implementation notes

`TauCeti.BaseChangeModule f` reuses `TauCeti.Bimodule` from
`TauCeti/Algebra/CentralSimple/Bimodule.lean` with codomain `Aᵐᵒᵖ` and the opposite of `f`. Its
scalar action is transported along `A ≃ₐ[K] Aᵐᵒᵖᵐᵒᵖ`, giving the required orientation over
`L ⊗[K] A`:
`l ⊗ₜ a` acts by `x ↦ a * x * f l`. This orientation makes the conclusion land on the tensor
product occurring in `TauCeti.Algebra.IsSplittingField`, rather than on its opposite.

The `L`-module structure on `TauCeti.BaseChangeModule f` is defined by restricting scalars along
`algebraMap L (L ⊗[K] A)` rather than as a separate right-multiplication action, which is what
makes `TauCeti.BaseChangeModule.toEndL` available as `Algebra.lsmul` and the scalar towers
formal. The `K`-structure is the one `A` already has, so `TauCeti.BaseChangeModule.of` is the
identity linear equivalence and dimensions over `K` transfer by `rfl`-like transport.

Nothing here needs `A` to be a division algebra: the classical statement is about a maximal
subfield of a central *division* algebra, but the argument only uses simplicity of `L ⊗[K] A`, so
it is stated for every finite-dimensional central simple `A`. What a division algebra adds is the
*existence* of a subfield attaining the bound, which is a separate question, settled by
`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg` in
`TauCeti/Algebra/CentralSimple/MaximalSubfield.lean`.

## References

This is the maximal-subfield half of the fourth bullet of Layer 6 ("Splitting fields, maximal
subfields, and the index") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13.
-/

public section

namespace TauCeti

open scoped TensorProduct

/-! ### The algebra as a module over its scalar extension -/

section Defs

variable {K L A : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  [Semiring A] [Algebra K A]

local macro "rightAlgHom% " f:term : term =>
  `(($f).toOpposite fun x y ↦ by simp [commute_iff_eq, ← map_mul, mul_comm])

local macro "opOpMap%" : term =>
  `(Algebra.TensorProduct.map (AlgHom.id K L) (AlgEquiv.opOp K A).toAlgHom)

/-- `A` regarded as a module over the scalar extension `L ⊗[K] A`, along a `K`-algebra homomorphism
`f : L →ₐ[K] A` out of a **commutative** algebra: the pure tensor `l ⊗ₜ a` acts by
`x ↦ a * x * f l`.

Equivalently this is the `A`-`L`-bimodule `A`, with `A` acting on the left by multiplication and
`L` on the right through `f`; commutativity of `L` is what lets the right action be packaged as a
left action of `L ⊗[K] A` with no opposite algebra. It is a type synonym for `A` so that `A` itself
is left without an `L ⊗[K] A`-action, and so that different subfields can act at the same time. -/
@[expose] def BaseChangeModule (f : L →ₐ[K] A) : Type _ := Bimodule (rightAlgHom% f)

namespace BaseChangeModule

variable (f : L →ₐ[K] A)

instance : AddCommMonoid (BaseChangeModule f) :=
  inferInstanceAs (AddCommMonoid (Bimodule (rightAlgHom% f)))

-- Conditional, so that the endomorphism ring of `BaseChangeModule f` is a ring and not merely a
-- semiring when `A` is one; nothing in the construction itself needs the negation.
instance {A : Type*} [Ring A] [Algebra K A] (f : L →ₐ[K] A) : AddCommGroup (BaseChangeModule f) :=
  inferInstanceAs (AddCommGroup (Bimodule (rightAlgHom% f)))

instance : Module K (BaseChangeModule f) :=
  inferInstanceAs (Module K (Bimodule (rightAlgHom% f)))

instance [Nontrivial A] : Nontrivial (BaseChangeModule f) :=
  inferInstanceAs (Nontrivial (Bimodule (rightAlgHom% f)))

instance [Module.Finite K A] : Module.Finite K (BaseChangeModule f) :=
  Module.Finite.equiv ((MulOpposite.opLinearEquiv K).trans (Bimodule.of (rightAlgHom% f)))

/-- `BaseChangeModule f` is `A` again as a `K`-module: only the `L ⊗[K] A`-action is new. -/
def of : A ≃ₗ[K] BaseChangeModule f :=
  (MulOpposite.opLinearEquiv K).trans (Bimodule.of (rightAlgHom% f))

noncomputable instance : Module (L ⊗[K] A) (BaseChangeModule f) :=
  Module.compHom (M := Bimodule (rightAlgHom% f)) opOpMap%.toRingHom

/-- The action of `L ⊗[K] A` on `A` defining `BaseChangeModule f`, as a `K`-algebra homomorphism
into `Module.End K A`, transported from `TauCeti.Bimodule.toEnd`. -/
noncomputable def toEnd : L ⊗[K] A →ₐ[K] Module.End K A :=
  ((MulOpposite.opLinearEquiv K).conjAlgEquiv K).symm.toAlgHom.comp
    ((Bimodule.toEnd (rightAlgHom% f)).comp opOpMap%)

/-- A pure tensor `l ⊗ₜ a` acts on `x : A` through `toEnd f` by `x ↦ a * x * f l`. -/
@[simp]
theorem toEnd_tmul_apply (l : L) (a x : A) : toEnd f (l ⊗ₜ a) x = a * x * f l := by
  simp [toEnd, mul_assoc]

/-- A scalar `r : L ⊗[K] A` acts on `BaseChangeModule f` through `toEnd f`. This is the defining
equation of the module structure, and the single place it is unfolded: everything else rewrites
with it instead of reasoning up to definitional equality. -/
theorem smul_def (r : L ⊗[K] A) (x : A) : r • of f x = of f (toEnd f r x) := by
  change opOpMap% r • Bimodule.of (rightAlgHom% f) (MulOpposite.op x) =
    Bimodule.of (rightAlgHom% f) (MulOpposite.op (toEnd f r x))
  rw [Bimodule.smul_def]
  rfl

/-- A pure tensor `l ⊗ₜ a` acts on `BaseChangeModule f` by `x ↦ a * x * f l`. -/
@[simp]
theorem smul_of (l : L) (a x : A) : (l ⊗ₜ a : L ⊗[K] A) • of f x = of f (a * x * f l) := by
  rw [smul_def, toEnd_tmul_apply]

instance : IsScalarTower K (L ⊗[K] A) (BaseChangeModule f) where
  smul_assoc c r x := by
    rw [← (of f).apply_symm_apply x, smul_def, smul_def, map_smul (toEnd f),
      LinearMap.smul_apply, map_smul (of f)]

noncomputable instance : Module L (BaseChangeModule f) :=
  Module.compHom (M := BaseChangeModule f) (algebraMap L (L ⊗[K] A))

/-- `L` acts on `BaseChangeModule f` through its image in `L ⊗[K] A`. This is the defining equation
of the `L`-module structure; `TauCeti.BaseChangeModule.lsmul_of` reads it off concretely. -/
theorem lsmul_def (l : L) (x : BaseChangeModule f) :
    l • x = (algebraMap L (L ⊗[K] A) l) • x := rfl

/-- Concretely, `L` acts on `BaseChangeModule f` by **right multiplication** through `f`. This is
the right action the type synonym exists to carry, and the reason the pairing with the left action
of `A` needs `L` to be commutative. -/
@[simp]
theorem lsmul_of (l : L) (x : A) : l • of f x = of f (x * f l) := by
  rw [lsmul_def, Algebra.TensorProduct.algebraMap_apply, smul_of, one_mul,
    Algebra.algebraMap_self_apply]

instance : IsScalarTower L (L ⊗[K] A) (BaseChangeModule f) where
  smul_assoc l r x := by
    rw [lsmul_def, Algebra.smul_def, mul_smul]

instance : SMulCommClass (L ⊗[K] A) L (BaseChangeModule f) where
  smul_comm r l x := by
    simp only [lsmul_def, ← mul_smul, Algebra.commutes]

instance : IsScalarTower K L (BaseChangeModule f) where
  smul_assoc c l x := by
    have h : algebraMap L (L ⊗[K] A) (c • l) = c • algebraMap L (L ⊗[K] A) l := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
    rw [lsmul_def, lsmul_def, h, smul_assoc]

/-- Over the base field nothing has changed: `BaseChangeModule f` has the dimension of `A`. -/
theorem finrank_eq : Module.finrank K (BaseChangeModule f) = Module.finrank K A :=
  (of f).symm.finrank_eq

end BaseChangeModule

end Defs

/-! ### The action of the scalar extension is faithful -/

section Field

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  {A : Type*} [Ring A] [Algebra K A] (f : L →ₐ[K] A)

namespace BaseChangeModule

/-- The tower law for `A`, with its `L`-module structure induced by `f`. -/
theorem finrank_mul_finrank :
    Module.finrank K L * Module.finrank L (BaseChangeModule f) = Module.finrank K A := by
  rw [Module.finrank_mul_finrank K L (BaseChangeModule f), finrank_eq]

/-- The action of `L ⊗[K] A` on `BaseChangeModule f` as an `L`-algebra homomorphism. -/
noncomputable def toEndL : L ⊗[K] A →ₐ[L] Module.End L (BaseChangeModule f) :=
  _root_.Algebra.lsmul L L (BaseChangeModule f)

@[simp]
theorem toEndL_apply (r : L ⊗[K] A) (x : BaseChangeModule f) : toEndL f r x = r • x := by
  simp [toEndL]

/-- The action of the scalar extension on `BaseChangeModule f` is faithful. -/
theorem toEndL_injective [Algebra.IsCentral K A] [IsSimpleRing A] :
    Function.Injective (toEndL f) := by
  have : FaithfulSMul (L ⊗[K] A) (BaseChangeModule f) := faithfulSMul_of_isSimpleRing
  exact fun r r' h ↦ eq_of_smul_eq_smul (α := BaseChangeModule f) fun m ↦ by
    simpa using LinearMap.congr_fun h m

variable [FiniteDimensional K A]

instance : Module.Finite L (BaseChangeModule f) :=
  Module.Finite.of_restrictScalars_finite K L (BaseChangeModule f)

variable [Algebra.IsCentral K A] [IsSimpleRing A]

-- The dimension inequality obtained from the faithful scalar-extension action.
private theorem finrank_le_finrank_mul_finrank :
    Module.finrank K A
      ≤ Module.finrank L (BaseChangeModule f) * Module.finrank L (BaseChangeModule f) := by
  have h := (toEndL f).toLinearMap.finrank_le_finrank_of_injective (toEndL_injective f)
  rwa [Module.finrank_baseChange, Module.finrank_linearMap] at h

/-- If `L` has degree `deg K A`, then `BaseChangeModule f` has dimension `deg K A` over `L`. -/
theorem finrank_eq_deg (h : Module.finrank K L = Algebra.deg K A) :
    Module.finrank L (BaseChangeModule f) = Algebra.deg K A := by
  have hmul := finrank_mul_finrank f
  rw [h, ← Algebra.deg_sq K A, sq] at hmul
  exact Nat.eq_of_mul_eq_mul_left (Algebra.deg_pos K A) hmul

/-- The scalar extension by a subfield of degree `deg K A` is isomorphic to the algebra of
`L`-linear endomorphisms of `BaseChangeModule f`. -/
noncomputable def algEquivEnd (h : Module.finrank K L = Algebra.deg K A) :
    L ⊗[K] A ≃ₐ[L] Module.End L (BaseChangeModule f) :=
  AlgEquiv.ofBijective (toEndL f) <| by
    have hdim : Module.finrank L (L ⊗[K] A)
        = Module.finrank L (Module.End L (BaseChangeModule f)) := by
      rw [Module.finrank_baseChange, Module.finrank_linearMap, finrank_eq_deg f h, ← sq,
        Algebra.deg_sq]
    exact ⟨toEndL_injective f,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (toEndL f).toLinearMap)
        hdim).1 (toEndL_injective f)⟩

/-- The equivalence `algEquivEnd f h` sends a scalar-extension element to its action on
`BaseChangeModule f`. -/
@[simp]
theorem algEquivEnd_apply (h : Module.finrank K L = Algebra.deg K A) (r : L ⊗[K] A)
    (x : BaseChangeModule f) : algEquivEnd f h r x = r • x :=
  toEndL_apply f r x

end BaseChangeModule

/-! ### Subfields, their degrees, and the splitting theorem -/

namespace Algebra

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- A subfield of a central simple algebra has degree at most the degree of the algebra. -/
theorem finrank_le_deg (f : L →ₐ[K] A) : Module.finrank K L ≤ deg K A := by
  have hmul := BaseChangeModule.finrank_mul_finrank f
  have hle := BaseChangeModule.finrank_le_finrank_mul_finrank f
  rw [← deg_sq K A, sq] at hmul hle
  have hdm : deg K A ≤ Module.finrank L (BaseChangeModule f) :=
    Nat.mul_self_le_mul_self_iff.1 hle
  refine Nat.le_of_mul_le_mul_right ?_ (deg_pos K A)
  calc Module.finrank K L * deg K A
      ≤ Module.finrank K L * Module.finrank L (BaseChangeModule f) :=
        Nat.mul_le_mul_left _ hdm
    _ = deg K A * deg K A := hmul

/-- A subfield of degree `deg K A` is a splitting field of `A`. -/
theorem isSplittingField_of_finrank_eq_deg (f : L →ₐ[K] A)
    (h : Module.finrank K L = deg K A) : IsSplittingField K A L :=
  (isSplittingField_iff_deg K A L).2
    ⟨(BaseChangeModule.algEquivEnd f h).trans
      (endAlgEquivMatrix L (BaseChangeModule f) (BaseChangeModule.finrank_eq_deg f h))⟩

/-- If subfields `L` and `L'` of `A` satisfy `Module.finrank K L = deg K A`, then every
`K`-algebra homomorphism `L →ₐ[K] L'` is bijective. -/
theorem bijective_of_finrank_eq_deg {L' : Type*} [Field L'] [Algebra K L']
    (g : L' →ₐ[K] A) (i : L →ₐ[K] L') (h : Module.finrank K L = deg K A) :
    Function.Bijective i := by
  have : FiniteDimensional K L' := Module.Finite.of_injective g.toLinearMap g.injective
  have : FiniteDimensional K L := Module.Finite.of_injective i.toLinearMap i.injective
  have hle : Module.finrank K L ≤ Module.finrank K L' :=
    i.toLinearMap.finrank_le_finrank_of_injective i.injective
  have hge : Module.finrank K L' ≤ Module.finrank K L := h ▸ finrank_le_deg g
  exact ⟨i.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := i.toLinearMap) (le_antisymm hle hge)).1 i.injective⟩

end Algebra

end Field

/-! ### Worked example: the complex numbers inside the real quaternions -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- **`ℂ` is a maximal subfield of the real quaternions.** The `ℝ`-algebra homomorphism sending
`Complex.I` to the quaternion `i` exhibits `ℂ` as a subfield of `ℍ[ℝ]`, and its degree `2` is the
degree of `ℍ[ℝ]`, which by `TauCeti.Algebra.finrank_le_deg` is the largest a subfield can have. -/
example : ∃ _ : ℂ →ₐ[ℝ] ℍ[ℝ], Module.finrank ℝ ℂ = Algebra.deg ℝ ℍ[ℝ] := by
  have hI : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ = -1 := by ext <;> simp
  refine ⟨Complex.lift ⟨_, hI⟩, ?_⟩
  rw [Complex.finrank_real_complex,
    Algebra.deg_eq_of_finrank_eq_sq (K := ℝ) (A := ℍ[ℝ]) (n := 2)
      (by rw [Quaternion.finrank_eq_four]; norm_num)]

/-- **`ℂ` splits the real quaternions, as a maximal subfield.** This is the same conclusion as the
example in `TauCeti/Algebra/CentralSimple/Splitting.lean`, but reached from inside `ℍ[ℝ]`: there it
came from `ℂ` being algebraically closed, here from `ℂ` being a subfield of the right degree. -/
example : Algebra.IsSplittingField ℝ ℍ[ℝ] ℂ := by
  have hI : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ = -1 := by ext <;> simp
  refine Algebra.isSplittingField_of_finrank_eq_deg (Complex.lift ⟨_, hI⟩) ?_
  rw [Complex.finrank_real_complex,
    Algebra.deg_eq_of_finrank_eq_sq (K := ℝ) (A := ℍ[ℝ]) (n := 2)
      (by rw [Quaternion.finrank_eq_four]; norm_num)]

/-- **No subfield of `ℍ[ℝ]` is bigger than `ℂ`.** Every subfield of the real quaternions has degree
at most `2`; there is no room for a cubic or quartic one, even though `ℍ[ℝ]` has dimension `4` over
`ℝ`. This is the negative half of maximality, and it needs the general bound: it does not follow
from the splitting of `ℍ[ℝ]` by `ℂ` alone. -/
example (L : Type) [Field L] [Algebra ℝ L] (f : L →ₐ[ℝ] ℍ[ℝ]) : Module.finrank ℝ L ≤ 2 := by
  have h : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  exact h ▸ Algebra.finrank_le_deg f

end Examples

end TauCeti
