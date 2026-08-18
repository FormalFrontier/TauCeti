/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.RingTheory.Subring.RationalBaseChange

/-!
# The Kostant form is an integral form of the enveloping algebra

Let `L` be a Lie algebra over `ℚ` and let `e : ι → L` and `h : κ → L` be the two distinguished
families out of which `TauCeti.UniversalEnvelopingAlgebra.kostantForm` is built. As soon as those
families generate `L` as a Lie algebra, the resulting subring is an integral form of the whole
enveloping algebra: extending its scalars to `ℚ` recovers `U(L)`,

```text
ℚ ⊗[ℤ] kostantForm e h ≃ₐ[ℚ] UniversalEnvelopingAlgebra ℚ L.
```

The spanning half of that statement is
`TauCeti.UniversalEnvelopingAlgebra.span_kostantForm_eq_top`, proved with the form itself. What
this file adds is that the comparison map is an isomorphism and not merely a surjection: it is
`Subring.ratBaseChangeEquiv` applied to the form, the point being that the map out of `ℚ ⊗[ℤ] R` is
injective for every subring `R` of a `ℚ`-algebra, so a rationally spanning subring is automatically
a `ℤ`-form.

Nothing here bounds the form from the other side. That the form is a *free* `ℤ`-module on the
ordered monomials in divided powers, the integral Poincaré--Birkhoff--Witt theorem, is a separate
statement and is not proved here; the results below say only that the form rationally spans the
enveloping algebra and allows denominators to be cleared.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.kostantFormBaseChange`: the isomorphism
  `ℚ ⊗[ℤ] kostantForm e h ≃ₐ[ℚ] UniversalEnvelopingAlgebra ℚ L`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exists_natCast_smul_mem_kostantForm`: every element of the
  enveloping algebra is carried into the form by a nonzero natural number.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open scoped TensorProduct

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

variable (e : ι → L) (h : κ → L)

/-- **The Kostant form is an integral form of the enveloping algebra.** Extending its scalars from
`ℤ` to `ℚ` recovers `U(L)`. -/
noncomputable def kostantFormBaseChange
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) :
    ℚ ⊗[ℤ] (kostantForm e h) ≃ₐ[ℚ] U :=
  Subring.ratBaseChangeEquiv _ (span_kostantForm_eq_top e h hgen)

@[simp]
theorem kostantFormBaseChange_tmul
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤)
    (q : ℚ) (x : kostantForm e h) :
    kostantFormBaseChange e h hgen (q ⊗ₜ[ℤ] x) = q • (x : U) :=
  Subring.ratBaseChangeEquiv_tmul _ _ q x

/-- The Kostant form allows denominators to be cleared: every element of the enveloping algebra is
carried into it by some nonzero natural number. -/
theorem exists_natCast_smul_mem_kostantForm
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) (u : U) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • u ∈ kostantForm e h :=
  Subring.exists_natCast_smul_mem _ (span_kostantForm_eq_top e h hgen) u

end TauCeti.UniversalEnvelopingAlgebra
