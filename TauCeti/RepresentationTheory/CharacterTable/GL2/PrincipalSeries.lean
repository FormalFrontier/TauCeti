/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional

/-!
# The principal series of `GL₂(𝔽_q)`

A pair of characters `α, β : Fˣ →* ℂˣ` of the multiplicative group of a field inflates through the
split torus to a one-dimensional character of the Borel subgroup `B = T U` of upper-triangular
matrices, on which the unipotent radical acts trivially. Inducing that character up to `GL₂` is
**parabolic induction**, and the resulting representation

`GL2PrincipalSeries F α β = Ind_B^{GL₂} (α ⊗ β)`

is the **principal series**. Over a finite field with `q` elements the Borel subgroup has index
`q + 1`, so the principal series has dimension `q + 1`.

This file builds the characters of `B`, the one-dimensional representations carrying them, the
principal series itself, and its dimension. The irreducibility criterion `α ≠ β` and the
decomposition of the boundary case `α = β` into a linear character and the Steinberg
representation are not proved here.

## Main definitions

* `TauCeti.GL2Borel.linearChar`: the character `b ↦ α b₁₁ · β b₂₂` of the Borel subgroup obtained
  by inflating a pair of characters through the split torus.
* `TauCeti.GL2Borel.linearRep`: the one-dimensional representation carrying that character.
* `TauCeti.GL2BorelChar`: the same representation as an object of `FDRep ℂ B`.
* `TauCeti.GL2PrincipalSeries`: the principal series `Ind_B^{GL₂}(α ⊗ β)`.

## Main statements

* `TauCeti.GL2Borel.linearChar_unipotentHom`: the character is trivial on the unipotent radical, so
  it is genuinely inflated from the split torus (`TauCeti.GL2Borel.linearChar_torusHom`).
* `TauCeti.GL2Borel.linearChar_inj`: the pair `(α, β)` is recovered from the character it
  inflates to, so distinct pairs give distinct one-dimensional representations of `B`.
* `TauCeti.GL2Borel.linearChar_self`: for `α = β` the Borel character is the determinant twisted by
  `α`; this is the boundary case whose principal series is reducible.
* `TauCeti.GL2Borel.character_linearRep`: the character of a one-dimensional representation is the
  scalar it acts by.
* `TauCeti.finrank_GL2PrincipalSeries` and `TauCeti.character_one_GL2PrincipalSeries`: the
  principal series has dimension `q + 1`.

## Implementation notes

`TauCeti.GL2Borel.linearChar` and `TauCeti.GL2Borel.linearRep` are stated over an arbitrary
commutative ring `R` for the group — the Borel subgroup itself is defined over any commutative
ring — and over the weakest coefficients each needs: the character only multiplies values in `kˣ`,
so it lives over a `CommMonoid k`, while the representation needs a module structure on the line
and so lives over a `CommSemiring k`. Nothing in the inflation uses finiteness or the complex
numbers; the complex, finite-field hypotheses enter only with `TauCeti.GL2PrincipalSeries`, where
they supply the finite index that makes induction finite-dimensional.

`TauCetiRoadmap/RepresentationTheory/CharacterTheory/Suggested.lean` pins `GL2PrincipalSeries`
with a `[DecidableEq F]` hypothesis. It is not needed: `GL (Fin 2) F` needs decidable equality only
on the index type `Fin 2`, and carrying an unused instance argument would be flagged by the
`unusedArguments` linter, so it is dropped here.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The Borel and the principal series": the targets `GL2PrincipalSeries` and
  `character_one_GL2PrincipalSeries`, whose names are the roadmap's.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 5.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 5.2.
-/

public section

open Matrix

namespace TauCeti

namespace GL2Borel

section CommMonoid

variable {R : Type*} [CommRing R] {k : Type*} [CommMonoid k]

/-! ### The linear characters of the Borel subgroup -/

/-- **The linear character of the Borel subgroup attached to a pair of characters.** The two
diagonal entries of an upper-triangular matrix are units, and `TauCeti.GL2Borel.diag` reads them
off; the character `α ⊗ β` sends `b` to `α b₁₁ · β b₂₂`. It is inflated from the split torus,
being trivial on the unipotent radical. -/
def linearChar (α β : Rˣ →* kˣ) : GL2Borel R →* kˣ :=
  (α.comp (MonoidHom.fst Rˣ Rˣ) * β.comp (MonoidHom.snd Rˣ Rˣ)).comp diag

@[simp]
theorem linearChar_apply (α β : Rˣ →* kˣ) (g : GL2Borel R) :
    linearChar α β g = α (diag g).1 * β (diag g).2 :=
  (rfl)

/-- On the split torus the character is literally `α ⊗ β`. -/
theorem linearChar_torusHom (α β : Rˣ →* kˣ) (p : Rˣ × Rˣ) :
    linearChar α β (torusHom p) = α p.1 * β p.2 := by
  simp

/-- The value of the character on the explicit upper-triangular matrix `!![a, b; 0, d]`. -/
theorem linearChar_mk (α β : Rˣ →* kˣ) (a d : Rˣ) (b : R) :
    linearChar α β ⟨mk a d b, mk_mem a d b⟩ = α a * β d := by
  simp

/-- **The character is trivial on the unipotent radical**, which is what makes it an inflation from
the split torus rather than a general character of the Borel subgroup. -/
theorem linearChar_unipotentHom (α β : Rˣ →* kˣ) (b : R) :
    linearChar α β (unipotentHom b) = 1 := by
  simp [diag_unipotentHom]

/-- **The pair of characters is recovered from the character it inflates to.** Restricting along
the two coordinate embeddings of the split torus returns `α` and `β`, so distinct pairs inflate to
distinct characters of `B`, hence to non-isomorphic one-dimensional representations. -/
theorem linearChar_inj {α β α' β' : Rˣ →* kˣ} :
    linearChar (R := R) α β = linearChar α' β' ↔ α = α' ∧ β = β' := by
  refine ⟨fun h => ⟨MonoidHom.ext fun a => ?_, MonoidHom.ext fun d => ?_⟩, ?_⟩
  · have := congrArg (fun χ => χ (torusHom (a, 1))) h
    simpa [linearChar_torusHom] using this
  · have := congrArg (fun χ => χ (torusHom (1, d))) h
    simpa [linearChar_torusHom] using this
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The equal-character case is a determinant twist.** When the two characters agree, the Borel
character is the restriction of `α ∘ det`, the linear character of `GL₂` whose principal series is
the reducible one. -/
theorem linearChar_self (α : Rˣ →* kˣ) (g : GL2Borel R) :
    linearChar α α g = α (Matrix.GeneralLinearGroup.det (g : GL (Fin 2) R)) := by
  rw [det_diag, map_mul, linearChar_apply]

end CommMonoid

section CommSemiring

variable {R : Type*} [CommRing R] {k : Type*} [CommSemiring k]

/-! ### The one-dimensional representation carrying a linear character -/

/-- **The one-dimensional representation of the Borel subgroup** on which `b` acts by the scalar
`TauCeti.GL2Borel.linearChar α β b`. This is the representation `α ⊗ β` that parabolic induction
consumes. -/
def linearRep (α β : Rˣ →* kˣ) : Representation k (GL2Borel R) k where
  toFun g := LinearMap.lsmul k k (linearChar α β g : k)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp only [map_mul, Units.val_mul, LinearMap.lsmul_apply, smul_eq_mul, Module.End.mul_apply]
    ring

@[simp]
theorem linearRep_apply (α β : Rˣ →* kˣ) (g : GL2Borel R) (x : k) :
    linearRep α β g x = (linearChar α β g : k) * x :=
  (rfl)

end CommSemiring

section Field

variable {R : Type*} [CommRing R] {k : Type*} [Field k]

/-- **The character of a one-dimensional representation is the scalar it acts by**: the trace of
multiplication by `c` on the line `k` is `c`. -/
@[simp]
theorem character_linearRep (α β : Rˣ →* kˣ) (g : GL2Borel R) :
    (linearRep (R := R) α β).character g = (linearChar α β g : k) := by
  rw [Representation.character]
  have h : (linearRep (R := R) (k := k) α β) g =
      LinearMap.id.smulRight (linearChar α β g : k) := by
    refine LinearMap.ext fun x => ?_
    simp [mul_comm]
  rw [h, LinearMap.trace_smulRight, LinearMap.id_apply]

end Field

end GL2Borel

/-! ### The principal series -/

variable (F : Type) [Field F]

/-- **The one-dimensional representation `α ⊗ β` of the Borel subgroup**, bundled as an object of
`FDRep ℂ B`, which is the shape parabolic induction consumes. -/
noncomputable def GL2BorelChar (α β : Fˣ →* ℂˣ) : FDRep ℂ (GL2Borel F) :=
  FDRep.of (GL2Borel.linearRep (R := F) (k := ℂ) α β)

/-- The representation `α ⊗ β` of the Borel subgroup is one-dimensional. -/
@[simp]
theorem finrank_GL2BorelChar (α β : Fˣ →* ℂˣ) :
    Module.finrank ℂ (GL2BorelChar F α β) = 1 :=
  Module.finrank_self ℂ

/-- The character of `TauCeti.GL2BorelChar` is `TauCeti.GL2Borel.linearChar`. -/
@[simp]
theorem character_GL2BorelChar (α β : Fˣ →* ℂˣ) (g : GL2Borel F) :
    (GL2BorelChar F α β).character g = (GL2Borel.linearChar α β g : ℂ) :=
  GL2Borel.character_linearRep (R := F) (k := ℂ) α β g

variable [Fintype F]

/-- **The principal series** `Ind_B^{GL₂}(α ⊗ β)`: the representation of `GL₂(𝔽_q)` induced from
the one-dimensional character `α ⊗ β` of the Borel subgroup. This is parabolic induction in rank
one. -/
noncomputable def GL2PrincipalSeries (α β : Fˣ →* ℂˣ) : FDRep ℂ (GL (Fin 2) F) :=
  indFDRep (GL2BorelChar F α β)

/-- **The principal series has dimension `q + 1`**, the index of the Borel subgroup, because it is
induced from a one-dimensional representation. -/
@[simp]
theorem finrank_GL2PrincipalSeries (α β : Fˣ →* ℂˣ) :
    Module.finrank ℂ (GL2PrincipalSeries F α β) = Fintype.card F + 1 := by
  rw [GL2PrincipalSeries, finrank_indFDRep, finrank_GL2BorelChar, mul_one, GL2Borel.index_eq]

/-- **The principal series has dimension `q + 1`**, read off the character at the identity. -/
theorem character_one_GL2PrincipalSeries (α β : Fˣ →* ℂˣ) :
    (GL2PrincipalSeries F α β).character 1 = (Fintype.card F : ℂ) + 1 := by
  rw [FDRep.char_one, finrank_GL2PrincipalSeries]
  push_cast
  ring

end TauCeti
