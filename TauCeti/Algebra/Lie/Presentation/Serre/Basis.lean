/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic
public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.Presentation.Serre

/-!
# The Serre system carried by a Lie algebra basis

A `LieAlgebra.Basis ι H` carries four of the six families of Serre relations as fields: the `hᵢ`
commute, `⁅eᵢ, fᵢ⁆ = hᵢ`, `⁅eᵢ, fⱼ⁆ = 0` for `i ≠ j`, and the two eigenvector equations for
`ad hᵢ`. This file proves the remaining two, the higher relations

```text
(ad eᵢ) ^ (1 - Aⱼᵢ) eⱼ = 0    and    (ad fᵢ) ^ (1 - Aⱼᵢ) fⱼ = 0,
```

so that the generators of a basis form a `TauCeti.IsSerreSystem` and the Lie algebra is a quotient
of the Serre algebra of the transposed matrix of the basis.

The coefficient ring is a characteristic-zero integral domain, and the Lie algebra is torsion-free
and Noetherian as a module over it, which is what makes the `sl₂`-strings finite. In particular no
Killing form, splitting Cartan subalgebra or triangularizability is assumed, and the argument never
mentions a root system.

The proof is `sl₂` theory rather than root strings. For `i ≠ j` the vector `eⱼ` is primitive for
the triple `(-hᵢ, fᵢ, eᵢ)` obtained from `LieAlgebra.Basis.sl2` by exchanging the raising and
lowering generators, because `⁅fᵢ, eⱼ⁆ = 0`, and its eigenvalue for `-hᵢ` is `-Aⱼᵢ`. A primitive
vector in a Noetherian module has a natural number as eigenvalue, so `-Aⱼᵢ` is one, and one further
step along its string is zero. The `f` family follows by applying the result for `e` to the
symmetric basis, which exchanges `e` and `f` and negates `h`.

Reading `-Aⱼᵢ` off `LieAlgebra.IsSl2Triple.HasPrimitiveVectorWith.exists_nat` rather than assuming
it is why no sign condition on the off-diagonal entries of `LieAlgebra.Basis.A` is needed: that
`-Aⱼᵢ` is a nonnegative integer is a consequence of the relations.

## Main results

* `TauCeti.ad_pow_lie_lieBasis_e_e` and `TauCeti.ad_pow_lie_lieBasis_f_f`: the two higher Serre
  relations for the generators of a Lie algebra basis.
* `TauCeti.isSerreSystem_lieBasis`: those generators form a Serre system for the transposed matrix
  of the basis.
* `TauCeti.serreLift_lieBasis_surjective`: the homomorphism induced by those generators is
  surjective.

## References

* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI
* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §18.1

## Roadmap

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the split reductive group scheme
over `ℤ` to be constructed "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping
algebra". `RootPairing.GeckConstruction.basis` produces a `LieAlgebra.Basis` for the explicit
matrix Lie algebra of a root system over any field of characteristic zero, whereas that algebra is
known to have a nondegenerate Killing form only over an algebraically closed one. So a form of
these relations that does not assume `LieAlgebra.IsKilling` is what a pinned construction over `ℚ`
can use, and `TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/SerrePresentation.lean` is
the consumer. `TauCeti/Algebra/Lie/Presentation/Serre/Killing.lean` keeps the root-string form of
the same relations, which applies to a split semisimple Lie algebra presented by a base rather
than by a basis.
-/

public section

namespace TauCeti

open LieAlgebra LieModule
open scoped Matrix

variable {ι K L : Type*} [Finite ι] [CommRing K] [IsDomain K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.IsTorsionFree K L] [IsNoetherian K L]
  {H : LieSubalgebra K L} (b : LieAlgebra.Basis ι H)

/-! ## Primitive vectors among the generators -/

omit [IsDomain K] [CharZero K] [Module.IsTorsionFree K L] [IsNoetherian K L] in
/-- For `i ≠ j` the raising generator `eⱼ` is primitive of eigenvalue `-Aⱼᵢ` for the triple
`(-hᵢ, fᵢ, eᵢ)` obtained from `LieAlgebra.Basis.sl2` by exchanging the raising and lowering
generators and negating `hᵢ`. -/
private theorem hasPrimitiveVectorWith_lieBasis_e {i j : ι} (hij : i ≠ j) :
    (b.sl2 i).symm.HasPrimitiveVectorWith (M := L) (b.e j) ((-b.A j i : ℤ) : K) where
  ne_zero := (b.sl2 j).e_ne_zero
  lie_h := by
    rw [neg_lie, b.lie_h_e j i, Int.cast_smul_eq_zsmul, neg_smul]
  lie_e := by
    rw [← lie_skew, b.lie_e_f_ne j i hij.symm, neg_zero]

/-! ## The higher Serre relations -/

omit [Finite ι] in
/-- The string below a primitive vector of integer eigenvalue `n` stops after `n.toNat` steps.
This is the common core of the two higher Serre relations: `y` is the lowering generator of the
triple being iterated and `m` the primitive vector. -/
private theorem ad_pow_succ_toNat_eq_zero {x y z m : L} {ht : IsSl2Triple z x y} {n : ℤ}
    (P : ht.HasPrimitiveVectorWith (M := L) m ((n : ℤ) : K)) :
    ((ad K L y) ^ (n.toNat + 1)) m = 0 := by
  obtain ⟨k, hk⟩ := P.exists_nat
  have hnk : n = (k : ℤ) := by exact_mod_cast hk
  have htn : n.toNat = k := by omega
  rw [show ad K L y = toEnd K L L y from rfl, htn]
  exact P.pow_toEnd_f_eq_zero_of_eq_nat hk

/-- **The higher Serre relation on the raising generators of a Lie algebra basis.** -/
theorem ad_pow_lie_lieBasis_e_e (i j : ι) :
    ((ad K L (b.e i)) ^ (-b.Aᵀ i j).toNat) ⁅b.e i, b.e j⁆ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have h0 := ad_pow_succ_toNat_eq_zero (K := K) (hasPrimitiveVectorWith_lieBasis_e b hij)
    rw [pow_succ, Module.End.mul_apply, ad_apply] at h0
    rw [Matrix.transpose_apply]
    exact h0

/-- **The higher Serre relation on the lowering generators of a Lie algebra basis.** -/
theorem ad_pow_lie_lieBasis_f_f (i j : ι) :
    ((ad K L (b.f i)) ^ (-b.Aᵀ i j).toNat) ⁅b.f i, b.f j⁆ = 0 := by
  simpa using ad_pow_lie_lieBasis_e_e b.symm i j

/-! ## The Serre system and the presentation -/

/-- **The generators of a Lie algebra basis form a Serre system.** The relevant Cartan matrix is
the transpose of `LieAlgebra.Basis.A`, because `TauCeti.IsSerreSystem` follows Serre's convention
`⁅Hᵢ, Eⱼ⁆ = CMᵢⱼ Eⱼ` while `LieAlgebra.Basis.lie_h_e` reads `⁅hⱼ, eᵢ⁆ = Aᵢⱼ eᵢ`. -/
theorem isSerreSystem_lieBasis : IsSerreSystem K b.Aᵀ b.h b.e b.f where
  lie_H_H := b.lie_h_h
  lie_E_F_self i := (b.sl2 i).lie_e_f
  lie_E_F_of_ne _ _ hij := b.lie_e_f_ne _ _ hij
  lie_H_E i j := by rw [Matrix.transpose_apply]; exact b.lie_h_e j i
  lie_H_F i j := by rw [Matrix.transpose_apply, ← neg_smul]; exact b.lie_h_f j i
  ad_pow_lie_E_E := ad_pow_lie_lieBasis_e_e b
  ad_pow_lie_F_F := ad_pow_lie_lieBasis_f_f b

open scoped Classical in
/-- **The homomorphism induced by the generators of a Lie algebra basis is surjective.** -/
theorem serreLift_lieBasis_surjective :
    Function.Surjective (serreLift (isSerreSystem_lieBasis b)) :=
  serreLift_surjective _ b.span_ef

end TauCeti
