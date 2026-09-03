/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.RingTheory.Flat.Basic
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Testing geometric connectedness over algebraically closed fields

For a commutative Hopf algebra `H` over a field `k`, geometric connectedness may be tested only
after algebraically closed extensions of `k`. For an arbitrary extension `K / k`, its algebraic
closure `Ω` is again a `k`-algebra. The map

```text
H ⊗[k] K → H ⊗[k] Ω
```

is injective because `H` is flat over the field `k`. Connectedness of the target therefore
descends to the source by the idempotent characterization of connected affine spectra.

## Main declaration

* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed`:
  geometric connectedness is equivalent to connectedness after every algebraically closed field
  extension.
* `TauCeti.HopfAlgebra.rightTranslationAlgHom_eq_self_of_path`: a domain-valued path from the
  identity to a point makes that point's translation fix every idempotent.
* `TauCeti.HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self`:
  if every point translation fixes every idempotent, the spectrum is connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is the algebraically-closed-field reduction for Layer 3, "Identity component and component
group", of the ReductiveGroups roadmap. It is the first reduction toward expressing geometric
connectedness using a chosen algebraic closure of the ground field.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

universe u

/-- **Geometric connectedness of a commutative Hopf algebra can be tested after algebraically
closed field extensions.** -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
        ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] K)) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  constructor
  · intro h K _ _ _
    exact h K
  · intro h K _ _
    let Ω := AlgebraicClosure K
    let g : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
    let f : (H : Type u) ⊗[k] K →ₐ[k] (H : Type u) ⊗[k] Ω :=
      Algebra.TensorProduct.map (AlgHom.id k H) g
    have hg : Function.Injective g := RingHom.injective g.toRingHom
    have hf : Function.Injective f :=
      Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
    exact connectedSpace_primeSpectrum_of_injective f.toRingHom hf

namespace HopfAlgebra

/-- Two specializations of a domain-valued algebra homomorphism agree on an idempotent. -/
private theorem algHom_apply_eq_of_isIdempotentElem
    {K H A : Type u} [CommSemiring K] [Semiring H] [Algebra K H]
    [CommSemiring A] [Algebra K A] [IsDomain A]
    (e : H) (he : IsIdempotentElem e) (q : H →ₐ[K] A)
    (phi psi : A →ₐ[K] K) :
    phi (q e) = psi (q e) := by
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map q) with h | h <;> simp [h]

/-- If a point of a finite-type Hopf algebra is connected to the identity by a path valued in a
domain, its right translation fixes every idempotent. -/
theorem rightTranslationAlgHom_eq_self_of_path
    {K H D : Type u} [Field K] [CommRing H] [_root_.HopfAlgebra K H]
    [Algebra.FiniteType K H] [CommRing D] [Algebra K D] [IsDomain D]
    [IsAlgClosed K] (e : H) (he : IsIdempotentElem e)
    (g : WithConv (H →ₐ[K] K)) (x : WithConv (H →ₐ[K] D))
    (phi psi : D →ₐ[K] K)
    (hphi : AlgHom.mapValue (H := H) phi x = g)
    (hpsi : AlgHom.mapValue (H := H) psi x = 1) :
    rightTranslationAlgHom g e = e := by
  apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
    (k := K) (A := H) (K := K) (he.map _) he
  intro f
  let c : WithConv (H →ₐ[K] D) :=
    AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom K K D) (toConv f)
  have hc (theta : D →ₐ[K] K) :
      AlgHom.mapValue (H := H) theta c = toConv f := by
    have hcomp : theta.comp (IsScalarTower.toAlgHom K K D) = AlgHom.id K K :=
      AlgHom.ext fun z ↦ theta.commutes z
    dsimp only [c]
    rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, hcomp,
      AlgHom.mapValue_id, MonoidHom.id_apply]
  have hpath :
      (AlgHom.mapValue (H := H) phi (c * x)).ofConv e =
        (AlgHom.mapValue (H := H) psi (c * x)).ofConv e := by
    simpa only [AlgHom.mapValue_apply, AlgHom.comp_apply] using
      algHom_apply_eq_of_isIdempotentElem e he (c * x).ofConv phi psi
  rw [map_mul, hc phi, hphi] at hpath
  rw [map_mul, hc psi, hpsi, mul_one] at hpath
  calc
    f (rightTranslationAlgHom g e) = (toConv f * g).ofConv e :=
      ofConv_rightTranslationAlgHom (toConv f) g e
    _ = f e := hpath

/-- If right translation by every rational point fixes every idempotent of a finite-type Hopf
algebra over an algebraically closed field, its prime spectrum is connected. -/
theorem connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
    {K H : Type u} [Field K] [CommRing H] [_root_.HopfAlgebra K H]
    [Algebra.FiniteType K H] [IsAlgClosed K]
    (htranslate : ∀ (e : H), IsIdempotentElem e →
      ∀ g : WithConv (H →ₐ[K] K), rightTranslationAlgHom g e = e) :
    ConnectedSpace (PrimeSpectrum H) := by
  let _ : Nontrivial H := Bialgebra.nontrivial (A := H) K
  apply connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr
  intro e he
  have heval (g : WithConv (H →ₐ[K] K)) :
      g.ofConv e = Coalgebra.counit (R := K) e := by
    have h := DFunLike.congr_fun (counitAlgHom_comp_rightTranslationAlgHom g) e
    rw [AlgHom.comp_apply, htranslate e he g] at h
    exact h.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp
    (he.map (_root_.Bialgebra.counitAlgHom K H)) with hzero | hone
  · left
    rw [Bialgebra.counitAlgHom_apply] at hzero
    apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
      (k := K) (A := H) (K := K) he IsIdempotentElem.zero
    intro f
    simpa using (heval (toConv f)).trans hzero
  · right
    rw [Bialgebra.counitAlgHom_apply] at hone
    apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
      (k := K) (A := H) (K := K) he IsIdempotentElem.one
    intro f
    simpa using (heval (toConv f)).trans hone

end HopfAlgebra

end TauCeti
