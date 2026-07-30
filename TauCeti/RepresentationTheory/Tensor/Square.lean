/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.TensorSquare
public import TauCeti.LinearAlgebra.ExteriorPower
public import TauCeti.RepresentationTheory.ExteriorPower
public import TauCeti.RepresentationTheory.SymmetricPower
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# Tensor-square decompositions of representations

When `2` is invertible, the tensor square of a representation splits into its symmetric and
exterior squares. This file lifts the natural linear decomposition to representations. It also
proves the corresponding trace identity over every field, including characteristic two where the
decomposition does not split.

## Main definitions

* `Representation.tensorSquareEquivSymmetricExterior` is the natural representation equivalence.
* `Representation.char_tensorSquare` is the tensor-square character identity.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “The first decomposition”.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6.
* Mathlib's exterior-power universal-property, pairing, and basis APIs, by Sophie Morel,
  Joël Riou, and Daniel Morrison.
-/

public section

open scoped TensorProduct

universe v w

variable {R : Type} {G : Type v} {M : Type w}

namespace TauCeti.TensorSquare

private theorem toTensorPower_ιMulti_two {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (f : Fin 2 → M) :
    exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 f) =
      PiTensorProduct.tprod R f -
        PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i)) := by
  classical
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_fin_two_eq_one_or_swap e
  rw [exteriorPower.toTensorPower_apply_ιMulti, hperm,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [sub_eq_add_neg]

private theorem mk_comp_toTensorPower {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] :
    (SymmetricPower.mk R (Fin 2) M).comp
      (exteriorPower.toTensorPower R M 2) = 0 := by
  classical
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    toTensorPower_ιMulti_two]
  change
    (⨂ₛ[R] i, f i) -
      (⨂ₛ[R] i, f (Equiv.swap 0 1 i)) = 0
  rw [SymmetricPower.tprod_equiv]
  simp

private noncomputable def symToAlternatingQuotient {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] :
    Sym[R]^2 M →ₗ[R]
      (⨂[R]^2 M) ⧸ LinearMap.range (exteriorPower.toTensorPower R M 2) where
  toFun :=
    (addConGen (SymmetricPower.Rel R (Fin 2) M)).lift
      (LinearMap.toAddMonoidHom
        (Submodule.mkQ (LinearMap.range (exteriorPower.toTensorPower R M 2))))
      (by
        apply AddCon.addConGen_le.2
        intro x y h
        cases h with
        | perm e f =>
          apply (AddCon.ker_rel _).2
          apply (Submodule.Quotient.eq _).2
          rcases perm_fin_two_eq_one_or_swap e with rfl | rfl
          · simp
          · exact ⟨exteriorPower.ιMulti R 2 f, toTensorPower_ιMulti_two f⟩)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x ↦ by
    exact congrArg
      (Submodule.Quotient.mk
        (p := LinearMap.range (exteriorPower.toTensorPower R M 2)))
      ((LinearMap.id.map_smul r x))

private theorem symToAlternatingQuotient_mk {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] (x : ⨂[R]^2 M) :
    symToAlternatingQuotient (R := R) (M := M)
        (SymmetricPower.mk R (Fin 2) M x) =
      Submodule.Quotient.mk x := by
  simp [symToAlternatingQuotient, SymmetricPower.mk]

-- These maps form the characteristic-free exact sequence `⋀²M → M⊗M → Sym²M`.
private theorem range_toTensorPower_eq_ker_mk {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] :
    LinearMap.range (exteriorPower.toTensorPower R M 2) =
      LinearMap.ker (SymmetricPower.mk R (Fin 2) M) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun (mk_comp_toTensorPower (R := R) (M := M)) x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (exteriorPower.toTensorPower R M 2))).mp
    rw [← symToAlternatingQuotient_mk x, hx, map_zero]

private theorem toTensorPower_injective {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M] :
    Function.Injective (exteriorPower.toTensorPower R M 2) := by
  classical
  let b := Module.finBasis R M
  intro x y h
  apply (b.exteriorPower 2).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  change
    exteriorPower.pairingDual R M 2
        (exteriorPower.ιMulti_family R 2 b.coord s) x =
      exteriorPower.pairingDual R M 2
        (exteriorPower.ιMulti_family R 2 b.coord s) y
  simp only [exteriorPower.ιMulti_family, exteriorPower.pairingDual,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    exteriorPower.alternatingMapToDual]
  change
    TensorPower.multilinearMapToDual R M 2
        (b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm s)
        (exteriorPower.toTensorPower R M 2 x) =
      TensorPower.multilinearMapToDual R M 2
        (b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm s)
        (exteriorPower.toTensorPower R M 2 y)
  rw [h]

-- Split an exact sequence as vector spaces. In that basis the middle action is block triangular,
-- so its trace is the sum of the traces on the subspace and quotient.
private theorem trace_eq_add_of_exact
    {K A B C : Type*} [Field K]
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    (i : A →ₗ[K] B) (q : B →ₗ[K] C)
    (fA : A →ₗ[K] A) (fB : B →ₗ[K] B) (fC : C →ₗ[K] C)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : LinearMap.range i = LinearMap.ker q)
    (hfi : fB.comp i = i.comp fA) (hfq : q.comp fB = fC.comp q) :
    LinearMap.trace K B fB =
      LinearMap.trace K A fA + LinearMap.trace K C fC := by
  classical
  obtain ⟨s, hs⟩ :=
    q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : q.comp s = LinearMap.id := hs
  have hqi : q.comp i = 0 := by
    apply LinearMap.ext
    intro a
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    apply LinearMap.mem_ker.mp
    rw [← hexact]
    exact ⟨a, rfl⟩
  have hqi_apply (a : A) : q (i a) = 0 := by
    exact LinearMap.congr_fun hqi a
  have hqs_apply (c : C) : q (s c) = c := by
    exact LinearMap.congr_fun hqs c
  let eMap : (A × C) →ₗ[K] B := i.coprod s
  have eMap_injective : Function.Injective eMap := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    have hc : c = c' := by
      have := congrArg q h
      simp only [eMap, LinearMap.coprod_apply, map_add] at this
      rw [hqi_apply, hqi_apply, hqs_apply, hqs_apply, zero_add, zero_add] at this
      exact this
    subst c'
    apply Prod.ext
    · apply hi
      simpa only [eMap, LinearMap.coprod_apply, add_left_inj] using h
    · rfl
  have eMap_surjective : Function.Surjective eMap := by
    intro b
    have hb : b - s (q b) ∈ LinearMap.range i := by
      rw [hexact, LinearMap.mem_ker]
      rw [map_sub, hqs_apply, sub_self]
    obtain ⟨a, ha⟩ := hb
    exact ⟨(a, q b), by
      simp only [eMap, LinearMap.coprod_apply]
      rw [ha]
      abel⟩
  let e : (A × C) ≃ₗ[K] B :=
    LinearEquiv.ofBijective eMap ⟨eMap_injective, eMap_surjective⟩
  let F : (A × C) →ₗ[K] (A × C) := e.symm.conj fB
  have he_apply (a : A) (c : C) : e (a, c) = i a + s c := by
    rfl
  have hq_e (a : A) (c : C) : q (e (a, c)) = c := by
    rw [he_apply, map_add, hqi_apply, hqs_apply, zero_add]
  have hsnd_e_symm (b : B) :
      (LinearMap.snd K A C) (e.symm b) = q b := by
    rw [← e.apply_symm_apply b]
    obtain ⟨a, c⟩ := e.symm b
    simpa only [e.symm_apply_apply, LinearMap.snd_apply] using (hq_e a c).symm
  have hF_inl : F.comp (LinearMap.inl K A C) =
      (LinearMap.inl K A C).comp fA := by
    apply LinearMap.ext
    intro a
    apply e.injective
    simp only [LinearMap.comp_apply, F, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    rw [he_apply, he_apply]
    simp only [LinearMap.inl_apply, map_zero, add_zero]
    exact LinearMap.congr_fun hfi a
  have hsndF : (LinearMap.snd K A C).comp F =
      fC.comp (LinearMap.snd K A C) := by
    apply LinearMap.ext
    rintro ⟨a, c⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change (LinearMap.snd K A C) (e.symm (fB (e (a, c)))) = fC c
    rw [hsnd_e_symm, ← LinearMap.comp_apply, hfq, LinearMap.comp_apply, hq_e]
  let u : C →ₗ[K] A :=
    (LinearMap.fst K A C).comp (F.comp (LinearMap.inr K A C))
  have hF :
      F = LinearMap.prodMap fA fC +
        (LinearMap.inl K A C).comp (u.comp (LinearMap.snd K A C)) := by
    apply LinearMap.ext
    rintro ⟨a, c⟩
    apply Prod.ext
    · change (F (a, c)).1 = fA a + u c
      have hsplit : (a, c) = (LinearMap.inl K A C) a +
          (LinearMap.inr K A C) c := by
        ext <;> simp
      rw [hsplit, map_add]
      rw [show F ((LinearMap.inl K A C) a) =
          (LinearMap.inl K A C) (fA a) by
            exact LinearMap.congr_fun hF_inl a]
      rfl
    · simpa only [LinearMap.add_apply, LinearMap.prodMap_apply,
        LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply,
        Prod.snd_add, add_zero] using
          LinearMap.congr_fun hsndF (a, c)
  rw [← LinearMap.trace_conj' fB e.symm]
  change LinearMap.trace K (A × C) F = _
  rw [hF, map_add, LinearMap.trace_prodMap']
  have hoff :
      LinearMap.trace K (A × C)
          ((LinearMap.inl K A C).comp (u.comp (LinearMap.snd K A C))) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hz :
        (u.comp (LinearMap.snd K A C)).comp (LinearMap.inl K A C) = 0 := by
      apply LinearMap.ext
      intro a
      simp
    rw [hz, map_zero]
  rw [hoff, add_zero]

end TauCeti.TensorSquare

namespace Representation

section CommRing

variable [CommRing R] [Invertible (2 : R)] [Monoid G]
variable [AddCommGroup M] [Module R M]

/-- The tensor square of a representation is equivalent to the product of its symmetric and
exterior squares when `2` is invertible. -/
noncomputable def tensorSquareEquivSymmetricExterior (ρ : Representation R G M) :
    (ρ.tensorPower 2).Equiv ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) :=
  .mk (TauCeti.tensorSquareEquivSymmetricExterior R M) fun g ↦ by
    apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
    rintro _ ⟨f, rfl⟩
    simp only [LinearMap.comp_apply, tensorPower_apply, PiTensorProduct.map_tprod]
    -- Unfold the representation action and product wrappers to compare their pure-tensor values.
    change TauCeti.tensorSquareEquivSymmetricExterior R M
        (PiTensorProduct.tprod R fun i ↦ ρ g (f i)) =
      ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) g
        (TauCeti.tensorSquareEquivSymmetricExterior R M (PiTensorProduct.tprod R f))
    have h₁ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M
      (fun i ↦ ρ g (f i))
    have h₂ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M f
    rw [h₁, h₂]
    simp only [prod_apply_apply, symmetricPower_apply, SymmetricPower.map_tprod,
      exteriorPower_apply, exteriorPower.map_apply_ιMulti, Prod.mk.injEq, true_and]
    apply congrArg (exteriorPower.ιMulti R 2)
    funext i
    rfl

/-- The underlying linear equivalence of the tensor-square decomposition is the natural
linear-algebraic decomposition. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_toLinearEquiv (ρ : Representation R G M) :
    ρ.tensorSquareEquivSymmetricExterior.toLinearEquiv =
      TauCeti.tensorSquareEquivSymmetricExterior R M :=
  (rfl)

end CommRing

section Field

variable [Field R] [Monoid G]
variable [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- Over any field, the tensor-square character is the sum of the symmetric-square and
exterior-square characters. -/
theorem char_tensorSquare (ρ : Representation R G M) (g : G) :
    (ρ.character g) ^ 2 =
      (ρ.symmetricPower 2).character g + (ρ.exteriorPower 2).character g := by
  classical
  rw [← char_tensorPower ρ 2 g]
  simp only [Representation.character, tensorPower_apply, symmetricPower_apply,
    exteriorPower_apply]
  -- The alternating inclusion and symmetric quotient intertwine the three induced actions.
  have hfi :
      (PiTensorProduct.map fun _ : Fin 2 ↦ ρ g).comp
          (exteriorPower.toTensorPower R M 2) =
        (exteriorPower.toTensorPower R M 2).comp
          (exteriorPower.map 2 (ρ g)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
    rw [TauCeti.TensorSquare.toTensorPower_ιMulti_two,
      exteriorPower.map_apply_ιMulti,
      TauCeti.TensorSquare.toTensorPower_ιMulti_two]
    simp only [map_sub, PiTensorProduct.map_tprod, Function.comp_apply]
    congr 1
  have hfq :
      (SymmetricPower.mk R (Fin 2) M).comp
          (PiTensorProduct.map fun _ : Fin 2 ↦ ρ g) =
        (SymmetricPower.map (ρ g)).comp
          (SymmetricPower.mk R (Fin 2) M) := by
    apply LinearMap.ext
    intro x
    simp
  -- Trace is additive along the exact sequence `⋀²M → M⊗M → Sym²M`.
  have h := TauCeti.TensorSquare.trace_eq_add_of_exact
    (exteriorPower.toTensorPower R M 2)
    (SymmetricPower.mk R (Fin 2) M)
    (exteriorPower.map 2 (ρ g))
    (PiTensorProduct.map fun _ : Fin 2 ↦ ρ g)
    (SymmetricPower.map (ρ g))
    TauCeti.TensorSquare.toTensorPower_injective
    (LinearMap.range_eq_top.mp (SymmetricPower.range_mk R (Fin 2) M))
    TauCeti.TensorSquare.range_toTensorPower_eq_ker_mk hfi hfq
  simpa only [add_comm] using h

end Field

end Representation
