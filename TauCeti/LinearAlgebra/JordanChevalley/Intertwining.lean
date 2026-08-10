/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative

/-!
# Intertwining multiplicative Jordan decompositions

Over a perfect field, every linear map intertwining two automorphisms also intertwines their
canonical semisimple and unipotent factors.  No injectivity or surjectivity assumption on the
linear map is needed.

The proof applies the product automorphism to the graph of the intertwiner.  The graph is invariant
under the product, and the semisimple factor is a polynomial in that product, so the graph is also
invariant under the semisimple factor.  The product decomposition is componentwise, which gives
the desired equality for semisimple factors; the equality for unipotent factors then follows from
`u = s⁻¹g`.

This completes the linear-algebraic functoriality step in Layer 4 of the ReductiveGroups roadmap.
It is the input needed to transport Jordan decompositions through representations of affine
algebraic groups.

## Main declarations

* `TauCeti.GeneralLinearGroup.comp_semisimplePart_eq_of_comp_eq`: intertwiners commute with
  semisimple factors.
* `TauCeti.GeneralLinearGroup.comp_unipotentPart_eq_of_comp_eq`: intertwiners commute with
  unipotent factors.
* `TauCeti.GeneralLinearGroup.jordanDecomposition_prod`: Jordan decomposition is componentwise on
  product modules.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap Polynomial

namespace Module.End

universe u v

section Semiring

variable {K : Type u} {V W : Type v}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

@[simp]
private theorem prodMap_pow (f : Module.End K V) (g : Module.End K W) (n : ℕ) :
    (f.prodMap g) ^ n = (f ^ n).prodMap (g ^ n) := by
  induction n with
  | zero => exact LinearMap.prodMap_one.symm
  | succ n hn => rw [pow_succ, pow_succ, pow_succ, hn, LinearMap.prodMap_mul]

/-- The componentwise product of two nilpotent endomorphisms is nilpotent. -/
theorem _root_.IsNilpotent.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f.prodMap g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, ?_⟩
  rw [prodMap_pow, pow_add, hm, zero_mul, pow_add, hn, mul_zero,
    LinearMap.prodMap_zero]

end Semiring

section CommRing

variable {K : Type u} {V W : Type v}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private theorem aeval_prodMap (f : Module.End K V) (g : Module.End K W) (p : K[X]) :
    aeval (f.prodMap g) p = (aeval f p).prodMap (aeval g p) := by
  have h : aeval (f.prodMap g) =
      (LinearMap.prodMapAlgHom K V W).comp ((aeval f).prod (aeval g)) := by
    ext <;> simp
  exact DFunLike.congr_fun h p

/-- The componentwise product of two semisimple endomorphisms is semisimple. -/
theorem IsSemisimple.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    Module.End.IsSemisimple (f.prodMap g) := by
  rw [Module.End.IsSemisimple] at hf hg ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let _ : IsSemisimpleModule K[X] (Module.AEval' g) := hg
  let L := LinearMap.range
    (LinearMap.inl K[X] (Module.AEval' f) (Module.AEval' g))
  let R := LinearMap.range
    (LinearMap.inr K[X] (Module.AEval' f) (Module.AEval' g))
  let _ : IsSemisimpleModule K[X] L := IsSemisimpleModule.range _
  let _ : IsSemisimpleModule K[X] R := IsSemisimpleModule.range _
  have hprod : IsSemisimpleModule K[X] (Module.AEval' f × Module.AEval' g) := by
    have hsup : IsSemisimpleModule K[X] ↑(L ⊔ R) :=
      IsSemisimpleModule.sup inferInstance inferInstance
    let _ : IsSemisimpleModule K[X] ↑(L ⊔ R) := hsup
    apply IsSemisimpleModule.of_surjective (L ⊔ R).subtype
    intro x
    have htop : L ⊔ R = ⊤ := LinearMap.sup_range_inl_inr
    exact ⟨⟨x, htop.symm ▸ Submodule.mem_top⟩, rfl⟩
  let E : Module.AEval' (f.prodMap g) ≃ₗ[K[X]]
      Module.AEval' f × Module.AEval' g := {
    toFun x := (x.1, x.2)
    invFun x := (x.1, x.2)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' p x := by
      -- Unfold the two `AEval` scalar actions to compare their underlying endomorphisms.
      apply Prod.ext
      · change ((aeval (f.prodMap g) p) x).1 = (aeval f p) x.1
        rw [aeval_prodMap]
        rfl
      · change ((aeval (f.prodMap g) p) x).2 = (aeval g p) x.2
        rw [aeval_prodMap]
        rfl
  }
  let _ := hprod
  exact IsSemisimpleModule.congr E

end CommRing

end Module.End

namespace GeneralLinearGroup

universe u v

section Semiring

variable {K : Type u} {V W : Type v}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- The product of two linear automorphisms, acting componentwise on the product module. -/
def prod (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    GeneralLinearGroup K (V × W) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (g.toLinearEquiv.prodCongr h.toLinearEquiv)

/-- The endomorphism underlying a product automorphism is `LinearMap.prodMap`. -/
@[simp]
theorem coe_prod (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    (prod g h : Module.End K (V × W)) =
      (g : Module.End K V).prodMap (h : Module.End K W) :=
  (rfl)

/-- Componentwise products preserve multiplication. -/
@[simp]
theorem prod_mul (g₁ g₂ : GeneralLinearGroup K V) (h₁ h₂ : GeneralLinearGroup K W) :
    prod (g₁ * g₂) (h₁ * h₂) = prod g₁ h₁ * prod g₂ h₂ := by
  ext x <;> rfl

/-- The product of two identity automorphisms is the identity. -/
@[simp]
theorem prod_one : prod (1 : GeneralLinearGroup K V) (1 : GeneralLinearGroup K W) = 1 := by
  ext x <;> rfl

end Semiring

section CommRing

variable {K : Type u} {V W : Type v}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The product of two semisimple automorphisms is semisimple. -/
theorem IsSemisimple.prod {g : GeneralLinearGroup K V} {h : GeneralLinearGroup K W}
    (hg : IsSemisimple g) (hh : IsSemisimple h) : IsSemisimple (prod g h) := by
  rw [isSemisimple_def] at hg hh ⊢
  exact Module.End.IsSemisimple.prodMap hg hh

/-- The product of two unipotent automorphisms is unipotent. -/
theorem IsUnipotent.prod {g : GeneralLinearGroup K V} {h : GeneralLinearGroup K W}
    (hg : IsUnipotent g) (hh : IsUnipotent h) : IsUnipotent (prod g h) := by
  rw [isUnipotent_def] at hg hh ⊢
  have hp := hg.prodMap hh
  rw [show (GeneralLinearGroup.prod g h : Module.End K (V × W)) - 1 =
      ((g : Module.End K V) - 1).prodMap ((h : Module.End K W) - 1) by
    rw [coe_prod]
    ext x <;> simp]
  exact hp

end CommRing

section PerfectField

variable {K : Type u} {V W : Type v}
variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The semisimple factor of an automorphism is a polynomial in that automorphism. -/
theorem coe_semisimplePart_mem_adjoin (g : GeneralLinearGroup K V) :
    (semisimplePart g : Module.End K V) ∈
      Algebra.adjoin K {(g : Module.End K V)} := by
  obtain ⟨n, hn_mem, s, hs_mem, hn, hs, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := (g : Module.End K V))
  let s₀ : Module.End K V := semisimplePart g
  let u₀ : Module.End K V := unipotentPart g
  let n₀ : Module.End K V := s₀ * (u₀ - 1)
  have hsu : Commute s₀ (u₀ - 1) :=
    (commute_semisimplePart_unipotentPart g).units_val.sub_right (Commute.one_right _)
  have hn₀ : IsNilpotent n₀ :=
    hsu.isNilpotent_mul_left ((isUnipotent_def _).mp (isUnipotent_unipotentPart g))
  have hs₀ : Module.End.IsSemisimple s₀ :=
    (isSemisimple_def _).mp (isSemisimple_semisimplePart g)
  have hcomm₀ : Commute n₀ s₀ := (Commute.refl s₀).mul_left hsu.symm
  have hsum₀ : n₀ + s₀ = (g : Module.End K V) := by
    dsimp only [n₀]
    rw [mul_sub, mul_one, sub_add_cancel]
    exact congrArg ((↑·) : GeneralLinearGroup K V → Module.End K V)
      (semisimplePart_mul_unipotentPart g)
  have hcomm : Commute n s :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_mem
      (Algebra.commute_of_mem_adjoin_self hn_mem).symm
  have heq := Module.End.isNilpotent_isSemisimple_unique hn₀ hs₀ hn hs hcomm₀ hcomm
    (hsum₀.trans hsum)
  -- Restate the opaque factor through the local name used by the uniqueness calculation.
  change s₀ ∈ Algebra.adjoin K {(g : Module.End K V)}
  rw [heq.2]
  exact hs_mem

/-- The multiplicative Jordan decomposition of a product automorphism is the product of the
decompositions of its two factors. -/
theorem jordanDecomposition_prod (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    jordanDecomposition (prod g h) =
      (prod (semisimplePart g) (semisimplePart h),
        prod (unipotentPart g) (unipotentPart h)) := by
  symm
  apply (eq_jordanDecomposition_iff (prod g h) _ _).2
  refine ⟨(isSemisimple_semisimplePart g).prod (isSemisimple_semisimplePart h),
    (isUnipotent_unipotentPart g).prod (isUnipotent_unipotentPart h), ?_, ?_⟩
  · rw [commute_iff_eq, ← prod_mul, ← prod_mul]
    exact congrArg₂ prod (commute_semisimplePart_unipotentPart g).eq
      (commute_semisimplePart_unipotentPart h).eq
  · rw [← prod_mul, semisimplePart_mul_unipotentPart,
      semisimplePart_mul_unipotentPart]

@[simp]
theorem semisimplePart_prod (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    semisimplePart (prod g h) = prod (semisimplePart g) (semisimplePart h) := by
  rw [semisimplePart_def]
  exact congrArg Prod.fst (jordanDecomposition_prod g h)

@[simp]
theorem unipotentPart_prod (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    unipotentPart (prod g h) = prod (unipotentPart g) (unipotentPart h) := by
  rw [unipotentPart_def]
  exact congrArg Prod.snd (jordanDecomposition_prod g h)

/-- A linear map intertwining two automorphisms also intertwines their semisimple factors. -/
theorem comp_semisimplePart_eq_of_comp_eq
    (f : V →ₗ[K] W) (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W)
    (hfg : f.comp (g : Module.End K V) = (h : Module.End K W).comp f) :
    f.comp (semisimplePart g : Module.End K V) =
      (semisimplePart h : Module.End K W).comp f := by
  let gh : GeneralLinearGroup K (V × W) := prod g h
  have hgraph : f.graph ≤ f.graph.comap (gh : Module.End K (V × W)) := by
    intro x hx
    change (gh : Module.End K (V × W)) x ∈ f.graph
    rw [LinearMap.mem_graph_iff] at hx ⊢
    rw [coe_prod, LinearMap.prodMap_apply, hx]
    exact (LinearMap.congr_fun hfg x.1).symm
  have hs := coe_semisimplePart_mem_adjoin gh
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hs
  obtain ⟨p, hp⟩ := hs
  apply LinearMap.ext
  intro x
  have hx : (x, f x) ∈ f.graph := by simp
  have hpx : aeval (gh : Module.End K (V × W)) p (x, f x) ∈ f.graph :=
    aeval_apply_smul_mem_of_le_comap hx p _ hgraph
  have hp' : aeval (gh : Module.End K (V × W)) p =
      (semisimplePart gh : Module.End K (V × W)) := hp
  rw [hp'] at hpx
  change (semisimplePart (prod g h) : Module.End K (V × W)) (x, f x) ∈ f.graph at hpx
  rw [semisimplePart_prod, LinearMap.mem_graph_iff, coe_prod,
    LinearMap.prodMap_apply] at hpx
  exact hpx.symm

/-- A linear map intertwining two automorphisms also intertwines their unipotent factors. -/
theorem comp_unipotentPart_eq_of_comp_eq
    (f : V →ₗ[K] W) (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W)
    (hfg : f.comp (g : Module.End K V) = (h : Module.End K W).comp f) :
    f.comp (unipotentPart g : Module.End K V) =
      (unipotentPart h : Module.End K W).comp f := by
  have hs := comp_semisimplePart_eq_of_comp_eq f g h hfg
  have hs_inv :
      f.comp (↑((semisimplePart g)⁻¹) : Module.End K V) =
        (↑((semisimplePart h)⁻¹) : Module.End K W).comp f := by
    apply LinearMap.ext
    intro x
    calc
      f ((↑((semisimplePart g)⁻¹) : Module.End K V) x) =
          (↑((semisimplePart h)⁻¹) : Module.End K W)
            ((semisimplePart h : Module.End K W)
              (f ((↑((semisimplePart g)⁻¹) : Module.End K V) x))) := by
        exact ((semisimplePart h).toLinearEquiv.symm_apply_apply _).symm
      _ = (↑((semisimplePart h)⁻¹) : Module.End K W)
          (f ((semisimplePart g : Module.End K V)
            ((↑((semisimplePart g)⁻¹) : Module.End K V) x))) := by
        exact congrArg (↑((semisimplePart h)⁻¹) : Module.End K W)
          (LinearMap.congr_fun hs
            ((↑((semisimplePart g)⁻¹) : Module.End K V) x)).symm
      _ = (↑((semisimplePart h)⁻¹) : Module.End K W) (f x) := by
        have hxg : (semisimplePart g : Module.End K V)
            ((↑((semisimplePart g)⁻¹) : Module.End K V) x) = x :=
          LinearMap.congr_fun (semisimplePart g).val_inv x
        rw [hxg]
  have hug : unipotentPart g = (semisimplePart g)⁻¹ * g := by
    apply mul_left_cancel (a := semisimplePart g)
    simp
  have huh : unipotentPart h = (semisimplePart h)⁻¹ * h := by
    apply mul_left_cancel (a := semisimplePart h)
    simp
  rw [hug, huh]
  apply LinearMap.ext
  intro x
  change f ((↑((semisimplePart g)⁻¹) : Module.End K V) ((g : Module.End K V) x)) =
    (↑((semisimplePart h)⁻¹) : Module.End K W) ((h : Module.End K W) (f x))
  calc
    _ = (↑((semisimplePart h)⁻¹) : Module.End K W)
        (f ((g : Module.End K V) x)) :=
      LinearMap.congr_fun hs_inv ((g : Module.End K V) x)
    _ = _ := congrArg (↑((semisimplePart h)⁻¹) : Module.End K W)
      (LinearMap.congr_fun hfg x)

end PerfectField

end GeneralLinearGroup

end TauCeti
