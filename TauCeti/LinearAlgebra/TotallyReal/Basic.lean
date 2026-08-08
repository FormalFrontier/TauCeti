/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Projection

/-!
# Totally real linear subspaces

This file supplies the linear-algebra notion of a (maximal) totally real subspace with respect to
a linear endomorphism `J` over an arbitrary scalar semiring.  This is the algebraic pointwise
model for totally real boundary conditions in the analytic Heegaard Floer roadmap: a boundary
tangent space `L` is totally real when it is disjoint from its `J`-image, and maximal totally
real when the two are moreover complementary.  The terminology is borrowed from the usual
real-linear situation, but the complement API itself is purely module-theoretic.

No integrability, topology, or symplectic form is bundled here.
-/

public section

namespace TauCeti

open LinearMap

variable {R E F : Type*}

section Basic

variable [Semiring R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]

/-- A submodule is totally real with respect to `J` if it is disjoint from its `J`-image. -/
def IsTotallyReal (J : E →ₗ[R] E) (L : Submodule R E) : Prop :=
  Disjoint L (L.map J)

/-- The totally real predicate unfolds to disjointness of `L` and its `J`-image. -/
@[simp, grind =]
theorem isTotallyReal_iff (J : E →ₗ[R] E) (L : Submodule R E) :
    IsTotallyReal J L ↔ Disjoint L (L.map J) :=
  Iff.rfl

/-- A submodule is maximal totally real with respect to `J` if it is complementary to its
`J`-image. -/
def IsMaximalTotallyReal (J : E →ₗ[R] E) (L : Submodule R E) : Prop :=
  IsCompl L (L.map J)

/-- The maximal totally real predicate unfolds to complementarity of `L` and its `J`-image. -/
@[simp, grind =]
theorem isMaximalTotallyReal_iff (J : E →ₗ[R] E) (L : Submodule R E) :
    IsMaximalTotallyReal J L ↔ IsCompl L (L.map J) :=
  Iff.rfl

namespace IsTotallyReal

variable {J : E →ₗ[R] E} {L : Submodule R E}

/-- A totally real submodule is disjoint from its `J`-image. -/
theorem disjoint (hL : IsTotallyReal J L) : Disjoint L (L.map J) :=
  hL

/-- The intersection of a totally real submodule with its `J`-image is bottom. -/
theorem inf_eq_bot (hL : IsTotallyReal J L) : L ⊓ L.map J = ⊥ :=
  hL.disjoint.eq_bot

/-- The zero submodule is totally real for any `J`. -/
theorem bot (J : E →ₗ[R] E) : IsTotallyReal J (⊥ : Submodule R E) :=
  disjoint_bot_left

/-- A submodule of a totally real submodule is totally real. -/
theorem mono (hL : IsTotallyReal J L) {L' : Submodule R E} (h : L' ≤ L) :
    IsTotallyReal J L' :=
  hL.disjoint.mono h (Submodule.map_mono h)

/-- Products of totally real submodules are totally real for `LinearMap.prodMap`. -/
theorem prod {K : F →ₗ[R] F} {M : Submodule R F} (hL : IsTotallyReal J L) (hM : IsTotallyReal K M) :
    IsTotallyReal (LinearMap.prodMap J K) (L.prod M) := by
  rw [isTotallyReal_iff, LinearMap.prodMap_map_prod, disjoint_iff, Submodule.prod_inf_prod,
    hL.inf_eq_bot, hM.inf_eq_bot, Submodule.prod_bot]

end IsTotallyReal

namespace IsCompl

variable {L₁ L₂ : Submodule R E} {M₁ M₂ : Submodule R F}

/-- Products of complementary submodules are complementary.

This is a local helper for the maximal totally real product and doubled-module lemmas below; it
is `private` because it is not part of the totally real subspace API surface. -/
private theorem prod (hL : IsCompl L₁ L₂) (hM : IsCompl M₁ M₂) :
    IsCompl (L₁.prod M₁) (L₂.prod M₂) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, hL.inf_eq_bot, hM.inf_eq_bot, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, hL.sup_eq_top, hM.sup_eq_top, Submodule.prod_top]

end IsCompl

namespace IsMaximalTotallyReal

variable {J : E →ₗ[R] E} {K : F →ₗ[R] F} {L L' : Submodule R E} {M : Submodule R F}

/-- A maximal totally real submodule is complementary to its `J`-image. -/
theorem isCompl (hL : IsMaximalTotallyReal J L) : IsCompl L (L.map J) :=
  hL

/-- A maximal totally real submodule is disjoint from its `J`-image. -/
theorem disjoint (hL : IsMaximalTotallyReal J L) : Disjoint L (L.map J) :=
  hL.isCompl.disjoint

/-- A maximal totally real submodule is in particular totally real. -/
theorem isTotallyReal (hL : IsMaximalTotallyReal J L) : IsTotallyReal J L :=
  hL.disjoint

/-- The intersection of a maximal totally real submodule with its `J`-image is bottom. -/
theorem inf_eq_bot (hL : IsMaximalTotallyReal J L) : L ⊓ L.map J = ⊥ :=
  hL.isCompl.inf_eq_bot

/-- A maximal totally real submodule spans codisjointly with its `J`-image. -/
theorem codisjoint (hL : IsMaximalTotallyReal J L) : Codisjoint L (L.map J) :=
  hL.isCompl.codisjoint

/-- A maximal totally real submodule and its `J`-image span the whole module. -/
theorem sup_eq_top (hL : IsMaximalTotallyReal J L) : L ⊔ L.map J = ⊤ :=
  hL.isCompl.sup_eq_top

/-- Products of maximal totally real submodules are maximal totally real for `LinearMap.prodMap`. -/
theorem prod (hL : IsMaximalTotallyReal J L) (hM : IsMaximalTotallyReal K M) :
    IsMaximalTotallyReal (LinearMap.prodMap J K) (L.prod M) := by
  rw [isMaximalTotallyReal_iff]
  rw [LinearMap.prodMap_map_prod]
  exact TauCeti.IsCompl.prod hL.isCompl hM.isCompl

end IsMaximalTotallyReal

end Basic

section AddCommGroup

variable [Semiring R]
variable [AddCommGroup E] [Module R E]

namespace Submodule

/-- The image of the first coordinate factor under the standard doubled-module complex
structure is the second coordinate factor. -/
@[simp]
theorem map_prod_top_bot_skewSwap : ((⊤ : Submodule R E).prod (⊥ : Submodule R E)).map
        (LinearEquiv.skewSwap R E E).toLinearMap =
      (⊥ : Submodule R E).prod (⊤ : Submodule R E) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by simpa using hy.2, trivial⟩
  · intro hx
    have hx1 : x.1 = 0 := by
      simpa using hx.1
    refine ⟨(x.2, 0), by simp, ?_⟩
    ext <;> simp [hx1]

/-- The image of the second coordinate factor under the standard doubled-module complex
structure is the first coordinate factor. -/
@[simp]
theorem map_prod_bot_top_skewSwap : ((⊥ : Submodule R E).prod (⊤ : Submodule R E)).map
        (LinearEquiv.skewSwap R E E).toLinearMap =
      (⊤ : Submodule R E).prod (⊥ : Submodule R E) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨trivial, by simpa using hy.1⟩
  · intro hx
    have hx2 : x.2 = 0 := by
      simpa using hx.2
    refine ⟨(0, -x.1), by simp, ?_⟩
    ext <;> simp [hx2]

/-- The first factor in `E × E` is maximal totally real for the standard doubled-module complex
structure. -/
theorem isMaximalTotallyReal_prod_top_bot_skewSwap :
    IsMaximalTotallyReal (LinearEquiv.skewSwap R E E).toLinearMap
      ((⊤ : Submodule R E).prod (⊥ : Submodule R E)) := by
  rw [isMaximalTotallyReal_iff]
  rw [map_prod_top_bot_skewSwap]
  exact TauCeti.IsCompl.prod isCompl_top_bot isCompl_bot_top

/-- The second factor in `E × E` is maximal totally real for the standard doubled-module complex
structure. -/
theorem isMaximalTotallyReal_prod_bot_top_skewSwap :
    IsMaximalTotallyReal (LinearEquiv.skewSwap R E E).toLinearMap
      ((⊥ : Submodule R E).prod (⊤ : Submodule R E)) := by
  rw [isMaximalTotallyReal_iff]
  rw [map_prod_bot_top_skewSwap]
  exact TauCeti.IsCompl.prod isCompl_bot_top isCompl_top_bot

end Submodule

end AddCommGroup

section Ring

variable [Ring R]
variable [AddCommGroup E] [Module R E]

variable {J : E →ₗ[R] E} {L : Submodule R E}

/-- If `J² = -1`, applying `J` twice to a submodule returns the original submodule.

This is a local helper for the image lemmas below; it is `private` because it is not part of the
totally real subspace API surface. -/
private theorem map_map_eq (hJ : J.comp J = -LinearMap.id) : (L.map J).map J = L := by
  rw [← Submodule.map_comp J J L, hJ, Submodule.map_neg, Submodule.map_id]

namespace IsTotallyReal

/-- If `J² = -1`, the image `J(L)` is totally real whenever `L` is totally real. -/
theorem image (hL : IsTotallyReal J L) (hJ : J.comp J = -LinearMap.id) :
    IsTotallyReal J (L.map J) := by
  rw [isTotallyReal_iff, map_map_eq hJ]
  exact hL.disjoint.symm

/-- Under `J² = -1`, `L` is totally real if and only if its image `J(L)` is totally real. -/
theorem image_iff (hJ : J.comp J = -LinearMap.id) :
    IsTotallyReal J (L.map J) ↔ IsTotallyReal J L := by
  constructor
  · intro h
    have h' := h.image hJ
    rwa [map_map_eq hJ] at h'
  · intro h
    exact h.image hJ

end IsTotallyReal

namespace IsMaximalTotallyReal

/-- If `J² = -1`, the image `J(L)` is maximal totally real whenever `L` is maximal totally
real. -/
theorem image (hL : IsMaximalTotallyReal J L) (hJ : J.comp J = -LinearMap.id) :
    IsMaximalTotallyReal J (L.map J) := by
  rw [isMaximalTotallyReal_iff, map_map_eq hJ]
  exact hL.isCompl.symm

/-- Under `J² = -1`, `L` is maximal totally real if and only if its image `J(L)` is maximal
totally real. -/
theorem image_iff (hJ : J.comp J = -LinearMap.id) :
    IsMaximalTotallyReal J (L.map J) ↔ IsMaximalTotallyReal J L := by
  constructor
  · intro h
    have h' := h.image hJ
    rwa [map_map_eq hJ] at h'
  · intro h
    exact h.image hJ

end IsMaximalTotallyReal

namespace IsMaximalTotallyReal

variable {J : E →ₗ[R] E} {L : Submodule R E}

/-- Every vector decomposes uniquely as an element of `L` plus an element of `J(L)`. -/
theorem existsUnique_add (hL : IsMaximalTotallyReal J L) (x : E) :
    ∃! y : L × L.map J, (y.1 : E) + y.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod hL.isCompl x

end IsMaximalTotallyReal

end Ring

end TauCeti
