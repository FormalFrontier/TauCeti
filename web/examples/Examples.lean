import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Basic
import TauCeti.Analysis.PDE.Uniform.Ellipticity
import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
import TauCeti.Algebra.HopfAlgebra.Basic
import SubVerso.Examples
open SubVerso.Examples

%example deck_rigidity
open TauCeti in
/-- Universal covers — two deck transformations of a connected covering space that
agree at a single point of the total space are equal. -/
theorem deck_rigidity {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} [PreconnectedSpace E] (hp : IsCoveringMap p)
    (φ ψ : Deck p) {e : E} (h : φ.1 e = ψ.1 e) : φ = ψ :=
  Deck.eq_of_apply_eq hp φ ψ h
%end

%example ellipticity_coercive
open TauCeti.PDE Matrix in
/-- Partial differential equations — on a uniformly elliptic region the coefficient
matrix induces a coercive bilinear form, the hypothesis that powers Lax–Milgram. -/
theorem ellipticity_coercive {X n : Type*} [Fintype n] [DecidableEq n]
    {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  h.isCoercive_matrixBilinearForm hx
%end

%example effective_divisor
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.WeilDivisor in
/-- The Jacobian challenge — a nonzero effective Weil divisor has a point with
strictly positive coefficient. -/
theorem effective_divisor {X : Type*} {D : WeilDivisor X}
    (hD : IsEffective D) (hD0 : D ≠ 0) : ∃ x, 0 < D.coeff x :=
  hD.exists_pos_coeff_of_ne_zero hD0
%end

%example hopf_antipode
open HopfAlgebra in
/-- Reductive algebraic groups — a bialgebra homomorphism between Hopf algebras
commutes with the antipodes. -/
theorem hopf_antipode {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (φ : A →ₐc[R] B) :
    φ.toLinearMap.comp (antipode R (A := A)) = (antipode R (A := B)).comp φ.toLinearMap :=
  TauCeti.BialgHom.toLinearMap_comp_antipode φ
%end
