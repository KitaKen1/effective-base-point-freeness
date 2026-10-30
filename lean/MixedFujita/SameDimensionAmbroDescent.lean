/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SameDimensionSteinBirational
public import MixedFujita.BirationalAmbroDescent

/-!
The original Ambro conclusion for an actual same-dimensional contraction.
The function-field isomorphism needed by birational descent is constructed
from normality, dimension equality and the Stein open-function property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The Ambro conclusion with t=1 for a same-dimensional normal projective
contraction. Birationality is a conclusion of the Stein property, not a premise. -/
theorem ambroContraction_same_dimension {K : Type u} [Field K] [CharZero K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdimX : topologicalKrullDim X = n) (hdimY : topologicalKrullDim Y = n)
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcovX : CodimOneChartCovered n K X)
    (hprojX : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hprojY : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (DX : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d DX)
    (hklt : LogPairIsKlt cX fX d DX)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    (H : CartierDivisor Y) (a : ℕ) (ψ : X.functionFieldˣ)
    (hDX : DX = a • cartierPullback f H + principalCartierDivisor X ψ) :
    ∃ (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (t : ℕ) (_ : 1 ≤ t)
      (DY : CartierDivisor Y) (φ : Y.functionFieldˣ),
      LogPairBoundaryEffective cY fY (t * d) DY ∧ LogPairIsKlt cY fY (t * d) DY ∧
      DY = (t * a) • H + principalCartierDivisor Y φ ∧ t = 1 := by
  have hf := stein_functionFieldAlgHom_bijective_of_same_dimension (K := K) f
    (hdimX.trans hdimY.symm) happ hnormX
  exact ambroContraction_birational hdimX hdimY hnormX hcovX hprojX hnormY hprojY
    cX fX d hd DX heff hklt f hf H a ψ hDX

end MixedFujita
