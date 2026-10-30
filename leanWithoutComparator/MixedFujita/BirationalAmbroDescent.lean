/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalLogPairDescent
public import MixedFujita.KodairaLemmaStatementProof

/-!
The conclusion of the manuscript's Ambro input is proved when the actual map
is birational. Projectivity supplies properness, the target chart is chosen
internally, and the effective klt pair is constructed with t = 1. No all-open
function isomorphism or canonical bundle formula is an additional premise.
Positive-relative-dimensional Ambro descent remains a separate obligation.
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

/-- An actual projective Cartier ample witness makes the structure map proper. -/
theorem cartierIsAmpleProj_isProper_base {K : Type u} [Field K] {X : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) :
    IsProper (X ↘ Spec (CommRingCat.of K)) := by
  obtain ⟨m, hm, N, e, he, hbase, F, hF, hFgen, φ, hrel⟩ := hA
  have : IsClosedImmersion e := he
  have := polynomialProjectiveToBase_isProper N K
  rw [← hbase]
  infer_instance

/-- The actual conclusion of Ambro's contraction input for a birational map
between normal projective schemes. The form, divisor and chart downstairs are
constructed, and the denominator multiplier is exactly one. -/
theorem ambroContraction_birational {K : Type u} [Field K] [CharZero K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    {n k : ℕ} (hdimX : topologicalKrullDim X = n) (hdimY : topologicalKrullDim Y = k)
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcovX : CodimOneChartCovered n K X)
    (hprojX : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hprojY : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (DX : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d DX)
    (hklt : LogPairIsKlt cX fX d DX)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (hf : Function.Bijective (dominantFunctionFieldAlgHom (K := K) f))
    (H : CartierDivisor Y) (a : ℕ) (ψ : X.functionFieldˣ)
    (hDX : DX = a • cartierPullback f H + principalCartierDivisor X ψ) :
    ∃ (cY : EtaleChart K Y k) (fY : Y.functionFieldˣ) (t : ℕ) (_ : 1 ≤ t)
      (DY : CartierDivisor Y) (φ : Y.functionFieldˣ),
      LogPairBoundaryEffective cY fY (t * d) DY ∧ LogPairIsKlt cY fY (t * d) DY ∧
      DY = (t * a) • H + principalCartierDivisor Y φ ∧ t = 1 := by
  have hnk : n = k := by
    exact_mod_cast hdimX.symm.trans ((birational_topologicalKrullDim_eq f hf).trans hdimY)
  subst k
  obtain ⟨AX, hAX⟩ := hprojX
  obtain ⟨AY, hAY⟩ := hprojY
  have := cartierIsAmpleProj_isProper_base AX hAX
  have := cartierIsAmpleProj_isProper_base AY hAY
  have : IsProper (f ≫ (Y ↘ Spec (CommRingCat.of K))) := by
    rw [HomIsOver.comp_over]
    infer_instance
  have : IsProper f := IsProper.of_comp f (Y ↘ Spec (CommRingCat.of K))
  obtain ⟨cY⟩ := nonempty_etaleChart_of_charZero (K := K) hdimY
  obtain ⟨fY, φ, heffY, hkltY, hpull, hform⟩ :=
    birational_logPair_descent f hf hnormY hnormX hcovX cX fX d hd DX heff hklt
      cY H a ψ hDX
  refine ⟨cY, fY, 1, le_rfl, a • H + principalCartierDivisor Y φ, φ, ?_, ?_, ?_, rfl⟩
  · simpa only [one_mul] using heffY
  · simpa only [one_mul] using hkltY
  · simp only [one_mul]

end MixedFujita
