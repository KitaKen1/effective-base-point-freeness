/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SameDimensionAmbroDescent
public import MixedFujita.SemiampleContractionProof

/-!
The original Ambro input is equivalent to its restriction to strictly smaller
target dimension. Dominance bounds target dimension, and the same-dimensional
case is proved by actual Stein birationality and klt-pair descent. Consequently
the full F2 reduction only needs Ambro for positive relative dimension.
This does not prove that remaining canonical-bundle-formula input.
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

/-- The unchanged manuscript Ambro input, restricted to strictly smaller positive
target dimension. The removed same-dimensional case is proved independently. -/
def AmbroStrictDimensionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₁ : X.functionFieldˣ) (r' : ℕ), 1 ≤ r' →
    ∀ D'' : CartierDivisor X, LogPairBoundaryEffective c₀ f₁ r' D'' → LogPairIsKlt c₀ f₁ r' D'' →
    ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
      [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (k : ℕ),
      topologicalKrullDim Y = k → 1 ≤ k → k < n →
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered k K Y →
      (∃ H₁ : CartierDivisor Y, CartierIsAmpleProj K H₁) →
      ∀ (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))],
        (∀ V : Y.Opens, Function.Bijective (f.app V).hom) →
      ∀ (H : CartierDivisor Y) (u : ℕ) (ψ : X.functionFieldˣ),
        D'' = u • cartierPullback f H + principalCartierDivisor X ψ →
        ∃ (cY : EtaleChart K Y k) (fY : Y.functionFieldˣ) (t : ℕ) (_ : 1 ≤ t)
          (DY : CartierDivisor Y) (φ : Y.functionFieldˣ),
          LogPairBoundaryEffective cY fY (t * r') DY ∧ LogPairIsKlt cY fY (t * r') DY ∧
          DY = (t * u) • H + principalCartierDivisor Y φ

/-- The full original Ambro statement is equivalent to only its strict-dimension
part. Its same-dimensional case is supplied by a proved construction. -/
theorem ambroContractionStatement_iff_strict_dimension :
    AmbroContractionStatement.{u} ↔ AmbroStrictDimensionStatement.{u} := by
  constructor
  · intro h K _ _ _ _ X _ _ _ _ n hdimX hn hnormX hcovX hprojX
      cX fX d hd DX heff hklt Y _ _ _ _ k hdimY hk hkn hnormY hcovY hprojY
      f _ _ happ H a ψ hDX
    exact h K X n hdimX hn hnormX hcovX hprojX cX fX d hd DX heff hklt
      Y k hdimY hk hnormY hcovY hprojY f happ H a ψ hDX
  · intro h K _ _ _ _ X _ _ _ _ n hdimX hn hnormX hcovX hprojX
      cX fX d hd DX heff hklt Y _ _ _ _ k hdimY hk hnormY hcovY hprojY
      f _ _ happ H a ψ hDX
    have hle : k ≤ n := by
      have hdim := dominant_topologicalKrullDim_le (K := K) f
      rw [hdimX, hdimY] at hdim
      exact_mod_cast hdim
    by_cases hkn : k < n
    · exact h K X n hdimX hn hnormX hcovX hprojX cX fX d hd DX heff hklt
        Y k hdimY hk hkn hnormY hcovY hprojY f happ H a ψ hDX
    · have heq : k = n := by omega
      subst k
      obtain ⟨cY, fY, t, ht, DY, φ, heffY, hkltY, hrel, ht1⟩ :=
        ambroContraction_same_dimension hdimX hdimY hnormX hcovX hprojX hnormY hprojY
          cX fX d hd DX heff hklt f (fun U => (happ U).2) H a ψ hDX
      exact ⟨cY, fY, t, ht, DY, φ, heffY, hkltY, hrel⟩

/-- F2 only needs Ambro for strictly smaller positive target dimension, alongside
K-NF, klt base-point-freeness and nef-plus-ample positivity. -/
theorem linearEffectiveFreeness_of_knf_of_bpf_of_nefAddAmple_of_strictAmbro
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hna : NefAddAmpleStatement.{u}) (hamb : AmbroStrictDimensionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_knf_of_basePointFree_of_nefAddAmple_of_ambro hKNF hbpf hna
    (ambroContractionStatement_iff_strict_dimension.mpr hamb)

end MixedFujita
