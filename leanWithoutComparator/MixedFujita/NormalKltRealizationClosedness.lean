/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.F2RemainingInputs
public import MixedFujita.KltNumericalFreenessConditional
public import MixedFujita.ProjectiveCurveCohomology

/-!
The closedness input of K-NF for normal klt pairs with effective boundary only (step 15).

`KltRealizationClosedness` (check 569) asks for the closedness of the realization sets for every
pair satisfying `LogPairIsKlt` on every integral variety. That includes sub-boundaries and
non-normal varieties, where the lower semicontinuity of thresholds behind the closedness fails in
general (on a blow-up with boundary −E the total threshold of a family can be smaller than the
threshold of its fibre). K-NF uses the closedness only for the pair of its own statement, which is
normal with effective boundary: its reduction to minimizer data is made variety by variety
(`klt_cartierIsGloballyGenerated_of_minimizerData`,
`klt_ample_minimizerData_of_knf_numerical_and_closedPoints`), as in the smooth case (check 562).

So K-NF and F2 follow from the closedness for normal klt pairs with effective boundary
(`NormalKltRealizationClosedness`, `kawamataNumericalFreeness_of_normalKltRealizationClosedness`,
`linearEffectiveFreeness_of_normalKltRealizationClosedness_of_basePointFree_of_ambro`). This
statement is implied by `KltRealizationClosedness`
(`normalKltRealizationClosedness_of_kltRealizationClosedness`), and on smooth varieties it is
proved (checks 560 and 561).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- The closedness of the realization sets for normal klt pairs with effective boundary, the
remaining input of K-NF: for a klt pair with effective boundary on a normal variety of finite type
over an uncountable algebraically closed field of characteristic zero whose codimension-one points
lie in étale charts, every ample A and every closed point x, the realization sets in the tuple at
x are Zariski closed and the realization sets in the point are closed on closed points, for all
large multiples of A. -/
def NormalKltRealizationClosedness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (Y : Scheme.{u})
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim Y = n → 1 ≤ n →
    (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered n K Y →
    ∀ (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
    ∀ (D₀ A : CartierDivisor Y), LogPairBoundaryEffective cY fY d D₀ →
      LogPairIsKlt cY fY d D₀ → CartierIsAmpleProj K A →
      ∀ x : Y, IsClosed ({x} : Set Y) →
        (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • A) x) ∧
        (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
          IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
            fY d D₀ (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})

/-- The closedness for all klt pairs implies the closedness for normal klt pairs with effective
boundary. -/
theorem normalKltRealizationClosedness_of_kltRealizationClosedness
    (h : KltRealizationClosedness.{u}) : NormalKltRealizationClosedness.{u} :=
  fun K _ _ _ _ Y _ _ _ _ _ _ _ _ _ cY fY d hd D₀ A _ hklt hA x hx =>
    h K Y _ cY fY d hd D₀ A hklt hA x hx

/-- **K-NF from the closedness of the realization sets of normal klt pairs with effective
boundary** (Kawamata–Viehweg vanishing is proved). -/
theorem kawamataNumericalFreeness_of_normalKltRealizationClosedness
    (h : NormalKltRealizationClosedness.{u}) : KawamataNumericalFreeness.{u} := by
  intro K _ _ _ _ Y _ _ _ _ n hdim hn hnorm hcov c₀ f₀ r hr D heff hklt P hA hvol hsub
  obtain ⟨m, hm, v, e, hcl, he, -⟩ := id hA
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of K))
  exact klt_cartierIsGloballyGenerated_of_minimizerData (kawamataViehwegVanishingSNC_of_charZero K n)
    hn hnorm hcov c₀ f₀ r hr D heff hklt P hA
    (fun m₀ hm₀ x hx _ =>
      klt_ample_minimizerData_of_knf_numerical_and_closedPoints hn c₀ f₀ r hr D (r • P - D) hklt
        hA hvol hsub x hx
        (h K Y n hdim hn hnorm hcov c₀ f₀ r hr D (r • P - D) heff hklt hA x hx).1
        (h K Y n hdim hn hnorm hcov c₀ f₀ r hr D (r • P - D) heff hklt hA x hx).2 m₀ hm₀)

/-- **F2 from the closedness of the realization sets of normal klt pairs with effective boundary,
the base point free theorem for klt pairs and Ambro's canonical bundle formula for contractions to
lower-dimensional bases.** -/
theorem linearEffectiveFreeness_of_normalKltRealizationClosedness_of_basePointFree_of_ambro
    (h : NormalKltRealizationClosedness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hamb : AmbroStrictDimensionStatement.{u}) : LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_knf_of_bpf_of_nefAddAmple_of_strictAmbro
    (kawamataNumericalFreeness_of_normalKltRealizationClosedness h) hbpf nefAddAmpleStatement_holds
    hamb

end MixedFujita
