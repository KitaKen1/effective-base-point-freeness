/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierFixedPartResidualSections
public import MixedFujita.PrincipalizedGlobalGeneration
public import MixedFujita.CartierBirationalZeroDivisors
public import MixedFujita.SteinCartierSectionEquiv

/-! 主化後も元の同じ有限族を保つ残余基点自由性。 See reports/check-262-concentration-residual-snc.json for the verified scope. Actual natural global pullback is semilinear and linear over the actual base ring. SAME finite linear combinations preserve natural restriction, original nonvanishing and exact restricted concentration order. Actual fixed-part removal retains the rational function and recovers the original section. Given actual dominant principalization, the SAME original finite subsystem yields a residual basepointfree family; its linear combinations recover the original combinations with SAME coefficients. Existing global residual Bertini chooses first coefficient nonzero and an actual smooth reduced SNC cut with indicator coefficients. New model construction, final center-exterior LC coefficient bounds, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Principalizing the base ideal of the ORIGINAL finite family produces a
base-point-free residual family corresponding to those SAME original sections.
Its actual inclusion, rational functions and zero divisors are all tracked.
No properness, normality, base-field or new choice of globally generated system
is required. -/
theorem principalized_original_finite_system_exists_residual_basePointFree
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (ρ : T ⟶ X) [IsDominant ρ] {ι : Type*} [Finite ι]
    (P : CartierDivisor X) (s : ι → Γ(P.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (F : CartierDivisor T) (hF : F.IsEffective)
    (hI : effectiveCartierIdealSheaf F hF =
      (⨆ i, effectiveCartierIdealSheaf (cartierSectionZeroDivisor P (s i) (hs i))
        (cartierSectionZeroDivisor_isEffective P (s i) (hs i))).comap ρ) :
    ∃ (t : ι → Γ((cartierPullback ρ P - F).sheaf, ⊤)) (ht : ∀ i, t i ≠ 0),
      (∀ i, Scheme.Modules.Hom.app (cartierEffectiveInclusion (cartierPullback ρ P) F hF) ⊤
        (t i) = cartierDominantPullbackSection ρ P (s i)) ∧
      (∀ i, cartierSectionRational (cartierPullback ρ P - F) (t i) =
        dominantFunctionFieldMap ρ (cartierSectionRational P (s i))) ∧
      (∀ i, cartierSectionZeroDivisor (cartierPullback ρ P - F) (t i) (ht i) =
        cartierPullback ρ (cartierSectionZeroDivisor P (s i) (hs i)) - F) ∧
      CartierSectionsBasePointFree (cartierPullback ρ P - F) t := by
  classical
  let A : ι → CartierDivisor X := fun i => cartierSectionZeroDivisor P (s i) (hs i)
  have hA : ∀ i, (A i).IsEffective := fun i => cartierSectionZeroDivisor_isEffective P (s i) (hs i)
  have hres (i : ι) : (cartierPullback ρ (A i) - F).IsEffective := by
    apply cartier_sub_isEffective_of_effectiveCartierIdealSheaf_le _ _
      (cartierPullback_isEffective ρ (A i) (hA i)) hF
    rw [hI, effectiveCartierIdealSheaf_cartierPullback ρ (A i) (hA i)]
    exact Scheme.IdealSheafData.comap_mono ρ
      (le_iSup (fun i => effectiveCartierIdealSheaf (A i) (hA i)) i)
  have hex (i : ι) := exists_cartier_section_remove_fixed_part_recovers_original
    (cartierPullback ρ P) F hF (cartierDominantPullbackSection ρ P (s i))
    (cartierDominantPullbackSection_ne_zero ρ P (s i) (hs i))
    (by rw [cartierDominantPullbackSection_zeroDivisor]; exact hres i)
  choose t ht hi hr hz using hex
  have hzero (i : ι) : cartierSectionZeroDivisor (cartierPullback ρ P - F) (t i) (ht i) =
      cartierPullback ρ (A i) - F := by
    rw [hz i, cartierDominantPullbackSection_zeroDivisor]
  refine ⟨t, ht, hi, ?_, hzero, ?_⟩
  · intro i
    exact (hr i).trans (cartierDominantPullbackSection_rational ρ P (s i))
  · intro x
    obtain ⟨i, f, hFf, hAf⟩ :=
      exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup
        ρ A hA F hF hI x
    have hloc : (cartierPullback ρ (A i) - F).IsLocalEquationAt x 1 := by
      have h := hAf.mul hFf.inv
      rwa [mul_inv_cancel, ← sub_eq_add_neg] at h
    have hzloc : (cartierSectionZeroDivisor (cartierPullback ρ P - F) (t i) (ht i)).IsLocalEquationAt x 1 :=
      (hzero i).symm ▸ hloc
    exact ⟨i, cartierLocalCoefficient_isUnit_of_zeroDivisor_localEquation_one _ _ (ht i) x hzloc _ _⟩


/-- The SAME coefficients in the residual family recover the ACTUAL dominant
pullback of the ORIGINAL linear combination under the fixed-part inclusion. -/
theorem residual_original_linear_combination_inclusion
    {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    {ι : Type*} [Fintype ι] (P : CartierDivisor X)
    (s : ι → Γ(P.sheaf, ⊤)) (F : CartierDivisor T) (hF : F.IsEffective)
    (t : ι → Γ((cartierPullback ρ P - F).sheaf, ⊤))
    (hi : ∀ i, Scheme.Modules.Hom.app (cartierEffectiveInclusion (cartierPullback ρ P) F hF) ⊤
      (t i) = cartierDominantPullbackSection ρ P (s i)) (a : ι → K) :
    Scheme.Modules.Hom.app (cartierEffectiveInclusion (cartierPullback ρ P) F hF) ⊤
      (∑ i, a i • t i) = cartierDominantPullbackSection ρ P (∑ i, a i • s i) := by
  let j := cartierEffectiveInclusion (cartierPullback ρ P) F hF
  have hj (b : K) (v : Γ((cartierPullback ρ P - F).sheaf, ⊤)) :
      Scheme.Modules.Hom.app j ⊤ (b • v) = b • Scheme.Modules.Hom.app j ⊤ v :=
    Scheme.Modules.Hom.app_smul j (Scheme.Modules.baseRingToGlobalSections K T b) v
  change Scheme.Modules.Hom.app j ⊤ (∑ i, a i • t i) = _
  calc
    Scheme.Modules.Hom.app j ⊤ (∑ i, a i • t i) =
        ∑ i, Scheme.Modules.Hom.app j ⊤ (a i • t i) := map_sum _ _ _
    _ = ∑ i, a i • cartierDominantPullbackSection ρ P (s i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hj (a i) (t i)).trans (congrArg (fun v => a i • v) (hi i))
    _ = cartierDominantPullbackSection ρ P (∑ i, a i • s i) := by
      change (∑ i, a i • (cartierDominantPullbackLinear ρ K P) (s i)) =
        (cartierDominantPullbackLinear ρ K P) (∑ i, a i • s i)
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => ((cartierDominantPullbackLinear ρ K P).map_smul (a i) (s i)).symm)

end MixedFujita
