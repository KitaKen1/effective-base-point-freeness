/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CrepantBertiniPerturbationDescent
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.CrepantSNCBasePointLogCanonical
public import MixedFujita.EffectiveCartierCoefficientSupport

/-! 中心外に関係する固定成分係数零と元lcの外部lc評価。 See reports/check-263-exterior-lc-concentration.json for the verified scope. Actual SNC principalization of the SAME original finite subsystem and boundary-avoiding first-nonzero residual Bertini are assembled internally. Fixed-part coefficients vanish at EVERY prime relevant to points outside actual center support. Old LC coefficient bounds and new reduced-cut coefficients 0/1 prove original all-model pointwise exterior LC. Zero sections are filtered while preserving original nonzero indices. ALL high ample powers preserve nonzero natural restriction up to nonzero scalar and prove exterior LC. Positive RESTRICTED numerical dimension gives all-high actual concentrated original lifts preserving exact restricted order AND exterior LC. No original klt, normality, supplied model, initial L section or KV is required. Ambient nonLC from restricted concentration, actual lower-center iteration, original mL/center adjoint vanishing, nu=0, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- A principalized fixed part has coefficient ZERO at every prime whose image
specializes to a point outside a closed set containing the original base.
This uses actual ideal support, so nonreduced centers are allowed. -/
theorem principalized_fixed_coefficient_zero_over_exterior_point
    {X T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (ρ : T ⟶ X) (I : X.IdealSheafData) (F : CartierDivisor T) (hF : F.IsEffective)
    (hFI : effectiveCartierIdealSheaf F hF = I.comap ρ)
    (Z : Closeds X) (hIZ : (I.support : Set X) ⊆ Z) (x : X) (hx : x ∉ Z)
    (t : CodimensionOnePoint T) (htx : x ∈ closure ({ρ (t : T)} : Set X)) :
    cartierCoefficient F (t : T) = 0 := by
  by_contra hn
  have hmem : (t : T) ∈ (effectiveCartierIdealSheaf F hF).support := by
    by_contra hnot
    exact hn (cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf F hF _ hnot)
  rw [hFI, Scheme.IdealSheafData.support_comap] at hmem
  exact hx ((specializes_iff_mem_closure.mpr htx).mem_closed Z.isClosed (hIZ hmem))


/-- On an actual proper SNC model, an old lc pair remains lc outside the
original base after adding an actual residual reduced SNC cut at coefficient
1/(j*d). No original klt hypothesis, center normality or open-SNC restriction
is needed; the fixed part vanishes at every relevant prime over the exterior. -/
theorem logCanonical_exterior_of_principalized_reduced_snc_cut
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D) (cT : EtaleChart K T n)
    {r q : ℕ} (ξ : Fin r → T) (η : Fin q → T)
    (hξinj : Function.Injective ξ) (hηinj : Function.Injective η)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hη : ∀ i, Order.coheight (η i) = 1)
    (hsnc : IsSNCFamily K n (Fin.append ξ η))
    (hdis : Disjoint (Set.range ξ) (Set.range η))
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (z : T) = 0)
    (I : X.IdealSheafData) (F : CartierDivisor T) (hF : F.IsEffective)
    (hFI : effectiveCartierIdealSheaf F hF = I.comap ρ)
    (hFsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient F (z : T) = 0)
    (M : CartierDivisor X) (G : CartierDivisor T) (hM : cartierPullback ρ M = F + G)
    (hG : ∀ z : CodimensionOnePoint T, cartierCoefficient G (z : T) =
      if (z : T) ∈ Set.range η then 1 else 0)
    (Z : Closeds X) (hIZ : (I.support : Set X) ⊆ Z) (j : ℕ) (hj : 1 ≤ j) :
    ∀ x : X, x ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M) := by
  classical
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let B' := crepantBoundaryCartier ρ hρ c f (j * d) (j • D + M) cT etaleCharts_cover
  have he : B' = j • B + F + G := by
    dsimp [B', B]
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator, hM]
    abel
  have hformula (z : CodimensionOnePoint T) : cartierCoefficient B' (z : T) =
      (j : ℤ) * cartierCoefficient B (z : T) + cartierCoefficient F (z : T) +
        if (z : T) ∈ Set.range η then 1 else 0 := by
    rw [he, cartierCoefficient_add, cartierCoefficient_add, cartierCoefficient_nsmul, hG]
  have hinj : Function.Injective (Fin.append ξ η) :=
    Fin.append_injective_iff.mpr ⟨hξinj, hηinj, fun i l h =>
      Set.disjoint_left.mp hdis ⟨i, rfl⟩ ⟨l, h.symm⟩⟩
  have hprime : ∀ i, Order.coheight (Fin.append ξ η i) = 1 := by
    intro i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simpa using hξ l
    · simpa using hη l
  have hsupp' (z : CodimensionOnePoint T) (hz : (z : T) ∉ Set.range (Fin.append ξ η)) :
      cartierCoefficient B' (z : T) = 0 := by
    have hold : (z : T) ∉ Set.range ξ := by
      rintro ⟨i, hi⟩
      exact hz ⟨Fin.castAdd q i, by simpa using hi⟩
    have hnew : (z : T) ∉ Set.range η := by
      rintro ⟨i, hi⟩
      exact hz ⟨Fin.natAdd r i, by simpa using hi⟩
    rw [hformula, hsupp z hold, hFsupp z hold, ite_eq_right hnew]
    ring
  intro x hx
  apply (logPairIsLogCanonicalOverBasePoint_iff_crepant_snc_coefficients ρ hρ (𝟙 X) x
    c f (j * d) (by nlinarith) (j • D + M) cT (Fin.append ξ η) hinj hprime hsnc hsupp').mpr
  intro i hix
  let z : CodimensionOnePoint T := ⟨Fin.append ξ η i, hprime i⟩
  have hzF : cartierCoefficient F (z : T) = 0 :=
    principalized_fixed_coefficient_zero_over_exterior_point ρ I F hF hFI Z hIZ x hx z
      (by simpa only [Category.comp_id] using hix)
  change cartierCoefficient B' (z : T) ≤ ((j * d : ℕ) : ℤ)
  by_cases hz : (z : T) ∈ Set.range η
  · have hold : (z : T) ∉ Set.range ξ := fun h => Set.disjoint_left.mp hdis h hz
    rw [hformula, hsupp z hold, hzF, ite_eq_left hz]
    push_cast
    nlinarith
  · rw [hformula, hzF, ite_eq_right hz, add_zero, add_zero]
    have hb := logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT z
    exact_mod_cast mul_le_mul_of_nonneg_left hb (by omega : (0 : ℤ) ≤ j)

end MixedFujita
