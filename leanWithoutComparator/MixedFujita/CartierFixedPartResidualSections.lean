/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionLifting
public import MixedFujita.CartierBigDefinition
public import MixedFujita.CartierLocalCoefficient

/-! 同じ関数体元による固定成分除去と元切断回収。 See reports/check-262-concentration-residual-snc.json for the verified scope. Actual natural global pullback is semilinear and linear over the actual base ring. SAME finite linear combinations preserve natural restriction, original nonvanishing and exact restricted concentration order. Actual fixed-part removal retains the rational function and recovers the original section. Given actual dominant principalization, the SAME original finite subsystem yields a residual basepointfree family; its linear combinations recover the original combinations with SAME coefficients. Existing global residual Bertini chooses first coefficient nonzero and an actual smooth reduced SNC cut with indicator coefficients. New model construction, final center-exterior LC coefficient bounds, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- Removing ANY actual Cartier fixed part bounded by the actual zero divisor
constructs the residual section with the SAME rational function and exact
residual zero divisor. No normality, properness or DVR division is required. -/
theorem exists_cartier_section_remove_fixed_part
    {X : Scheme.{u}} [IsIntegral X] (P F : CartierDivisor X)
    (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0)
    (hres : (cartierSectionZeroDivisor P s hs - F).IsEffective) :
    ∃ (t : Γ((P - F).sheaf, ⊤)) (ht : t ≠ 0),
      cartierSectionRational (P - F) t = cartierSectionRational P s ∧
      cartierSectionZeroDivisor (P - F) t ht = cartierSectionZeroDivisor P s hs - F := by
  let u := cartierSectionUnit P s hs
  have he : (P - F + principalCartierDivisor X u).IsEffective := by
    convert hres using 1
    dsimp only [cartierSectionZeroDivisor, u]
    abel
  let r := Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) ⊤ (1 : Γ(X, ⊤))
  have hr : r ∈ (P - F + principalCartierDivisor X u).sections ⊤ :=
    CartierDivisor.isEffective_iff_one_mem_sections.mp he
  have hmem := (cartierSections_mem_principalShift (P - F) u ⊤ r).mp hr
  let t := CartierDivisor.sectionMk _ hmem
  have htval : cartierSectionRational (P - F) t = cartierSectionRational P s := by
    rw [cartierSectionRational_sectionMk_of_mem,
      rationalFunctionsEquiv_rationalFunctionsMul_app]
    dsimp only [r]
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one]
    rfl
  have ht : t ≠ 0 := by
    intro hz
    apply hs
    apply cartierSectionRational_injective P
    rw [← htval, hz, map_zero, map_zero]
  refine ⟨t, ht, htval, ?_⟩
  have hu : cartierSectionUnit (P - F) t ht = cartierSectionUnit P s hs := Units.ext htval
  rw [cartierSectionZeroDivisor, hu, cartierSectionZeroDivisor]
  abel


/-- Triviality of the ACTUAL zero divisor at a point makes the ACTUAL section
coefficient a unit in every chosen local frame. -/
theorem cartierLocalCoefficient_isUnit_of_zeroDivisor_localEquation_one
    {X : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X)
    (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0) (x : X)
    (hz : (cartierSectionZeroDivisor P s hs).IsLocalEquationAt x 1)
    (f : X.functionFieldˣ) (hf : P.IsLocalEquationAt x f) :
    IsUnit (cartierLocalCoefficient P x f hf s) := by
  obtain ⟨v, hv⟩ := (cartierSectionZeroDivisor_localEquation P s hs x f hf).exists_unit_mul_eq hz
  have he : cartierLocalCoefficient P x f hf s = (v : X.presheaf.stalk x) := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [cartierLocalCoefficient_image]
    simpa only [Units.val_one, mul_one, Units.val_mul, cartierSectionUnit_val] using hv.symm
  rw [he]
  exact v.isUnit


/-- Residual removal recovers the ORIGINAL section under the actual inclusion,
with no arbitrary replacement by another globally generated section. -/
theorem exists_cartier_section_remove_fixed_part_recovers_original
    {X : Scheme.{u}} [IsIntegral X] (P F : CartierDivisor X) (hF : F.IsEffective)
    (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0)
    (hres : (cartierSectionZeroDivisor P s hs - F).IsEffective) :
    ∃ (t : Γ((P - F).sheaf, ⊤)) (ht : t ≠ 0),
      Scheme.Modules.Hom.app (cartierEffectiveInclusion P F hF) ⊤ t = s ∧
      cartierSectionRational (P - F) t = cartierSectionRational P s ∧
      cartierSectionZeroDivisor (P - F) t ht = cartierSectionZeroDivisor P s hs - F := by
  obtain ⟨t, ht, he, hz⟩ := exists_cartier_section_remove_fixed_part P F s hs hres
  refine ⟨t, ht, ?_, he, hz⟩
  apply cartierSectionRational_injective P
  have hi : cartierSectionRational P
      (Scheme.Modules.Hom.app (cartierEffectiveInclusion P F hF) ⊤ t) =
      cartierSectionRational (P - F) t := by
    apply congrArg (rationalFunctionsEquiv (X := X) ⊤)
      (ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤)
        (cartierEffectiveInclusion_ι P F hF)) t)
  exact hi.trans he

end MixedFujita
