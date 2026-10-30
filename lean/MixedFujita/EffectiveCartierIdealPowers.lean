/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.InfinitesimalIdealSheafPowers

/-! Cartier multiplicities agree with actual ideal-sheaf powers, including
degree zero. The comparison with the canonical ideal module preserves its
inclusion in the structure sheaf. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} [IsIntegral X]

theorem regularEquationRationalUnit_pow (U : X.Opens) [Nonempty U]
    (a : Γ(X, U)) (ha : a ≠ 0) (n : ℕ) :
    regularEquationRationalUnit X U (a ^ n) (pow_ne_zero n ha) =
      regularEquationRationalUnit X U a ha ^ n := by
  apply Units.ext
  change X.germToFunctionField U (a ^ n) = (X.germToFunctionField U a) ^ n
  exact map_pow (X.germToFunctionField U).hom a n

theorem regularEquation_nsmul (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (a : Γ(X, U)) (ha : a ≠ 0)
    (hEq : rationalUnitClass X U (Additive.ofMul
      (regularEquationRationalUnit X U a ha)) = D |_ U) (n : ℕ) :
    rationalUnitClass X U (Additive.ofMul
      (regularEquationRationalUnit X U (a ^ n) (pow_ne_zero n ha))) = (n • D) |_ U := by
  rw [regularEquationRationalUnit_pow U a ha n, ofMul_pow, map_nsmul, hEq]
  exact (map_nsmul ((cartierDivisorSheaf X).1.map
    (homOfLE (le_top : U ≤ ⊤)).op).hom n D).symm

theorem effectiveCartierIdealSheaf_nsmul (D : CartierDivisor X) (hD : D.IsEffective)
    (n : ℕ) (hnD : (n • D).IsEffective) :
    effectiveCartierIdealSheaf (n • D) hnD = (effectiveCartierIdealSheaf D hD) ^ n := by
  classical
  choose U hx hne a ha hEq using exists_affineOpen_regularEquation_of_isEffective D hD
  let (x : X) : Nonempty (U x).1 := hne x
  have hcover : ⨆ x : X, (U x).1 = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro x
  change (effectiveCartierIdealSheaf (n • D) hnD).ideal (U x) =
    ((effectiveCartierIdealSheaf D hD).ideal (U x)) ^ n
  rw [effectiveCartierIdealSheaf_ideal_eq_span D hD (U x) (a x) (ha x) (hEq x),
    effectiveCartierIdealSheaf_ideal_eq_span (n • D) hnD (U x) ((a x) ^ n)
      (pow_ne_zero n (ha x)) (regularEquation_nsmul D (U x).1 (a x) (ha x) (hEq x) n),
    Ideal.span_singleton_pow]

noncomputable def effectiveCartierIdealModuleIsoOfEq (D : CartierDivisor X)
    (hD : D.IsEffective) (J : X.IdealSheafData)
    (hJ : effectiveCartierIdealSheaf D hD = J) :
    (-D).sheaf ≅ idealSheafDataModule J := by
  subst J
  exact effectiveCartierIdealModuleIso D hD

@[reassoc (attr := simp)]
theorem effectiveCartierIdealModuleIsoOfEq_inclusion (D : CartierDivisor X)
    (hD : D.IsEffective) (J : X.IdealSheafData)
    (hJ : effectiveCartierIdealSheaf D hD = J) :
    (effectiveCartierIdealModuleIsoOfEq D hD J hJ).hom ≫
        idealSheafDataModuleInclusion J = negativeCartierToUnit X D hD := by
  subst J
  exact effectiveCartierIdealModuleIso_hom_inclusion D hD

noncomputable def effectiveCartierIdealPowerModuleIso (D : CartierDivisor X)
    (hD : D.IsEffective) (n : ℕ) :
    (-(n • D)).sheaf ≅ idealSheafDataModule ((effectiveCartierIdealSheaf D hD) ^ n) :=
  effectiveCartierIdealModuleIsoOfEq (n • D)
    ((CartierDivisor.mem_effectiveSubmonoid _).mp
      ((CartierDivisor.effectiveSubmonoid X).nsmul_mem
        ((CartierDivisor.mem_effectiveSubmonoid D).mpr hD) n)) _
    (effectiveCartierIdealSheaf_nsmul D hD n _)

@[reassoc (attr := simp)]
theorem effectiveCartierIdealPowerModuleIso_inclusion (D : CartierDivisor X)
    (hD : D.IsEffective) (n : ℕ) :
    (effectiveCartierIdealPowerModuleIso D hD n).hom ≫
        idealSheafDataModuleInclusion ((effectiveCartierIdealSheaf D hD) ^ n) =
      negativeCartierToUnit X (n • D)
        ((CartierDivisor.mem_effectiveSubmonoid _).mp
      ((CartierDivisor.effectiveSubmonoid X).nsmul_mem
        ((CartierDivisor.mem_effectiveSubmonoid D).mpr hD) n)) :=
  effectiveCartierIdealModuleIsoOfEq_inclusion _ _ _ _

end MixedFujita
