/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KltNonvanishing
public import MixedFujita.KltStableBaseLocusRemoval

/-! The klt base point free theorem without an Iitaka hypothesis. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Every sufficiently large multiple is globally generated. -/
theorem kltBasePointFreeStatement_holds : KltBasePointFreeStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hproj c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig
  let : IsProper (X ↘ Spec (CommRingCat.of K)) := isProper_structureMap_of_exists_ample_cartier hproj
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  obtain ⟨H, hH⟩ := hproj
  obtain ⟨N₀, hN₀⟩ := klt_nef_eventually_nonzero_section K hdim hn hnorm hcov ⟨H, hH⟩
    c₀ f₀ r hr D' heff hklt D hD a hnef hbig
  let m₀ := N₀ + 1
  have hm₀ : 1 ≤ m₀ := by dsimp [m₀]; omega
  obtain ⟨s₀, hs₀⟩ := hN₀ m₀ (by dsimp [m₀]; omega)
  -- curves
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact ⟨a + 1, fun m hm => linearEffectiveFreeness_normalCurve hdim hnorm ⟨H, hH⟩ c₀ f₀ r hr D'
      heff D hD a hbig m hm⟩
  -- nonvanishing in all large degrees
  obtain ⟨N, hN⟩ := klt_nef_eventually_exists_nonzero_section_of_multiple K hdim hn hnorm hcov
    ⟨H, hH⟩ c₀ f₀ r hr D' heff hklt D hD a hnef hbig m₀ hm₀ s₀ hs₀
  by_cases hν : cartierNumericalDimension K n hdim D H = 0
  · obtain ⟨φ, hφ⟩ := klt_nef_numericalDimension_zero_principal_of_multiple K hdim hn hnorm hcov
      H hH c₀ f₀ r hr D' heff hklt D hD a hnef hbig hν m₀ hm₀ s₀ hs₀
    refine ⟨0, fun q _ => ?_⟩
    rw [hφ, ← principalCartierDivisor_power]
    exact principalCartierDivisor_globallyGenerated (φ ^ q)
  have hν1 : 1 ≤ cartierNumericalDimension K n hdim D H := Nat.one_le_iff_ne_zero.mpr hν
  apply cartier_eventually_generated_of_two_stable_base_locus_removals D 2 3 N (by norm_num)
    (by norm_num)
  intro b hb e he hstable hne
  have hb2 : 2 ≤ b := by
    rcases hb with rfl | rfl
    · exact le_rfl
    · norm_num
  have hpow : N ≤ b ^ e := le_trans he (Nat.lt_pow_self (by omega)).le
  exact kltStableBaseLocusRemovalStatement_holds K X n hdim hn2 hnorm hcov H hH c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig N hN hν1
    b hb2 e hpow hstable hne

end MixedFujita
