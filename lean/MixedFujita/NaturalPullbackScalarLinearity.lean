/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePullbackSections

/-! 実自然pullbackの半線形性とbase環線形性。 See reports/check-262-concentration-residual-snc.json for the verified scope. Actual natural global pullback is semilinear and linear over the actual base ring. SAME finite linear combinations preserve natural restriction, original nonvanishing and exact restricted concentration order. Actual fixed-part removal retains the rational function and recovers the original section. Given actual dominant principalization, the SAME original finite subsystem yields a residual basepointfree family; its linear combinations recover the original combinations with SAME coefficients. Existing global residual Bertini chooses first coefficient nonzero and an actual smooth reduced SNC cut with indicator coefficients. New model construction, final center-exterior LC coefficient bounds, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- NATURAL actual global pullback is semilinear over the ACTUAL global-ring
map. TauCeti's natural global-scalar endomorphism removes all top-open transport
bookkeeping. Arbitrary schemes and modules are allowed. -/
theorem modulePullbackGlobalSections_smul_global_function
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    modulePullbackGlobalSections φ M (r • s) = φ.appTop r • modulePullbackGlobalSections φ M s := by
  have h := modulePullbackGlobalSections_naturality φ (Scheme.Modules.globalSectionsSmul M r) s
  rw [Scheme.Modules.pullback_map_globalSectionsSmul] at h
  rw [Scheme.Modules.globalSectionsSmul_app, Scheme.Modules.globalSectionsSmul_app] at h
  change modulePullbackGlobalSections φ M (X.presheaf.map (𝟙 (op ⊤)) r • s) =
    Y.presheaf.map (𝟙 (op ⊤)) (φ.appTop r) • modulePullbackGlobalSections φ M s at h
  simpa only [X.presheaf.map_id, Y.presheaf.map_id, ConcreteCategory.id_apply] using h


/-- An ACTUAL morphism over the base commutative ring preserves its image in
global regular functions. -/
theorem appTop_baseRingToGlobalSections_of_isOver
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of R))] (r : R) :
    φ.appTop (Scheme.Modules.baseRingToGlobalSections R X r) =
      Scheme.Modules.baseRingToGlobalSections R Y r := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply, Scheme.Modules.baseRingToGlobalSections_apply]
  have h := congrArg Scheme.Hom.appTop (HomIsOver.comp_over (f := φ) (S := Spec (CommRingCat.of R)))
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)


/-- NATURAL actual global pullback is linear over ANY base commutative ring
for an actual morphism over that base. No dominance or integrality is used. -/
theorem modulePullbackGlobalSections_smul_base
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of R))] (M : X.Modules) (r : R) (s : Γ(M, ⊤)) :
    modulePullbackGlobalSections φ M (r • s) = r • modulePullbackGlobalSections φ M s := by
  simp only [Scheme.Modules.base_smul_globalSections, modulePullbackGlobalSections_smul_global_function,
    appTop_baseRingToGlobalSections_of_isOver]

end MixedFujita
