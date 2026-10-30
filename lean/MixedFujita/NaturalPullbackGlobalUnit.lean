/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePullbackSections
public import SGA.Foundations.Cohomology.Devissage

/-! 自然pullback大域1と実unit比較の厳密一致。 See reports/check-261-exact-center-base-canonical-pullback.json for the verified scope. Tracking GLOBAL1 proves exact compatibility of canonical section homs and NATURAL global pullback. Mathlib biproduct formulas identify exterior finite-free pullback with canonical generation by the SAME naturally pulled family. Actual stalk maps reflect unit coefficients without target integrality. ALL high original ample powers have an actual ambient finite family naturally zero on the actual closed center with common ZERO SET exactly its support and a unit coefficient at every point off support. Adding the fixed concentrated lift gives restriction vector (fixed,0,...,0) and exact common zero set. Multiplying a nonzero parameter polynomial by X_0 ensures first coefficient nonzero over an infinite field. Actual SNC exterior-LC Bertini geometry, linear-combination scalar/concentration preservation, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000


/-- The NATURAL pullback of the GLOBAL structure-sheaf unit becomes the actual
global unit under the actual unit comparison, with no scheme hypotheses. -/
theorem modulePullbackGlobalSections_unit_one
    {X Y : Scheme.{u}} (φ : Y ⟶ X) :
    Scheme.Modules.Hom.app (Scheme.Modules.pullbackObjUnitIso φ).hom ⊤
      (modulePullbackGlobalSections φ (CohomologyAux.unitModule X) (1 : Γ(X, ⊤))) = (1 : Γ(Y, ⊤)) := by
  rw [modulePullbackGlobalSections_eq_top]
  let i := eqToHom φ.preimage_top.symm
  have hn := CohomologyAux.hom_app_presheaf_map (Scheme.Modules.pullbackObjUnitIso φ).hom i
    (modulePullbackSections φ (SheafOfModules.unit X.ringCatSheaf) ⊤ (1 : Γ(X, ⊤)))
  have hc := modulePullbackSections_unit_coefficient φ ⊤ (1 : Γ(X, ⊤))
  calc
    _ = (CohomologyAux.unitModule Y).presheaf.map i.op
        (Scheme.Modules.Hom.app (Scheme.Modules.pullbackObjUnitIso φ).hom (φ ⁻¹ᵁ ⊤)
          (modulePullbackSections φ (SheafOfModules.unit X.ringCatSheaf) ⊤ (1 : Γ(X, ⊤)))) := hn
    _ = Y.presheaf.map i.op (φ.app ⊤ (1 : Γ(X, ⊤))) :=
      congrArg (fun r : Γ(Y, φ ⁻¹ᵁ ⊤) => Y.presheaf.map i.op r) hc
    _ = (1 : Γ(Y, ⊤)) := by rw [map_one, map_one]


/-- The inverse unit comparison sends GLOBAL1 to its NATURAL pulled section. -/
theorem modulePullbackObjUnitIso_inv_global_one
    {X Y : Scheme.{u}} (φ : Y ⟶ X) :
    Scheme.Modules.Hom.app (Scheme.Modules.pullbackObjUnitIso φ).inv ⊤ (1 : Γ(Y, ⊤)) =
      modulePullbackGlobalSections φ (CohomologyAux.unitModule X) (1 : Γ(X, ⊤)) := by
  apply CohomologyAux.app_injective_of_mono (Scheme.Modules.pullbackObjUnitIso φ).hom ⊤
  rw [modulePullbackGlobalSections_unit_one]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun a => Scheme.Modules.Hom.app a ⊤) (Scheme.Modules.pullbackObjUnitIso φ).inv_hom_id)
    (1 : Γ(Y, ⊤))
  exact h

end MixedFujita
