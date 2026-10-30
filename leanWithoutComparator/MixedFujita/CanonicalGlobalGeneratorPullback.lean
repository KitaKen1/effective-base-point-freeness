/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NaturalPullbackGlobalUnit
public import MixedFujita.FiniteFreeGlobalGenerators
public import MixedFujita.SGATwistPullbackIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! 同じ自然pullback大域有限族のcanonical全射比較。 See reports/check-261-exact-center-base-canonical-pullback.json for the verified scope. Tracking GLOBAL1 proves exact compatibility of canonical section homs and NATURAL global pullback. Mathlib biproduct formulas identify exterior finite-free pullback with canonical generation by the SAME naturally pulled family. Actual stalk maps reflect unit coefficients without target integrality. ALL high original ample powers have an actual ambient finite family naturally zero on the actual closed center with common ZERO SET exactly its support and a unit coefficient at every point off support. Adding the fixed concentrated lift gives restriction vector (fixed,0,...,0) and exact common zero set. Multiplying a nonzero parameter polynomial by X_0 ensures first coefficient nonzero over an infinite field. Actual SNC exterior-LC Bertini geometry, linear-combination scalar/concentration preservation, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- Pulling back the canonical hom of an ACTUAL global section is exactly the
canonical hom of its NATURAL pulled global section, after the actual unit
comparison. Tracking GLOBAL1 avoids frame or sheafification expansions. -/
theorem modulePullback_homOfSection_natural_global_section
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) (s : Γ(M, ⊤)) :
    (Scheme.Modules.pullbackObjUnitIso φ).inv ≫
      (Scheme.Modules.pullback φ).map (CohomologyAux.homOfSection M s) =
        CohomologyAux.homOfSection ((Scheme.Modules.pullback φ).obj M)
          (modulePullbackGlobalSections φ M s) := by
  let q := (Scheme.Modules.pullbackObjUnitIso φ).inv ≫
    (Scheme.Modules.pullback φ).map (CohomologyAux.homOfSection M s)
  have htop : Scheme.Modules.Hom.app (CohomologyAux.homOfSection M s) ⊤ (1 : Γ(X, ⊤)) = s := by
    rw [CohomologyAux.homOfSection_app]
    simp only [homOfLE_refl, op_id, M.presheaf.map_id, ConcreteCategory.id_apply, one_smul]
  have hq : Scheme.Modules.Hom.app q ⊤ (1 : Γ(Y, ⊤)) = modulePullbackGlobalSections φ M s := by
    change Scheme.Modules.Hom.app ((Scheme.Modules.pullback φ).map (CohomologyAux.homOfSection M s)) ⊤
      (Scheme.Modules.Hom.app (Scheme.Modules.pullbackObjUnitIso φ).inv ⊤ (1 : Γ(Y, ⊤))) = _
    rw [modulePullbackObjUnitIso_inv_global_one]
    have h := modulePullbackGlobalSections_naturality φ (CohomologyAux.homOfSection M s) (1 : Γ(X, ⊤))
    rw [htop] at h
    exact h.symm
  exact (unit_hom_eq_homOfSection_global_one q).symm.trans
    (congrArg (CohomologyAux.homOfSection ((Scheme.Modules.pullback φ).obj M)) hq)


/-- The actual pullback of a finite canonical generator map is EXACTLY the
canonical generator map of the SAME NATURALLY pulled global sections. The
finite-free comparison is the already constructed actual comparison. -/
theorem modulePullbackUnitBiproductIso_inv_map_global_generator_desc
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) (k : ℕ) (s : Fin k → Γ(M, ⊤)) :
    (modulePullbackUnitBiproductIso φ k).inv ≫
      (Scheme.Modules.pullback φ).map (biproduct.desc (fun i => CohomologyAux.homOfSection M (s i))) =
        biproduct.desc (fun i => CohomologyAux.homOfSection ((Scheme.Modules.pullback φ).obj M)
          (modulePullbackGlobalSections φ M (s i))) := by
  unfold modulePullbackUnitBiproductIso
  rw [Iso.trans_inv, Category.assoc, biproduct.mapBiproduct_inv_map_desc, biproduct.mapIso_inv,
    biproduct.map_desc]
  congr 1
  funext i
  exact modulePullback_homOfSection_natural_global_section φ M (s i)

end MixedFujita
