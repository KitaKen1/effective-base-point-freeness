/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalGlobalGeneratorPullback
public import MixedFujita.FiniteGlobalAffineGeneration
public import MixedFujita.ModuleLocalPullbackCoefficients
public import MixedFujita.CartierGlobalGenerationFiniteFamily

/-! 同じ生成族の元Cartier単元反映と自然零の像上零性。 See reports/check-261-exact-center-base-canonical-pullback.json for the verified scope. Tracking GLOBAL1 proves exact compatibility of canonical section homs and NATURAL global pullback. Mathlib biproduct formulas identify exterior finite-free pullback with canonical generation by the SAME naturally pulled family. Actual stalk maps reflect unit coefficients without target integrality. ALL high original ample powers have an actual ambient finite family naturally zero on the actual closed center with common ZERO SET exactly its support and a unit coefficient at every point off support. Adding the fixed concentrated lift gives restriction vector (fixed,0,...,0) and exact common zero set. Multiplying a nonzero parameter polynomial by X_0 ensures first coefficient nonzero over an infinite field. Actual SNC exterior-LC Bertini geometry, linear-combination scalar/concentration preservation, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- A canonical generating family of NATURALLY pulled sections has a member
with unit ORIGINAL coefficient at each image point, in ANY specified original
local frame. The actual stalk map is local and reflects units. -/
theorem natural_pulled_global_generators_reflect_unit_in_original_frame
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
    (k : ℕ) (s : Fin k → Γ(M, ⊤))
    [Epi (biproduct.desc (fun i => CohomologyAux.homOfSection ((Scheme.Modules.pullback φ).obj M)
      (modulePullbackGlobalSections φ M (s i))))]
    (U : X.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (y : Y) (hy : φ y ∈ U) :
    ∃ i, IsUnit (moduleOverFrameGlobalCoefficientGerm M U (moduleRestrictFrameOverIso M U e) (φ y) hy (s i)) := by
  classical
  let N := (Scheme.Modules.pullback φ).obj M
  let : N.IsQuasicoherent := inferInstance
  let V := φ ⁻¹ᵁ U
  let d := moduleRestrictFrameOverIso N V (moduleLocalPullbackFrameIso φ M U e)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ V from hy) V.isOpen
  let dW := moduleOverFrameRestrictIso N V d W hWV
  obtain ⟨i, hi⟩ := finite_global_generators_exists_unit_at_affine_frame N k
    (fun i => modulePullbackGlobalSections φ M (s i)) ⟨W, hW⟩ dW y hyW
  have hiV : IsUnit (moduleOverFrameGlobalCoefficientGerm N V d y hy
      (modulePullbackGlobalSections φ M (s i))) := by
    simpa only [dW, moduleOverFrameGlobalCoefficientGerm_restrict] using hi
  have heq := moduleLocalPullbackFrame_global_germ φ M U e y hy (s i)
  have himap : IsUnit (φ.stalkMap y
      (moduleOverFrameGlobalCoefficientGerm M U (moduleRestrictFrameOverIso M U e) (φ y) hy (s i))) := by
    rw [← heq]
    exact hiV
  exact ⟨i, isUnit_of_map_unit (φ.stalkMap y).hom _ himap⟩


/-- Canonical generation by the SAME natural pulled Cartier sections supplies
an ORIGINAL Cartier unit coefficient at every image point. No normality,
properness, dominance or target integrality is needed. -/
theorem natural_pulled_Cartier_generators_unit_at_image
    {X Y : Scheme.{u}} [IsIntegral X] (φ : Y ⟶ X) (P : CartierDivisor X)
    (k : ℕ) (s : Fin k → Γ(P.sheaf, ⊤))
    [Epi (biproduct.desc (fun i => CohomologyAux.homOfSection ((Scheme.Modules.pullback φ).obj P.sheaf)
      (modulePullbackGlobalSections φ P.sheaf (s i))))] (y : Y) :
    ∃ i, IsUnit (cartierLocalCoefficient P (φ y)
      (Classical.choose (P.exists_isLocalEquationAt (φ y)))
      (Classical.choose_spec (P.exists_isLocalEquationAt (φ y))) (s i)) := by
  classical
  let := P.isInvertible_sheaf
  let : P.sheaf.IsQuasicoherent := inferInstance
  let f := Classical.choose (P.exists_isLocalEquationAt (φ y))
  have hf := Classical.choose_spec (P.exists_isLocalEquationAt (φ y))
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  obtain ⟨i, hi⟩ := natural_pulled_global_generators_reflect_unit_in_original_frame φ P.sheaf k s U
    (cartierOpenRestrictFrameIso P U f hU) y hy
  exact ⟨i, by simpa only [moduleRestrictFrameGlobalCoefficientGerm_cartier] using hi⟩


/-- A ZERO natural pulled Cartier section cannot have a unit original
coefficient at any image point. The target scheme can be nonreduced or
nonintegral: the actual local stalk map alone gives the contradiction. -/
theorem Cartier_natural_pullback_zero_image_mem_zero_locus
    {X Y : Scheme.{u}} [IsIntegral X] (φ : Y ⟶ X) (P : CartierDivisor X)
    (s : Γ(P.sheaf, ⊤)) (hzero : modulePullbackGlobalSections φ P.sheaf s = 0)
    (y : Y) : φ y ∈ cartierSectionZeroLocus P s := by
  classical
  obtain ⟨f, hf⟩ := P.exists_isLocalEquationAt (φ y)
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  have h := moduleLocalPullbackFrame_global_germ φ P.sheaf U (cartierOpenRestrictFrameIso P U f hU) y hy s
  rw [hzero] at h
  have hz : φ.stalkMap y (cartierLocalCoefficient P (φ y) f
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hy) s) = 0 := by
    have hcoef := moduleRestrictFrameGlobalCoefficientGerm_cartier P U f hU (φ y) hy s
    have hleft : moduleOverFrameGlobalCoefficientGerm ((Scheme.Modules.pullback φ).obj P.sheaf)
        (φ ⁻¹ᵁ U) (moduleRestrictFrameOverIso _ _ (moduleLocalPullbackFrameIso φ P.sheaf U
          (cartierOpenRestrictFrameIso P U f hU))) y hy 0 = 0 := by
      simp only [moduleOverFrameGlobalCoefficientGerm, map_zero]
    exact (congrArg (φ.stalkMap y) hcoef).symm.trans (h.symm.trans hleft)
  change φ y ∉ cartierSectionNonvanishingOpen P s
  intro hu
  have hunit := (mem_cartierSectionNonvanishingOpen_iff_localCoefficient P s (φ y) f
    (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hy)).mp hu
  exact (hunit.map (φ.stalkMap y).hom).ne_zero hz

end MixedFujita
