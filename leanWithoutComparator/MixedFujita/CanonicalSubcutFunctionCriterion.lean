/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalSubcutUnitInclusion

/-! 標準kernel像の任意正則関数・全開上Cartier格子判定。 See reports/check-246-lc-radical-reduced-fixed-subscheme-lifting.json for the verified scope. The actual lc kernel image ideal is radical and its nonempty lower-dimensional subscheme W is reduced. One fixed I and W works for all nef-big adjoints. Usual KV gives actual restriction section lifting; any nonzero restricted section removes an original basepoint on W. Usual KV itself, restricted-section nonvanishing and stable-base-locus placement remain unproved; no normal lc-center adjunction, klt BPF or full F1/F2 is claimed. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The canonical kernel image criterion for EVERY regular function on EVERY open.
It uses the actual effective-divisor unit map and Cartier rational sections. -/
theorem function_in_range_cartierSubcutPushforwardUnitInclusion_iff
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (p : T ⟶ X)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] (U : X.Opens) (a : Γ(X, U)) :
    (∃ s : Γ((Scheme.Modules.pushforward p).obj (E - S).sheaf, U),
      Scheme.Modules.Hom.app (cartierSubcutPushforwardUnitInclusion p E S hE hS) U s = a) ↔
      Scheme.Modules.Hom.app (toRationalFunctions T) (p ⁻¹ᵁ U) ((p.app U).hom a) ∈
        (E - S).sections (p ⁻¹ᵁ U) := by
  let c := effectiveCartierPushforwardUnitMap p E hE
  let j := cartierSubcutPushforwardUnitInclusion p E S hE hS
  have hcomp : j ≫ c = (Scheme.Modules.pushforward p).map (cartierEffectiveInclusion E S hS) :=
    cartierSubcutPushforwardUnitInclusion_comp_unit p E S hE hS
  have hcanon : Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app c U a) =
      Scheme.Modules.Hom.app (toRationalFunctions T) (p ⁻¹ᵁ U) ((p.app U).hom a) := by
    rw [effectiveCartierPushforwardUnitMap_app]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.unitToSheaf_ι]
  have hinc (s : Γ((Scheme.Modules.pushforward p).obj (E - S).sheaf, U)) :
      Scheme.Modules.Hom.app c U (Scheme.Modules.Hom.app j U s) =
        Scheme.Modules.Hom.app (cartierEffectiveInclusion E S hS) (p ⁻¹ᵁ U) s := by
    change Scheme.Modules.Hom.app (j ≫ c) U s = _
    rw [hcomp]
    rfl
  constructor
  · rintro ⟨s, hs⟩
    have he := congrArg (Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U)) (hinc s)
    rw [hs, hcanon] at he
    have hι := ConcreteCategory.congr_hom (congrArg
      (fun f => Scheme.Modules.Hom.app f (p ⁻¹ᵁ U)) (cartierEffectiveInclusion_ι E S hS)) s
    exact he.symm ▸ (hι.symm ▸ (E - S).sheafι_app_mem (p ⁻¹ᵁ U) s)
  · intro hs
    let s := CartierDivisor.sectionMk _ hs
    refine ⟨s, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app c U)).injective
    rw [hinc s]
    apply E.sheafι_app_injective (p ⁻¹ᵁ U)
    rw [hcanon]
    have hι := ConcreteCategory.congr_hom (congrArg
      (fun f => Scheme.Modules.Hom.app f (p ⁻¹ᵁ U)) (cartierEffectiveInclusion_ι E S hS)) s
    exact hι.trans (CartierDivisor.sheafι_app_sectionMk _ hs)

end MixedFujita
