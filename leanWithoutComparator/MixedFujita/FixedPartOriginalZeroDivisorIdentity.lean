/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierFixedPartResidualSections

/-! 指定元切断と実固定成分包含の零因子等式。 See reports/check-263-exterior-lc-concentration.json for the verified scope. Actual SNC principalization of the SAME original finite subsystem and boundary-avoiding first-nonzero residual Bertini are assembled internally. Fixed-part coefficients vanish at EVERY prime relevant to points outside actual center support. Old LC coefficient bounds and new reduced-cut coefficients 0/1 prove original all-model pointwise exterior LC. Zero sections are filtered while preserving original nonzero indices. ALL high ample powers preserve nonzero natural restriction up to nonzero scalar and prove exterior LC. Positive RESTRICTED numerical dimension gives all-high actual concentrated original lifts preserving exact restricted order AND exterior LC. No original klt, normality, supplied model, initial L section or KV is required. Ambient nonLC from restricted concentration, actual lower-center iteration, original mL/center adjoint vanishing, nu=0, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Exact actual zero-divisor identity for a specified residual section and its
specified ORIGINAL image under the effective fixed-part inclusion. -/
theorem cartier_fixed_part_inclusion_zeroDivisor
    {X : Scheme.{u}} [IsIntegral X] (P F : CartierDivisor X) (hF : F.IsEffective)
    (t : Γ((P - F).sheaf, ⊤)) (ht : t ≠ 0) (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0)
    (hi : Scheme.Modules.Hom.app (cartierEffectiveInclusion P F hF) ⊤ t = s) :
    cartierSectionZeroDivisor P s hs = F + cartierSectionZeroDivisor (P - F) t ht := by
  have he : cartierSectionRational P s = cartierSectionRational (P - F) t := by
    rw [← hi]
    apply congrArg (rationalFunctionsEquiv (X := X) ⊤)
      (ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤)
        (cartierEffectiveInclusion_ι P F hF)) t)
  have hu : cartierSectionUnit P s hs = cartierSectionUnit (P - F) t ht := Units.ext he
  rw [cartierSectionZeroDivisor, hu, cartierSectionZeroDivisor]
  abel

end MixedFujita
