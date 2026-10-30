/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ImageIdealSupportUnit
public import MixedFujita.CanonicalSubcutUnitInclusion
public import MixedFujita.NormalCartierBaseNeighborhoodSections

/-! 実subcut像の負素因子中心による台と閉集合包含判定。 See reports/check-247-lc-non-klt-support-canonical-subscheme.json for the verified scope. The actual lc kernel image support equals the original all-model non-klt locus. Its radical coherent ideal and nonempty reduced lower-dimensional W are unique, independent of the SNC model and adjoint P, and constructed without KV. Containment in any closed Z is equivalent to klt outside Z. Usual KV is a condition only for simultaneous restriction lifting. Stable-base-locus perturbation, restricted-section nonvanishing, usual KV, normal minimal-lc-center adjunction, klt BPF and full F1/F2 remain unproved. -/

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



/-- The actual canonical subcut image has precisely the closed centres of its
negative prime coefficients as support. No properness of the model map is needed. -/
theorem canonical_subcut_image_support_iff_negative_prime
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    [((Scheme.Modules.pushforward p).obj (E - S).sheaf).IsQuasicoherent] (x : X) :
    x ∈ ((quasicoherentModuleImageIdealSheaf ((Scheme.Modules.pushforward p).obj (E - S).sheaf)
      (cartierSubcutPushforwardUnitInclusion p E S hE hS)).support : Set X) ↔
      ∃ t : CodimensionOnePoint T, x ∈ closure ({p (t : T)} : Set X) ∧
        cartierCoefficient (E - S) (t : T) < 0 := by
  classical
  have hc : (x ∉ ((quasicoherentModuleImageIdealSheaf
      ((Scheme.Modules.pushforward p).obj (E - S).sheaf)
      (cartierSubcutPushforwardUnitInclusion p E S hE hS)).support : Set X)) ↔
      ∀ t : CodimensionOnePoint T, x ∈ closure ({p (t : T)} : Set X) →
        0 ≤ cartierCoefficient (E - S) (t : T) := by
    rw [quasicoherentImageIdeal_notMem_support_iff_local_unit]
    simp_rw [one_in_range_cartierSubcutPushforwardUnitInclusion_iff]
    exact exists_base_neighborhood_one_mem_cartier_sections_iff hnormT p x (E - S)
  have hn := not_congr hc
  push Not at hn
  exact hn


/-- A closed set contains the ACTUAL canonical subcut support precisely when it
contains the images of all negative-coefficient primes. It need not contain an entire model. -/
theorem canonical_subcut_image_support_le_closed_iff
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    [((Scheme.Modules.pushforward p).obj (E - S).sheaf).IsQuasicoherent] (Z : Closeds X) :
    (quasicoherentModuleImageIdealSheaf ((Scheme.Modules.pushforward p).obj (E - S).sheaf)
      (cartierSubcutPushforwardUnitInclusion p E S hE hS)).support ≤ Z ↔
      ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) < 0 → p (t : T) ∈ Z := by
  constructor
  · intro h t ht
    apply h
    exact (canonical_subcut_image_support_iff_negative_prime p hnormT E S hE hS _).mpr
      ⟨t, subset_closure (Set.mem_singleton _), ht⟩
  · intro h x hx
    obtain ⟨t, hxt, ht⟩ := (canonical_subcut_image_support_iff_negative_prime p hnormT E S hE hS x).mp hx
    exact (specializes_iff_mem_closure.mpr hxt).mem_closed Z.isClosed (h t ht)

end MixedFujita
