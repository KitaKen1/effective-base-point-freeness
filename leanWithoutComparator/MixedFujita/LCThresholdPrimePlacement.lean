/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCNewCenterDescent

/-! 同じ閾値素因子の旧discrepancyから実中心の包含。 See reports/check-258-minimal-lc-section-adjoint-descent.json for the verified scope. Inclusion-minimality and exterior LC force zero perturbation at every old critical prime, removing the all-old-center avoidance premise. Nonzero NATURAL restriction is equivalent to noncontainment in the actual zero-divisor support. The same threshold-prime strict old discrepancy places its center inside the original minimal center. An exact positive rational threshold and a lower-dimensional inclusion-minimal integral new-pair lc center are constructed internally. Actual original ample-adjoint sections preserve all-large ORIGINAL L ample adjoints. Exterior LC and an actual ambient non-LC point remain explicit hypotheses. Their construction from restricted concentration, appropriate center vanishing, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower


/-- A threshold prime whose OLD discrepancy is strictly above -d has its
entire closed center in Z if a larger coefficient is lc outside Z. Only this
actual witness is needed; the closed center may also be an old lc center via
another prime. -/
theorem strict_lc_perturbation_prime_center_le_closed_of_old_discrepancy_strict
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d a q j : ℕ)
    (hsmall : d * a * j < q) (D M : CartierDivisor X) (Z : Closeds X)
    (houtside : ∀ x : X, x ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M))
    (cT : EtaleChart K T n) (t : T) (ht : Order.coheight t = 1)
    (hold : -(d : ℤ) < cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t)
    (heq : cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q * d)
      (q • D + (d * a) • M) cT etaleCharts_cover) t = -((q * d : ℕ) : ℤ)) :
    closure ({ρ t} : Set X) ⊆ Z := by
  intro x hx
  by_contra hxZ
  have hxcl : x ∈ closure ({(ρ ≫ 𝟙 X) t} : Set X) := by simpa only [Category.comp_id] using hx
  have hlarge := houtside x hxZ T ρ hρ cT t ht hxcl
  rw [logDiscrepancyDivisor_rational_perturbation, cartierCoefficient_sub,
    cartierCoefficient_nsmul, cartierCoefficient_nsmul] at heq
  rw [logDiscrepancyDivisor_add_source, logDiscrepancyDivisor_scale_denominator,
    cartierCoefficient_sub, cartierCoefficient_nsmul] at hlarge
  let A := cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t
  let m := cartierCoefficient (cartierPullback ρ M) t
  change -(d : ℤ) < A at hold
  change -((j * d : ℕ) : ℤ) ≤ (j : ℤ) * A - m at hlarge
  change (q : ℤ) * A - ((d * a : ℕ) : ℤ) * m = -((q * d : ℕ) : ℤ) at heq
  have hsmallZ : (d : ℤ) * a * j < q := by exact_mod_cast hsmall
  have hmul := mul_le_mul_of_nonneg_left hlarge (show (0 : ℤ) ≤ (d : ℤ) * a by positivity)
  push_cast at heq hmul
  have hh := mul_pos (sub_pos.mpr hsmallZ) (show 0 < A + d by omega)
  nlinarith

end MixedFujita
