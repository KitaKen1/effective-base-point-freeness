/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.HighPowerPerturbedAdjointDecomposition
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.LinearEffectiveFreenessReduction

/-! 全大倍数の高倍数lc摂動後随伴のample性。 See reports/check-250-BPF-ample-boundary-concentration-extension.json for the verified scope. Original nef-big BPF data internally yield a small effective klt boundary increase with an ample adjoint, retaining L and a0. High-power lc adjoints stay ample for all large degrees. Every coherent ideal subscheme has unconditional full Serre vanishing and actual restriction lifting for high ample twists. The fixed nonempty reduced base source and these concentration-twist extensions are internal. Original L lifting still needs explicit usual KV. Initial and restricted L-nonvanishing, minimal-center normality/vanishing, high-multiplicity concentration, usual KV, BPF and full F1/F2 remain unproved. -/

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






/-- With the original BPF adjoint AMPLE, every large high-power perturbed
adjoint is AMPLE as well. This uses the SAME explicit coarse natural degree bound. -/
theorem original_ample_bpf_high_power_perturbed_adjoint_isAmple
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (L D : CartierDivisor X) (hL : CartierIsNef K L)
    (d a₀ : ℕ) (hA : CartierIsAmpleProj K ((d * a₀) • L - D))
    (a q N m j : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) (hj : a₀ + a * m ≤ j)
    (t : Γ((N • (m • L)).sheaf, ⊤)) (ht : t ≠ 0) :
    CartierIsAmpleProj K (((q * N) * d) • (j • L) -
      ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • (m • L)) t ht)) := by
  rw [high_power_perturbed_adjoint_decomposition L D d a₀ a q N m j hq hj t ht]
  have hqn : 1 ≤ q * N := Nat.mul_pos (by omega) (by omega)
  have htail := cartierIsNef_nsmul hL (d * N * (q * (j - a₀) - a * m))
  have hmulti := cartierIsAmpleProj_nsmul hA hqn
  have hsum := proper_nef_add_ample_isAmpleProj K _ _ htail hmulti
  apply cartierIsAmpleProj_add_principal
  simpa only [add_comm] using hsum

end MixedFujita
