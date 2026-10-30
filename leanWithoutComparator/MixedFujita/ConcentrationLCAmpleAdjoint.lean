/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.LinearEffectiveFreenessReduction

/-! 集中lc閾値後の実随伴恒等式・ample保持と全大倍数。 See reports/check-254-positive-numerical-lc-ample-source.json for the verified scope. Actual non-lc concentration internally gives a strictly smaller rational effective lc non-klt endpoint. Actual Cartier decomposition preserves an ample original L-adjoint in every large degree. Original normal klt BPF data with positive original numerical dimension construct a canonical nonempty reduced lower-dimensional non-klt source without an initial L section or KV; codimension-one charts follow internally from normality. The same source has all-large-original-L restriction lifting under explicit usual H1 KV. Initial and positive-dimensional restricted nonvanishing, minimal lc-center geometry, center-exterior control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- The actual concentrated-lc adjoint is a POSITIVE ample multiple plus
an original nef multiple and an explicit principal divisor. -/
theorem concentration_lc_perturbed_adjoint_decomposition
    {X : Scheme.{u}} [IsIntegral X] (L D M : CartierDivisor X)
    (d a₀ a q j l : ℕ) (hsmall : d * a * j < q) (u : X.functionFieldˣ)
    (hM : M = j • ((l + d * a₀) • L - D) + principalCartierDivisor X u) :
    ((q * d) * (a₀ + a * j * l)) • L - (q • D + (d * a) • M) =
      (q - d * a * j) • ((d * a₀) • L - D) +
        (d * (q - 1) * a * j * l) • L + principalCartierDivisor X (u ^ (d * a))⁻¹ := by
  rw [hM, principalCartierDivisor_inv, principalCartierDivisor_power,
    sub_nsmul ((d * a₀) • L - D) (Nat.le_of_lt hsmall)]
  have hrem : (d * (q - 1) * a * j * l) • L = (q - 1) • ((d * a * j * l) • L) := by module
  rw [hrem, sub_nsmul ((d * a * j * l) • L) (show 1 ≤ q by omega)]
  module


/-- A strict concentration threshold keeps the ORIGINAL L-adjoint ample;
no boundary lc input or vanishing input is needed for the positivity itself. -/
theorem concentration_lc_perturbed_adjoint_isAmple
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (L D M : CartierDivisor X) (hL : CartierIsNef K L)
    (d a₀ a q j l : ℕ) (hsmall : d * a * j < q)
    (hA : CartierIsAmpleProj K ((d * a₀) • L - D)) (u : X.functionFieldˣ)
    (hM : M = j • ((l + d * a₀) • L - D) + principalCartierDivisor X u) :
    CartierIsAmpleProj K (((q * d) * (a₀ + a * j * l)) • L - (q • D + (d * a) • M)) := by
  rw [concentration_lc_perturbed_adjoint_decomposition L D M d a₀ a q j l hsmall u hM]
  have hm : 1 ≤ q - d * a * j := by omega
  have hamp := cartierIsAmpleProj_nsmul hA hm
  have hnef := cartierIsNef_nsmul hL (d * (q - 1) * a * j * l)
  apply cartierIsAmpleProj_add_principal
  simpa only [add_comm] using proper_nef_add_ample_isAmpleProj K _ _ hnef hamp


/-- One ample ORIGINAL L-adjoint stays ample for every larger original
multiple, by a natural multiple of the original nef divisor. -/
theorem original_nef_ample_adjoint_all_large
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (L D : CartierDivisor X) (hL : CartierIsNef K L) (r b : ℕ)
    (hA : CartierIsAmpleProj K ((r * b) • L - D)) (m : ℕ) (hm : b ≤ m) :
    CartierIsAmpleProj K ((r * m) • L - D) := by
  have heq : (r * m) • L - D = (m - b) • (r • L) + ((r * b) • L - D) := by
    rw [sub_nsmul (r • L) hm]
    module
  rw [heq]
  exact proper_nef_add_ample_isAmpleProj K _ _ (cartierIsNef_nsmul (cartierIsNef_nsmul hL r) (m - b)) hA

end MixedFujita
