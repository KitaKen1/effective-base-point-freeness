/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KodairaLemmaNormal
public import MixedFujita.SNCModelFreeKltPerturbations
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.LinearEffectiveFreenessReduction

/-! 元L・a0を保つ小有効klt境界増加とBPF随伴のample化。 See reports/check-250-BPF-ample-boundary-concentration-extension.json for the verified scope. Original nef-big BPF data internally yield a small effective klt boundary increase with an ample adjoint, retaining L and a0. High-power lc adjoints stay ample for all large degrees. Every coherent ideal subscheme has unconditional full Serre vanishing and actual restriction lifting for high ample twists. The fixed nonempty reduced base source and these concentration-twist extensions are internal. Original L lifting still needs explicit usual KV. Initial and restricted L-nonvanishing, minimal-center normality/vanishing, high-multiplicity concentration, usual KV, BPF and full F1/F2 remain unproved. -/

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






/-- The first, fixed-effective-divisor part of Kodaira perturbation already
makes the ORIGINAL BPF adjoint ample, retaining L and its coefficient a₀. -/
theorem bpf_Kodaira_fixed_perturbation_adjoint_identity
    {X : Scheme.{u}} [IsIntegral X] (L D H : CartierDivisor X) (d a₀ m e : ℕ)
    (t : Γ((m • ((d * a₀) • L - D) - H).sheaf, ⊤)) (ht : t ≠ 0) :
    (((m + e + 1) * d) * a₀) • L -
        ((m + e + 1) • D + cartierSectionZeroDivisor (m • ((d * a₀) • L - D) - H) t ht) =
      (e + 1) • ((d * a₀) • L - D) + H +
        principalCartierDivisor X (cartierSectionUnit (m • ((d * a₀) • L - D) - H) t ht)⁻¹ := by
  rw [cartierSectionZeroDivisor, principalCartierDivisor_inv]
  module


/-- ORIGINAL nef-big BPF adjoint data internally give a SMALL EFFECTIVE klt
boundary increase whose adjoint is AMPLE, with the SAME L and SAME a₀.
No initial section of L, usual KV, Kodaira section or small perturbation is supplied. -/
theorem original_klt_bpf_exists_small_effective_boundary_ample_adjoint
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (L : CartierDivisor X) (a₀ : ℕ)
    (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D)) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ G : CartierDivisor X, G.IsEffective ∧
      LogPairBoundaryEffective cX fX (s * d) (s • D + G) ∧
      LogPairIsKlt cX fX (s * d) (s • D + G) ∧
      CartierIsAmpleProj K (((s * d) * a₀) • L - (s • D + G)) := by
  obtain ⟨H, hH⟩ := hProj
  let B := (d * a₀) • L - D
  obtain ⟨m, hm, t, ht⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj
    hdim hn hnorm cX B H hbig hH
  let G := cartierSectionZeroDivisor (m • B - H) t ht
  have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective _ t ht
  have hmd : (0 : ℚ) < ((m * d : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  obtain ⟨s, hs, hsd, hsmall, heff', hklt'⟩ :=
    logPairIsKlt_exists_small_fixed_effective_divisor_perturbation cX fX d hd D G hklt heff hG
      (1 / ((m * d : ℕ) : ℚ)) (one_div_pos.mpr hmd)
  have hms : m < s := by
    have hsdpos : (0 : ℚ) < ((s * d : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_pos (by omega : 0 < s) (by omega : 0 < d)
    have h := (one_div_lt_one_div hsdpos hmd).mp hsmall
    have hmul : m * d < s * d := by exact_mod_cast h
    exact Nat.lt_of_mul_lt_mul_right hmul
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, s = m + e + 1 := ⟨s - m - 1, by omega⟩
  have hA : CartierIsAmpleProj K ((e + 1) • B + H) :=
    proper_nef_add_ample_isAmpleProj K _ _ (cartierIsNef_nsmul hnef (e + 1)) hH
  refine ⟨m + e + 1, hs, G, hG, heff', hklt', ?_⟩
  change CartierIsAmpleProj K ((((m + e + 1) * d) * a₀) • L -
    ((m + e + 1) • D + cartierSectionZeroDivisor (m • ((d * a₀) • L - D) - H) t ht))
  rw [bpf_Kodaira_fixed_perturbation_adjoint_identity]
  exact cartierIsAmpleProj_add_principal hA _

end MixedFujita
